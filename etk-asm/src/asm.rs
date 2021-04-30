mod error {
    use crate::ops::TryFromIntError;
    use crate::parse::ParseError;

    use snafu::{Backtrace, Snafu};

    #[derive(Snafu, Debug)]
    #[non_exhaustive]
    #[snafu(visibility = "pub(super)")]
    pub enum Error {
        #[snafu(display("label `{}` declared multiple times", label))]
        DuplicateLabel { label: String, backtrace: Backtrace },

        #[snafu(display("value of label `{}` was too large for the given opcode", label))]
        LabelTooLarge {
            label: String,
            #[snafu(backtrace)]
            source: TryFromIntError,
        },

        #[snafu(display("label `{}` was never defined", label))]
        UndefinedLabel { label: String, backtrace: Backtrace },

        #[snafu(display("include or import failed to parse: {}", source))]
        #[snafu(context(false))]
        ParseInclude {
            #[snafu(backtrace)]
            source: ParseError,
        },
    }
}

use crate::ops::{AbstractOp, LabelOp};

pub use self::error::Error;

use snafu::ResultExt;

use std::collections::{hash_map, HashMap, VecDeque};
use std::convert::TryInto;

#[derive(Debug, Clone)]
pub enum RawOp {
    Op(LabelOp),
    Raw(Vec<u8>),
}

impl RawOp {
    pub fn is_empty(&self) -> bool {
        match self {
            Self::Op(_) => false,
            Self::Raw(raw) => raw.is_empty(),
        }
    }

    pub fn len(&self) -> u32 {
        match self {
            Self::Op(op) => 1 + op.specifier().extra_len(),
            Self::Raw(raw) => raw.len().try_into().expect("raw too long"),
        }
    }
}

impl From<AbstractOp> for RawOp {
    fn from(op: AbstractOp) -> Self {
        Self::Op(op.into())
    }
}

impl From<LabelOp> for RawOp {
    fn from(op: LabelOp) -> Self {
        Self::Op(op)
    }
}

impl From<Vec<u8>> for RawOp {
    fn from(vec: Vec<u8>) -> Self {
        Self::Raw(vec)
    }
}

#[derive(Debug, Default)]
pub struct Assembler {
    ready: Vec<u8>,
    pending: VecDeque<RawOp>,
    code_len: u32,
    labels: HashMap<String, u32>,
}

impl Assembler {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn finish(self) -> Result<(), Error> {
        if let Some(undef) = self.pending.front() {
            return match undef {
                RawOp::Op(op) => {
                    let label = op.immediate_label().unwrap();
                    error::UndefinedLabel { label }.fail()
                }
                _ => unreachable!(),
            };
        }

        if !self.ready.is_empty() {
            panic!("not all assembled bytecode has been taken");
        }

        Ok(())
    }

    pub fn take(&mut self) -> Vec<u8> {
        std::mem::take(&mut self.ready)
    }

    pub fn push_all<I, O>(&mut self, ops: I) -> Result<usize, Error>
    where
        I: IntoIterator<Item = O>,
        O: Into<RawOp>,
    {
        let ops = ops.into_iter().map(Into::into);

        for op in ops {
            self.push(op)?;
        }

        Ok(self.ready.len())
    }

    pub fn push<O>(&mut self, rop: O) -> Result<usize, Error>
    where
        O: Into<RawOp>,
    {
        let rop = rop.into();

        if let RawOp::Op(ref op) = rop {
            if let Some(label) = op.label() {
                match self.labels.entry(label.to_owned()) {
                    hash_map::Entry::Occupied(_) => {
                        return error::DuplicateLabel { label }.fail();
                    }
                    hash_map::Entry::Vacant(v) => {
                        v.insert(self.code_len);
                    }
                }
            }
        }

        let len = rop.len();
        self.push_unchecked(rop)?;

        self.code_len += len;
        Ok(self.ready.len())
    }

    fn push_unchecked(&mut self, rop: RawOp) -> Result<(), Error> {
        if self.pending.is_empty() {
            self.push_ready(rop)
        } else {
            self.push_pending(rop)
        }
    }

    fn push_ready(&mut self, rop: RawOp) -> Result<(), Error> {
        match rop {
            RawOp::Op(mut op) => {
                if let Some(label) = op.immediate_label() {
                    match self.labels.get(label) {
                        Some(addr) => {
                            op = op.realize(*addr).context(error::LabelTooLarge { label })?;
                        }
                        None => {
                            self.pending.push_back(RawOp::Op(op));
                            return Ok(());
                        }
                    }
                }

                op.concretize().assemble(&mut self.ready);

                Ok(())
            }
            RawOp::Raw(raw) => {
                self.ready.extend(raw);
                Ok(())
            }
        }
    }

    fn push_pending(&mut self, rop: RawOp) -> Result<(), Error> {
        self.pending.push_back(rop);

        while let Some(next) = self.pending.front() {
            let op = match next {
                RawOp::Op(op) => op,
                RawOp::Raw(raw) => {
                    self.ready.extend(raw);
                    self.pending.pop_front();
                    continue;
                }
            };

            let mut address = None;
            let mut label = None;

            if let Some(lbl) = op.immediate_label() {
                // If the op has a label, try to resolve it.
                match self.labels.get(lbl) {
                    Some(addr) => {
                        // The label resolved! Move the op to ready.
                        address = Some(*addr);
                        label = Some(lbl);
                    }
                    None => {
                        // Otherwise, the address isn't known yet, so break!
                        break;
                    }
                }
            }

            match address {
                Some(s) => {
                    // Don't modify `self.pending` if realize returns an error.
                    let realized = op.realize(s).with_context(|| error::LabelTooLarge {
                        label: label.unwrap(),
                    })?;
                    self.pending.pop_front();
                    realized.concretize().assemble(&mut self.ready);
                }
                None => {
                    op.clone().concretize().assemble(&mut self.ready);
                    self.pending.pop_front();
                }
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use assert_matches::assert_matches;

    use crate::ops::{Imm, Op};

    use hex_literal::hex;

    use super::*;

    #[test]
    fn assemble_jumpdest_no_label() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let sz = asm.push_all(vec![Op::JumpDest])?;
        assert_eq!(1, sz);
        assert!(asm.labels.is_empty());
        assert_eq!(asm.take(), hex!("5b"));
        Ok(())
    }

    #[test]
    fn assemble_jumpdest_with_label() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let op = LabelOp::with_label(Op::JumpDest, "lbl");

        let sz = asm.push_all(vec![op])?;
        assert_eq!(1, sz);
        assert_eq!(asm.labels.len(), 1);
        assert_eq!(asm.labels.get("lbl"), Some(&0));
        assert_eq!(asm.take(), hex!("5b"));
        Ok(())
    }

    #[test]
    fn assemble_jumpdest_jump_with_label() -> Result<(), Error> {
        let ops = vec![
            LabelOp::with_label(Op::JumpDest, "lbl"),
            LabelOp::new(Op::Push1("lbl".into())),
        ];

        let mut asm = Assembler::new();
        let sz = asm.push_all(ops)?;
        assert_eq!(sz, 3);
        assert_eq!(asm.take(), hex!("5b6000"));

        Ok(())
    }

    #[test]
    fn assemble_labeled_pc() -> Result<(), Error> {
        let ops = vec![
            LabelOp::new(Op::Push1("lbl".into())),
            LabelOp::with_label(Op::GetPc, "lbl"),
        ];

        let mut asm = Assembler::new();
        let sz = asm.push_all(ops)?;
        assert_eq!(sz, 3);
        assert_eq!(asm.take(), hex!("600258"));

        Ok(())
    }

    #[test]
    fn assemble_jump_jumpdest_with_label() -> Result<(), Error> {
        let ops = vec![
            LabelOp::new(Op::Push1("lbl".into())),
            LabelOp::with_label(Op::JumpDest, "lbl"),
        ];

        let mut asm = Assembler::new();
        let sz = asm.push_all(ops)?;
        assert_eq!(sz, 3);
        assert_eq!(asm.take(), hex!("60025b"));

        Ok(())
    }

    #[test]
    fn assemble_label_too_large() {
        let mut ops: Vec<_> = std::iter::repeat(Op::GetPc)
            .take(255)
            .map(LabelOp::new)
            .collect();
        ops.push(LabelOp::with_label(Op::JumpDest, "b"));
        ops.push(LabelOp::with_label(Op::JumpDest, "a"));
        ops.push(Op::Push1(Imm::from("a")).into());
        let mut asm = Assembler::new();
        let err = asm.push_all(ops).unwrap_err();
        assert_matches!(err, Error::LabelTooLarge { label, .. } if label == "a");
    }

    #[test]
    fn assemble_label_just_right() -> Result<(), Error> {
        let mut ops: Vec<_> = std::iter::repeat(Op::GetPc)
            .take(255)
            .map(LabelOp::new)
            .collect();
        ops.push(LabelOp::with_label(Op::JumpDest, "b"));
        ops.push(LabelOp::with_label(Op::JumpDest, "a"));
        ops.push(Op::Push1(Imm::from("b")).into());
        let mut asm = Assembler::new();
        let sz = asm.push_all(ops)?;
        assert_eq!(sz, 259);

        let assembled = asm.take();
        asm.finish()?;

        let mut expected = vec![0x58; 255];
        expected.push(0x5b);
        expected.push(0x5b);
        expected.push(0x60);
        expected.push(0xff);

        assert_eq!(assembled, expected);

        Ok(())
    }
}
