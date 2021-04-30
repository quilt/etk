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

        #[snafu(display("value was too large for any push"))]
        UnsizedPushTooLarge { backtrace: Backtrace },

        #[snafu(display("label `{}` was never defined", label))]
        UndeclaredLabel { label: String, backtrace: Backtrace },

        #[snafu(display("include or import failed to parse: {}", source))]
        #[snafu(context(false))]
        ParseInclude {
            #[snafu(backtrace)]
            source: ParseError,
        },
    }
}

use crate::ops::{AbstractOp, Imm, Specifier};

pub use self::error::Error;

use snafu::{OptionExt, ResultExt};

use std::collections::{hash_map, HashMap, HashSet, VecDeque};
use std::convert::TryInto;

#[derive(Debug, Clone)]
pub enum RawOp {
    Op(AbstractOp),
    Raw(Vec<u8>),
}

impl RawOp {
    fn size(&self) -> Option<u32> {
        match self {
            Self::Op(op) => op.size(),
            Self::Raw(raw) => Some(raw.len().try_into().expect("raw too big")),
        }
    }

    fn immediate_label(&self) -> Option<&str> {
        match self {
            Self::Op(op) => op.immediate_label(),
            Self::Raw(_) => None,
        }
    }
}

impl From<AbstractOp> for RawOp {
    fn from(op: AbstractOp) -> Self {
        Self::Op(op)
    }
}

impl From<Vec<u8>> for RawOp {
    fn from(vec: Vec<u8>) -> Self {
        Self::Raw(vec)
    }
}

#[derive(Debug)]
pub struct Assembler {
    /// Assembled ops, ready to be taken.
    ready: Vec<u8>,

    /// Ops which cannot be encoded yet.
    pending: VecDeque<RawOp>,

    /// Sum of the size of all the ops in `pending`, or `None` if `pending` contains
    /// an unsized op.
    pending_len: Option<u32>,

    /// Total number of `u8` which have been appended to `ready`.
    concrete_len: u32,

    /// Labels, in `pending`, associated with an `AbstractOp::Label`.
    declared_labels: HashMap<String, Option<u32>>,

    /// Labels, in `pending`, which have been referred to (ex. with push) but
    /// have not been declared with an `AbstractOp::Label`.
    undeclared_labels: HashSet<String>,
}

impl Default for Assembler {
    fn default() -> Self {
        Self {
            ready: Default::default(),
            pending: Default::default(),
            pending_len: Some(0),
            concrete_len: 0,
            declared_labels: Default::default(),
            undeclared_labels: Default::default(),
        }
    }
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
                    error::UndeclaredLabel { label }.fail()
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

        if let RawOp::Op(AbstractOp::Label(ref label)) = rop {
            match self.declared_labels.entry(label.to_owned()) {
                hash_map::Entry::Occupied(_) => {
                    return error::DuplicateLabel { label }.fail();
                }
                hash_map::Entry::Vacant(v) => {
                    v.insert(None);
                    self.undeclared_labels.remove(label);
                }
            }
        }

        if let Some(label) = rop.immediate_label() {
            if !self.declared_labels.contains_key(label) {
                self.undeclared_labels.insert(label.to_owned());
            }
        }

        self.push_unchecked(rop)?;
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
            RawOp::Op(AbstractOp::Label(label)) => {
                let old = self
                    .declared_labels
                    .insert(label, Some(self.concrete_len))
                    .expect("label should exist");
                assert_eq!(old, None, "label should have been undefined");
                Ok(())
            }
            RawOp::Op(mut op) => {
                if let Some(label) = op.immediate_label() {
                    match self.declared_labels.get(label) {
                        Some(Some(addr)) => {
                            op = op.realize(*addr).context(error::LabelTooLarge { label })?;
                        }
                        _ => {
                            assert_eq!(self.pending_len, Some(0));
                            self.pending_len = op.size();
                            self.pending.push_back(RawOp::Op(op));
                            return Ok(());
                        }
                    }
                }

                let concrete = op.concretize().context(error::UnsizedPushTooLarge)?;
                self.concrete_len += concrete.size();

                concrete.assemble(&mut self.ready);

                Ok(())
            }
            RawOp::Raw(raw) => {
                let len: u32 = raw.len().try_into().expect("raw too long");
                self.concrete_len += len;
                self.ready.extend(raw);
                Ok(())
            }
        }
    }

    fn pop_pending(&mut self) -> Result<(), Error> {
        let popped = self.pending.pop_front().unwrap();

        let size;

        match popped {
            RawOp::Raw(raw) => {
                size = raw.len() as u32;
                self.ready.extend(raw);
            }
            RawOp::Op(aop) => {
                let cop = aop.concretize().context(error::UnsizedPushTooLarge {})?;
                size = cop.size();
                cop.assemble(&mut self.ready);
            }
        }

        self.concrete_len += size;

        if self.pending.is_empty() {
            self.pending_len = Some(0);
        } else if let Some(ref mut pending_len) = self.pending_len {
            *pending_len -= size;
        }

        Ok(())
    }

    fn push_pending(&mut self, rop: RawOp) -> Result<(), Error> {
        // Update total size of pending ops.
        match (&mut self.pending_len, rop.size()) {
            (Some(p), Some(me)) => {
                *p += me;
            }
            (p, None) => {
                *p = None;
            }
            (None, _) => (),
        }

        // Handle labels.
        match (self.pending_len, rop) {
            (Some(pending_len), RawOp::Op(AbstractOp::Label(lbl))) => {
                // The label has a defined address.
                let address = self.concrete_len + pending_len;
                let item = self.declared_labels.get_mut(&*lbl).unwrap();
                *item = Some(address);
            }
            (None, rop @ RawOp::Op(AbstractOp::Label(_))) => {
                self.pending.push_back(rop);
                if self.undeclared_labels.is_empty() {
                    self.choose_sizes()?;
                }
            }
            (_, rop) => {
                // Not a label.
                self.pending.push_back(rop);
            }
        }

        // Repeatedly check if the front of the pending list is ready.
        while let Some(next) = self.pending.front() {
            let op = match next {
                RawOp::Op(AbstractOp::Push(Imm::Label(_))) => {
                    if self.undeclared_labels.is_empty() {
                        unreachable!()
                    } else {
                        // Still waiting on more labels.
                        break;
                    }
                }
                RawOp::Op(AbstractOp::Push(Imm::Constant(_))) => unreachable!(),
                RawOp::Op(AbstractOp::Label(_)) => unreachable!(),
                RawOp::Op(op) => op,
                RawOp::Raw(_) => {
                    self.pop_pending()?;
                    continue;
                }
            };

            let mut address = None;
            let mut label = None;

            if let Some(lbl) = op.immediate_label() {
                // If the op has a label, try to resolve it.
                match self.declared_labels.get(lbl) {
                    Some(Some(addr)) => {
                        // The label resolved! Move the op to ready.
                        address = Some(*addr);
                        label = Some(lbl);
                    }
                    _ => {
                        // Otherwise, the address isn't known yet, so break!
                        break;
                    }
                }
            }

            if let Some(s) = address {
                // Don't modify `self.pending` if realize returns an error.
                let realized = op.realize(s).with_context(|| error::LabelTooLarge {
                    label: label.unwrap(),
                })?;
                let front = self.pending.front_mut().unwrap();
                *front = RawOp::Op(realized);
            }

            self.pop_pending()?;
        }

        Ok(())
    }

    fn choose_sizes(&mut self) -> Result<(), Error> {
        let minimum = Specifier::push_for(self.concrete_len).unwrap();

        let mut undefined_labels: HashMap<String, Specifier> = self
            .declared_labels
            .iter()
            .filter(|(_, v)| v.is_none())
            .map(|(k, _)| (k.clone(), minimum))
            .collect();

        let mut subasm;

        loop {
            // Create a sub-assembler to try assembling with the sizes in
            // `undefined_labels`.
            subasm = Self::default();
            subasm.concrete_len = self.concrete_len;
            subasm.declared_labels = self.declared_labels.clone();

            let result: Result<Vec<_>, Error> = self
                .pending
                .iter()
                .map(|op| {
                    let new = match op {
                        RawOp::Op(AbstractOp::Push(Imm::Label(lbl))) => {
                            // Replace unsized push with our current guess.
                            let spec = undefined_labels[lbl];
                            let aop = AbstractOp::with_label(spec, lbl);
                            RawOp::Op(aop)
                        }
                        RawOp::Op(aop @ AbstractOp::Push(Imm::Constant(_))) => {
                            let cop = aop
                                .clone()
                                .concretize()
                                .context(error::UnsizedPushTooLarge)?;
                            RawOp::Op(cop.into())
                        }

                        op => op.clone(),
                    };

                    subasm.push_pending(new)
                })
                .collect();

            match result {
                Ok(_) => {
                    assert!(subasm.pending.is_empty());
                    break;
                }
                Err(Error::LabelTooLarge { label, .. }) => {
                    // If a label is too large for an op, increase the width of
                    // that label.
                    let item = undefined_labels.get_mut(&label).unwrap();

                    let new_size = item.upsize().context(error::UnsizedPushTooLarge)?;
                    *item = new_size;
                }
                Err(e) => return Err(e),
            }
        }

        // Insert the results of the sub-assembler into self.
        let raw = subasm.take();
        self.pending_len = Some(raw.len().try_into().unwrap());
        self.pending.clear();
        self.pending.push_back(RawOp::Raw(raw));
        self.declared_labels = subasm.declared_labels;

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
    fn assemble_variable_push_const_while_pending() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let sz = asm.push_all(vec![
            AbstractOp::Op(Op::Push1("label1".into())),
            AbstractOp::Push(Imm::Constant(vec![0x00, 0xaa, 0xbb])),
            AbstractOp::Label("label1".into()),
        ])?;
        assert_eq!(5, sz);
        assert_eq!(asm.take(), hex!("600561aabb"));
        Ok(())
    }

    #[test]
    fn assemble_variable_pushes_abab() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let sz = asm.push_all(vec![
            AbstractOp::Op(Op::JumpDest),
            AbstractOp::Push("label1".into()),
            AbstractOp::Push("label2".into()),
            AbstractOp::Label("label1".into()),
            AbstractOp::Op(Op::GetPc),
            AbstractOp::Label("label2".into()),
            AbstractOp::Op(Op::GetPc),
        ])?;
        assert_eq!(7, sz);
        assert_eq!(asm.take(), hex!("5b600560065858"));
        Ok(())
    }

    #[test]
    fn assemble_variable_pushes_abba() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let sz = asm.push_all(vec![
            AbstractOp::Op(Op::JumpDest),
            AbstractOp::Push("label1".into()),
            AbstractOp::Push("label2".into()),
            AbstractOp::Label("label2".into()),
            AbstractOp::Op(Op::GetPc),
            AbstractOp::Label("label1".into()),
            AbstractOp::Op(Op::GetPc),
        ])?;
        assert_eq!(7, sz);
        assert_eq!(asm.take(), hex!("5b600660055858"));
        Ok(())
    }

    #[test]
    fn assemble_variable_push1_multiple() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let sz = asm.push_all(vec![
            AbstractOp::Op(Op::JumpDest),
            AbstractOp::Push("auto".into()),
            AbstractOp::Push("auto".into()),
            AbstractOp::Label("auto".into()),
        ])?;
        assert_eq!(5, sz);
        assert_eq!(asm.take(), hex!("5b60056005"));
        Ok(())
    }

    #[test]
    fn assemble_variable_push_const() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let sz = asm.push_all(vec![AbstractOp::Push(Imm::Constant(
            hex!("00aaaaaaaaaaaaaaaaaaaaaaaa").into(),
        ))])?;
        assert_eq!(13, sz);
        assert_eq!(asm.take(), hex!("6baaaaaaaaaaaaaaaaaaaaaaaa"));
        Ok(())
    }

    #[test]
    fn assemble_variable_push1_known() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let sz = asm.push_all(vec![
            AbstractOp::Op(Op::JumpDest),
            AbstractOp::Label("auto".into()),
            AbstractOp::Push("auto".into()),
        ])?;
        assert_eq!(3, sz);
        assert_eq!(asm.take(), hex!("5b6001"));
        Ok(())
    }

    #[test]
    fn assemble_variable_push1() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let sz = asm.push_all(vec![
            AbstractOp::Push("auto".into()),
            AbstractOp::Label("auto".into()),
            AbstractOp::Op(Op::JumpDest),
        ])?;
        assert_eq!(3, sz);
        assert_eq!(asm.take(), hex!("60025b"));
        Ok(())
    }

    #[test]
    fn assemble_variable_push1_reuse() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let sz = asm.push_all(vec![
            AbstractOp::Push("auto".into()),
            AbstractOp::Label("auto".into()),
            AbstractOp::Op(Op::JumpDest),
            AbstractOp::Op(Op::Push1("auto".into())),
        ])?;
        assert_eq!(5, sz);
        assert_eq!(asm.take(), hex!("60025b6002"));
        Ok(())
    }

    #[test]
    fn assemble_variable_push2() -> Result<(), Error> {
        let mut asm = Assembler::new();
        asm.push(AbstractOp::Push("auto".into()))?;
        for _ in 0..255 {
            asm.push(AbstractOp::Op(Op::GetPc))?;
        }

        asm.push_all(vec![
            AbstractOp::Label("auto".into()),
            AbstractOp::Op(Op::JumpDest),
        ])?;

        let mut expected = vec![0x61, 0x01, 0x02];
        expected.extend_from_slice(&[0x58; 255]);
        expected.push(0x5b);
        assert_eq!(asm.take(), expected);

        asm.finish()?;

        Ok(())
    }

    #[test]
    fn assemble_undeclared_label() -> Result<(), Error> {
        let mut asm = Assembler::new();
        asm.push_all(vec![AbstractOp::Op(Op::Push1("hi".into()))])?;
        let err = asm.finish().unwrap_err();
        assert_matches!(err, Error::UndeclaredLabel { label, .. } if label == "hi");
        Ok(())
    }

    #[test]
    fn assemble_jumpdest_no_label() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let sz = asm.push_all(vec![AbstractOp::Op(Op::JumpDest)])?;
        assert_eq!(1, sz);
        assert!(asm.declared_labels.is_empty());
        assert_eq!(asm.take(), hex!("5b"));
        Ok(())
    }

    #[test]
    fn assemble_jumpdest_with_label() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let ops = vec![
            AbstractOp::Label("lbl".into()),
            AbstractOp::Op(Op::JumpDest),
        ];

        let sz = asm.push_all(ops)?;
        assert_eq!(1, sz);
        assert_eq!(asm.declared_labels.len(), 1);
        assert_eq!(asm.declared_labels.get("lbl"), Some(&Some(0)));
        assert_eq!(asm.take(), hex!("5b"));
        Ok(())
    }

    #[test]
    fn assemble_jumpdest_jump_with_label() -> Result<(), Error> {
        let ops = vec![
            AbstractOp::Label("lbl".into()),
            AbstractOp::Op(Op::JumpDest),
            AbstractOp::Op(Op::Push1("lbl".into())),
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
            AbstractOp::Op(Op::Push1("lbl".into())),
            AbstractOp::Label("lbl".into()),
            AbstractOp::Op(Op::GetPc),
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
            AbstractOp::Op(Op::Push1("lbl".into())),
            AbstractOp::Label("lbl".into()),
            AbstractOp::Op(Op::JumpDest),
        ];

        let mut asm = Assembler::new();
        let sz = asm.push_all(ops)?;
        assert_eq!(sz, 3);
        assert_eq!(asm.take(), hex!("60025b"));

        Ok(())
    }

    #[test]
    fn assemble_label_too_large() {
        let mut ops: Vec<_> = vec![AbstractOp::Op(Op::GetPc); 255];
        ops.push(AbstractOp::Label("b".into()));
        ops.push(AbstractOp::Op(Op::JumpDest));
        ops.push(AbstractOp::Label("a".into()));
        ops.push(AbstractOp::Op(Op::JumpDest));
        ops.push(AbstractOp::Op(Op::Push1(Imm::from("a"))));
        let mut asm = Assembler::new();
        let err = asm.push_all(ops).unwrap_err();
        assert_matches!(err, Error::LabelTooLarge { label, .. } if label == "a");
    }

    #[test]
    fn assemble_label_just_right() -> Result<(), Error> {
        let mut ops: Vec<_> = vec![AbstractOp::Op(Op::GetPc); 255];
        ops.push(AbstractOp::Label("b".into()));
        ops.push(AbstractOp::Op(Op::JumpDest));
        ops.push(AbstractOp::Label("a".into()));
        ops.push(AbstractOp::Op(Op::JumpDest));
        ops.push(AbstractOp::Op(Op::Push1(Imm::from("b"))));
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
