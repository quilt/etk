mod error {
    use crate::ops::TryFromIntError;
    use crate::parse::ParseError;

    use snafu::{Backtrace, Snafu};

    use std::path::PathBuf;

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

        #[snafu(display("included file `{}` is invalid hex: {}", path.to_string_lossy(), source))]
        InvalidHex {
            path: PathBuf,
            source: Box<dyn std::error::Error>,
            backtrace: Backtrace,
        },
    }
}

use crate::ast::Node;
use crate::parse::parse_file;

pub use self::error::Error;

use snafu::ResultExt;

use std::collections::{hash_map, HashMap, VecDeque};
use std::fs;

#[derive(Debug, Default)]
pub struct Assembler {
    ready: Vec<u8>,
    pending: VecDeque<Node>,
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
                Node::Op(op) => {
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
        O: Into<Node>,
    {
        let ops = ops.into_iter().map(Into::into);

        for op in ops {
            self.push(op)?;
        }

        Ok(self.ready.len())
    }

    pub fn push(&mut self, node: Node) -> Result<usize, Error> {
        match &node {
            Node::Op(op) => {
                let specifier = op.specifier();

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

                self.push_unchecked(node)?;

                self.code_len += 1 + specifier.extra_len();
                Ok(self.ready.len())
            }
            Node::Import(path) => {
                let parsed = parse_file(path)?;
                self.push_all(parsed)
            }
            Node::Include(path) => {
                let parsed = parse_file(path)?;

                let mut asm = Self::new();
                asm.push_all(parsed)?;

                let raw = asm.take();
                self.code_len += raw.len() as u32;
                asm.finish()?;

                self.push_unchecked(Node::Raw(raw))?;

                Ok(self.ready.len())
            }
            Node::IncludeHex(path) => {
                let file =
                    fs::read_to_string(path).with_context(|| crate::parse::error::Io { path })?;
                let raw = hex::decode(file)
                    .map_err(|e| Box::new(e) as Box<dyn std::error::Error>)
                    .context(error::InvalidHex { path })?;
                self.code_len += raw.len() as u32;
                self.push_unchecked(Node::Raw(raw))?;

                Ok(self.ready.len())
            }
            _ => unimplemented!(),
        }
    }

    fn push_unchecked(&mut self, node: Node) -> Result<(), Error> {
        if self.pending.is_empty() {
            self.push_ready(node)
        } else {
            self.push_pending(node)
        }
    }

    fn push_ready(&mut self, mut node: Node) -> Result<(), Error> {
        match node.clone() {
            Node::Op(op) => {
                if let Some(label) = op.immediate_label() {
                    match self.labels.get(label) {
                        Some(addr) => {
                            node = op
                                .realize(*addr)
                                .context(error::LabelTooLarge { label })?
                                .into();
                        }
                        None => {
                            self.pending.push_back(node);
                            return Ok(());
                        }
                    }
                }

                node.assemble(&mut self.ready);

                Ok(())
            }
            Node::Raw(raw) => {
                self.ready.extend(raw);
                Ok(())
            }
            _ => unimplemented!(),
        }
    }

    fn push_pending(&mut self, node: Node) -> Result<(), Error> {
        self.pending.push_back(node);

        while let Some(next) = self.pending.front() {
            let mut address = None;
            let mut label = None;

            if let Node::Op(op) = next {
                if let Some(lbl) = op.immediate_label() {
                    match self.labels.get(lbl) {
                        Some(addr) => {
                            address = Some(*addr);
                            label = Some(lbl);
                        }
                        None => break,
                    }
                }

                let popped = match address {
                    Some(s) => {
                        // Don't modify `self.pending` if realize returns an error.
                        let realized = op.realize(s).with_context(|| error::LabelTooLarge {
                            label: label.unwrap(),
                        })?;
                        self.pending.pop_front();
                        Node::Op(realized)
                    }
                    None => self.pending.pop_front().unwrap(),
                };

                popped.assemble(&mut self.ready);
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

    use std::io::Write;

    use tempfile::NamedTempFile;

    macro_rules! new_file {
        ($s:expr) => {{
            match NamedTempFile::new() {
                Ok(mut f) => {
                    write!(f, $s).expect("unable to write tmp file");
                    f
                }
                Err(e) => panic!("{}", e),
            }
        }};
    }

    macro_rules! nodes {
        ($($x:expr),+ $(,)?) => (
            vec![$(Node::from($x)),+]
        );
    }

    #[test]
    fn assemble_jumpdest_no_label() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let sz = asm.push_all(vec![Op::JumpDest(None)])?;
        assert_eq!(1, sz);
        assert!(asm.labels.is_empty());
        assert_eq!(asm.take(), hex!("5b"));
        Ok(())
    }

    #[test]
    fn assemble_jumpdest_with_label() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let op = Op::JumpDest(Some("lbl".into()));

        let sz = asm.push_all(vec![op])?;
        assert_eq!(1, sz);
        assert_eq!(asm.labels.len(), 1);
        assert_eq!(asm.labels.get("lbl"), Some(&0));
        assert_eq!(asm.take(), hex!("5b"));
        Ok(())
    }

    #[test]
    fn assemble_jumpdest_jump_with_label() -> Result<(), Error> {
        let ops = vec![Op::JumpDest(Some("lbl".into())), Op::Push1("lbl".into())];

        let mut asm = Assembler::new();
        let sz = asm.push_all(ops)?;
        assert_eq!(sz, 3);
        assert_eq!(asm.take(), hex!("5b6000"));

        Ok(())
    }

    #[test]
    fn assemble_jump_jumpdest_with_label() -> Result<(), Error> {
        let ops = vec![Op::Push1("lbl".into()), Op::JumpDest(Some("lbl".into()))];

        let mut asm = Assembler::new();
        let sz = asm.push_all(ops)?;
        assert_eq!(sz, 3);
        assert_eq!(asm.take(), hex!("60025b"));

        Ok(())
    }

    #[test]
    fn assemble_import() -> Result<(), Error> {
        let f = new_file!("push1 42");
        let nodes = nodes![
            Op::Push1(Imm::from(1)),
            Node::Import(f.path().to_owned()),
            Op::Push1(Imm::from(2)),
        ];
        let mut asm = Assembler::new();
        let sz = asm.push_all(nodes)?;
        assert_eq!(sz, 6);
        assert_eq!(asm.take(), hex!("6001602a6002"));

        Ok(())
    }

    #[test]
    fn assemble_include() -> Result<(), Error> {
        let f = new_file!(
            r#"
                jumpdest .a
                pc
                push1 .a
                jump
            "#
        );
        let nodes = nodes![
            Op::Push1(Imm::from(1)),
            Node::Include(f.path().to_owned()),
            Op::Push1(Imm::from(2)),
        ];
        let mut asm = Assembler::new();
        let sz = asm.push_all(nodes)?;
        assert_eq!(sz, 9);
        assert_eq!(asm.take(), hex!("60015b586000566002"));

        Ok(())
    }

    #[test]
    fn assemble_import_twice() -> Result<(), Error> {
        let f = new_file!(
            r#"
                jumpdest .a
                push1 .a
            "#
        );
        let nodes = nodes![
            Op::Push1(Imm::from(1)),
            Node::Import(f.path().to_owned()),
            Node::Import(f.path().to_owned()),
            Op::Push1(Imm::from(2)),
        ];
        let mut asm = Assembler::new();
        let err = asm.push_all(nodes).unwrap_err();

        assert_matches!(err, Error::DuplicateLabel { label, ..} if label == "a");

        Ok(())
    }

    #[test]
    fn assemble_include_hex() -> Result<(), Error> {
        let f = new_file!("deadbeef0102f6");
        let nodes = nodes![
            Op::Push1(Imm::from(1)),
            Node::IncludeHex(f.path().to_owned()),
            Op::Push1(Imm::from(2)),
        ];
        let mut asm = Assembler::new();
        let sz = asm.push_all(nodes)?;
        assert_eq!(sz, 11);
        assert_eq!(asm.take(), hex!("6001deadbeef0102f66002"));

        Ok(())
    }

    #[test]
    fn assemble_include_hex_label() -> Result<(), Error> {
        let f = new_file!("deadbeef0102f6");
        let nodes = nodes![
            Op::Push1(Imm::from(1)),
            Node::IncludeHex(f.path().to_owned()),
            Op::JumpDest(Some("a".into())),
            Op::Push1(Imm::Label("a".into())),
            Op::Push1(Imm::from(0xff)),
        ];
        let mut asm = Assembler::new();
        let sz = asm.push_all(nodes)?;
        assert_eq!(sz, 14);
        assert_eq!(asm.take(), hex!("6001deadbeef0102f65b600960ff"));

        Ok(())
    }

    #[test]
    fn assemble_label_too_large() {
        let mut nodes = vec![Node::Op(Op::GetPc); 255];
        nodes.push(Node::Op(Op::JumpDest(Some("b".into()))));
        nodes.push(Node::Op(Op::JumpDest(Some("a".into()))));
        nodes.push(Node::Op(Op::Push1(Imm::from("a"))));
        let mut asm = Assembler::new();
        let err = asm.push_all(nodes).unwrap_err();
        assert_matches!(err, Error::LabelTooLarge { label, .. } if label == "a");
    }

    #[test]
    fn assemble_label_just_right() -> Result<(), Error> {
        let mut nodes = vec![Node::Op(Op::GetPc); 255];
        nodes.push(Node::Op(Op::JumpDest(Some("b".into()))));
        nodes.push(Node::Op(Op::JumpDest(Some("a".into()))));
        nodes.push(Node::Op(Op::Push1(Imm::from("b"))));
        let mut asm = Assembler::new();
        let sz = asm.push_all(nodes)?;
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
