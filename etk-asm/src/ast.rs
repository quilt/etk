use crate::ops::Op;
use std::path::PathBuf;

#[derive(Debug, Clone, PartialEq)]
pub enum Node {
    Op(Op),
    Raw(Vec<u8>),
    Include(PathBuf),
    IncludeAsm(PathBuf),
}

impl Node {
    pub(crate) fn assemble(&self, buf: &mut Vec<u8>) {
        match self {
            Self::Op(op) => op.assemble(buf),
            _ => unimplemented!(),
        }
    }
}

impl From<Op> for Node {
    fn from(op: Op) -> Self {
        Node::Op(op)
    }
}
