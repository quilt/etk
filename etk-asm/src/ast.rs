use crate::ops::{AbstractOp, Op};
use std::path::PathBuf;

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Node {
    Op(AbstractOp),
    Raw(Vec<u8>),
    Import(PathBuf),
    Include(PathBuf),
    IncludeHex(PathBuf),
}

impl From<Op> for Node {
    fn from(op: Op) -> Self {
        Node::Op(AbstractOp::Op(op))
    }
}

impl From<AbstractOp> for Node {
    fn from(op: AbstractOp) -> Self {
        Node::Op(op)
    }
}
