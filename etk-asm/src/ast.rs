use crate::ops::{LabelOp, Op};
use std::path::PathBuf;

#[derive(Debug, Clone, PartialEq)]
pub enum Node {
    Op(LabelOp),
    Raw(Vec<u8>),
    Import(PathBuf),
    Include(PathBuf),
    IncludeHex(PathBuf),
}

impl From<LabelOp> for Node {
    fn from(op: LabelOp) -> Self {
        Node::Op(op)
    }
}

impl From<Op> for Node {
    fn from(op: Op) -> Self {
        Node::Op(LabelOp::new(op))
    }
}
