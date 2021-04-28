use crate::ops::Op;
use std::path::PathBuf;

#[derive(Debug, Clone, PartialEq)]
pub enum Node {
    Op(Op),
    Raw(Vec<u8>),
    Import(PathBuf),
    Include(PathBuf),
    IncludeHex(PathBuf),
}

impl From<Op> for Node {
    fn from(op: Op) -> Self {
        Node::Op(op)
    }
}
