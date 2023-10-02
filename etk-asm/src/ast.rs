use crate::ops::{Abstract, AbstractOp, ExpressionMacroDefinition, InstructionMacroDefinition};
use etk_ops::cancun::Op;

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Node {
    Op(AbstractOp),
    //Raw(Vec<u8>),
    //Import(Vec<Node>),
    Include(Vec<Node>),
    IncludeHex(Vec<u8>),
}

impl From<Op<Abstract>> for Node {
    fn from(op: Op<Abstract>) -> Self {
        Node::Op(AbstractOp::Op(op))
    }
}

impl From<AbstractOp> for Node {
    fn from(op: AbstractOp) -> Self {
        Node::Op(op)
    }
}

impl From<InstructionMacroDefinition> for Node {
    fn from(item: InstructionMacroDefinition) -> Self {
        Node::Op(item.into())
    }
}

impl From<ExpressionMacroDefinition> for Node {
    fn from(item: ExpressionMacroDefinition) -> Self {
        Node::Op(item.into())
    }
}
