use std::path::PathBuf;

use crate::ops::{Abstract, AbstractOp, ExpressionMacroDefinition, InstructionMacroDefinition};
use etk_ops::cancun::Op as CancunOp;
use etk_ops::london::Op as LondonOp;
use etk_ops::shanghai::Op as ShanghaiOp;
use etk_ops::HardForkDirective;

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Node {
    Op(AbstractOp),
    Import(PathBuf),
    Include(PathBuf),
    IncludeHex(PathBuf),
    HardforkMacro((HardForkDirective, Option<HardForkDirective>)),
}
impl From<CancunOp<Abstract>> for Node {
    fn from(op: CancunOp<Abstract>) -> Self {
        Node::Op(AbstractOp::Op(etk_ops::HardForkOp::Cancun(op)))
    }
}

impl From<ShanghaiOp<Abstract>> for Node {
    fn from(op: ShanghaiOp<Abstract>) -> Self {
        Node::Op(AbstractOp::Op(etk_ops::HardForkOp::Shanghai(op)))
    }
}

impl From<LondonOp<Abstract>> for Node {
    fn from(op: LondonOp<Abstract>) -> Self {
        Node::Op(AbstractOp::Op(etk_ops::HardForkOp::London(op)))
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
