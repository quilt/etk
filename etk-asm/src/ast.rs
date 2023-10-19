use std::path::PathBuf;

use crate::ops::{Abstract, AbstractOp, ExpressionMacroDefinition, InstructionMacroDefinition};
use etk_ops::cancun::Op as CancunOp;
use etk_ops::london::Op as LondonOp;
use etk_ops::prague::Op as PragueOp;
use etk_ops::shanghai::Op as ShanghaiOp;

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Node {
    Op(AbstractOp),
    Import(PathBuf),
    Include(PathBuf),
    IncludeHex(PathBuf),
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

impl From<PragueOp<Abstract>> for Node {
    fn from(op: PragueOp<Abstract>) -> Self {
        Node::Op(AbstractOp::Op(etk_ops::HardForkOp::Prague(op)))
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
