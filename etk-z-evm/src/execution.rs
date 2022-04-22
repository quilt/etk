use etk_asm::ops::ConcreteOp;
use z3::ast::Int;
use z3::Context;

use crate::constants::Constants;
use crate::memory::Memory;
use crate::stack::Stack;
use crate::Offset;

#[derive(Debug, Clone)]
pub struct Execution<'ctx> {
    pub instruction: usize,
    pub pc: Offset,
    pub stack: Stack<'ctx>,
    pub memory: Memory<'ctx>,
    pub gas_remaining: Int<'ctx>,
}

impl<'ctx> Execution<'ctx> {
    pub fn new(ctx: &'ctx Context) -> Self {
        Self {
            instruction: 0,
            pc: Offset(0),
            stack: Default::default(),
            memory: Default::default(),
            gas_remaining: Int::fresh_const(ctx, "gas"),
        }
    }

    pub fn op(&self, constants: &Constants) -> ConcreteOp {
        constants.op(self.instruction)
    }
}
