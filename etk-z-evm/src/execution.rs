use etk_ops::london::Op;

use crate::constants::Constants;
use crate::memory::Memory;
use crate::stack::Stack;
use crate::storage::Delta;
use crate::{to_bv, Offset};

use z3::ast::{Ast, Bool, Int, BV};
use z3::{Context, Solver};

#[derive(Debug)]
pub(crate) struct Execution<'ctx, S> {
    pub instruction: usize,
    pub pc: Offset,
    pub stack: Stack<'ctx>,
    pub memory: Memory<'ctx>,
    pub gas_remaining: Int<'ctx>,
    pub storage: Delta<'ctx, S>,

    /// Address of the account who's state would be accessed with `sload` & `store`.
    pub state_address: BV<'ctx>,

    /// Storage slots that have been accessed during this transaction.
    pub warm_slots: Vec<(BV<'ctx>, BV<'ctx>)>,
}

impl<'ctx, S> Clone for Execution<'ctx, S> {
    fn clone(&self) -> Self {
        Self {
            instruction: self.instruction,
            pc: self.pc,
            stack: self.stack.clone(),
            memory: self.memory.clone(),
            gas_remaining: self.gas_remaining.clone(),
            storage: self.storage.clone(),
            state_address: self.state_address.clone(),
            warm_slots: self.warm_slots.clone(),
        }
    }
}

impl<'ctx, S> Execution<'ctx, S> {
    pub fn new(ctx: &'ctx Context, storage: S) -> Self {
        Self {
            instruction: 0,
            pc: Offset(0),
            stack: Default::default(),
            memory: Default::default(),
            gas_remaining: Int::fresh_const(ctx, "gas"),
            storage: Delta::new(storage),
            state_address: to_bv(ctx, &[0xAB; 32]), // TODO
            warm_slots: Default::default(),
        }
    }

    pub fn op(&self, constants: &Constants) -> Op<[u8]> {
        constants.op(self.instruction)
    }

    pub fn is_warm_slot(&self, slot: &BV<'ctx>) -> Bool<'ctx> {
        let mut result = Bool::from_bool(self.state_address.get_ctx(), false);

        for warm_slot in &self.warm_slots {
            let matches = warm_slot.0._eq(&self.state_address) & warm_slot.1._eq(slot);
            result |= matches;
        }

        result.simplify()
    }
}
