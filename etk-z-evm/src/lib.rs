mod constants;
mod execution;
mod memory;
mod ops;
mod stack;

use etk_asm::ops::ConcreteOp;
use z3::ast::{Ast, Int, BV};
use z3::{Context, Solver};

use self::constants::Constants;
use self::execution::Execution;

use std::ops::{Add, AddAssign};

fn to_bv<'ctx>(ctx: &'ctx Context, v: &[u8]) -> BV<'ctx> {
    const LEN: usize = 32;
    let mut buffer = [0u8; LEN];
    buffer[LEN - v.len()..LEN].copy_from_slice(v);

    BV::from_u64(
        ctx,
        u64::from_be_bytes(buffer[0..8].try_into().unwrap()),
        64,
    )
    .concat(&BV::from_u64(
        ctx,
        u64::from_be_bytes(buffer[8..16].try_into().unwrap()),
        64,
    ))
    .concat(&BV::from_u64(
        ctx,
        u64::from_be_bytes(buffer[16..24].try_into().unwrap()),
        64,
    ))
    .concat(&BV::from_u64(
        ctx,
        u64::from_be_bytes(buffer[24..32].try_into().unwrap()),
        64,
    ))
    .simplify()
}

#[derive(Debug, Ord, PartialOrd, Eq, PartialEq, Hash, Clone, Copy)]
pub struct Offset(pub u32);

impl AddAssign<u32> for Offset {
    fn add_assign(&mut self, rhs: u32) {
        self.0 += rhs;
    }
}

impl Add<u32> for Offset {
    type Output = Self;

    fn add(self, rhs: u32) -> Self {
        Offset(self.0 + rhs)
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub enum Run {
    Jump(Offset),
    Advance,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub enum Halt {
    Stop,
    Revert,
    StackUnderflow,
    StackOverflow,
    OutOfGas,
    InvalidOpcode,
    InvalidJumpDest,
    CallStackTooDeep,
    InsufficientFunds,
    WriteInStaticContext,
    ReturnDataOutOfBounds,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub enum Outcome {
    Halt(Halt),
    Run(Run),
}

#[derive(Debug)]
pub struct Step<'ctx> {
    outcomes: smallvec::SmallVec<[Outcome; 2]>,
    previous: ZEvm<'ctx>,
}

impl<'ctx> Step<'ctx> {
    pub fn is_empty(&self) -> bool {
        self.outcomes.is_empty()
    }

    pub fn len(&self) -> usize {
        self.outcomes.len()
    }

    pub fn apply(self, run: Run) -> Result<ZEvm<'ctx>, crate::memory::Error> {
        if !self.outcomes.contains(&Outcome::Run(run)) {
            panic!("`{:?}` was not a possible outcome", run);
        }

        self.previous.solver.push();

        let mut execution = self.previous.execution().clone();

        match run {
            Run::Advance => {
                execution.instruction += 1;
                execution.pc += self.previous.next_op().size();
            }
            Run::Jump(dest) => {
                execution.instruction = self.previous.constants.destination(dest).unwrap();
                execution.pc = dest;
            }
        }

        match self.previous.next_op() {
            ConcreteOp::Stop => self.stop(run, &mut execution),
            ConcreteOp::Add => self.add(run, &mut execution),
            // ...
            ConcreteOp::MLoad => self.mload(run, &self.previous.solver, &mut execution)?,
            ConcreteOp::MStore => self.mstore(run, &self.previous.solver, &mut execution)?,
            // ...
            ConcreteOp::JumpI => self.jumpi(run, &mut execution),
            // ...
            ConcreteOp::JumpDest => self.jumpdest(run, &mut execution),
            ConcreteOp::Push1(v) => self.push(&v, run, &mut execution),
            ConcreteOp::Push2(v) => self.push(&v, run, &mut execution),
            ConcreteOp::Push3(v) => self.push(&v, run, &mut execution),
            ConcreteOp::Push4(v) => self.push(&v, run, &mut execution),
            ConcreteOp::Push5(v) => self.push(&v, run, &mut execution),
            ConcreteOp::Push6(v) => self.push(&v, run, &mut execution),
            ConcreteOp::Push7(v) => self.push(&v, run, &mut execution),
            ConcreteOp::Push8(v) => self.push(&v, run, &mut execution),
            ConcreteOp::Push9(v) => self.push(&v, run, &mut execution),
            ConcreteOp::Push10(v) => self.push(&v, run, &mut execution),
            ConcreteOp::Push11(v) => self.push(&v, run, &mut execution),
            ConcreteOp::Push12(v) => self.push(&v, run, &mut execution),
            ConcreteOp::Push13(v) => self.push(&v, run, &mut execution),
            ConcreteOp::Push14(v) => self.push(&v, run, &mut execution),
            ConcreteOp::Push15(v) => self.push(&v, run, &mut execution),
            ConcreteOp::Push16(v) => self.push(&v, run, &mut execution),
            ConcreteOp::Push17(v) => self.push(&v, run, &mut execution),
            ConcreteOp::Push18(v) => self.push(&v, run, &mut execution),
            ConcreteOp::Push19(v) => self.push(&v, run, &mut execution),
            ConcreteOp::Push20(v) => self.push(&v, run, &mut execution),
            ConcreteOp::Push21(v) => self.push(&v, run, &mut execution),
            ConcreteOp::Push22(v) => self.push(&v, run, &mut execution),
            ConcreteOp::Push23(v) => self.push(&v, run, &mut execution),
            ConcreteOp::Push24(v) => self.push(&v, run, &mut execution),
            ConcreteOp::Push25(v) => self.push(&v, run, &mut execution),
            ConcreteOp::Push26(v) => self.push(&v, run, &mut execution),
            ConcreteOp::Push27(v) => self.push(&v, run, &mut execution),
            ConcreteOp::Push28(v) => self.push(&v, run, &mut execution),
            ConcreteOp::Push29(v) => self.push(&v, run, &mut execution),
            ConcreteOp::Push30(v) => self.push(&v, run, &mut execution),
            ConcreteOp::Push31(v) => self.push(&v, run, &mut execution),
            ConcreteOp::Push32(v) => self.push(&v, run, &mut execution),
            _ => unimplemented!(),
        }

        let mut executions = self.previous.executions;
        executions.push(execution);

        Ok(ZEvm {
            constants: self.previous.constants,
            executions,
            ctx: self.previous.ctx,
            solver: self.previous.solver,
        })
    }

    pub fn cancel(self) -> ZEvm<'ctx> {
        // TODO: Bikeshed a better name. `into_something` maybe.
        self.previous
    }

    pub fn outcomes(&self) -> impl Iterator<Item = Outcome> + '_ {
        self.outcomes.iter().copied()
    }
}

#[derive(Debug)]
pub struct ZEvm<'ctx> {
    constants: Constants,
    executions: Vec<Execution<'ctx>>,
    ctx: &'ctx Context,
    solver: Solver<'ctx>,
}

impl<'ctx> ZEvm<'ctx> {
    pub fn new(ctx: &'ctx Context, ops: Vec<ConcreteOp>) -> Self {
        Self {
            constants: Constants::new(ops),
            executions: vec![Execution::new(ctx)],
            ctx,
            solver: Solver::new(ctx),
        }
    }

    pub fn with_gas(ctx: &'ctx Context, ops: Vec<ConcreteOp>, gas: u64) -> Self {
        let new = Self::new(ctx, ops);
        let gas_remaining = &new.execution().gas_remaining;
        new.solver
            .assert(&gas_remaining._eq(&Int::from_u64(ctx, gas)));
        new
    }

    fn execution(&self) -> &Execution<'ctx> {
        self.executions.last().unwrap()
    }

    pub fn next_op(&self) -> ConcreteOp {
        self.execution().op(&self.constants)
    }

    pub fn step(self) -> Step<'ctx> {
        let mut step = match self.next_op() {
            ConcreteOp::Stop => self.stop(),
            ConcreteOp::Add => self.add(),
            // ...
            ConcreteOp::MLoad => self.mload(),
            ConcreteOp::MStore => self.mstore(),
            // ...
            ConcreteOp::JumpI => self.jumpi(),
            // ...
            ConcreteOp::JumpDest => self.jumpdest(),
            ConcreteOp::Push1(_) => self.push(),
            ConcreteOp::Push2(_) => self.push(),
            ConcreteOp::Push3(_) => self.push(),
            ConcreteOp::Push4(_) => self.push(),
            ConcreteOp::Push5(_) => self.push(),
            ConcreteOp::Push6(_) => self.push(),
            ConcreteOp::Push7(_) => self.push(),
            ConcreteOp::Push8(_) => self.push(),
            ConcreteOp::Push9(_) => self.push(),
            ConcreteOp::Push10(_) => self.push(),
            ConcreteOp::Push11(_) => self.push(),
            ConcreteOp::Push12(_) => self.push(),
            ConcreteOp::Push13(_) => self.push(),
            ConcreteOp::Push14(_) => self.push(),
            ConcreteOp::Push15(_) => self.push(),
            ConcreteOp::Push16(_) => self.push(),
            ConcreteOp::Push17(_) => self.push(),
            ConcreteOp::Push18(_) => self.push(),
            ConcreteOp::Push19(_) => self.push(),
            ConcreteOp::Push20(_) => self.push(),
            ConcreteOp::Push21(_) => self.push(),
            ConcreteOp::Push22(_) => self.push(),
            ConcreteOp::Push23(_) => self.push(),
            ConcreteOp::Push24(_) => self.push(),
            ConcreteOp::Push25(_) => self.push(),
            ConcreteOp::Push26(_) => self.push(),
            ConcreteOp::Push27(_) => self.push(),
            ConcreteOp::Push28(_) => self.push(),
            ConcreteOp::Push29(_) => self.push(),
            ConcreteOp::Push30(_) => self.push(),
            ConcreteOp::Push31(_) => self.push(),
            ConcreteOp::Push32(_) => self.push(),
            _ => unimplemented!(),
        };

        step.outcomes.sort();

        step
    }
}
