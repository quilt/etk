mod constants;
pub mod error;
mod execution;
mod memory;
mod ops;
pub mod resolve;
mod stack;
pub mod storage;

use crate::constants::Constants;
use crate::error::Error;
use crate::execution::Execution;
use crate::storage::Storage;

use etk_ops::london::*;

use snafu::ResultExt;

use std::ops::{Add, AddAssign};

use z3::ast::{Ast, Int, BV};
use z3::{Context, Solver};

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
pub struct Offset(pub u64);

impl AddAssign<u64> for Offset {
    fn add_assign(&mut self, rhs: u64) {
        self.0 += rhs;
    }
}

impl Add<u64> for Offset {
    type Output = Self;

    fn add(self, rhs: u64) -> Self {
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
pub struct Step<'ctx, S> {
    outcomes: smallvec::SmallVec<[Outcome; 2]>,
    previous: ZEvm<'ctx, S>,
}

impl<'ctx, S> Step<'ctx, S> {
    pub fn is_empty(&self) -> bool {
        self.outcomes.is_empty()
    }

    pub fn len(&self) -> usize {
        self.outcomes.len()
    }
}

impl<'ctx, S> Step<'ctx, S>
where
    S: Storage<'ctx>,
{
    pub fn apply(self, run: Run) -> Result<ZEvm<'ctx, S>, Error<S::Error>> {
        if !self.outcomes.contains(&Outcome::Run(run)) {
            panic!("`{:?}` was not a possible outcome", run);
        }

        self.previous.solver.push();

        let mut execution = self.previous.execution().clone();
        execution.storage.reset();

        match run {
            Run::Advance => {
                execution.instruction += 1;
                execution.pc += self.previous.next_op().size().try_into().unwrap();
            }
            Run::Jump(dest) => {
                execution.instruction = self.previous.constants.destination(dest).unwrap();
                execution.pc = dest;
            }
        }

        match self.previous.next_op() {
            Op::Stop(_) => self.stop(run, &mut execution),
            Op::Add(_) => self.add(run, &mut execution),
            // ...
            Op::MLoad(_) => self
                .mload(run, &self.previous.solver, &mut execution)
                .context(error::MemorySnafu)?,
            Op::MStore(_) => self
                .mstore(run, &self.previous.solver, &mut execution)
                .context(error::MemorySnafu)?,
            // ...
            Op::SStore(_) => self
                .sstore(run, &self.previous.solver, &mut execution)
                .context(error::StorageSnafu)?,
            // ...
            Op::JumpI(_) => self.jumpi(run, &mut execution),
            // ...
            Op::JumpDest(_) => self.jumpdest(run, &mut execution),
            Op::Push1(v) => self.push(&v.0, run, &mut execution),
            Op::Push2(v) => self.push(&v.0, run, &mut execution),
            Op::Push3(v) => self.push(&v.0, run, &mut execution),
            Op::Push4(v) => self.push(&v.0, run, &mut execution),
            Op::Push5(v) => self.push(&v.0, run, &mut execution),
            Op::Push6(v) => self.push(&v.0, run, &mut execution),
            Op::Push7(v) => self.push(&v.0, run, &mut execution),
            Op::Push8(v) => self.push(&v.0, run, &mut execution),
            Op::Push9(v) => self.push(&v.0, run, &mut execution),
            Op::Push10(v) => self.push(&v.0, run, &mut execution),
            Op::Push11(v) => self.push(&v.0, run, &mut execution),
            Op::Push12(v) => self.push(&v.0, run, &mut execution),
            Op::Push13(v) => self.push(&v.0, run, &mut execution),
            Op::Push14(v) => self.push(&v.0, run, &mut execution),
            Op::Push15(v) => self.push(&v.0, run, &mut execution),
            Op::Push16(v) => self.push(&v.0, run, &mut execution),
            Op::Push17(v) => self.push(&v.0, run, &mut execution),
            Op::Push18(v) => self.push(&v.0, run, &mut execution),
            Op::Push19(v) => self.push(&v.0, run, &mut execution),
            Op::Push20(v) => self.push(&v.0, run, &mut execution),
            Op::Push21(v) => self.push(&v.0, run, &mut execution),
            Op::Push22(v) => self.push(&v.0, run, &mut execution),
            Op::Push23(v) => self.push(&v.0, run, &mut execution),
            Op::Push24(v) => self.push(&v.0, run, &mut execution),
            Op::Push25(v) => self.push(&v.0, run, &mut execution),
            Op::Push26(v) => self.push(&v.0, run, &mut execution),
            Op::Push27(v) => self.push(&v.0, run, &mut execution),
            Op::Push28(v) => self.push(&v.0, run, &mut execution),
            Op::Push29(v) => self.push(&v.0, run, &mut execution),
            Op::Push30(v) => self.push(&v.0, run, &mut execution),
            Op::Push31(v) => self.push(&v.0, run, &mut execution),
            Op::Push32(v) => self.push(&v.0, run, &mut execution),
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

    pub fn cancel(self) -> ZEvm<'ctx, S> {
        // TODO: Bikeshed a better name. `into_something` maybe.
        self.previous
    }

    pub fn outcomes(&self) -> impl Iterator<Item = Outcome> + '_ {
        self.outcomes.iter().copied()
    }
}

#[derive(Debug)]
pub struct Builder<'ctx, S> {
    ctx: &'ctx Context,
    ops: Vec<Op<[u8]>>,
    storage: S,
    gas: Option<u64>,
}

impl<'ctx, S> Builder<'ctx, S>
where
    S: Default,
{
    pub fn new(ctx: &'ctx Context, ops: Vec<Op<[u8]>>) -> Self {
        Self::with_storage(ctx, ops, S::default())
    }
}

impl<'ctx, S> Builder<'ctx, S> {
    pub fn with_storage(ctx: &'ctx Context, ops: Vec<Op<[u8]>>, storage: S) -> Self {
        Self {
            ctx,
            ops,
            storage,
            gas: None,
        }
    }

    pub fn set_gas(mut self, gas: u64) -> Self {
        self.gas = Some(gas);
        self
    }

    pub fn build(self) -> ZEvm<'ctx, S> {
        let new = ZEvm {
            constants: Constants::new(self.ops),
            executions: vec![Execution::new(self.ctx, self.storage)],
            ctx: self.ctx,
            solver: Solver::new(self.ctx),
        };

        if let Some(gas) = self.gas {
            let gas_remaining = &new.execution().gas_remaining;
            new.solver
                .assert(&gas_remaining._eq(&Int::from_u64(self.ctx, gas)));
        }

        new
    }
}

#[derive(Debug)]
pub struct ZEvm<'ctx, S> {
    constants: Constants,
    executions: Vec<Execution<'ctx, S>>,
    ctx: &'ctx Context,
    solver: Solver<'ctx>,
}

impl<'ctx, S> ZEvm<'ctx, S> {
    fn execution(&self) -> &Execution<'ctx, S> {
        self.executions.last().unwrap()
    }

    pub fn next_op(&self) -> Op<[u8]> {
        self.execution().op(&self.constants)
    }
}

impl<'ctx, S> ZEvm<'ctx, S>
where
    S: Storage<'ctx>,
{
    pub fn step(self) -> Step<'ctx, S> {
        let mut step = match self.next_op() {
            Op::Stop(_) => self.stop(),
            Op::Add(_) => self.add(),
            // ...
            Op::MLoad(_) => self.mload(),
            Op::MStore(_) => self.mstore(),
            // ...
            Op::SStore(_) => self.sstore(),
            // ...
            Op::JumpI(_) => self.jumpi(),
            // ...
            Op::JumpDest(_) => self.jumpdest(),
            Op::Push1(_) => self.push(),
            Op::Push2(_) => self.push(),
            Op::Push3(_) => self.push(),
            Op::Push4(_) => self.push(),
            Op::Push5(_) => self.push(),
            Op::Push6(_) => self.push(),
            Op::Push7(_) => self.push(),
            Op::Push8(_) => self.push(),
            Op::Push9(_) => self.push(),
            Op::Push10(_) => self.push(),
            Op::Push11(_) => self.push(),
            Op::Push12(_) => self.push(),
            Op::Push13(_) => self.push(),
            Op::Push14(_) => self.push(),
            Op::Push15(_) => self.push(),
            Op::Push16(_) => self.push(),
            Op::Push17(_) => self.push(),
            Op::Push18(_) => self.push(),
            Op::Push19(_) => self.push(),
            Op::Push20(_) => self.push(),
            Op::Push21(_) => self.push(),
            Op::Push22(_) => self.push(),
            Op::Push23(_) => self.push(),
            Op::Push24(_) => self.push(),
            Op::Push25(_) => self.push(),
            Op::Push26(_) => self.push(),
            Op::Push27(_) => self.push(),
            Op::Push28(_) => self.push(),
            Op::Push29(_) => self.push(),
            Op::Push30(_) => self.push(),
            Op::Push31(_) => self.push(),
            Op::Push32(_) => self.push(),
            _ => unimplemented!(),
        };

        step.outcomes.sort();

        step
    }
}
