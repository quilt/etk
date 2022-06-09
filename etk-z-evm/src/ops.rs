pub mod add;
pub mod jumpdest;
pub mod jumpi;
pub mod mload;
pub mod mstore;
pub mod push;
pub mod sstore;
pub mod stop;

use crate::error::Error;
use crate::execution::Execution;
use crate::storage::Storage;
use crate::{Outcome, Run, ZEvm};

use etk_ops::london::Op;
use etk_ops::Immediates;
use smallvec::SmallVec;
use z3::{Context, Solver};

pub(crate) trait SymbolicOp {
    fn outcomes<'ctx, S>(&self, evm: &ZEvm<'ctx, S>) -> SmallVec<[Outcome; 2]>
    where
        S: Storage<'ctx>;

    fn execute<'ctx, S>(
        &self,
        context: &'ctx Context,
        solver: &Solver<'ctx>,
        run: Run,
        execution: &mut Execution<'ctx, S>,
    ) -> Result<(), Error<S::Error>>
    where
        S: Storage<'ctx>;
}

impl<T> SymbolicOp for Op<T>
where
    T: ?Sized + Immediates<ImmediateRef = [u8]>,
{
    fn outcomes<'ctx, S>(&self, evm: &ZEvm<'ctx, S>) -> SmallVec<[Outcome; 2]>
    where
        S: Storage<'ctx>,
    {
        match self {
            Self::Stop(o) => o.outcomes(evm),
            Self::Add(o) => o.outcomes(evm),
            // ...
            Self::MLoad(o) => o.outcomes(evm),
            Self::MStore(o) => o.outcomes(evm),
            // ...
            Self::SStore(o) => o.outcomes(evm),
            // ...
            Self::JumpI(o) => o.outcomes(evm),
            // ...
            Self::JumpDest(o) => o.outcomes(evm),
            Self::Push1(o) => o.outcomes(evm),
            Self::Push2(o) => o.outcomes(evm),
            Self::Push3(o) => o.outcomes(evm),
            Self::Push4(o) => o.outcomes(evm),
            Self::Push5(o) => o.outcomes(evm),
            Self::Push6(o) => o.outcomes(evm),
            Self::Push7(o) => o.outcomes(evm),
            Self::Push8(o) => o.outcomes(evm),
            Self::Push9(o) => o.outcomes(evm),
            Self::Push10(o) => o.outcomes(evm),
            Self::Push11(o) => o.outcomes(evm),
            Self::Push12(o) => o.outcomes(evm),
            Self::Push13(o) => o.outcomes(evm),
            Self::Push14(o) => o.outcomes(evm),
            Self::Push15(o) => o.outcomes(evm),
            Self::Push16(o) => o.outcomes(evm),
            Self::Push17(o) => o.outcomes(evm),
            Self::Push18(o) => o.outcomes(evm),
            Self::Push19(o) => o.outcomes(evm),
            Self::Push20(o) => o.outcomes(evm),
            Self::Push21(o) => o.outcomes(evm),
            Self::Push22(o) => o.outcomes(evm),
            Self::Push23(o) => o.outcomes(evm),
            Self::Push24(o) => o.outcomes(evm),
            Self::Push25(o) => o.outcomes(evm),
            Self::Push26(o) => o.outcomes(evm),
            Self::Push27(o) => o.outcomes(evm),
            Self::Push28(o) => o.outcomes(evm),
            Self::Push29(o) => o.outcomes(evm),
            Self::Push30(o) => o.outcomes(evm),
            Self::Push31(o) => o.outcomes(evm),
            Self::Push32(o) => o.outcomes(evm),
            // ...
            _ => todo!(),
        }
    }

    fn execute<'ctx, S>(
        &self,
        context: &'ctx Context,
        solver: &Solver<'ctx>,
        run: Run,
        execution: &mut Execution<'ctx, S>,
    ) -> Result<(), Error<S::Error>>
    where
        S: Storage<'ctx>,
    {
        match self {
            Self::Stop(o) => o.execute(context, solver, run, execution),
            Self::Add(o) => o.execute(context, solver, run, execution),
            // ...
            Self::MLoad(o) => o.execute(context, solver, run, execution),
            Self::MStore(o) => o.execute(context, solver, run, execution),
            // ...
            Self::SStore(o) => o.execute(context, solver, run, execution),
            // ...
            Self::JumpI(o) => o.execute(context, solver, run, execution),
            // ...
            Self::JumpDest(o) => o.execute(context, solver, run, execution),
            Self::Push1(o) => o.execute(context, solver, run, execution),
            Self::Push2(o) => o.execute(context, solver, run, execution),
            Self::Push3(o) => o.execute(context, solver, run, execution),
            Self::Push4(o) => o.execute(context, solver, run, execution),
            Self::Push5(o) => o.execute(context, solver, run, execution),
            Self::Push6(o) => o.execute(context, solver, run, execution),
            Self::Push7(o) => o.execute(context, solver, run, execution),
            Self::Push8(o) => o.execute(context, solver, run, execution),
            Self::Push9(o) => o.execute(context, solver, run, execution),
            Self::Push10(o) => o.execute(context, solver, run, execution),
            Self::Push11(o) => o.execute(context, solver, run, execution),
            Self::Push12(o) => o.execute(context, solver, run, execution),
            Self::Push13(o) => o.execute(context, solver, run, execution),
            Self::Push14(o) => o.execute(context, solver, run, execution),
            Self::Push15(o) => o.execute(context, solver, run, execution),
            Self::Push16(o) => o.execute(context, solver, run, execution),
            Self::Push17(o) => o.execute(context, solver, run, execution),
            Self::Push18(o) => o.execute(context, solver, run, execution),
            Self::Push19(o) => o.execute(context, solver, run, execution),
            Self::Push20(o) => o.execute(context, solver, run, execution),
            Self::Push21(o) => o.execute(context, solver, run, execution),
            Self::Push22(o) => o.execute(context, solver, run, execution),
            Self::Push23(o) => o.execute(context, solver, run, execution),
            Self::Push24(o) => o.execute(context, solver, run, execution),
            Self::Push25(o) => o.execute(context, solver, run, execution),
            Self::Push26(o) => o.execute(context, solver, run, execution),
            Self::Push27(o) => o.execute(context, solver, run, execution),
            Self::Push28(o) => o.execute(context, solver, run, execution),
            Self::Push29(o) => o.execute(context, solver, run, execution),
            Self::Push30(o) => o.execute(context, solver, run, execution),
            Self::Push31(o) => o.execute(context, solver, run, execution),
            Self::Push32(o) => o.execute(context, solver, run, execution),
            // ...
            _ => todo!(),
        }
    }
}
