use crate::error::Error;
use crate::execution::Execution;
use crate::storage::Storage;
use crate::{Halt, Outcome, Run, ZEvm};

use etk_ops::london::Stop;

use smallvec::smallvec;

use super::SymbolicOp;

use z3::{Context, Solver};

impl SymbolicOp for Stop {
    fn outcomes<'ctx, S>(&self, _: &ZEvm<'ctx, S>) -> smallvec::SmallVec<[Outcome; 2]>
    where
        S: crate::storage::Storage<'ctx>,
    {
        smallvec![Outcome::Halt(Halt::Stop)]
    }

    fn execute<'ctx, S>(
        &self,
        _: &'ctx Context,
        _: &Solver<'ctx>,
        _: Run,
        _: &mut Execution<'ctx, S>,
    ) -> Result<(), Error<S::Error>>
    where
        S: Storage<'ctx>,
    {
        unreachable!()
    }
}
