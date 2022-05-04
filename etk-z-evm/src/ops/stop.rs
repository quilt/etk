use crate::execution::Execution;
use crate::{Halt, Outcome, Run, Step, ZEvm};

use smallvec::smallvec;

impl<'ctx, S> ZEvm<'ctx, S> {
    pub(crate) fn stop(self) -> Step<'ctx, S> {
        Step {
            outcomes: smallvec![Outcome::Halt(Halt::Stop)],
            previous: self,
        }
    }
}

impl<'ctx, S> Step<'ctx, S> {
    pub(crate) fn stop(&self, _: Run, _: &mut Execution<'ctx, S>) {
        unreachable!()
    }
}
