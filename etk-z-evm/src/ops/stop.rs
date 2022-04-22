use crate::execution::Execution;
use crate::{Halt, Outcome, Run, Step, ZEvm};

use smallvec::smallvec;

impl<'ctx> ZEvm<'ctx> {
    pub(crate) fn stop(self) -> Step<'ctx> {
        Step {
            outcomes: smallvec![Outcome::Halt(Halt::Stop)],
            previous: self,
        }
    }
}

impl<'ctx> Step<'ctx> {
    pub(crate) fn stop(&self, _: Run, _: &mut Execution<'ctx>) {
        unreachable!()
    }
}
