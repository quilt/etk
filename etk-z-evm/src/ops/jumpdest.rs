use crate::execution::Execution;
use crate::{Halt, Outcome, Run, Step, ZEvm};

use smallvec::SmallVec;

use z3::ast::Int;
use z3::SatResult;

impl<'ctx, S> ZEvm<'ctx, S> {
    pub(crate) fn jumpdest(self) -> Step<'ctx, S> {
        let execution = self.execution();

        let gas_cost = Int::from_u64(self.ctx, 1);
        let covers_cost = execution.gas_remaining.ge(&gas_cost);

        let mut outcomes = SmallVec::new();

        if SatResult::Sat == self.solver.check_assumptions(&[covers_cost.not()]) {
            outcomes.push(Outcome::Halt(Halt::OutOfGas));
        }

        if SatResult::Sat == self.solver.check_assumptions(&[covers_cost]) {
            outcomes.push(Outcome::Run(Run::Advance));
        }

        Step {
            previous: self,
            outcomes,
        }
    }
}

impl<'ctx, S> Step<'ctx, S> {
    pub(crate) fn jumpdest(&self, run: Run, execution: &mut Execution<'ctx, S>) {
        if run != Run::Advance {
            panic!("invalid run for jumpdest: {:?}", run);
        }

        let gas_cost = Int::from_u64(self.previous.ctx, 1);
        execution.gas_remaining -= gas_cost;
    }
}

#[cfg(test)]
mod tests {
    use crate::storage::InMemory;
    use crate::Builder;

    use etk_ops::london::*;

    use super::*;

    use z3::ast::{Ast, BV};
    use z3::{Config, Context};

    #[test]
    fn not_enough_gas() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let evm = Builder::<'_, InMemory>::new(&ctx, vec![JumpDest.into()])
            .set_gas(0)
            .build();

        let step = evm.step();
        assert_eq!(step.len(), 1);

        let outcomes: Vec<_> = step.outcomes().collect();

        assert_eq!(outcomes[0], Outcome::Halt(Halt::OutOfGas));
    }

    #[test]
    fn advance() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let evm = Builder::<'_, InMemory>::new(&ctx, vec![JumpDest.into()])
            .set_gas(1)
            .build();

        let step = evm.step();
        assert_eq!(step.len(), 1);

        let outcomes: Vec<_> = step.outcomes().collect();

        assert_eq!(outcomes[0], Outcome::Run(Run::Advance));

        let next = step.apply(Run::Advance).unwrap();
        assert_eq!(next.executions.len(), 2);

        let result = next.solver.check_assumptions(&[next.executions[1]
            .gas_remaining
            ._eq(&Int::from_u64(&ctx, 0))]);

        assert_eq!(SatResult::Sat, result);

        let result = next.solver.check_assumptions(&[next.executions[1]
            .gas_remaining
            ._eq(&Int::from_u64(&ctx, 0))
            .not()]);

        assert_eq!(SatResult::Unsat, result);
    }
}
