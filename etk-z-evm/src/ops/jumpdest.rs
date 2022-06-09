use crate::error::Error;
use crate::execution::Execution;
use crate::storage::Storage;
use crate::{Halt, Outcome, Run, ZEvm};

use etk_ops::london::JumpDest;

use smallvec::SmallVec;

use super::SymbolicOp;

use z3::ast::Int;
use z3::{Context, SatResult, Solver};

impl SymbolicOp for JumpDest {
    fn outcomes<'ctx, S>(&self, evm: &ZEvm<'ctx, S>) -> SmallVec<[Outcome; 2]>
    where
        S: Storage<'ctx>,
    {
        let execution = evm.execution();

        let gas_cost = Int::from_u64(evm.ctx, 1);
        let covers_cost = execution.gas_remaining.ge(&gas_cost);

        let mut outcomes = SmallVec::new();

        if SatResult::Sat == evm.solver.check_assumptions(&[covers_cost.not()]) {
            outcomes.push(Outcome::Halt(Halt::OutOfGas));
        }

        if SatResult::Sat == evm.solver.check_assumptions(&[covers_cost]) {
            outcomes.push(Outcome::Run(Run::Advance));
        }

        outcomes
    }

    fn execute<'ctx, S>(
        &self,
        context: &'ctx Context,
        _: &Solver<'ctx>,
        run: Run,
        execution: &mut Execution<'ctx, S>,
    ) -> Result<(), Error<S::Error>>
    where
        S: Storage<'ctx>,
    {
        if run != Run::Advance {
            panic!("invalid run for jumpdest: {:?}", run);
        }

        let gas_cost = Int::from_u64(context, 1);
        execution.gas_remaining -= gas_cost;
        Ok(())
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
