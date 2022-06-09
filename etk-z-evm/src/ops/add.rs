use crate::error::Error;
use crate::execution::Execution;
use crate::storage::Storage;
use crate::{Halt, Outcome, Run, ZEvm};

use etk_ops::london::Add;

use smallvec::SmallVec;

use super::SymbolicOp;

use z3::ast::Int;
use z3::{Context, SatResult, Solver};

impl SymbolicOp for Add {
    fn outcomes<'ctx, S>(&self, evm: &ZEvm<'ctx, S>) -> SmallVec<[Outcome; 2]>
    where
        S: Storage<'ctx>,
    {
        let execution = evm.execution();

        let gas_cost = Int::from_u64(evm.ctx, 3);
        let covers_cost = execution.gas_remaining.ge(&gas_cost);

        let mut outcomes = SmallVec::new();

        if execution.stack.len() < 2 {
            outcomes.push(Outcome::Halt(Halt::StackUnderflow));
            return outcomes;
        }

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
            panic!("invalid run for add: {:?}", run);
        }

        let lhs = execution.stack.pop().unwrap();
        let rhs = execution.stack.pop().unwrap();
        execution.stack.push(lhs + rhs).unwrap();

        let gas_cost = Int::from_u64(context, 3);
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
    fn underflow() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let evm = Builder::<'_, InMemory>::new(&ctx, vec![Add.into()])
            .set_gas(3)
            .build();

        let step = evm.step();
        assert_eq!(step.len(), 1);

        let outcomes: Vec<_> = step.outcomes().collect();

        assert_eq!(outcomes[0], Outcome::Halt(Halt::StackUnderflow));
    }

    #[test]
    fn not_enough_gas() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut evm = Builder::<'_, InMemory>::new(&ctx, vec![Add.into()])
            .set_gas(0)
            .build();

        evm.executions[0]
            .stack
            .push(BV::from_u64(&ctx, 11, 256))
            .unwrap();
        evm.executions[0]
            .stack
            .push(BV::from_u64(&ctx, 29, 256))
            .unwrap();

        let step = evm.step();
        assert_eq!(step.len(), 1);

        let outcomes: Vec<_> = step.outcomes().collect();

        assert_eq!(outcomes[0], Outcome::Halt(Halt::OutOfGas));
    }

    #[test]
    fn add_two() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut evm = Builder::<'_, InMemory>::new(&ctx, vec![Add.into()])
            .set_gas(3)
            .build();

        evm.executions[0]
            .stack
            .push(BV::from_u64(&ctx, 11, 256))
            .unwrap();
        evm.executions[0]
            .stack
            .push(BV::from_u64(&ctx, 29, 256))
            .unwrap();

        let step = evm.step();
        assert_eq!(step.len(), 1);

        let outcomes: Vec<_> = step.outcomes().collect();

        assert_eq!(outcomes[0], Outcome::Run(Run::Advance));

        let mut next = step.apply(Run::Advance).unwrap();
        assert_eq!(next.executions.len(), 2);
        assert_eq!(next.executions[1].stack.len(), 1);

        let sum = next.executions[1].stack.pop().unwrap();
        let result = next.solver.check_assumptions(&[
            sum._eq(&BV::from_u64(&ctx, 40, 256)),
            next.executions[1]
                .gas_remaining
                ._eq(&Int::from_u64(&ctx, 0)),
        ]);

        assert_eq!(SatResult::Sat, result);
    }
}
