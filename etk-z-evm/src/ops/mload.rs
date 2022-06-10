use crate::error::{self, Error};
use crate::execution::Execution;
use crate::storage::Storage;
use crate::{Halt, Outcome, Run, ZEvm};

use etk_ops::london::MLoad;

use smallvec::SmallVec;
use snafu::ResultExt;

use super::SymbolicOp;

use z3::ast::{Int, BV};
use z3::{SatResult, Solver};

impl SymbolicOp for MLoad {
    fn outcomes<'ctx, S>(&self, evm: &ZEvm<'ctx, S>) -> SmallVec<[Outcome; 2]>
    where
        S: Storage<'ctx>,
    {
        let execution = evm.execution();

        let mut outcomes = SmallVec::new();

        // Are there enough stack elements?
        if execution.stack.len() < 1 {
            outcomes.push(Outcome::Halt(Halt::StackUnderflow));
            return outcomes;
        }

        // Get the stack elements for this instruction.
        let position = execution.stack.peek(0).unwrap();

        let mut gas_cost = Int::from_u64(evm.ctx, 3);
        gas_cost +=
            execution
                .memory
                .expansion_gas(&evm.solver, position, &BV::from_u64(evm.ctx, 32, 256));

        let covers_cost = execution.gas_remaining.ge(&gas_cost);

        // Is out of gas possible?
        if SatResult::Sat == evm.solver.check_assumptions(&[covers_cost.not()]) {
            outcomes.push(Outcome::Halt(Halt::OutOfGas));
        }

        // Is it possible to have enough gas?
        if SatResult::Sat == evm.solver.check_assumptions(&[covers_cost]) {
            outcomes.push(Outcome::Run(Run::Advance));
        }

        outcomes
    }

    fn execute<'ctx, S>(
        &self,
        context: &'ctx z3::Context,
        solver: &Solver<'ctx>,
        run: Run,
        execution: &mut Execution<'ctx, S>,
    ) -> Result<(), Error<S::Error>>
    where
        S: Storage<'ctx>,
    {
        if Run::Advance != run {
            panic!("invalid run for mload: {:?}", run);
        }

        let position = execution.stack.pop().unwrap();

        let mut gas_cost = Int::from_u64(context, 3);
        gas_cost += execution
            .memory
            .try_expansion_gas(solver, &position, &BV::from_u64(context, 32, 256))
            .context(error::MemorySnafu)?;

        execution.gas_remaining -= gas_cost;

        let value = execution
            .memory
            .load(solver, &position)
            .context(error::MemorySnafu)?;
        execution.stack.push(value).unwrap();

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
        let evm = Builder::<'_, InMemory>::new(&ctx, vec![MLoad.into()])
            .set_gas(10)
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
        let mut evm = Builder::<'_, InMemory>::new(&ctx, vec![MLoad.into()])
            .set_gas(5)
            .build();

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
    fn ambiguous_at() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut evm = Builder::<'_, InMemory>::new(&ctx, vec![MLoad.into()])
            .set_gas(100)
            .build();

        let at = BV::fresh_const(&ctx, "at", 256);
        evm.solver
            .assert(&(at._eq(&BV::from_u64(&ctx, 0, 256)) | at._eq(&BV::from_u64(&ctx, 32, 256))));

        evm.executions[0].stack.push(at).unwrap();

        let step = evm.step();
        assert_eq!(step.len(), 2);

        let outcomes: Vec<_> = step.outcomes().collect();

        assert_eq!(outcomes[0], Outcome::Halt(Halt::OutOfGas)); // This is technically incorrect.
        assert_eq!(outcomes[1], Outcome::Run(Run::Advance));

        match step.apply(Run::Advance).unwrap_err() {
            crate::Error::Memory {
                source: crate::resolve::Error::Ambiguous { .. },
            } => (),
            _ => panic!("expected Ambiguous"),
        }
    }

    #[test]
    fn specific_at() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut evm = Builder::<'_, InMemory>::new(&ctx, vec![MLoad.into()])
            .set_gas(6)
            .build();

        evm.executions[0]
            .memory
            .set([0; 32], BV::from_u64(&ctx, 0x1a58, 256));

        evm.executions[0]
            .stack
            .push(BV::from_u64(&ctx, 0, 256))
            .unwrap();

        let step = evm.step();
        assert_eq!(step.len(), 1);

        let outcomes: Vec<_> = step.outcomes().collect();

        assert_eq!(outcomes[0], Outcome::Run(Run::Advance));

        let evm = step.apply(Run::Advance).unwrap();

        let got = evm.execution().memory.get(&[0; 32]).unwrap();
        assert_eq!(got, &BV::from_u64(&ctx, 6744, 256));
    }

    #[test]
    fn specific_at_big() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut evm = Builder::<'_, InMemory>::new(&ctx, vec![MLoad.into()])
            .set_gas(126)
            .build();

        let mut key = [0u8; 32];
        key[30] = 0x04;
        key[31] = 0xe0;

        evm.executions[0]
            .memory
            .set(key, BV::from_u64(&ctx, 0x1a58, 256));

        evm.executions[0]
            .stack
            .push(BV::from_u64(&ctx, 1248, 256))
            .unwrap();

        let step = evm.step();
        assert_eq!(step.len(), 1);

        let outcomes: Vec<_> = step.outcomes().collect();

        assert_eq!(outcomes[0], Outcome::Run(Run::Advance));

        let evm = step.apply(Run::Advance).unwrap();

        let got = evm.execution().memory.get(&key).unwrap();
        assert_eq!(got, &BV::from_u64(&ctx, 6744, 256));
    }
}
