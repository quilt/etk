use crate::error::{self, Error};
use crate::execution::Execution;
use crate::storage::{Key, Storage};
use crate::{Halt, Outcome, Run, ZEvm};

use etk_ops::london::SLoad;

use smallvec::SmallVec;

use snafu::ResultExt;

use super::SymbolicOp;

use z3::ast::{Ast, Bool, Int};
use z3::{SatResult, Solver};

const BASE_GAS: u64 = 100;
const COLD_GAS: u64 = 2_000;

fn gas_cost(warm: Bool) -> Int {
    let ctx = warm.get_ctx();
    let sload_gas = Int::from_u64(ctx, BASE_GAS);
    let sload_cold = Int::from_u64(ctx, COLD_GAS);

    let cost = sload_gas + warm.ite(&Int::from_u64(ctx, 0), &sload_cold);

    cost.simplify()
}

impl SymbolicOp for SLoad {
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
        let slot = execution.stack.peek(0).unwrap();

        // Calculate the gas cost.
        let warm = execution.is_warm_slot(slot);

        let covers_cost = execution.gas_remaining.ge(&gas_cost(warm));

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
        _: &'ctx z3::Context,
        solver: &Solver<'ctx>,
        run: Run,
        execution: &mut Execution<'ctx, S>,
    ) -> Result<(), Error<S::Error>>
    where
        S: Storage<'ctx>,
    {
        if Run::Advance != run {
            panic!("invalid run for sstore: {:?}", run);
        }

        let slot = execution.stack.pop().unwrap();

        let key = Key::new(solver, &execution.state_address, &slot);

        let warm = execution.is_warm_slot(&slot);

        execution.gas_remaining -= gas_cost(warm);

        let value = execution.storage.get(key).context(error::StorageSnafu)?;

        execution
            .stack
            .push(value)
            .expect("not possible to overflow stack");

        execution
            .warm_slots
            .push((execution.state_address.clone(), slot));

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
        let evm = Builder::<'_, InMemory>::new(&ctx, vec![SLoad.into()])
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
        let mut evm = Builder::<'_, InMemory>::new(&ctx, vec![SLoad.into()])
            .set_gas(5)
            .build();

        evm.executions[0]
            .stack
            .push(BV::from_u64(&ctx, 0, 256))
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
    fn ambiguous_at() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut evm = Builder::<'_, InMemory>::new(&ctx, vec![SLoad.into()])
            .set_gas(2100)
            .build();

        // Store a value to force the account to exist.
        let state_address = evm.executions[0].state_address.clone();
        let slot = BV::from_u64(&ctx, 0, 256);
        let key = Key::new(&evm.solver, &state_address, &slot);
        evm.executions[0]
            .storage
            .set(key, &BV::from_u64(&ctx, 1, 256))
            .unwrap();

        // Choose an intentionally ambiguous slot.
        let at = BV::fresh_const(&ctx, "at", 256);
        evm.solver
            .assert(&(at._eq(&BV::from_u64(&ctx, 0, 256)) | at._eq(&BV::from_u64(&ctx, 32, 256))));

        evm.executions[0].stack.push(at).unwrap();

        let step = evm.step();
        assert_eq!(step.len(), 1);

        let outcomes: Vec<_> = step.outcomes().collect();

        assert_eq!(outcomes[0], Outcome::Run(Run::Advance));

        match step.apply(Run::Advance).unwrap_err() {
            crate::Error::Storage {
                source: crate::resolve::Error::Ambiguous { .. },
                ..
            } => (),
            _ => panic!("expected Ambiguous"),
        }
    }

    #[test]
    fn cold_load_not_enough_gas() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut evm = Builder::<'_, InMemory>::new(&ctx, vec![SLoad.into()])
            .set_gas(2099)
            .build();

        evm.executions[0]
            .stack
            .push(BV::from_u64(&ctx, 0, 256))
            .unwrap();

        let step = evm.step();
        assert_eq!(step.len(), 1);

        let outcomes: Vec<_> = step.outcomes().collect();

        assert_eq!(outcomes[0], Outcome::Halt(Halt::OutOfGas));
    }

    #[test]
    fn specific_at() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut evm = Builder::<'_, InMemory>::new(&ctx, vec![SLoad.into()])
            .set_gas(22100)
            .build();

        // Store a value to get later.
        let state_address = evm.executions[0].state_address.clone();
        let slot = BV::from_u64(&ctx, 6744, 256);
        let key = Key::new(&evm.solver, &state_address, &slot);
        evm.executions[0]
            .storage
            .set(key, &BV::from_u64(&ctx, 42069, 256))
            .unwrap();

        evm.executions[0].stack.push(slot).unwrap();

        let step = evm.step();
        assert_eq!(step.len(), 1);

        let outcomes: Vec<_> = step.outcomes().collect();

        assert_eq!(outcomes[0], Outcome::Run(Run::Advance));

        let evm = step.apply(Run::Advance).unwrap();

        let got = evm.execution().stack.peek(0).unwrap();

        assert_eq!(got, &BV::from_u64(&ctx, 42069, 256));
    }
}
