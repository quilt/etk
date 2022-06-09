use crate::error::{self, Error};
use crate::execution::Execution;
use crate::storage::{Key, Storage};
use crate::{Halt, Outcome, Run, ZEvm};

use etk_ops::london::SStore;

use smallvec::SmallVec;

use snafu::ResultExt;

use super::SymbolicOp;

use z3::ast::{Ast, Bool, Int, BV};
use z3::{SatResult, Solver};

const SET_GAS: u64 = 20_000;
const RESET_GAS: u64 = 5_000;
const BASE_GAS: u64 = 100;
const COLD_GAS: u64 = 2_100;

fn gas_cost<'ctx, S>(
    storage: &S,
    key: Key<'_, 'ctx>,
    new_value: &BV<'ctx>,
    warm: Bool<'ctx>,
) -> Result<Int<'ctx>, S::Error>
where
    S: Storage<'ctx>,
{
    let ctx = key.context();
    let sload_gas = Int::from_u64(ctx, BASE_GAS);
    let sstore_set_gas = Int::from_u64(ctx, SET_GAS);
    let sstore_reset_gas = Int::from_u64(ctx, RESET_GAS);
    let sstore_cold = Int::from_u64(ctx, COLD_GAS);
    let zero = BV::from_u64(ctx, 0, 256);

    let current_value = storage.get(key)?;
    let original_value = storage.original(key)?;

    let cost = (original_value._eq(&current_value) & current_value._eq(new_value).not()).ite(
        &original_value
            ._eq(&zero)
            .ite(&sstore_set_gas, &sstore_reset_gas),
        &sload_gas,
    ) + warm.ite(&Int::from_u64(ctx, 0), &sstore_cold);

    Ok(cost.simplify())
}

impl SymbolicOp for SStore {
    fn outcomes<'ctx, S>(&self, evm: &ZEvm<'ctx, S>) -> SmallVec<[Outcome; 2]>
    where
        S: Storage<'ctx>,
    {
        let execution = evm.execution();

        let mut outcomes = SmallVec::new();

        // Are there enough stack elements?
        if execution.stack.len() < 2 {
            outcomes.push(Outcome::Halt(Halt::StackUnderflow));
            return outcomes;
        }

        // Get the stack elements for this instruction.
        let slot = execution.stack.peek(0).unwrap();
        let new_value = execution.stack.peek(1).unwrap();

        // Calculate the gas cost.
        let warm = execution.is_warm_slot(slot);

        let key = Key::new(&evm.solver, &execution.state_address, slot);

        let gas_cost = gas_cost(&execution.storage, key, new_value, warm).unwrap_or_else(|_| {
            // TODO: technically not a strict bound on what paths are possible.
            let g = Int::fresh_const(evm.ctx, "str-gas");

            let one_of = &g._eq(&Int::from_u64(evm.ctx, BASE_GAS))
                | &g._eq(&Int::from_u64(evm.ctx, SET_GAS))
                | &g._eq(&Int::from_u64(evm.ctx, RESET_GAS))
                | &g._eq(&Int::from_u64(evm.ctx, BASE_GAS + COLD_GAS))
                | &g._eq(&Int::from_u64(evm.ctx, SET_GAS + COLD_GAS))
                | &g._eq(&Int::from_u64(evm.ctx, RESET_GAS + COLD_GAS));

            evm.solver.assert(&one_of);

            g
        });

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
        let new_value = execution.stack.pop().unwrap();

        let key = Key::new(solver, &execution.state_address, &slot);

        let warm = execution.is_warm_slot(&slot);
        let gas_cost =
            gas_cost(&execution.storage, key, &new_value, warm).context(error::StorageSnafu)?;

        execution.gas_remaining -= gas_cost;

        execution
            .storage
            .set(key, &new_value)
            .context(error::StorageSnafu)?;

        execution
            .warm_slots
            .push((execution.state_address.clone(), slot));

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::storage::InMemory;
    use crate::{to_bv, Builder, Offset};

    use etk_ops::london::*;

    use super::*;

    use z3::ast::{Ast, BV};
    use z3::{Config, Context};

    #[test]
    fn underflow() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let evm = Builder::<'_, InMemory>::new(&ctx, vec![SStore.into()])
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
        let mut evm = Builder::<'_, InMemory>::new(&ctx, vec![SStore.into()])
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
        let mut evm = Builder::<'_, InMemory>::new(&ctx, vec![SStore.into()])
            .set_gas(2200)
            .build();

        let at = BV::fresh_const(&ctx, "at", 256);
        evm.solver
            .assert(&(at._eq(&BV::from_u64(&ctx, 0, 256)) | at._eq(&BV::from_u64(&ctx, 32, 256))));

        evm.executions[0]
            .stack
            .push(BV::from_u64(&ctx, 0, 256))
            .unwrap();
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
    fn cold_write_non_zero_not_enough_gas() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut evm = Builder::<'_, InMemory>::new(&ctx, vec![SStore.into()])
            .set_gas(22099)
            .build();

        evm.executions[0]
            .stack
            .push(BV::from_u64(&ctx, 6744, 256))
            .unwrap();
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
        let mut evm = Builder::<'_, InMemory>::new(&ctx, vec![SStore.into()])
            .set_gas(22100)
            .build();

        evm.executions[0]
            .stack
            .push(BV::from_u64(&ctx, 6744, 256))
            .unwrap();
        evm.executions[0]
            .stack
            .push(BV::from_u64(&ctx, 0, 256))
            .unwrap();

        let step = evm.step();
        assert_eq!(step.len(), 1);

        let outcomes: Vec<_> = step.outcomes().collect();

        assert_eq!(outcomes[0], Outcome::Run(Run::Advance));

        let evm = step.apply(Run::Advance).unwrap();

        let slot = BV::from_u64(&ctx, 0, 256);
        let got = evm
            .execution()
            .storage
            .get(&evm.solver, &evm.executions[0].state_address, &slot)
            .unwrap();

        assert_eq!(&got, &BV::from_u64(&ctx, 6744, 256));
    }
}
