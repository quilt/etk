use crate::execution::Execution;
use crate::{Halt, Outcome, Run, Step, ZEvm};

use smallvec::SmallVec;

use z3::ast::{Int, BV};
use z3::{SatResult, Solver};

impl<'ctx> ZEvm<'ctx> {
    pub(crate) fn mstore(self) -> Step<'ctx> {
        let execution = self.execution();

        let mut outcomes = SmallVec::new();

        // Are there enough stack elements?
        if execution.stack.len() < 2 {
            outcomes.push(Outcome::Halt(Halt::StackUnderflow));
            return Step {
                outcomes,
                previous: self,
            };
        }

        // Get the stack elements for this instruction.
        let position = execution.stack.peek(0).unwrap();

        let mut gas_cost = Int::from_u64(self.ctx, 3);
        gas_cost += execution.memory.expansion_gas(
            &self.solver,
            position,
            &BV::from_u64(self.ctx, 32, 256),
        );

        let covers_cost = execution.gas_remaining.ge(&gas_cost);

        // Is out of gas possible?
        if SatResult::Sat == self.solver.check_assumptions(&[covers_cost.not()]) {
            outcomes.push(Outcome::Halt(Halt::OutOfGas));
        }

        // Is it possible to have enough gas?
        if SatResult::Sat == self.solver.check_assumptions(&[covers_cost]) {
            outcomes.push(Outcome::Run(Run::Advance));
        }

        Step {
            previous: self,
            outcomes,
        }
    }
}

impl<'ctx> Step<'ctx> {
    pub(crate) fn mstore(
        &self,
        run: Run,
        solver: &Solver<'ctx>,
        execution: &mut Execution<'ctx>,
    ) -> Result<(), crate::memory::Error> {
        if Run::Advance != run {
            panic!("invalid run for mstore: {:?}", run);
        }

        let ctx = self.previous.ctx;

        let position = execution.stack.pop().unwrap();
        let value = execution.stack.pop().unwrap();

        let mut gas_cost = Int::from_u64(ctx, 3);
        gas_cost +=
            execution
                .memory
                .try_expansion_gas(solver, &position, &BV::from_u64(ctx, 32, 256))?;

        execution.gas_remaining -= gas_cost;

        execution.memory.store(solver, &position, &value)
    }
}

#[cfg(test)]
mod tests {
    use etk_asm::ops::ConcreteOp;
    use z3::ast::{Ast, BV};

    use crate::Offset;

    use super::*;

    use z3::{Config, Context};

    #[test]
    fn underflow() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let evm = ZEvm::with_gas(&ctx, vec![ConcreteOp::MStore], 10);

        let step = evm.step();
        assert_eq!(step.len(), 1);

        let outcomes: Vec<_> = step.outcomes().collect();

        assert_eq!(outcomes[0], Outcome::Halt(Halt::StackUnderflow));
    }

    #[test]
    fn not_enough_gas() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut evm = ZEvm::with_gas(&ctx, vec![ConcreteOp::MStore], 5);

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
        let mut evm = ZEvm::with_gas(&ctx, vec![ConcreteOp::MStore], 100);

        let at = BV::fresh_const(&ctx, "at", 256);
        evm.solver
            .assert(&(at._eq(&BV::from_u64(&ctx, 0, 256)) | at._eq(&BV::from_u64(&ctx, 32, 256))));

        evm.executions[0]
            .stack
            .push(BV::from_u64(&ctx, 0, 256))
            .unwrap();
        evm.executions[0].stack.push(at).unwrap();

        let step = evm.step();
        assert_eq!(step.len(), 2);

        let outcomes: Vec<_> = step.outcomes().collect();

        assert_eq!(outcomes[0], Outcome::Halt(Halt::OutOfGas)); // This is technically incorrect.
        assert_eq!(outcomes[1], Outcome::Run(Run::Advance));

        match step.apply(Run::Advance).unwrap_err() {
            crate::memory::Error::Ambiguous => (),
            _ => panic!("expected Ambiguous"),
        }
    }

    #[test]
    fn specific_at() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut evm = ZEvm::with_gas(&ctx, vec![ConcreteOp::MStore], 6);

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

        let got = evm.execution().memory.get(&[0; 32]).unwrap();
        assert_eq!(got, &BV::from_u64(&ctx, 6744, 256));
    }

    #[test]
    fn specific_at_big() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut evm = ZEvm::with_gas(&ctx, vec![ConcreteOp::MStore], 126);

        evm.executions[0]
            .stack
            .push(BV::from_u64(&ctx, 6744, 256))
            .unwrap();
        evm.executions[0]
            .stack
            .push(BV::from_u64(&ctx, 1248, 256))
            .unwrap();

        let step = evm.step();
        assert_eq!(step.len(), 1);

        let outcomes: Vec<_> = step.outcomes().collect();

        assert_eq!(outcomes[0], Outcome::Run(Run::Advance));

        let evm = step.apply(Run::Advance).unwrap();

        let mut key = [0u8; 32];
        key[30] = 0x04;
        key[31] = 0xe0;

        let got = evm.execution().memory.get(&key).unwrap();
        assert_eq!(got, &BV::from_u64(&ctx, 6744, 256));
    }
}
