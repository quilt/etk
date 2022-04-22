use crate::execution::Execution;
use crate::{to_bv, Halt, Outcome, Run, Step, ZEvm};

use smallvec::SmallVec;

use z3::ast::Int;
use z3::SatResult;

impl<'ctx> ZEvm<'ctx> {
    pub(crate) fn push(self) -> Step<'ctx> {
        let execution = self.execution();

        let gas_cost = Int::from_u64(self.ctx, 3);
        let covers_cost = execution.gas_remaining.ge(&gas_cost);

        let mut outcomes = SmallVec::new();

        if SatResult::Sat == self.solver.check_assumptions(&[covers_cost.not()]) {
            outcomes.push(Outcome::Halt(Halt::OutOfGas));
        }

        if SatResult::Sat == self.solver.check_assumptions(&[covers_cost]) {
            if execution.stack.is_full() {
                outcomes.push(Outcome::Halt(Halt::StackOverflow));
            } else {
                outcomes.push(Outcome::Run(Run::Advance));
            }
        }

        Step {
            previous: self,
            outcomes,
        }
    }
}

impl<'ctx> Step<'ctx> {
    pub(crate) fn push(&self, v: &[u8], run: Run, execution: &mut Execution<'ctx>) {
        if run != Run::Advance {
            panic!("invalid run for push: {:?}", run);
        }

        execution.stack.push(to_bv(self.previous.ctx, v)).unwrap();
        execution.gas_remaining -= Int::from_u64(self.previous.ctx, 3);
    }
}

#[cfg(test)]
mod tests {
    use etk_asm::ops::ConcreteOp;

    use super::*;

    use z3::ast::Ast;
    use z3::{Config, Context};

    #[test]
    fn unrestricted() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let evm = ZEvm::new(&ctx, vec![ConcreteOp::Push1([5])]);

        let step = evm.step();
        assert_eq!(step.len(), 2);

        let outcomes: Vec<_> = step.outcomes().collect();

        assert_eq!(outcomes[0], Outcome::Halt(Halt::OutOfGas));
        assert_eq!(outcomes[1], Outcome::Run(Run::Advance));
    }

    #[test]
    fn not_enough_gas() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let evm = ZEvm::with_gas(&ctx, vec![ConcreteOp::Push1([5])], 2);

        let step = evm.step();
        assert_eq!(step.len(), 1);

        let outcomes: Vec<_> = step.outcomes().collect();

        assert_eq!(outcomes[0], Outcome::Halt(Halt::OutOfGas));
    }

    #[test]
    fn just_enough_gas() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let evm = ZEvm::with_gas(
            &ctx,
            vec![ConcreteOp::Push32([
                0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc, 0xde, 0xf0, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66,
                0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff, 0x00, 0x23, 0x45, 0x67, 0x89,
                0xab, 0xcd, 0xef, 0xff,
            ])],
            3,
        );

        let step = evm.step();
        assert_eq!(step.len(), 1);

        let outcomes: Vec<_> = step.outcomes().collect();

        assert_eq!(outcomes[0], Outcome::Run(Run::Advance));

        let next = step.apply(Run::Advance).unwrap();
        assert_eq!(next.execution().stack.len(), 1);

        let result = next
            .solver
            .check_assumptions(&[next.execution().gas_remaining._eq(&Int::from_u64(&ctx, 0))]);

        assert_eq!(result, SatResult::Sat);
    }
}
