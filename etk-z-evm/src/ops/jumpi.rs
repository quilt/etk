use crate::execution::Execution;
use crate::{Halt, Outcome, Run, Step, ZEvm};

use smallvec::SmallVec;

use z3::ast::{Ast, Bool, Int, BV};
use z3::SatResult;

impl<'ctx> ZEvm<'ctx> {
    pub(crate) fn jumpi(self) -> Step<'ctx> {
        let execution = self.execution();

        let gas_cost = Int::from_u64(self.ctx, 10);
        let covers_cost = execution.gas_remaining.ge(&gas_cost);

        let mut outcomes = SmallVec::new();

        // Are there enough stack elements?
        if execution.stack.len() < 2 {
            outcomes.push(Outcome::Halt(Halt::StackUnderflow));
            return Step {
                outcomes,
                previous: self,
            };
        }

        // Is out of gas possible?
        if SatResult::Sat == self.solver.check_assumptions(&[covers_cost.not()]) {
            outcomes.push(Outcome::Halt(Halt::OutOfGas));
        }

        // Is it possible to have enough gas?
        if SatResult::Sat == self.solver.check_assumptions(&[covers_cost]) {
            // Get the stack elements for this instruction.
            let dest = execution.stack.peek(0).unwrap();
            let advance = execution
                .stack
                .peek(1)
                .unwrap()
                ._eq(&BV::from_u64(self.ctx, 0, 256));

            // Assume this instruction jumps (instead of falling through.)
            self.solver.push();
            self.solver.assert(&advance.not());
            if SatResult::Sat == self.solver.check() {
                let mut possible_dests = Vec::new();

                // Check if it's possible for `dest` to be each JUMPDEST offset.
                for (offset, _) in self.constants.destinations() {
                    let possible_dest = BV::from_u64(self.ctx, offset.0.into(), 256);
                    let can_jump = possible_dest._eq(dest);
                    let cannot_jump = can_jump.not();

                    if SatResult::Sat == self.solver.check_assumptions(&[can_jump]) {
                        possible_dests.push(cannot_jump);
                        outcomes.push(Outcome::Run(Run::Jump(offset)))
                    }
                }

                // Check if it's possible for `dest` to not be a JUMPDEST offset.
                let possible_dests_refs: Vec<_> = possible_dests.iter().collect();
                let bad_jump = Bool::and(self.ctx, &possible_dests_refs);

                if SatResult::Sat == self.solver.check_assumptions(&[bad_jump]) {
                    outcomes.push(Outcome::Halt(Halt::InvalidJumpDest));
                }
            }
            self.solver.pop(1);

            // Check if it's possible to fall through (instead of jumping.)
            if SatResult::Sat == self.solver.check_assumptions(&[advance]) {
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
    pub(crate) fn jumpi(&self, run: Run, execution: &mut Execution<'ctx>) {
        execution.gas_remaining -= Int::from_u64(self.previous.ctx, 10);

        let dest = execution.stack.pop().unwrap();
        let cmp = execution.stack.pop().unwrap();

        let will_advance = cmp._eq(&BV::from_u64(self.previous.ctx, 0, 256));

        match run {
            Run::Jump(offset) => {
                self.previous.solver.assert(&will_advance.not());

                let offset = BV::from_u64(self.previous.ctx, offset.0.into(), 256);
                self.previous.solver.assert(&dest._eq(&offset));
            }
            Run::Advance => {
                self.previous.solver.assert(&will_advance);
            }
        }
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
        let evm = ZEvm::with_gas(&ctx, vec![ConcreteOp::JumpI], 10);

        let step = evm.step();
        assert_eq!(step.len(), 1);

        let outcomes: Vec<_> = step.outcomes().collect();

        assert_eq!(outcomes[0], Outcome::Halt(Halt::StackUnderflow));
    }

    #[test]
    fn not_enough_gas() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut evm = ZEvm::with_gas(&ctx, vec![ConcreteOp::JumpI], 9);

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
    fn advance_only() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut evm = ZEvm::with_gas(&ctx, vec![ConcreteOp::JumpI], 10);

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

        assert_eq!(outcomes[0], Outcome::Run(Run::Advance));
    }

    #[test]
    fn invalid_jump_only() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut evm = ZEvm::with_gas(&ctx, vec![ConcreteOp::JumpI], 10);

        evm.executions[0]
            .stack
            .push(BV::from_u64(&ctx, 1, 256))
            .unwrap();
        evm.executions[0]
            .stack
            .push(BV::from_u64(&ctx, 29, 256))
            .unwrap();

        let step = evm.step();
        assert_eq!(step.len(), 1);

        let outcomes: Vec<_> = step.outcomes().collect();

        assert_eq!(outcomes[0], Outcome::Halt(Halt::InvalidJumpDest));
    }

    #[test]
    fn unrestricted() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut evm = ZEvm::new(
            &ctx,
            vec![
                ConcreteOp::JumpI,
                ConcreteOp::JumpDest,
                ConcreteOp::JumpDest,
            ],
        );

        evm.executions[0]
            .stack
            .push(BV::fresh_const(&ctx, "condition", 256))
            .unwrap();
        evm.executions[0]
            .stack
            .push(BV::fresh_const(&ctx, "destination", 256))
            .unwrap();

        let step = evm.step();
        assert_eq!(step.len(), 5);

        let outcomes: Vec<_> = step.outcomes().collect();

        assert_eq!(outcomes[0], Outcome::Halt(Halt::OutOfGas));
        assert_eq!(outcomes[1], Outcome::Halt(Halt::InvalidJumpDest));
        assert_eq!(outcomes[2], Outcome::Run(Run::Jump(Offset(1))));
        assert_eq!(outcomes[3], Outcome::Run(Run::Jump(Offset(2))));
        assert_eq!(outcomes[4], Outcome::Run(Run::Advance));
    }

    #[test]
    fn asserts_when_jump() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut evm = ZEvm::new(
            &ctx,
            vec![ConcreteOp::JumpI, ConcreteOp::Stop, ConcreteOp::JumpDest],
        );

        let condition = BV::fresh_const(&ctx, "condition", 256);

        evm.executions[0].stack.push(condition.clone()).unwrap();
        evm.executions[0]
            .stack
            .push(BV::fresh_const(&ctx, "destination", 256))
            .unwrap();

        let evm = evm.step().apply(Run::Jump(Offset(2))).unwrap();

        let eq_zero = condition._eq(&BV::from_u64(&ctx, 0, 256));

        assert_eq!(
            SatResult::Sat,
            evm.solver.check_assumptions(&[eq_zero.not()])
        );
        assert_eq!(SatResult::Unsat, evm.solver.check_assumptions(&[eq_zero]));

        assert_eq!(evm.execution().pc, Offset(2));
    }

    #[test]
    fn asserts_when_advance() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut evm = ZEvm::new(
            &ctx,
            vec![ConcreteOp::JumpI, ConcreteOp::Stop, ConcreteOp::JumpDest],
        );

        let condition = BV::fresh_const(&ctx, "condition", 256);

        evm.executions[0].stack.push(condition.clone()).unwrap();
        evm.executions[0]
            .stack
            .push(BV::fresh_const(&ctx, "destination", 256))
            .unwrap();

        let evm = evm.step().apply(Run::Advance).unwrap();

        let eq_zero = condition._eq(&BV::from_u64(&ctx, 0, 256));

        assert_eq!(
            SatResult::Unsat,
            evm.solver.check_assumptions(&[eq_zero.not()])
        );
        assert_eq!(SatResult::Sat, evm.solver.check_assumptions(&[eq_zero]));

        assert_eq!(evm.execution().pc, Offset(1));
    }
}
