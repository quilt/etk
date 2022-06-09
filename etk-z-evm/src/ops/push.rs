use crate::execution::Execution;
use crate::storage::Storage;
use crate::{to_bv, Halt, Outcome, Run, ZEvm};

use etk_ops::london::*;
use etk_ops::Immediate;

use smallvec::SmallVec;

use std::borrow::Borrow;

use super::SymbolicOp;

use z3::ast::Int;
use z3::SatResult;

fn outcomes<S>(evm: &ZEvm<S>) -> SmallVec<[Outcome; 2]> {
    let execution = evm.execution();

    let gas_cost = Int::from_u64(evm.ctx, 3);
    let covers_cost = execution.gas_remaining.ge(&gas_cost);

    let mut outcomes = SmallVec::new();

    if SatResult::Sat == evm.solver.check_assumptions(&[covers_cost.not()]) {
        outcomes.push(Outcome::Halt(Halt::OutOfGas));
    }

    if SatResult::Sat == evm.solver.check_assumptions(&[covers_cost]) {
        if execution.stack.is_full() {
            outcomes.push(Outcome::Halt(Halt::StackOverflow));
        } else {
            outcomes.push(Outcome::Run(Run::Advance));
        }
    }

    outcomes
}

fn execute<'ctx, S>(
    v: &[u8],
    context: &'ctx z3::Context,
    _: &z3::Solver<'ctx>,
    run: Run,
    execution: &mut Execution<'ctx, S>,
) -> Result<(), crate::error::Error<S::Error>>
where
    S: crate::storage::Storage<'ctx>,
{
    if run != Run::Advance {
        panic!("invalid run for push: {:?}", run);
    }

    execution.stack.push(to_bv(context, v)).unwrap();
    execution.gas_remaining -= Int::from_u64(context, 3);
    Ok(())
}

macro_rules! impl_push {
    () => {};

    ($p:ident<$i:literal>, $($restp:ident<$resti:literal>, )*) => {
        impl<I> SymbolicOp for $p<I>
        where
            I: Immediate<$i> + Borrow<[u8]>,
        {
            fn outcomes<'ctx, S>(&self, evm: &ZEvm<'ctx, S>) -> SmallVec<[Outcome; 2]>
            where
                S: Storage<'ctx>,
            {
                outcomes(evm)
            }

            fn execute<'ctx, S>(
                &self,
                context: &'ctx z3::Context,
                solver: &z3::Solver<'ctx>,
                run: Run,
                execution: &mut Execution<'ctx, S>,
            ) -> Result<(), crate::error::Error<S::Error>>
            where
                S: Storage<'ctx>,
            {
                execute(self.0.borrow(), context, solver, run, execution)
            }
        }

        impl_push!($($restp<$resti>,)*);
    };
}

impl_push!(
    Push32<32>,
    Push31<31>,
    Push30<30>,
    Push29<29>,
    Push28<28>,
    Push27<27>,
    Push26<26>,
    Push25<25>,
    Push24<24>,
    Push23<23>,
    Push22<22>,
    Push21<21>,
    Push20<20>,
    Push19<19>,
    Push18<18>,
    Push17<17>,
    Push16<16>,
    Push15<15>,
    Push14<14>,
    Push13<13>,
    Push12<12>,
    Push11<11>,
    Push10<10>,
    Push9<9>,
    Push8<8>,
    Push7<7>,
    Push6<6>,
    Push5<5>,
    Push4<4>,
    Push3<3>,
    Push2<2>,
    Push1<1>,
);

#[cfg(test)]
mod tests {
    use crate::storage::InMemory;
    use crate::Builder;

    use etk_ops::london::*;

    use super::*;

    use z3::ast::Ast;
    use z3::{Config, Context};

    #[test]
    fn unrestricted() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let evm = Builder::<'_, InMemory>::new(&ctx, vec![Push1([5]).into()]).build();

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
        let evm = Builder::<'_, InMemory>::new(&ctx, vec![Push1([5]).into()])
            .set_gas(2)
            .build();

        let step = evm.step();
        assert_eq!(step.len(), 1);

        let outcomes: Vec<_> = step.outcomes().collect();

        assert_eq!(outcomes[0], Outcome::Halt(Halt::OutOfGas));
    }

    #[test]
    fn just_enough_gas() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let evm = Builder::<'_, InMemory>::new(
            &ctx,
            vec![Push32([
                0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc, 0xde, 0xf0, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66,
                0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff, 0x00, 0x23, 0x45, 0x67, 0x89,
                0xab, 0xcd, 0xef, 0xff,
            ])
            .into()],
        )
        .set_gas(3)
        .build();

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
