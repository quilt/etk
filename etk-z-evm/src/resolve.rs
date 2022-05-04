use snafu::{Backtrace, OptionExt, Snafu};

use z3::ast::{Ast, BV};
use z3::{SatResult, Solver};

#[derive(Debug, Snafu)]
pub enum Error {
    Unsat { backtrace: Backtrace },
    Ambiguous { backtrace: Backtrace },
}

pub(crate) fn resolve<'ctx>(solver: &Solver<'ctx>, at: &BV<'ctx>) -> Result<[u8; 32], Error> {
    let ctx = solver.get_context();

    if SatResult::Sat != solver.check() {
        return UnsatSnafu {}.fail();
    }

    let model = solver.get_model().unwrap();
    let resolved = model.eval(at, true).context(AmbiguousSnafu)?;

    let mut store = [0u8; 32];

    for ii in 0..4 {
        let dest = &mut store[ii * 8..(ii + 1) * 8];
        let shift = ((3 - ii) * 8 * 8).try_into().unwrap();

        let fragment = resolved
            .bvlshr(&BV::from_u64(ctx, shift, 256))
            .bvand(&BV::from_u64(ctx, u64::MAX, 256))
            .simplify()
            .as_u64()
            .context(AmbiguousSnafu)?
            .to_be_bytes();

        dest.copy_from_slice(&fragment);
    }

    if SatResult::Unsat != solver.check_assumptions(&[at._eq(&resolved).not()]) {
        // If the given address `at` can resolve to multiple values, bail.
        return AmbiguousSnafu.fail();
    }

    Ok(store)
}
