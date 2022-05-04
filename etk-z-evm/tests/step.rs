use etk_ops::london::*;

use etk_z_evm::storage::InMemory;
use etk_z_evm::{Builder, Halt, Offset, Outcome, Run};

use z3::{Config, Context};

#[test]
fn add_jumpi_stop() {
    let mut cfg = Config::new();
    cfg.set_model_generation(true);

    let ctx = Context::new(&cfg);
    let evm = Builder::<'_, InMemory>::new(
        &ctx,
        vec![
            Push1([8]).into(),
            Push1([8]).into(),
            Add.into(),
            Push1([5]).into(),
            Push2([0, 8]).into(),
            Add.into(),
            JumpI.into(),
            Stop.into(),
            JumpDest.into(),
            Stop.into(),
        ],
    )
    .set_gas(29)
    .build();

    // push1 8
    let step = evm.step();
    assert_eq!(step.len(), 1);

    let evm = step.apply(Run::Advance).unwrap();

    // push1 8
    let step = evm.step();
    assert_eq!(step.len(), 1);

    let evm = step.apply(Run::Advance).unwrap();

    // add
    let step = evm.step();
    assert_eq!(step.len(), 1);

    let evm = step.apply(Run::Advance).unwrap();

    // push1 5
    let step = evm.step();
    assert_eq!(step.len(), 1);

    let evm = step.apply(Run::Advance).unwrap();

    // push2 1
    let step = evm.step();
    assert_eq!(step.len(), 1);

    let evm = step.apply(Run::Advance).unwrap();

    // add
    let step = evm.step();
    assert_eq!(step.len(), 1);

    let evm = step.apply(Run::Advance).unwrap();

    // jumpi
    let step = evm.step();
    assert_eq!(step.len(), 1);

    let evm = step.apply(Run::Jump(Offset(13))).unwrap();

    // jumpdest
    let step = evm.step();
    assert_eq!(step.len(), 1);

    let evm = step.apply(Run::Advance).unwrap();

    // stop
    let step = evm.step();
    assert_eq!(step.len(), 1);

    let outcome = step.outcomes().next().unwrap();
    assert_eq!(outcome, Outcome::Halt(Halt::Stop));

    // TODO: check that gas _can_ equal zero, and that gas _cannot_ not equal zero.
}
