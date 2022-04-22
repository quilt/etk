use etk_asm::ops::ConcreteOp;

use etk_z_evm::{ZEvm, Outcome, Halt, Run, Offset};

use z3::{Config, Context};

#[test]
fn add_jumpi_stop() {
    let mut cfg = Config::new();
    cfg.set_model_generation(true);

    let ctx = Context::new(&cfg);
    let evm = ZEvm::with_gas(&ctx, vec![
        ConcreteOp::Push1([8]),
        ConcreteOp::Push1([8]),
        ConcreteOp::Add,
        ConcreteOp::Push1([5]),
        ConcreteOp::Push2([0, 8]),
        ConcreteOp::Add,
        ConcreteOp::JumpI,
        ConcreteOp::Stop,
        ConcreteOp::JumpDest,
        ConcreteOp::Stop,
    ], 29);

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
