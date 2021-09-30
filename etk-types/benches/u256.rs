use criterion::{black_box, criterion_group, criterion_main, Criterion};

use etk_types::num::U256;

fn addition(c: &mut Criterion) {
    c.bench_function("etk_wrapping_add", |b| {
        let lhs = U256::new(20);
        let rhs = U256::with_high_order(
            0x67676767676767676767676767676767,
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        );

        b.iter(|| black_box(black_box(lhs).wrapping_add(black_box(rhs))))
    });

    #[cfg(feature = "benches-comparison")]
    c.bench_function("pt_overflowing_add", |b| {
        use primitive_types::U256;

        let lhs = U256::from(20);
        let rhs = U256::from([
            0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67,
            0x67, 0x67, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
            0xFF, 0xFF, 0xFF, 0xFF,
        ]);

        b.iter(|| black_box(black_box(lhs).overflowing_add(black_box(rhs))))
    });

    c.bench_function("etk_saturating_add", |b| {
        let lhs = U256::new(20);
        let rhs = U256::with_high_order(
            0x67676767676767676767676767676767,
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        );

        b.iter(|| black_box(black_box(lhs).saturating_add(black_box(rhs))))
    });

    #[cfg(feature = "benches-comparison")]
    c.bench_function("pt_saturating_add", |b| {
        use primitive_types::U256;

        let lhs = U256::from(20);
        let rhs = U256::from([
            0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67,
            0x67, 0x67, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
            0xFF, 0xFF, 0xFF, 0xFF,
        ]);

        b.iter(|| black_box(black_box(lhs).saturating_add(black_box(rhs))))
    });

    c.bench_function("etk_checked_add", |b| {
        let lhs = U256::new(20);
        let rhs = U256::with_high_order(
            0x67676767676767676767676767676767,
            0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        );

        b.iter(|| black_box(black_box(lhs).checked_add(black_box(rhs))))
    });

    #[cfg(feature = "benches-comparison")]
    c.bench_function("pt_checked_add", |b| {
        use primitive_types::U256;

        let lhs = U256::from(20);
        let rhs = U256::from([
            0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67,
            0x67, 0x67, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
            0xFF, 0xFF, 0xFF, 0xFF,
        ]);

        b.iter(|| black_box(black_box(lhs).checked_add(black_box(rhs))))
    });
}

fn multiplication(c: &mut Criterion) {
    c.bench_function("etk_saturating_mul", |b| {
        let lhs = U256::new(20);
        let rhs = U256::with_high_order(
            0x67676767676767676767676767676767,
            0x34343434343434343434343434343434,
        );

        b.iter(|| black_box(black_box(lhs).saturating_mul(black_box(rhs))))
    });

    #[cfg(feature = "benches-comparison")]
    c.bench_function("pt_saturating_mul", |b| {
        use primitive_types::U256;

        let lhs = U256::from(20);
        let rhs = U256::from([
            0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67,
            0x67, 0x67, 0x34, 0x34, 0x34, 0x34, 0x34, 0x34, 0x34, 0x34, 0x34, 0x34, 0x34, 0x34,
            0x34, 0x34, 0x34, 0x34,
        ]);

        b.iter(|| black_box(black_box(lhs).saturating_mul(black_box(rhs))))
    });

    c.bench_function("etk_checked_mul", |b| {
        let lhs = U256::new(20);
        let rhs = U256::with_high_order(
            0x67676767676767676767676767676767,
            0x34343434343434343434343434343434,
        );

        b.iter(|| black_box(black_box(lhs).checked_mul(black_box(rhs))))
    });

    #[cfg(feature = "benches-comparison")]
    c.bench_function("pt_checked_mul", |b| {
        use primitive_types::U256;

        let lhs = U256::from(20);
        let rhs = U256::from([
            0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67,
            0x67, 0x67, 0x34, 0x34, 0x34, 0x34, 0x34, 0x34, 0x34, 0x34, 0x34, 0x34, 0x34, 0x34,
            0x34, 0x34, 0x34, 0x34,
        ]);

        b.iter(|| black_box(black_box(lhs).checked_mul(black_box(rhs))))
    });

    c.bench_function("etk_wrapping_mul", |b| {
        let lhs = U256::new(20);
        let rhs = U256::with_high_order(
            0x67676767676767676767676767676767,
            0x34343434343434343434343434343434,
        );

        b.iter(|| black_box(black_box(lhs).wrapping_mul(black_box(rhs))))
    });

    #[cfg(feature = "benches-comparison")]
    c.bench_function("pt_overflowing_mul", |b| {
        use primitive_types::U256;

        let lhs = U256::from(20);
        let rhs = U256::from([
            0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67, 0x67,
            0x67, 0x67, 0x34, 0x34, 0x34, 0x34, 0x34, 0x34, 0x34, 0x34, 0x34, 0x34, 0x34, 0x34,
            0x34, 0x34, 0x34, 0x34,
        ]);

        b.iter(|| black_box(black_box(lhs).overflowing_mul(black_box(rhs))))
    });
}

criterion_group!(arithmetic, multiplication, addition);
criterion_main!(arithmetic);
