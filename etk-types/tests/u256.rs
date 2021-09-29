use etk_types::U256;

use num_traits as num;

use static_assertions::assert_impl_all;

use std::cmp::Ordering;

#[test]
fn ord_eq_big() {
    let lhs = U256::with_high_order(u128::max_value(), 5);
    let rhs = U256::with_high_order(u128::max_value(), 5);

    assert_eq!(lhs.cmp(&rhs), Ordering::Equal);
}

#[test]
fn ord_eq() {
    let lhs = U256::new(5);
    let rhs = U256::new(5);

    assert_eq!(lhs.cmp(&rhs), Ordering::Equal);
}

#[test]
fn ord_less() {
    let lhs = U256::new(4);
    let rhs = U256::new(5);

    assert_eq!(lhs.cmp(&rhs), Ordering::Less);
}

#[test]
fn ord_less_big() {
    let lhs = U256::with_high_order(0, u128::max_value());
    let rhs = U256::with_high_order(u128::max_value(), 0);

    assert_eq!(lhs.cmp(&rhs), Ordering::Less);
}

#[test]
fn ord_greater() {
    let lhs = U256::new(5);
    let rhs = U256::new(4);

    assert_eq!(lhs.cmp(&rhs), Ordering::Greater);
}

#[test]
fn ord_greater_big() {
    let lhs = U256::with_high_order(u128::max_value(), 0);
    let rhs = U256::with_high_order(0, u128::max_value());

    assert_eq!(lhs.cmp(&rhs), Ordering::Greater);
}

#[test]
fn checked_add_fits() {
    let lhs = U256::new(100);
    let rhs = U256::new(101);

    assert_eq!(lhs.checked_add(rhs), Some(U256::new(201)));
}

#[test]
fn checked_add_carry() {
    let lhs = U256::new(u128::max_value());
    let rhs = U256::new(1);

    let expected = U256::with_high_order(1, 0);
    assert_eq!(lhs.checked_add(rhs), Some(expected));
}

#[test]
fn checked_add_overflow() {
    let lhs = U256::max_value();
    let rhs = U256::new(1);

    assert_eq!(lhs.checked_add(rhs), None);
}

#[test]
fn saturating_add_fits() {
    let lhs = U256::new(100);
    let rhs = U256::new(1);

    assert_eq!(lhs.saturating_add(rhs), U256::new(101));
}

#[test]
fn saturating_add_overflows_big_plus_small() {
    let lhs = U256::max_value();
    let rhs = U256::new(1);

    assert_eq!(lhs.saturating_add(rhs), U256::max_value());
}

#[test]
fn saturating_add_overflows_small_plus_big() {
    let lhs = U256::new(1);
    let rhs = U256::max_value();

    assert_eq!(lhs.saturating_add(rhs), U256::max_value());
}

assert_impl_all!(
    U256: num::Num,
    num::NumAssign,
    num::NumAssignOps,
    num::NumAssignRef,
    num::NumOps,
    num::NumRef,
    num::RefNum<U256>,
    num::Unsigned,
);
