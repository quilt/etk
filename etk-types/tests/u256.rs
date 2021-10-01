use etk_types::num::U256;

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
fn wrapping_add_fits() {
    let lhs = U256::new(100);
    let rhs = U256::new(101);

    assert_eq!(lhs.wrapping_add(rhs), U256::new(201));
}

#[test]
fn wrapping_add_carry() {
    let lhs = U256::new(u128::max_value());
    let rhs = U256::new(1);

    let expected = U256::with_high_order(1, 0);
    assert_eq!(lhs.wrapping_add(rhs), expected);
}

#[test]
fn wrapping_add_overflow() {
    let lhs = U256::max_value();
    let rhs = U256::new(1);

    assert_eq!(lhs.wrapping_add(rhs), U256::new(0));
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

#[test]
fn wrapping_sub_fits() {
    let lhs = U256::new(201);
    let rhs = U256::new(100);

    assert_eq!(lhs.wrapping_sub(rhs), U256::new(101));
}

#[test]
fn wrapping_sub_carry() {
    let lhs = U256::with_high_order(1, 0);
    let rhs = U256::new(1);

    let expected = U256::new(u128::max_value());
    assert_eq!(lhs.wrapping_sub(rhs), expected);
}

#[test]
fn wrapping_sub_overflow() {
    let lhs = U256::new(0);
    let rhs = U256::new(1);

    assert_eq!(lhs.wrapping_sub(rhs), U256::max_value());
}

#[test]
fn checked_sub_fits() {
    let lhs = U256::new(201);
    let rhs = U256::new(100);

    assert_eq!(lhs.checked_sub(rhs), Some(U256::new(101)));
}

#[test]
fn checked_sub_carry() {
    let lhs = U256::with_high_order(1, 0);
    let rhs = U256::new(1);

    let expected = U256::new(u128::max_value());
    assert_eq!(lhs.checked_sub(rhs), Some(expected));
}

#[test]
fn checked_sub_overflow() {
    let lhs = U256::new(0);
    let rhs = U256::new(1);

    assert_eq!(lhs.checked_sub(rhs), None);
}

#[test]
fn wrapping_mul_fits() {
    let rhs = U256::new(2);
    let lhs = U256::with_high_order(
        0x67676767676767676767676767676767,
        0x34343434343434343434343434343434,
    );

    assert_eq!(
        lhs.wrapping_mul(rhs),
        U256::with_high_order(
            0xcececececececececececececececece,
            0x68686868686868686868686868686868
        ),
    );
}

#[test]
fn wrapping_mul_zero() {
    let rhs = U256::new(0);
    let lhs = U256::new(0);

    assert_eq!(lhs.wrapping_mul(rhs), U256::new(0),);
}

#[test]
fn wrapping_mul_max_value() {
    let rhs = U256::max_value();
    let lhs = U256::max_value();

    assert_eq!(lhs.wrapping_mul(rhs), U256::new(1),);
}

#[test]
fn wrapping_mul_low_overflow() {
    let lhs = U256::new((1 << 64) + 1);
    let rhs = U256::new((1 << 64) + 0xFFFFFFFFFFFFFFFF);

    assert_eq!(
        lhs.wrapping_mul(rhs),
        U256::with_high_order(0x2, 0xffffffffffffffff),
    );
}

#[test]
fn wrapping_mul() {
    let lhs = U256::new(10000000000000000);
    let rhs = U256::new(10000000000000000);

    assert_eq!(
        lhs.wrapping_mul(rhs),
        U256::new(100000000000000000000000000000000),
    );
}

#[test]
fn checked_mul_fits() {
    let rhs = U256::new(2);
    let lhs = U256::with_high_order(
        0x67676767676767676767676767676767,
        0x34343434343434343434343434343434,
    );

    assert_eq!(
        lhs.checked_mul(rhs),
        Some(U256::with_high_order(
            0xcececececececececececececececece,
            0x68686868686868686868686868686868
        )),
    );
}

#[test]
fn checked_mul_zero() {
    let rhs = U256::new(0);
    let lhs = U256::new(0);

    assert_eq!(lhs.checked_mul(rhs), Some(U256::new(0)));
}

#[test]
fn checked_mul_max_value() {
    let rhs = U256::max_value();
    let lhs = U256::max_value();

    assert_eq!(lhs.checked_mul(rhs), None);
}

#[test]
fn checked_mul_low_overflow() {
    let lhs = U256::new((1 << 64) + 1);
    let rhs = U256::new((1 << 64) + 0xFFFFFFFFFFFFFFFF);

    assert_eq!(
        lhs.checked_mul(rhs),
        Some(U256::with_high_order(0x2, 0xffffffffffffffff)),
    );
}

#[test]
fn checked_mul() {
    let lhs = U256::new(10000000000000000);
    let rhs = U256::new(10000000000000000);

    assert_eq!(
        lhs.checked_mul(rhs),
        Some(U256::new(100000000000000000000000000000000)),
    );
}

#[test]
fn saturating_mul_fits() {
    let rhs = U256::new(2);
    let lhs = U256::with_high_order(
        0x67676767676767676767676767676767,
        0x34343434343434343434343434343434,
    );

    assert_eq!(
        lhs.saturating_mul(rhs),
        U256::with_high_order(
            0xcececececececececececececececece,
            0x68686868686868686868686868686868
        ),
    );
}

#[test]
fn saturating_mul_zero() {
    let rhs = U256::new(0);
    let lhs = U256::new(0);

    assert_eq!(lhs.saturating_mul(rhs), U256::new(0));
}

#[test]
fn saturating_mul_max_value() {
    let rhs = U256::max_value();
    let lhs = U256::max_value();

    assert_eq!(lhs.saturating_mul(rhs), U256::max_value());
}

#[test]
fn saturating_mul_low_overflow() {
    let lhs = U256::new((1 << 64) + 1);
    let rhs = U256::new((1 << 64) + 0xFFFFFFFFFFFFFFFF);

    assert_eq!(
        lhs.saturating_mul(rhs),
        U256::with_high_order(0x2, 0xffffffffffffffff),
    );
}

#[test]
fn saturating_mul() {
    let lhs = U256::new(10000000000000000);
    let rhs = U256::new(10000000000000000);

    assert_eq!(
        lhs.saturating_mul(rhs),
        U256::new(100000000000000000000000000000000),
    );
}

#[test]
fn swap_bytes() {
    let input = U256::with_high_order(
        0x102030405060708090a0b0c0d0e0f01c,
        0x112233445566778899aabbccddeeff1d,
    );

    let expected = U256::with_high_order(
        0x1dffeeddccbbaa998877665544332211,
        0x1cf0e0d0c0b0a0908070605040302010,
    );

    assert_eq!(input.swap_bytes(), expected);
}

#[test]
fn from_le() {
    let input = U256::with_high_order(
        0x102030405060708090a0b0c0d0e0f01c,
        0x112233445566778899aabbccddeeff1d,
    );

    #[cfg(target_endian = "little")]
    let expected = input;

    #[cfg(target_endian = "big")]
    let expected = U256::with_high_order(
        u128::from_le(0x112233445566778899aabbccddeeff1d),
        u128::from_le(0x102030405060708090a0b0c0d0e0f01c),
    );

    assert_eq!(U256::from_le(input), expected);
}

#[test]
fn from_be() {
    let input = U256::with_high_order(
        0x102030405060708090a0b0c0d0e0f01c,
        0x112233445566778899aabbccddeeff1d,
    );

    #[cfg(target_endian = "big")]
    let expected = input;

    #[cfg(target_endian = "little")]
    let expected = U256::with_high_order(
        u128::from_be(0x112233445566778899aabbccddeeff1d),
        u128::from_be(0x102030405060708090a0b0c0d0e0f01c),
    );

    assert_eq!(U256::from_be(input), expected);
}

#[test]
fn to_le_bytes() {
    let input = U256::with_high_order(
        0x102030405060708090a0b0c0d0e0f01c,
        0x112233445566778899aabbccddeeff1d,
    );

    let expected = [
        0x1d, 0xff, 0xee, 0xdd, 0xcc, 0xbb, 0xaa, 0x99, 0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22,
        0x11, 0x1c, 0xf0, 0xe0, 0xd0, 0xc0, 0xb0, 0xa0, 0x90, 0x80, 0x70, 0x60, 0x50, 0x40, 0x30,
        0x20, 0x10,
    ];

    assert_eq!(U256::to_le_bytes(input), expected);
}

#[test]
fn to_le_bytes_const() {
    let input = U256::with_high_order(
        0x102030405060708090a0b0c0d0e0f01c,
        0x112233445566778899aabbccddeeff1d,
    );

    let expected = [
        0x1d, 0xff, 0xee, 0xdd, 0xcc, 0xbb, 0xaa, 0x99, 0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22,
        0x11, 0x1c, 0xf0, 0xe0, 0xd0, 0xc0, 0xb0, 0xa0, 0x90, 0x80, 0x70, 0x60, 0x50, 0x40, 0x30,
        0x20, 0x10,
    ];

    assert_eq!(U256::to_le_bytes_const(input), expected);
}

#[test]
fn to_le() {
    let input = U256::with_high_order(
        0x102030405060708090a0b0c0d0e0f01c,
        0x112233445566778899aabbccddeeff1d,
    );

    #[cfg(target_endian = "little")]
    let expected = input;

    #[cfg(target_endian = "big")]
    let expected = U256::with_high_order(
        0x112233445566778899aabbccddeeff1du128.to_le(),
        0x102030405060708090a0b0c0d0e0f01cu128.to_le(),
    );

    assert_eq!(U256::to_le(input), expected);
}

#[test]
fn to_be_bytes() {
    let input = U256::with_high_order(
        0x102030405060708090a0b0c0d0e0f01c,
        0x112233445566778899aabbccddeeff1d,
    );

    let expected = [
        0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80, 0x90, 0xa0, 0xb0, 0xc0, 0xd0, 0xe0, 0xf0,
        0x1c, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee,
        0xff, 0x1d,
    ];

    assert_eq!(U256::to_be_bytes(input), expected);
}

#[test]
fn to_be() {
    let input = U256::with_high_order(
        0x102030405060708090a0b0c0d0e0f01c,
        0x112233445566778899aabbccddeeff1d,
    );

    #[cfg(target_endian = "big")]
    let expected = input;

    #[cfg(target_endian = "little")]
    let expected = U256::with_high_order(
        0x112233445566778899aabbccddeeff1du128.to_be(),
        0x102030405060708090a0b0c0d0e0f01cu128.to_be(),
    );

    assert_eq!(U256::to_be(input), expected);
}

#[test]
fn to_ne_bytes() {
    let input = U256::with_high_order(
        0x102030405060708090a0b0c0d0e0f01c,
        0x112233445566778899aabbccddeeff1d,
    );

    #[cfg(target_endian = "little")]
    let expected = [
        0x1d, 0xff, 0xee, 0xdd, 0xcc, 0xbb, 0xaa, 0x99, 0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22,
        0x11, 0x1c, 0xf0, 0xe0, 0xd0, 0xc0, 0xb0, 0xa0, 0x90, 0x80, 0x70, 0x60, 0x50, 0x40, 0x30,
        0x20, 0x10,
    ];

    #[cfg(target_endian = "big")]
    let expected = [
        0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80, 0x90, 0xa0, 0xb0, 0xc0, 0xd0, 0xe0, 0xf0,
        0x1c, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee,
        0xff, 0x1d,
    ];

    assert_eq!(U256::to_ne_bytes(input), expected);
}

#[test]
fn to_ne_bytes_const() {
    let input = U256::with_high_order(
        0x102030405060708090a0b0c0d0e0f01c,
        0x112233445566778899aabbccddeeff1d,
    );

    #[cfg(target_endian = "little")]
    let expected = [
        0x1d, 0xff, 0xee, 0xdd, 0xcc, 0xbb, 0xaa, 0x99, 0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22,
        0x11, 0x1c, 0xf0, 0xe0, 0xd0, 0xc0, 0xb0, 0xa0, 0x90, 0x80, 0x70, 0x60, 0x50, 0x40, 0x30,
        0x20, 0x10,
    ];

    #[cfg(target_endian = "big")]
    let expected = [
        0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80, 0x90, 0xa0, 0xb0, 0xc0, 0xd0, 0xe0, 0xf0,
        0x1c, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee,
        0xff, 0x1d,
    ];

    assert_eq!(U256::to_ne_bytes_const(input), expected);
}

#[test]
fn from_be_bytes() {
    let input = [
        0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80, 0x90, 0xa0, 0xb0, 0xc0, 0xd0, 0xe0, 0xf0,
        0x1c, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee,
        0xff, 0x1d,
    ];

    let expected = U256::with_high_order(
        0x102030405060708090a0b0c0d0e0f01c,
        0x112233445566778899aabbccddeeff1d,
    );

    assert_eq!(U256::from_be_bytes(input), expected);
}

#[test]
fn from_be_bytes_const() {
    let input = [
        0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80, 0x90, 0xa0, 0xb0, 0xc0, 0xd0, 0xe0, 0xf0,
        0x1c, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee,
        0xff, 0x1d,
    ];

    let expected = U256::with_high_order(
        0x102030405060708090a0b0c0d0e0f01c,
        0x112233445566778899aabbccddeeff1d,
    );

    assert_eq!(U256::from_be_bytes_const(input), expected);
}

#[test]
fn from_le_bytes() {
    let input = [
        0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80, 0x90, 0xa0, 0xb0, 0xc0, 0xd0, 0xe0, 0xf0,
        0x1c, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee,
        0xff, 0x1d,
    ];

    let expected = U256::with_high_order(
        0x1dffeeddccbbaa998877665544332211,
        0x1cf0e0d0c0b0a0908070605040302010,
    );

    assert_eq!(U256::from_le_bytes(input), expected);
}

#[test]
fn from_le_bytes_const() {
    let input = [
        0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80, 0x90, 0xa0, 0xb0, 0xc0, 0xd0, 0xe0, 0xf0,
        0x1c, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee,
        0xff, 0x1d,
    ];

    let expected = U256::with_high_order(
        0x1dffeeddccbbaa998877665544332211,
        0x1cf0e0d0c0b0a0908070605040302010,
    );

    assert_eq!(U256::from_le_bytes_const(input), expected);
}

#[test]
fn count_ones_max_value() {
    let input = U256::max_value();
    assert_eq!(input.count_ones(), 256);
}

#[test]
fn count_ones_min_value() {
    let input = U256::min_value();
    assert_eq!(input.count_ones(), 0);
}

#[test]
fn count_zeros_max_value() {
    let input = U256::max_value();
    assert_eq!(input.count_zeros(), 0);
}

#[test]
fn count_zeros_min_value() {
    let input = U256::min_value();
    assert_eq!(input.count_zeros(), 256);
}

#[test]
fn leading_zeros_max_value() {
    let input = U256::max_value();
    assert_eq!(input.leading_zeros(), 0);
}

#[test]
fn leading_zeros_min_value() {
    let input = U256::min_value();
    assert_eq!(input.leading_zeros(), 256);
}

#[test]
fn leading_zeros_127() {
    let input = U256::with_high_order(1, u128::max_value());
    assert_eq!(input.leading_zeros(), 127);
}

#[test]
fn leading_zeros_129() {
    let input = U256::new(u128::max_value() >> 1);
    assert_eq!(input.leading_zeros(), 129);
}

#[test]
fn trailing_zeros_max_value() {
    let input = U256::max_value();
    assert_eq!(input.trailing_zeros(), 0);
}

#[test]
fn trailing_zeros_min_value() {
    let input = U256::min_value();
    assert_eq!(input.trailing_zeros(), 256);
}

#[test]
fn trailing_zeros_127() {
    let input = U256::new(1 << 127);
    assert_eq!(input.trailing_zeros(), 127);
}

#[test]
fn trailing_zeros_129() {
    let input = U256::with_high_order(2, 0);
    assert_eq!(input.trailing_zeros(), 129);
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
