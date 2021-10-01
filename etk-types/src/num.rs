use num_traits as num;

use core::convert::{TryFrom, TryInto};
use core::num::TryFromIntError;
use core::ops;

#[inline]
fn try_from_int_error() -> TryFromIntError {
    // XXX: Literally the dumbest thing I've ever had to write.
    u8::try_from(256).unwrap_err()
}

union Transmute {
    ints: [u128; 2],
    bytes: [u8; 32],
}

static_assertions::assert_eq_size!(Transmute, [u128; 2], [u8; 32]);
static_assertions::assert_eq_align!(Transmute, [u128; 2]);

#[derive(Debug, Default, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct U256 {
    high: u128,
    low: u128,
}

impl<T> From<T> for U256
where
    T: Into<u128>,
{
    #[inline]
    fn from(t: T) -> Self {
        Self {
            high: 0,
            low: t.into(),
        }
    }
}

macro_rules! impl_try_from_u256 {
    ($($int:ty, )+) => {
        $(
        impl TryFrom<U256> for $int {
            type Error = TryFromIntError;

            #[inline]
            fn try_from(u: U256) -> Result<Self, Self::Error> {
                if u.high == 0 {
                    Self::try_from(u.low)
                } else {
                    Err(try_from_int_error())
                }
            }
        }

        impl TryFrom<&U256> for $int {
            type Error = TryFromIntError;

            #[inline]
            fn try_from(u: &U256) -> Result<Self, Self::Error> {
                if u.high == 0 {
                    Self::try_from(u.low)
                } else {
                    Err(try_from_int_error())
                }
            }
        }
        )+
    }
}

impl_try_from_u256!(i8, u8, i16, u16, i32, u32, i64, u64, i128, isize, usize,);

impl TryFrom<U256> for u128 {
    type Error = TryFromIntError;

    #[inline]
    fn try_from(u: U256) -> Result<Self, Self::Error> {
        if u.high == 0 {
            Ok(u.low)
        } else {
            Err(try_from_int_error())
        }
    }
}

impl TryFrom<&U256> for u128 {
    type Error = TryFromIntError;

    #[inline]
    fn try_from(u: &U256) -> Result<Self, Self::Error> {
        if u.high == 0 {
            Ok(u.low)
        } else {
            Err(try_from_int_error())
        }
    }
}

impl U256 {
    #[inline]
    pub const fn new(low: u128) -> Self {
        Self { low, high: 0 }
    }

    #[inline]
    pub const fn with_high_order(high: u128, low: u128) -> Self {
        Self { high, low }
    }

    #[inline]
    pub const fn wrapping_add(self, rhs: Self) -> Self {
        let (low, low_overflow) = self.low.overflowing_add(rhs.low);
        let high = self.high.wrapping_add(rhs.high);
        U256 {
            low,
            high: if low_overflow {
                high.wrapping_add(1)
            } else {
                high
            },
        }
    }

    #[inline]
    pub const fn checked_add(self, rhs: Self) -> Option<Self> {
        // TODO: Optimize this.

        let (mid, mid_overflow) = self.high.overflowing_add(rhs.high);

        if mid_overflow {
            return None;
        }

        let (low, low_overflow) = self.low.overflowing_add(rhs.low);

        if !low_overflow {
            return Some(Self { high: mid, low });
        }

        let (high, high_overflow) = mid.overflowing_add(1);

        if high_overflow {
            None
        } else {
            Some(Self { high, low })
        }
    }

    #[inline]
    pub const fn saturating_add(self, rhs: Self) -> Self {
        match self.checked_add(rhs) {
            Some(v) => v,
            None => Self::max_value(),
        }
    }

    #[inline(always)]
    const fn split_u128(v: u128) -> (u64, u64) {
        let high = v >> 64;
        let low = v & 0xFFFFFFFFFFFFFFFF;
        (high as u64, low as u64)
    }

    #[inline(always)]
    const fn split(self) -> (u64, u64, u64, u64) {
        let (hh, hl) = Self::split_u128(self.high);
        let (lh, ll) = Self::split_u128(self.low);
        (hh, hl, lh, ll)
    }

    #[inline]
    pub const fn wrapping_mul(self, rhs: Self) -> Self {
        let (s0, s1, s2, s3) = self.split();
        let (r0, r1, r2, r3) = rhs.split();

        /*
         * Now we have:
         *  self = (s0 * (1 << 192)) + (s1 * (1 << 128)) + (s2 * (1 << 64)) + s3
         *  rhs  = (r0 * (1 << 192)) + (r1 * (1 << 128)) + (r2 * (1 << 64)) + r3
         */

        let s0_r3: u128 = s0 as u128 * r3 as u128;
        let s1_r2: u128 = s1 as u128 * r2 as u128;
        let s1_r3: u128 = s1 as u128 * r3 as u128;
        let s2_r1: u128 = s2 as u128 * r1 as u128;
        let s2_r2: u128 = s2 as u128 * r2 as u128;
        let s2_r3: u128 = s2 as u128 * r3 as u128;
        let s3_r0: u128 = s3 as u128 * r0 as u128;
        let s3_r1: u128 = s3 as u128 * r1 as u128;
        let s3_r2: u128 = s3 as u128 * r2 as u128;
        let s3_r3: u128 = s3 as u128 * r3 as u128;

        let mut high = s0_r3.wrapping_shl(64);
        high = high.wrapping_add(s1_r2.wrapping_shl(64));
        high = high.wrapping_add(s1_r3);
        high = high.wrapping_add(s2_r1.wrapping_shl(64));
        high = high.wrapping_add(s2_r2);
        high = high.wrapping_add(s2_r3.wrapping_shr(64));

        let low = s2_r3.wrapping_shl(64);

        high = high.wrapping_add(s3_r0.wrapping_shl(64));
        high = high.wrapping_add(s3_r1);
        high = high.wrapping_add(s3_r2.wrapping_shr(64));

        let (low, over) = low.overflowing_add(s3_r2.wrapping_shl(64));
        if over {
            high = high.wrapping_add(1);
        }

        let (low, over) = low.overflowing_add(s3_r3);
        if over {
            high = high.wrapping_add(1);
        }

        Self { high, low }
    }

    #[inline]
    #[allow(clippy::question_mark)] // `?` isn't supported in const fn yet.
    pub const fn checked_mul(self, rhs: Self) -> Option<Self> {
        // TODO: Needs more tests

        let (s0, s1, s2, s3) = self.split();
        let (r0, r1, r2, r3) = rhs.split();

        /*
         * Now we have:
         *  self = (s0 * (1 << 192)) + (s1 * (1 << 128)) + (s2 * (1 << 64)) + s3
         *  rhs  = (r0 * (1 << 192)) + (r1 * (1 << 128)) + (r2 * (1 << 64)) + r3
         */

        let s0_r3: u128 = s0 as u128 * r3 as u128;
        let s1_r2: u128 = s1 as u128 * r2 as u128;
        let s1_r3: u128 = s1 as u128 * r3 as u128;
        let s2_r1: u128 = s2 as u128 * r1 as u128;
        let s2_r2: u128 = s2 as u128 * r2 as u128;
        let s2_r3: u128 = s2 as u128 * r3 as u128;
        let s3_r0: u128 = s3 as u128 * r0 as u128;
        let s3_r1: u128 = s3 as u128 * r1 as u128;
        let s3_r2: u128 = s3 as u128 * r2 as u128;
        let s3_r3: u128 = s3 as u128 * r3 as u128;

        macro_rules! try_ {
            ($v:expr) => {
                if let Some(val) = $v {
                    val
                } else {
                    return None;
                }
            };
        }

        let mut high = try_!(s0_r3.checked_shl(64));
        high = try_!(high.checked_add(try_!(s1_r2.checked_shl(64))));
        high = try_!(high.checked_add(s1_r3));
        high = try_!(high.checked_add(try_!(s2_r1.checked_shl(64))));
        high = try_!(high.checked_add(s2_r2));
        high = try_!(high.checked_add(s2_r3.wrapping_shr(64)));

        let low = s2_r3.wrapping_shl(64);

        high = try_!(high.checked_add(try_!(s3_r0.checked_shl(64))));
        high = try_!(high.checked_add(s3_r1));
        high = try_!(high.checked_add(s3_r2.wrapping_shr(64)));

        let (low, over) = low.overflowing_add(s3_r2.wrapping_shl(64));
        if over {
            high = try_!(high.checked_add(1));
        }

        let (low, over) = low.overflowing_add(s3_r3);
        if over {
            high = try_!(high.checked_add(1));
        }

        Some(Self { high, low })
    }

    #[inline]
    pub const fn saturating_mul(self, rhs: Self) -> Self {
        match self.checked_mul(rhs) {
            Some(v) => v,
            None => Self::max_value(),
        }
    }

    #[inline]
    pub const fn wrapping_sub(self, rhs: Self) -> Self {
        let (low, low_overflow) = self.low.overflowing_sub(rhs.low);
        let high = self.high.wrapping_sub(rhs.high);
        U256 {
            low,
            high: if low_overflow {
                high.wrapping_sub(1)
            } else {
                high
            },
        }
    }

    #[inline]
    pub const fn checked_sub(self, rhs: Self) -> Option<Self> {
        let (mid, mid_overflow) = self.high.overflowing_sub(rhs.high);

        if mid_overflow {
            return None;
        }

        let (low, low_overflow) = self.low.overflowing_sub(rhs.low);

        if !low_overflow {
            return Some(Self { high: mid, low });
        }

        let (high, high_overflow) = mid.overflowing_sub(1);

        if high_overflow {
            None
        } else {
            Some(Self { high, low })
        }
    }

    #[inline]
    pub const fn saturating_sub(self, rhs: Self) -> Self {
        match self.checked_sub(rhs) {
            Some(v) => v,
            None => Self::min_value(),
        }
    }

    #[inline]
    pub const fn wrapping_div(self, _rhs: Self) -> Self {
        // TODO
        self
    }

    #[inline]
    pub const fn checked_div(self, _rhs: Self) -> Option<Self> {
        // TODO
        None
    }

    #[inline]
    pub const fn wrapping_rem(self, _rhs: Self) -> Self {
        // TODO
        self
    }

    #[inline]
    pub const fn checked_rem(self, _rhs: Self) -> Option<Self> {
        // TODO
        None
    }

    #[inline]
    pub const fn checked_shr(self, _cnt: Self) -> Option<Self> {
        // TODO
        None
    }

    #[inline]
    pub const fn wrapping_shr(self, _cnt: Self) -> Self {
        // TODO
        self
    }

    #[inline]
    pub const fn checked_shl(self, _cnt: Self) -> Option<Self> {
        // TODO
        None
    }

    #[inline]
    pub const fn wrapping_shl(self, _cnt: Self) -> Self {
        // TODO
        self
    }

    #[inline]
    pub const fn signed_shr(self, _cnt: Self) -> Self {
        // TODO
        self
    }

    #[inline]
    pub const fn signed_shl(self, _cnt: Self) -> Self {
        // TODO
        self
    }

    #[inline]
    pub const fn swap_bytes(self) -> Self {
        Self {
            high: self.low.swap_bytes(),
            low: self.high.swap_bytes(),
        }
    }

    #[allow(clippy::wrong_self_convention)]
    #[inline]
    pub const fn from_be(v: Self) -> Self {
        #[cfg(target_endian = "big")]
        return v;

        #[cfg(target_endian = "little")]
        return v.swap_bytes();
    }

    #[allow(clippy::wrong_self_convention)]
    #[inline]
    pub const fn from_le(v: Self) -> Self {
        #[cfg(target_endian = "little")]
        return v;

        #[cfg(target_endian = "big")]
        return v.swap_bytes();
    }

    #[inline]
    pub const fn to_be(self) -> Self {
        #[cfg(target_endian = "big")]
        return self;

        #[cfg(target_endian = "little")]
        return self.swap_bytes();
    }

    #[inline]
    pub const fn to_le(self) -> Self {
        #[cfg(target_endian = "little")]
        return self;

        #[cfg(target_endian = "big")]
        return self.swap_bytes();
    }

    #[inline]
    pub fn pow(self, exp: Self) -> Self {
        #[cfg(debug_assertions)]
        let result = self.checked_pow(exp).unwrap();

        #[cfg(not(debug_assertions))]
        let result = self.wrapping_pow(exp);

        result
    }

    #[inline]
    pub const fn wrapping_pow(self, _: Self) -> Self {
        // TODO
        self
    }

    #[inline]
    pub const fn checked_pow(self, _: Self) -> Option<Self> {
        // TODO
        None
    }

    #[inline]
    pub const fn saturating_pow(self, _: Self) -> Self {
        // TODO
        self
    }

    #[inline]
    pub const fn min_value() -> Self {
        Self { high: 0, low: 0 }
    }

    #[inline]
    pub const fn max_value() -> Self {
        Self {
            high: u128::max_value(),
            low: u128::max_value(),
        }
    }

    #[inline]
    pub const fn count_ones(self) -> u32 {
        self.low.count_ones() + self.high.count_ones()
    }

    #[inline]
    pub const fn count_zeros(self) -> u32 {
        self.low.count_zeros() + self.high.count_zeros()
    }

    #[inline]
    pub const fn leading_zeros(self) -> u32 {
        if self.high == 0 {
            128 + self.low.leading_zeros()
        } else {
            self.high.leading_zeros()
        }
    }

    #[inline]
    pub const fn trailing_zeros(self) -> u32 {
        if self.low == 0 {
            128 + self.high.trailing_zeros()
        } else {
            self.low.trailing_zeros()
        }
    }

    #[inline]
    pub const fn rotate_left(self, _cnt: u32) -> Self {
        // TODO
        self
    }

    #[inline]
    pub const fn rotate_right(self, _cnt: u32) -> Self {
        // TODO
        self
    }

    #[inline]
    pub fn to_le_bytes(self) -> [u8; 32] {
        // TODO: Optimize further.
        let transmute = Transmute {
            ints: [self.low.to_le(), self.high.to_le()],
        };

        unsafe { transmute.bytes }
    }

    #[inline]
    pub const fn to_le_bytes_const(self) -> [u8; 32] {
        // TODO: Deprecate this in a later Rust version, once `const_fn_union`
        //       is stabilized: https://github.com/rust-lang/rust/issues/51909
        let low = self.low.to_le_bytes();
        let high = self.high.to_le_bytes();

        let mut output = [0; 32];
        output[0] = low[0];
        output[1] = low[1];
        output[2] = low[2];
        output[3] = low[3];
        output[4] = low[4];
        output[5] = low[5];
        output[6] = low[6];
        output[7] = low[7];
        output[8] = low[8];
        output[9] = low[9];
        output[10] = low[10];
        output[11] = low[11];
        output[12] = low[12];
        output[13] = low[13];
        output[14] = low[14];
        output[15] = low[15];
        output[16] = high[0];
        output[17] = high[1];
        output[18] = high[2];
        output[19] = high[3];
        output[20] = high[4];
        output[21] = high[5];
        output[22] = high[6];
        output[23] = high[7];
        output[24] = high[8];
        output[25] = high[9];
        output[26] = high[10];
        output[27] = high[11];
        output[28] = high[12];
        output[29] = high[13];
        output[30] = high[14];
        output[31] = high[15];

        output
    }

    #[inline]
    pub fn to_be_bytes(self) -> [u8; 32] {
        // TODO: Optimize further.
        let transmute = Transmute {
            ints: [self.high.to_be(), self.low.to_be()],
        };

        unsafe { transmute.bytes }
    }

    #[inline]
    pub const fn to_be_bytes_const(self) -> [u8; 32] {
        // TODO: Deprecate this in a later Rust version, once `const_fn_union`
        //       is stabilized: https://github.com/rust-lang/rust/issues/51909
        let low = self.low.to_be_bytes();
        let high = self.high.to_be_bytes();

        let mut output = [0; 32];
        output[0] = high[0];
        output[1] = high[1];
        output[2] = high[2];
        output[3] = high[3];
        output[4] = high[4];
        output[5] = high[5];
        output[6] = high[6];
        output[7] = high[7];
        output[8] = high[8];
        output[9] = high[9];
        output[10] = high[10];
        output[11] = high[11];
        output[12] = high[12];
        output[13] = high[13];
        output[14] = high[14];
        output[15] = high[15];
        output[16] = low[0];
        output[17] = low[1];
        output[18] = low[2];
        output[19] = low[3];
        output[20] = low[4];
        output[21] = low[5];
        output[22] = low[6];
        output[23] = low[7];
        output[24] = low[8];
        output[25] = low[9];
        output[26] = low[10];
        output[27] = low[11];
        output[28] = low[12];
        output[29] = low[13];
        output[30] = low[14];
        output[31] = low[15];

        output
    }

    #[inline]
    pub fn to_ne_bytes(self) -> [u8; 32] {
        #[cfg(target_endian = "big")]
        return self.to_be_bytes();

        #[cfg(target_endian = "little")]
        return self.to_le_bytes();
    }

    #[inline]
    pub const fn to_ne_bytes_const(self) -> [u8; 32] {
        // TODO: Deprecate this in a later Rust version, once `const_fn_union`
        //       is stabilized: https://github.com/rust-lang/rust/issues/51909
        #[cfg(target_endian = "big")]
        return self.to_be_bytes_const();

        #[cfg(target_endian = "little")]
        return self.to_le_bytes_const();
    }

    #[inline]
    pub fn from_be_bytes(bytes: [u8; 32]) -> Self {
        // TODO: Optimize this further.
        let transmute = Transmute { bytes };
        let [high, low] = unsafe { transmute.ints };
        Self {
            high: u128::from_be(high),
            low: u128::from_be(low),
        }
    }

    #[inline]
    pub const fn from_be_bytes_const(bytes: [u8; 32]) -> Self {
        // TODO: Deprecate this in a later Rust version, once `const_fn_union`
        //       is stabilized: https://github.com/rust-lang/rust/issues/51909

        let high = ((bytes[0] as u128) << 120)
            + ((bytes[1] as u128) << 112)
            + ((bytes[2] as u128) << 104)
            + ((bytes[3] as u128) << 96)
            + ((bytes[4] as u128) << 88)
            + ((bytes[5] as u128) << 80)
            + ((bytes[6] as u128) << 72)
            + ((bytes[7] as u128) << 64)
            + ((bytes[8] as u128) << 56)
            + ((bytes[9] as u128) << 48)
            + ((bytes[10] as u128) << 40)
            + ((bytes[11] as u128) << 32)
            + ((bytes[12] as u128) << 24)
            + ((bytes[13] as u128) << 16)
            + ((bytes[14] as u128) << 8)
            + (bytes[15] as u128);

        let low = ((bytes[16] as u128) << 120)
            + ((bytes[17] as u128) << 112)
            + ((bytes[18] as u128) << 104)
            + ((bytes[19] as u128) << 96)
            + ((bytes[20] as u128) << 88)
            + ((bytes[21] as u128) << 80)
            + ((bytes[22] as u128) << 72)
            + ((bytes[23] as u128) << 64)
            + ((bytes[24] as u128) << 56)
            + ((bytes[25] as u128) << 48)
            + ((bytes[26] as u128) << 40)
            + ((bytes[27] as u128) << 32)
            + ((bytes[28] as u128) << 24)
            + ((bytes[29] as u128) << 16)
            + ((bytes[30] as u128) << 8)
            + (bytes[31] as u128);

        Self { high, low }
    }

    #[inline]
    pub fn from_le_bytes(bytes: [u8; 32]) -> Self {
        // TODO: Optimize this further.
        let transmute = Transmute { bytes };
        let [low, high] = unsafe { transmute.ints };
        Self {
            high: u128::from_le(high),
            low: u128::from_le(low),
        }
    }

    #[inline]
    pub const fn from_le_bytes_const(bytes: [u8; 32]) -> Self {
        // TODO: Deprecate this in a later Rust version, once `const_fn_union`
        //       is stabilized: https://github.com/rust-lang/rust/issues/51909

        let low = ((bytes[15] as u128) << 120)
            + ((bytes[14] as u128) << 112)
            + ((bytes[13] as u128) << 104)
            + ((bytes[12] as u128) << 96)
            + ((bytes[11] as u128) << 88)
            + ((bytes[10] as u128) << 80)
            + ((bytes[9] as u128) << 72)
            + ((bytes[8] as u128) << 64)
            + ((bytes[7] as u128) << 56)
            + ((bytes[6] as u128) << 48)
            + ((bytes[5] as u128) << 40)
            + ((bytes[4] as u128) << 32)
            + ((bytes[3] as u128) << 24)
            + ((bytes[2] as u128) << 16)
            + ((bytes[1] as u128) << 8)
            + (bytes[0] as u128);

        let high = ((bytes[31] as u128) << 120)
            + ((bytes[30] as u128) << 112)
            + ((bytes[29] as u128) << 104)
            + ((bytes[28] as u128) << 96)
            + ((bytes[27] as u128) << 88)
            + ((bytes[26] as u128) << 80)
            + ((bytes[25] as u128) << 72)
            + ((bytes[24] as u128) << 64)
            + ((bytes[23] as u128) << 56)
            + ((bytes[22] as u128) << 48)
            + ((bytes[21] as u128) << 40)
            + ((bytes[20] as u128) << 32)
            + ((bytes[19] as u128) << 24)
            + ((bytes[18] as u128) << 16)
            + ((bytes[17] as u128) << 8)
            + (bytes[16] as u128);

        Self { high, low }
    }

    #[inline]
    pub fn from_ne_bytes(bytes: [u8; 32]) -> Self {
        #[cfg(target_endian = "big")]
        return Self::from_be_bytes(bytes);

        #[cfg(target_endian = "little")]
        return Self::from_le_bytes(bytes);
    }

    #[inline]
    pub const fn from_ne_bytes_const(bytes: [u8; 32]) -> Self {
        #[cfg(target_endian = "big")]
        return Self::from_be_bytes_const(bytes);

        #[cfg(target_endian = "little")]
        return Self::from_le_bytes_const(bytes);
    }
}

impl ops::BitAnd for U256 {
    type Output = Self;

    #[inline]
    fn bitand(self, rhs: Self) -> Self::Output {
        Self {
            high: self.high & rhs.high,
            low: self.low & rhs.low,
        }
    }
}

impl ops::BitOr for U256 {
    type Output = Self;

    #[inline]
    fn bitor(self, rhs: Self) -> Self::Output {
        Self {
            high: self.high | rhs.high,
            low: self.low | rhs.low,
        }
    }
}

impl ops::BitXor for U256 {
    type Output = Self;

    #[inline]
    fn bitxor(self, rhs: Self) -> Self::Output {
        Self {
            high: self.high ^ rhs.high,
            low: self.low ^ rhs.low,
        }
    }
}

impl ops::Not for U256 {
    type Output = Self;

    #[inline]
    fn not(self) -> Self::Output {
        Self {
            high: !self.high,
            low: !self.low,
        }
    }
}

impl ops::Rem<&Self> for U256 {
    type Output = Self;

    #[inline]
    fn rem(self, _rhs: &Self) -> Self::Output {
        // TODO
        self
    }
}

impl ops::Rem for U256 {
    type Output = Self;

    #[inline]
    fn rem(self, rhs: Self) -> Self::Output {
        #[cfg(debug_assertions)]
        let result = self.checked_rem(rhs).unwrap();

        #[cfg(not(debug_assertions))]
        let result = self.wrapping_rem(rhs);

        result
    }
}

impl ops::Div<&Self> for U256 {
    type Output = Self;

    #[inline]
    fn div(self, _rhs: &Self) -> Self::Output {
        // TODO
        self
    }
}

impl ops::Div for U256 {
    type Output = Self;

    #[inline]
    fn div(self, rhs: Self) -> Self::Output {
        #[cfg(debug_assertions)]
        let result = self.checked_div(rhs).unwrap();

        #[cfg(not(debug_assertions))]
        let result = self.wrapping_div(rhs);

        result
    }
}

impl ops::Sub<&Self> for U256 {
    type Output = Self;

    #[inline]
    fn sub(self, _rhs: &Self) -> Self::Output {
        // TODO
        self
    }
}

impl ops::Sub for U256 {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        #[cfg(debug_assertions)]
        let result = self.checked_sub(rhs).unwrap();

        #[cfg(not(debug_assertions))]
        let result = self.wrapping_sub(rhs);

        result
    }
}

impl ops::Mul<&Self> for U256 {
    type Output = Self;

    #[inline]
    fn mul(self, _rhs: &Self) -> Self::Output {
        // TODO
        self
    }
}

impl ops::Mul for U256 {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self::Output {
        #[cfg(debug_assertions)]
        let result = self.checked_mul(rhs).unwrap();

        #[cfg(not(debug_assertions))]
        let result = self.wrapping_mul(rhs);

        result
    }
}

impl ops::Add<&Self> for U256 {
    type Output = Self;

    #[inline]
    fn add(self, _rhs: &Self) -> Self::Output {
        // TODO
        self
    }
}

impl ops::Add for U256 {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        #[cfg(debug_assertions)]
        let result = self.checked_add(rhs).unwrap();

        #[cfg(not(debug_assertions))]
        let result = self.wrapping_add(rhs);

        result
    }
}

impl ops::AddAssign<&Self> for U256 {
    #[inline]
    fn add_assign(&mut self, _rhs: &Self) {
        // TODO
    }
}

impl ops::AddAssign for U256 {
    #[inline]
    fn add_assign(&mut self, _rhs: Self) {
        // TODO
    }
}

impl ops::SubAssign<&Self> for U256 {
    #[inline]
    fn sub_assign(&mut self, _rhs: &Self) {
        // TODO
    }
}

impl ops::SubAssign for U256 {
    #[inline]
    fn sub_assign(&mut self, _rhs: Self) {
        // TODO
    }
}

impl ops::MulAssign<&Self> for U256 {
    #[inline]
    fn mul_assign(&mut self, _rhs: &Self) {
        // TODO
    }
}

impl ops::MulAssign for U256 {
    #[inline]
    fn mul_assign(&mut self, _rhs: Self) {
        // TODO
    }
}

impl ops::DivAssign<&Self> for U256 {
    #[inline]
    fn div_assign(&mut self, _rhs: &Self) {
        // TODO
    }
}

impl ops::DivAssign for U256 {
    #[inline]
    fn div_assign(&mut self, _rhs: Self) {
        // TODO
    }
}

impl ops::RemAssign<&Self> for U256 {
    #[inline]
    fn rem_assign(&mut self, _rhs: &Self) {
        // TODO
    }
}

impl ops::RemAssign for U256 {
    #[inline]
    fn rem_assign(&mut self, _rhs: Self) {
        // TODO
    }
}

macro_rules! impl_shl {
    ($($int:ty, )+) => {
        $(
        impl ops::Shl<$int> for U256 {
            type Output = Self;

            #[inline]
            fn shl(self, rhs: $int) -> Self::Output {
                let low: u128 = rhs.try_into().unwrap();
                ops::Shl::<Self>::shl(self, Self { high: 0, low })
            }
        }
        )+
    }
}

macro_rules! impl_shr {
    ($($int:ty, )+) => {
        $(
        impl ops::Shr<$int> for U256 {
            type Output = Self;

            #[inline]
            fn shr(self, rhs: $int) -> Self::Output {
                let low: u128 = rhs.try_into().unwrap();
                ops::Shr::<Self>::shr(self, Self { high: 0, low })
            }
        }
        )+
    }
}

impl_shr!(i8, u8, i16, u16, i32, u32, i64, u64, i128, u128, isize, usize,);
impl_shl!(i8, u8, i16, u16, i32, u32, i64, u64, i128, u128, isize, usize,);

impl ops::Shl for U256 {
    type Output = Self;

    #[inline]
    fn shl(self, rhs: Self) -> Self::Output {
        #[cfg(debug_assertions)]
        let result = self.checked_shl(rhs).unwrap();

        #[cfg(not(debug_assertions))]
        let result = self.wrapping_shl(rhs);

        result
    }
}

impl ops::Shr for U256 {
    type Output = Self;

    #[inline]
    fn shr(self, rhs: Self) -> Self::Output {
        #[cfg(debug_assertions)]
        let result = self.checked_shr(rhs).unwrap();

        #[cfg(not(debug_assertions))]
        let result = self.wrapping_shr(rhs);

        result
    }
}

impl num::One for U256 {
    #[inline]
    fn one() -> Self {
        Self { high: 0, low: 1 }
    }
}

impl num::Zero for U256 {
    #[inline]
    fn zero() -> Self {
        Self { high: 0, low: 0 }
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.high == 0 && self.low == 0
    }
}

impl num::Bounded for U256 {
    #[inline]
    fn min_value() -> Self {
        U256::min_value()
    }

    #[inline]
    fn max_value() -> Self {
        U256::max_value()
    }
}

impl num::Saturating for U256 {
    #[inline]
    fn saturating_add(self, rhs: Self) -> Self {
        U256::saturating_add(self, rhs)
    }

    #[inline]
    fn saturating_sub(self, rhs: Self) -> Self {
        U256::saturating_sub(rhs, rhs)
    }
}

impl num::SaturatingMul for U256 {
    #[inline]
    fn saturating_mul(&self, rhs: &Self) -> Self {
        U256::saturating_mul(*self, *rhs)
    }
}

impl num::SaturatingSub for U256 {
    #[inline]
    fn saturating_sub(&self, rhs: &Self) -> Self {
        U256::saturating_sub(*self, *rhs)
    }
}

impl num::SaturatingAdd for U256 {
    #[inline]
    fn saturating_add(&self, rhs: &Self) -> Self {
        U256::saturating_add(*self, *rhs)
    }
}

impl<T> num::Pow<T> for U256
where
    T: Into<Self>,
{
    type Output = Self;

    #[inline]
    fn pow(self, rhs: T) -> Self {
        Self::pow(self, Into::<Self>::into(rhs))
    }
}

impl num::ToPrimitive for U256 {
    #[inline]
    fn to_u64(&self) -> Option<u64> {
        TryFrom::try_from(self).ok()
    }

    #[inline]
    fn to_i64(&self) -> Option<i64> {
        TryFrom::try_from(self).ok()
    }

    #[inline]
    fn to_isize(&self) -> Option<isize> {
        TryFrom::try_from(self).ok()
    }

    #[inline]
    fn to_i8(&self) -> Option<i8> {
        TryFrom::try_from(self).ok()
    }

    #[inline]
    fn to_i16(&self) -> Option<i16> {
        TryFrom::try_from(self).ok()
    }

    #[inline]
    fn to_i32(&self) -> Option<i32> {
        TryFrom::try_from(self).ok()
    }

    #[inline]
    fn to_i128(&self) -> Option<i128> {
        TryFrom::try_from(self).ok()
    }

    #[inline]
    fn to_usize(&self) -> Option<usize> {
        TryFrom::try_from(self).ok()
    }

    #[inline]
    fn to_u8(&self) -> Option<u8> {
        TryFrom::try_from(self).ok()
    }

    #[inline]
    fn to_u16(&self) -> Option<u16> {
        TryFrom::try_from(self).ok()
    }

    #[inline]
    fn to_u32(&self) -> Option<u32> {
        TryFrom::try_from(self).ok()
    }

    #[inline]
    fn to_u128(&self) -> Option<u128> {
        TryFrom::try_from(self).ok()
    }
}

impl num::NumCast for U256 {
    #[inline]
    fn from<T>(n: T) -> Option<Self>
    where
        T: num::ToPrimitive,
    {
        n.to_u128().map(Self::new)
    }
}

impl num::PrimInt for U256 {
    #[inline]
    fn count_ones(self) -> u32 {
        Self::count_ones(self)
    }

    #[inline]
    fn count_zeros(self) -> u32 {
        Self::count_zeros(self)
    }

    #[inline]
    fn leading_zeros(self) -> u32 {
        Self::leading_zeros(self)
    }

    #[inline]
    fn trailing_zeros(self) -> u32 {
        Self::trailing_zeros(self)
    }

    #[inline]
    fn rotate_left(self, cnt: u32) -> Self {
        Self::rotate_left(self, cnt)
    }

    #[inline]
    fn rotate_right(self, cnt: u32) -> Self {
        Self::rotate_right(self, cnt)
    }

    #[inline]
    fn signed_shr(self, cnt: u32) -> Self {
        Self::signed_shr(self, Self::from(cnt))
    }

    #[inline]
    fn unsigned_shr(self, cnt: u32) -> Self {
        ops::Shr::shr(self, cnt)
    }

    #[inline]
    fn signed_shl(self, cnt: u32) -> Self {
        Self::signed_shl(self, Self::from(cnt))
    }

    #[inline]
    fn unsigned_shl(self, cnt: u32) -> Self {
        ops::Shl::shl(self, cnt)
    }

    #[inline]
    fn swap_bytes(self) -> Self {
        Self::swap_bytes(self)
    }

    #[inline]
    fn from_be(v: Self) -> Self {
        Self::from_be(v)
    }

    #[inline]
    fn from_le(v: Self) -> Self {
        Self::from_le(v)
    }

    #[inline]
    fn to_be(self) -> Self {
        Self::to_be(self)
    }

    #[inline]
    fn to_le(self) -> Self {
        Self::to_le(self)
    }

    #[inline]
    fn pow(self, exp: u32) -> Self {
        Self::pow(self, Self::from(exp))
    }
}

impl num::Num for U256 {
    type FromStrRadixErr = (); // TODO

    fn from_str_radix(_: &str, _: u32) -> Result<Self, Self::FromStrRadixErr> {
        Err(()) // TODO
    }
}

impl num::CheckedAdd for U256 {
    #[inline]
    fn checked_add(&self, rhs: &Self) -> Option<Self> {
        U256::checked_add(*self, *rhs)
    }
}

impl num::CheckedSub for U256 {
    #[inline]
    fn checked_sub(&self, rhs: &Self) -> Option<Self> {
        U256::checked_sub(*self, *rhs)
    }
}

impl num::CheckedMul for U256 {
    #[inline]
    fn checked_mul(&self, rhs: &Self) -> Option<Self> {
        U256::checked_mul(*self, *rhs)
    }
}

impl num::CheckedDiv for U256 {
    #[inline]
    fn checked_div(&self, rhs: &Self) -> Option<Self> {
        U256::checked_div(*self, *rhs)
    }
}

impl num::CheckedRem for U256 {
    #[inline]
    fn checked_rem(&self, rhs: &Self) -> Option<Self> {
        U256::checked_rem(*self, *rhs)
    }
}

impl num::CheckedShl for U256 {
    #[inline]
    fn checked_shl(&self, rhs: u32) -> Option<Self> {
        U256::checked_shl(*self, rhs.into())
    }
}

impl num::CheckedShr for U256 {
    #[inline]
    fn checked_shr(&self, rhs: u32) -> Option<Self> {
        U256::checked_shr(*self, rhs.into())
    }
}

impl num::WrappingAdd for U256 {
    #[inline]
    fn wrapping_add(&self, rhs: &Self) -> Self {
        U256::wrapping_add(*self, *rhs)
    }
}

impl num::WrappingSub for U256 {
    #[inline]
    fn wrapping_sub(&self, rhs: &Self) -> Self {
        U256::wrapping_sub(*self, *rhs)
    }
}

impl num::WrappingMul for U256 {
    #[inline]
    fn wrapping_mul(&self, rhs: &Self) -> Self {
        U256::wrapping_mul(*self, *rhs)
    }
}

impl num::WrappingShl for U256 {
    #[inline]
    fn wrapping_shl(&self, rhs: u32) -> Self {
        U256::wrapping_shl(*self, rhs.into())
    }
}

impl num::WrappingShr for U256 {
    #[inline]
    fn wrapping_shr(&self, rhs: u32) -> Self {
        U256::wrapping_shr(*self, rhs.into())
    }
}

impl num::Unsigned for U256 {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn split_combine_max_value() {
        let expected = U256::max_value();
        let (s0, s1, s2, s3) = expected.split();

        let actual_hi = ((s0 as u128) << 64) + s1 as u128;
        let actual_lo = ((s2 as u128) << 64) + s3 as u128;
        let actual = U256::with_high_order(actual_hi, actual_lo);

        assert_eq!(expected, actual);
    }

    #[test]
    fn split_combine() {
        let expected = U256::with_high_order(
            0xa1a2a3a4a5a6a7a8b1b2b3b4b5b6b7b8,
            0xc1c2c3c4c5c6c7c8d1d2d3d4d5d6d7d8,
        );

        let (s0, s1, s2, s3) = expected.split();

        let actual_hi = ((s0 as u128) << 64) + s1 as u128;
        let actual_lo = ((s2 as u128) << 64) + s3 as u128;
        let actual = U256::with_high_order(actual_hi, actual_lo);

        assert_eq!(expected, actual);
    }
}
