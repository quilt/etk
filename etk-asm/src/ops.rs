use hex::ToHex;

use snafu::{Backtrace, Snafu};

use std::cmp::{Eq, PartialEq};
use std::convert::{TryFrom, TryInto};
use std::fmt;
use std::str::FromStr;

#[derive(Snafu, Debug)]
pub struct TryFromIntError {
    backtrace: Backtrace,
}

impl From<std::convert::Infallible> for TryFromIntError {
    fn from(e: std::convert::Infallible) -> Self {
        match e {}
    }
}

#[derive(Snafu, Debug)]
pub struct TryFromSliceError {
    backtrace: Backtrace,
}

#[derive(Clone, Eq, PartialEq)]
pub enum Imm<T> {
    Label(String),
    Constant(T),
}

impl<T> From<&str> for Imm<T> {
    fn from(label: &str) -> Self {
        Imm::Label(label.to_owned())
    }
}

impl<T> From<String> for Imm<T> {
    fn from(label: String) -> Self {
        Imm::Label(label)
    }
}

macro_rules! impl_from {
    ($ii:literal;) => {
        impl From<[u8; $ii]> for Imm<[u8; $ii]> {
            fn from(konst: [u8; $ii]) -> Self {
                Imm::Constant(konst)
            }
        }
    };

    ($ii:literal; $ty:ty $(, $rest:ty)* $(,)*) => {
        impl From<$ty> for Imm<[u8; $ii]> {
            fn from(x: $ty) -> Self {
                let mut output = [0u8; $ii];
                let bytes = x.to_be_bytes();
                let start = $ii - bytes.len();
                (&mut output[start..$ii]).copy_from_slice(&bytes);
                Imm::Constant(output)
            }
        }

        impl_from!($ii; $($rest,)*);
    }
}

macro_rules! impl_try_from {
    ($ii:literal;) => {
    };

    ($ii:literal; $ty:ty $(, $rest:ty)* $(,)*) => {
        impl TryFrom<$ty> for Imm<[u8; $ii]> {
            type Error = TryFromIntError;

            fn try_from(x: $ty) -> Result<Self, Self::Error> {
                let max = <$ty>::pow(2, 8 * $ii);

                if x >= max {
                    return TryFromIntContext.fail();
                }

                let mut output = [0u8; $ii];
                let bytes = x.to_be_bytes();
                let start = std::mem::size_of::<$ty>() - $ii;
                output.copy_from_slice(&bytes[start..]);
                Ok(Imm::Constant(output))
            }
        }

        impl_try_from!($ii; $($rest,)*);
    }
}

macro_rules! impl_try_from_slice {
    ($ii:literal) => {
        impl TryFrom<&[u8]> for Imm<[u8; $ii]> {
            type Error = TryFromSliceError;

            fn try_from(x: &[u8]) -> Result<Self, Self::Error> {
                if x.len() > $ii {
                    return TryFromSliceContext.fail();
                }

                let mut output = [0u8; $ii];
                output.copy_from_slice(x);
                Ok(Imm::Constant(output))
            }
        }
    };
}

impl_from!(1; u8);
impl_from!(2; u8, u16);
impl_from!(3; u8, u16);
impl_from!(4; u8, u16, u32);
impl_from!(5; u8, u16, u32);
impl_from!(6; u8, u16, u32);
impl_from!(7; u8, u16, u32);
impl_from!(8; u8, u16, u32, u64);
impl_from!(9; u8, u16, u32, u64);
impl_from!(10; u8, u16, u32, u64);
impl_from!(11; u8, u16, u32, u64);
impl_from!(12; u8, u16, u32, u64);
impl_from!(13; u8, u16, u32, u64);
impl_from!(14; u8, u16, u32, u64);
impl_from!(15; u8, u16, u32, u64);
impl_from!(16; u8, u16, u32, u64, u128);
impl_from!(17; u8, u16, u32, u64, u128);
impl_from!(18; u8, u16, u32, u64, u128);
impl_from!(19; u8, u16, u32, u64, u128);
impl_from!(20; u8, u16, u32, u64, u128);
impl_from!(21; u8, u16, u32, u64, u128);
impl_from!(22; u8, u16, u32, u64, u128);
impl_from!(23; u8, u16, u32, u64, u128);
impl_from!(24; u8, u16, u32, u64, u128);
impl_from!(25; u8, u16, u32, u64, u128);
impl_from!(26; u8, u16, u32, u64, u128);
impl_from!(27; u8, u16, u32, u64, u128);
impl_from!(28; u8, u16, u32, u64, u128);
impl_from!(29; u8, u16, u32, u64, u128);
impl_from!(30; u8, u16, u32, u64, u128);
impl_from!(31; u8, u16, u32, u64, u128);
impl_from!(32; u8, u16, u32, u64, u128);

impl_try_from_slice!(1);
impl_try_from_slice!(2);
impl_try_from_slice!(3);
impl_try_from_slice!(4);
impl_try_from_slice!(5);
impl_try_from_slice!(6);
impl_try_from_slice!(7);
impl_try_from_slice!(8);
impl_try_from_slice!(9);
impl_try_from_slice!(10);
impl_try_from_slice!(11);
impl_try_from_slice!(12);
impl_try_from_slice!(13);
impl_try_from_slice!(14);
impl_try_from_slice!(15);
impl_try_from_slice!(16);
impl_try_from_slice!(17);
impl_try_from_slice!(18);
impl_try_from_slice!(19);
impl_try_from_slice!(20);
impl_try_from_slice!(21);
impl_try_from_slice!(22);
impl_try_from_slice!(23);
impl_try_from_slice!(24);
impl_try_from_slice!(25);
impl_try_from_slice!(26);
impl_try_from_slice!(27);
impl_try_from_slice!(28);
impl_try_from_slice!(29);
impl_try_from_slice!(30);
impl_try_from_slice!(31);
impl_try_from_slice!(32);

impl_try_from!(1; u16, u32, u64, u128);
impl_try_from!(2; u32, u64, u128);
impl_try_from!(3; u32, u64, u128);
impl_try_from!(4; u64, u128);
impl_try_from!(5; u64, u128);
impl_try_from!(6; u64, u128);
impl_try_from!(7; u64, u128);
impl_try_from!(8; u128);
impl_try_from!(9; u128);
impl_try_from!(10; u128);
impl_try_from!(11; u128);
impl_try_from!(12; u128);
impl_try_from!(13; u128);
impl_try_from!(14; u128);
impl_try_from!(15; u128);

impl<T> fmt::Debug for Imm<T>
where
    T: ToHex,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Imm::Label(s) => write!(f, r#"Imm::Label("{}")"#, s),
            Imm::Constant(c) => write!(f, "Imm::Constant(0x{})", c.encode_hex::<String>()),
        }
    }
}

impl<T> fmt::Display for Imm<T>
where
    T: ToHex,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Imm::Label(s) => write!(f, ":{}", s),
            Imm::Constant(c) => write!(f, "0x{}", c.encode_hex::<String>()),
        }
    }
}

pub trait Immediate<const N: usize>: fmt::Debug + Clone + Eq + PartialEq {
    fn extra_len() -> usize {
        N
    }
}

impl<T, const N: usize> Immediate<N> for [T; N] where T: fmt::Debug + Clone + Eq + PartialEq {}
impl<const N: usize> Immediate<N> for Imm<[u8; N]> {}
impl<const N: usize> Immediate<N> for () {}

pub trait ImmediateTypes: fmt::Debug + Clone + Eq + PartialEq {
    // TODO: Technically `Self` doesn't need to implement anything, but it makes
    //       derive(...) work on `Op`.

    type P1: Immediate<1>;
    type P2: Immediate<2>;
    type P3: Immediate<3>;
    type P4: Immediate<4>;
    type P5: Immediate<5>;
    type P6: Immediate<6>;
    type P7: Immediate<7>;
    type P8: Immediate<8>;
    type P9: Immediate<9>;
    type P10: Immediate<10>;
    type P11: Immediate<11>;
    type P12: Immediate<12>;
    type P13: Immediate<13>;
    type P14: Immediate<14>;
    type P15: Immediate<15>;
    type P16: Immediate<16>;
    type P17: Immediate<17>;
    type P18: Immediate<18>;
    type P19: Immediate<19>;
    type P20: Immediate<20>;
    type P21: Immediate<21>;
    type P22: Immediate<22>;
    type P23: Immediate<23>;
    type P24: Immediate<24>;
    type P25: Immediate<25>;
    type P26: Immediate<26>;
    type P27: Immediate<27>;
    type P28: Immediate<28>;
    type P29: Immediate<29>;
    type P30: Immediate<30>;
    type P31: Immediate<31>;
    type P32: Immediate<32>;
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Concrete {}

impl ImmediateTypes for Concrete {
    type P1 = [u8; 1];
    type P2 = [u8; 2];
    type P3 = [u8; 3];
    type P4 = [u8; 4];
    type P5 = [u8; 5];
    type P6 = [u8; 6];
    type P7 = [u8; 7];
    type P8 = [u8; 8];
    type P9 = [u8; 9];
    type P10 = [u8; 10];
    type P11 = [u8; 11];
    type P12 = [u8; 12];
    type P13 = [u8; 13];
    type P14 = [u8; 14];
    type P15 = [u8; 15];
    type P16 = [u8; 16];
    type P17 = [u8; 17];
    type P18 = [u8; 18];
    type P19 = [u8; 19];
    type P20 = [u8; 20];
    type P21 = [u8; 21];
    type P22 = [u8; 22];
    type P23 = [u8; 23];
    type P24 = [u8; 24];
    type P25 = [u8; 25];
    type P26 = [u8; 26];
    type P27 = [u8; 27];
    type P28 = [u8; 28];
    type P29 = [u8; 29];
    type P30 = [u8; 30];
    type P31 = [u8; 31];
    type P32 = [u8; 32];
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Abstract {}

impl ImmediateTypes for Abstract {
    type P1 = Imm<[u8; 1]>;
    type P2 = Imm<[u8; 2]>;
    type P3 = Imm<[u8; 3]>;
    type P4 = Imm<[u8; 4]>;
    type P5 = Imm<[u8; 5]>;
    type P6 = Imm<[u8; 6]>;
    type P7 = Imm<[u8; 7]>;
    type P8 = Imm<[u8; 8]>;
    type P9 = Imm<[u8; 9]>;
    type P10 = Imm<[u8; 10]>;
    type P11 = Imm<[u8; 11]>;
    type P12 = Imm<[u8; 12]>;
    type P13 = Imm<[u8; 13]>;
    type P14 = Imm<[u8; 14]>;
    type P15 = Imm<[u8; 15]>;
    type P16 = Imm<[u8; 16]>;
    type P17 = Imm<[u8; 17]>;
    type P18 = Imm<[u8; 18]>;
    type P19 = Imm<[u8; 19]>;
    type P20 = Imm<[u8; 20]>;
    type P21 = Imm<[u8; 21]>;
    type P22 = Imm<[u8; 22]>;
    type P23 = Imm<[u8; 23]>;
    type P24 = Imm<[u8; 24]>;
    type P25 = Imm<[u8; 25]>;
    type P26 = Imm<[u8; 26]>;
    type P27 = Imm<[u8; 27]>;
    type P28 = Imm<[u8; 28]>;
    type P29 = Imm<[u8; 29]>;
    type P30 = Imm<[u8; 30]>;
    type P31 = Imm<[u8; 31]>;
    type P32 = Imm<[u8; 32]>;
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Spec {}

impl ImmediateTypes for Spec {
    type P1 = ();
    type P2 = ();
    type P3 = ();
    type P4 = ();
    type P5 = ();
    type P6 = ();
    type P7 = ();
    type P8 = ();
    type P9 = ();
    type P10 = ();
    type P11 = ();
    type P12 = ();
    type P13 = ();
    type P14 = ();
    type P15 = ();
    type P16 = ();
    type P17 = ();
    type P18 = ();
    type P19 = ();
    type P20 = ();
    type P21 = ();
    type P22 = ();
    type P23 = ();
    type P24 = ();
    type P25 = ();
    type P26 = ();
    type P27 = ();
    type P28 = ();
    type P29 = ();
    type P30 = ();
    type P31 = ();
    type P32 = ();
}

macro_rules! tuple {
    ($arg:ident) => {
        ()
    };
}

macro_rules! default {
    ($arg:ident) => {
        Default::default()
    };
}

macro_rules! pat {
    ($op:ident) => {
        Self::$op
    };
    ($op:ident, $arg:ident) => {
        Self::$op(_)
    };
}

macro_rules! pat_cap {
    ($cap:ident, $op:ident) => {
        Self::$op
    };
    ($cap:ident, $op:ident, $arg:ident) => {
        Self::$op($cap)
    };
}

macro_rules! write_cap {
    ($f:ident, $sp:ident, $cap:expr) => {
        write!($f, "{}", $sp)
    };
    ($f:ident, $sp:ident, $cap:expr, $arg:ident) => {
        write!($f, "{} {}", $sp, $cap)
    };
}

macro_rules! pat_const {
    ($cap:ident, $op:ident) => {
        Self::$op
    };
    ($cap:ident, $op:ident, $arg:ident) => {
        Self::$op(Imm::Constant($cap))
    };
}

macro_rules! pat_label {
    ($cap:ident, $op:ident) => { Self::$op };
    ($cap:ident, $op:ident, $arg:ident) => { Self::$op(Imm::Label(ref $cap)) };
}

macro_rules! ret_label {
    ($cap:ident) => {
        None
    };
    ($cap:ident, $arg:ident) => {
        Some($cap)
    };
}

macro_rules! ret_realize {
    ($op:ident, $addr:ident) => {
        panic!()
    };
    ($op:ident, $addr:ident, $arg:ident) => {
        Op::$op($addr.try_into()?)
    };
}

macro_rules! ret_concretize {
    ($op:ident, $addr:ident) => {
        Op::$op
    };
    ($op:ident, $addr:ident, $arg:ident) => {
        Op::$op($addr)
    };
}

macro_rules! ret_assemble {
    ($op:ident) => {
        return
    };
    ($addr:ident, $arg:ident) => {
        $addr as &[u8]
    };
}

macro_rules! pat_spec {
    ($op:ident) => {
        Op::<Spec>::$op
    };
    ($op:ident, $arg:ident) => {
        Op::<Spec>::$op(_)
    };
}

macro_rules! ret_new {
    ($op:ident) => {
        Some(Self::$op)
    };
    ($op:ident, $arg:ident) => {
        None
    };
}

macro_rules! ret_with_immediate {
    ($imm:ident, $op:ident) => {
        panic!()
    };
    ($imm:ident, $op:ident, $arg:ident) => {
        Self::$op($imm.try_into()?)
    };
}

macro_rules! ret_with_label {
    ($imm:ident, $op:ident) => {
        panic!()
    };
    ($imm:ident, $op:ident, $arg:ident) => {
        Self::$op($imm.into())
    };
}

macro_rules! ret_from_slice {
    ($imm:ident, $op:ident) => {
        Self::$op
    };
    ($imm:ident, $op:ident, $arg:ident) => {
        Self::$op(TryFrom::try_from(&$imm[1..]).unwrap())
    };
}

macro_rules! extra_len {
    () => {
        0
    };
    ($arg:ident) => {{
        fn helper<T: ImmediateTypes>() -> u32 {
            T::$arg::extra_len().try_into().unwrap()
        }
        helper::<Spec>()
    }};
}

macro_rules! to_u8 {
    ($test:ident, $c:expr; $first:ident, ) => {
        0u8
    };
    ($test:ident, $c:expr; $first:ident$(|$arg:ident)?, $($rest:ident$(|$args:ident)?, )+) => {
        if matches!($test, pat!($first$(, $arg)?)) {
            $c
        } else {
            to_u8!($test, $c + 1u8; $($rest$(|$args)?, )+)
        }
    };
}

macro_rules! or_false {
    () => {
        false
    };
    ($v:expr) => {
        $v
    };
}

macro_rules! ops {
    ($($op:ident(
        mnemonic = $mnemonic:literal
        $(, arg = $arg:ident )?
        $(, exit = $exit:expr)?
        $(, jump = $jmp:expr)?
        $(, jump_target = $jt:expr)?),
    )*) => {
        #[derive(Debug, Clone, PartialEq, Eq)]
        pub enum Op<I = Abstract> where I: ImmediateTypes {
            $($op$((I::$arg))?, )*
        }

        impl<I> Op<I> where I: ImmediateTypes {
            pub fn new(spec: Op<Spec>) -> Option<Self> {
                match spec {
                    $(
                        pat_spec!($op$(, $arg)?) => ret_new!($op$(, $arg)?),
                    )*
                }
            }

            pub fn specifier(&self) -> Op<Spec> {
                match self {
                    $(
                        pat!($op$(, $arg)?) => Op::$op$((default!($arg)))?,
                    )*
                }
            }

            pub fn is_jump_target(&self) -> bool {
                match self {
                    $(
                        pat!($op$(, $arg)?) => or_false!($($jt)?),
                    )*
                }
            }

            pub fn is_exit(&self) -> bool {
                match self {
                    $(
                        pat!($op$(, $arg)?) => or_false!($($exit)?),
                    )*
                }
            }

            pub fn is_jump(&self) -> bool {
                match self {
                    $(
                        pat!($op$(, $arg)?) => or_false!($($jmp)?),
                    )*
                }
            }
        }

        pub type Specifier = Op<Spec>;

        impl Copy for Op<Spec> {}

        impl Op<Spec> {
            const LUT: [Op<Spec>; 256] = [
                $(
                    Op::$op$((tuple!($arg)))?,
                )*
            ];

            const fn to_u8(self) -> u8 {
                to_u8!(self, 0; $($op$(|$arg)?, )*)
            }

            pub fn extra_len(self) -> u32 {
                match self {
                    $(
                        pat!($op$(, $arg)?) => extra_len!($($arg)?),
                    )*
                }
            }
        }

        impl From<u8> for Op<Spec> {
            fn from(v: u8) -> Self {
                Self::LUT[v as usize]
            }
        }

        impl From<Op<Spec>> for u8 {
            fn from(sp: Op<Spec>) -> u8 {
                sp.to_u8()
            }
        }

        impl FromStr for Op<Spec> {
            type Err = UnknownSpecifier;

            fn from_str(text: &str) -> Result<Self, Self::Err> {
                let result = match text {
                    $(
                        $mnemonic => Op::$op$((default!($arg)))?,
                    )*

                    _ => return Err(UnknownSpecifier(())),
                };

                Ok(result)
            }
        }

        impl fmt::Display for Op<Spec> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                let txt = match self {
                    $(
                        pat!($op$(, $arg)?) => $mnemonic,
                    )*
                };
                write!(f, "{}", txt)
            }
        }

        pub type AbstractOp = Op<Abstract>;

        impl Op<Abstract> {
            pub fn with_label<S: Into<String>>(spec: Op<Spec>, lbl: S) -> Self {
                let lbl = lbl.into();

                match spec {
                    $(
                        pat_spec!($op$(, $arg)?) => ret_with_label!(lbl, $op$(, $arg)?),
                    )*
                }
            }

            pub fn with_immediate(spec: Op<Spec>, imm: &[u8]) -> Result<Self, TryFromSliceError> {
                let op = match spec {
                    $(
                        pat_spec!($op$(, $arg)?) => ret_with_immediate!(imm, $op$(, $arg)?),
                    )*
                };

                Ok(op)
            }

            /// The label to be pushed on the stack. Only relevant for push instructions.
            pub(crate) fn immediate_label(&self) -> Option<&str> {
                match self {
                    $(
                        pat_label!(a, $op$(, $arg)?) => ret_label!(a$(, $arg)?),
                    )*
                    _ => None,
                }
            }

            // TODO: Rename `realize`
            pub(crate) fn realize(&self, address: u32) -> Result<Self, TryFromIntError> {
                let op = match self {
                    $(
                        pat_label!(_a, $op$(, $arg)?) => ret_realize!($op, address$(, $arg)?),
                    )*
                    _ => panic!("only push ops with labels can be realized"),
                };
                Ok(op)
            }

            pub(crate) fn concretize(self) -> Op<Concrete> {
                match self {
                    $(
                        pat_const!(a, $op$(, $arg)?) => ret_concretize!($op, a$(, $arg)?),
                    )*
                    _ => panic!("labels must be resolved be concretizing"),
                }
            }
        }

        impl fmt::Display for Op<Abstract> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                let sp = self.specifier();

                match self {
                    $(
                        pat_cap!(a, $op$(, $arg)?) => {
                            write_cap!(f, sp, a$(, $arg)?)
                        }
                    )*
                }
            }
        }

        pub type ConcreteOp = Op<Concrete>;

        impl Op<Concrete> {
            pub fn with_immediate(spec: Op<Spec>, imm: &[u8]) -> Result<Self, std::array::TryFromSliceError> {
                let op = match spec {
                    $(
                        pat_spec!($op$(, $arg)?) => ret_with_immediate!(imm, $op$(, $arg)?),
                    )*
                };

                Ok(op)
            }

            pub fn from_slice(bytes: &[u8]) -> Self {
                let specifier: Op<Spec> = Op::from(bytes[0]);
                let sz = specifier.extra_len() as usize + 1;

                if bytes.len() != sz {
                    panic!(
                        "got {} bytes for {}, expected {}",
                        bytes.len(),
                        specifier,
                        sz
                    );
                }

                match specifier {
                    $(
                        pat_spec!($op$(, $arg)?) => ret_from_slice!(bytes, $op$(, $arg)?),
                    )*
                }
            }

            pub(crate) fn assemble(&self, buf: &mut Vec<u8>) {
                buf.push(self.specifier().into());

                let args = match self {
                    $(
                        pat_cap!(a, $op$(, $arg)?) => {
                            ret_assemble!(a$(, $arg)?)
                        }
                    )*
                };

                buf.extend_from_slice(args);
            }
        }

        impl fmt::Display for Op<Concrete> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                let sp = self.specifier();

                match self {
                    $(
                        pat_cap!(a, $op$(, $arg)?) => {
                            write_cap!(f, sp, Imm::Constant(a)$(, $arg)?)
                        }
                    )*
                }
            }
        }

    }
}

ops! {
    Stop(mnemonic="stop", exit=true),
    Add(mnemonic="add"),
    Mul(mnemonic="mul"),
    Sub(mnemonic="sub"),
    Div(mnemonic="div"),
    SDiv(mnemonic="sdiv"),
    Mod(mnemonic="mod"),
    SMod(mnemonic="smod"),
    AddMod(mnemonic="addmod"),
    MulMod(mnemonic="mulmod"),
    Exp(mnemonic="exp"),
    SignExtend(mnemonic="signextend"),

    Invalid0c(mnemonic="invalid_0c", exit=true),
    Invalid0d(mnemonic="invalid_0d", exit=true),
    Invalid0e(mnemonic="invalid_0e", exit=true),
    Invalid0f(mnemonic="invalid_0f", exit=true),

    Lt(mnemonic="lt"),
    Gt(mnemonic="gt"),
    SLt(mnemonic="slt"),
    SGt(mnemonic="sgt"),
    Eq(mnemonic="eq"),
    IsZero(mnemonic="iszero"),
    And(mnemonic="and"),
    Or(mnemonic="or"),
    Xor(mnemonic="xor"),
    Not(mnemonic="not"),
    Byte(mnemonic="byte"),
    Shl(mnemonic="shl"),
    Shr(mnemonic="shr"),
    Sar(mnemonic="sar"),

    Invalid1e(mnemonic="invalid_1e", exit=true),
    Invalid1f(mnemonic="invalid_1f", exit=true),

    Keccak256(mnemonic="keccak256"),

    Invalid21(mnemonic="invalid_21", exit=true),
    Invalid22(mnemonic="invalid_22", exit=true),
    Invalid23(mnemonic="invalid_23", exit=true),
    Invalid24(mnemonic="invalid_24", exit=true),
    Invalid25(mnemonic="invalid_25", exit=true),
    Invalid26(mnemonic="invalid_26", exit=true),
    Invalid27(mnemonic="invalid_27", exit=true),
    Invalid28(mnemonic="invalid_28", exit=true),
    Invalid29(mnemonic="invalid_29", exit=true),
    Invalid2a(mnemonic="invalid_2a", exit=true),
    Invalid2b(mnemonic="invalid_2b", exit=true),
    Invalid2c(mnemonic="invalid_2c", exit=true),
    Invalid2d(mnemonic="invalid_2d", exit=true),
    Invalid2e(mnemonic="invalid_2e", exit=true),
    Invalid2f(mnemonic="invalid_2f", exit=true),

    Address(mnemonic="address"),
    Balance(mnemonic="balance"),
    Origin(mnemonic="origin"),
    Caller(mnemonic="caller"),
    CallValue(mnemonic="callvalue"),
    CallDataLoad(mnemonic="calldataload"),
    CallDataSize(mnemonic="calldatasize"),
    CallDataCopy(mnemonic="calldatacopy"),
    CodeSize(mnemonic="codesize"),
    CodeCopy(mnemonic="codecopy"),
    GasPrice(mnemonic="gasprice"),
    ExtCodeSize(mnemonic="extcodesize"),
    ExtCodeCopy(mnemonic="extcodecopy"),
    ReturnDataSize(mnemonic="returndatasize"),
    ReturnDataCopy(mnemonic="returndatacopy"),
    ExtCodeHash(mnemonic="extcodehash"),
    BlockHash(mnemonic="blockhash"),
    Coinbase(mnemonic="coinbase"),
    Timestamp(mnemonic="timestamp"),
    Number(mnemonic="number"),
    Difficulty(mnemonic="difficulty"),
    GasLimit(mnemonic="gaslimit"),
    ChainId(mnemonic="chainid"),

    Invalid47(mnemonic="invalid_47", exit=true),
    Invalid48(mnemonic="invalid_48", exit=true),
    Invalid49(mnemonic="invalid_49", exit=true),
    Invalid4a(mnemonic="invalid_4a", exit=true),
    Invalid4b(mnemonic="invalid_4b", exit=true),
    Invalid4c(mnemonic="invalid_4c", exit=true),
    Invalid4d(mnemonic="invalid_4d", exit=true),
    Invalid4e(mnemonic="invalid_4e", exit=true),
    Invalid4f(mnemonic="invalid_4f", exit=true),

    Pop(mnemonic="pop"),
    MLoad(mnemonic="mload"),
    MStore(mnemonic="mstore"),
    MStore8(mnemonic="mstore8"),
    SLoad(mnemonic="sload"),
    SStore(mnemonic="sstore"),
    Jump(mnemonic="jump", jump=true),
    JumpI(mnemonic="jumpi", jump=true),
    GetPc(mnemonic="pc"),
    MSize(mnemonic="msize"),
    Gas(mnemonic="gas"),
    JumpDest(mnemonic="jumpdest", jump_target=true),

    Invalid5c(mnemonic="invalid_5c", exit=true),
    Invalid5d(mnemonic="invalid_5d", exit=true),
    Invalid5e(mnemonic="invalid_5e", exit=true),
    Invalid5f(mnemonic="invalid_5f", exit=true),

    Push1(mnemonic="push1", arg=P1),
    Push2(mnemonic="push2", arg=P2),
    Push3(mnemonic="push3", arg=P3),
    Push4(mnemonic="push4", arg=P4),
    Push5(mnemonic="push5", arg=P5),
    Push6(mnemonic="push6", arg=P6),
    Push7(mnemonic="push7", arg=P7),
    Push8(mnemonic="push8", arg=P8),
    Push9(mnemonic="push9", arg=P9),
    Push10(mnemonic="push10", arg=P10),
    Push11(mnemonic="push11", arg=P11),
    Push12(mnemonic="push12", arg=P12),
    Push13(mnemonic="push13", arg=P13),
    Push14(mnemonic="push14", arg=P14),
    Push15(mnemonic="push15", arg=P15),
    Push16(mnemonic="push16", arg=P16),
    Push17(mnemonic="push17", arg=P17),
    Push18(mnemonic="push18", arg=P18),
    Push19(mnemonic="push19", arg=P19),
    Push20(mnemonic="push20", arg=P20),
    Push21(mnemonic="push21", arg=P21),
    Push22(mnemonic="push22", arg=P22),
    Push23(mnemonic="push23", arg=P23),
    Push24(mnemonic="push24", arg=P24),
    Push25(mnemonic="push25", arg=P25),
    Push26(mnemonic="push26", arg=P26),
    Push27(mnemonic="push27", arg=P27),
    Push28(mnemonic="push28", arg=P28),
    Push29(mnemonic="push29", arg=P29),
    Push30(mnemonic="push30", arg=P30),
    Push31(mnemonic="push31", arg=P31),
    Push32(mnemonic="push32", arg=P32),

    // Push(mnemonic="push"),

    Dup1(mnemonic="dup1"),
    Dup2(mnemonic="dup2"),
    Dup3(mnemonic="dup3"),
    Dup4(mnemonic="dup4"),
    Dup5(mnemonic="dup5"),
    Dup6(mnemonic="dup6"),
    Dup7(mnemonic="dup7"),
    Dup8(mnemonic="dup8"),
    Dup9(mnemonic="dup9"),
    Dup10(mnemonic="dup10"),
    Dup11(mnemonic="dup11"),
    Dup12(mnemonic="dup12"),
    Dup13(mnemonic="dup13"),
    Dup14(mnemonic="dup14"),
    Dup15(mnemonic="dup15"),
    Dup16(mnemonic="dup16"),
    Swap1(mnemonic="swap1"),
    Swap2(mnemonic="swap2"),
    Swap3(mnemonic="swap3"),
    Swap4(mnemonic="swap4"),
    Swap5(mnemonic="swap5"),
    Swap6(mnemonic="swap6"),
    Swap7(mnemonic="swap7"),
    Swap8(mnemonic="swap8"),
    Swap9(mnemonic="swap9"),
    Swap10(mnemonic="swap10"),
    Swap11(mnemonic="swap11"),
    Swap12(mnemonic="swap12"),
    Swap13(mnemonic="swap13"),
    Swap14(mnemonic="swap14"),
    Swap15(mnemonic="swap15"),
    Swap16(mnemonic="swap16"),
    Log0(mnemonic="log0"),
    Log1(mnemonic="log1"),
    Log2(mnemonic="log2"),
    Log3(mnemonic="log3"),
    Log4(mnemonic="log4"),

    InvalidA5(mnemonic="invalid_a5", exit=true),
    InvalidA6(mnemonic="invalid_a6", exit=true),
    InvalidA7(mnemonic="invalid_a7", exit=true),
    InvalidA8(mnemonic="invalid_a8", exit=true),
    InvalidA9(mnemonic="invalid_a9", exit=true),
    InvalidAa(mnemonic="invalid_aa", exit=true),
    InvalidAb(mnemonic="invalid_ab", exit=true),
    InvalidAc(mnemonic="invalid_ac", exit=true),
    InvalidAd(mnemonic="invalid_ad", exit=true),
    InvalidAe(mnemonic="invalid_ae", exit=true),
    InvalidAf(mnemonic="invalid_af", exit=true),

    JumpTo(mnemonic="jumpto", jump=true),
    JumpIf(mnemonic="jumpif", jump=true),
    JumpSub(mnemonic="jumpsub", jump=true),

    InvalidB3(mnemonic="invalid_b3", exit=true),

    JumpSubV(mnemonic="jumpsubv", jump=true),
    BeginSub(mnemonic="beginsub", jump_target=true),
    BeginData(mnemonic="begindata"),

    InvalidB7(mnemonic="invalid_b7", exit=true),

    ReturnSub(mnemonic="returnsub", jump=true),
    PutLocal(mnemonic="putlocal"),
    GetLocal(mnemonic="getlocal"),

    InvalidBb(mnemonic="invalid_bb", exit=true),
    InvalidBc(mnemonic="invalid_bc", exit=true),
    InvalidBd(mnemonic="invalid_bd", exit=true),
    InvalidBe(mnemonic="invalid_be", exit=true),
    InvalidBf(mnemonic="invalid_bf", exit=true),
    InvalidC0(mnemonic="invalid_c0", exit=true),
    InvalidC1(mnemonic="invalid_c1", exit=true),
    InvalidC2(mnemonic="invalid_c2", exit=true),
    InvalidC3(mnemonic="invalid_c3", exit=true),
    InvalidC4(mnemonic="invalid_c4", exit=true),
    InvalidC5(mnemonic="invalid_c5", exit=true),
    InvalidC6(mnemonic="invalid_c6", exit=true),
    InvalidC7(mnemonic="invalid_c7", exit=true),
    InvalidC8(mnemonic="invalid_c8", exit=true),
    InvalidC9(mnemonic="invalid_c9", exit=true),
    InvalidCa(mnemonic="invalid_ca", exit=true),
    InvalidCb(mnemonic="invalid_cb", exit=true),
    InvalidCc(mnemonic="invalid_cc", exit=true),
    InvalidCd(mnemonic="invalid_cd", exit=true),
    InvalidCe(mnemonic="invalid_ce", exit=true),
    InvalidCf(mnemonic="invalid_cf", exit=true),
    InvalidD0(mnemonic="invalid_d0", exit=true),
    InvalidD1(mnemonic="invalid_d1", exit=true),
    InvalidD2(mnemonic="invalid_d2", exit=true),
    InvalidD3(mnemonic="invalid_d3", exit=true),
    InvalidD4(mnemonic="invalid_d4", exit=true),
    InvalidD5(mnemonic="invalid_d5", exit=true),
    InvalidD6(mnemonic="invalid_d6", exit=true),
    InvalidD7(mnemonic="invalid_d7", exit=true),
    InvalidD8(mnemonic="invalid_d8", exit=true),
    InvalidD9(mnemonic="invalid_d9", exit=true),
    InvalidDa(mnemonic="invalid_da", exit=true),
    InvalidDb(mnemonic="invalid_db", exit=true),
    InvalidDc(mnemonic="invalid_dc", exit=true),
    InvalidDd(mnemonic="invalid_dd", exit=true),
    InvalidDe(mnemonic="invalid_de", exit=true),
    InvalidDf(mnemonic="invalid_df", exit=true),
    InvalidE0(mnemonic="invalid_e0", exit=true),

    SLoadBytes(mnemonic="sloadbytes"),
    SStoreBytes(mnemonic="sstorebytes"),
    SSize(mnemonic="ssize"),

    InvalidE4(mnemonic="invalid_e4", exit=true),
    InvalidE5(mnemonic="invalid_e5", exit=true),
    InvalidE6(mnemonic="invalid_e6", exit=true),
    InvalidE7(mnemonic="invalid_e7", exit=true),
    InvalidE8(mnemonic="invalid_e8", exit=true),
    InvalidE9(mnemonic="invalid_e9", exit=true),
    InvalidEa(mnemonic="invalid_ea", exit=true),
    InvalidEb(mnemonic="invalid_eb", exit=true),
    InvalidEc(mnemonic="invalid_ec", exit=true),
    InvalidEd(mnemonic="invalid_ed", exit=true),
    InvalidEe(mnemonic="invalid_ee", exit=true),
    InvalidEf(mnemonic="invalid_ef", exit=true),

    Create(mnemonic="create"),
    Call(mnemonic="call"),
    CallCode(mnemonic="callcode"),
    Return(mnemonic="return", exit=true),
    DelegateCall(mnemonic="delegatecall"),
    Create2(mnemonic="create2"),

    InvalidF6(mnemonic="invalid_f6", exit=true),
    InvalidF7(mnemonic="invalid_f7", exit=true),
    InvalidF8(mnemonic="invalid_f8", exit=true),
    InvalidF9(mnemonic="invalid_f9", exit=true),

    StaticCall(mnemonic="staticcall"),

    InvalidFb(mnemonic="invalid_fb", exit=true),

    TxExecGas(mnemonic="txexecgas"),
    Revert(mnemonic="revert", exit=true),
    Invalid(mnemonic="invalid", exit=true),
    SelfDestruct(mnemonic="selfdestruct", exit=true),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct LabelOp {
    op: AbstractOp,
    label: Option<String>,
}

impl LabelOp {
    pub fn new(op: AbstractOp) -> Self {
        LabelOp { op, label: None }
    }

    pub fn with_label<S>(op: AbstractOp, label: S) -> Self
    where
        S: Into<String>,
    {
        LabelOp {
            op,
            label: Some(label.into()),
        }
    }

    pub fn op(&self) -> &AbstractOp {
        &self.op
    }

    pub fn op_mut(&mut self) -> &mut AbstractOp {
        &mut self.op
    }

    pub fn label(&self) -> Option<&str> {
        self.label.as_ref().map(AsRef::as_ref)
    }

    pub fn specifier(&self) -> Specifier {
        self.op.specifier()
    }

    pub fn immediate_label(&self) -> Option<&str> {
        self.op.immediate_label()
    }

    pub(crate) fn realize(&self, address: u32) -> Result<Self, TryFromIntError> {
        Ok(Self {
            op: self.op.realize(address)?,
            label: self.label.clone(),
        })
    }

    pub(crate) fn concretize(self) -> Op<Concrete> {
        self.op.concretize()
    }
}

impl From<AbstractOp> for LabelOp {
    fn from(op: AbstractOp) -> Self {
        Self::new(op)
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
#[non_exhaustive]
pub struct UnknownSpecifier(());

#[cfg(test)]
mod tests {
    use assert_matches::assert_matches;

    use std::convert::TryInto;

    use super::*;

    #[test]
    fn u8_into_imm1() {
        let x: u8 = 0xdc;
        let imm: Imm<[u8; 1]> = x.into();
        assert_matches!(imm, Imm::Constant([0xdc]));
    }

    #[test]
    fn u16_try_into_imm1() {
        let x: u16 = 0xFF;
        let imm: Imm<[u8; 1]> = x.try_into().unwrap();
        assert_matches!(imm, Imm::Constant([0xFF]));
    }

    #[test]
    fn imm1_try_from_u16_too_large() {
        let x: u16 = 0x0100;
        Imm::<[u8; 1]>::try_from(x).unwrap_err();
    }

    #[test]
    fn imm15_try_from_u128_too_large() {
        let x: u128 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF + 0x1;
        Imm::<[u8; 15]>::try_from(x).unwrap_err();
    }

    #[test]
    fn u8_into_imm2() {
        let x: u8 = 0xdc;
        let imm: Imm<[u8; 2]> = x.into();
        assert_matches!(imm, Imm::Constant([0x00, 0xdc]));
    }

    #[test]
    fn u16_into_imm2() {
        let x: u16 = 0xfedc;
        let imm: Imm<[u8; 2]> = x.into();
        assert_matches!(imm, Imm::Constant([0xfe, 0xdc]));
    }

    #[test]
    fn u128_into_imm32() {
        let x: u128 = 0x1023456789abcdef0123456789abcdef;
        let imm: Imm<[u8; 32]> = x.into();
        assert_matches!(
            imm,
            Imm::Constant([
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x10, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef, 0x01, 0x23, 0x45, 0x67,
                0x89, 0xab, 0xcd, 0xef,
            ])
        );
    }

    #[test]
    fn specifier_from_u8() {
        for ii in 0..u8::MAX {
            let parsed = Specifier::try_from(ii).unwrap();
            if ii == 0xfe {
                assert_eq!(Specifier::Invalid, parsed);
            } else {
                assert_ne!(Specifier::Invalid, parsed);
            }
        }
    }

    #[test]
    fn specifier_through_str() {
        for ii in 0..u8::MAX {
            let spec = Specifier::try_from(ii).unwrap();
            let txt = spec.to_string();
            let parsed: Specifier = txt.parse().unwrap();
            assert_eq!(spec, parsed);
        }
    }

    #[test]
    fn op_new() {
        for ii in 0..u8::MAX {
            let spec = Specifier::try_from(ii).unwrap();
            let op = AbstractOp::new(spec);
            if spec.extra_len() > 0 {
                assert_eq!(op, None);
            } else {
                let op = op.unwrap();
                assert_eq!(op.specifier(), spec);
            }
        }
    }
}
