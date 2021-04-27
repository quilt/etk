use hex::ToHex;

use num_enum::{FromPrimitive, IntoPrimitive};

use snafu::{Backtrace, Snafu};

use std::convert::{TryFrom, TryInto};
use std::fmt;
use std::str::FromStr;

#[derive(Snafu, Debug)]
pub struct TryFromIntError {
    backtrace: Backtrace,
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

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Op {
    Stop,
    Add,
    Mul,
    Sub,
    Div,
    SDiv,
    Mod,
    SMod,
    AddMod,
    MulMod,
    Exp,
    SignExtend,

    Lt,
    Gt,
    SLt,
    SGt,
    Eq,
    IsZero,
    And,
    Or,
    Xor,
    Not,
    Byte,
    Shl,
    Shr,
    Sar,
    Keccak256,

    Address,
    Balance,
    Origin,
    Caller,
    CallValue,
    CallDataLoad,
    CallDataSize,
    CallDataCopy,
    CodeSize,
    CodeCopy,
    GasPrice,
    ExtCodeSize,
    ExtCodeCopy,
    ReturnDataSize,
    ReturnDataCopy,
    ExtCodeHash,
    BlockHash,
    Coinbase,
    Timestamp,
    Number,
    Difficulty,
    GasLimit,
    ChainId,

    Pop,
    MLoad,
    MStore,
    MStore8,
    SLoad,
    SStore,
    Jump,
    JumpI,
    GetPc,
    MSize,
    Gas,
    JumpDest(Option<String>),

    Push1(Imm<[u8; 1]>),
    Push2(Imm<[u8; 2]>),
    Push3(Imm<[u8; 3]>),
    Push4(Imm<[u8; 4]>),
    Push5(Imm<[u8; 5]>),
    Push6(Imm<[u8; 6]>),
    Push7(Imm<[u8; 7]>),
    Push8(Imm<[u8; 8]>),
    Push9(Imm<[u8; 9]>),
    Push10(Imm<[u8; 10]>),
    Push11(Imm<[u8; 11]>),
    Push12(Imm<[u8; 12]>),
    Push13(Imm<[u8; 13]>),
    Push14(Imm<[u8; 14]>),
    Push15(Imm<[u8; 15]>),
    Push16(Imm<[u8; 16]>),
    Push17(Imm<[u8; 17]>),
    Push18(Imm<[u8; 18]>),
    Push19(Imm<[u8; 19]>),
    Push20(Imm<[u8; 20]>),
    Push21(Imm<[u8; 21]>),
    Push22(Imm<[u8; 22]>),
    Push23(Imm<[u8; 23]>),
    Push24(Imm<[u8; 24]>),
    Push25(Imm<[u8; 25]>),
    Push26(Imm<[u8; 26]>),
    Push27(Imm<[u8; 27]>),
    Push28(Imm<[u8; 28]>),
    Push29(Imm<[u8; 29]>),
    Push30(Imm<[u8; 30]>),
    Push31(Imm<[u8; 31]>),
    Push32(Imm<[u8; 32]>),
    Dup1,
    Dup2,
    Dup3,
    Dup4,
    Dup5,
    Dup6,
    Dup7,
    Dup8,
    Dup9,
    Dup10,
    Dup11,
    Dup12,
    Dup13,
    Dup14,
    Dup15,
    Dup16,
    Swap1,
    Swap2,
    Swap3,
    Swap4,
    Swap5,
    Swap6,
    Swap7,
    Swap8,
    Swap9,
    Swap10,
    Swap11,
    Swap12,
    Swap13,
    Swap14,
    Swap15,
    Swap16,
    Log0,
    Log1,
    Log2,
    Log3,
    Log4,

    JumpTo,
    JumpIf,
    JumpSub,
    JumpSubV,
    BeginSub,
    BeginData,
    ReturnSub,
    PutLocal,
    GetLocal,

    SLoadBytes,
    SStoreBytes,
    SSize,

    Create,
    Call,
    CallCode,
    Return,
    DelegateCall,
    Create2,

    StaticCall,

    TxExecGas,
    Revert,
    Invalid,
    SelfDestruct,

    Invalid0c,
    Invalid0d,
    Invalid0e,
    Invalid0f,

    Invalid1e,
    Invalid1f,

    Invalid21,
    Invalid22,
    Invalid23,
    Invalid24,
    Invalid25,
    Invalid26,
    Invalid27,
    Invalid28,
    Invalid29,
    Invalid2a,
    Invalid2b,
    Invalid2c,
    Invalid2d,
    Invalid2e,
    Invalid2f,

    Invalid47,
    Invalid48,
    Invalid49,
    Invalid4a,
    Invalid4b,
    Invalid4c,
    Invalid4d,
    Invalid4e,
    Invalid4f,

    Invalid5c,
    Invalid5d,
    Invalid5e,
    Invalid5f,

    InvalidA5,
    InvalidA6,
    InvalidA7,
    InvalidA8,
    InvalidA9,
    InvalidAa,
    InvalidAb,
    InvalidAc,
    InvalidAd,
    InvalidAe,
    InvalidAf,

    InvalidB3,

    InvalidB7,

    InvalidBb,
    InvalidBc,
    InvalidBd,
    InvalidBe,
    InvalidBf,
    InvalidC0,
    InvalidC1,
    InvalidC2,
    InvalidC3,
    InvalidC4,
    InvalidC5,
    InvalidC6,
    InvalidC7,
    InvalidC8,
    InvalidC9,
    InvalidCa,
    InvalidCb,
    InvalidCc,
    InvalidCd,
    InvalidCe,
    InvalidCf,
    InvalidD0,
    InvalidD1,
    InvalidD2,
    InvalidD3,
    InvalidD4,
    InvalidD5,
    InvalidD6,
    InvalidD7,
    InvalidD8,
    InvalidD9,
    InvalidDa,
    InvalidDb,
    InvalidDc,
    InvalidDd,
    InvalidDe,
    InvalidDf,
    InvalidE0,

    InvalidE4,
    InvalidE5,
    InvalidE6,
    InvalidE7,
    InvalidE8,
    InvalidE9,
    InvalidEa,
    InvalidEb,
    InvalidEc,
    InvalidEd,
    InvalidEe,
    InvalidEf,

    InvalidF6,
    InvalidF7,
    InvalidF8,
    InvalidF9,

    InvalidFb,
}

impl Op {
    pub fn new(spec: Specifier) -> Option<Self> {
        let result = match spec {
            Specifier::Stop => Op::Stop,
            Specifier::Add => Op::Add,
            Specifier::Mul => Op::Mul,
            Specifier::Sub => Op::Sub,
            Specifier::Div => Op::Div,
            Specifier::SDiv => Op::SDiv,
            Specifier::Mod => Op::Mod,
            Specifier::SMod => Op::SMod,
            Specifier::AddMod => Op::AddMod,
            Specifier::MulMod => Op::MulMod,
            Specifier::Exp => Op::Exp,
            Specifier::SignExtend => Op::SignExtend,

            Specifier::Invalid0c => Op::Invalid0c,
            Specifier::Invalid0d => Op::Invalid0d,
            Specifier::Invalid0e => Op::Invalid0e,
            Specifier::Invalid0f => Op::Invalid0f,

            Specifier::Lt => Op::Lt,
            Specifier::Gt => Op::Gt,
            Specifier::SLt => Op::SLt,
            Specifier::SGt => Op::SGt,
            Specifier::Eq => Op::Eq,
            Specifier::IsZero => Op::IsZero,
            Specifier::And => Op::And,
            Specifier::Or => Op::Or,
            Specifier::Xor => Op::Xor,
            Specifier::Not => Op::Not,
            Specifier::Byte => Op::Byte,
            Specifier::Shl => Op::Shl,
            Specifier::Shr => Op::Shr,
            Specifier::Sar => Op::Sar,

            Specifier::Invalid1e => Op::Invalid1e,
            Specifier::Invalid1f => Op::Invalid1f,

            Specifier::Keccak256 => Op::Keccak256,

            Specifier::Invalid21 => Op::Invalid21,
            Specifier::Invalid22 => Op::Invalid22,
            Specifier::Invalid23 => Op::Invalid23,
            Specifier::Invalid24 => Op::Invalid24,
            Specifier::Invalid25 => Op::Invalid25,
            Specifier::Invalid26 => Op::Invalid26,
            Specifier::Invalid27 => Op::Invalid27,
            Specifier::Invalid28 => Op::Invalid28,
            Specifier::Invalid29 => Op::Invalid29,
            Specifier::Invalid2a => Op::Invalid2a,
            Specifier::Invalid2b => Op::Invalid2b,
            Specifier::Invalid2c => Op::Invalid2c,
            Specifier::Invalid2d => Op::Invalid2d,
            Specifier::Invalid2e => Op::Invalid2e,
            Specifier::Invalid2f => Op::Invalid2f,

            Specifier::Address => Op::Address,
            Specifier::Balance => Op::Balance,
            Specifier::Origin => Op::Origin,
            Specifier::Caller => Op::Caller,
            Specifier::CallValue => Op::CallValue,
            Specifier::CallDataLoad => Op::CallDataLoad,
            Specifier::CallDataSize => Op::CallDataSize,
            Specifier::CallDataCopy => Op::CallDataCopy,
            Specifier::CodeSize => Op::CodeSize,
            Specifier::CodeCopy => Op::CodeCopy,
            Specifier::GasPrice => Op::GasPrice,
            Specifier::ExtCodeSize => Op::ExtCodeSize,
            Specifier::ExtCodeCopy => Op::ExtCodeCopy,
            Specifier::ReturnDataSize => Op::ReturnDataSize,
            Specifier::ReturnDataCopy => Op::ReturnDataCopy,
            Specifier::ExtCodeHash => Op::ExtCodeHash,
            Specifier::BlockHash => Op::BlockHash,
            Specifier::Coinbase => Op::Coinbase,
            Specifier::Timestamp => Op::Timestamp,
            Specifier::Number => Op::Number,
            Specifier::Difficulty => Op::Difficulty,
            Specifier::GasLimit => Op::GasLimit,
            Specifier::ChainId => Op::ChainId,

            Specifier::Invalid47 => Op::Invalid47,
            Specifier::Invalid48 => Op::Invalid48,
            Specifier::Invalid49 => Op::Invalid49,
            Specifier::Invalid4a => Op::Invalid4a,
            Specifier::Invalid4b => Op::Invalid4b,
            Specifier::Invalid4c => Op::Invalid4c,
            Specifier::Invalid4d => Op::Invalid4d,
            Specifier::Invalid4e => Op::Invalid4e,
            Specifier::Invalid4f => Op::Invalid4f,

            Specifier::Pop => Op::Pop,
            Specifier::MLoad => Op::MLoad,
            Specifier::MStore => Op::MStore,
            Specifier::MStore8 => Op::MStore8,
            Specifier::SLoad => Op::SLoad,
            Specifier::SStore => Op::SStore,
            Specifier::Jump => Op::Jump,
            Specifier::JumpI => Op::JumpI,
            Specifier::GetPc => Op::GetPc,
            Specifier::MSize => Op::MSize,
            Specifier::Gas => Op::Gas,

            Specifier::Invalid5c => Op::Invalid5c,
            Specifier::Invalid5d => Op::Invalid5d,
            Specifier::Invalid5e => Op::Invalid5e,
            Specifier::Invalid5f => Op::Invalid5f,

            Specifier::Dup1 => Op::Dup1,
            Specifier::Dup2 => Op::Dup2,
            Specifier::Dup3 => Op::Dup3,
            Specifier::Dup4 => Op::Dup4,
            Specifier::Dup5 => Op::Dup5,
            Specifier::Dup6 => Op::Dup6,
            Specifier::Dup7 => Op::Dup7,
            Specifier::Dup8 => Op::Dup8,
            Specifier::Dup9 => Op::Dup9,
            Specifier::Dup10 => Op::Dup10,
            Specifier::Dup11 => Op::Dup11,
            Specifier::Dup12 => Op::Dup12,
            Specifier::Dup13 => Op::Dup13,
            Specifier::Dup14 => Op::Dup14,
            Specifier::Dup15 => Op::Dup15,
            Specifier::Dup16 => Op::Dup16,
            Specifier::Swap1 => Op::Swap1,
            Specifier::Swap2 => Op::Swap2,
            Specifier::Swap3 => Op::Swap3,
            Specifier::Swap4 => Op::Swap4,
            Specifier::Swap5 => Op::Swap5,
            Specifier::Swap6 => Op::Swap6,
            Specifier::Swap7 => Op::Swap7,
            Specifier::Swap8 => Op::Swap8,
            Specifier::Swap9 => Op::Swap9,
            Specifier::Swap10 => Op::Swap10,
            Specifier::Swap11 => Op::Swap11,
            Specifier::Swap12 => Op::Swap12,
            Specifier::Swap13 => Op::Swap13,
            Specifier::Swap14 => Op::Swap14,
            Specifier::Swap15 => Op::Swap15,
            Specifier::Swap16 => Op::Swap16,
            Specifier::Log0 => Op::Log0,
            Specifier::Log1 => Op::Log1,
            Specifier::Log2 => Op::Log2,
            Specifier::Log3 => Op::Log3,
            Specifier::Log4 => Op::Log4,

            Specifier::InvalidA5 => Op::InvalidA5,
            Specifier::InvalidA6 => Op::InvalidA6,
            Specifier::InvalidA7 => Op::InvalidA7,
            Specifier::InvalidA8 => Op::InvalidA8,
            Specifier::InvalidA9 => Op::InvalidA9,
            Specifier::InvalidAa => Op::InvalidAa,
            Specifier::InvalidAb => Op::InvalidAb,
            Specifier::InvalidAc => Op::InvalidAc,
            Specifier::InvalidAd => Op::InvalidAd,
            Specifier::InvalidAe => Op::InvalidAe,
            Specifier::InvalidAf => Op::InvalidAf,

            Specifier::JumpTo => Op::JumpTo,
            Specifier::JumpIf => Op::JumpIf,
            Specifier::JumpSub => Op::JumpSub,

            Specifier::InvalidB3 => Op::InvalidB3,

            Specifier::JumpSubV => Op::JumpSubV,
            Specifier::BeginSub => Op::BeginSub,
            Specifier::BeginData => Op::BeginData,

            Specifier::InvalidB7 => Op::InvalidB7,

            Specifier::ReturnSub => Op::ReturnSub,
            Specifier::PutLocal => Op::PutLocal,
            Specifier::GetLocal => Op::GetLocal,

            Specifier::InvalidBb => Op::InvalidBb,
            Specifier::InvalidBc => Op::InvalidBc,
            Specifier::InvalidBd => Op::InvalidBd,
            Specifier::InvalidBe => Op::InvalidBe,
            Specifier::InvalidBf => Op::InvalidBf,
            Specifier::InvalidC0 => Op::InvalidC0,
            Specifier::InvalidC1 => Op::InvalidC1,
            Specifier::InvalidC2 => Op::InvalidC2,
            Specifier::InvalidC3 => Op::InvalidC3,
            Specifier::InvalidC4 => Op::InvalidC4,
            Specifier::InvalidC5 => Op::InvalidC5,
            Specifier::InvalidC6 => Op::InvalidC6,
            Specifier::InvalidC7 => Op::InvalidC7,
            Specifier::InvalidC8 => Op::InvalidC8,
            Specifier::InvalidC9 => Op::InvalidC9,
            Specifier::InvalidCa => Op::InvalidCa,
            Specifier::InvalidCb => Op::InvalidCb,
            Specifier::InvalidCc => Op::InvalidCc,
            Specifier::InvalidCd => Op::InvalidCd,
            Specifier::InvalidCe => Op::InvalidCe,
            Specifier::InvalidCf => Op::InvalidCf,
            Specifier::InvalidD0 => Op::InvalidD0,
            Specifier::InvalidD1 => Op::InvalidD1,
            Specifier::InvalidD2 => Op::InvalidD2,
            Specifier::InvalidD3 => Op::InvalidD3,
            Specifier::InvalidD4 => Op::InvalidD4,
            Specifier::InvalidD5 => Op::InvalidD5,
            Specifier::InvalidD6 => Op::InvalidD6,
            Specifier::InvalidD7 => Op::InvalidD7,
            Specifier::InvalidD8 => Op::InvalidD8,
            Specifier::InvalidD9 => Op::InvalidD9,
            Specifier::InvalidDa => Op::InvalidDa,
            Specifier::InvalidDb => Op::InvalidDb,
            Specifier::InvalidDc => Op::InvalidDc,
            Specifier::InvalidDd => Op::InvalidDd,
            Specifier::InvalidDe => Op::InvalidDe,
            Specifier::InvalidDf => Op::InvalidDf,
            Specifier::InvalidE0 => Op::InvalidE0,

            Specifier::SLoadBytes => Op::SLoadBytes,
            Specifier::SStoreBytes => Op::SStoreBytes,
            Specifier::SSize => Op::SSize,

            Specifier::InvalidE4 => Op::InvalidE4,
            Specifier::InvalidE5 => Op::InvalidE5,
            Specifier::InvalidE6 => Op::InvalidE6,
            Specifier::InvalidE7 => Op::InvalidE7,
            Specifier::InvalidE8 => Op::InvalidE8,
            Specifier::InvalidE9 => Op::InvalidE9,
            Specifier::InvalidEa => Op::InvalidEa,
            Specifier::InvalidEb => Op::InvalidEb,
            Specifier::InvalidEc => Op::InvalidEc,
            Specifier::InvalidEd => Op::InvalidEd,
            Specifier::InvalidEe => Op::InvalidEe,
            Specifier::InvalidEf => Op::InvalidEf,

            Specifier::Create => Op::Create,
            Specifier::Call => Op::Call,
            Specifier::CallCode => Op::CallCode,
            Specifier::Return => Op::Return,
            Specifier::DelegateCall => Op::DelegateCall,
            Specifier::Create2 => Op::Create2,

            Specifier::InvalidF6 => Op::InvalidF6,
            Specifier::InvalidF7 => Op::InvalidF7,
            Specifier::InvalidF8 => Op::InvalidF8,
            Specifier::InvalidF9 => Op::InvalidF9,

            Specifier::StaticCall => Op::StaticCall,

            Specifier::InvalidFb => Op::InvalidFb,

            Specifier::TxExecGas => Op::TxExecGas,
            Specifier::Revert => Op::Revert,
            Specifier::Invalid => Op::Invalid,
            Specifier::SelfDestruct => Op::SelfDestruct,

            Specifier::JumpDest
            | Specifier::Push1
            | Specifier::Push2
            | Specifier::Push3
            | Specifier::Push4
            | Specifier::Push5
            | Specifier::Push6
            | Specifier::Push7
            | Specifier::Push8
            | Specifier::Push9
            | Specifier::Push10
            | Specifier::Push11
            | Specifier::Push12
            | Specifier::Push13
            | Specifier::Push14
            | Specifier::Push15
            | Specifier::Push16
            | Specifier::Push17
            | Specifier::Push18
            | Specifier::Push19
            | Specifier::Push20
            | Specifier::Push21
            | Specifier::Push22
            | Specifier::Push23
            | Specifier::Push24
            | Specifier::Push25
            | Specifier::Push26
            | Specifier::Push27
            | Specifier::Push28
            | Specifier::Push29
            | Specifier::Push30
            | Specifier::Push31
            | Specifier::Push32 => return None,
        };

        Some(result)
    }

    pub(crate) fn push1(a: &[u8]) -> Self {
        Op::Push1(Imm::Constant(a[1..].try_into().unwrap()))
    }

    pub(crate) fn push2(a: &[u8]) -> Self {
        Op::Push2(Imm::Constant(a[1..].try_into().unwrap()))
    }

    pub(crate) fn push3(a: &[u8]) -> Self {
        Op::Push3(Imm::Constant(a[1..].try_into().unwrap()))
    }

    pub(crate) fn push4(a: &[u8]) -> Self {
        Op::Push4(Imm::Constant(a[1..].try_into().unwrap()))
    }

    pub(crate) fn push5(a: &[u8]) -> Self {
        Op::Push5(Imm::Constant(a[1..].try_into().unwrap()))
    }

    pub(crate) fn push6(a: &[u8]) -> Self {
        Op::Push6(Imm::Constant(a[1..].try_into().unwrap()))
    }

    pub(crate) fn push7(a: &[u8]) -> Self {
        Op::Push7(Imm::Constant(a[1..].try_into().unwrap()))
    }

    pub(crate) fn push8(a: &[u8]) -> Self {
        Op::Push8(Imm::Constant(a[1..].try_into().unwrap()))
    }

    pub(crate) fn push9(a: &[u8]) -> Self {
        Op::Push9(Imm::Constant(a[1..].try_into().unwrap()))
    }

    pub(crate) fn push10(a: &[u8]) -> Self {
        Op::Push10(Imm::Constant(a[1..].try_into().unwrap()))
    }

    pub(crate) fn push11(a: &[u8]) -> Self {
        Op::Push11(Imm::Constant(a[1..].try_into().unwrap()))
    }

    pub(crate) fn push12(a: &[u8]) -> Self {
        Op::Push12(Imm::Constant(a[1..].try_into().unwrap()))
    }

    pub(crate) fn push13(a: &[u8]) -> Self {
        Op::Push13(Imm::Constant(a[1..].try_into().unwrap()))
    }

    pub(crate) fn push14(a: &[u8]) -> Self {
        Op::Push14(Imm::Constant(a[1..].try_into().unwrap()))
    }

    pub(crate) fn push15(a: &[u8]) -> Self {
        Op::Push15(Imm::Constant(a[1..].try_into().unwrap()))
    }

    pub(crate) fn push16(a: &[u8]) -> Self {
        Op::Push16(Imm::Constant(a[1..].try_into().unwrap()))
    }

    pub(crate) fn push17(a: &[u8]) -> Self {
        Op::Push17(Imm::Constant(a[1..].try_into().unwrap()))
    }

    pub(crate) fn push18(a: &[u8]) -> Self {
        Op::Push18(Imm::Constant(a[1..].try_into().unwrap()))
    }

    pub(crate) fn push19(a: &[u8]) -> Self {
        Op::Push19(Imm::Constant(a[1..].try_into().unwrap()))
    }

    pub(crate) fn push20(a: &[u8]) -> Self {
        Op::Push20(Imm::Constant(a[1..].try_into().unwrap()))
    }

    pub(crate) fn push21(a: &[u8]) -> Self {
        Op::Push21(Imm::Constant(a[1..].try_into().unwrap()))
    }

    pub(crate) fn push22(a: &[u8]) -> Self {
        Op::Push22(Imm::Constant(a[1..].try_into().unwrap()))
    }

    pub(crate) fn push23(a: &[u8]) -> Self {
        Op::Push23(Imm::Constant(a[1..].try_into().unwrap()))
    }

    pub(crate) fn push24(a: &[u8]) -> Self {
        Op::Push24(Imm::Constant(a[1..].try_into().unwrap()))
    }

    pub(crate) fn push25(a: &[u8]) -> Self {
        Op::Push25(Imm::Constant(a[1..].try_into().unwrap()))
    }

    pub(crate) fn push26(a: &[u8]) -> Self {
        Op::Push26(Imm::Constant(a[1..].try_into().unwrap()))
    }

    pub(crate) fn push27(a: &[u8]) -> Self {
        Op::Push27(Imm::Constant(a[1..].try_into().unwrap()))
    }

    pub(crate) fn push28(a: &[u8]) -> Self {
        Op::Push28(Imm::Constant(a[1..].try_into().unwrap()))
    }

    pub(crate) fn push29(a: &[u8]) -> Self {
        Op::Push29(Imm::Constant(a[1..].try_into().unwrap()))
    }

    pub(crate) fn push30(a: &[u8]) -> Self {
        Op::Push30(Imm::Constant(a[1..].try_into().unwrap()))
    }

    pub(crate) fn push31(a: &[u8]) -> Self {
        Op::Push31(Imm::Constant(a[1..].try_into().unwrap()))
    }

    pub(crate) fn push32(a: &[u8]) -> Self {
        Op::Push32(Imm::Constant(a[1..].try_into().unwrap()))
    }

    pub fn is_exit(&self) -> bool {
        self.specifier().is_exit()
    }

    pub fn is_jump(&self) -> bool {
        self.specifier().is_jump()
    }

    pub fn is_jump_target(&self) -> bool {
        self.specifier().is_jump_target()
    }

    pub fn from_slice(bytes: &[u8]) -> Self {
        let specifier = Specifier::from(bytes[0]);
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
            Specifier::Stop => Op::Stop,
            Specifier::Add => Op::Add,
            Specifier::Mul => Op::Mul,
            Specifier::Sub => Op::Sub,
            Specifier::Div => Op::Div,
            Specifier::SDiv => Op::SDiv,
            Specifier::Mod => Op::Mod,
            Specifier::SMod => Op::SMod,
            Specifier::AddMod => Op::AddMod,
            Specifier::MulMod => Op::MulMod,
            Specifier::Exp => Op::Exp,
            Specifier::SignExtend => Op::SignExtend,

            Specifier::Invalid0c => Op::Invalid0c,
            Specifier::Invalid0d => Op::Invalid0d,
            Specifier::Invalid0e => Op::Invalid0e,
            Specifier::Invalid0f => Op::Invalid0f,

            Specifier::Lt => Op::Lt,
            Specifier::Gt => Op::Gt,
            Specifier::SLt => Op::SLt,
            Specifier::SGt => Op::SGt,
            Specifier::Eq => Op::Eq,
            Specifier::IsZero => Op::IsZero,
            Specifier::And => Op::And,
            Specifier::Or => Op::Or,
            Specifier::Xor => Op::Xor,
            Specifier::Not => Op::Not,
            Specifier::Byte => Op::Byte,
            Specifier::Shl => Op::Shl,
            Specifier::Shr => Op::Shr,
            Specifier::Sar => Op::Sar,

            Specifier::Invalid1e => Op::Invalid1e,
            Specifier::Invalid1f => Op::Invalid1f,

            Specifier::Keccak256 => Op::Keccak256,

            Specifier::Invalid21 => Op::Invalid21,
            Specifier::Invalid22 => Op::Invalid22,
            Specifier::Invalid23 => Op::Invalid23,
            Specifier::Invalid24 => Op::Invalid24,
            Specifier::Invalid25 => Op::Invalid25,
            Specifier::Invalid26 => Op::Invalid26,
            Specifier::Invalid27 => Op::Invalid27,
            Specifier::Invalid28 => Op::Invalid28,
            Specifier::Invalid29 => Op::Invalid29,
            Specifier::Invalid2a => Op::Invalid2a,
            Specifier::Invalid2b => Op::Invalid2b,
            Specifier::Invalid2c => Op::Invalid2c,
            Specifier::Invalid2d => Op::Invalid2d,
            Specifier::Invalid2e => Op::Invalid2e,
            Specifier::Invalid2f => Op::Invalid2f,

            Specifier::Address => Op::Address,
            Specifier::Balance => Op::Balance,
            Specifier::Origin => Op::Origin,
            Specifier::Caller => Op::Caller,
            Specifier::CallValue => Op::CallValue,
            Specifier::CallDataLoad => Op::CallDataLoad,
            Specifier::CallDataSize => Op::CallDataSize,
            Specifier::CallDataCopy => Op::CallDataCopy,
            Specifier::CodeSize => Op::CodeSize,
            Specifier::CodeCopy => Op::CodeCopy,
            Specifier::GasPrice => Op::GasPrice,
            Specifier::ExtCodeSize => Op::ExtCodeSize,
            Specifier::ExtCodeCopy => Op::ExtCodeCopy,
            Specifier::ReturnDataSize => Op::ReturnDataSize,
            Specifier::ReturnDataCopy => Op::ReturnDataCopy,
            Specifier::ExtCodeHash => Op::ExtCodeHash,
            Specifier::BlockHash => Op::BlockHash,
            Specifier::Coinbase => Op::Coinbase,
            Specifier::Timestamp => Op::Timestamp,
            Specifier::Number => Op::Number,
            Specifier::Difficulty => Op::Difficulty,
            Specifier::GasLimit => Op::GasLimit,
            Specifier::ChainId => Op::ChainId,

            Specifier::Invalid47 => Op::Invalid47,
            Specifier::Invalid48 => Op::Invalid48,
            Specifier::Invalid49 => Op::Invalid49,
            Specifier::Invalid4a => Op::Invalid4a,
            Specifier::Invalid4b => Op::Invalid4b,
            Specifier::Invalid4c => Op::Invalid4c,
            Specifier::Invalid4d => Op::Invalid4d,
            Specifier::Invalid4e => Op::Invalid4e,
            Specifier::Invalid4f => Op::Invalid4f,

            Specifier::Pop => Op::Pop,
            Specifier::MLoad => Op::MLoad,
            Specifier::MStore => Op::MStore,
            Specifier::MStore8 => Op::MStore8,
            Specifier::SLoad => Op::SLoad,
            Specifier::SStore => Op::SStore,
            Specifier::Jump => Op::Jump,
            Specifier::JumpI => Op::JumpI,
            Specifier::GetPc => Op::GetPc,
            Specifier::MSize => Op::MSize,
            Specifier::Gas => Op::Gas,
            Specifier::JumpDest => Op::JumpDest(None),

            Specifier::Invalid5c => Op::Invalid5c,
            Specifier::Invalid5d => Op::Invalid5d,
            Specifier::Invalid5e => Op::Invalid5e,
            Specifier::Invalid5f => Op::Invalid5f,

            Specifier::Push1 => Op::push1(bytes),
            Specifier::Push2 => Op::push2(bytes),
            Specifier::Push3 => Op::push3(bytes),
            Specifier::Push4 => Op::push4(bytes),
            Specifier::Push5 => Op::push5(bytes),
            Specifier::Push6 => Op::push6(bytes),
            Specifier::Push7 => Op::push7(bytes),
            Specifier::Push8 => Op::push8(bytes),
            Specifier::Push9 => Op::push9(bytes),
            Specifier::Push10 => Op::push10(bytes),
            Specifier::Push11 => Op::push11(bytes),
            Specifier::Push12 => Op::push12(bytes),
            Specifier::Push13 => Op::push13(bytes),
            Specifier::Push14 => Op::push14(bytes),
            Specifier::Push15 => Op::push15(bytes),
            Specifier::Push16 => Op::push16(bytes),
            Specifier::Push17 => Op::push17(bytes),
            Specifier::Push18 => Op::push18(bytes),
            Specifier::Push19 => Op::push19(bytes),
            Specifier::Push20 => Op::push20(bytes),
            Specifier::Push21 => Op::push21(bytes),
            Specifier::Push22 => Op::push22(bytes),
            Specifier::Push23 => Op::push23(bytes),
            Specifier::Push24 => Op::push24(bytes),
            Specifier::Push25 => Op::push25(bytes),
            Specifier::Push26 => Op::push26(bytes),
            Specifier::Push27 => Op::push27(bytes),
            Specifier::Push28 => Op::push28(bytes),
            Specifier::Push29 => Op::push29(bytes),
            Specifier::Push30 => Op::push30(bytes),
            Specifier::Push31 => Op::push31(bytes),
            Specifier::Push32 => Op::push32(bytes),
            Specifier::Dup1 => Op::Dup1,
            Specifier::Dup2 => Op::Dup2,
            Specifier::Dup3 => Op::Dup3,
            Specifier::Dup4 => Op::Dup4,
            Specifier::Dup5 => Op::Dup5,
            Specifier::Dup6 => Op::Dup6,
            Specifier::Dup7 => Op::Dup7,
            Specifier::Dup8 => Op::Dup8,
            Specifier::Dup9 => Op::Dup9,
            Specifier::Dup10 => Op::Dup10,
            Specifier::Dup11 => Op::Dup11,
            Specifier::Dup12 => Op::Dup12,
            Specifier::Dup13 => Op::Dup13,
            Specifier::Dup14 => Op::Dup14,
            Specifier::Dup15 => Op::Dup15,
            Specifier::Dup16 => Op::Dup16,
            Specifier::Swap1 => Op::Swap1,
            Specifier::Swap2 => Op::Swap2,
            Specifier::Swap3 => Op::Swap3,
            Specifier::Swap4 => Op::Swap4,
            Specifier::Swap5 => Op::Swap5,
            Specifier::Swap6 => Op::Swap6,
            Specifier::Swap7 => Op::Swap7,
            Specifier::Swap8 => Op::Swap8,
            Specifier::Swap9 => Op::Swap9,
            Specifier::Swap10 => Op::Swap10,
            Specifier::Swap11 => Op::Swap11,
            Specifier::Swap12 => Op::Swap12,
            Specifier::Swap13 => Op::Swap13,
            Specifier::Swap14 => Op::Swap14,
            Specifier::Swap15 => Op::Swap15,
            Specifier::Swap16 => Op::Swap16,
            Specifier::Log0 => Op::Log0,
            Specifier::Log1 => Op::Log1,
            Specifier::Log2 => Op::Log2,
            Specifier::Log3 => Op::Log3,
            Specifier::Log4 => Op::Log4,

            Specifier::InvalidA5 => Op::InvalidA5,
            Specifier::InvalidA6 => Op::InvalidA6,
            Specifier::InvalidA7 => Op::InvalidA7,
            Specifier::InvalidA8 => Op::InvalidA8,
            Specifier::InvalidA9 => Op::InvalidA9,
            Specifier::InvalidAa => Op::InvalidAa,
            Specifier::InvalidAb => Op::InvalidAb,
            Specifier::InvalidAc => Op::InvalidAc,
            Specifier::InvalidAd => Op::InvalidAd,
            Specifier::InvalidAe => Op::InvalidAe,
            Specifier::InvalidAf => Op::InvalidAf,

            Specifier::JumpTo => Op::JumpTo,
            Specifier::JumpIf => Op::JumpIf,
            Specifier::JumpSub => Op::JumpSub,

            Specifier::InvalidB3 => Op::InvalidB3,

            Specifier::JumpSubV => Op::JumpSubV,
            Specifier::BeginSub => Op::BeginSub,
            Specifier::BeginData => Op::BeginData,

            Specifier::InvalidB7 => Op::InvalidB7,

            Specifier::ReturnSub => Op::ReturnSub,
            Specifier::PutLocal => Op::PutLocal,
            Specifier::GetLocal => Op::GetLocal,

            Specifier::InvalidBb => Op::InvalidBb,
            Specifier::InvalidBc => Op::InvalidBc,
            Specifier::InvalidBd => Op::InvalidBd,
            Specifier::InvalidBe => Op::InvalidBe,
            Specifier::InvalidBf => Op::InvalidBf,
            Specifier::InvalidC0 => Op::InvalidC0,
            Specifier::InvalidC1 => Op::InvalidC1,
            Specifier::InvalidC2 => Op::InvalidC2,
            Specifier::InvalidC3 => Op::InvalidC3,
            Specifier::InvalidC4 => Op::InvalidC4,
            Specifier::InvalidC5 => Op::InvalidC5,
            Specifier::InvalidC6 => Op::InvalidC6,
            Specifier::InvalidC7 => Op::InvalidC7,
            Specifier::InvalidC8 => Op::InvalidC8,
            Specifier::InvalidC9 => Op::InvalidC9,
            Specifier::InvalidCa => Op::InvalidCa,
            Specifier::InvalidCb => Op::InvalidCb,
            Specifier::InvalidCc => Op::InvalidCc,
            Specifier::InvalidCd => Op::InvalidCd,
            Specifier::InvalidCe => Op::InvalidCe,
            Specifier::InvalidCf => Op::InvalidCf,
            Specifier::InvalidD0 => Op::InvalidD0,
            Specifier::InvalidD1 => Op::InvalidD1,
            Specifier::InvalidD2 => Op::InvalidD2,
            Specifier::InvalidD3 => Op::InvalidD3,
            Specifier::InvalidD4 => Op::InvalidD4,
            Specifier::InvalidD5 => Op::InvalidD5,
            Specifier::InvalidD6 => Op::InvalidD6,
            Specifier::InvalidD7 => Op::InvalidD7,
            Specifier::InvalidD8 => Op::InvalidD8,
            Specifier::InvalidD9 => Op::InvalidD9,
            Specifier::InvalidDa => Op::InvalidDa,
            Specifier::InvalidDb => Op::InvalidDb,
            Specifier::InvalidDc => Op::InvalidDc,
            Specifier::InvalidDd => Op::InvalidDd,
            Specifier::InvalidDe => Op::InvalidDe,
            Specifier::InvalidDf => Op::InvalidDf,
            Specifier::InvalidE0 => Op::InvalidE0,

            Specifier::SLoadBytes => Op::SLoadBytes,
            Specifier::SStoreBytes => Op::SStoreBytes,
            Specifier::SSize => Op::SSize,

            Specifier::InvalidE4 => Op::InvalidE4,
            Specifier::InvalidE5 => Op::InvalidE5,
            Specifier::InvalidE6 => Op::InvalidE6,
            Specifier::InvalidE7 => Op::InvalidE7,
            Specifier::InvalidE8 => Op::InvalidE8,
            Specifier::InvalidE9 => Op::InvalidE9,
            Specifier::InvalidEa => Op::InvalidEa,
            Specifier::InvalidEb => Op::InvalidEb,
            Specifier::InvalidEc => Op::InvalidEc,
            Specifier::InvalidEd => Op::InvalidEd,
            Specifier::InvalidEe => Op::InvalidEe,
            Specifier::InvalidEf => Op::InvalidEf,

            Specifier::Create => Op::Create,
            Specifier::Call => Op::Call,
            Specifier::CallCode => Op::CallCode,
            Specifier::Return => Op::Return,
            Specifier::DelegateCall => Op::DelegateCall,
            Specifier::Create2 => Op::Create2,

            Specifier::InvalidF6 => Op::InvalidF6,
            Specifier::InvalidF7 => Op::InvalidF7,
            Specifier::InvalidF8 => Op::InvalidF8,
            Specifier::InvalidF9 => Op::InvalidF9,

            Specifier::StaticCall => Op::StaticCall,

            Specifier::InvalidFb => Op::InvalidFb,

            Specifier::TxExecGas => Op::TxExecGas,
            Specifier::Revert => Op::Revert,
            Specifier::Invalid => Op::Invalid,
            Specifier::SelfDestruct => Op::SelfDestruct,
        }
    }

    pub(crate) fn realize(&self, address: u32) -> Result<Self, TryFromIntError> {
        let res = match self {
            Op::Push1(Imm::Label(_)) => Op::Push1(address.try_into()?),
            Op::Push2(Imm::Label(_)) => Op::Push2(address.try_into()?),
            Op::Push3(Imm::Label(_)) => Op::Push3(address.try_into()?),
            Op::Push4(Imm::Label(_)) => Op::Push4(address.into()),
            Op::Push5(Imm::Label(_)) => Op::Push5(address.into()),
            Op::Push6(Imm::Label(_)) => Op::Push6(address.into()),
            Op::Push7(Imm::Label(_)) => Op::Push7(address.into()),
            Op::Push8(Imm::Label(_)) => Op::Push8(address.into()),
            Op::Push9(Imm::Label(_)) => Op::Push9(address.into()),
            Op::Push10(Imm::Label(_)) => Op::Push10(address.into()),
            Op::Push11(Imm::Label(_)) => Op::Push11(address.into()),
            Op::Push12(Imm::Label(_)) => Op::Push12(address.into()),
            Op::Push13(Imm::Label(_)) => Op::Push13(address.into()),
            Op::Push14(Imm::Label(_)) => Op::Push14(address.into()),
            Op::Push15(Imm::Label(_)) => Op::Push15(address.into()),
            Op::Push16(Imm::Label(_)) => Op::Push16(address.into()),
            Op::Push17(Imm::Label(_)) => Op::Push17(address.into()),
            Op::Push18(Imm::Label(_)) => Op::Push18(address.into()),
            Op::Push19(Imm::Label(_)) => Op::Push19(address.into()),
            Op::Push20(Imm::Label(_)) => Op::Push20(address.into()),
            Op::Push21(Imm::Label(_)) => Op::Push21(address.into()),
            Op::Push22(Imm::Label(_)) => Op::Push22(address.into()),
            Op::Push23(Imm::Label(_)) => Op::Push23(address.into()),
            Op::Push24(Imm::Label(_)) => Op::Push24(address.into()),
            Op::Push25(Imm::Label(_)) => Op::Push25(address.into()),
            Op::Push26(Imm::Label(_)) => Op::Push26(address.into()),
            Op::Push27(Imm::Label(_)) => Op::Push27(address.into()),
            Op::Push28(Imm::Label(_)) => Op::Push28(address.into()),
            Op::Push29(Imm::Label(_)) => Op::Push29(address.into()),
            Op::Push30(Imm::Label(_)) => Op::Push30(address.into()),
            Op::Push31(Imm::Label(_)) => Op::Push31(address.into()),
            Op::Push32(Imm::Label(_)) => Op::Push32(address.into()),
            _ => panic!("only push can be realized"),
        };
        Ok(res)
    }

    pub fn push_with_immediate(size: usize, imm: &[u8]) -> Result<Op, TryFromSliceError> {
        let op = match size {
            1 => Op::Push1(Imm::try_from(imm)?),
            2 => Op::Push2(Imm::try_from(imm)?),
            3 => Op::Push3(Imm::try_from(imm)?),
            4 => Op::Push4(Imm::try_from(imm)?),
            5 => Op::Push5(Imm::try_from(imm)?),
            6 => Op::Push6(Imm::try_from(imm)?),
            7 => Op::Push7(Imm::try_from(imm)?),
            8 => Op::Push8(Imm::try_from(imm)?),
            9 => Op::Push9(Imm::try_from(imm)?),
            10 => Op::Push10(Imm::try_from(imm)?),
            11 => Op::Push11(Imm::try_from(imm)?),
            12 => Op::Push12(Imm::try_from(imm)?),
            13 => Op::Push13(Imm::try_from(imm)?),
            14 => Op::Push14(Imm::try_from(imm)?),
            15 => Op::Push15(Imm::try_from(imm)?),
            16 => Op::Push16(Imm::try_from(imm)?),
            17 => Op::Push17(Imm::try_from(imm)?),
            18 => Op::Push18(Imm::try_from(imm)?),
            19 => Op::Push19(Imm::try_from(imm)?),
            20 => Op::Push20(Imm::try_from(imm)?),
            21 => Op::Push21(Imm::try_from(imm)?),
            22 => Op::Push22(Imm::try_from(imm)?),
            23 => Op::Push23(Imm::try_from(imm)?),
            24 => Op::Push24(Imm::try_from(imm)?),
            25 => Op::Push25(Imm::try_from(imm)?),
            26 => Op::Push26(Imm::try_from(imm)?),
            27 => Op::Push27(Imm::try_from(imm)?),
            28 => Op::Push28(Imm::try_from(imm)?),
            29 => Op::Push29(Imm::try_from(imm)?),
            30 => Op::Push30(Imm::try_from(imm)?),
            31 => Op::Push31(Imm::try_from(imm)?),
            32 => Op::Push32(Imm::try_from(imm)?),
            _ => panic!("push size must be between 1 and 32"),
        };

        Ok(op)
    }

    pub fn push_with_label(size: usize, label: String) -> Op {
        match size {
            1 => Op::Push1(Imm::from(label)),
            2 => Op::Push2(Imm::from(label)),
            3 => Op::Push3(Imm::from(label)),
            4 => Op::Push4(Imm::from(label)),
            5 => Op::Push5(Imm::from(label)),
            6 => Op::Push6(Imm::from(label)),
            7 => Op::Push7(Imm::from(label)),
            8 => Op::Push8(Imm::from(label)),
            9 => Op::Push9(Imm::from(label)),
            10 => Op::Push10(Imm::from(label)),
            11 => Op::Push11(Imm::from(label)),
            12 => Op::Push12(Imm::from(label)),
            13 => Op::Push13(Imm::from(label)),
            14 => Op::Push14(Imm::from(label)),
            15 => Op::Push15(Imm::from(label)),
            16 => Op::Push16(Imm::from(label)),
            17 => Op::Push17(Imm::from(label)),
            18 => Op::Push18(Imm::from(label)),
            19 => Op::Push19(Imm::from(label)),
            20 => Op::Push20(Imm::from(label)),
            21 => Op::Push21(Imm::from(label)),
            22 => Op::Push22(Imm::from(label)),
            23 => Op::Push23(Imm::from(label)),
            24 => Op::Push24(Imm::from(label)),
            25 => Op::Push25(Imm::from(label)),
            26 => Op::Push26(Imm::from(label)),
            27 => Op::Push27(Imm::from(label)),
            28 => Op::Push28(Imm::from(label)),
            29 => Op::Push29(Imm::from(label)),
            30 => Op::Push30(Imm::from(label)),
            31 => Op::Push31(Imm::from(label)),
            32 => Op::Push32(Imm::from(label)),
            _ => panic!("push size must be between 1 and 32"),
        }
    }

    pub const fn specifier(&self) -> Specifier {
        match self {
            Op::Stop => Specifier::Stop,
            Op::Add => Specifier::Add,
            Op::Mul => Specifier::Mul,
            Op::Sub => Specifier::Sub,
            Op::Div => Specifier::Div,
            Op::SDiv => Specifier::SDiv,
            Op::Mod => Specifier::Mod,
            Op::SMod => Specifier::SMod,
            Op::AddMod => Specifier::AddMod,
            Op::MulMod => Specifier::MulMod,
            Op::Exp => Specifier::Exp,
            Op::SignExtend => Specifier::SignExtend,

            Op::Lt => Specifier::Lt,
            Op::Gt => Specifier::Gt,
            Op::SLt => Specifier::SLt,
            Op::SGt => Specifier::SGt,
            Op::Eq => Specifier::Eq,
            Op::IsZero => Specifier::IsZero,
            Op::And => Specifier::And,
            Op::Or => Specifier::Or,
            Op::Xor => Specifier::Xor,
            Op::Not => Specifier::Not,
            Op::Byte => Specifier::Byte,
            Op::Shl => Specifier::Shl,
            Op::Shr => Specifier::Shr,
            Op::Sar => Specifier::Sar,
            Op::Keccak256 => Specifier::Keccak256,

            Op::Address => Specifier::Address,
            Op::Balance => Specifier::Balance,
            Op::Origin => Specifier::Origin,
            Op::Caller => Specifier::Caller,
            Op::CallValue => Specifier::CallValue,
            Op::CallDataLoad => Specifier::CallDataLoad,
            Op::CallDataSize => Specifier::CallDataSize,
            Op::CallDataCopy => Specifier::CallDataCopy,
            Op::CodeSize => Specifier::CodeSize,
            Op::CodeCopy => Specifier::CodeCopy,
            Op::GasPrice => Specifier::GasPrice,
            Op::ExtCodeSize => Specifier::ExtCodeSize,
            Op::ExtCodeCopy => Specifier::ExtCodeCopy,
            Op::ReturnDataSize => Specifier::ReturnDataSize,
            Op::ReturnDataCopy => Specifier::ReturnDataCopy,
            Op::ExtCodeHash => Specifier::ExtCodeHash,
            Op::BlockHash => Specifier::BlockHash,
            Op::Coinbase => Specifier::Coinbase,
            Op::Timestamp => Specifier::Timestamp,
            Op::Number => Specifier::Number,
            Op::Difficulty => Specifier::Difficulty,
            Op::GasLimit => Specifier::GasLimit,
            Op::ChainId => Specifier::ChainId,

            Op::Pop => Specifier::Pop,
            Op::MLoad => Specifier::MLoad,
            Op::MStore => Specifier::MStore,
            Op::MStore8 => Specifier::MStore8,
            Op::SLoad => Specifier::SLoad,
            Op::SStore => Specifier::SStore,
            Op::Jump => Specifier::Jump,
            Op::JumpI => Specifier::JumpI,
            Op::GetPc => Specifier::GetPc,
            Op::MSize => Specifier::MSize,
            Op::Gas => Specifier::Gas,
            Op::JumpDest(_) => Specifier::JumpDest,

            Op::Push1(_) => Specifier::Push1,
            Op::Push2(_) => Specifier::Push2,
            Op::Push3(_) => Specifier::Push3,
            Op::Push4(_) => Specifier::Push4,
            Op::Push5(_) => Specifier::Push5,
            Op::Push6(_) => Specifier::Push6,
            Op::Push7(_) => Specifier::Push7,
            Op::Push8(_) => Specifier::Push8,
            Op::Push9(_) => Specifier::Push9,
            Op::Push10(_) => Specifier::Push10,
            Op::Push11(_) => Specifier::Push11,
            Op::Push12(_) => Specifier::Push12,
            Op::Push13(_) => Specifier::Push13,
            Op::Push14(_) => Specifier::Push14,
            Op::Push15(_) => Specifier::Push15,
            Op::Push16(_) => Specifier::Push16,
            Op::Push17(_) => Specifier::Push17,
            Op::Push18(_) => Specifier::Push18,
            Op::Push19(_) => Specifier::Push19,
            Op::Push20(_) => Specifier::Push20,
            Op::Push21(_) => Specifier::Push21,
            Op::Push22(_) => Specifier::Push22,
            Op::Push23(_) => Specifier::Push23,
            Op::Push24(_) => Specifier::Push24,
            Op::Push25(_) => Specifier::Push25,
            Op::Push26(_) => Specifier::Push26,
            Op::Push27(_) => Specifier::Push27,
            Op::Push28(_) => Specifier::Push28,
            Op::Push29(_) => Specifier::Push29,
            Op::Push30(_) => Specifier::Push30,
            Op::Push31(_) => Specifier::Push31,
            Op::Push32(_) => Specifier::Push32,
            Op::Dup1 => Specifier::Dup1,
            Op::Dup2 => Specifier::Dup2,
            Op::Dup3 => Specifier::Dup3,
            Op::Dup4 => Specifier::Dup4,
            Op::Dup5 => Specifier::Dup5,
            Op::Dup6 => Specifier::Dup6,
            Op::Dup7 => Specifier::Dup7,
            Op::Dup8 => Specifier::Dup8,
            Op::Dup9 => Specifier::Dup9,
            Op::Dup10 => Specifier::Dup10,
            Op::Dup11 => Specifier::Dup11,
            Op::Dup12 => Specifier::Dup12,
            Op::Dup13 => Specifier::Dup13,
            Op::Dup14 => Specifier::Dup14,
            Op::Dup15 => Specifier::Dup15,
            Op::Dup16 => Specifier::Dup16,
            Op::Swap1 => Specifier::Swap1,
            Op::Swap2 => Specifier::Swap2,
            Op::Swap3 => Specifier::Swap3,
            Op::Swap4 => Specifier::Swap4,
            Op::Swap5 => Specifier::Swap5,
            Op::Swap6 => Specifier::Swap6,
            Op::Swap7 => Specifier::Swap7,
            Op::Swap8 => Specifier::Swap8,
            Op::Swap9 => Specifier::Swap9,
            Op::Swap10 => Specifier::Swap10,
            Op::Swap11 => Specifier::Swap11,
            Op::Swap12 => Specifier::Swap12,
            Op::Swap13 => Specifier::Swap13,
            Op::Swap14 => Specifier::Swap14,
            Op::Swap15 => Specifier::Swap15,
            Op::Swap16 => Specifier::Swap16,
            Op::Log0 => Specifier::Log0,
            Op::Log1 => Specifier::Log1,
            Op::Log2 => Specifier::Log2,
            Op::Log3 => Specifier::Log3,
            Op::Log4 => Specifier::Log4,

            Op::JumpTo => Specifier::JumpTo,
            Op::JumpIf => Specifier::JumpIf,
            Op::JumpSub => Specifier::JumpSub,
            Op::JumpSubV => Specifier::JumpSubV,
            Op::BeginSub => Specifier::BeginSub,
            Op::BeginData => Specifier::BeginData,
            Op::ReturnSub => Specifier::ReturnSub,
            Op::PutLocal => Specifier::PutLocal,
            Op::GetLocal => Specifier::GetLocal,

            Op::SLoadBytes => Specifier::SLoadBytes,
            Op::SStoreBytes => Specifier::SStoreBytes,
            Op::SSize => Specifier::SSize,

            Op::Create => Specifier::Create,
            Op::Call => Specifier::Call,
            Op::CallCode => Specifier::CallCode,
            Op::Return => Specifier::Return,
            Op::DelegateCall => Specifier::DelegateCall,
            Op::Create2 => Specifier::Create2,

            Op::StaticCall => Specifier::StaticCall,

            Op::TxExecGas => Specifier::TxExecGas,
            Op::Revert => Specifier::Revert,
            Op::Invalid => Specifier::Invalid,
            Op::SelfDestruct => Specifier::SelfDestruct,

            Op::Invalid0c => Specifier::Invalid0c,
            Op::Invalid0d => Specifier::Invalid0d,
            Op::Invalid0e => Specifier::Invalid0e,
            Op::Invalid0f => Specifier::Invalid0f,

            Op::Invalid1e => Specifier::Invalid1e,
            Op::Invalid1f => Specifier::Invalid1f,

            Op::Invalid21 => Specifier::Invalid21,
            Op::Invalid22 => Specifier::Invalid22,
            Op::Invalid23 => Specifier::Invalid23,
            Op::Invalid24 => Specifier::Invalid24,
            Op::Invalid25 => Specifier::Invalid25,
            Op::Invalid26 => Specifier::Invalid26,
            Op::Invalid27 => Specifier::Invalid27,
            Op::Invalid28 => Specifier::Invalid28,
            Op::Invalid29 => Specifier::Invalid29,
            Op::Invalid2a => Specifier::Invalid2a,
            Op::Invalid2b => Specifier::Invalid2b,
            Op::Invalid2c => Specifier::Invalid2c,
            Op::Invalid2d => Specifier::Invalid2d,
            Op::Invalid2e => Specifier::Invalid2e,
            Op::Invalid2f => Specifier::Invalid2f,

            Op::Invalid47 => Specifier::Invalid47,
            Op::Invalid48 => Specifier::Invalid48,
            Op::Invalid49 => Specifier::Invalid49,
            Op::Invalid4a => Specifier::Invalid4a,
            Op::Invalid4b => Specifier::Invalid4b,
            Op::Invalid4c => Specifier::Invalid4c,
            Op::Invalid4d => Specifier::Invalid4d,
            Op::Invalid4e => Specifier::Invalid4e,
            Op::Invalid4f => Specifier::Invalid4f,

            Op::Invalid5c => Specifier::Invalid5c,
            Op::Invalid5d => Specifier::Invalid5d,
            Op::Invalid5e => Specifier::Invalid5e,
            Op::Invalid5f => Specifier::Invalid5f,

            Op::InvalidA5 => Specifier::InvalidA5,
            Op::InvalidA6 => Specifier::InvalidA6,
            Op::InvalidA7 => Specifier::InvalidA7,
            Op::InvalidA8 => Specifier::InvalidA8,
            Op::InvalidA9 => Specifier::InvalidA9,
            Op::InvalidAa => Specifier::InvalidAa,
            Op::InvalidAb => Specifier::InvalidAb,
            Op::InvalidAc => Specifier::InvalidAc,
            Op::InvalidAd => Specifier::InvalidAd,
            Op::InvalidAe => Specifier::InvalidAe,
            Op::InvalidAf => Specifier::InvalidAf,

            Op::InvalidB3 => Specifier::InvalidB3,

            Op::InvalidB7 => Specifier::InvalidB7,

            Op::InvalidBb => Specifier::InvalidBb,
            Op::InvalidBc => Specifier::InvalidBc,
            Op::InvalidBd => Specifier::InvalidBd,
            Op::InvalidBe => Specifier::InvalidBe,
            Op::InvalidBf => Specifier::InvalidBf,
            Op::InvalidC0 => Specifier::InvalidC0,
            Op::InvalidC1 => Specifier::InvalidC1,
            Op::InvalidC2 => Specifier::InvalidC2,
            Op::InvalidC3 => Specifier::InvalidC3,
            Op::InvalidC4 => Specifier::InvalidC4,
            Op::InvalidC5 => Specifier::InvalidC5,
            Op::InvalidC6 => Specifier::InvalidC6,
            Op::InvalidC7 => Specifier::InvalidC7,
            Op::InvalidC8 => Specifier::InvalidC8,
            Op::InvalidC9 => Specifier::InvalidC9,
            Op::InvalidCa => Specifier::InvalidCa,
            Op::InvalidCb => Specifier::InvalidCb,
            Op::InvalidCc => Specifier::InvalidCc,
            Op::InvalidCd => Specifier::InvalidCd,
            Op::InvalidCe => Specifier::InvalidCe,
            Op::InvalidCf => Specifier::InvalidCf,
            Op::InvalidD0 => Specifier::InvalidD0,
            Op::InvalidD1 => Specifier::InvalidD1,
            Op::InvalidD2 => Specifier::InvalidD2,
            Op::InvalidD3 => Specifier::InvalidD3,
            Op::InvalidD4 => Specifier::InvalidD4,
            Op::InvalidD5 => Specifier::InvalidD5,
            Op::InvalidD6 => Specifier::InvalidD6,
            Op::InvalidD7 => Specifier::InvalidD7,
            Op::InvalidD8 => Specifier::InvalidD8,
            Op::InvalidD9 => Specifier::InvalidD9,
            Op::InvalidDa => Specifier::InvalidDa,
            Op::InvalidDb => Specifier::InvalidDb,
            Op::InvalidDc => Specifier::InvalidDc,
            Op::InvalidDd => Specifier::InvalidDd,
            Op::InvalidDe => Specifier::InvalidDe,
            Op::InvalidDf => Specifier::InvalidDf,
            Op::InvalidE0 => Specifier::InvalidE0,

            Op::InvalidE4 => Specifier::InvalidE4,
            Op::InvalidE5 => Specifier::InvalidE5,
            Op::InvalidE6 => Specifier::InvalidE6,
            Op::InvalidE7 => Specifier::InvalidE7,
            Op::InvalidE8 => Specifier::InvalidE8,
            Op::InvalidE9 => Specifier::InvalidE9,
            Op::InvalidEa => Specifier::InvalidEa,
            Op::InvalidEb => Specifier::InvalidEb,
            Op::InvalidEc => Specifier::InvalidEc,
            Op::InvalidEd => Specifier::InvalidEd,
            Op::InvalidEe => Specifier::InvalidEe,
            Op::InvalidEf => Specifier::InvalidEf,

            Op::InvalidF6 => Specifier::InvalidF6,
            Op::InvalidF7 => Specifier::InvalidF7,
            Op::InvalidF8 => Specifier::InvalidF8,
            Op::InvalidF9 => Specifier::InvalidF9,

            Op::InvalidFb => Specifier::InvalidFb,
        }
    }

    /// The label which would refer to this instruction. Only relevant for
    /// `Op::JumpDest`.
    pub(crate) fn label(&self) -> Option<&str> {
        match self {
            Op::JumpDest(Some(ref lbl)) => Some(lbl),
            _ => None,
        }
    }

    /// The label to be pushed on the stack. Only relevant for push instructions.
    pub(crate) fn immediate_label(&self) -> Option<&str> {
        match self {
            Op::Push1(Imm::Label(ref lbl)) => Some(lbl),
            Op::Push2(Imm::Label(ref lbl)) => Some(lbl),
            Op::Push3(Imm::Label(ref lbl)) => Some(lbl),
            Op::Push4(Imm::Label(ref lbl)) => Some(lbl),
            Op::Push5(Imm::Label(ref lbl)) => Some(lbl),
            Op::Push6(Imm::Label(ref lbl)) => Some(lbl),
            Op::Push7(Imm::Label(ref lbl)) => Some(lbl),
            Op::Push8(Imm::Label(ref lbl)) => Some(lbl),
            Op::Push9(Imm::Label(ref lbl)) => Some(lbl),
            Op::Push10(Imm::Label(ref lbl)) => Some(lbl),
            Op::Push11(Imm::Label(ref lbl)) => Some(lbl),
            Op::Push12(Imm::Label(ref lbl)) => Some(lbl),
            Op::Push13(Imm::Label(ref lbl)) => Some(lbl),
            Op::Push14(Imm::Label(ref lbl)) => Some(lbl),
            Op::Push15(Imm::Label(ref lbl)) => Some(lbl),
            Op::Push16(Imm::Label(ref lbl)) => Some(lbl),
            Op::Push17(Imm::Label(ref lbl)) => Some(lbl),
            Op::Push18(Imm::Label(ref lbl)) => Some(lbl),
            Op::Push19(Imm::Label(ref lbl)) => Some(lbl),
            Op::Push20(Imm::Label(ref lbl)) => Some(lbl),
            Op::Push21(Imm::Label(ref lbl)) => Some(lbl),
            Op::Push22(Imm::Label(ref lbl)) => Some(lbl),
            Op::Push23(Imm::Label(ref lbl)) => Some(lbl),
            Op::Push24(Imm::Label(ref lbl)) => Some(lbl),
            Op::Push25(Imm::Label(ref lbl)) => Some(lbl),
            Op::Push26(Imm::Label(ref lbl)) => Some(lbl),
            Op::Push27(Imm::Label(ref lbl)) => Some(lbl),
            Op::Push28(Imm::Label(ref lbl)) => Some(lbl),
            Op::Push29(Imm::Label(ref lbl)) => Some(lbl),
            Op::Push30(Imm::Label(ref lbl)) => Some(lbl),
            Op::Push31(Imm::Label(ref lbl)) => Some(lbl),
            Op::Push32(Imm::Label(ref lbl)) => Some(lbl),
            _ => None,
        }
    }

    pub(crate) fn assemble(&self, buf: &mut Vec<u8>) {
        if self.immediate_label().is_some() {
            panic!("label not resolved before assemble");
        }

        let specifier = [self.specifier() as u8];
        buf.extend_from_slice(&specifier);

        let args = match self {
            Op::Push1(Imm::Constant(ref cnst)) => cnst as &[u8],
            Op::Push2(Imm::Constant(ref cnst)) => cnst as &[u8],
            Op::Push3(Imm::Constant(ref cnst)) => cnst as &[u8],
            Op::Push4(Imm::Constant(ref cnst)) => cnst as &[u8],
            Op::Push5(Imm::Constant(ref cnst)) => cnst as &[u8],
            Op::Push6(Imm::Constant(ref cnst)) => cnst as &[u8],
            Op::Push7(Imm::Constant(ref cnst)) => cnst as &[u8],
            Op::Push8(Imm::Constant(ref cnst)) => cnst as &[u8],
            Op::Push9(Imm::Constant(ref cnst)) => cnst as &[u8],
            Op::Push10(Imm::Constant(ref cnst)) => cnst as &[u8],
            Op::Push11(Imm::Constant(ref cnst)) => cnst as &[u8],
            Op::Push12(Imm::Constant(ref cnst)) => cnst as &[u8],
            Op::Push13(Imm::Constant(ref cnst)) => cnst as &[u8],
            Op::Push14(Imm::Constant(ref cnst)) => cnst as &[u8],
            Op::Push15(Imm::Constant(ref cnst)) => cnst as &[u8],
            Op::Push16(Imm::Constant(ref cnst)) => cnst as &[u8],
            Op::Push17(Imm::Constant(ref cnst)) => cnst as &[u8],
            Op::Push18(Imm::Constant(ref cnst)) => cnst as &[u8],
            Op::Push19(Imm::Constant(ref cnst)) => cnst as &[u8],
            Op::Push20(Imm::Constant(ref cnst)) => cnst as &[u8],
            Op::Push21(Imm::Constant(ref cnst)) => cnst as &[u8],
            Op::Push22(Imm::Constant(ref cnst)) => cnst as &[u8],
            Op::Push23(Imm::Constant(ref cnst)) => cnst as &[u8],
            Op::Push24(Imm::Constant(ref cnst)) => cnst as &[u8],
            Op::Push25(Imm::Constant(ref cnst)) => cnst as &[u8],
            Op::Push26(Imm::Constant(ref cnst)) => cnst as &[u8],
            Op::Push27(Imm::Constant(ref cnst)) => cnst as &[u8],
            Op::Push28(Imm::Constant(ref cnst)) => cnst as &[u8],
            Op::Push29(Imm::Constant(ref cnst)) => cnst as &[u8],
            Op::Push30(Imm::Constant(ref cnst)) => cnst as &[u8],
            Op::Push31(Imm::Constant(ref cnst)) => cnst as &[u8],
            Op::Push32(Imm::Constant(ref cnst)) => cnst as &[u8],
            _ => return,
        };

        buf.extend_from_slice(args);
    }
}

impl fmt::Display for Op {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let sp = self.specifier();

        match self {
            Op::JumpDest(Some(txt)) => write!(f, "{} :{}", sp, txt),

            Op::Push1(imm) => write!(f, "{} {}", sp, imm),
            Op::Push2(imm) => write!(f, "{} {}", sp, imm),
            Op::Push3(imm) => write!(f, "{} {}", sp, imm),
            Op::Push4(imm) => write!(f, "{} {}", sp, imm),
            Op::Push5(imm) => write!(f, "{} {}", sp, imm),
            Op::Push6(imm) => write!(f, "{} {}", sp, imm),
            Op::Push7(imm) => write!(f, "{} {}", sp, imm),
            Op::Push8(imm) => write!(f, "{} {}", sp, imm),
            Op::Push9(imm) => write!(f, "{} {}", sp, imm),
            Op::Push10(imm) => write!(f, "{} {}", sp, imm),
            Op::Push11(imm) => write!(f, "{} {}", sp, imm),
            Op::Push12(imm) => write!(f, "{} {}", sp, imm),
            Op::Push13(imm) => write!(f, "{} {}", sp, imm),
            Op::Push14(imm) => write!(f, "{} {}", sp, imm),
            Op::Push15(imm) => write!(f, "{} {}", sp, imm),
            Op::Push16(imm) => write!(f, "{} {}", sp, imm),
            Op::Push17(imm) => write!(f, "{} {}", sp, imm),
            Op::Push18(imm) => write!(f, "{} {}", sp, imm),
            Op::Push19(imm) => write!(f, "{} {}", sp, imm),
            Op::Push20(imm) => write!(f, "{} {}", sp, imm),
            Op::Push21(imm) => write!(f, "{} {}", sp, imm),
            Op::Push22(imm) => write!(f, "{} {}", sp, imm),
            Op::Push23(imm) => write!(f, "{} {}", sp, imm),
            Op::Push24(imm) => write!(f, "{} {}", sp, imm),
            Op::Push25(imm) => write!(f, "{} {}", sp, imm),
            Op::Push26(imm) => write!(f, "{} {}", sp, imm),
            Op::Push27(imm) => write!(f, "{} {}", sp, imm),
            Op::Push28(imm) => write!(f, "{} {}", sp, imm),
            Op::Push29(imm) => write!(f, "{} {}", sp, imm),
            Op::Push30(imm) => write!(f, "{} {}", sp, imm),
            Op::Push31(imm) => write!(f, "{} {}", sp, imm),
            Op::Push32(imm) => write!(f, "{} {}", sp, imm),

            _ => write!(f, "{}", sp),
        }
    }
}

#[derive(Debug, Clone, Copy, IntoPrimitive, FromPrimitive, Eq, PartialEq)]
#[repr(u8)]
pub enum Specifier {
    Stop = 0x00,
    Add = 0x01,
    Mul = 0x02,
    Sub = 0x03,
    Div = 0x04,
    SDiv = 0x05,
    Mod = 0x06,
    SMod = 0x07,
    AddMod = 0x08,
    MulMod = 0x09,
    Exp = 0x0a,
    SignExtend = 0x0b,

    Invalid0c = 0x0c,
    Invalid0d = 0x0d,
    Invalid0e = 0x0e,
    Invalid0f = 0x0f,

    Lt = 0x10,
    Gt = 0x11,
    SLt = 0x12,
    SGt = 0x13,
    Eq = 0x14,
    IsZero = 0x15,
    And = 0x16,
    Or = 0x17,
    Xor = 0x18,
    Not = 0x19,
    Byte = 0x1a,
    Shl = 0x1b,
    Shr = 0x1c,
    Sar = 0x1d,

    Invalid1e = 0x1e,
    Invalid1f = 0x1f,

    Keccak256 = 0x20,

    Invalid21 = 0x21,
    Invalid22 = 0x22,
    Invalid23 = 0x23,
    Invalid24 = 0x24,
    Invalid25 = 0x25,
    Invalid26 = 0x26,
    Invalid27 = 0x27,
    Invalid28 = 0x28,
    Invalid29 = 0x29,
    Invalid2a = 0x2a,
    Invalid2b = 0x2b,
    Invalid2c = 0x2c,
    Invalid2d = 0x2d,
    Invalid2e = 0x2e,
    Invalid2f = 0x2f,

    Address = 0x30,
    Balance = 0x31,
    Origin = 0x32,
    Caller = 0x33,
    CallValue = 0x34,
    CallDataLoad = 0x35,
    CallDataSize = 0x36,
    CallDataCopy = 0x37,
    CodeSize = 0x38,
    CodeCopy = 0x39,
    GasPrice = 0x3a,
    ExtCodeSize = 0x3b,
    ExtCodeCopy = 0x3c,
    ReturnDataSize = 0x3d,
    ReturnDataCopy = 0x3e,
    ExtCodeHash = 0x3f,
    BlockHash = 0x40,
    Coinbase = 0x41,
    Timestamp = 0x42,
    Number = 0x43,
    Difficulty = 0x44,
    GasLimit = 0x45,
    ChainId = 0x46,

    Invalid47 = 0x47,
    Invalid48 = 0x48,
    Invalid49 = 0x49,
    Invalid4a = 0x4a,
    Invalid4b = 0x4b,
    Invalid4c = 0x4c,
    Invalid4d = 0x4d,
    Invalid4e = 0x4e,
    Invalid4f = 0x4f,

    Pop = 0x50,
    MLoad = 0x51,
    MStore = 0x52,
    MStore8 = 0x53,
    SLoad = 0x54,
    SStore = 0x55,
    Jump = 0x56,
    JumpI = 0x57,
    GetPc = 0x58,
    MSize = 0x59,
    Gas = 0x5a,
    JumpDest = 0x5b,

    Invalid5c = 0x5c,
    Invalid5d = 0x5d,
    Invalid5e = 0x5e,
    Invalid5f = 0x5f,

    Push1 = 0x60,
    Push2 = 0x61,
    Push3 = 0x62,
    Push4 = 0x63,
    Push5 = 0x64,
    Push6 = 0x65,
    Push7 = 0x66,
    Push8 = 0x67,
    Push9 = 0x68,
    Push10 = 0x69,
    Push11 = 0x6a,
    Push12 = 0x6b,
    Push13 = 0x6c,
    Push14 = 0x6d,
    Push15 = 0x6e,
    Push16 = 0x6f,
    Push17 = 0x70,
    Push18 = 0x71,
    Push19 = 0x72,
    Push20 = 0x73,
    Push21 = 0x74,
    Push22 = 0x75,
    Push23 = 0x76,
    Push24 = 0x77,
    Push25 = 0x78,
    Push26 = 0x79,
    Push27 = 0x7a,
    Push28 = 0x7b,
    Push29 = 0x7c,
    Push30 = 0x7d,
    Push31 = 0x7e,
    Push32 = 0x7f,
    Dup1 = 0x80,
    Dup2 = 0x81,
    Dup3 = 0x82,
    Dup4 = 0x83,
    Dup5 = 0x84,
    Dup6 = 0x85,
    Dup7 = 0x86,
    Dup8 = 0x87,
    Dup9 = 0x88,
    Dup10 = 0x89,
    Dup11 = 0x8a,
    Dup12 = 0x8b,
    Dup13 = 0x8c,
    Dup14 = 0x8d,
    Dup15 = 0x8e,
    Dup16 = 0x8f,
    Swap1 = 0x90,
    Swap2 = 0x91,
    Swap3 = 0x92,
    Swap4 = 0x93,
    Swap5 = 0x94,
    Swap6 = 0x95,
    Swap7 = 0x96,
    Swap8 = 0x97,
    Swap9 = 0x98,
    Swap10 = 0x99,
    Swap11 = 0x9a,
    Swap12 = 0x9b,
    Swap13 = 0x9c,
    Swap14 = 0x9d,
    Swap15 = 0x9e,
    Swap16 = 0x9f,
    Log0 = 0xa0,
    Log1 = 0xa1,
    Log2 = 0xa2,
    Log3 = 0xa3,
    Log4 = 0xa4,

    InvalidA5 = 0xa5,
    InvalidA6 = 0xa6,
    InvalidA7 = 0xa7,
    InvalidA8 = 0xa8,
    InvalidA9 = 0xa9,
    InvalidAa = 0xaa,
    InvalidAb = 0xab,
    InvalidAc = 0xac,
    InvalidAd = 0xad,
    InvalidAe = 0xae,
    InvalidAf = 0xaf,

    JumpTo = 0xb0,
    JumpIf = 0xb1,
    JumpSub = 0xb2,

    InvalidB3 = 0xb3,

    JumpSubV = 0xb4,
    BeginSub = 0xb5,
    BeginData = 0xb6,

    InvalidB7 = 0xb7,

    ReturnSub = 0xb8,
    PutLocal = 0xb9,
    GetLocal = 0xba,

    InvalidBb = 0xbb,
    InvalidBc = 0xbc,
    InvalidBd = 0xbd,
    InvalidBe = 0xbe,
    InvalidBf = 0xbf,
    InvalidC0 = 0xc0,
    InvalidC1 = 0xc1,
    InvalidC2 = 0xc2,
    InvalidC3 = 0xc3,
    InvalidC4 = 0xc4,
    InvalidC5 = 0xc5,
    InvalidC6 = 0xc6,
    InvalidC7 = 0xc7,
    InvalidC8 = 0xc8,
    InvalidC9 = 0xc9,
    InvalidCa = 0xca,
    InvalidCb = 0xcb,
    InvalidCc = 0xcc,
    InvalidCd = 0xcd,
    InvalidCe = 0xce,
    InvalidCf = 0xcf,
    InvalidD0 = 0xd0,
    InvalidD1 = 0xd1,
    InvalidD2 = 0xd2,
    InvalidD3 = 0xd3,
    InvalidD4 = 0xd4,
    InvalidD5 = 0xd5,
    InvalidD6 = 0xd6,
    InvalidD7 = 0xd7,
    InvalidD8 = 0xd8,
    InvalidD9 = 0xd9,
    InvalidDa = 0xda,
    InvalidDb = 0xdb,
    InvalidDc = 0xdc,
    InvalidDd = 0xdd,
    InvalidDe = 0xde,
    InvalidDf = 0xdf,
    InvalidE0 = 0xe0,

    SLoadBytes = 0xe1,
    SStoreBytes = 0xe2,
    SSize = 0xe3,

    InvalidE4 = 0xe4,
    InvalidE5 = 0xe5,
    InvalidE6 = 0xe6,
    InvalidE7 = 0xe7,
    InvalidE8 = 0xe8,
    InvalidE9 = 0xe9,
    InvalidEa = 0xea,
    InvalidEb = 0xeb,
    InvalidEc = 0xec,
    InvalidEd = 0xed,
    InvalidEe = 0xee,
    InvalidEf = 0xef,

    Create = 0xf0,
    Call = 0xf1,
    CallCode = 0xf2,
    Return = 0xf3,
    DelegateCall = 0xf4,
    Create2 = 0xf5,

    InvalidF6 = 0xf6,
    InvalidF7 = 0xf7,
    InvalidF8 = 0xf8,
    InvalidF9 = 0xf9,

    StaticCall = 0xfa,

    InvalidFb = 0xfb,

    TxExecGas = 0xfc,
    Revert = 0xfd,
    #[num_enum(default)]
    Invalid = 0xfe,
    SelfDestruct = 0xff,
}

impl Specifier {
    pub const fn is_exit(self) -> bool {
        matches!(
            self,
            Specifier::SelfDestruct
                | Specifier::Stop
                | Specifier::Revert
                | Specifier::Return
                | Specifier::Invalid
                | Specifier::Invalid0c
                | Specifier::Invalid0d
                | Specifier::Invalid0e
                | Specifier::Invalid0f
                | Specifier::Invalid1e
                | Specifier::Invalid1f
                | Specifier::Invalid21
                | Specifier::Invalid22
                | Specifier::Invalid23
                | Specifier::Invalid24
                | Specifier::Invalid25
                | Specifier::Invalid26
                | Specifier::Invalid27
                | Specifier::Invalid28
                | Specifier::Invalid29
                | Specifier::Invalid2a
                | Specifier::Invalid2b
                | Specifier::Invalid2c
                | Specifier::Invalid2d
                | Specifier::Invalid2e
                | Specifier::Invalid2f
                | Specifier::Invalid47
                | Specifier::Invalid48
                | Specifier::Invalid49
                | Specifier::Invalid4a
                | Specifier::Invalid4b
                | Specifier::Invalid4c
                | Specifier::Invalid4d
                | Specifier::Invalid4e
                | Specifier::Invalid4f
                | Specifier::Invalid5c
                | Specifier::Invalid5d
                | Specifier::Invalid5e
                | Specifier::Invalid5f
                | Specifier::InvalidA5
                | Specifier::InvalidA6
                | Specifier::InvalidA7
                | Specifier::InvalidA8
                | Specifier::InvalidA9
                | Specifier::InvalidAa
                | Specifier::InvalidAb
                | Specifier::InvalidAc
                | Specifier::InvalidAd
                | Specifier::InvalidAe
                | Specifier::InvalidAf
                | Specifier::InvalidB3
                | Specifier::InvalidB7
                | Specifier::InvalidBb
                | Specifier::InvalidBc
                | Specifier::InvalidBd
                | Specifier::InvalidBe
                | Specifier::InvalidBf
                | Specifier::InvalidC0
                | Specifier::InvalidC1
                | Specifier::InvalidC2
                | Specifier::InvalidC3
                | Specifier::InvalidC4
                | Specifier::InvalidC5
                | Specifier::InvalidC6
                | Specifier::InvalidC7
                | Specifier::InvalidC8
                | Specifier::InvalidC9
                | Specifier::InvalidCa
                | Specifier::InvalidCb
                | Specifier::InvalidCc
                | Specifier::InvalidCd
                | Specifier::InvalidCe
                | Specifier::InvalidCf
                | Specifier::InvalidD0
                | Specifier::InvalidD1
                | Specifier::InvalidD2
                | Specifier::InvalidD3
                | Specifier::InvalidD4
                | Specifier::InvalidD5
                | Specifier::InvalidD6
                | Specifier::InvalidD7
                | Specifier::InvalidD8
                | Specifier::InvalidD9
                | Specifier::InvalidDa
                | Specifier::InvalidDb
                | Specifier::InvalidDc
                | Specifier::InvalidDd
                | Specifier::InvalidDe
                | Specifier::InvalidDf
                | Specifier::InvalidE0
                | Specifier::InvalidE4
                | Specifier::InvalidE5
                | Specifier::InvalidE6
                | Specifier::InvalidE7
                | Specifier::InvalidE8
                | Specifier::InvalidE9
                | Specifier::InvalidEa
                | Specifier::InvalidEb
                | Specifier::InvalidEc
                | Specifier::InvalidEd
                | Specifier::InvalidEe
                | Specifier::InvalidEf
                | Specifier::InvalidF6
                | Specifier::InvalidF7
                | Specifier::InvalidF8
                | Specifier::InvalidF9
                | Specifier::InvalidFb
        )
    }

    pub const fn is_jump_target(self) -> bool {
        matches!(self, Specifier::JumpDest | Specifier::BeginSub)
    }

    pub const fn is_jump(self) -> bool {
        matches!(
            self,
            Specifier::Jump
                | Specifier::ReturnSub
                | Specifier::JumpSubV
                | Specifier::JumpSub
                | Specifier::JumpIf
                | Specifier::JumpTo
                | Specifier::JumpI
        )
    }

    pub const fn extra_len(self) -> u32 {
        match self {
            Specifier::Push1 => 1,
            Specifier::Push2 => 2,
            Specifier::Push3 => 3,
            Specifier::Push4 => 4,
            Specifier::Push5 => 5,
            Specifier::Push6 => 6,
            Specifier::Push7 => 7,
            Specifier::Push8 => 8,
            Specifier::Push9 => 9,
            Specifier::Push10 => 10,
            Specifier::Push11 => 11,
            Specifier::Push12 => 12,
            Specifier::Push13 => 13,
            Specifier::Push14 => 14,
            Specifier::Push15 => 15,
            Specifier::Push16 => 16,
            Specifier::Push17 => 17,
            Specifier::Push18 => 18,
            Specifier::Push19 => 19,
            Specifier::Push20 => 20,
            Specifier::Push21 => 21,
            Specifier::Push22 => 22,
            Specifier::Push23 => 23,
            Specifier::Push24 => 24,
            Specifier::Push25 => 25,
            Specifier::Push26 => 26,
            Specifier::Push27 => 27,
            Specifier::Push28 => 28,
            Specifier::Push29 => 29,
            Specifier::Push30 => 30,
            Specifier::Push31 => 31,
            Specifier::Push32 => 32,
            _ => 0,
        }
    }
}

impl From<Op> for Specifier {
    fn from(op: Op) -> Self {
        op.specifier()
    }
}

impl From<&Op> for Specifier {
    fn from(op: &Op) -> Self {
        op.specifier()
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
#[non_exhaustive]
pub struct UnknownSpecifier(());

impl FromStr for Specifier {
    type Err = UnknownSpecifier;

    fn from_str(txt: &str) -> Result<Self, UnknownSpecifier> {
        let result = match txt {
            "stop" => Specifier::Stop,
            "add" => Specifier::Add,
            "mul" => Specifier::Mul,
            "sub" => Specifier::Sub,
            "div" => Specifier::Div,
            "sdiv" => Specifier::SDiv,
            "mod" => Specifier::Mod,
            "smod" => Specifier::SMod,
            "addmod" => Specifier::AddMod,
            "mulmod" => Specifier::MulMod,
            "exp" => Specifier::Exp,
            "signextend" => Specifier::SignExtend,

            "lt" => Specifier::Lt,
            "gt" => Specifier::Gt,
            "slt" => Specifier::SLt,
            "sgt" => Specifier::SGt,
            "eq" => Specifier::Eq,
            "iszero" => Specifier::IsZero,
            "and" => Specifier::And,
            "or" => Specifier::Or,
            "xor" => Specifier::Xor,
            "not" => Specifier::Not,
            "byte" => Specifier::Byte,
            "shl" => Specifier::Shl,
            "shr" => Specifier::Shr,
            "sar" => Specifier::Sar,
            "keccak256" => Specifier::Keccak256,

            "address" => Specifier::Address,
            "balance" => Specifier::Balance,
            "origin" => Specifier::Origin,
            "caller" => Specifier::Caller,
            "callvalue" => Specifier::CallValue,
            "calldataload" => Specifier::CallDataLoad,
            "calldatasize" => Specifier::CallDataSize,
            "calldatacopy" => Specifier::CallDataCopy,
            "codesize" => Specifier::CodeSize,
            "codecopy" => Specifier::CodeCopy,
            "gasprice" => Specifier::GasPrice,
            "extcodesize" => Specifier::ExtCodeSize,
            "extcodecopy" => Specifier::ExtCodeCopy,
            "returndatasize" => Specifier::ReturnDataSize,
            "returndatacopy" => Specifier::ReturnDataCopy,
            "extcodehash" => Specifier::ExtCodeHash,
            "blockhash" => Specifier::BlockHash,
            "coinbase" => Specifier::Coinbase,
            "timestamp" => Specifier::Timestamp,
            "number" => Specifier::Number,
            "difficulty" => Specifier::Difficulty,
            "gaslimit" => Specifier::GasLimit,
            "chainid" => Specifier::ChainId,

            "pop" => Specifier::Pop,
            "mload" => Specifier::MLoad,
            "mstore" => Specifier::MStore,
            "mstore8" => Specifier::MStore8,
            "sload" => Specifier::SLoad,
            "sstore" => Specifier::SStore,
            "jump" => Specifier::Jump,
            "jumpi" => Specifier::JumpI,
            "pc" => Specifier::GetPc,
            "msize" => Specifier::MSize,
            "gas" => Specifier::Gas,
            "jumpdest" => Specifier::JumpDest,

            "push1" => Specifier::Push1,
            "push2" => Specifier::Push2,
            "push3" => Specifier::Push3,
            "push4" => Specifier::Push4,
            "push5" => Specifier::Push5,
            "push6" => Specifier::Push6,
            "push7" => Specifier::Push7,
            "push8" => Specifier::Push8,
            "push9" => Specifier::Push9,
            "push10" => Specifier::Push10,
            "push11" => Specifier::Push11,
            "push12" => Specifier::Push12,
            "push13" => Specifier::Push13,
            "push14" => Specifier::Push14,
            "push15" => Specifier::Push15,
            "push16" => Specifier::Push16,
            "push17" => Specifier::Push17,
            "push18" => Specifier::Push18,
            "push19" => Specifier::Push19,
            "push20" => Specifier::Push20,
            "push21" => Specifier::Push21,
            "push22" => Specifier::Push22,
            "push23" => Specifier::Push23,
            "push24" => Specifier::Push24,
            "push25" => Specifier::Push25,
            "push26" => Specifier::Push26,
            "push27" => Specifier::Push27,
            "push28" => Specifier::Push28,
            "push29" => Specifier::Push29,
            "push30" => Specifier::Push30,
            "push31" => Specifier::Push31,
            "push32" => Specifier::Push32,
            "dup1" => Specifier::Dup1,
            "dup2" => Specifier::Dup2,
            "dup3" => Specifier::Dup3,
            "dup4" => Specifier::Dup4,
            "dup5" => Specifier::Dup5,
            "dup6" => Specifier::Dup6,
            "dup7" => Specifier::Dup7,
            "dup8" => Specifier::Dup8,
            "dup9" => Specifier::Dup9,
            "dup10" => Specifier::Dup10,
            "dup11" => Specifier::Dup11,
            "dup12" => Specifier::Dup12,
            "dup13" => Specifier::Dup13,
            "dup14" => Specifier::Dup14,
            "dup15" => Specifier::Dup15,
            "dup16" => Specifier::Dup16,
            "swap1" => Specifier::Swap1,
            "swap2" => Specifier::Swap2,
            "swap3" => Specifier::Swap3,
            "swap4" => Specifier::Swap4,
            "swap5" => Specifier::Swap5,
            "swap6" => Specifier::Swap6,
            "swap7" => Specifier::Swap7,
            "swap8" => Specifier::Swap8,
            "swap9" => Specifier::Swap9,
            "swap10" => Specifier::Swap10,
            "swap11" => Specifier::Swap11,
            "swap12" => Specifier::Swap12,
            "swap13" => Specifier::Swap13,
            "swap14" => Specifier::Swap14,
            "swap15" => Specifier::Swap15,
            "swap16" => Specifier::Swap16,
            "log0" => Specifier::Log0,
            "log1" => Specifier::Log1,
            "log2" => Specifier::Log2,
            "log3" => Specifier::Log3,
            "log4" => Specifier::Log4,

            "jumpto" => Specifier::JumpTo,
            "jumpif" => Specifier::JumpIf,
            "jumpsub" => Specifier::JumpSub,
            "jumpsubv" => Specifier::JumpSubV,
            "beginsub" => Specifier::BeginSub,
            "begindata" => Specifier::BeginData,
            "returnsub" => Specifier::ReturnSub,
            "putlocal" => Specifier::PutLocal,
            "getlocal" => Specifier::GetLocal,

            "sloadbytes" => Specifier::SLoadBytes,
            "sstorebytes" => Specifier::SStoreBytes,
            "ssize" => Specifier::SSize,

            "create" => Specifier::Create,
            "call" => Specifier::Call,
            "callcode" => Specifier::CallCode,
            "return" => Specifier::Return,
            "delegatecall" => Specifier::DelegateCall,
            "create2" => Specifier::Create2,

            "staticcall" => Specifier::StaticCall,

            "txexecgas" => Specifier::TxExecGas,
            "revert" => Specifier::Revert,
            "invalid" => Specifier::Invalid,
            "selfdestruct" => Specifier::SelfDestruct,

            "invalid_0c" => Specifier::Invalid0c,
            "invalid_0d" => Specifier::Invalid0d,
            "invalid_0e" => Specifier::Invalid0e,
            "invalid_0f" => Specifier::Invalid0f,
            "invalid_1e" => Specifier::Invalid1e,
            "invalid_1f" => Specifier::Invalid1f,
            "invalid_21" => Specifier::Invalid21,
            "invalid_22" => Specifier::Invalid22,
            "invalid_23" => Specifier::Invalid23,
            "invalid_24" => Specifier::Invalid24,
            "invalid_25" => Specifier::Invalid25,
            "invalid_26" => Specifier::Invalid26,
            "invalid_27" => Specifier::Invalid27,
            "invalid_28" => Specifier::Invalid28,
            "invalid_29" => Specifier::Invalid29,
            "invalid_2a" => Specifier::Invalid2a,
            "invalid_2b" => Specifier::Invalid2b,
            "invalid_2c" => Specifier::Invalid2c,
            "invalid_2d" => Specifier::Invalid2d,
            "invalid_2e" => Specifier::Invalid2e,
            "invalid_2f" => Specifier::Invalid2f,
            "invalid_47" => Specifier::Invalid47,
            "invalid_48" => Specifier::Invalid48,
            "invalid_49" => Specifier::Invalid49,
            "invalid_4a" => Specifier::Invalid4a,
            "invalid_4b" => Specifier::Invalid4b,
            "invalid_4c" => Specifier::Invalid4c,
            "invalid_4d" => Specifier::Invalid4d,
            "invalid_4e" => Specifier::Invalid4e,
            "invalid_4f" => Specifier::Invalid4f,
            "invalid_5c" => Specifier::Invalid5c,
            "invalid_5d" => Specifier::Invalid5d,
            "invalid_5e" => Specifier::Invalid5e,
            "invalid_5f" => Specifier::Invalid5f,
            "invalid_a5" => Specifier::InvalidA5,
            "invalid_a6" => Specifier::InvalidA6,
            "invalid_a7" => Specifier::InvalidA7,
            "invalid_a8" => Specifier::InvalidA8,
            "invalid_a9" => Specifier::InvalidA9,
            "invalid_aa" => Specifier::InvalidAa,
            "invalid_ab" => Specifier::InvalidAb,
            "invalid_ac" => Specifier::InvalidAc,
            "invalid_ad" => Specifier::InvalidAd,
            "invalid_ae" => Specifier::InvalidAe,
            "invalid_af" => Specifier::InvalidAf,
            "invalid_b3" => Specifier::InvalidB3,
            "invalid_b7" => Specifier::InvalidB7,
            "invalid_bb" => Specifier::InvalidBb,
            "invalid_bc" => Specifier::InvalidBc,
            "invalid_bd" => Specifier::InvalidBd,
            "invalid_be" => Specifier::InvalidBe,
            "invalid_bf" => Specifier::InvalidBf,
            "invalid_c0" => Specifier::InvalidC0,
            "invalid_c1" => Specifier::InvalidC1,
            "invalid_c2" => Specifier::InvalidC2,
            "invalid_c3" => Specifier::InvalidC3,
            "invalid_c4" => Specifier::InvalidC4,
            "invalid_c5" => Specifier::InvalidC5,
            "invalid_c6" => Specifier::InvalidC6,
            "invalid_c7" => Specifier::InvalidC7,
            "invalid_c8" => Specifier::InvalidC8,
            "invalid_c9" => Specifier::InvalidC9,
            "invalid_ca" => Specifier::InvalidCa,
            "invalid_cb" => Specifier::InvalidCb,
            "invalid_cc" => Specifier::InvalidCc,
            "invalid_cd" => Specifier::InvalidCd,
            "invalid_ce" => Specifier::InvalidCe,
            "invalid_cf" => Specifier::InvalidCf,
            "invalid_d0" => Specifier::InvalidD0,
            "invalid_d1" => Specifier::InvalidD1,
            "invalid_d2" => Specifier::InvalidD2,
            "invalid_d3" => Specifier::InvalidD3,
            "invalid_d4" => Specifier::InvalidD4,
            "invalid_d5" => Specifier::InvalidD5,
            "invalid_d6" => Specifier::InvalidD6,
            "invalid_d7" => Specifier::InvalidD7,
            "invalid_d8" => Specifier::InvalidD8,
            "invalid_d9" => Specifier::InvalidD9,
            "invalid_da" => Specifier::InvalidDa,
            "invalid_db" => Specifier::InvalidDb,
            "invalid_dc" => Specifier::InvalidDc,
            "invalid_dd" => Specifier::InvalidDd,
            "invalid_de" => Specifier::InvalidDe,
            "invalid_df" => Specifier::InvalidDf,
            "invalid_e0" => Specifier::InvalidE0,
            "invalid_e4" => Specifier::InvalidE4,
            "invalid_e5" => Specifier::InvalidE5,
            "invalid_e6" => Specifier::InvalidE6,
            "invalid_e7" => Specifier::InvalidE7,
            "invalid_e8" => Specifier::InvalidE8,
            "invalid_e9" => Specifier::InvalidE9,
            "invalid_ea" => Specifier::InvalidEa,
            "invalid_eb" => Specifier::InvalidEb,
            "invalid_ec" => Specifier::InvalidEc,
            "invalid_ed" => Specifier::InvalidEd,
            "invalid_ee" => Specifier::InvalidEe,
            "invalid_ef" => Specifier::InvalidEf,
            "invalid_f6" => Specifier::InvalidF6,
            "invalid_f7" => Specifier::InvalidF7,
            "invalid_f8" => Specifier::InvalidF8,
            "invalid_f9" => Specifier::InvalidF9,
            "invalid_fb" => Specifier::InvalidFb,

            _ => return Err(UnknownSpecifier(())),
        };

        Ok(result)
    }
}

impl fmt::Display for Specifier {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let txt = match self {
            Specifier::Stop => "stop",
            Specifier::Add => "add",
            Specifier::Mul => "mul",
            Specifier::Sub => "sub",
            Specifier::Div => "div",
            Specifier::SDiv => "sdiv",
            Specifier::Mod => "mod",
            Specifier::SMod => "smod",
            Specifier::AddMod => "addmod",
            Specifier::MulMod => "mulmod",
            Specifier::Exp => "exp",
            Specifier::SignExtend => "signextend",

            Specifier::Lt => "lt",
            Specifier::Gt => "gt",
            Specifier::SLt => "slt",
            Specifier::SGt => "sgt",
            Specifier::Eq => "eq",
            Specifier::IsZero => "iszero",
            Specifier::And => "and",
            Specifier::Or => "or",
            Specifier::Xor => "xor",
            Specifier::Not => "not",
            Specifier::Byte => "byte",
            Specifier::Shl => "shl",
            Specifier::Shr => "shr",
            Specifier::Sar => "sar",
            Specifier::Keccak256 => "keccak256",

            Specifier::Address => "address",
            Specifier::Balance => "balance",
            Specifier::Origin => "origin",
            Specifier::Caller => "caller",
            Specifier::CallValue => "callvalue",
            Specifier::CallDataLoad => "calldataload",
            Specifier::CallDataSize => "calldatasize",
            Specifier::CallDataCopy => "calldatacopy",
            Specifier::CodeSize => "codesize",
            Specifier::CodeCopy => "codecopy",
            Specifier::GasPrice => "gasprice",
            Specifier::ExtCodeSize => "extcodesize",
            Specifier::ExtCodeCopy => "extcodecopy",
            Specifier::ReturnDataSize => "returndatasize",
            Specifier::ReturnDataCopy => "returndatacopy",
            Specifier::ExtCodeHash => "extcodehash",
            Specifier::BlockHash => "blockhash",
            Specifier::Coinbase => "coinbase",
            Specifier::Timestamp => "timestamp",
            Specifier::Number => "number",
            Specifier::Difficulty => "difficulty",
            Specifier::GasLimit => "gaslimit",
            Specifier::ChainId => "chainid",

            Specifier::Pop => "pop",
            Specifier::MLoad => "mload",
            Specifier::MStore => "mstore",
            Specifier::MStore8 => "mstore8",
            Specifier::SLoad => "sload",
            Specifier::SStore => "sstore",
            Specifier::Jump => "jump",
            Specifier::JumpI => "jumpi",
            Specifier::GetPc => "pc",
            Specifier::MSize => "msize",
            Specifier::Gas => "gas",
            Specifier::JumpDest => "jumpdest",

            Specifier::Push1 => "push1",
            Specifier::Push2 => "push2",
            Specifier::Push3 => "push3",
            Specifier::Push4 => "push4",
            Specifier::Push5 => "push5",
            Specifier::Push6 => "push6",
            Specifier::Push7 => "push7",
            Specifier::Push8 => "push8",
            Specifier::Push9 => "push9",
            Specifier::Push10 => "push10",
            Specifier::Push11 => "push11",
            Specifier::Push12 => "push12",
            Specifier::Push13 => "push13",
            Specifier::Push14 => "push14",
            Specifier::Push15 => "push15",
            Specifier::Push16 => "push16",
            Specifier::Push17 => "push17",
            Specifier::Push18 => "push18",
            Specifier::Push19 => "push19",
            Specifier::Push20 => "push20",
            Specifier::Push21 => "push21",
            Specifier::Push22 => "push22",
            Specifier::Push23 => "push23",
            Specifier::Push24 => "push24",
            Specifier::Push25 => "push25",
            Specifier::Push26 => "push26",
            Specifier::Push27 => "push27",
            Specifier::Push28 => "push28",
            Specifier::Push29 => "push29",
            Specifier::Push30 => "push30",
            Specifier::Push31 => "push31",
            Specifier::Push32 => "push32",
            Specifier::Dup1 => "dup1",
            Specifier::Dup2 => "dup2",
            Specifier::Dup3 => "dup3",
            Specifier::Dup4 => "dup4",
            Specifier::Dup5 => "dup5",
            Specifier::Dup6 => "dup6",
            Specifier::Dup7 => "dup7",
            Specifier::Dup8 => "dup8",
            Specifier::Dup9 => "dup9",
            Specifier::Dup10 => "dup10",
            Specifier::Dup11 => "dup11",
            Specifier::Dup12 => "dup12",
            Specifier::Dup13 => "dup13",
            Specifier::Dup14 => "dup14",
            Specifier::Dup15 => "dup15",
            Specifier::Dup16 => "dup16",
            Specifier::Swap1 => "swap1",
            Specifier::Swap2 => "swap2",
            Specifier::Swap3 => "swap3",
            Specifier::Swap4 => "swap4",
            Specifier::Swap5 => "swap5",
            Specifier::Swap6 => "swap6",
            Specifier::Swap7 => "swap7",
            Specifier::Swap8 => "swap8",
            Specifier::Swap9 => "swap9",
            Specifier::Swap10 => "swap10",
            Specifier::Swap11 => "swap11",
            Specifier::Swap12 => "swap12",
            Specifier::Swap13 => "swap13",
            Specifier::Swap14 => "swap14",
            Specifier::Swap15 => "swap15",
            Specifier::Swap16 => "swap16",
            Specifier::Log0 => "log0",
            Specifier::Log1 => "log1",
            Specifier::Log2 => "log2",
            Specifier::Log3 => "log3",
            Specifier::Log4 => "log4",

            Specifier::JumpTo => "jumpto",
            Specifier::JumpIf => "jumpif",
            Specifier::JumpSub => "jumpsub",
            Specifier::JumpSubV => "jumpsubv",
            Specifier::BeginSub => "beginsub",
            Specifier::BeginData => "begindata",
            Specifier::ReturnSub => "returnsub",
            Specifier::PutLocal => "putlocal",
            Specifier::GetLocal => "getlocal",

            Specifier::SLoadBytes => "sloadbytes",
            Specifier::SStoreBytes => "sstorebytes",
            Specifier::SSize => "ssize",

            Specifier::Create => "create",
            Specifier::Call => "call",
            Specifier::CallCode => "callcode",
            Specifier::Return => "return",
            Specifier::DelegateCall => "delegatecall",
            Specifier::Create2 => "create2",

            Specifier::StaticCall => "staticcall",

            Specifier::TxExecGas => "txexecgas",
            Specifier::Revert => "revert",
            Specifier::Invalid => "invalid",
            Specifier::SelfDestruct => "selfdestruct",

            Specifier::Invalid0c => "invalid_0c",
            Specifier::Invalid0d => "invalid_0d",
            Specifier::Invalid0e => "invalid_0e",
            Specifier::Invalid0f => "invalid_0f",
            Specifier::Invalid1e => "invalid_1e",
            Specifier::Invalid1f => "invalid_1f",
            Specifier::Invalid21 => "invalid_21",
            Specifier::Invalid22 => "invalid_22",
            Specifier::Invalid23 => "invalid_23",
            Specifier::Invalid24 => "invalid_24",
            Specifier::Invalid25 => "invalid_25",
            Specifier::Invalid26 => "invalid_26",
            Specifier::Invalid27 => "invalid_27",
            Specifier::Invalid28 => "invalid_28",
            Specifier::Invalid29 => "invalid_29",
            Specifier::Invalid2a => "invalid_2a",
            Specifier::Invalid2b => "invalid_2b",
            Specifier::Invalid2c => "invalid_2c",
            Specifier::Invalid2d => "invalid_2d",
            Specifier::Invalid2e => "invalid_2e",
            Specifier::Invalid2f => "invalid_2f",
            Specifier::Invalid47 => "invalid_47",
            Specifier::Invalid48 => "invalid_48",
            Specifier::Invalid49 => "invalid_49",
            Specifier::Invalid4a => "invalid_4a",
            Specifier::Invalid4b => "invalid_4b",
            Specifier::Invalid4c => "invalid_4c",
            Specifier::Invalid4d => "invalid_4d",
            Specifier::Invalid4e => "invalid_4e",
            Specifier::Invalid4f => "invalid_4f",
            Specifier::Invalid5c => "invalid_5c",
            Specifier::Invalid5d => "invalid_5d",
            Specifier::Invalid5e => "invalid_5e",
            Specifier::Invalid5f => "invalid_5f",
            Specifier::InvalidA5 => "invalid_a5",
            Specifier::InvalidA6 => "invalid_a6",
            Specifier::InvalidA7 => "invalid_a7",
            Specifier::InvalidA8 => "invalid_a8",
            Specifier::InvalidA9 => "invalid_a9",
            Specifier::InvalidAa => "invalid_aa",
            Specifier::InvalidAb => "invalid_ab",
            Specifier::InvalidAc => "invalid_ac",
            Specifier::InvalidAd => "invalid_ad",
            Specifier::InvalidAe => "invalid_ae",
            Specifier::InvalidAf => "invalid_af",
            Specifier::InvalidB3 => "invalid_b3",
            Specifier::InvalidB7 => "invalid_b7",
            Specifier::InvalidBb => "invalid_bb",
            Specifier::InvalidBc => "invalid_bc",
            Specifier::InvalidBd => "invalid_bd",
            Specifier::InvalidBe => "invalid_be",
            Specifier::InvalidBf => "invalid_bf",
            Specifier::InvalidC0 => "invalid_c0",
            Specifier::InvalidC1 => "invalid_c1",
            Specifier::InvalidC2 => "invalid_c2",
            Specifier::InvalidC3 => "invalid_c3",
            Specifier::InvalidC4 => "invalid_c4",
            Specifier::InvalidC5 => "invalid_c5",
            Specifier::InvalidC6 => "invalid_c6",
            Specifier::InvalidC7 => "invalid_c7",
            Specifier::InvalidC8 => "invalid_c8",
            Specifier::InvalidC9 => "invalid_c9",
            Specifier::InvalidCa => "invalid_ca",
            Specifier::InvalidCb => "invalid_cb",
            Specifier::InvalidCc => "invalid_cc",
            Specifier::InvalidCd => "invalid_cd",
            Specifier::InvalidCe => "invalid_ce",
            Specifier::InvalidCf => "invalid_cf",
            Specifier::InvalidD0 => "invalid_d0",
            Specifier::InvalidD1 => "invalid_d1",
            Specifier::InvalidD2 => "invalid_d2",
            Specifier::InvalidD3 => "invalid_d3",
            Specifier::InvalidD4 => "invalid_d4",
            Specifier::InvalidD5 => "invalid_d5",
            Specifier::InvalidD6 => "invalid_d6",
            Specifier::InvalidD7 => "invalid_d7",
            Specifier::InvalidD8 => "invalid_d8",
            Specifier::InvalidD9 => "invalid_d9",
            Specifier::InvalidDa => "invalid_da",
            Specifier::InvalidDb => "invalid_db",
            Specifier::InvalidDc => "invalid_dc",
            Specifier::InvalidDd => "invalid_dd",
            Specifier::InvalidDe => "invalid_de",
            Specifier::InvalidDf => "invalid_df",
            Specifier::InvalidE0 => "invalid_e0",
            Specifier::InvalidE4 => "invalid_e4",
            Specifier::InvalidE5 => "invalid_e5",
            Specifier::InvalidE6 => "invalid_e6",
            Specifier::InvalidE7 => "invalid_e7",
            Specifier::InvalidE8 => "invalid_e8",
            Specifier::InvalidE9 => "invalid_e9",
            Specifier::InvalidEa => "invalid_ea",
            Specifier::InvalidEb => "invalid_eb",
            Specifier::InvalidEc => "invalid_ec",
            Specifier::InvalidEd => "invalid_ed",
            Specifier::InvalidEe => "invalid_ee",
            Specifier::InvalidEf => "invalid_ef",
            Specifier::InvalidF6 => "invalid_f6",
            Specifier::InvalidF7 => "invalid_f7",
            Specifier::InvalidF8 => "invalid_f8",
            Specifier::InvalidF9 => "invalid_f9",
            Specifier::InvalidFb => "invalid_fb",
        };
        write!(f, "{}", txt)
    }
}

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
            let op = Op::new(spec);
            if spec.extra_len() > 0 || spec == Specifier::JumpDest {
                assert_eq!(op, None);
            } else {
                let op = op.unwrap();
                assert_eq!(op.specifier(), spec);
            }
        }
    }
}
