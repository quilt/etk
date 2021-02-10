use hex::ToHex;

use num_enum::{IntoPrimitive, TryFromPrimitive};

use std::convert::{TryFrom, TryInto};
use std::fmt;

#[derive(Debug, Clone)]
pub struct TryFromIntError(pub(crate) ());

#[derive(Debug, Clone)]
pub struct TryFromSliceError(pub(crate) ());

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
                    return Err(TryFromIntError(()));
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
                    return Err(TryFromSliceError(()));
                }

                let mut output = [0u8; $ii];
                output.copy_from_slice(&x[..]);
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
}

impl Op {
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
        let op = match size {
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
        };

        op
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

#[derive(Debug, Clone, Copy, IntoPrimitive, TryFromPrimitive)]
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

    Keccak256 = 0x20,

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

    JumpTo = 0xb0,
    JumpIf = 0xb1,
    JumpSub = 0xb2,
    JumpSubV = 0xb4,
    BeginSub = 0xb5,
    BeginData = 0xb6,

    ReturnSub = 0xb8,
    PutLocal = 0xb9,
    GetLocal = 0xba,

    SLoadBytes = 0xe1,
    SStoreBytes = 0xe2,
    SSize = 0xe3,

    Create = 0xf0,
    Call = 0xf1,
    CallCode = 0xf2,
    Return = 0xf3,
    DelegateCall = 0xf4,
    Create2 = 0xf5,

    StaticCall = 0xfa,

    TxExecGas = 0xfc,
    Revert = 0xfd,
    Invalid = 0xfe,
    SelfDestruct = 0xff,
}

impl Specifier {
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

impl fmt::Display for Specifier {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let txt = match self {
            Specifier::Stop => "STOP",
            Specifier::Add => "ADD",
            Specifier::Mul => "MUL",
            Specifier::Sub => "SUB",
            Specifier::Div => "DIV",
            Specifier::SDiv => "SDIV",
            Specifier::Mod => "MOD",
            Specifier::SMod => "SMOD",
            Specifier::AddMod => "ADDMOD",
            Specifier::MulMod => "MULMOD",
            Specifier::Exp => "EXP",
            Specifier::SignExtend => "SIGNEXTEND",

            Specifier::Lt => "LT",
            Specifier::Gt => "GT",
            Specifier::SLt => "SLT",
            Specifier::SGt => "SGT",
            Specifier::Eq => "EQ",
            Specifier::IsZero => "ISZERO",
            Specifier::And => "AND",
            Specifier::Or => "OR",
            Specifier::Xor => "XOR",
            Specifier::Not => "NOT",
            Specifier::Byte => "BYTE",
            Specifier::Shl => "SHL",
            Specifier::Shr => "SHR",
            Specifier::Sar => "SAR",
            Specifier::Keccak256 => "KECCAK256",

            Specifier::Address => "ADDRESS",
            Specifier::Balance => "BALANCE",
            Specifier::Origin => "ORIGIN",
            Specifier::Caller => "CALLER",
            Specifier::CallValue => "CALLVALUE",
            Specifier::CallDataLoad => "CALLDATALOAD",
            Specifier::CallDataSize => "CALLDATASIZE",
            Specifier::CallDataCopy => "CALLDATACOPY",
            Specifier::CodeSize => "CODESIZE",
            Specifier::CodeCopy => "CODECOPY",
            Specifier::GasPrice => "GASPRICE",
            Specifier::ExtCodeSize => "EXTCODESIZE",
            Specifier::ExtCodeCopy => "EXTCODECOPY",
            Specifier::ReturnDataSize => "RETURNDATASIZE",
            Specifier::ReturnDataCopy => "RETURNDATACOPY",
            Specifier::ExtCodeHash => "EXTCODEHASH",
            Specifier::BlockHash => "BLOCKHASH",
            Specifier::Coinbase => "COINBASE",
            Specifier::Timestamp => "TIMESTAMP",
            Specifier::Number => "NUMBER",
            Specifier::Difficulty => "DIFFICULTY",
            Specifier::GasLimit => "GASLIMIT",
            Specifier::ChainId => "CHAINID",

            Specifier::Pop => "POP",
            Specifier::MLoad => "MLOAD",
            Specifier::MStore => "MSTORE",
            Specifier::MStore8 => "MSTORE8",
            Specifier::SLoad => "SLOAD",
            Specifier::SStore => "SSTORE",
            Specifier::Jump => "JUMP",
            Specifier::JumpI => "JUMPI",
            Specifier::GetPc => "GETPC",
            Specifier::MSize => "MSIZE",
            Specifier::Gas => "GAS",
            Specifier::JumpDest => "JUMPDEST",

            Specifier::Push1 => "PUSH1",
            Specifier::Push2 => "PUSH2",
            Specifier::Push3 => "PUSH3",
            Specifier::Push4 => "PUSH4",
            Specifier::Push5 => "PUSH5",
            Specifier::Push6 => "PUSH6",
            Specifier::Push7 => "PUSH7",
            Specifier::Push8 => "PUSH8",
            Specifier::Push9 => "PUSH9",
            Specifier::Push10 => "PUSH10",
            Specifier::Push11 => "PUSH11",
            Specifier::Push12 => "PUSH12",
            Specifier::Push13 => "PUSH13",
            Specifier::Push14 => "PUSH14",
            Specifier::Push15 => "PUSH15",
            Specifier::Push16 => "PUSH16",
            Specifier::Push17 => "PUSH17",
            Specifier::Push18 => "PUSH18",
            Specifier::Push19 => "PUSH19",
            Specifier::Push20 => "PUSH20",
            Specifier::Push21 => "PUSH21",
            Specifier::Push22 => "PUSH22",
            Specifier::Push23 => "PUSH23",
            Specifier::Push24 => "PUSH24",
            Specifier::Push25 => "PUSH25",
            Specifier::Push26 => "PUSH26",
            Specifier::Push27 => "PUSH27",
            Specifier::Push28 => "PUSH28",
            Specifier::Push29 => "PUSH29",
            Specifier::Push30 => "PUSH30",
            Specifier::Push31 => "PUSH31",
            Specifier::Push32 => "PUSH32",
            Specifier::Dup1 => "DUP1",
            Specifier::Dup2 => "DUP2",
            Specifier::Dup3 => "DUP3",
            Specifier::Dup4 => "DUP4",
            Specifier::Dup5 => "DUP5",
            Specifier::Dup6 => "DUP6",
            Specifier::Dup7 => "DUP7",
            Specifier::Dup8 => "DUP8",
            Specifier::Dup9 => "DUP9",
            Specifier::Dup10 => "DUP10",
            Specifier::Dup11 => "DUP11",
            Specifier::Dup12 => "DUP12",
            Specifier::Dup13 => "DUP13",
            Specifier::Dup14 => "DUP14",
            Specifier::Dup15 => "DUP15",
            Specifier::Dup16 => "DUP16",
            Specifier::Swap1 => "SWAP1",
            Specifier::Swap2 => "SWAP2",
            Specifier::Swap3 => "SWAP3",
            Specifier::Swap4 => "SWAP4",
            Specifier::Swap5 => "SWAP5",
            Specifier::Swap6 => "SWAP6",
            Specifier::Swap7 => "SWAP7",
            Specifier::Swap8 => "SWAP8",
            Specifier::Swap9 => "SWAP9",
            Specifier::Swap10 => "SWAP10",
            Specifier::Swap11 => "SWAP11",
            Specifier::Swap12 => "SWAP12",
            Specifier::Swap13 => "SWAP13",
            Specifier::Swap14 => "SWAP14",
            Specifier::Swap15 => "SWAP15",
            Specifier::Swap16 => "SWAP16",
            Specifier::Log0 => "LOG0",
            Specifier::Log1 => "LOG1",
            Specifier::Log2 => "LOG2",
            Specifier::Log3 => "LOG3",
            Specifier::Log4 => "LOG4",

            Specifier::JumpTo => "JUMPTO",
            Specifier::JumpIf => "JUMPIF",
            Specifier::JumpSub => "JUMPSUB",
            Specifier::JumpSubV => "JUMPSUBV",
            Specifier::BeginSub => "BEGINSUB",
            Specifier::BeginData => "BEGINDATA",
            Specifier::ReturnSub => "RETURNSUB",
            Specifier::PutLocal => "PUTLOCAL",
            Specifier::GetLocal => "GETLOCAL",

            Specifier::SLoadBytes => "SLOADBYTES",
            Specifier::SStoreBytes => "SSTOREBYTES",
            Specifier::SSize => "SSIZE",

            Specifier::Create => "CREATE",
            Specifier::Call => "CALL",
            Specifier::CallCode => "CALLCODE",
            Specifier::Return => "RETURN",
            Specifier::DelegateCall => "DELEGATECALL",
            Specifier::Create2 => "CREATE2",

            Specifier::StaticCall => "STATICCALL",

            Specifier::TxExecGas => "TXEXECGAS",
            Specifier::Revert => "REVERT",
            Specifier::Invalid => "INVALID",
            Specifier::SelfDestruct => "SELFDESTRUCT",
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
}
