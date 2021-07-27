//! Definitions of all instructions supported by the assembler.

mod error {
    use snafu::{Backtrace, Snafu};

    /// The error that can arise while parsing a specifier from a string.
    #[derive(Debug, Snafu)]
    #[snafu(display("unknown specifier: {}", text))]
    #[snafu(visibility = "pub(super)")]
    #[non_exhaustive]
    pub struct UnknownSpecifierError {
        text: String,
        backtrace: Backtrace,
    }
}

mod imm;
mod types;

pub use self::error::UnknownSpecifierError;
pub use self::imm::{Imm, Immediate, TryFromIntError, TryFromSliceError};
use self::types::ImmediateTypes;
pub use self::types::{Abstract, Concrete, Spec};

use snafu::OptionExt;

use std::cmp::{Eq, PartialEq};
use std::collections::HashMap;
use std::convert::{TryFrom, TryInto};
use std::fmt;
use std::str::FromStr;

/// The access mode (read, write, both) of an instruction.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Access {
    /// Indicates that the instruction might read.
    Read,

    /// Indicates that the instruction might write.
    Write,

    /// Indicates that the instruction may read and/or write.
    ReadWrite,
}

impl Access {
    /// Returns true if the instruction might read.
    pub fn reads(self) -> bool {
        matches!(self, Self::Read | Self::ReadWrite)
    }

    /// Returns true if the instruction might write.
    pub fn writes(self) -> bool {
        matches!(self, Self::Write | Self::ReadWrite)
    }
}

/// Extra information about an instruction.
pub trait Metadata {
    /// Returns true if the current instruction changes the program counter (other
    /// than incrementing it.)
    fn is_jump(&self) -> bool;

    /// Returns true if the current instruction is a valid destination for jumps.
    fn is_jump_target(&self) -> bool;

    /// Returns true if the current instruction causes the EVM to stop executing
    /// the contract.
    fn is_exit(&self) -> bool;

    /// Returns the access mode, if any, for touching account storage.
    fn storage_access(&self) -> Option<Access>;

    /// Returns the access mode, if any, for touching EVM memory.
    fn memory_access(&self) -> Option<Access>;

    /// How many stack elements this instruction pops.
    fn pops(&self) -> usize;

    /// How many stack elements this instruction pushes.
    fn pushes(&self) -> usize;
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

macro_rules! pat_cap_concrete {
    ($cap:ident, $op:ident) => {
        Op::<Concrete>::$op
    };
    ($cap:ident, $op:ident, $arg:ident) => {
        Op::<Concrete>::$op($cap)
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
    ($f:ident, $sp:expr, $cap:expr) => {
        write!($f, "{}", $sp)
    };
    ($f:ident, $sp:expr, $cap:expr, $arg:ident) => {
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

macro_rules! ret_from_concrete {
    ($op:ident, $addr:ident) => {
        Self::$op
    };
    ($op:ident, $addr:expr, $arg:ident) => {
        Self::$op(Imm::Constant($addr))
    };
}

macro_rules! ret_concretize {
    ($op:ident, $addr:ident) => {
        Op::$op
    };
    ($op:ident, $addr:expr, $arg:ident) => {
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
        $c
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

macro_rules! or_none {
    () => {
        None
    };
    ($v:expr) => {
        Some($v)
    };
}

macro_rules! or_zero {
    () => {
        0
    };
    ($v:expr) => {
        $v
    };
}

macro_rules! ops {
    ($($op:ident(
        mnemonic = $mnemonic:literal
        $(, arg = $arg:ident )?
        $(, pops = $pops:literal)?
        $(, pushes = $pushes:literal)?
        $(, memory = $memory:expr)?
        $(, storage = $storage:expr)?
        $(, exit = $exit:expr)?
        $(, jump = $jmp:expr)?
        $(, jump_target = $jt:expr)?),
    )*) => {
        /// Enumeration of all supported instructions.
        ///
        /// There are three flavors of `Op`:
        ///  - Abstract: `Op` that may use labels or constants.
        ///  - Concrete: `Op` that may only use constants.
        ///  - Specifier: `Op` without any arguments.
        #[derive(Debug, Clone, PartialEq, Eq)]
        #[allow(missing_docs)]
        pub enum Op<I = Abstract> where I: ImmediateTypes {
            $($op$((I::$arg))?, )*
        }

        impl<I> Metadata for Op<I> where I: ImmediateTypes {
            fn is_jump_target(&self) -> bool {
                match self {
                    $(
                        pat!($op$(, $arg)?) => or_false!($($jt)?),
                    )*
                }
            }

            fn is_exit(&self) -> bool {
                match self {
                    $(
                        pat!($op$(, $arg)?) => or_false!($($exit)?),
                    )*
                }
            }

            fn is_jump(&self) -> bool {
                match self {
                    $(
                        pat!($op$(, $arg)?) => or_false!($($jmp)?),
                    )*
                }
            }

            fn storage_access(&self) -> Option<Access> {
                match self {
                    $(
                        pat!($op$(, $arg)?) => or_none!($($storage)?),
                    )*
                }
            }

            fn memory_access(&self) -> Option<Access> {
                match self {
                    $(
                        pat!($op$(, $arg)?) => or_none!($($memory)?),
                    )*
                }
            }

            fn pushes(&self) -> usize {
                match self {
                    $(
                        pat!($op$(, $arg)?) => or_zero!($($pushes)?),
                    )*
                }
            }

            fn pops(&self) -> usize {
                match self {
                    $(
                        pat!($op$(, $arg)?) => or_zero!($($pops)?),
                    )*
                }
            }
        }

        impl<I> Op<I> where I: ImmediateTypes {
            /// Create a new `Op` given a particular specifier.
            ///
            /// Returns `None` if the instruction specified requires an
            /// immediate argument.
            pub fn new(spec: Op<Spec>) -> Option<Self> {
                match spec {
                    $(
                        pat_spec!($op$(, $arg)?) => ret_new!($op$(, $arg)?),
                    )*
                }
            }

            /// Return the specifier that corresponds to this `Op`.
            pub fn specifier(&self) -> Op<Spec> {
                match self {
                    $(
                        pat!($op$(, $arg)?) => Op::$op$((default!($arg)))?,
                    )*
                }
            }

            /// Return the total encoded size for this instruction, including the
            /// immediate if one is required.
            pub fn size(&self) -> u32 {
                self.specifier().extra_len() + 1u32
            }
        }

        /// A `Specifier` is an `Op` that takes no arguments. It's useful to refer
        /// to instructions without needing knowledge of any particular immediate
        /// argument value.
        pub type Specifier = Op<Spec>;

        impl Copy for Op<Spec> {}

        impl Op<Spec> {
            const LUT: [Op<Spec>; 256] = [
                $(
                    Op::$op$((tuple!($arg)))?,
                )*
            ];

            const fn to_u8(self) -> u8 {
                to_u8!(self, 0u8; $($op$(|$arg)?, )*)
            }

            fn extra_len(self) -> u32 {
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
            type Err = UnknownSpecifierError;

            fn from_str(text: &str) -> Result<Self, Self::Err> {
                let result = match text {
                    $(
                        $mnemonic => Op::$op$((default!($arg)))?,
                    )*

                    _ => return error::UnknownSpecifierContext {
                        text: text.clone()
                    }.fail(),
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

        impl Op<Abstract> {
            /// Construct an `Op` with the given label.
            ///
            /// ## Panics
            ///
            /// This function panics if the instruction described by the specifier
            /// does not accept immediate arguments.
            pub fn with_label<S: Into<String>>(spec: Op<Spec>, lbl: S) -> Self {
                let lbl = lbl.into();

                match spec {
                    $(
                        pat_spec!($op$(, $arg)?) => ret_with_label!(lbl, $op$(, $arg)?),
                    )*
                }
            }

            /// Construct an `Op` with the given immediate argument.
            ///
            /// An error is returned if `imm` doesn't match the immediate size for
            /// the instruction described by `spec`.
            ///
            /// ## Panics
            ///
            /// This function panics if the instruction described by the specifier
            /// does not accept immediate arguments.
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

        impl From<Op<Concrete>> for Op<Abstract> {
            fn from(concrete: Op<Concrete>) -> Self {
                match concrete {
                    $(
                        pat_cap_concrete!(a, $op$(, $arg)?) =>
                            ret_from_concrete!($op, a$(, $arg)?),
                    )*
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

        /// Shorthand for `Op<Concrete>`, that is an `Op` that can only accept
        /// constants as arguments.
        pub type ConcreteOp = Op<Concrete>;

        impl Op<Concrete> {
            /// Construct an `Op` with the given immediate argument.
            ///
            /// An error is returned if `imm` doesn't match the immediate size for
            /// the instruction described by `spec`.
            ///
            /// ## Panics
            ///
            /// This function panics if the instruction described by the specifier
            /// does not accept immediate arguments.
            pub fn with_immediate(spec: Op<Spec>, imm: &[u8]) -> Result<Self, std::array::TryFromSliceError> {
                let op = match spec {
                    $(
                        pat_spec!($op$(, $arg)?) => ret_with_immediate!(imm, $op$(, $arg)?),
                    )*
                };

                Ok(op)
            }

            /// Construct an `Op` by disassembling the given slice `bytes`.
            ///
            /// ## Panics
            ///
            /// This function panics if the length of `bytes` doesn't match the
            /// instruction size, as determined by the first element of `bytes`.
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

impl Op<Spec> {
    pub(crate) fn push_for(n: u32) -> Option<Specifier> {
        let bits = 0u32.leading_zeros() - n.leading_zeros();
        let bytes = (bits + 8 - 1) / 8;
        Self::push(bytes)
    }

    /// Converts a push instruction to the next larger push size.
    ///
    /// For example, a `push2` will become a `push3`.
    ///
    /// ## Panics
    ///
    /// This function panics if `self` is not a push instruction.
    pub fn upsize(self) -> Option<Self> {
        let extra = match self.extra_len() {
            0 => panic!("only push ops can be upsized"),
            e => e,
        };

        Self::push(extra + 1)
    }

    /// Create a new push instruction with the given immediate size.
    pub fn push(bytes: u32) -> Option<Self> {
        let spec = match bytes {
            0 | 1 => Self::Push1(()),
            2 => Self::Push2(()),
            3 => Self::Push3(()),
            4 => Self::Push4(()),
            5 => Self::Push5(()),
            6 => Self::Push6(()),
            7 => Self::Push7(()),
            8 => Self::Push8(()),
            9 => Self::Push9(()),
            10 => Self::Push10(()),
            11 => Self::Push11(()),
            12 => Self::Push12(()),
            13 => Self::Push13(()),
            14 => Self::Push14(()),
            15 => Self::Push15(()),
            16 => Self::Push16(()),
            17 => Self::Push17(()),
            18 => Self::Push18(()),
            19 => Self::Push19(()),
            20 => Self::Push20(()),
            21 => Self::Push21(()),
            22 => Self::Push22(()),
            23 => Self::Push23(()),
            24 => Self::Push24(()),
            25 => Self::Push25(()),
            26 => Self::Push26(()),
            27 => Self::Push27(()),
            28 => Self::Push28(()),
            29 => Self::Push29(()),
            30 => Self::Push30(()),
            31 => Self::Push31(()),
            32 => Self::Push32(()),
            _ => return None,
        };

        Some(spec)
    }
}

ops! {
    Stop(mnemonic="stop", exit=true),
    Add(mnemonic="add", pops=2, pushes=1),
    Mul(mnemonic="mul", pops=2, pushes=1),
    Sub(mnemonic="sub", pops=2, pushes=1),
    Div(mnemonic="div", pops=2, pushes=1),
    SDiv(mnemonic="sdiv", pops=2, pushes=1),
    Mod(mnemonic="mod", pops=2, pushes=1),
    SMod(mnemonic="smod", pops=2, pushes=1),
    AddMod(mnemonic="addmod", pops=3, pushes=1),
    MulMod(mnemonic="mulmod", pops=3, pushes=1),
    Exp(mnemonic="exp", pops=2, pushes=1),
    SignExtend(mnemonic="signextend", pops=2, pushes=1),

    Invalid0c(mnemonic="invalid_0c", exit=true),
    Invalid0d(mnemonic="invalid_0d", exit=true),
    Invalid0e(mnemonic="invalid_0e", exit=true),
    Invalid0f(mnemonic="invalid_0f", exit=true),

    Lt(mnemonic="lt", pops=2, pushes=1),
    Gt(mnemonic="gt", pops=2, pushes=1),
    SLt(mnemonic="slt", pops=2, pushes=1),
    SGt(mnemonic="sgt", pops=2, pushes=1),
    Eq(mnemonic="eq", pops=2, pushes=1),
    IsZero(mnemonic="iszero", pops=1, pushes=1),
    And(mnemonic="and", pops=2, pushes=1),
    Or(mnemonic="or", pops=2, pushes=1),
    Xor(mnemonic="xor", pops=2, pushes=1),
    Not(mnemonic="not", pops=1, pushes=1),
    Byte(mnemonic="byte", pops=2, pushes=1),
    Shl(mnemonic="shl", pops=2, pushes=1),
    Shr(mnemonic="shr", pops=2, pushes=1),
    Sar(mnemonic="sar", pops=2, pushes=1),

    Invalid1e(mnemonic="invalid_1e", exit=true),
    Invalid1f(mnemonic="invalid_1f", exit=true),

    Keccak256(mnemonic="keccak256", pops=2, pushes=1, memory=Access::Read),

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

    Address(mnemonic="address", pushes=1),
    Balance(mnemonic="balance", pops=1, pushes=1),
    Origin(mnemonic="origin", pushes=1),
    Caller(mnemonic="caller", pushes=1),
    CallValue(mnemonic="callvalue", pushes=1),
    CallDataLoad(mnemonic="calldataload", pops=1, pushes=1),
    CallDataSize(mnemonic="calldatasize", pushes=1),
    CallDataCopy(mnemonic="calldatacopy", pops=3, memory=Access::Write),
    CodeSize(mnemonic="codesize", pushes=1),
    CodeCopy(mnemonic="codecopy", pops=3, memory=Access::Write),
    GasPrice(mnemonic="gasprice", pushes=1),
    ExtCodeSize(mnemonic="extcodesize", pops=1, pushes=1),
    ExtCodeCopy(mnemonic="extcodecopy", pops=4, memory=Access::Write),
    ReturnDataSize(mnemonic="returndatasize", pushes=1),
    ReturnDataCopy(mnemonic="returndatacopy", pops=3, memory=Access::Write),
    ExtCodeHash(mnemonic="extcodehash", pops=1, pushes=1),
    BlockHash(mnemonic="blockhash", pops=1, pushes=1),
    Coinbase(mnemonic="coinbase", pushes=1),
    Timestamp(mnemonic="timestamp", pushes=1),
    Number(mnemonic="number", pushes=1),
    Difficulty(mnemonic="difficulty", pushes=1),
    GasLimit(mnemonic="gaslimit", pushes=1),
    ChainId(mnemonic="chainid", pushes=1),
    SelfBalance(mnemonic="selfbalance", pushes=1),
    BaseFee(mnemonic="basefee", pushes=1),

    Invalid49(mnemonic="invalid_49", exit=true),
    Invalid4a(mnemonic="invalid_4a", exit=true),
    Invalid4b(mnemonic="invalid_4b", exit=true),
    Invalid4c(mnemonic="invalid_4c", exit=true),
    Invalid4d(mnemonic="invalid_4d", exit=true),
    Invalid4e(mnemonic="invalid_4e", exit=true),
    Invalid4f(mnemonic="invalid_4f", exit=true),

    Pop(mnemonic="pop", pops=1),
    MLoad(mnemonic="mload", pops=1, pushes=1, memory=Access::Read),
    MStore(mnemonic="mstore", pops=2, memory=Access::Read),
    MStore8(mnemonic="mstore8", pops=2, memory=Access::Read),
    SLoad(mnemonic="sload", pops=1, pushes=1, storage=Access::Read),
    SStore(mnemonic="sstore", pops=2, storage=Access::Write),
    Jump(mnemonic="jump", pops=1, jump=true),
    JumpI(mnemonic="jumpi", pops=2, jump=true),
    GetPc(mnemonic="pc", pushes=1),
    MSize(mnemonic="msize", pushes=1, memory=Access::Read),
    Gas(mnemonic="gas", pushes=1),
    JumpDest(mnemonic="jumpdest", jump_target=true),

    Invalid5c(mnemonic="invalid_5c", exit=true),
    Invalid5d(mnemonic="invalid_5d", exit=true),
    Invalid5e(mnemonic="invalid_5e", exit=true),
    Invalid5f(mnemonic="invalid_5f", exit=true),

    Push1(mnemonic="push1", arg=P1, pushes=1),
    Push2(mnemonic="push2", arg=P2, pushes=1),
    Push3(mnemonic="push3", arg=P3, pushes=1),
    Push4(mnemonic="push4", arg=P4, pushes=1),
    Push5(mnemonic="push5", arg=P5, pushes=1),
    Push6(mnemonic="push6", arg=P6, pushes=1),
    Push7(mnemonic="push7", arg=P7, pushes=1),
    Push8(mnemonic="push8", arg=P8, pushes=1),
    Push9(mnemonic="push9", arg=P9, pushes=1),
    Push10(mnemonic="push10", arg=P10, pushes=1),
    Push11(mnemonic="push11", arg=P11, pushes=1),
    Push12(mnemonic="push12", arg=P12, pushes=1),
    Push13(mnemonic="push13", arg=P13, pushes=1),
    Push14(mnemonic="push14", arg=P14, pushes=1),
    Push15(mnemonic="push15", arg=P15, pushes=1),
    Push16(mnemonic="push16", arg=P16, pushes=1),
    Push17(mnemonic="push17", arg=P17, pushes=1),
    Push18(mnemonic="push18", arg=P18, pushes=1),
    Push19(mnemonic="push19", arg=P19, pushes=1),
    Push20(mnemonic="push20", arg=P20, pushes=1),
    Push21(mnemonic="push21", arg=P21, pushes=1),
    Push22(mnemonic="push22", arg=P22, pushes=1),
    Push23(mnemonic="push23", arg=P23, pushes=1),
    Push24(mnemonic="push24", arg=P24, pushes=1),
    Push25(mnemonic="push25", arg=P25, pushes=1),
    Push26(mnemonic="push26", arg=P26, pushes=1),
    Push27(mnemonic="push27", arg=P27, pushes=1),
    Push28(mnemonic="push28", arg=P28, pushes=1),
    Push29(mnemonic="push29", arg=P29, pushes=1),
    Push30(mnemonic="push30", arg=P30, pushes=1),
    Push31(mnemonic="push31", arg=P31, pushes=1),
    Push32(mnemonic="push32", arg=P32, pushes=1),

    Dup1(mnemonic="dup1", pops=1, pushes=2),
    Dup2(mnemonic="dup2", pops=2, pushes=3),
    Dup3(mnemonic="dup3", pops=3, pushes=4),
    Dup4(mnemonic="dup4", pops=4, pushes=5),
    Dup5(mnemonic="dup5", pops=5, pushes=6),
    Dup6(mnemonic="dup6", pops=6, pushes=7),
    Dup7(mnemonic="dup7", pops=7, pushes=8),
    Dup8(mnemonic="dup8", pops=8, pushes=9),
    Dup9(mnemonic="dup9", pops=9, pushes=10),
    Dup10(mnemonic="dup10", pops=10, pushes=11),
    Dup11(mnemonic="dup11", pops=11, pushes=12),
    Dup12(mnemonic="dup12", pops=12, pushes=13),
    Dup13(mnemonic="dup13", pops=13, pushes=14),
    Dup14(mnemonic="dup14", pops=14, pushes=15),
    Dup15(mnemonic="dup15", pops=15, pushes=16),
    Dup16(mnemonic="dup16", pops=16, pushes=17),
    Swap1(mnemonic="swap1", pops=2, pushes=2),
    Swap2(mnemonic="swap2", pops=3, pushes=3),
    Swap3(mnemonic="swap3", pops=4, pushes=4),
    Swap4(mnemonic="swap4", pops=5, pushes=5),
    Swap5(mnemonic="swap5", pops=6, pushes=6),
    Swap6(mnemonic="swap6", pops=7, pushes=7),
    Swap7(mnemonic="swap7", pops=8, pushes=8),
    Swap8(mnemonic="swap8", pops=9, pushes=9),
    Swap9(mnemonic="swap9", pops=10, pushes=10),
    Swap10(mnemonic="swap10", pops=11, pushes=11),
    Swap11(mnemonic="swap11", pops=12, pushes=12),
    Swap12(mnemonic="swap12", pops=13, pushes=13),
    Swap13(mnemonic="swap13", pops=14, pushes=14),
    Swap14(mnemonic="swap14", pops=15, pushes=15),
    Swap15(mnemonic="swap15", pops=16, pushes=16),
    Swap16(mnemonic="swap16", pops=17, pushes=17),
    Log0(mnemonic="log0", pops=2, memory=Access::Read),
    Log1(mnemonic="log1", pops=3, memory=Access::Read),
    Log2(mnemonic="log2", pops=4, memory=Access::Read),
    Log3(mnemonic="log3", pops=5, memory=Access::Read),
    Log4(mnemonic="log4", pops=6, memory=Access::Read),

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
    InvalidB0(mnemonic="invalid_b0", exit=true),
    InvalidB1(mnemonic="invalid_b1", exit=true),
    InvalidB2(mnemonic="invalid_b2", exit=true),
    InvalidB3(mnemonic="invalid_b3", exit=true),
    InvalidB4(mnemonic="invalid_b4", exit=true),
    InvalidB5(mnemonic="invalid_b5", exit=true),
    InvalidB6(mnemonic="invalid_b6", exit=true),
    InvalidB7(mnemonic="invalid_b7", exit=true),
    InvalidB8(mnemonic="invalid_b8", exit=true),
    InvalidB9(mnemonic="invalid_b9", exit=true),
    InvalidBa(mnemonic="invalid_ba", exit=true),
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
    InvalidE1(mnemonic="invalid_e1", exit=true),
    InvalidE2(mnemonic="invalid_e2", exit=true),
    InvalidE3(mnemonic="invalid_e3", exit=true),
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

    Create(mnemonic="create", pops=3, pushes=1, memory=Access::Read),
    Call(mnemonic="call", pops=7, pushes=1, memory=Access::ReadWrite),
    CallCode(mnemonic="callcode", pops=7, pushes=1, memory=Access::ReadWrite),
    Return(mnemonic="return", pops=2, memory=Access::Read, exit=true),
    DelegateCall(mnemonic="delegatecall", pops=6, pushes=1, memory=Access::ReadWrite),
    Create2(mnemonic="create2", pops=4, pushes=1, memory=Access::Read),

    InvalidF6(mnemonic="invalid_f6", exit=true),
    InvalidF7(mnemonic="invalid_f7", exit=true),
    InvalidF8(mnemonic="invalid_f8", exit=true),
    InvalidF9(mnemonic="invalid_f9", exit=true),

    StaticCall(mnemonic="staticcall", pops=6, pushes=1, memory=Access::ReadWrite),

    InvalidFb(mnemonic="invalid_fb", exit=true),
    InvalidFc(mnemonic="invalid_fc", exit=true),

    Revert(mnemonic="revert", pops=2, memory=Access::ReadWrite, exit=true),
    Invalid(mnemonic="invalid", exit=true),
    SelfDestruct(mnemonic="selfdestruct", pops=1, exit=true),
}

/// Like an [`Op`], except it also supports virtual instructions.
///
/// In addition to the real EVM instructions, `AbstractOp` also supports defining
/// labels, and pushing variable length immediate arguments.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum AbstractOp {
    /// A real `Op`, as opposed to a label or variable sized push.
    Op(Op<Abstract>),

    /// A label, which is a virtual instruction.
    Label(String),

    /// A variable sized push, which is a virtual instruction.
    Push(Imm<Vec<u8>>),

    /// A user-defined instruction macro definition, which is a virtual instruction.
    MacroDefinition(String, Vec<AbstractOp>),

    /// A user-defined instruction macro, which is a virtual instruction.
    Macro(String),
}

impl AbstractOp {
    /// Construct a new `AbstractOp` given a specifier.
    ///
    /// Returns `None` if the instruction described by `spec` requires an immediate
    /// argument.
    pub fn new(spec: Op<Spec>) -> Option<Self> {
        Some(Self::Op(Op::new(spec)?))
    }

    /// Construct an `AbstractOp` with the given label.
    ///
    /// ## Panics
    ///
    /// This function panics if the instruction described by the specifier
    /// does not accept immediate arguments.
    pub fn with_label<S: Into<String>>(spec: Op<Spec>, lbl: S) -> Self {
        Self::Op(Op::with_label(spec, lbl))
    }

    /// Construct an `AbstractOp` with the given immediate argument.
    ///
    /// An error is returned if `imm` doesn't match the immediate size for
    /// the instruction described by `spec`.
    ///
    /// ## Panics
    ///
    /// This function panics if the instruction described by the specifier
    /// does not accept immediate arguments.
    pub fn with_immediate(spec: Op<Spec>, imm: &[u8]) -> Result<Self, TryFromSliceError> {
        Ok(Self::Op(Op::<Abstract>::with_immediate(spec, imm)?))
    }

    pub(crate) fn immediate_label(&self) -> Option<&str> {
        match self {
            Self::Op(op) => op.immediate_label(),
            Self::Push(Imm::Label(lbl)) => Some(lbl),
            Self::Push(_) => None,
            Self::Label(_) => None,
            Self::Macro(_) => None,
            Self::MacroDefinition(_, _) => None,
        }
    }

    ///
    pub(crate) fn realize(&self, address: u32) -> Result<Self, TryFromIntError> {
        let ret = match self {
            Self::Push(Imm::Label(_)) => {
                let spec = Specifier::push_for(address).context(imm::TryFromIntContext)?;
                let bytes = address.to_be_bytes();
                let start = bytes.len() - spec.extra_len() as usize;
                AbstractOp::with_immediate(spec, &bytes[start..]).unwrap()
            }
            Self::Push(Imm::Constant(_)) => {
                panic!("only pushes with a label can be realized");
            }
            Self::Op(op) => Self::Op(op.realize(address)?),
            Self::Label(_) => panic!("labels cannot be realized"),
            Self::Macro(_) => panic!("macros cannot be realized"),
            Self::MacroDefinition(_, _) => panic!("macro definitions cannot be realized"),
        };

        Ok(ret)
    }

    pub(crate) fn concretize(self) -> Option<Op<Concrete>> {
        let res = match self {
            Self::Op(op) => op.concretize(),
            Self::Push(Imm::Label(_)) => panic!("label immediates must be realized first"),
            Self::Push(Imm::Constant(konst)) => {
                let mut trimmed = konst.as_slice();
                while !trimmed.is_empty() && trimmed[0] == 0 {
                    trimmed = &trimmed[1..];
                }
                let spec = Specifier::push(trimmed.len() as u32)?;

                Op::<Concrete>::with_immediate(spec, trimmed).unwrap()
            }
            Self::Label(_) => panic!("labels cannot be concretized"),
            Self::Macro(_) => panic!("macros cannot be concretized"),
            Self::MacroDefinition(_, _) => panic!("macro definitions cannot be concretized"),
        };

        Some(res)
    }

    pub(crate) fn expand(self, declared: &HashMap<String, Vec<AbstractOp>>) -> Option<Vec<Self>> {
        match self {
            Self::Macro(ref name) => {
                // Remap labels to macro scope.
                if let Some(mut content) = declared.get(name).cloned() {
                    let mut labels = HashMap::<String, String>::new();

                    // First pass, find locally defined macros and rename them.
                    for op in content.iter_mut() {
                        match op {
                            AbstractOp::Label(ref mut label) => {
                                // add hash extension later
                                let scoped_label = format!("{}_macro", label);
                                let old = labels.insert(label.to_owned(), scoped_label.clone());
                                assert_eq!(old, None, "label should have been undefined");
                                *label = scoped_label;
                            }
                            _ => continue,
                        }
                    }

                    // Second pass, update local macro invocations.
                    for op in content.iter_mut() {
                        if let Some(label) = op.immediate_label() {
                            if let Some(label) = labels.get(label) {
                                *op = AbstractOp::with_label(op.specifier().unwrap(), label);
                            }
                        }
                    }

                    Some(content)
                } else {
                    None
                }
            }
            _ => panic!("only macros can be expanded"),
        }
    }

    /// Return the total encoded size for this instruction, including the
    /// immediate if one is required.
    ///
    /// If the size of this instruction is undefined (for example a variable sized
    /// push), this function returns `None`.
    pub fn size(&self) -> Option<u32> {
        match self {
            Self::Op(op) => Some(op.size()),
            Self::Label(_) => Some(0),
            Self::Push(_) => None,
            Self::Macro(_) => None,
            Self::MacroDefinition(_, _) => None,
        }
    }

    /// Return the specifier that corresponds to this `AbstractOp`.
    pub fn specifier(&self) -> Option<Op<Spec>> {
        match self {
            Self::Op(op) => Some(op.specifier()),
            _ => None,
        }
    }
}

impl From<Op<Concrete>> for AbstractOp {
    fn from(cop: Op<Concrete>) -> Self {
        Self::Op(cop.into())
    }
}

impl fmt::Display for AbstractOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Op(op) => write!(f, "{}", op),
            Self::Push(txt) => write!(f, r#"%push({})"#, txt),
            Self::Label(lbl) => write!(f, r#".{}:"#, lbl),
            Self::Macro(name) => write!(f, r#"%{}"#, name),
            Self::MacroDefinition(name, content) => write!(f, r#"%{}: {:?}"#, name, content),
        }
    }
}

impl Metadata for AbstractOp {
    fn is_jump(&self) -> bool {
        match self {
            Self::Op(op) => op.is_jump(),
            Self::Push(_) => false,
            Self::Label(_) => false,
            Self::Macro(_) => false,
            Self::MacroDefinition(_, _) => false,
        }
    }

    fn is_jump_target(&self) -> bool {
        match self {
            Self::Op(op) => op.is_jump_target(),
            Self::Push(_) => false,
            Self::Label(_) => false,
            Self::Macro(_) => false,
            Self::MacroDefinition(_, _) => false,
        }
    }

    fn is_exit(&self) -> bool {
        match self {
            Self::Op(op) => op.is_exit(),
            Self::Push(_) => false,
            Self::Label(_) => false,
            Self::Macro(_) => false,
            Self::MacroDefinition(_, _) => false,
        }
    }

    fn memory_access(&self) -> Option<Access> {
        match self {
            Self::Op(op) => op.storage_access(),
            Self::Push(_) => None,
            Self::Label(_) => None,
            Self::Macro(_) => None,
            Self::MacroDefinition(_, _) => None,
        }
    }

    fn storage_access(&self) -> Option<Access> {
        match self {
            Self::Op(op) => op.storage_access(),
            Self::Push(_) => None,
            Self::Label(_) => None,
            Self::Macro(_) => None,
            Self::MacroDefinition(_, _) => None,
        }
    }

    fn pops(&self) -> usize {
        match self {
            Self::Op(op) => op.pops(),
            Self::Push(_) => 0,
            Self::Label(_) => 0,
            Self::Macro(_) => 0,
            Self::MacroDefinition(_, _) => 0,
        }
    }

    fn pushes(&self) -> usize {
        match self {
            Self::Op(op) => op.pushes(),
            Self::Push(_) => 1,
            Self::Label(_) => 0,
            Self::Macro(_) => 0,
            Self::MacroDefinition(_, _) => 0,
        }
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
        for ii in 0..=u8::MAX {
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
        for ii in 0..=u8::MAX {
            let spec = Specifier::try_from(ii).unwrap();
            let txt = spec.to_string();
            let parsed: Specifier = txt.parse().unwrap();
            assert_eq!(spec, parsed);
        }
    }

    #[test]
    fn op_new() {
        for ii in 0..=u8::MAX {
            let spec = Specifier::try_from(ii).unwrap();
            let op = AbstractOp::new(spec);
            if spec.extra_len() > 0 {
                assert_eq!(op, None);
            } else {
                let op = op.unwrap();
                assert_eq!(op.specifier(), Some(spec));
            }
        }
    }

    #[test]
    fn specifier_push_for_zero() {
        let spec = Specifier::push_for(0);
        assert_eq!(spec, Some(Specifier::Push1(())));
    }

    #[test]
    fn specifier_push_for_one() {
        let spec = Specifier::push_for(1);
        assert_eq!(spec, Some(Specifier::Push1(())));
    }

    #[test]
    fn specifier_push_for_255() {
        let spec = Specifier::push_for(255);
        assert_eq!(spec, Some(Specifier::Push1(())));
    }

    #[test]
    fn specifier_push_for_256() {
        let spec = Specifier::push_for(256);
        assert_eq!(spec, Some(Specifier::Push2(())));
    }

    #[test]
    fn specifier_push_for_65535() {
        let spec = Specifier::push_for(65535);
        assert_eq!(spec, Some(Specifier::Push2(())));
    }

    #[test]
    fn specifier_push_for_65536() {
        let spec = Specifier::push_for(65536);
        assert_eq!(spec, Some(Specifier::Push3(())));
    }

    #[test]
    fn specifier_push_for_16777215() {
        let spec = Specifier::push_for(16777215);
        assert_eq!(spec, Some(Specifier::Push3(())));
    }

    #[test]
    fn specifier_push_for_16777216() {
        let spec = Specifier::push_for(16777216);
        assert_eq!(spec, Some(Specifier::Push4(())));
    }

    #[test]
    fn specifier_push_for_4294967295() {
        let spec = Specifier::push_for(4294967295);
        assert_eq!(spec, Some(Specifier::Push4(())));
    }

    #[test]
    fn specifier_to_u8_selfdestruct() {
        let spec = Specifier::SelfDestruct;
        assert_eq!(0xffu8, spec.into());
    }
}
