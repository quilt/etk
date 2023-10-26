//! The EVM Toolkit Operations Crate.
//!
//! You can find more information about the command-line tools in
//! [The ETK Book](https://quilt.github.io/etk/).
//!
//! This crate defines Rust types for all the instructions in the Ethereum
//! Virtual Machine (EVM.)
#![deny(unsafe_code)]
#![deny(missing_docs)]
#![deny(unreachable_pub)]
#![deny(missing_debug_implementations)]

use snafu::{Backtrace, Snafu};

use std::borrow::{Borrow, BorrowMut};

use std::fmt::Display;
use std::str::FromStr;

/// Trait for types that represent an EVM instruction.
pub trait Operation {
    /// The return type of [`Operation::code`].
    type Code: Operation<Code = Self::Code> + Into<u8>;

    /// The return root type of [`Operation::immediate_mut`] and
    /// [`Operation::immediate`].
    type ImmediateRef: ?Sized;

    /// The type of the immediate argument for this operation.
    type Immediate: std::borrow::Borrow<Self::ImmediateRef>
        + std::borrow::BorrowMut<Self::ImmediateRef>;

    /// Get a shared reference to the immediate argument of this operation,
    /// if one exists.
    fn immediate(&self) -> Option<&Self::ImmediateRef>;

    /// Get a mutable reference to the immediate argument of this operation,
    /// if one exists.
    fn immediate_mut(&mut self) -> Option<&mut Self::ImmediateRef>;

    /// Consume this operation and return its immediate argument, if one
    /// exists.
    fn into_immediate(self) -> Option<Self::Immediate>;

    /// Length of immediate argument.
    fn extra_len(&self) -> usize;

    /// The action (opcode) of this operation, without any immediates.
    fn code(&self) -> Self::Code;

    /// The byte (opcode) that indicates this operation.
    fn code_byte(&self) -> u8 {
        self.code().into()
    }

    /// Human-readable name for this operation.
    fn mnemonic(&self) -> &str;

    /// Returns true if the current instruction changes the program counter (other
    /// than incrementing it.)
    fn is_jump(&self) -> bool;

    /// Returns true if the current instruction is a valid destination for jumps.
    fn is_jump_target(&self) -> bool;

    /// Returns true if the current instruction causes the EVM to stop executing
    /// the contract.
    fn is_exit(&self) -> bool;

    /// How many stack elements this instruction pops.
    fn pops(&self) -> usize;

    /// How many stack elements this instruction pushes.
    fn pushes(&self) -> usize;
}

pub mod london {
    //! Instructions available in the London hard fork.
    include!(concat!(env!("OUT_DIR"), "/london.rs"));
}

pub mod shanghai {
    //! Instructions available in the Shanghai hard fork.
    include!(concat!(env!("OUT_DIR"), "/shanghai.rs"));
}

pub mod cancun {
    //! Instructions available in the Cancun hard fork.
    include!(concat!(env!("OUT_DIR"), "/cancun.rs"));
}

/// An operation that can be executed by the EVM.
#[derive(Debug)]
pub enum HardForkOp<T>
where
    T: Immediates + ?Sized,
{
    /// Cancun hard fork operations.
    Cancun(cancun::Op<T>),

    /// Shanghai hard fork operations.
    Shanghai(shanghai::Op<T>),

    /// London hard fork operations.
    London(london::Op<T>),
}

impl<T> Clone for HardForkOp<T>
where
    T: Immediates + ?Sized,
    T::P1: Clone,
    T::P2: Clone,
    T::P3: Clone,
    T::P4: Clone,
    T::P5: Clone,
    T::P6: Clone,
    T::P7: Clone,
    T::P8: Clone,
    T::P9: Clone,
    T::P10: Clone,
    T::P11: Clone,
    T::P12: Clone,
    T::P13: Clone,
    T::P14: Clone,
    T::P15: Clone,
    T::P16: Clone,
    T::P17: Clone,
    T::P18: Clone,
    T::P19: Clone,
    T::P20: Clone,
    T::P21: Clone,
    T::P22: Clone,
    T::P23: Clone,
    T::P24: Clone,
    T::P25: Clone,
    T::P26: Clone,
    T::P27: Clone,
    T::P28: Clone,
    T::P29: Clone,
    T::P30: Clone,
    T::P31: Clone,
    T::P32: Clone,
{
    fn clone(&self) -> Self {
        match *self {
            Self::Cancun(ref op) => Self::Cancun(op.clone()),
            Self::Shanghai(ref op) => Self::Shanghai(op.clone()),
            Self::London(ref op) => Self::London(op.clone()),
        }
    }
}

impl<T> PartialEq<HardForkOp<T>> for HardForkOp<T>
where
    T: Immediates + ?Sized,
    T::P1: PartialEq,
    T::P2: PartialEq,
    T::P3: PartialEq,
    T::P4: PartialEq,
    T::P5: PartialEq,
    T::P6: PartialEq,
    T::P7: PartialEq,
    T::P8: PartialEq,
    T::P9: PartialEq,
    T::P10: PartialEq,
    T::P11: PartialEq,
    T::P12: PartialEq,
    T::P13: PartialEq,
    T::P14: PartialEq,
    T::P15: PartialEq,
    T::P16: PartialEq,
    T::P17: PartialEq,
    T::P18: PartialEq,
    T::P19: PartialEq,
    T::P20: PartialEq,
    T::P21: PartialEq,
    T::P22: PartialEq,
    T::P23: PartialEq,
    T::P24: PartialEq,
    T::P25: PartialEq,
    T::P26: PartialEq,
    T::P27: PartialEq,
    T::P28: PartialEq,
    T::P29: PartialEq,
    T::P30: PartialEq,
    T::P31: PartialEq,
    T::P32: PartialEq,
{
    fn eq(&self, other: &HardForkOp<T>) -> bool {
        match (self, other) {
            (Self::Cancun(op1), HardForkOp::Cancun(op2)) => op1 == op2,
            (Self::Shanghai(op1), HardForkOp::Shanghai(op2)) => op1 == op2,
            (Self::London(op1), HardForkOp::London(op2)) => op1 == op2,
            _ => false,
        }
    }
}

impl<T> Eq for HardForkOp<T>
where
    T: Immediates + ?Sized,
    T::P1: Eq,
    T::P2: Eq,
    T::P3: Eq,
    T::P4: Eq,
    T::P5: Eq,
    T::P6: Eq,
    T::P7: Eq,
    T::P8: Eq,
    T::P9: Eq,
    T::P10: Eq,
    T::P11: Eq,
    T::P12: Eq,
    T::P13: Eq,
    T::P14: Eq,
    T::P15: Eq,
    T::P16: Eq,
    T::P17: Eq,
    T::P18: Eq,
    T::P19: Eq,
    T::P20: Eq,
    T::P21: Eq,
    T::P22: Eq,
    T::P23: Eq,
    T::P24: Eq,
    T::P25: Eq,
    T::P26: Eq,
    T::P27: Eq,
    T::P28: Eq,
    T::P29: Eq,
    T::P30: Eq,
    T::P31: Eq,
    T::P32: Eq,
{
}

impl<T> HardForkOp<T>
where
    T: Immediates + ?Sized,
{
    /// Get an operation from a [`HardForkOp`] enum.
    pub fn new_op(code: HardForkOp<()>) -> Option<HardForkOp<T>> {
        match code {
            HardForkOp::Cancun(op) => cancun::Op::new(op).map(HardForkOp::Cancun),
            HardForkOp::Shanghai(op) => shanghai::Op::new(op).map(HardForkOp::Shanghai),
            HardForkOp::London(op) => london::Op::new(op).map(HardForkOp::London),
        }
    }

    /// Returns the total length of this operation, including its immediate.
    pub fn size(&self) -> usize {
        match self {
            HardForkOp::Cancun(op) => op.size(),
            HardForkOp::Shanghai(op) => op.size(),
            HardForkOp::London(op) => op.size(),
        }
    }
}

impl HardForkOp<()> {
    /// Join this opcode with an immediate argument.
    ///
    /// Panics if this opcode does not take an immediate argument.
    pub fn with<T, I, E>(self, immediate: I) -> Result<HardForkOp<T>, E>
    where
        T: ?Sized + Immediates,
        I: TryInto<T::P1, Error = E>,
        I: TryInto<T::P2, Error = E>,
        I: TryInto<T::P3, Error = E>,
        I: TryInto<T::P4, Error = E>,
        I: TryInto<T::P5, Error = E>,
        I: TryInto<T::P6, Error = E>,
        I: TryInto<T::P7, Error = E>,
        I: TryInto<T::P8, Error = E>,
        I: TryInto<T::P9, Error = E>,
        I: TryInto<T::P10, Error = E>,
        I: TryInto<T::P11, Error = E>,
        I: TryInto<T::P12, Error = E>,
        I: TryInto<T::P13, Error = E>,
        I: TryInto<T::P14, Error = E>,
        I: TryInto<T::P15, Error = E>,
        I: TryInto<T::P16, Error = E>,
        I: TryInto<T::P17, Error = E>,
        I: TryInto<T::P18, Error = E>,
        I: TryInto<T::P19, Error = E>,
        I: TryInto<T::P20, Error = E>,
        I: TryInto<T::P21, Error = E>,
        I: TryInto<T::P22, Error = E>,
        I: TryInto<T::P23, Error = E>,
        I: TryInto<T::P24, Error = E>,
        I: TryInto<T::P25, Error = E>,
        I: TryInto<T::P26, Error = E>,
        I: TryInto<T::P27, Error = E>,
        I: TryInto<T::P28, Error = E>,
        I: TryInto<T::P29, Error = E>,
        I: TryInto<T::P30, Error = E>,
        I: TryInto<T::P31, Error = E>,
        I: TryInto<T::P32, Error = E>,
    {
        match self {
            HardForkOp::Cancun(op) => Ok(HardForkOp::Cancun(op.with(immediate)?)),
            HardForkOp::Shanghai(op) => Ok(HardForkOp::Shanghai(op.with(immediate)?)),
            HardForkOp::London(op) => Ok(HardForkOp::London(op.with(immediate)?)),
        }
    }
}

impl<T> Operation for HardForkOp<T>
where
    T: Immediates + ?Sized,
{
    type Code = HardForkOp<()>;
    type Immediate = T::Immediate;
    type ImmediateRef = T::ImmediateRef;
    fn immediate(&self) -> Option<&Self::ImmediateRef> {
        match self {
            HardForkOp::Cancun(op) => op.immediate(),
            HardForkOp::Shanghai(op) => op.immediate(),
            HardForkOp::London(op) => op.immediate(),
        }
    }
    fn immediate_mut(&mut self) -> Option<&mut Self::ImmediateRef> {
        match self {
            HardForkOp::Cancun(op) => op.immediate_mut(),
            HardForkOp::Shanghai(op) => op.immediate_mut(),
            HardForkOp::London(op) => op.immediate_mut(),
        }
    }
    fn into_immediate(self) -> Option<Self::Immediate> {
        match self {
            HardForkOp::Cancun(op) => op.into_immediate(),
            HardForkOp::Shanghai(op) => op.into_immediate(),
            HardForkOp::London(op) => op.into_immediate(),
        }
    }
    fn extra_len(&self) -> usize {
        match self {
            HardForkOp::Cancun(op) => op.extra_len(),
            HardForkOp::Shanghai(op) => op.extra_len(),
            HardForkOp::London(op) => op.extra_len(),
        }
    }
    fn code(&self) -> Self::Code {
        match self {
            HardForkOp::Cancun(op) => HardForkOp::Cancun(op.code()),
            HardForkOp::Shanghai(op) => HardForkOp::Shanghai(op.code()),
            HardForkOp::London(op) => HardForkOp::London(op.code()),
        }
    }
    fn mnemonic(&self) -> &str {
        match self {
            HardForkOp::Cancun(op) => op.mnemonic(),
            HardForkOp::Shanghai(op) => op.mnemonic(),
            HardForkOp::London(op) => op.mnemonic(),
        }
    }
    fn is_jump(&self) -> bool {
        match self {
            HardForkOp::Cancun(op) => op.is_jump(),
            HardForkOp::Shanghai(op) => op.is_jump(),
            HardForkOp::London(op) => op.is_jump(),
        }
    }
    fn is_jump_target(&self) -> bool {
        match self {
            HardForkOp::Cancun(op) => op.is_jump_target(),
            HardForkOp::Shanghai(op) => op.is_jump_target(),
            HardForkOp::London(op) => op.is_jump_target(),
        }
    }
    fn is_exit(&self) -> bool {
        match self {
            HardForkOp::Cancun(op) => op.is_exit(),
            HardForkOp::Shanghai(op) => op.is_exit(),
            HardForkOp::London(op) => op.is_exit(),
        }
    }
    fn pops(&self) -> usize {
        match self {
            HardForkOp::Cancun(op) => op.pops(),
            HardForkOp::Shanghai(op) => op.pops(),
            HardForkOp::London(op) => op.pops(),
        }
    }
    fn pushes(&self) -> usize {
        match self {
            HardForkOp::Cancun(op) => op.pushes(),
            HardForkOp::Shanghai(op) => op.pushes(),
            HardForkOp::London(op) => op.pushes(),
        }
    }
}

impl From<HardForkOp<()>> for u8 {
    fn from(op: HardForkOp<()>) -> u8 {
        match op {
            HardForkOp::Cancun(op) => op.code_byte(),
            HardForkOp::Shanghai(op) => op.code_byte(),
            HardForkOp::London(op) => op.code_byte(),
        }
    }
}

impl std::fmt::Display for HardForkOp<()> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            HardForkOp::Cancun(op) => op.fmt(f),
            HardForkOp::Shanghai(op) => op.fmt(f),
            HardForkOp::London(op) => op.fmt(f),
        }
    }
}

/// Hard forks of the Ethereum Virtual Machine.
#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq)]
pub enum HardFork {
    /// The London hard fork.
    London,

    /// The Shanghai hard fork.
    Shanghai,

    /// The Cancun hard fork.
    Cancun,
}

impl HardFork {
    /// Returns true if the given hardfork directive is valid for this hardfork.
    pub fn is_valid(&self, directive: &HardForkDirective) -> bool {
        match directive.operator {
            Some(OperatorDirective::GreaterThan) => self > &directive.hardfork,
            Some(OperatorDirective::GreaterThanOrEqual) => self >= &directive.hardfork,
            Some(OperatorDirective::LessThan) => self < &directive.hardfork,
            Some(OperatorDirective::LessThanOrEqual) => self <= &directive.hardfork,
            None => self == &directive.hardfork,
        }
    }
}

impl Default for HardFork {
    fn default() -> Self {
        Self::Cancun
    }
}

impl Display for HardFork {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::London => write!(f, "london"),
            Self::Shanghai => write!(f, "shanghai"),
            Self::Cancun => write!(f, "cancun"),
        }
    }
}

impl FromStr for HardFork {
    type Err = FromStrError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "london" => Ok(HardFork::London),
            "shanghai" => Ok(HardFork::Shanghai),
            "cancun" => Ok(HardFork::Cancun),
            _ => FromStrSnafu { mnemonic: s }.fail(),
        }
    }
}

/// A directive that specifies a hardfork.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HardForkDirective {
    /// The operator used to define a range of hardforks.
    pub operator: Option<OperatorDirective>,

    /// The hardfork.
    pub hardfork: HardFork,
}

impl Display for HardForkDirective {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match &self.operator {
            Some(op) => write!(f, "{}{}", op, self.hardfork),
            None => write!(f, "{}", self.hardfork),
        }
    }
}

impl Into<HardForkDirective> for Option<&HardForkDirective> {
    fn into(self) -> HardForkDirective {
        match self {
            Some(hfd) => hfd.to_owned(),
            None => panic!("Cannot convert None into HardForkDirective"),
        }
    }
}

impl PartialOrd<Option<HardForkDirective>> for HardForkDirective {
    fn partial_cmp(&self, other: &Option<HardForkDirective>) -> Option<std::cmp::Ordering> {
        match other {
            Some(_) => self.partial_cmp(other),
            None => Some(std::cmp::Ordering::Greater),
        }
    }
}

impl PartialEq<Option<HardForkDirective>> for HardForkDirective {
    fn eq(&self, other: &Option<HardForkDirective>) -> bool {
        match other {
            Some(hfd) => self.eq(hfd),
            None => false,
        }
    }
}

impl PartialOrd<HardForkDirective> for Option<HardForkDirective> {
    fn partial_cmp(&self, other: &HardForkDirective) -> Option<std::cmp::Ordering> {
        match self {
            Some(hfd) => hfd.partial_cmp(&Some(other.to_owned())),
            None => Some(std::cmp::Ordering::Less),
        }
    }
}

impl PartialEq<HardForkDirective> for Option<HardForkDirective> {
    fn eq(&self, other: &HardForkDirective) -> bool {
        match self {
            Some(hfd) => hfd.eq(other),
            None => false,
        }
    }
}

/// An operator used to define a range of hardforks.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OperatorDirective {
    /// The `>=` operator.
    GreaterThan,

    /// The `<=` operator.
    GreaterThanOrEqual,

    /// The `>` operator.
    LessThan,

    /// The `<` operator.
    LessThanOrEqual,
}

impl From<&str> for OperatorDirective {
    fn from(s: &str) -> Self {
        match s {
            ">=" => Self::GreaterThanOrEqual,
            "<=" => Self::LessThanOrEqual,
            ">" => Self::GreaterThan,
            "<" => Self::LessThan,
            _ => panic!("Invalid operator: {}", s),
        }
    }
}

impl Display for OperatorDirective {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::GreaterThanOrEqual => write!(f, ">="),
            Self::LessThanOrEqual => write!(f, "<="),
            Self::GreaterThan => write!(f, ">"),
            Self::LessThan => write!(f, "<"),
        }
    }
}

/// Error that can occur when parsing an operation from a string.
#[derive(Debug, Snafu)]
pub struct FromStrError {
    backtrace: Backtrace,
    mnemonic: String,
}

/// Errors that can occur when parsing an operation from a byte slice.
#[derive(Debug, Snafu)]
pub enum FromSliceError<E>
where
    E: 'static + std::fmt::Display + std::error::Error,
{
    /// Converting the byte slice into an immediate failed.
    ///
    /// Often means the slice was the wrong length.
    #[snafu(context(false))]
    TryInto {
        /// The source of this error.
        source: E,

        /// The source location where this error occurred.
        backtrace: Backtrace,
    },

    /// The slice is too long for instructions that do not take an immediate argument.
    NoImmediate {
        /// The source location where this error occurred.
        backtrace: Backtrace,
    },
}

/// Trait for types that contain an immediate argument.
pub trait Immediate<const N: usize> {}

impl<const N: usize> Immediate<N> for [u8; N] {}

impl<const N: usize> Immediate<N> for () {}

/// Immediate type for operations that do not have an immediate argument.
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub enum Void {}

impl<const N: usize> Immediate<N> for Void {}

/// Trait for describing the types of immediate arguments for operation enums.
pub trait Immediates {
    /// A reference type common to all immediate types ([`Self::P1`], [`Self::P2`], ...)
    ///
    /// For example, for immediates like `[u8; _]`, a possible `ImmediateRef` type
    /// is `[u8]`.
    type ImmediateRef: ?Sized;

    /// A common type that all immediates ([`Self::P1`], [`Self::P2`], ...) can
    /// be converted into.
    ///
    /// For example, for immediates like `[u8; _]`, a possible `Immediate` type
    /// is `Vec<u8>`.
    type Immediate: Borrow<Self::ImmediateRef> + BorrowMut<Self::ImmediateRef>;

    /// The type of immediates used by `push1` instructions.
    type P1: Immediate<1>
        + Borrow<Self::ImmediateRef>
        + BorrowMut<Self::ImmediateRef>
        + Into<Self::Immediate>;

    /// The type of immediates used by `push2` instructions.
    type P2: Immediate<2>
        + Borrow<Self::ImmediateRef>
        + BorrowMut<Self::ImmediateRef>
        + Into<Self::Immediate>;

    /// The type of immediates used by `push3` instructions.
    type P3: Immediate<3>
        + Borrow<Self::ImmediateRef>
        + BorrowMut<Self::ImmediateRef>
        + Into<Self::Immediate>;

    /// The type of immediates used by `push4` instructions.
    type P4: Immediate<4>
        + Borrow<Self::ImmediateRef>
        + BorrowMut<Self::ImmediateRef>
        + Into<Self::Immediate>;

    /// The type of immediates used by `push5` instructions.
    type P5: Immediate<5>
        + Borrow<Self::ImmediateRef>
        + BorrowMut<Self::ImmediateRef>
        + Into<Self::Immediate>;

    /// The type of immediates used by `push6` instructions.
    type P6: Immediate<6>
        + Borrow<Self::ImmediateRef>
        + BorrowMut<Self::ImmediateRef>
        + Into<Self::Immediate>;

    /// The type of immediates used by `push7` instructions.
    type P7: Immediate<7>
        + Borrow<Self::ImmediateRef>
        + BorrowMut<Self::ImmediateRef>
        + Into<Self::Immediate>;

    /// The type of immediates used by `push8` instructions.
    type P8: Immediate<8>
        + Borrow<Self::ImmediateRef>
        + BorrowMut<Self::ImmediateRef>
        + Into<Self::Immediate>;

    /// The type of immediates used by `push9` instructions.
    type P9: Immediate<9>
        + Borrow<Self::ImmediateRef>
        + BorrowMut<Self::ImmediateRef>
        + Into<Self::Immediate>;

    /// The type of immediates used by `push10` instructions.
    type P10: Immediate<10>
        + Borrow<Self::ImmediateRef>
        + BorrowMut<Self::ImmediateRef>
        + Into<Self::Immediate>;

    /// The type of immediates used by `push11` instructions.
    type P11: Immediate<11>
        + Borrow<Self::ImmediateRef>
        + BorrowMut<Self::ImmediateRef>
        + Into<Self::Immediate>;

    /// The type of immediates used by `push12` instructions.
    type P12: Immediate<12>
        + Borrow<Self::ImmediateRef>
        + BorrowMut<Self::ImmediateRef>
        + Into<Self::Immediate>;

    /// The type of immediates used by `push13` instructions.
    type P13: Immediate<13>
        + Borrow<Self::ImmediateRef>
        + BorrowMut<Self::ImmediateRef>
        + Into<Self::Immediate>;

    /// The type of immediates used by `push14` instructions.
    type P14: Immediate<14>
        + Borrow<Self::ImmediateRef>
        + BorrowMut<Self::ImmediateRef>
        + Into<Self::Immediate>;

    /// The type of immediates used by `push15` instructions.
    type P15: Immediate<15>
        + Borrow<Self::ImmediateRef>
        + BorrowMut<Self::ImmediateRef>
        + Into<Self::Immediate>;

    /// The type of immediates used by `push16` instructions.
    type P16: Immediate<16>
        + Borrow<Self::ImmediateRef>
        + BorrowMut<Self::ImmediateRef>
        + Into<Self::Immediate>;

    /// The type of immediates used by `push17` instructions.
    type P17: Immediate<17>
        + Borrow<Self::ImmediateRef>
        + BorrowMut<Self::ImmediateRef>
        + Into<Self::Immediate>;

    /// The type of immediates used by `push18` instructions.
    type P18: Immediate<18>
        + Borrow<Self::ImmediateRef>
        + BorrowMut<Self::ImmediateRef>
        + Into<Self::Immediate>;

    /// The type of immediates used by `push19` instructions.
    type P19: Immediate<19>
        + Borrow<Self::ImmediateRef>
        + BorrowMut<Self::ImmediateRef>
        + Into<Self::Immediate>;

    /// The type of immediates used by `push20` instructions.
    type P20: Immediate<20>
        + Borrow<Self::ImmediateRef>
        + BorrowMut<Self::ImmediateRef>
        + Into<Self::Immediate>;

    /// The type of immediates used by `push21` instructions.
    type P21: Immediate<21>
        + Borrow<Self::ImmediateRef>
        + BorrowMut<Self::ImmediateRef>
        + Into<Self::Immediate>;

    /// The type of immediates used by `push22` instructions.
    type P22: Immediate<22>
        + Borrow<Self::ImmediateRef>
        + BorrowMut<Self::ImmediateRef>
        + Into<Self::Immediate>;

    /// The type of immediates used by `push23` instructions.
    type P23: Immediate<23>
        + Borrow<Self::ImmediateRef>
        + BorrowMut<Self::ImmediateRef>
        + Into<Self::Immediate>;

    /// The type of immediates used by `push24` instructions.
    type P24: Immediate<24>
        + Borrow<Self::ImmediateRef>
        + BorrowMut<Self::ImmediateRef>
        + Into<Self::Immediate>;

    /// The type of immediates used by `push25` instructions.
    type P25: Immediate<25>
        + Borrow<Self::ImmediateRef>
        + BorrowMut<Self::ImmediateRef>
        + Into<Self::Immediate>;

    /// The type of immediates used by `push26` instructions.
    type P26: Immediate<26>
        + Borrow<Self::ImmediateRef>
        + BorrowMut<Self::ImmediateRef>
        + Into<Self::Immediate>;

    /// The type of immediates used by `push27` instructions.
    type P27: Immediate<27>
        + Borrow<Self::ImmediateRef>
        + BorrowMut<Self::ImmediateRef>
        + Into<Self::Immediate>;

    /// The type of immediates used by `push28` instructions.
    type P28: Immediate<28>
        + Borrow<Self::ImmediateRef>
        + BorrowMut<Self::ImmediateRef>
        + Into<Self::Immediate>;

    /// The type of immediates used by `push29` instructions.
    type P29: Immediate<29>
        + Borrow<Self::ImmediateRef>
        + BorrowMut<Self::ImmediateRef>
        + Into<Self::Immediate>;

    /// The type of immediates used by `push30` instructions.
    type P30: Immediate<30>
        + Borrow<Self::ImmediateRef>
        + BorrowMut<Self::ImmediateRef>
        + Into<Self::Immediate>;

    /// The type of immediates used by `push31` instructions.
    type P31: Immediate<31>
        + Borrow<Self::ImmediateRef>
        + BorrowMut<Self::ImmediateRef>
        + Into<Self::Immediate>;

    /// The type of immediates used by `push32` instructions.
    type P32: Immediate<32>
        + Borrow<Self::ImmediateRef>
        + BorrowMut<Self::ImmediateRef>
        + Into<Self::Immediate>;
}

impl Immediates for () {
    type ImmediateRef = ();
    type Immediate = ();

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

impl Immediates for [u8] {
    type ImmediateRef = [u8];
    type Immediate = Vec<u8>;

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
