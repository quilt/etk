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

pub mod prague {
    //! Instructions available in the London hard fork.
    include!(concat!(env!("OUT_DIR"), "/prague.rs"));
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
