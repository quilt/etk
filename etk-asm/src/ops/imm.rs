use etk_ops::Immediate;

use num_bigint::{BigInt, Sign};

use snafu::{Backtrace, Snafu};

use std::convert::TryFrom;
use std::fmt::{self, Debug};

use super::expression::{Expression, Terminal};
use super::macros::ExpressionMacroInvocation;

/// An error that arises when converting a slice into an immediate.
#[derive(Snafu, Debug)]
#[snafu(context(suffix(Context)))]
pub struct TryFromSliceError {
    backtrace: Backtrace,
}

impl From<std::convert::Infallible> for TryFromSliceError {
    fn from(e: std::convert::Infallible) -> Self {
        match e {}
    }
}

/// An immediate value for push instructions.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Imm {
    /// An infix tree representing a mathematical expression.
    pub tree: Expression,
}

impl Imm {
    /// Construct an `Imm` with a label.
    pub fn with_label<S: Into<String>>(s: S) -> Self {
        Terminal::Label(s.into()).into()
    }

    /// Construct an `Imm` with a variable.
    pub fn with_variable<S: Into<String>>(s: S) -> Self {
        Terminal::Variable(s.into()).into()
    }

    /// Construct an `Imm` with an expression.
    pub fn with_expression(e: Expression) -> Self {
        e.into()
    }

    /// Construct an `Imm` with an expression macro.
    pub fn with_macro(m: ExpressionMacroInvocation) -> Self {
        Expression::Macro(m).into()
    }
}

impl From<Vec<u8>> for Imm {
    fn from(konst: Vec<u8>) -> Self {
        Imm::from(Terminal::Number(BigInt::from_bytes_be(Sign::Plus, &konst)))
    }
}

impl fmt::Display for Imm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.tree)
    }
}

macro_rules! impl_from {
    ($ii:literal;) => {
        impl From<[u8; $ii]> for Imm {
            fn from(konst: [u8; $ii]) -> Self {
                Imm::from(Terminal::Number(BigInt::from_bytes_be(
                    Sign::Plus,
                    &konst,
                )))
            }
        }
    };

    ($ii:literal; $ty:ty $(, $rest:ty)* $(,)*) => {
        impl From<$ty> for Imm {
            fn from(x: $ty) -> Self {
                Imm::from(Terminal::Number(x.into()))
            }
        }

        impl_from!($ii; $($rest,)*);
    }
}

macro_rules! impl_try_from_slice {
    ($ii:literal) => {
        impl TryFrom<&[u8]> for Imm {
            type Error = TryFromSliceError;

            fn try_from(x: &[u8]) -> Result<Self, Self::Error> {
                if x.len() > $ii {
                    return TryFromSliceContext.fail();
                }

                Ok(Imm::from(Terminal::Number(BigInt::from_bytes_be(
                    Sign::Plus,
                    x,
                ))))
            }
        }
    };
}

impl_from!(1;);
impl_from!(2;);
impl_from!(3;);
impl_from!(4;);
impl_from!(5;);
impl_from!(6;);
impl_from!(7;);
impl_from!(8;);
impl_from!(9;);
impl_from!(10;);
impl_from!(11;);
impl_from!(12;);
impl_from!(13;);
impl_from!(14;);
impl_from!(15;);
impl_from!(16;);
impl_from!(17;);
impl_from!(18;);
impl_from!(19;);
impl_from!(20;);
impl_from!(21;);
impl_from!(22;);
impl_from!(23;);
impl_from!(24;);
impl_from!(25;);
impl_from!(26;);
impl_from!(27;);
impl_from!(28;);
impl_from!(29;);
impl_from!(30;);
impl_from!(31;);
impl_from!(32; u8, u16, u32, u64, u128);

impl_try_from_slice!(32);

impl From<Expression> for Imm {
    fn from(tree: Expression) -> Self {
        Self { tree }
    }
}

impl From<Terminal> for Imm {
    fn from(terminal: Terminal) -> Self {
        Expression::Terminal(terminal).into()
    }
}

impl<const N: usize> Immediate<N> for Imm {}
