use num_bigint::{BigInt, Sign};
use snafu::OptionExt;

use std::collections::HashMap;
use std::convert::TryFrom;
use std::fmt::{self, Debug};
use std::marker::PhantomData;

use super::macros::{ExpressionMacroInvocation, MacroDefinition};
use super::{Labels, Macros, Variables};

use snafu::{Backtrace, Snafu};

/// An error that arises when a label is used without being declared.
#[derive(Snafu, Debug)]
#[snafu(visibility = "pub")]
pub enum Error {
    #[snafu(display("unknown label `{}`", label))]
    #[non_exhaustive]
    UnknownLabel { label: String, backtrace: Backtrace },

    #[snafu(display("unknown macro `{}`", macro_name))]
    #[non_exhaustive]
    UnknownMacro {
        macro_name: String,
        backtrace: Backtrace,
    },

    #[snafu(display("undefined macro variable `{}`", name))]
    #[non_exhaustive]
    UndefinedVariable { name: String, backtrace: Backtrace },
}

/// An error that arises when converting an integer into an immediate.
#[derive(Snafu, Debug)]
#[snafu(visibility = "pub")]
pub struct TryFromIntError {
    backtrace: Backtrace,
}

/// An error that arises when converting a slice into an immediate.
#[derive(Snafu, Debug)]
#[snafu(visibility = "pub")]
pub struct TryFromSliceError {
    backtrace: Backtrace,
}

impl From<std::convert::Infallible> for TryFromIntError {
    fn from(e: std::convert::Infallible) -> Self {
        match e {}
    }
}

/// An immediate value for push instructions.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Imm<T> {
    /// An infix tree representing a mathematical expression.
    pub tree: Expression,
    _p: PhantomData<T>,
}

impl<T> Imm<T> {
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

    /// Returns all labels referenced in an immediate's expression.
    pub fn labels(&self, macros: &Macros) -> Result<Vec<String>, Error> {
        self.tree.labels(macros)
    }
}

impl From<Vec<u8>> for Imm<Vec<u8>> {
    fn from(konst: Vec<u8>) -> Self {
        Imm::from(Terminal::Number(BigInt::from_bytes_be(Sign::Plus, &konst)))
    }
}

impl<T> fmt::Display for Imm<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.tree)
    }
}

impl From<u128> for Imm<Vec<u8>> {
    fn from(konst: u128) -> Self {
        Imm::from(Terminal::Number(konst.into()))
    }
}

macro_rules! impl_from {
    ($ii:literal;) => {
        impl From<[u8; $ii]> for Imm<[u8; $ii]> {
            fn from(konst: [u8; $ii]) -> Self {
                Imm::from(Terminal::Number(BigInt::from_bytes_be(
                    Sign::Plus,
                    &konst,
                )))
            }
        }
    };

    ($ii:literal; $ty:ty $(, $rest:ty)* $(,)*) => {
        impl From<$ty> for Imm<[u8; $ii]> {
            fn from(x: $ty) -> Self {
                Imm::from(Terminal::Number(x.into()))
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

                Ok(Imm::from(Terminal::Number(x.into())))
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

                Ok(Imm::from(Terminal::Number(BigInt::from_bytes_be(
                    Sign::Plus,
                    x,
                ))))
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

/// An mathematical expression.
#[derive(Clone, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Expression {
    /// A mathematical expression.
    Expression(Box<Self>),

    /// An expression macro invocation.
    Macro(ExpressionMacroInvocation),

    /// A terminal value.
    Terminal(Terminal),

    /// An addition operation.
    Plus(Box<Self>, Box<Self>),

    /// A subtraction operation.
    Minus(Box<Self>, Box<Self>),

    /// A multiplication operation.
    Times(Box<Self>, Box<Self>),

    /// A division operation.
    Divide(Box<Self>, Box<Self>),
}

impl Debug for Expression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expression::Expression(s) => write!(f, r#"({:?})"#, s),
            Expression::Macro(m) => write!(f, r#"Expression::Macro("{}")"#, m.name),
            Expression::Terminal(t) => write!(f, r#"Expression::Terminal({:?})"#, t),
            Expression::Plus(lhs, rhs) => write!(f, r#"Expression::Plus({:?}, {:?})"#, lhs, rhs),
            Expression::Minus(lhs, rhs) => write!(f, r#"Expression::Minus({:?}, {:?})"#, lhs, rhs),
            Expression::Times(lhs, rhs) => write!(f, r#"Expression::Times({:?}, {:?})"#, lhs, rhs),
            Expression::Divide(lhs, rhs) => {
                write!(f, r#"Expression::Divide({:?}, {:?})"#, lhs, rhs)
            }
        }
    }
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expression::Expression(s) => write!(f, r#"({})"#, s),
            Expression::Macro(m) => unimplemented!(),
            Expression::Terminal(t) => write!(f, r#"{}"#, t),
            Expression::Plus(lhs, rhs) => write!(f, r#"{}+{}"#, lhs, rhs),
            Expression::Minus(lhs, rhs) => write!(f, r#"{}-{}"#, lhs, rhs),
            Expression::Times(lhs, rhs) => write!(f, r#"{}*{}"#, lhs, rhs),
            Expression::Divide(lhs, rhs) => write!(f, r#"{}/{}"#, lhs, rhs),
        }
    }
}

/// A terminal value in an expression.
#[derive(Clone, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Terminal {
    /// A integer value.
    Number(BigInt),

    /// A label.
    Label(String),

    /// A macro variable.
    Variable(String),

    /// A bytes value.
    Bytes(Vec<u8>),
}

impl Terminal {
    /// Evaluates a terminal into an integer value.
    pub fn evaluate(
        &self,
        labels: &Labels,
        variables: &Variables,
        macros: &Macros,
    ) -> Result<BigInt, Error> {
        let ret = match self {
            Terminal::Number(n) => n.clone(),
            Terminal::Label(label) => labels
                .get(label)
                .context(UnknownLabel { label })?
                .context(UnknownLabel { label })?
                .into(),
            Terminal::Variable(name) => variables
                .get(name)
                .context(UndefinedVariable { name })?
                .evaluate(labels, variables, macros)?,
            Terminal::Bytes(_) => unimplemented!(),
        };

        Ok(ret)
    }
}

impl Expression {
    /// Returns the constant value of the expression.
    pub fn constant(&self) -> Option<BigInt> {
        self.evaluate(&HashMap::new(), &HashMap::new(), &HashMap::new())
            .ok()
    }
    /// Evaluates the expression, substituting resolved label address for labels.
    pub fn evaluate(
        &self,
        labels: &HashMap<String, Option<u32>>,
        variables: &HashMap<String, Expression>,
        macros: &HashMap<String, MacroDefinition>,
    ) -> Result<BigInt, Error> {
        fn recursive_eval(
            e: &Expression,
            l: &HashMap<String, Option<u32>>,
            v: &HashMap<String, Expression>,
            m: &HashMap<String, MacroDefinition>,
        ) -> Result<BigInt, Error> {
            let ret = match e {
                Expression::Expression(expr) => recursive_eval(expr, l, v, m)?,
                Expression::Macro(mac) => m
                    .get(&mac.name)
                    .context(UnknownMacro {
                        macro_name: mac.name.clone(),
                    })?
                    .unwrap_expression()
                    .content
                    .tree
                    .evaluate(l, v, m)?,
                Expression::Terminal(term) => term.evaluate(l, v, m)?,
                Expression::Plus(lhs, rhs) => {
                    recursive_eval(lhs, l, v, m)? + recursive_eval(rhs, l, v, m)?
                }
                Expression::Minus(lhs, rhs) => {
                    recursive_eval(lhs, l, v, m)? - recursive_eval(rhs, l, v, m)?
                }
                Expression::Times(lhs, rhs) => {
                    recursive_eval(lhs, l, v, m)? * recursive_eval(rhs, l, v, m)?
                }
                Expression::Divide(lhs, rhs) => {
                    recursive_eval(lhs, l, v, m)? / recursive_eval(rhs, l, v, m)?
                }
            };
            Ok(ret)
        }
        // TODO error if top level receives negative value.
        recursive_eval(self, labels, variables, macros)
    }

    /// Returns a list of all labels used in the expression.
    pub fn labels(&self, macros: &Macros) -> Result<Vec<String>, Error> {
        fn dfs(x: &Expression, m: &Macros) -> Result<Vec<String>, Error> {
            match x {
                Expression::Expression(e) => dfs(e, m),
                Expression::Macro(mac) => m
                    .get(&mac.name)
                    .context(UnknownMacro {
                        macro_name: mac.name.clone(),
                    })?
                    .unwrap_expression()
                    .content
                    .tree
                    .labels(m),
                Expression::Terminal(Terminal::Label(label)) => Ok(vec![label.clone()]),
                Expression::Terminal(_) => Ok(vec![]),
                Expression::Plus(lhs, rhs)
                | Expression::Minus(lhs, rhs)
                | Expression::Times(lhs, rhs)
                | Expression::Divide(lhs, rhs) => dfs(lhs, m).and_then(|x: Vec<String>| {
                    let ret = x.into_iter().chain(dfs(rhs, m)?).collect();
                    Ok(ret)
                }),
            }
        }

        dfs(self, macros)
    }
}

impl Debug for Terminal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Terminal::Label(l) => write!(f, r#"Terminal::Label({})"#, l),
            Terminal::Number(n) => write!(f, r#"Terminal::Number({})"#, n),
            Terminal::Bytes(b) => write!(f, r#"Terminal::Bytes(0x{})"#, hex::encode(b)),
            Terminal::Variable(v) => write!(f, r#"Terminal::Variable({})"#, v),
        }
    }
}

impl fmt::Display for Terminal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Terminal::Label(l) => write!(f, r#"Label({})"#, l),
            Terminal::Number(n) => write!(f, r#"{}"#, n),
            Terminal::Bytes(b) => write!(f, r#"0x{}"#, hex::encode(b)),
            Terminal::Variable(v) => write!(f, r#"Variable({})"#, v),
        }
    }
}

impl<T> From<Expression> for Imm<T> {
    fn from(tree: Expression) -> Self {
        Self {
            tree,
            _p: PhantomData,
        }
    }
}

impl<T> From<Terminal> for Imm<T> {
    fn from(terminal: Terminal) -> Self {
        Expression::Terminal(terminal).into()
    }
}

impl From<Terminal> for Expression {
    fn from(terminal: Terminal) -> Self {
        Expression::Terminal(terminal)
    }
}

impl From<Terminal> for Box<Expression> {
    fn from(terminal: Terminal) -> Self {
        Box::new(Expression::Terminal(terminal))
    }
}

impl From<u64> for Box<Expression> {
    fn from(n: u64) -> Self {
        Box::new(Expression::Terminal(Terminal::Number(n.into())))
    }
}

impl From<u64> for Terminal {
    fn from(n: u64) -> Self {
        Terminal::Number(n.into())
    }
}

impl From<BigInt> for Box<Expression> {
    fn from(n: BigInt) -> Self {
        Box::new(n.into())
    }
}

impl From<BigInt> for Expression {
    fn from(n: BigInt) -> Self {
        Expression::Terminal(Terminal::Number(n))
    }
}

#[doc(hidden)]
pub trait Immediate<const N: usize>: Debug + Clone + Eq + PartialEq {
    fn extra_len() -> usize {
        N
    }
}

impl<T, const N: usize> Immediate<N> for [T; N] where T: Debug + Clone + Eq + PartialEq {}
impl<const N: usize> Immediate<N> for Imm<[u8; N]> {}
impl<const N: usize> Immediate<N> for () {}

#[cfg(test)]
mod tests {
    use assert_matches::assert_matches;

    use hex_literal::hex;

    use super::*;

    // #[test]
    // fn imm4_from_array() {
    //     let imm = Imm::from(hex!("95ea7b30"));
    //     assert_matches!(imm, Terminal::Bytes(vec![0x95, 0xea, 0x7b, 0x30]).into());
    // }

    #[test]
    fn expr_simple() {
        // 24 + 42 = 66
        let expr = Expression::Plus(
            Terminal::Number(24.into()).into(),
            Terminal::Number(42.into()).into(),
        );

        let out = expr
            .evaluate(&HashMap::new(), &HashMap::new(), &HashMap::new())
            .unwrap();
        assert_eq!(out, BigInt::from(66));
    }

    #[test]
    fn expr_nested() {
        //((1+2)*3-(4/2) = 7
        let expr = Expression::Minus(
            Expression::Times(
                Expression::Plus(
                    Terminal::Number(1.into()).into(),
                    Terminal::Number(2.into()).into(),
                )
                .into(),
                Terminal::Number(3.into()).into(),
            )
            .into(),
            Expression::Divide(
                Terminal::Number(4.into()).into(),
                Terminal::Number(2.into()).into(),
            )
            .into(),
        );
        let out = expr
            .evaluate(&HashMap::new(), &HashMap::new(), &HashMap::new())
            .unwrap();
        assert_eq!(out, BigInt::from(7));
    }

    #[test]
    fn expr_with_label() {
        // foo + 1 = 42
        let expr = Expression::Plus(
            Terminal::Label(String::from("foo")).into(),
            Terminal::Number(1.into()).into(),
        );

        let mut labels = HashMap::new();
        labels.insert("foo".into(), Some(41));

        let out = expr
            .evaluate(&labels, &HashMap::new(), &HashMap::new())
            .unwrap();
        assert_eq!(out, BigInt::from(42));
    }

    #[test]
    fn expr_unknown_label() {
        let expr = Expression::Plus(
            Terminal::Label(String::from("foo")).into(),
            Terminal::Number(1.into()).into(),
        );

        let err = expr
            .evaluate(&HashMap::new(), &HashMap::new(), &HashMap::new())
            .unwrap_err();
        assert_matches!(err, Error::UnknownLabel { label, .. } if label == "foo");

        let expr = Expression::Plus(
            Terminal::Label(String::from("foo")).into(),
            Terminal::Number(1.into()).into(),
        );

        let mut labels = HashMap::new();
        labels.insert("foo".into(), None);

        let err = expr
            .evaluate(&labels, &HashMap::new(), &HashMap::new())
            .unwrap_err();
        assert_matches!(err, Error::UnknownLabel { label, .. } if label == "foo");
    }
}
