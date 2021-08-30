use snafu::OptionExt;
use std::collections::HashMap;

mod error {
    use snafu::{Backtrace, Snafu};

    /// Errors that can occur while assembling instructions.
    #[derive(Snafu, Debug)]
    #[non_exhaustive]
    #[snafu(visibility = "pub(super)")]
    #[allow(unreachable_pub)]
    pub enum Error {
        /// The error that can arise when evaluate an expression without all label offsets being known.
        #[snafu(display("mising label: {}", label))]
        #[non_exhaustive]
        UndeclaredLabel { label: String, backtrace: Backtrace },

        /// The error that can arise when the label is known, but hasn't resolved a concrete
        /// address.
        #[snafu(display("unresolved label: {}", label))]
        #[non_exhaustive]
        UnresolvedLabel { label: String, backtrace: Backtrace },
    }
}

use self::error::Error;

/// An infix mathematical expression.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Expression {
    /// A recusrive expression.
    Expression(Box<Self>),

    /// A integer value.
    Number(i128),

    /// A label.
    Label(String),

    /// An addition operation.
    Plus(Box<Self>, Box<Self>),

    /// A subtraction operation.
    Minus(Box<Self>, Box<Self>),

    /// A multiplication operation.
    Times(Box<Self>, Box<Self>),

    /// A division operation.
    Divide(Box<Self>, Box<Self>),
}

impl Expression {
    /// Evaluates the expression, substituting resolved label address for labels.
    fn evaluate(&self, labels: &HashMap<String, Option<u32>>) -> Result<i128, Error> {
        let ret = match self {
            Self::Expression(e) => e.evaluate(labels)?,
            Self::Number(n) => *n,
            Self::Label(label) => labels
                .get(label)
                .context(error::UndeclaredLabel { label })?
                .context(error::UnresolvedLabel { label })?
                as i128,
            Self::Plus(rhs, lhs) => rhs.evaluate(labels)? + lhs.evaluate(labels)?,
            Self::Minus(rhs, lhs) => rhs.evaluate(labels)? - lhs.evaluate(labels)?,
            Self::Times(rhs, lhs) => rhs.evaluate(labels)? * lhs.evaluate(labels)?,
            Self::Divide(rhs, lhs) => rhs.evaluate(labels)? / lhs.evaluate(labels)?,
        };
        Ok(ret)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use assert_matches::assert_matches;

    #[test]
    fn expr_simple() {
        // 24 + 42 = 66
        let expr = Expression::Plus(
            Box::new(Expression::Number(24)),
            Box::new(Expression::Number(42)),
        );

        assert_eq!(expr.evaluate(&HashMap::new()).unwrap(), 66);
    }

    #[test]
    fn expr_nested() {
        //((1+2)*3-(4/2) = 7
        let expr = Expression::Minus(
            Box::new(Expression::Times(
                Box::new(Expression::Plus(
                    Box::new(Expression::Number(1)),
                    Box::new(Expression::Number(2)),
                )),
                Box::new(Expression::Number(3)),
            )),
            Box::new(Expression::Divide(
                Box::new(Expression::Number(4)),
                Box::new(Expression::Number(2)),
            )),
        );
        assert_eq!(expr.evaluate(&HashMap::new()).unwrap(), 7);
    }

    #[test]
    fn expr_with_label() {
        // foo + 1 = 42
        let expr = Expression::Plus(
            Box::new(Expression::Label("foo".into())),
            Box::new(Expression::Number(1)),
        );

        let mut labels = HashMap::new();
        labels.insert("foo".into(), Some(41));

        assert_eq!(expr.evaluate(&labels).unwrap(), 42);
    }

    #[test]
    fn expr_undeclared_label() {
        let expr = Expression::Plus(
            Box::new(Expression::Label("foo".into())),
            Box::new(Expression::Number(1)),
        );

        let err = expr.evaluate(&HashMap::new()).unwrap_err();
        assert_matches!(err, Error::UndeclaredLabel { label, .. } if label == "foo");
    }

    #[test]
    fn expr_unresolved_label() {
        let expr = Expression::Plus(
            Box::new(Expression::Label("foo".into())),
            Box::new(Expression::Number(1)),
        );

        let mut labels = HashMap::new();
        labels.insert("foo".into(), None);

        let err = expr.evaluate(&labels).unwrap_err();
        assert_matches!(err, Error::UnresolvedLabel { label, .. } if label == "foo");
    }
}
