use snafu::OptionExt;
use std::collections::HashMap;

mod error {
    use snafu::{Backtrace, Snafu};

    /// An error that arises when a label is used without being declared.
    #[derive(Snafu, Debug)]
    #[snafu(visibility = "pub(crate)")]
    pub struct UnknownLabel {
        pub label: String,
        backtrace: Backtrace,
    }
}

pub(crate) use self::error::UnknownLabel;

/// An infix mathematical expression.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Expression {
    /// A recusrive expression.
    Expression(Box<Self>),

    /// A integer value.
    Number(i128),

    /// A hex value.
    Hex(String),

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
    pub fn evaluate(
        &self,
        labels: &HashMap<String, Option<u32>>,
    ) -> Result<u128, error::UnknownLabel> {
        fn rec(
            s: &Expression,
            labels: &HashMap<String, Option<u32>>,
        ) -> Result<i128, error::UnknownLabel> {
            let ret = match s {
                Expression::Expression(e) => rec(e, labels)?,
                Expression::Number(n) => *n,
                Expression::Hex(h) => i128::from_str_radix(&h.as_str()[2..], 16).unwrap(),
                Expression::Label(label) => labels
                    .get(label)
                    .context(error::UnknownLabelContext { label })?
                    .context(error::UnknownLabelContext { label })?
                    as i128,
                Expression::Plus(rhs, lhs) => rec(rhs, labels)? + rec(lhs, labels)?,
                Expression::Minus(rhs, lhs) => rec(rhs, labels)? - rec(lhs, labels)?,
                Expression::Times(rhs, lhs) => rec(rhs, labels)? * rec(lhs, labels)?,
                Expression::Divide(rhs, lhs) => rec(rhs, labels)? / rec(lhs, labels)?,
            };
            Ok(ret)
        }
        rec(self, labels).map(|n| n as u128)
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
    fn expr_unknown_label() {
        let expr = Expression::Plus(
            Box::new(Expression::Label("foo".into())),
            Box::new(Expression::Number(1)),
        );

        let err = expr.evaluate(&HashMap::new()).unwrap_err();
        assert_matches!(err, error::UnknownLabel { label, .. } if label == "foo");

        let expr = Expression::Plus(
            Box::new(Expression::Label("foo".into())),
            Box::new(Expression::Number(1)),
        );

        let mut labels = HashMap::new();
        labels.insert("foo".into(), None);

        let err = expr.evaluate(&labels).unwrap_err();
        assert_matches!(err, error::UnknownLabel { label, .. } if label == "foo");
    }
}
