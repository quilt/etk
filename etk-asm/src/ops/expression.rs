use super::macros::{ExpressionMacroInvocation, MacroDefinition};
use super::{Labels, Macros, Variables};
use num_bigint::BigInt;
use snafu::OptionExt;
use snafu::{Backtrace, Snafu};
use std::collections::HashMap;
use std::fmt::{self, Debug};

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
            Terminal::Variable(v) => write!(f, r#"Terminal::Variable({})"#, v),
        }
    }
}

impl fmt::Display for Terminal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Terminal::Label(l) => write!(f, r#"Label({})"#, l),
            Terminal::Number(n) => write!(f, r#"{}"#, n),
            Terminal::Variable(v) => write!(f, r#"Variable({})"#, v),
        }
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

#[cfg(test)]
mod tests {
    use super::*;
    use assert_matches::assert_matches;

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
