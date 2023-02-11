use super::macros::{ExpressionMacroInvocation, MacroDefinition};
use num_bigint::{BigInt, Sign};
use snafu::OptionExt;
use snafu::{Backtrace, Snafu};
use std::collections::HashMap;
use std::fmt::{self, Debug};

/// An error that arises when an expression cannot be evaluated.
#[derive(Snafu, Debug)]
#[snafu(context(suffix(false)), visibility(pub))]
pub enum Error {
    #[snafu(display("unknown label `{}`", label))]
    #[non_exhaustive]
    UnknownLabel { label: String, backtrace: Backtrace },

    #[snafu(display("unknown macro `{}`", name))]
    #[non_exhaustive]
    UnknownMacro { name: String, backtrace: Backtrace },

    #[snafu(display("undefined macro variable `{}`", name))]
    #[non_exhaustive]
    UndefinedVariable { name: String, backtrace: Backtrace },
}

type LabelsMap = HashMap<String, Option<usize>>;
type VariablesMap = HashMap<String, Expression>;
type MacrosMap = HashMap<String, MacroDefinition>;

/// Evaluation context for `Expression`.
#[derive(Clone, Copy, Debug, Default)]
pub struct Context<'a> {
    labels: Option<&'a LabelsMap>,
    macros: Option<&'a MacrosMap>,
    variables: Option<&'a VariablesMap>,
}

impl<'a> Context<'a> {
    /// Looks up a label in the current context.
    pub fn get_label(&self, key: &str) -> Option<&Option<usize>> {
        match self.labels {
            Some(labels) => labels.get(key),
            None => None,
        }
    }

    /// Looks up a macro in the current context.
    pub fn get_macro(&self, key: &str) -> Option<&MacroDefinition> {
        match self.macros {
            Some(macros) => macros.get(key),
            None => None,
        }
    }

    /// Looks up a variable in the current context.
    pub fn get_variable(&self, key: &str) -> Option<&Expression> {
        match self.variables {
            Some(variables) => variables.get(key),
            None => None,
        }
    }
}

impl<'a> From<&'a LabelsMap> for Context<'a> {
    fn from(labels: &'a LabelsMap) -> Self {
        Self {
            labels: Some(labels),
            macros: None,
            variables: None,
        }
    }
}

impl<'a> From<(&'a LabelsMap, &'a MacrosMap)> for Context<'a> {
    fn from(x: (&'a LabelsMap, &'a MacrosMap)) -> Self {
        Self {
            labels: Some(x.0),
            macros: Some(x.1),
            variables: None,
        }
    }
}

impl<'a> From<(&'a LabelsMap, &'a MacrosMap, &'a VariablesMap)> for Context<'a> {
    fn from(x: (&'a LabelsMap, &'a MacrosMap, &'a VariablesMap)) -> Self {
        Self {
            labels: Some(x.0),
            macros: Some(x.1),
            variables: Some(x.2),
        }
    }
}

/// A mathematical expression.
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

    /// A signed to unsigned integer conversion operation.
    Uint(Box<Self>, usize),
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
            Expression::Uint(s, bits) => {
                write!(f, r#"Expression::Uint{}({:?})"#, bits, s)
            }
        }
    }
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expression::Expression(s) => write!(f, r#"({})"#, s),
            Expression::Macro(m) => write!(f, r#"{}"#, m),
            Expression::Terminal(t) => write!(f, r#"{}"#, t),
            Expression::Plus(lhs, rhs) => write!(f, r#"{}+{}"#, lhs, rhs),
            Expression::Minus(lhs, rhs) => write!(f, r#"{}-{}"#, lhs, rhs),
            Expression::Times(lhs, rhs) => write!(f, r#"{}*{}"#, lhs, rhs),
            Expression::Divide(lhs, rhs) => write!(f, r#"{}/{}"#, lhs, rhs),
            Expression::Uint(s, bits) => write!(f, r#"uint{}({})"#, bits, s),
        }
    }
}

/// A terminal value in an expression.
#[derive(Clone, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Terminal {
    /// An integer value.
    Number(BigInt),

    /// A label.
    Label(String),

    /// A macro variable.
    Variable(String),
}

impl Terminal {
    /// Evaluates a terminal into an integer value.
    pub fn eval(&self) -> Result<BigInt, Error> {
        self.eval_with_context(Context::default())
    }

    /// Evaluates a terminal into an integer value, with a given given `Context`..
    pub fn eval_with_context(&self, ctx: Context) -> Result<BigInt, Error> {
        let ret = match self {
            Terminal::Number(n) => n.clone(),
            Terminal::Label(label) => ctx
                .get_label(label)
                .context(UnknownLabel { label })?
                .context(UnknownLabel { label })?
                .into(),
            Terminal::Variable(name) => ctx
                .get_variable(name)
                .context(UndefinedVariable { name })?
                .eval_with_context(ctx)?,
        };

        Ok(ret)
    }
}

impl Expression {
    /// Returns the constant value of the expression.
    pub fn eval(&self) -> Result<BigInt, Error> {
        self.eval_with_context(Context::default())
    }

    /// Evaluates the expression given a certain `Context`.
    pub fn eval_with_context(&self, ctx: Context) -> Result<BigInt, Error> {
        fn eval(e: &Expression, ctx: Context) -> Result<BigInt, Error> {
            let ret = match e {
                Expression::Expression(expr) => eval(expr, ctx)?,
                Expression::Macro(invc) => {
                    let defn = ctx.get_macro(&invc.name).context(UnknownMacro {
                        name: invc.name.clone(),
                    })?;

                    let vars = defn
                        .parameters()
                        .iter()
                        .cloned()
                        .zip(invc.parameters.iter().cloned())
                        .collect();

                    let mut ctx = ctx;
                    ctx.variables = Some(&vars);

                    defn.unwrap_expression()
                        .content
                        .tree
                        .eval_with_context(ctx)?
                }
                Expression::Terminal(term) => term.eval_with_context(ctx)?,
                Expression::Plus(lhs, rhs) => eval(lhs, ctx)? + eval(rhs, ctx)?,
                Expression::Minus(lhs, rhs) => eval(lhs, ctx)? - eval(rhs, ctx)?,
                Expression::Times(lhs, rhs) => eval(lhs, ctx)? * eval(rhs, ctx)?,
                Expression::Divide(lhs, rhs) => eval(lhs, ctx)? / eval(rhs, ctx)?,
                Expression::Uint(expr, bits) => {
                    let eval = eval(expr, ctx)?;
                    match eval.sign() {
                        Sign::Minus => {
                            let mut bytes = eval.to_signed_bytes_be();
                            bytes.resize(bits / 8, 0xff);
                            BigInt::from_bytes_le(Sign::Plus, &bytes)
                        }
                        _ => eval,
                    }
                }
            };

            Ok(ret)
        }

        // TODO error if top level receives negative value.
        eval(self, ctx)
    }

    /// Returns a list of all labels used in the expression.
    pub fn labels(&self, macros: &MacrosMap) -> Result<Vec<String>, Error> {
        fn dfs(x: &Expression, m: &MacrosMap) -> Result<Vec<String>, Error> {
            match x {
                Expression::Expression(e) | Expression::Uint(e, _) => dfs(e, m),
                Expression::Macro(macro_invocation) => m
                    .get(&macro_invocation.name)
                    .context(UnknownMacro {
                        name: macro_invocation.name.clone(),
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

    /// Replaces all instances of `old` with `new` in the expression.
    pub fn replace_label(&mut self, old: &str, new: &str) {
        fn dfs(x: &mut Expression, old: &str, new: &str) {
            match x {
                Expression::Expression(e) | Expression::Uint(e, _) => dfs(e, new, old),
                Expression::Terminal(Terminal::Label(ref mut label)) => {
                    if *label == old {
                        *label = new.to_string();
                    }
                }
                Expression::Plus(lhs, rhs)
                | Expression::Minus(lhs, rhs)
                | Expression::Times(lhs, rhs)
                | Expression::Divide(lhs, rhs) => {
                    dfs(lhs, new, old);
                    dfs(rhs, new, old);
                }
                Expression::Macro(_) | Expression::Terminal(_) => (),
            }
        }

        dfs(self, old, new)
    }

    /// Replaces all instances of `var` with `expr` in the expression.
    pub fn fill_variable(&mut self, var: &str, expr: &Expression) {
        fn dfs(x: &mut Expression, var: &str, expr: &Expression) {
            match x {
                Expression::Terminal(Terminal::Variable(name)) => {
                    if var == name {
                        *x = expr.clone();
                    }
                }
                Expression::Expression(e) | Expression::Uint(e, _) => dfs(e, var, expr),
                Expression::Plus(lhs, rhs)
                | Expression::Minus(lhs, rhs)
                | Expression::Times(lhs, rhs)
                | Expression::Divide(lhs, rhs) => {
                    dfs(lhs, var, expr);
                    dfs(rhs, var, expr);
                }
                Expression::Macro(_) | Expression::Terminal(_) => (),
            }
        }

        dfs(self, var, expr)
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
        let expr = Expression::Plus(24.into(), 42.into());
        let out = expr.eval().unwrap();
        assert_eq!(out, BigInt::from(66));
    }

    #[test]
    fn expr_nested() {
        //((1+2)*3-(4/2) = 7
        let expr = Expression::Minus(
            Expression::Times(Expression::Plus(1.into(), 2.into()).into(), 3.into()).into(),
            Expression::Divide(4.into(), 2.into()).into(),
        );
        let out = expr.eval().unwrap();
        assert_eq!(out, BigInt::from(7));
    }

    #[test]
    fn expr_with_label() {
        // foo + 1 = 42
        let expr = Expression::Plus(Terminal::Label(String::from("foo")).into(), 1.into());
        let labels: HashMap<_, _> = vec![("foo".to_string(), Some(41))].into_iter().collect();
        let out = expr.eval_with_context(Context::from(&labels)).unwrap();
        assert_eq!(out, BigInt::from(42));
    }

    #[test]
    fn expr_unknown_label() {
        // missing label
        let expr = Expression::Plus(Terminal::Label(String::from("foo")).into(), 1.into());
        let err = expr.eval().unwrap_err();
        assert_matches!(err, Error::UnknownLabel { label, .. } if label == "foo");

        // label w/o defined address
        let expr = Expression::Plus(Terminal::Label(String::from("foo")).into(), 1.into());
        let labels: HashMap<_, _> = vec![("foo".to_string(), None)].into_iter().collect();
        let err = expr.eval_with_context(Context::from(&labels)).unwrap_err();
        assert_matches!(err, Error::UnknownLabel { label, .. } if label == "foo");
    }
}
