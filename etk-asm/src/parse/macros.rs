use super::args::Signature;
use super::error::ParseError;
use super::expression;
use super::parser::Rule;
use crate::ast::Node;
use crate::ingest::Root;
use crate::ops::{
    AbstractOp, Expression, ExpressionMacroDefinition, ExpressionMacroInvocation,
    InstructionMacroDefinition, InstructionMacroInvocation,
};
use crate::parse::{error, parse_asm};
use pest::iterators::Pair;
use snafu::{ensure, IntoError};
use std::path::PathBuf;

pub(crate) fn parse(pair: Pair<Rule>) -> Result<AbstractOp, ParseError> {
    let mut pairs = pair.into_inner();
    let pair = pairs.next().unwrap();

    match pair.as_rule() {
        Rule::instruction_macro_definition => parse_instruction_macro_defn(pair),
        Rule::instruction_macro => parse_instruction_macro(pair),
        Rule::expression_macro_definition => parse_expression_macro_defn(pair),
        _ => unreachable!(),
    }
}

pub(crate) fn parse_builtin(
    root: Root,
    pair: Pair<Rule>,
    mut depth: u16,
) -> Result<Vec<Node>, ParseError> {
    ensure!(depth <= 255, error::RecursionLimit);
    let mut pairs = pair.into_inner();
    let pair = pairs.next().unwrap();
    assert!(pairs.next().is_none());
    let rule = pair.as_rule();

    depth += 1;

    let node = match rule {
        Rule::import => {
            let args = <(PathBuf,)>::parse_arguments(pair.into_inner())?;
            let new_path = root.canonicalized.join(args.0.clone());
            let root = Root::new(new_path.clone()).unwrap();
            let path = new_path.into_os_string().into_string().unwrap();
            let code_str = &std::fs::read_to_string(&path);
            let nodes = match code_str {
                Ok(code) => parse_asm(root.clone(), code, depth)?,
                Err(_) => return error::FileNotFound { path: args.0 }.fail(),
            };
            nodes
        }
        Rule::include => {
            let args = <(PathBuf,)>::parse_arguments(pair.into_inner())?;
            let new_path = root.canonicalized.join(args.0.clone());
            let root = Root::new(new_path.clone()).unwrap();
            let path = new_path.into_os_string().into_string().unwrap();
            let code_str = &std::fs::read_to_string(&path);
            let nodes = match code_str {
                Ok(code) => parse_asm(root.clone(), code, depth)?,
                Err(_) => return error::FileNotFound { path: args.0 }.fail(),
            };
            vec![Node::Include(nodes)]
        }
        Rule::include_hex => {
            let args = <(PathBuf,)>::parse_arguments(pair.into_inner())?;
            let file = &std::fs::read_to_string(&args.0);

            let raw = match file {
                Ok(value) => hex::decode(value.trim()),
                Err(_) => return error::FileNotFound { path: args.0 }.fail(),
            };

            match raw {
                Ok(values) => vec![Node::IncludeHex(values)],
                Err(e) => return Err(error::InvalidHex { path: args.0 }.into_error(Box::new(e))),
            }
            // TODO Check this error handling
        }
        Rule::push_macro => {
            let expr = expression::parse(pair.into_inner().next().unwrap())?;
            vec![Node::Op(AbstractOp::Push(expr.into()))]
        }
        _ => unreachable!(),
    };

    Ok(node)
}

fn parse_instruction_macro_defn(pair: Pair<Rule>) -> Result<AbstractOp, ParseError> {
    let mut pairs = pair.into_inner();

    let mut macro_defn = pairs.next().unwrap().into_inner();
    let name = macro_defn.next().unwrap();

    let mut parameters = Vec::<String>::new();
    for pair in macro_defn {
        parameters.push(pair.as_str().into());
    }

    let mut contents = Vec::<AbstractOp>::new();
    for pair in pairs {
        if pair.as_rule() == Rule::push_macro {
            let expr = expression::parse(pair.into_inner().next().unwrap())?;
            contents.push(AbstractOp::Push(expr.into()));
        } else {
            contents.push(super::parse_abstract_op(pair)?);
        }
    }

    let defn = InstructionMacroDefinition {
        name: name.as_str().to_string(),
        parameters,
        contents,
    };

    Ok(defn.into())
}

fn parse_instruction_macro(pair: Pair<Rule>) -> Result<AbstractOp, ParseError> {
    let mut pairs = pair.into_inner();
    let name = pairs.next().unwrap();
    let mut parameters = Vec::<Expression>::new();
    for pair in pairs {
        let expr = expression::parse(pair)?;
        parameters.push(expr);
    }
    let invocation = InstructionMacroInvocation {
        name: name.as_str().to_string(),
        parameters,
    };

    Ok(AbstractOp::Macro(invocation))
}

fn parse_expression_macro_defn(pair: Pair<Rule>) -> Result<AbstractOp, ParseError> {
    let mut pairs = pair.into_inner();

    let mut macro_defn = pairs.next().unwrap().into_inner();
    let name = macro_defn.next().unwrap();

    let mut parameters = Vec::<String>::new();
    for pair in macro_defn {
        parameters.push(pair.as_str().into());
    }

    let defn = ExpressionMacroDefinition {
        name: name.as_str().to_string(),
        parameters,
        content: expression::parse(pairs.next().unwrap())?.into(),
    };

    Ok(defn.into())
}

pub(crate) fn parse_expression_macro(pair: Pair<Rule>) -> Result<Expression, ParseError> {
    let mut pairs = pair.into_inner();
    let name = pairs.next().unwrap();
    let mut parameters = Vec::<Expression>::new();
    for pair in pairs {
        let expr = expression::parse(pair)?;
        parameters.push(expr);
    }
    let invocation = ExpressionMacroInvocation {
        name: name.as_str().to_string(),
        parameters,
    };
    Ok(Expression::Macro(invocation))
}
