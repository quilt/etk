use super::args::Signature;
use super::error::ParseError;
use super::expression;
use super::parser::Rule;
use crate::ast::Node;
use crate::ops::{
    AbstractOp, Expression, ExpressionMacroDefinition, ExpressionMacroInvocation,
    InstructionMacroDefinition, InstructionMacroInvocation,
};
use crate::parse::error;
use pest::iterators::Pair;
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

pub(crate) fn parse_builtin(pair: Pair<Rule>) -> Result<Node, ParseError> {
    let mut pairs = pair.into_inner();
    let pair = pairs.next().unwrap();
    assert!(pairs.next().is_none());
    let rule = pair.as_rule();

    let node = match rule {
        Rule::import => {
            let args = <(PathBuf,)>::parse_arguments(pair.into_inner())?;
            Node::Import(args.0)
        }
        Rule::include => {
            let args = <(PathBuf,)>::parse_arguments(pair.into_inner())?;
            Node::Include(args.0)
        }
        Rule::include_hex => {
            let args = <(PathBuf,)>::parse_arguments(pair.into_inner())?;
            Node::IncludeHex(args.0)
        }
        Rule::push_macro => {
            let expr = expression::parse(pair.into_inner().next().unwrap())?;
            Node::Op(AbstractOp::Push(expr.into()))
        }
        Rule::inline_hex => {
            let args = <(String,)>::parse_arguments(pair.into_inner())?;
            let bytes = hex::decode(args.0).map_err(|e| e.to_string());

            match bytes {
                Ok(bytes) => Node::Raw(bytes),
                Err(e) => {
                    return error::InvalidHex { value: e }.fail();
                }
            }
        }
        Rule::inline_string => {
            let args = <(String,)>::parse_arguments(pair.into_inner())?;
            let raw_string = args.0;

            let bytes = raw_string.as_bytes().to_vec();

            Node::Raw(bytes)
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
