use super::args::Signature;
use super::error::ParseError;
use super::parser::Rule;
use super::{parse_immediate, parse_push};
use crate::ast::Node;
use crate::ops::{
    AbstractOp, Imm, InstructionMacroDefinition, InstructionMacroInvocation, Op, Specifier,
};
use pest::iterators::Pair;
use std::path::PathBuf;

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
            // TODO: This should accept labels, literals, or variables, not just labels.
            let imm = parse_immediate(pair.into_inner().next().unwrap(), 32)?;
            Node::Op(AbstractOp::Push(imm))
        }
        _ => unreachable!(),
    };
    Ok(node)
}

pub(crate) fn parse(pair: Pair<Rule>) -> Result<Node, ParseError> {
    let mut pairs = pair.into_inner();
    let pair = pairs.next().unwrap();

    match pair.as_rule() {
        Rule::instruction_macro_definition => parse_instruction_macro_defn(pair),
        Rule::instruction_macro => parse_instruction_macro(pair),
        rule => unreachable!("unreachable macro type: {:?}", rule),
    }
}

fn parse_instruction_macro_defn(pair: Pair<Rule>) -> Result<Node, ParseError> {
    let mut pairs = pair.into_inner();

    let mut macro_defn = pairs.next().unwrap().into_inner();
    let name = macro_defn.next().unwrap();

    let mut parameters = Vec::<String>::new();
    for pair in macro_defn {
        parameters.push(pair.as_str().into());
    }

    let mut contents = Vec::<AbstractOp>::new();
    for pair in pairs {
        match pair.as_rule() {
            Rule::label_definition => {
                let mut pair = pair.into_inner();
                let label = pair.next().unwrap();
                let txt = label.as_str();
                contents.push(AbstractOp::Label(txt.to_string()));
            }
            Rule::instruction_macro_push => {
                contents.push(parse_push(pair)?);
            }
            Rule::op => {
                let spec: Specifier = pair.as_str().parse().unwrap();
                let op = Op::new(spec).unwrap();
                let aop = AbstractOp::Op(op);
                contents.push(aop);
            }
            _ => continue,
        }
    }

    let defn = InstructionMacroDefinition {
        name: name.as_str().to_string(),
        parameters,
        contents,
    };
    Ok(AbstractOp::MacroDefinition(defn).into())
}

fn parse_instruction_macro(pair: Pair<Rule>) -> Result<Node, ParseError> {
    let mut pairs = pair.into_inner();
    let name = pairs.next().unwrap();
    let mut parameters = Vec::<Imm<Vec<u8>>>::new();
    for pair in pairs {
        let imm = parse_immediate(pair, 16)?;
        parameters.push(imm);
    }
    let invocation = InstructionMacroInvocation {
        name: name.as_str().to_string(),
        parameters,
    };
    Ok(AbstractOp::Macro(invocation).into())
}
