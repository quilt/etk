use super::args::Signature;
use super::error::{EmptyRangeHardfork, OverlappingRangeHardfork, ParseError};
use super::expression;
use super::parser::Rule;
use crate::ast::Node;
use crate::ops::{
    AbstractOp, Expression, ExpressionMacroDefinition, ExpressionMacroInvocation,
    InstructionMacroDefinition, InstructionMacroInvocation,
};
use crate::parse::error::{ExceededRangeHardfork, InvalidHardfork, InvalidRangeHardfork};
use etk_ops::{HardFork, HardForkDirective, OperatorDirective};
use pest::iterators::Pair;
use std::path::PathBuf;

pub(crate) fn parse(pair: Pair<Rule>, hardfork: HardFork) -> Result<AbstractOp, ParseError> {
    let mut pairs = pair.into_inner();
    let pair = pairs.next().unwrap();

    match pair.as_rule() {
        Rule::instruction_macro_definition => parse_instruction_macro_defn(pair, hardfork),
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
        Rule::hardfork => {
            let mut directives = Vec::new();
            for inner in pair.into_inner() {
                let mut directive = inner.into_inner();
                let operator = match directive.next() {
                    Some(operator) => {
                        let operator = operator.as_str().into();
                        Some(operator)
                    }
                    None => None,
                };

                // Tried moving this to into() but can't manage invalid hardforks.
                let hardforkstr = directive.next().unwrap().as_str();
                let hardfork = match hardforkstr {
                    "london" => HardFork::London,
                    "shanghai" => HardFork::Shanghai,
                    "cancun" => HardFork::Cancun,
                    _ => {
                        return InvalidHardfork {
                            hardfork: hardforkstr,
                        }
                        .fail()
                    }
                };

                directives.push(HardForkDirective {
                    operator,
                    hardfork: hardfork,
                });
                if directives.len() > 2 {
                    return ExceededRangeHardfork {
                        parsed: directives.len(),
                    }
                    .fail();
                }
            }

            directives.reverse();
            hardfork_in_valid_range(&directives)?;
            let tuple = (directives.pop().unwrap(), directives.pop());
            Node::HardforkMacro(tuple)
        }
        _ => unreachable!(),
    };

    Ok(node)
}

fn hardfork_in_valid_range(directives: &[HardForkDirective]) -> Result<(), ParseError> {
    if directives.len() == 1 {
        return Ok(());
    }

    let mut decresing_bound: Option<HardForkDirective> = None;
    let mut incresing_bound: Option<HardForkDirective> = None;

    for directive in directives {
        match directive.operator {
            Some(OperatorDirective::LessThan) | Some(OperatorDirective::LessThanOrEqual) => {
                match decresing_bound {
                    Some(_) => {
                        return OverlappingRangeHardfork {
                            directive0: directives.get(0),
                            directive1: directives.get(1),
                        }
                        .fail();
                    }
                    None => {
                        decresing_bound = Some(directive.clone());
                    }
                }
            }
            Some(OperatorDirective::GreaterThan) | Some(OperatorDirective::GreaterThanOrEqual) => {
                match incresing_bound {
                    Some(_) => {
                        return OverlappingRangeHardfork {
                            directive0: directives.get(0),
                            directive1: directives.get(1),
                        }
                        .fail();
                    }
                    None => {
                        incresing_bound = Some(directive.clone());
                    }
                }
            }
            None => {
                return InvalidRangeHardfork {
                    directive0: directives.get(0),
                    directive1: directives.get(1),
                }
                .fail();
            }
        }
    }

    if incresing_bound.unwrap().hardfork > decresing_bound.unwrap().hardfork {
        return EmptyRangeHardfork {
            directive0: directives.get(0),
            directive1: directives.get(1),
        }
        .fail();
    }

    Ok(())
}

fn parse_instruction_macro_defn(
    pair: Pair<Rule>,
    hardfork: HardFork,
) -> Result<AbstractOp, ParseError> {
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
            contents.push(super::parse_abstract_op(pair, hardfork.clone())?);
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
