use super::error::ParseError;
use super::macros;
use super::parser::Rule;
use crate::ops::{Expression, Terminal};
use num_bigint::{BigInt, Sign};
use pest::{
    iterators::Pair,
    prec_climber::{Assoc, Operator, PrecClimber},
};
use sha3::{Digest, Keccak256};

pub(crate) fn parse(pair: Pair<Rule>) -> Result<Expression, ParseError> {
    let climber = PrecClimber::new(vec![
        Operator::new(Rule::plus, Assoc::Left) | Operator::new(Rule::minus, Assoc::Left),
        Operator::new(Rule::times, Assoc::Left) | Operator::new(Rule::divide, Assoc::Left),
    ]);

    fn consume(pair: Pair<Rule>, climber: &PrecClimber<Rule>) -> Expression {
        let primary = |pair| consume(pair, climber);
        let infix = |lhs: Expression, op: Pair<Rule>, rhs: Expression| match op.as_rule() {
            Rule::plus => Expression::Plus(Box::new(lhs), Box::new(rhs)),
            Rule::minus => Expression::Minus(Box::new(lhs), Box::new(rhs)),
            Rule::times => Expression::Times(Box::new(lhs), Box::new(rhs)),
            Rule::divide => Expression::Divide(Box::new(lhs), Box::new(rhs)),
            _ => unreachable!(),
        };

        let txt = pair.as_str();

        match pair.as_rule() {
            Rule::expression => climber.climb(pair.into_inner(), primary, infix),
            Rule::binary => parse_radix_str(&txt[2..], 2),
            Rule::octal => parse_radix_str(&txt[2..], 8),
            Rule::hex => parse_radix_str(&txt[2..], 16),
            Rule::decimal => parse_radix_str(txt, 10),
            Rule::negative_decimal => {
                let expr = parse_radix_str(&txt[1..], 10);
                BigInt::from_radix_be(Sign::Minus, &expr.eval().unwrap().to_bytes_be().1, 10)
                    .unwrap()
                    .into()
            }
            Rule::label => Terminal::Label(txt.to_string()).into(),
            Rule::selector => parse_selector(pair),
            Rule::expression_macro => macros::parse_expression_macro(pair).unwrap(),
            Rule::instruction_macro_variable => {
                let variable = txt.strip_prefix('$').unwrap();
                Terminal::Variable(variable.to_string()).into()
            }
            _ => unreachable!(),
        }
    }

    Ok(consume(pair, &climber))
}

fn parse_radix_str(s: &str, radix: u32) -> Expression {
    let buf: Vec<u8> = s
        .trim()
        .to_string()
        .chars()
        .map(|c| c.to_digit(radix).unwrap() as u8)
        .collect();
    BigInt::from_radix_be(Sign::Plus, &buf, radix)
        .unwrap()
        .into()
}

fn parse_selector(pair: Pair<Rule>) -> Expression {
    let raw = pair.into_inner().next().unwrap().as_str();
    let mut hasher = Keccak256::new();
    hasher.update(raw.as_bytes());
    // TODO: return full hash
    BigInt::from_bytes_be(Sign::Plus, &hasher.finalize()[0..4]).into()
}
