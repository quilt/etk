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

        match pair.as_rule() {
            Rule::expression => climber.climb(pair.into_inner(), primary, infix),
            Rule::binary => BigInt::from_radix_be(
                Sign::Plus,
                hex::decode(&pair.as_str()[2..]).unwrap().as_ref(),
                2,
            )
            .unwrap()
            .into(),
            Rule::decimal | Rule::int => BigInt::from_radix_be(
                Sign::Plus,
                hex::decode(&pair.as_str()[2..]).unwrap().as_ref(),
                10,
            )
            .unwrap()
            .into(),
            Rule::octal => BigInt::from_radix_be(
                Sign::Plus,
                hex::decode(&pair.as_str()[2..]).unwrap().as_ref(),
                8,
            )
            .unwrap()
            .into(),
            Rule::hex => Terminal::Bytes(hex::decode(pair.as_str().to_string()).unwrap()).into(),
            Rule::label => Terminal::Label(pair.as_str().to_string()).into(),
            Rule::selector => {
                let raw = pair.into_inner().next().unwrap().as_str();
                let mut hasher = Keccak256::new();
                hasher.update(raw.as_bytes());
                Terminal::Bytes(hasher.finalize()[0..4].to_vec()).into()
            }
            Rule::expression_macro => macros::parse_expression_macro(pair).unwrap(),
            Rule::instruction_macro_variable => {
                let variable = pair.as_str().strip_prefix('$').unwrap();
                Terminal::Variable(variable.to_string()).into()
            }
            _ => unreachable!(),
        }
    }

    Ok(consume(pair, &climber))
}
