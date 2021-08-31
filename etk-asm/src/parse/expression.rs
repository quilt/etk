use super::error::ParseError;
use super::parser::Rule;
use crate::ops::Expression;
use pest::{
    iterators::Pair,
    prec_climber::{Assoc, Operator, PrecClimber},
};

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
            Rule::math_expr => climber.climb(pair.into_inner(), primary, infix),
            Rule::binary => {
                Expression::Number(i128::from_str_radix(&pair.as_str()[2..], 2).unwrap())
            }
            Rule::decimal | Rule::int => Expression::Number(str::parse(pair.as_str()).unwrap()),
            Rule::octal => {
                Expression::Number(i128::from_str_radix(&pair.as_str()[2..], 8).unwrap())
            }
            Rule::hex => Expression::Hex(pair.as_str().to_string()),
            Rule::label => Expression::Label(pair.as_str().to_string()),
            r => panic!("unsupport expression primary: {:?}, {:?}", r, pair.as_str()),
        }
    }

    Ok(consume(pair, &climber))
}
