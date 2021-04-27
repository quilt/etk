use pest::iterators::{Pair, Pairs};

use std::path::PathBuf;

use super::{ParseError, Rule};

pub trait FromPair: Sized {
    fn from_pair(pair: Pair<Rule>) -> Result<Self, ParseError>;
}

impl FromPair for PathBuf {
    fn from_pair(pair: Pair<Rule>) -> Result<Self, ParseError> {
        if pair.as_rule() == Rule::string {
            let txt = pair.as_str();
            if txt.contains('\\') {
                // TODO
                panic!("backslashes in paths aren't implemented yet.");
            }
            Ok(txt[1..txt.len() - 1].into())
        } else {
            Err(ParseError::ArgumentType)
        }
    }
}

pub trait Signature {
    type Output;
    fn parse_arguments(pairs: Pairs<Rule>) -> Result<Self::Output, ParseError>;
}

fn arg<T>(pairs: &mut Pairs<Rule>, expected: usize, got: &mut usize) -> Result<T, ParseError>
where
    T: FromPair,
{
    let pair = pairs.next().ok_or(ParseError::MissingArgument {
        got: *got,
        expected,
    })?;
    *got += 1;
    T::from_pair(pair)
}

impl Signature for () {
    type Output = Self;

    fn parse_arguments(mut pairs: Pairs<Rule>) -> Result<Self, ParseError> {
        match pairs.next() {
            Some(_) => Err(ParseError::ExtraArgument { expected: 0 }),
            None => Ok(()),
        }
    }
}

impl<T> Signature for (T,)
where
    T: FromPair,
{
    type Output = Self;

    fn parse_arguments(mut pairs: Pairs<Rule>) -> Result<Self, ParseError> {
        let expected = 1;
        let mut got = 0;

        let result = (arg::<T>(&mut pairs, expected, &mut got)?,);

        match pairs.next() {
            Some(_) => Err(ParseError::ExtraArgument { expected }),
            None => Ok(result),
        }
    }
}
