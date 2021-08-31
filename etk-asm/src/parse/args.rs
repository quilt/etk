use pest::iterators::{Pair, Pairs};

use snafu::{ensure, OptionExt};

use std::path::PathBuf;

use super::{error, ParseError, Rule};

pub(super) trait FromPair: Sized {
    fn from_pair(pair: Pair<Rule>) -> Result<Self, ParseError>;
}

impl FromPair for PathBuf {
    fn from_pair(pair: Pair<Rule>) -> Result<Self, ParseError> {
        ensure!(pair.as_rule() == Rule::string, error::ArgumentType);

        let txt = pair.as_str();
        if txt.contains('\\') {
            // TODO
            panic!("backslashes in paths aren't implemented yet.");
        }

        Ok(txt[1..txt.len() - 1].into())
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub(super) struct Label(pub(super) String);

impl FromPair for Label {
    fn from_pair(pair: Pair<Rule>) -> Result<Self, ParseError> {
        let txt = pair.as_str().trim();
        Ok(Self(txt.into()))
    }
}

pub(super) trait Signature {
    type Output;
    fn parse_arguments(pairs: Pairs<Rule>) -> Result<Self::Output, ParseError>;
}

fn arg<T>(pairs: &mut Pairs<Rule>, expected: usize, got: &mut usize) -> Result<T, ParseError>
where
    T: FromPair,
{
    let pair = pairs.next().context(error::MissingArgument {
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
            Some(_) => error::ExtraArgument { expected: 0usize }.fail(),
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
            Some(_) => error::ExtraArgument { expected }.fail(),
            None => Ok(result),
        }
    }
}
