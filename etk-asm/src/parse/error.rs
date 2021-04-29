use pest::error::Error;

use snafu::{Backtrace, IntoError, Snafu};

use super::Rule;

#[derive(Snafu, Debug)]
#[snafu(visibility = "pub(super)")]
#[non_exhaustive]
pub enum ParseError {
    #[snafu(display("an immediate value was too large for the given opcode"))]
    ImmediateTooLarge { backtrace: Backtrace },

    #[snafu(display("lexing failed: {}", source))]
    Lexer {
        source: Box<dyn std::error::Error>,
        backtrace: Backtrace,
    },

    #[snafu(display("expected {} argument(s) but only got {}", expected, got))]
    MissingArgument {
        expected: usize,
        got: usize,
        backtrace: Backtrace,
    },

    #[snafu(display("extra argument (expected {})", expected))]
    ExtraArgument {
        expected: usize,
        backtrace: Backtrace,
    },

    #[snafu(display("incorrect argument type"))]
    ArgumentType { backtrace: Backtrace },
}

impl From<Error<Rule>> for ParseError {
    fn from(err: Error<Rule>) -> Self {
        Lexer {}.into_error(Box::new(err))
    }
}
