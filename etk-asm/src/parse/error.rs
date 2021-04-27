use pest::error::Error;

use snafu::{Backtrace, IntoError, Snafu};

use std::io;
use std::path::PathBuf;

use super::Rule;

#[derive(Snafu, Debug)]
#[snafu(visibility = "pub(crate)")]
#[non_exhaustive]
pub enum ParseError {
    #[snafu(display("an immediate value was too large for the given opcode"))]
    ImmediateTooLarge { backtrace: Backtrace },

    #[snafu(display("lexing failed: {}", source))]
    Lexer {
        source: Box<dyn std::error::Error>,
        backtrace: Backtrace,
    },

    #[snafu(display("i/o failed on `{}`: {}", path.to_string_lossy(), source))]
    Io {
        path: PathBuf,
        source: io::Error,
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
