use pest::error::Error;

use snafu::{Backtrace, IntoError, Snafu};

use super::Rule;

/// Type for errors that may arise while parsing assembly source code.
#[derive(Snafu, Debug)]
#[snafu(visibility = "pub(super)")]
#[non_exhaustive]
pub enum ParseError {
    /// An immediate value was too large for the given opcode.
    #[snafu(display("an immediate value was too large for the given opcode"))]
    #[non_exhaustive]
    ImmediateTooLarge {
        /// The location of the error.
        backtrace: Backtrace,
    },

    /// The source code did not lex correctly.
    #[snafu(display("lexing failed: {}", source))]
    #[non_exhaustive]
    Lexer {
        /// The underlying source of this error.
        source: Box<dyn std::error::Error>,

        /// The location of this error.
        backtrace: Backtrace,
    },

    /// A required argument for a macro was missing.
    #[snafu(display("expected {} argument(s) but only got {}", expected, got))]
    #[non_exhaustive]
    MissingArgument {
        /// How many arguments, total, were expected.
        expected: usize,

        /// How many arguments were provided.
        got: usize,

        /// Location of the error.
        backtrace: Backtrace,
    },

    /// Too many arguments were provided to a macro.
    #[snafu(display("extra argument (expected {})", expected))]
    #[non_exhaustive]
    ExtraArgument {
        /// How many arguments, total, were expected.
        expected: usize,

        /// Location of the error.
        backtrace: Backtrace,
    },

    /// An argument provided to a macro was of the wrong type.
    #[snafu(display("incorrect argument type"))]
    #[non_exhaustive]
    ArgumentType {
        /// The location of the error.
        backtrace: Backtrace,
    },
}

impl From<Error<Rule>> for ParseError {
    fn from(err: Error<Rule>) -> Self {
        Lexer {}.into_error(Box::new(err))
    }
}
