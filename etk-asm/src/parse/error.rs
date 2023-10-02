use std::path::PathBuf;

use pest::error::Error;

use snafu::{Backtrace, IntoError, Snafu};

use super::Rule;

/// Type for errors that may arise while parsing assembly source code.
#[derive(Snafu, Debug)]
#[snafu(context(suffix(false)), visibility(pub(super)))]
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
    #[snafu(display("lexing failed"))]
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

    /// An argument provided to a macro was of the wrong type.
    #[snafu(display("File {} does not exist", path.to_string_lossy()))]
    #[non_exhaustive]
    FileNotFound {
        /// Path to the offending file.
        path: PathBuf,

        /// The location of the error.
        backtrace: Backtrace,
    },

    /// An included fail failed to parse as hexadecimal.
    #[snafu(display("included file `{}` is invalid hex: {}", path.to_string_lossy(), source))]
    #[non_exhaustive]
    InvalidHex {
        /// Path to the offending file.
        path: PathBuf,

        /// The underlying source of this error.
        source: Box<dyn std::error::Error>,

        /// The location of the error.
        backtrace: Backtrace,
    },

    /// A recursion limit was reached while including or importing a file.
    #[snafu(display("too many levels of recursion/includes"))]
    #[non_exhaustive]
    RecursionLimit {
        /// The location of the error.
        backtrace: Backtrace,
    },
}

impl From<Error<Rule>> for ParseError {
    fn from(err: Error<Rule>) -> Self {
        Lexer {}.into_error(Box::new(err))
    }
}
