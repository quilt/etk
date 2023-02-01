//! Utilities for printing errors.

use snafu::{Backtrace, ErrorCompat};

use std::fmt;

/// A wrapper which prints a [`snafu::ErrorCompat`], plus its backtraces if they
/// exist.
#[derive(Debug)]
pub struct WithSources<E>(pub E);

impl<E> fmt::Display for WithSources<E>
where
    E: ErrorCompat + std::error::Error,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "Error: {}", self.0)?;

        let mut current = self.0.source();

        while let Some(e) = current.take() {
            writeln!(f, "Caused by: {e}")?;
            current = e.source();
        }

        if let Some(backtrace) = ErrorCompat::backtrace(&self.0) {
            // XXX: hack to determine if snafu's backtraces are enabled.
            if std::mem::size_of::<Backtrace>() > 0 {
                writeln!(f, "Backtrace:\n{backtrace}")?;
            }
        }

        Ok(())
    }
}
