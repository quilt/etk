//! Utilities for parsing strings.

use hex::FromHex;

use std::fmt;
use std::str::FromStr;

/// Wrapper around `T` that uses hexadecimal for `Display` and `FromStr`.
#[derive(Debug)]
pub struct Hex<T>(pub T);

/// Errors that can occur while parsing hexadecimal.
#[derive(Debug)]
pub enum FromHexError<E> {
    /// The required `0x` prefix was not found.
    Prefix,

    /// Parsing the hexadecimal string failed.
    Hex(E),
}

impl<E> std::error::Error for FromHexError<E>
where
    E: 'static + std::error::Error,
{
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            FromHexError::Prefix => None,
            FromHexError::Hex(ref e) => Some(e),
        }
    }
}

impl<E> fmt::Display for FromHexError<E>
where
    E: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            FromHexError::Prefix => write!(f, "missing 0x prefix"),
            FromHexError::Hex(e) => write!(f, "{}", e),
        }
    }
}

impl<T> FromStr for Hex<T>
where
    T: FromHex,
{
    type Err = FromHexError<<T as FromHex>::Error>;

    fn from_str(txt: &str) -> Result<Self, Self::Err> {
        let rest = txt.strip_prefix("0x").ok_or(FromHexError::Prefix)?;
        let item = T::from_hex(rest).map_err(FromHexError::Hex)?;
        Ok(Self(item))
    }
}
