//! A simple disassembler from the EVM Toolkit.
//!
//! Converts a stream of bytes into an iterator of [`Op<[u8]>'].
//!
//! See the documentation for [`Disassembler`] for more information.
mod error {
    use snafu::{Backtrace, Snafu};

    use super::Offset;

    /// Errors that may arise during disassembly.
    #[derive(Debug, Snafu)]
    #[snafu(context(suffix(false)), visibility(pub(super)))]
    #[non_exhaustive]
    pub enum Error {
        /// The input is incomplete.
        #[non_exhaustive]
        Truncated {
            /// The remaining bytes, with their location.
            remaining: Offset<Vec<u8>>,

            /// The location of the error.
            backtrace: Backtrace,
        },
    }
}

use etk_ops::cancun::Op;

pub use self::error::Error;

use snafu::ensure;

use std::collections::VecDeque;
use std::fmt;
use std::io::{self, Write};

/// An item with its location within a stream of bytes.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Offset<T> {
    /// The location within a stream of bytes of a particular item.
    pub offset: usize,

    /// The item, which was located at `offset.
    pub item: T,
}

impl<T> Offset<T> {
    /// Create a new instance of `Offset`.
    pub const fn new(offset: usize, item: T) -> Self {
        Self { offset, item }
    }
}

impl<T> fmt::Display for Offset<T>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{: >4x}:   {}", self.offset, self.item)
    }
}

/// A [`std::iter::Iterator`] over the [`Op<[u8]>`] produced by disassembling
/// a stream of bytes.
#[derive(Debug)]
pub struct Iter<'a> {
    disassembler: &'a mut Disassembler,
}

impl<'a> Iterator for Iter<'a> {
    type Item = Offset<Op<[u8]>>;

    fn next(&mut self) -> Option<Self::Item> {
        let buffer = &mut self.disassembler.buffer;
        let front = *buffer.front()?;
        let specifier = Op::<()>::from(front);
        let len = specifier.size();
        if buffer.len() < len {
            return None;
        }

        let remaining = buffer.split_off(len);
        let mut instruction = std::mem::replace(&mut self.disassembler.buffer, remaining);
        let instruction = instruction.make_contiguous();

        let item = Op::from_slice(instruction).ok()?;
        let offset = self.disassembler.offset;
        self.disassembler.offset += len;
        Some(Offset::new(offset, item))
    }
}

/// A simple disassembler that converts a stream of bytes into an iterator over
/// the disassembled [`Op<[u8]>`].
///
/// ## Example
/// ```rust
/// use etk_ops::cancun::{Op, GetPc, Stop};
/// use etk_asm::disasm::Disassembler;
/// # use etk_asm::disasm::Offset;
///
/// use std::io::Write;
///
/// let input = [0x58, 0x00];
///
/// let mut dasm = Disassembler::new();
/// dasm.write_all(&input).unwrap();
///
/// let actual: Vec<_> = dasm.ops().collect();
///
/// dasm.finish().unwrap();
///
/// # let expected = [Offset::new(0, GetPc.into()), Offset::new(1, Stop.into())];
/// # assert_eq!(expected, actual.as_slice());
/// ```
#[derive(Debug, Default)]
pub struct Disassembler {
    buffer: VecDeque<u8>,
    offset: usize,
}

impl Write for Disassembler {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.buffer.reserve(buf.len());
        self.buffer.extend(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

impl Disassembler {
    /// Create a new instance of `Disassembler`.
    pub fn new() -> Self {
        Default::default()
    }

    /// Get an iterator over the disassembled [`Op<[u8]>`].
    pub fn ops(&mut self) -> Iter {
        Iter { disassembler: self }
    }

    /// Indicate that there are no further bytes to write. Returns any errors
    /// collected.
    pub fn finish(self) -> Result<(), Error> {
        ensure!(
            self.buffer.is_empty(),
            error::Truncated {
                remaining: Offset::new(self.offset, self.buffer.into()),
            }
        );
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use etk_ops::cancun::*;

    use hex_literal::hex;

    use super::*;

    #[test]
    fn empty() {
        let mut dasm = Disassembler::new();
        assert!(dasm.ops().next().is_none());
        dasm.finish().unwrap();
    }

    #[test]
    fn stop() {
        let input = hex!("00");
        let expected = [Offset::new(0, Op::from(Stop))];

        let mut dasm = Disassembler::new();
        dasm.write_all(&input).unwrap();

        let actual: Vec<_> = dasm.ops().collect();

        assert_eq!(expected, actual.as_slice());
        dasm.finish().unwrap();
    }

    #[test]
    fn partial_push5() {
        let input = hex!("6401020304");
        let expected = [Offset::new(0, Op::from(Push5(hex!("0102030406"))))];

        let mut dasm = Disassembler::new();
        dasm.write_all(&input).unwrap();
        assert!(dasm.ops().next().is_none());

        dasm.write_all(&hex!("06")).unwrap();

        let actual: Vec<_> = dasm.ops().collect();

        assert_eq!(expected, actual.as_slice());
        dasm.finish().unwrap();
    }

    #[test]
    fn push5() {
        let input = hex!("640102030405");
        let expected = [Offset::new(0, Op::from(Push5(hex!("0102030405"))))];

        let mut dasm = Disassembler::new();
        dasm.write_all(&input).unwrap();

        let actual: Vec<_> = dasm.ops().collect();

        assert_eq!(expected, actual.as_slice());
        dasm.finish().unwrap();
    }
}
