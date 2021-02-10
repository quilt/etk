use crate::ops::{Op, Specifier};

use std::collections::VecDeque;
use std::fmt;
use std::io::{self, Write};

#[derive(Debug, Clone)]
pub enum Error {
    Truncated { remaining: Offset<Vec<u8>> },
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Offset<T> {
    pub offset: usize,
    pub item: T,
}

impl<T> Offset<T> {
    const fn new(offset: usize, item: T) -> Self {
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

#[derive(Debug)]
pub struct Iter<'a> {
    disassembler: &'a mut Disassembler,
}

impl<'a> Iterator for Iter<'a> {
    type Item = Offset<Op>;

    fn next(&mut self) -> Option<Self::Item> {
        let buffer = &mut self.disassembler.buffer;
        let front = *buffer.front()?;
        let specifier = Specifier::from(front);
        let len = specifier.extra_len() as usize + 1;
        if buffer.len() < len {
            return None;
        }

        let remaining = buffer.split_off(len);
        let mut instruction = std::mem::replace(&mut self.disassembler.buffer, remaining);
        let instruction = instruction.make_contiguous();

        let item = Op::from_slice(instruction);
        let offset = self.disassembler.offset;
        self.disassembler.offset += len;
        Some(Offset::new(offset, item))
    }
}

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
    pub fn new() -> Self {
        Default::default()
    }

    pub fn ops(&mut self) -> Iter {
        Iter { disassembler: self }
    }

    pub fn finish(self) -> Result<(), Error> {
        if self.buffer.is_empty() {
            Ok(())
        } else {
            Err(Error::Truncated {
                remaining: Offset::new(self.offset, self.buffer.into()),
            })
        }
    }
}

#[cfg(test)]
mod tests {
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
        let expected = [Offset::new(0, Op::Stop)];

        let mut dasm = Disassembler::new();
        dasm.write_all(&input).unwrap();

        let actual: Vec<_> = dasm.ops().collect();

        assert_eq!(expected, actual.as_slice());
        dasm.finish().unwrap();
    }

    #[test]
    fn partial_push5() {
        let input = hex!("6401020304");
        let expected = [Offset::new(0, Op::Push5(hex!("0102030406").into()))];

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
        let expected = [Offset::new(0, Op::Push5(hex!("0102030405").into()))];

        let mut dasm = Disassembler::new();
        dasm.write_all(&input).unwrap();

        let actual: Vec<_> = dasm.ops().collect();

        assert_eq!(expected, actual.as_slice());
        dasm.finish().unwrap();
    }
}
