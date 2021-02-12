use crate::parse::Hex;

use std::fs::File;
use std::io;
use std::path::PathBuf;

use structopt::StructOpt;

#[derive(Debug, StructOpt)]
pub struct InputSource {
    #[structopt(
        long = "bin-file",
        short = "b",
        help = "path to input data, as raw binary data",
        conflicts_with_all(&["hex-file", "code"]),
        required_unless_one(&["hex-file", "code"]),
    )]
    bin_file: Option<PathBuf>,

    #[structopt(
        long = "hex-file",
        short = "x",
        help = "path to input data, encoded in hexadecimal format",
        conflicts_with = "code"
    )]
    hex_file: Option<PathBuf>,

    #[structopt(
        long = "code",
        short = "c",
        help = "input data, encoded in hexadecimal format (with 0x prefix)"
    )]
    code: Option<Hex<Vec<u8>>>,
}

impl InputSource {
    pub fn open(self) -> Result<impl io::Read, io::Error> {
        let boxed: Box<dyn io::Read> = match (self.bin_file, self.hex_file, self.code) {
            (Some(bin), None, None) => Box::new(Self::bin(bin)?),
            (None, Some(hex), None) => Box::new(Self::hex(hex)?),
            (None, None, Some(code)) => Box::new(Self::code(code.0)),
            _ => unreachable!(),
        };

        Ok(boxed)
    }

    fn bin(path: PathBuf) -> Result<File, io::Error> {
        File::open(path)
    }

    fn hex(path: PathBuf) -> Result<HexRead<File>, io::Error> {
        Ok(HexRead::new(File::open(path)?))
    }

    fn code(code: Vec<u8>) -> io::Cursor<Vec<u8>> {
        io::Cursor::new(code)
    }
}

#[derive(Debug)]
struct HexRead<R> {
    first_read: bool,
    file: R,
    remainder: Option<u8>,
}

impl<R> HexRead<R> {
    fn new(file: R) -> Self {
        Self {
            first_read: true,
            remainder: None,
            file,
        }
    }
}

impl<R> io::Read for HexRead<R>
where
    R: io::Read,
{
    fn read(&mut self, buffer: &mut [u8]) -> Result<usize, io::Error> {
        // TODO: It's possible to avoid the allocation (use latter two thirds of
        //       `buffer` to read from file, then decode into first third) but
        //       it doesn't seem worth the effort.

        if 0 == buffer.len() {
            return Ok(0);
        }

        let mut available;
        let mut hexbuffer;

        if let Some(remainder) = self.remainder {
            available = 1;
            hexbuffer = vec![0u8; 1 + (2 * buffer.len())];
            hexbuffer[0] = remainder;
        } else {
            available = 0;
            hexbuffer = vec![0u8; 2 * buffer.len()];
        }

        // Shadow the vec so we can manipulate the start index.
        let mut hexbuffer: &mut [u8] = &mut hexbuffer;

        let mut eof;

        loop {
            let read = self.file.read(&mut hexbuffer[available..])?;
            eof = 0 == read;
            available += read;

            // Check for the 0x prefix, if we have read less than 2 bytes.
            if self.first_read && available >= 2 {
                self.first_read = false;
                if b"0x" == &hexbuffer[..2] {
                    available -= 2;

                    if hexbuffer.len() > 2 {
                        hexbuffer = &mut hexbuffer[2..];
                    }
                }
            }

            if eof || available > 1 {
                break;
            }
        }

        if eof && 1 == available {
            if char::from(hexbuffer[0]).is_whitespace() {
                available = 0;
            } else {
                let kind = io::ErrorKind::InvalidData;
                let src = hex::FromHexError::OddLength;
                return Err(io::Error::new(kind, src));
            }
        } else if available % 2 == 0 {
            self.remainder = None;
        } else {
            self.remainder = Some(hexbuffer[available - 1]);
            available -= 1;
        }

        if 0 == available {
            return Ok(0);
        }

        let out_sz = available / 2;

        hex::decode_to_slice(&mut hexbuffer[..available], &mut buffer[..out_sz])
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

        Ok(out_sz)
    }
}

#[cfg(test)]
mod tests {
    use hex_literal::hex;

    use std::io::Read;

    use structopt::clap::ErrorKind;

    use super::*;

    #[test]
    fn input_source_at_least_one() {
        let args: &[&str] = &[];
        let err = InputSource::from_iter_safe(args).unwrap_err();
        assert_eq!(err.kind, ErrorKind::MissingRequiredArgument);
    }

    #[test]
    fn input_source_bin_file_conflicts_with_hex_file() {
        let args = &["exe", "--bin-file", "floop", "--hex-file", "whoop"];
        let err = InputSource::from_iter_safe(args).unwrap_err();
        assert_eq!(err.kind, ErrorKind::ArgumentConflict);
    }

    #[test]
    fn input_source_bin_file_conflicts_with_code() {
        let args = &["exe", "--bin-file", "floop", "--code", "0x00"];
        let err = InputSource::from_iter_safe(args).unwrap_err();
        assert_eq!(err.kind, ErrorKind::ArgumentConflict);
    }

    #[test]
    fn input_source_hex_file_conflicts_with_code() {
        let args = &["exe", "--hex-file", "floop", "--code", "0x00"];
        let err = InputSource::from_iter_safe(args).unwrap_err();
        assert_eq!(err.kind, ErrorKind::ArgumentConflict);
    }

    #[test]
    fn hex_read_with_prefix_empty() {
        let data = b"0x";
        let mut decoder = HexRead::new(&data[..]);

        let mut buf = [0u8; 10];
        let sz = decoder.read(&mut buf).unwrap();
        assert_eq!(sz, 0);
    }

    #[test]
    fn hex_read_no_prefix_empty() {
        let data = b"";
        let mut decoder = HexRead::new(&data[..]);

        let mut buf = [0u8; 10];
        let sz = decoder.read(&mut buf).unwrap();
        assert_eq!(sz, 0);
    }

    #[test]
    fn hex_read_with_prefix_odd_length() {
        let data = b"0xabcdef012345678";
        let mut decoder = HexRead::new(&data[..]);
        let err = decoder.read_to_end(&mut vec![]).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::InvalidData);
    }

    #[test]
    fn hex_read_no_prefix_odd_length() {
        let data = b"abcdef012345678";
        let mut decoder = HexRead::new(&data[..]);
        let err = decoder.read_to_end(&mut vec![]).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::InvalidData);
    }

    #[test]
    fn hex_read_with_prefix_big_buffer() {
        let data = b"0xabcdef0123456789";
        let mut decoder = HexRead::new(&data[..]);

        let mut buf = vec![0u8; data.len()];
        let sz = decoder.read(&mut buf).unwrap();
        assert_eq!(sz, 8);

        let actual = &buf[..sz];
        assert_eq!(actual, hex!("abcdef0123456789"));

        let sz = decoder.read(&mut buf).unwrap();
        assert_eq!(sz, 0);
    }

    #[test]
    fn hex_read_no_prefix_big_buffer() {
        let data = b"abcdef0123456789";
        let mut decoder = HexRead::new(&data[..]);

        let mut buf = vec![0u8; data.len()];
        let sz = decoder.read(&mut buf).unwrap();
        assert_eq!(sz, 8);

        let actual = &buf[..sz];
        assert_eq!(actual, hex!("abcdef0123456789"));

        let sz = decoder.read(&mut buf).unwrap();
        assert_eq!(sz, 0);
    }

    #[test]
    fn hex_read_with_prefix_tiny_buffer() {
        let data = b"0xabcdef0123456789";
        let mut decoder = HexRead::new(&data[..]);

        let mut buf = [0u8];

        let sz = decoder.read(&mut buf).unwrap();
        assert_eq!(sz, 1);
        assert_eq!(buf[0], 0xab);

        let sz = decoder.read(&mut buf).unwrap();
        assert_eq!(sz, 1);
        assert_eq!(buf[0], 0xcd);

        let sz = decoder.read(&mut buf).unwrap();
        assert_eq!(sz, 1);
        assert_eq!(buf[0], 0xef);

        let sz = decoder.read(&mut buf).unwrap();
        assert_eq!(sz, 1);
        assert_eq!(buf[0], 0x01);

        let sz = decoder.read(&mut buf).unwrap();
        assert_eq!(sz, 1);
        assert_eq!(buf[0], 0x23);

        let sz = decoder.read(&mut buf).unwrap();
        assert_eq!(sz, 1);
        assert_eq!(buf[0], 0x45);

        let sz = decoder.read(&mut buf).unwrap();
        assert_eq!(sz, 1);
        assert_eq!(buf[0], 0x67);

        let sz = decoder.read(&mut buf).unwrap();
        assert_eq!(sz, 1);
        assert_eq!(buf[0], 0x89);
    }

    #[test]
    fn hex_read_no_prefix_tiny_buffer() {
        let data = b"abcdef0123456789";
        let mut decoder = HexRead::new(&data[..]);

        let mut buf = [0u8];

        let sz = decoder.read(&mut buf).unwrap();
        assert_eq!(sz, 1);
        assert_eq!(buf[0], 0xab);

        let sz = decoder.read(&mut buf).unwrap();
        assert_eq!(sz, 1);
        assert_eq!(buf[0], 0xcd);

        let sz = decoder.read(&mut buf).unwrap();
        assert_eq!(sz, 1);
        assert_eq!(buf[0], 0xef);

        let sz = decoder.read(&mut buf).unwrap();
        assert_eq!(sz, 1);
        assert_eq!(buf[0], 0x01);

        let sz = decoder.read(&mut buf).unwrap();
        assert_eq!(sz, 1);
        assert_eq!(buf[0], 0x23);

        let sz = decoder.read(&mut buf).unwrap();
        assert_eq!(sz, 1);
        assert_eq!(buf[0], 0x45);

        let sz = decoder.read(&mut buf).unwrap();
        assert_eq!(sz, 1);
        assert_eq!(buf[0], 0x67);

        let sz = decoder.read(&mut buf).unwrap();
        assert_eq!(sz, 1);
        assert_eq!(buf[0], 0x89);

        let sz = decoder.read(&mut buf).unwrap();
        assert_eq!(sz, 0);
    }
}
