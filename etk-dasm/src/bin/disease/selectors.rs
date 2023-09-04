use etk_4byte::reverse_selector;

use etk_ops::prague::{Op, Operation};

use std::fmt;

#[derive(Debug)]
pub struct DisplayOp(pub Op<[u8]>);

impl DisplayOp {
    fn reverse_selector(&self) -> Vec<&'static str> {
        self.selector()
            .map(|s| reverse_selector(s).collect())
            .unwrap_or_default()
    }

    fn selector(&self) -> Option<u32> {
        let mut imm = self.0.immediate()?;

        // Strip leading zeros.
        while !imm.is_empty() && imm[0] == 0 {
            imm = &imm[1..];
        }

        let mut be_bytes = [0u8; 4];

        let start = be_bytes.len().checked_sub(imm.len())?;
        let end = be_bytes.len();
        be_bytes[start..end].copy_from_slice(imm);

        Some(u32::from_be_bytes(be_bytes))
    }
}

impl fmt::Display for DisplayOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0.code())?;

        let imm = match self.0.immediate() {
            Some(i) => i,
            None => return Ok(()),
        };

        write!(f, " 0x{}", hex::encode(imm))?;

        let selectors = self.reverse_selector();

        if selectors.is_empty() {
            return Ok(());
        }

        write!(f, " #")?;

        if selectors.len() < 3 {
            for selector in &selectors {
                write!(f, r#" selector("{}")"#, selector)?;
            }
        } else {
            write!(
                f,
                " https://www.4byte.directory/signatures/?bytes4_signature=0x{:0>8}",
                hex::encode(imm),
            )?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use etk_ops::prague::*;

    use hex_literal::hex;

    use super::*;

    #[test]
    fn format_selector_push1() {
        let bin = hex!("b6");

        let op = Push1(bin).into();
        let txt = DisplayOp(op).to_string();

        assert_eq!(
            txt,
            r#"push1 0xb6 # selector("matchByAdmin_TwH36(uint256[])")"#,
        );
    }

    #[test]
    fn format_selector_push32() {
        let bin = hex!("00000000000000000000000000000000000000000000000000000000000000b6");

        let op = Push32(bin).into();
        let txt = DisplayOp(op).to_string();

        let expected = concat!(
            "push32 ",
            "0x00000000000000000000000000000000000000000000000000000000000000b6 ",
            r#"# selector("matchByAdmin_TwH36(uint256[])")"#,
        );

        assert_eq!(txt, expected);
    }

    #[test]
    fn format_selector_push1_zero() {
        let bin = hex!("00");

        let op = Push1(bin).into();
        let txt = DisplayOp(op).to_string();

        let expected = concat!(
            "push1 0x00 # ",
            "https://www.4byte.directory/signatures/?bytes4_signature=0x00000000",
        );

        assert_eq!(txt, expected);
    }
}
