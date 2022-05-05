use etk_4byte::reverse_selector;

use etk_asm::ops::ConcreteOp;

use std::fmt;

#[derive(Debug)]
pub struct DisplayOp(pub ConcreteOp);

impl DisplayOp {
    fn reverse_selector(&self) -> Vec<&'static str> {
        self.selector()
            .map(|s| reverse_selector(s).collect())
            .unwrap_or_default()
    }

    fn selector(&self) -> Option<u32> {
        let mut imm = match &self.0 {
            ConcreteOp::Push1(imm) => imm as &[u8],
            ConcreteOp::Push2(imm) => imm as &[u8],
            ConcreteOp::Push3(imm) => imm as &[u8],
            ConcreteOp::Push4(imm) => imm as &[u8],
            ConcreteOp::Push5(imm) => imm as &[u8],
            ConcreteOp::Push6(imm) => imm as &[u8],
            ConcreteOp::Push7(imm) => imm as &[u8],
            ConcreteOp::Push8(imm) => imm as &[u8],
            ConcreteOp::Push9(imm) => imm as &[u8],
            ConcreteOp::Push10(imm) => imm as &[u8],
            ConcreteOp::Push11(imm) => imm as &[u8],
            ConcreteOp::Push12(imm) => imm as &[u8],
            ConcreteOp::Push13(imm) => imm as &[u8],
            ConcreteOp::Push14(imm) => imm as &[u8],
            ConcreteOp::Push15(imm) => imm as &[u8],
            ConcreteOp::Push16(imm) => imm as &[u8],
            ConcreteOp::Push17(imm) => imm as &[u8],
            ConcreteOp::Push18(imm) => imm as &[u8],
            ConcreteOp::Push19(imm) => imm as &[u8],
            ConcreteOp::Push20(imm) => imm as &[u8],
            ConcreteOp::Push21(imm) => imm as &[u8],
            ConcreteOp::Push22(imm) => imm as &[u8],
            ConcreteOp::Push23(imm) => imm as &[u8],
            ConcreteOp::Push24(imm) => imm as &[u8],
            ConcreteOp::Push25(imm) => imm as &[u8],
            ConcreteOp::Push26(imm) => imm as &[u8],
            ConcreteOp::Push27(imm) => imm as &[u8],
            ConcreteOp::Push28(imm) => imm as &[u8],
            ConcreteOp::Push29(imm) => imm as &[u8],
            ConcreteOp::Push30(imm) => imm as &[u8],
            ConcreteOp::Push31(imm) => imm as &[u8],
            ConcreteOp::Push32(imm) => imm as &[u8],
            _ => return None,
        };

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
        let selectors = self.reverse_selector();

        if selectors.is_empty() {
            return fmt::Display::fmt(&self.0, f);
        }

        write!(f, "{} # ", self.0)?;

        if selectors.len() < 3 {
            for selector in &selectors[..selectors.len() - 1] {
                write!(f, r#"selector("{}") "#, selector)?;
            }

            write!(f, r#"selector("{}")"#, selectors.last().unwrap())?;
        } else {
            write!(
                f,
                "https://www.4byte.directory/signatures/?bytes4_signature={:#010x}",
                0
            )?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use etk_asm::ops::Specifier;

    use hex_literal::hex;

    use super::*;

    #[test]
    fn format_selector_push1() {
        let bin = hex!("b6");

        let op = ConcreteOp::with_immediate(Specifier::Push1(()), &bin).unwrap();
        let txt = DisplayOp(op).to_string();

        assert_eq!(
            txt,
            r#"push1 0xb6 # selector("matchByAdmin_TwH36(uint256[])")"#,
        );
    }

    #[test]
    fn format_selector_push32() {
        let bin = hex!("00000000000000000000000000000000000000000000000000000000000000b6");

        let op = ConcreteOp::with_immediate(Specifier::Push32(()), &bin).unwrap();
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

        let op = ConcreteOp::with_immediate(Specifier::Push1(()), &bin).unwrap();
        let txt = DisplayOp(op).to_string();

        let expected = concat!(
            "push1 0x00 # ",
            "https://www.4byte.directory/signatures/?bytes4_signature=0x00000000",
        );

        assert_eq!(txt, expected);
    }
}
