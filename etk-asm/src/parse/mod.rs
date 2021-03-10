use crate::ops::{Op, TryFromSliceError};

use pest::Parser;
use pest_derive::Parser;
use sha3::{Digest, Keccak256};

#[derive(Parser)]
#[grammar = "parse/asm.pest"]
struct AsmParser;

#[derive(Debug, Eq, PartialEq)]
pub enum ParseError {
    ImmediateTooLarge,
    LexerError(String),
}

impl From<TryFromSliceError> for ParseError {
    fn from(_: TryFromSliceError) -> Self {
        ParseError::ImmediateTooLarge
    }
}

pub fn parse_asm(asm: &str) -> Result<Vec<Op>, ParseError> {
    let mut ops: Vec<Op> = Vec::new();

    let pairs =
        AsmParser::parse(Rule::program, asm).map_err(|e| ParseError::LexerError(e.to_string()))?;
    for pair in pairs {
        match pair.as_rule() {
            Rule::jumpdest => {
                let mut pair = pair.into_inner();
                let label = pair.next().unwrap();
                ops.push(Op::JumpDest(Some(label.as_str()[1..].to_string())));
            }
            Rule::push => {
                ops.push(parse_push(pair)?);
            }
            Rule::op => {
                let op: Op = match pair.as_str() {
                    "stop" => Op::Stop,
                    "add" => Op::Add,
                    "mul" => Op::Mul,
                    "sub" => Op::Sub,
                    "div" => Op::Div,
                    "sdiv" => Op::SDiv,
                    "mod" => Op::Mod,
                    "smod" => Op::SMod,
                    "addmod" => Op::AddMod,
                    "mulmod" => Op::MulMod,
                    "exp" => Op::Exp,
                    "signextend" => Op::SignExtend,
                    "lt" => Op::Lt,
                    "gt" => Op::Gt,
                    "slt" => Op::SLt,
                    "sgt" => Op::SGt,
                    "eq" => Op::Eq,
                    "iszero" => Op::IsZero,
                    "and" => Op::And,
                    "or" => Op::Or,
                    "xor" => Op::Xor,
                    "not" => Op::Not,
                    "shl" => Op::Shl,
                    "shr" => Op::Shr,
                    "sar" => Op::Sar,
                    "sha3" => Op::Keccak256,
                    "address" => Op::Address,
                    "balance" => Op::Balance,
                    "origin" => Op::Origin,
                    "caller" => Op::Caller,
                    "callvalue" => Op::CallValue,
                    "calldataload" => Op::CallDataLoad,
                    "calldatasize" => Op::CallDataSize,
                    "calldatacopy" => Op::CallDataCopy,
                    "codesize" => Op::CodeSize,
                    "codecopy" => Op::CodeCopy,
                    "gasprice" => Op::GasPrice,
                    "extcodesize" => Op::ExtCodeSize,
                    "extcodecopy" => Op::ExtCodeCopy,
                    "returndatasize" => Op::ReturnDataSize,
                    "returndatacopy" => Op::ReturnDataCopy,
                    "extcodehash" => Op::ExtCodeHash,
                    "blockhash" => Op::BlockHash,
                    "coinbase" => Op::Coinbase,
                    "timestamp" => Op::Timestamp,
                    "number" => Op::Number,
                    "difficulty" => Op::Difficulty,
                    "gaslimit" => Op::GasLimit,
                    "pop" => Op::Pop,
                    "mload" => Op::MLoad,
                    "mstore" => Op::MStore,
                    "mstore8" => Op::MStore8,
                    "sload" => Op::SLoad,
                    "sstore" => Op::SStore,
                    "jump" => Op::Jump,
                    "jumpi" => Op::JumpI,
                    "pc" => Op::GetPc,
                    "msize" => Op::MSize,
                    "gas" => Op::Gas,
                    "create" => Op::Create,
                    "call" => Op::Call,
                    "callcode" => Op::CallCode,
                    "return" => Op::Return,
                    "delegatecall" => Op::DelegateCall,
                    "create2" => Op::Create2,
                    "staticcall" => Op::StaticCall,
                    "revert" => Op::Revert,
                    "selfdestruct" => Op::SelfDestruct,
                    "dup1" => Op::Dup1,
                    "dup2" => Op::Dup2,
                    "dup3" => Op::Dup3,
                    "dup4" => Op::Dup4,
                    "dup5" => Op::Dup5,
                    "dup6" => Op::Dup6,
                    "dup7" => Op::Dup7,
                    "dup8" => Op::Dup8,
                    "dup9" => Op::Dup9,
                    "dup10" => Op::Dup10,
                    "dup11" => Op::Dup11,
                    "dup12" => Op::Dup12,
                    "dup13" => Op::Dup13,
                    "dup14" => Op::Dup14,
                    "dup15" => Op::Dup15,
                    "dup16" => Op::Dup16,
                    "swap1" => Op::Swap1,
                    "swap2" => Op::Swap2,
                    "swap3" => Op::Swap3,
                    "swap4" => Op::Swap4,
                    "swap5" => Op::Swap5,
                    "swap6" => Op::Swap6,
                    "swap7" => Op::Swap7,
                    "swap8" => Op::Swap8,
                    "swap9" => Op::Swap9,
                    "swap10" => Op::Swap10,
                    "swap11" => Op::Swap11,
                    "swap12" => Op::Swap12,
                    "swap13" => Op::Swap13,
                    "swap14" => Op::Swap14,
                    "swap15" => Op::Swap15,
                    "swap16" => Op::Swap16,
                    "log0" => Op::Log0,
                    "log1" => Op::Log1,
                    "log2" => Op::Log2,
                    "log3" => Op::Log3,
                    "log4" => Op::Log4,
                    _ => unreachable!(),
                };
                ops.push(op);
            }
            _ => continue,
        }
    }

    Ok(ops)
}

fn parse_push(pair: pest::iterators::Pair<Rule>) -> Result<Op, ParseError> {
    let mut pair = pair.into_inner();
    let size = pair.next().unwrap();
    let size: usize = size.as_str().parse().unwrap();
    let operand = pair.next().unwrap();

    let op = match operand.as_rule() {
        Rule::hex => {
            let raw = operand.as_str();
            let imm = hex::decode(&raw[2..]).unwrap();
            Op::push_with_immediate(size, imm.as_slice())?
        }
        Rule::decimal => {
            let raw = operand.as_str();
            let imm: u128 = raw.parse().map_err(|_| ParseError::ImmediateTooLarge)?;

            let msb = 128 - imm.leading_zeros();
            let mut len = (msb / 8) as usize;
            if msb % 8 != 0 {
                len += 1;
            }
            len = std::cmp::max(len, size);

            Op::push_with_immediate(size, &imm.to_be_bytes()[16 - len..])?
        }
        Rule::binary => {
            unimplemented!()
        }
        Rule::selector => {
            let raw = operand.into_inner().next().unwrap().as_str();
            let mut hasher = Keccak256::new();
            hasher.update(raw.as_bytes());
            Op::push_with_immediate(size, &hasher.finalize()[0..4])?
        }
        Rule::label => {
            let label = operand.as_str()[1..].to_string();
            Op::push_with_label(size, label)
        }
        r => unreachable!(format!("{:?}", r)),
    };

    Ok(op)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ops::Imm;
    use hex_literal::hex;

    #[test]
    fn parse_ops() {
        let asm = r#"
            stop
            pc
            gas
            xor
        "#;
        let expected = vec![Op::Stop, Op::GetPc, Op::Gas, Op::Xor];
        assert_eq!(parse_asm(asm), Ok(expected));
    }

    #[test]
    fn parse_push_hex() {
        let asm = r#"
            push1 0x01 ; comment
            push1 0x42
            push2 0x0102
            push4 0x01020304
            push8 0x0102030405060708
            push16 0x0102030405060708090a0b0c0d0e0f10
            push24 0x0102030405060708090a0b0c0d0e0f101112131415161718
            push32 0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20
        "#;
        let expected = vec![
            Op::Push1(Imm::from(hex!("01"))),
            Op::Push1(Imm::from(hex!("42"))),
            Op::Push2(Imm::from(hex!("0102"))),
            Op::Push4(Imm::from(hex!("01020304"))),
            Op::Push8(Imm::from(hex!("0102030405060708"))),
            Op::Push16(Imm::from(hex!("0102030405060708090a0b0c0d0e0f10"))),
            Op::Push24(Imm::from(hex!(
                "0102030405060708090a0b0c0d0e0f101112131415161718"
            ))),
            Op::Push32(Imm::from(hex!(
                "0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20"
            ))),
        ];
        assert_eq!(parse_asm(asm), Ok(expected));

        let asm = "push2 0x010203";
        assert_eq!(parse_asm(asm), Err(ParseError::ImmediateTooLarge));
    }

    #[test]
    fn parse_push_decimal() {
        let asm = r#"
            push1 1
            push1 42
            push2 42
            push2 256
            push4 4294967295
            push8 18446744073709551615
            push16 340282366920938463463374607431768211455
        "#;
        let expected = vec![
            Op::Push1(Imm::from([1])),
            Op::Push1(Imm::from([42])),
            Op::Push2(Imm::from([0, 42])),
            Op::Push2(Imm::from(hex!("0100"))),
            Op::Push4(Imm::from(hex!("ffffffff"))),
            Op::Push8(Imm::from(hex!("ffffffffffffffff"))),
            Op::Push16(Imm::from(hex!("ffffffffffffffffffffffffffffffff"))),
        ];
        assert_eq!(parse_asm(asm), Ok(expected));

        // let asm = "push2 0x010203";
        // assert_eq!(parse_asm(asm), Err(ParseError::ImmediateTooLarge));
    }

    #[test]
    fn parse_variable_ops() {
        let asm = r#"
            swap1
            swap4
            swap16
            dup1
            dup4
            dup16
            log0
            log4
        "#;
        let expected = vec![
            Op::Swap1,
            Op::Swap4,
            Op::Swap16,
            Op::Dup1,
            Op::Dup4,
            Op::Dup16,
            Op::Log0,
            Op::Log4,
        ];
        assert_eq!(parse_asm(asm), Ok(expected));
    }

    #[test]
    fn parse_jumpdest_label() {
        let asm = "jumpdest .start";
        let expected = vec![Op::JumpDest(Some(String::from("start")))];
        assert_eq!(parse_asm(asm), Ok(expected));
    }

    #[test]
    fn parse_push_label() {
        let asm = r#"
            push2 .snake_case
            jumpi
        "#;
        let expected = vec![Op::Push2(Imm::from("snake_case")), Op::JumpI];
        assert_eq!(parse_asm(asm), Ok(expected));
    }

    #[test]
    fn parse_selector() {
        let asm = r#"
            push4 selector("name()")
            push4 selector("balanceOf(address)")
            push4 selector("transfer(address,uint256)")

        "#;
        let expected = vec![
            Op::Push4(Imm::from(hex!("06fdde03"))),
            Op::Push4(Imm::from(hex!("70a08231"))),
            Op::Push4(Imm::from(hex!("a9059cbb"))),
        ];
        assert_eq!(parse_asm(asm), Ok(expected));
    }
}
