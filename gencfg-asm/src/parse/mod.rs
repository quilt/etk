use crate::ops::{Imm, Op, TryFromSliceError};

use std::convert::TryFrom;

use pest::Parser;
use pest_derive::Parser;

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
                let label = pair
                    .into_inner()
                    .next()
                    .expect("jumpdest must have label")
                    .as_str();
                ops.push(Op::JumpDest(Some(label[1..].to_string())));
            }
            Rule::push => {
                let mut pair = pair.into_inner();
                let size: usize = pair.next().unwrap().as_str().parse().unwrap();

                let mut raw = pair.next().unwrap().as_str().to_string();
                if raw.len() == 1 {
                    raw = format!("0{}", raw);
                }

                let imm = &hex::decode(raw).unwrap()[..];

                let op = match size {
                    1 => Op::Push1(Imm::try_from(imm)?),
                    2 => Op::Push2(Imm::try_from(imm)?),
                    3 => Op::Push3(Imm::try_from(imm)?),
                    4 => Op::Push4(Imm::try_from(imm)?),
                    5 => Op::Push5(Imm::try_from(imm)?),
                    6 => Op::Push6(Imm::try_from(imm)?),
                    7 => Op::Push7(Imm::try_from(imm)?),
                    8 => Op::Push8(Imm::try_from(imm)?),
                    9 => Op::Push9(Imm::try_from(imm)?),
                    10 => Op::Push10(Imm::try_from(imm)?),
                    11 => Op::Push11(Imm::try_from(imm)?),
                    12 => Op::Push12(Imm::try_from(imm)?),
                    13 => Op::Push13(Imm::try_from(imm)?),
                    14 => Op::Push14(Imm::try_from(imm)?),
                    15 => Op::Push15(Imm::try_from(imm)?),
                    16 => Op::Push16(Imm::try_from(imm)?),
                    17 => Op::Push17(Imm::try_from(imm)?),
                    18 => Op::Push18(Imm::try_from(imm)?),
                    19 => Op::Push19(Imm::try_from(imm)?),
                    20 => Op::Push20(Imm::try_from(imm)?),
                    21 => Op::Push21(Imm::try_from(imm)?),
                    22 => Op::Push22(Imm::try_from(imm)?),
                    23 => Op::Push23(Imm::try_from(imm)?),
                    24 => Op::Push24(Imm::try_from(imm)?),
                    25 => Op::Push25(Imm::try_from(imm)?),
                    26 => Op::Push26(Imm::try_from(imm)?),
                    27 => Op::Push27(Imm::try_from(imm)?),
                    28 => Op::Push28(Imm::try_from(imm)?),
                    29 => Op::Push29(Imm::try_from(imm)?),
                    30 => Op::Push30(Imm::try_from(imm)?),
                    31 => Op::Push31(Imm::try_from(imm)?),
                    32 => Op::Push32(Imm::try_from(imm)?),

                    _ => unreachable!(),
                };

                ops.push(op);
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

#[cfg(test)]
mod tests {
    use super::*;
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
    fn parse_jumpdest_label() {
        let asm = "jumpdest .start";
        let expected = vec![Op::JumpDest(Some(String::from("start")))];
        assert_eq!(parse_asm(asm), Ok(expected));
    }

    #[test]
    fn parse_push() {
        let asm = r#"
            push1 1
            push1 42
            push2 0102
            push4 01020304
            push8 0102030405060708
            push16 0102030405060708090a0b0c0d0e0f10
            push24 0102030405060708090a0b0c0d0e0f101112131415161718
            push32 0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20
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

        let asm = "push2 010203";
        assert_eq!(parse_asm(asm), Err(ParseError::ImmediateTooLarge));
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
}
