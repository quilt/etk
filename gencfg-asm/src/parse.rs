use crate::ops::{Imm, Op};

use std::convert::TryFrom;

use pest::Parser;
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "asm.pest"]
struct AsmParser;

#[allow(dead_code)]
pub fn parse_asm(asm: &str) -> Vec<Op> {
    let mut ops: Vec<Op> = Vec::new();

    let pairs = AsmParser::parse(Rule::program, asm).unwrap_or_else(|e| panic!("{}", e));
    for pair in pairs {
        println!("Rule:    {:?}", pair.as_rule());
        println!("Span:    {:?}", pair.as_span());
        println!("Text:    {}", pair.as_str());

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

                let imm = &hex::decode(raw).expect("immediate must be valid hex")[..];

                let op = match size {
                    1 => Op::Push1(Imm::<[u8; 1]>::try_from(imm).unwrap()),
                    2 => Op::Push2(Imm::<[u8; 2]>::try_from(imm).unwrap()),
                    3 => Op::Push3(Imm::<[u8; 3]>::try_from(imm).unwrap()),
                    4 => Op::Push4(Imm::<[u8; 4]>::try_from(imm).unwrap()),
                    5 => Op::Push5(Imm::<[u8; 5]>::try_from(imm).unwrap()),
                    6 => Op::Push6(Imm::<[u8; 6]>::try_from(imm).unwrap()),
                    7 => Op::Push7(Imm::<[u8; 7]>::try_from(imm).unwrap()),
                    8 => Op::Push8(Imm::<[u8; 8]>::try_from(imm).unwrap()),
                    9 => Op::Push9(Imm::<[u8; 9]>::try_from(imm).unwrap()),
                    10 => Op::Push10(Imm::<[u8; 10]>::try_from(imm).unwrap()),
                    11 => Op::Push11(Imm::<[u8; 11]>::try_from(imm).unwrap()),
                    12 => Op::Push12(Imm::<[u8; 12]>::try_from(imm).unwrap()),
                    13 => Op::Push13(Imm::<[u8; 13]>::try_from(imm).unwrap()),
                    14 => Op::Push14(Imm::<[u8; 14]>::try_from(imm).unwrap()),
                    15 => Op::Push15(Imm::<[u8; 15]>::try_from(imm).unwrap()),
                    16 => Op::Push16(Imm::<[u8; 16]>::try_from(imm).unwrap()),
                    17 => Op::Push17(Imm::<[u8; 17]>::try_from(imm).unwrap()),
                    18 => Op::Push18(Imm::<[u8; 18]>::try_from(imm).unwrap()),
                    19 => Op::Push19(Imm::<[u8; 19]>::try_from(imm).unwrap()),
                    20 => Op::Push20(Imm::<[u8; 20]>::try_from(imm).unwrap()),
                    21 => Op::Push21(Imm::<[u8; 21]>::try_from(imm).unwrap()),
                    22 => Op::Push22(Imm::<[u8; 22]>::try_from(imm).unwrap()),
                    23 => Op::Push23(Imm::<[u8; 23]>::try_from(imm).unwrap()),
                    24 => Op::Push24(Imm::<[u8; 24]>::try_from(imm).unwrap()),
                    25 => Op::Push25(Imm::<[u8; 25]>::try_from(imm).unwrap()),
                    26 => Op::Push26(Imm::<[u8; 26]>::try_from(imm).unwrap()),
                    27 => Op::Push27(Imm::<[u8; 27]>::try_from(imm).unwrap()),
                    28 => Op::Push28(Imm::<[u8; 28]>::try_from(imm).unwrap()),
                    29 => Op::Push29(Imm::<[u8; 29]>::try_from(imm).unwrap()),
                    30 => Op::Push30(Imm::<[u8; 30]>::try_from(imm).unwrap()),
                    31 => Op::Push31(Imm::<[u8; 31]>::try_from(imm).unwrap()),
                    32 => Op::Push32(Imm::<[u8; 32]>::try_from(imm).unwrap()),
                    _ => unreachable!(),
                };

                ops.push(op);
            }
            Rule::op => {
                println!("instruction:  {}", pair.as_str());
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
                    inst => unreachable!("{}", inst),
                    // swap | dup |
                    // push log
                };
                ops.push(op);
            }
            _ => continue,
        }
    }

    ops
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_ops() {
        let asm = r#"
            stop
            pc
            gas
            xor
        "#;
        let expected = vec![Op::Stop, Op::GetPc, Op::Gas, Op::Xor];
        assert_eq!(parse_asm(asm), expected);
    }

    #[test]
    fn parse_jumpdest_label() {
        let asm = ":start jumpdest";
        let expected = vec![Op::JumpDest(Some(String::from("start")))];
        assert_eq!(parse_asm(asm), expected);
    }

    #[test]
    fn parse_push() {
        let asm = r#"
            push1 1
            push1 2a
            push2 0102
            push4 01020304
            push8 0102030405060708
            push16 0102030405060708090a0b0c0d0e0f10
            push24 0102030405060708090a0b0c0d0e0f101112131415161718
            push32 0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20
        "#;
        let expected = vec![
            Op::Push1(Imm::from([1])),
            Op::Push1(Imm::from([42])),
            Op::Push2(Imm::from([1, 2])),
            Op::Push4(Imm::from([1, 2, 3, 4])),
            Op::Push8(Imm::from([1, 2, 3, 4, 5, 6, 7, 8])),
            Op::Push16(Imm::from([
                1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
            ])),
            Op::Push24(Imm::from([
                1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
                24,
            ])),
            Op::Push32(Imm::from([
                1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
                24, 25, 26, 27, 28, 29, 30, 31, 32,
            ])),
        ];
        assert_eq!(parse_asm(asm), expected);
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
        assert_eq!(parse_asm(asm), expected);
    }
}
