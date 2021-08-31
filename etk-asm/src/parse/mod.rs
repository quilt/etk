mod args;
pub(crate) mod error;
mod parser {
    #![allow(clippy::upper_case_acronyms)]

    use pest_derive::Parser;

    #[derive(Parser)]
    #[grammar = "parse/asm.pest"]
    pub(super) struct AsmParser;
}

use crate::ast::Node;
use crate::ops::{
    AbstractOp, Imm, InstructionMacroDefinition, InstructionMacroInvocation, Op, Specifier,
};

use pest::{
    iterators::Pair,
    prec_climber::{Assoc, Operator, PrecClimber},
    Parser,
};

use self::args::{Label, Signature};
use self::error::ParseError;
use self::parser::{AsmParser, Rule};
use crate::ops::Expression;

use sha3::{Digest, Keccak256};

use snafu::OptionExt;

use std::path::PathBuf;

pub(crate) fn parse_asm(asm: &str) -> Result<Vec<Node>, ParseError> {
    let mut program: Vec<Node> = Vec::new();

    let pairs = AsmParser::parse(Rule::program, asm)?;
    for pair in pairs {
        match pair.as_rule() {
            Rule::instruction_macro_definition => {
                program.push(parse_instruction_macro(pair)?);
            }
            Rule::instruction_macro => {
                let mut pairs = pair.into_inner();
                let name = pairs.next().unwrap();
                let mut parameters = Vec::<Imm<Vec<u8>>>::new();
                for pair in pairs {
                    let imm = parse_operand(pair, 16)?;
                    parameters.push(imm);
                }
                let invocation = InstructionMacroInvocation {
                    name: name.as_str().to_string(),
                    parameters,
                };
                program.push(AbstractOp::Macro(invocation).into());
            }
            Rule::builtin => {
                let mut pairs = pair.into_inner();
                let builtin = pairs.next().unwrap();
                assert!(pairs.next().is_none());
                let node = parse_builtin(builtin)?;
                program.push(node);
            }
            Rule::label_definition => {
                let mut pair = pair.into_inner();
                let label = pair.next().unwrap();
                let txt = label.as_str();
                program.push(AbstractOp::Label(txt.to_string()).into());
            }
            Rule::push => {
                program.push(parse_push(pair)?.into());
            }
            Rule::op => {
                let spec: Specifier = pair.as_str().parse().unwrap();
                let op = Op::new(spec).unwrap();
                let aop = AbstractOp::Op(op);
                program.push(aop.into());
            }
            _ => continue,
        }
    }

    Ok(program)
}

fn parse_push(pair: pest::iterators::Pair<Rule>) -> Result<AbstractOp, ParseError> {
    let mut pair = pair.into_inner();
    let size = pair.next().unwrap();
    let size: u32 = size.as_str().parse().unwrap();
    let operand = pair.next().unwrap();

    let spec = Specifier::push(size).unwrap();

    let imm = parse_operand(operand, size)?;
    match imm {
        Imm::Label(s) => Ok(AbstractOp::with_label(spec, s)),
        Imm::Variable(v) => Ok(AbstractOp::with_variable(spec, v)),
        Imm::Constant(c) => AbstractOp::with_immediate(spec, c.as_ref())
            .ok()
            .context(error::ImmediateTooLarge),
        Imm::Expression(e) => Ok(AbstractOp::with_expression(spec, e)),
    }
}

fn parse_operand(
    operand: pest::iterators::Pair<Rule>,
    size: u32,
) -> Result<Imm<Vec<u8>>, ParseError> {
    let imm = match operand.as_rule() {
        Rule::math_expr => match parse_expr(operand)? {
            Expression::Label(lbl) => Imm::<Vec<u8>>::Label(lbl),
            Expression::Number(n) => {
                let msb = 128 - n.leading_zeros();
                let mut len = (msb / 8) as usize;
                if msb % 8 != 0 {
                    len += 1;
                }
                len = std::cmp::max(len, size as usize);
                Imm::from(n.to_be_bytes()[16 - len..].to_vec())
            }
            Expression::Hex(s) => Imm::from(hex::decode(&s[2..]).unwrap()),
            e => Imm::with_expression(e),
        },
        Rule::selector => {
            let raw = operand.into_inner().next().unwrap().as_str();
            let mut hasher = Keccak256::new();
            hasher.update(raw.as_bytes());
            Imm::from(hasher.finalize()[0..size as usize].to_vec())
        }
        Rule::instruction_macro_variable => {
            let variable = operand
                .as_str()
                .strip_prefix('$')
                .expect("variable didn't start with '$'");
            Imm::<Vec<u8>>::Variable(variable.to_string())
        }
        r => unreachable!(format!("{:?}", r)),
    };

    Ok(imm)
}

fn parse_expr(pair: pest::iterators::Pair<Rule>) -> Result<Expression, ParseError> {
    let climber = PrecClimber::new(vec![
        Operator::new(Rule::plus, Assoc::Left) | Operator::new(Rule::minus, Assoc::Left),
        Operator::new(Rule::times, Assoc::Left) | Operator::new(Rule::divide, Assoc::Left),
    ]);

    fn consume(pair: Pair<Rule>, climber: &PrecClimber<Rule>) -> Expression {
        let primary = |pair| consume(pair, climber);
        let infix = |lhs: Expression, op: Pair<Rule>, rhs: Expression| match op.as_rule() {
            Rule::plus => Expression::Plus(Box::new(lhs), Box::new(rhs)),
            Rule::minus => Expression::Minus(Box::new(lhs), Box::new(rhs)),
            Rule::times => Expression::Times(Box::new(lhs), Box::new(rhs)),
            Rule::divide => Expression::Divide(Box::new(lhs), Box::new(rhs)),
            _ => unreachable!(),
        };

        match pair.as_rule() {
            Rule::math_expr => climber.climb(pair.into_inner(), primary, infix),
            Rule::binary => {
                Expression::Number(i128::from_str_radix(&pair.as_str()[2..], 2).unwrap())
            }
            Rule::decimal | Rule::int => Expression::Number(str::parse(pair.as_str()).unwrap()),
            Rule::octal => {
                Expression::Number(i128::from_str_radix(&pair.as_str()[2..], 8).unwrap())
            }
            Rule::hex => Expression::Hex(pair.as_str().to_string()),
            Rule::label => Expression::Label(pair.as_str().to_string()),
            r => panic!("unsupport expression primary: {:?}, {:?}", r, pair.as_str()),
        }
    }

    Ok(consume(pair, &climber))
}

fn parse_instruction_macro(pair: pest::iterators::Pair<Rule>) -> Result<Node, ParseError> {
    let mut pairs = pair.into_inner();

    let mut macro_defn = pairs.next().unwrap().into_inner();
    let name = macro_defn.next().unwrap();
    let mut parameters = Vec::<String>::new();
    for pair in macro_defn {
        parameters.push(pair.as_str().into());
    }

    let mut contents = Vec::<AbstractOp>::new();

    for pair in pairs {
        match pair.as_rule() {
            Rule::label_definition => {
                let mut pair = pair.into_inner();
                let label = pair.next().unwrap();
                let txt = label.as_str();
                contents.push(AbstractOp::Label(txt.to_string()));
            }
            Rule::instruction_macro_push => {
                contents.push(parse_push(pair)?);
            }
            Rule::op => {
                let spec: Specifier = pair.as_str().parse().unwrap();
                let op = Op::new(spec).unwrap();
                let aop = AbstractOp::Op(op);
                contents.push(aop);
            }
            _ => continue,
        }
    }

    let defn = InstructionMacroDefinition {
        name: name.as_str().to_string(),
        parameters,
        contents,
    };
    Ok(AbstractOp::MacroDefinition(defn).into())
}

fn parse_builtin(pair: pest::iterators::Pair<Rule>) -> Result<Node, ParseError> {
    let rule = pair.as_rule();

    let node = match rule {
        Rule::import => {
            let args = <(PathBuf,)>::parse_arguments(pair.into_inner())?;
            Node::Import(args.0)
        }
        Rule::include => {
            let args = <(PathBuf,)>::parse_arguments(pair.into_inner())?;
            Node::Include(args.0)
        }
        Rule::include_hex => {
            let args = <(PathBuf,)>::parse_arguments(pair.into_inner())?;
            Node::IncludeHex(args.0)
        }
        Rule::push_macro => {
            // TODO: This should accept labels, literals, or variables, not just labels.
            let args = <(Label,)>::parse_arguments(pair.into_inner())?;
            let arg = Imm::with_label(args.0 .0);
            Node::Op(AbstractOp::Push(arg))
        }
        _ => unreachable!(),
    };
    Ok(node)
}

#[cfg(test)]
mod tests {
    use assert_matches::assert_matches;

    use crate::ops::Imm;

    use hex_literal::hex;

    use super::*;

    macro_rules! nodes {
        ($($x:expr),+ $(,)?) => (
            vec![$(Node::from($x)),+]
        );
    }

    #[test]
    fn parse_ops() {
        let asm = r#"
            stop
            pc
            gas
            xor
        "#;
        let expected = nodes![Op::Stop, Op::GetPc, Op::Gas, Op::Xor];
        assert_matches!(parse_asm(asm), Ok(e) if e == expected);
    }

    #[test]
    fn parse_single_line() {
        let asm = r#"
            push1 0b0; push1 0b1
        "#;
        let expected = nodes![Op::Push1(Imm::from([0])), Op::Push1(Imm::from([1]))];
        assert_matches!(parse_asm(asm), Ok(e) if e == expected);
    }

    #[test]
    fn parse_mixed_lines() {
        let asm = r#"
            push1 0b0; push1 0b1
            push1 0b1
        "#;
        let expected = nodes![
            Op::Push1(Imm::from([0])),
            Op::Push1(Imm::from([1])),
            Op::Push1(Imm::from([1]))
        ];
        assert_matches!(parse_asm(asm), Ok(e) if e == expected);
    }

    #[test]
    fn parse_push_binary() {
        let asm = r#"
            # simple cases
            push1 0b0
            push1 0b1
        "#;
        let expected = nodes![Op::Push1(Imm::from([0])), Op::Push1(Imm::from([1]))];
        assert_matches!(parse_asm(asm), Ok(e) if e == expected);
    }

    #[test]
    fn parse_push_octal() {
        let asm = r#"
            # simple cases
            push1 0o0
            push1 0o7
            push2 0o400
        "#;
        let expected = nodes![
            Op::Push1(Imm::from([0])),
            Op::Push1(Imm::from([7])),
            Op::Push2(Imm::from([1, 0])),
        ];
        assert_matches!(parse_asm(asm), Ok(e) if e == expected);
    }

    #[test]
    fn parse_push_decimal() {
        let asm = r#"
            # simple cases
            push1 0
            push1 1

            # left-pad values too small
            push2 42

            # barely enough for 2 bytes
            push2 256

            # just enough for 4 bytes
            push4 4294967295
        "#;
        let expected = nodes![
            Op::Push1(Imm::from([0])),
            Op::Push1(Imm::from([1])),
            Op::Push2(Imm::from([0, 42])),
            Op::Push2(Imm::from(hex!("0100"))),
            Op::Push4(Imm::from(hex!("ffffffff"))),
        ];
        assert_matches!(parse_asm(asm), Ok(e) if e == expected);

        let asm = "push1 256";
        assert_matches!(parse_asm(asm), Err(ParseError::ImmediateTooLarge { .. }));
    }

    #[test]
    fn parse_push_hex() {
        let asm = r#"
            push1 0x01 # comment
            push1 0x42
            push2 0x0102
            push4 0x01020304
            push8 0x0102030405060708
            push16 0x0102030405060708090a0b0c0d0e0f10
            push24 0x0102030405060708090a0b0c0d0e0f101112131415161718
            push32 0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20
        "#;
        let expected = nodes![
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
        assert_matches!(parse_asm(asm), Ok(e) if e == expected);

        let asm = "push2 0x010203";
        assert_matches!(parse_asm(asm), Err(ParseError::ImmediateTooLarge { .. }));
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
        let expected = nodes![
            Op::Swap1,
            Op::Swap4,
            Op::Swap16,
            Op::Dup1,
            Op::Dup4,
            Op::Dup16,
            Op::Log0,
            Op::Log4,
        ];
        assert_matches!(parse_asm(asm), Ok(e) if e == expected);
    }

    #[test]
    fn parse_jumpdest_no_label() {
        let asm = "jumpdest";
        let expected = nodes![Op::JumpDest];
        assert_matches!(parse_asm(asm), Ok(e) if e == expected);
    }

    #[test]
    fn parse_jumpdest_label() {
        let asm = "start:\njumpdest";
        let expected = nodes![AbstractOp::Label("start".into()), Op::JumpDest,];
        assert_matches!(parse_asm(asm), Ok(e) if e == expected);
    }

    #[test]
    fn parse_push_label() {
        let asm = r#"
            push2 snake_case
            jumpi
        "#;
        let expected = nodes![Op::Push2(Imm::with_label("snake_case")), Op::JumpI];
        assert_matches!(parse_asm(asm), Ok(e) if e == expected);
    }

    #[test]
    fn parse_push_op_as_label() {
        let asm = r#"
            push1:
            push1 push1
            jumpi
        "#;
        let expected = nodes![
            AbstractOp::Label("push1".into()),
            Op::Push1(Imm::with_label("push1")),
            Op::JumpI
        ];
        assert_matches!(parse_asm(asm), Ok(e) if e == expected);
    }

    #[test]
    fn parse_selector() {
        let asm = r#"
            push4 selector("name()")
            push4 selector("balanceOf(address)")
            push4 selector("transfer(address,uint256)")
            push4 selector("approve(address,uint256)")
            push32 selector("transfer(address,uint256)")
        "#;
        let expected = nodes![
            Op::Push4(Imm::from(hex!("06fdde03"))),
            Op::Push4(Imm::from(hex!("70a08231"))),
            Op::Push4(Imm::from(hex!("a9059cbb"))),
            Op::Push4(Imm::from(hex!("095ea7b3"))),
            Op::Push32(Imm::from(hex!(
                "a9059cbb2ab09eb219583f4a59a5d0623ade346d962bcd4e46b11da047c9049b"
            ))),
        ];
        assert_matches!(parse_asm(asm), Ok(e) if e == expected);
    }

    #[test]
    fn parse_selector_with_spaces() {
        let asm = r#"
            push4 selector("name( )")
        "#;
        assert_matches!(parse_asm(asm), Err(ParseError::Lexer { .. }));
    }

    #[test]
    fn parse_include() {
        let asm = format!(
            r#"
            push1 1
            %include("foo.asm")
            push1 2
            "#,
        );
        let expected = nodes![
            Op::Push1(Imm::from(1)),
            Node::Include(PathBuf::from("foo.asm")),
            Op::Push1(Imm::from(2)),
        ];
        assert_matches!(parse_asm(&asm), Ok(e) if e == expected)
    }

    #[test]
    fn parse_include_hex() {
        let asm = format!(
            r#"
            push1 1
            %include_hex("foo.hex")
            push1 2
            "#,
        );
        let expected = nodes![
            Op::Push1(Imm::from(1)),
            Node::IncludeHex(PathBuf::from("foo.hex")),
            Op::Push1(Imm::from(2)),
        ];
        assert_matches!(parse_asm(&asm), Ok(e) if e == expected)
    }

    #[test]
    fn parse_import() {
        let asm = format!(
            r#"
            push1 1
            %import("foo.asm")
            push1 2
            "#,
        );
        let expected = nodes![
            Op::Push1(Imm::from(1)),
            Node::Import(PathBuf::from("foo.asm")),
            Op::Push1(Imm::from(2)),
        ];
        assert_matches!(parse_asm(&asm), Ok(e) if e == expected)
    }

    #[test]
    fn parse_import_extra_argument() {
        let asm = format!(
            r#"
            %import("foo.asm", "bar.asm")
            "#,
        );
        assert!(matches!(
            parse_asm(&asm),
            Err(ParseError::ExtraArgument {
                expected: 1,
                backtrace: _
            })
        ))
    }

    #[test]
    fn parse_import_missing_argument() {
        let asm = format!(
            r#"
            %import()
            "#,
        );
        assert!(matches!(
            parse_asm(&asm),
            Err(ParseError::MissingArgument {
                got: 0,
                expected: 1,
                backtrace: _,
            })
        ))
    }

    #[test]
    fn parse_import_argument_type() {
        let asm = format!(
            r#"
            %import(0x44)
            "#,
        );
        assert_matches!(parse_asm(&asm), Err(ParseError::ArgumentType { .. }))
    }

    #[test]
    fn parse_import_spaces() {
        let asm = format!(
            r#"
            push1 1
            %import( "hello.asm" )
            push1 2
            "#,
        );
        let expected = nodes![
            Op::Push1(Imm::from(1)),
            Node::Import(PathBuf::from("hello.asm")),
            Op::Push1(Imm::from(2)),
        ];
        assert_matches!(parse_asm(&asm), Ok(e) if e == expected)
    }

    #[test]
    fn parse_push_macro_with_label() {
        let asm = format!(
            r#"
            push1 1
            %push( hello )
            push1 2
            "#,
        );
        let expected = nodes![
            Op::Push1(Imm::from(1)),
            AbstractOp::Push(Imm::with_label("hello")),
            Op::Push1(Imm::from(2)),
        ];
        assert_matches!(parse_asm(&asm), Ok(e) if e == expected)
    }

    #[test]
    fn parse_instruction_macro() {
        let asm = format!(
            r#"
            %macro my_macro(foo, bar)
                gasprice
                pop
                push1 $foo
                push1 $bar
            %end
            %my_macro(0x42, 10)
            "#,
        );
        let expected = nodes![
            AbstractOp::MacroDefinition(InstructionMacroDefinition {
                name: "my_macro".into(),
                parameters: vec!["foo".into(), "bar".into()],
                contents: vec![
                    Op::GasPrice.into(),
                    Op::Pop.into(),
                    AbstractOp::Op(Op::Push1(Imm::with_variable("foo"))),
                    AbstractOp::Op(Op::Push1(Imm::with_variable("bar"))),
                ]
            }),
            AbstractOp::Macro(InstructionMacroInvocation {
                name: "my_macro".into(),
                parameters: vec![
                    Imm::from(vec![0x42]),
                    Imm::from(vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10])
                ]
            })
        ];
        println!("{:?}", parse_asm(&asm));
        println!("{:?}", expected);
        assert_matches!(parse_asm(&asm), Ok(e) if e == expected)
    }

    #[test]
    fn parse_expression() {
        let asm = format!(
            r#"
            push1 1+1
            push1 2*foo
            push1 (1+(2*foo))-(bar/42)
            push1 0x20+0o1+0b10
            "#,
        );
        let expected = nodes![
            Op::Push1(Imm::with_expression(Expression::Plus(
                Box::new(Expression::Number(1)),
                Box::new(Expression::Number(1))
            ))),
            Op::Push1(Imm::with_expression(Expression::Times(
                Box::new(Expression::Number(2)),
                Box::new(Expression::Label("foo".into()))
            ))),
            Op::Push1(Imm::with_expression(Expression::Minus(
                Box::new(Expression::Plus(
                    Box::new(Expression::Number(1)),
                    Box::new(Expression::Times(
                        Box::new(Expression::Number(2)),
                        Box::new(Expression::Label("foo".into()))
                    ))
                )),
                Box::new(Expression::Divide(
                    Box::new(Expression::Label("bar".into())),
                    Box::new(Expression::Number(42))
                ))
            ))),
            Op::Push1(Imm::with_expression(Expression::Plus(
                Box::new(Expression::Plus(
                    Box::new(Expression::Hex("0x20".into())),
                    Box::new(Expression::Number(1))
                )),
                Box::new(Expression::Number(2))
            )))
        ];
        assert_matches!(parse_asm(&asm), Ok(e) if e == expected)
    }
}
