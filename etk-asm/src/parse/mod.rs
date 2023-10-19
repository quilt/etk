mod args;
mod expression;
mod macros;

pub(crate) mod error;
mod parser {
    #![allow(clippy::upper_case_acronyms)]

    use pest_derive::Parser;

    #[derive(Parser)]
    #[grammar = "parse/asm.pest"]
    pub(super) struct AsmParser;
}

use std::convert::TryInto;

use self::{
    error::ParseError,
    parser::{AsmParser, Rule},
};

use crate::ast::Node;
use crate::ops::AbstractOp;
use num_bigint::BigInt;
use pest::{iterators::Pair, Parser};

pub(crate) fn parse_asm(asm: &str) -> Result<Vec<Node>, ParseError> {
    let mut program: Vec<Node> = Vec::new();

    let pairs = AsmParser::parse(Rule::program, asm)?;
    for pair in pairs {
        let node = match pair.as_rule() {
            Rule::builtin => macros::parse_builtin(pair)?,
            Rule::EOI => continue,
            _ => parse_abstract_op(pair)?.into(),
        };
        program.push(node);
    }

    Ok(program)
}

fn parse_abstract_op(pair: Pair<Rule>) -> Result<AbstractOp, ParseError> {
    let ret = match pair.as_rule() {
        Rule::local_macro => macros::parse(pair)?,
        Rule::label_definition => {
            AbstractOp::Label(pair.into_inner().next().unwrap().as_str().to_string())
        }
        Rule::push => parse_push(pair)?,
        Rule::op => {
            let spec: Op<()> = pair.as_str().parse().unwrap();
            let op = Op::new(spec).unwrap();
            AbstractOp::Op(op)
        }
        _ => unreachable!(),
    };

    Ok(ret)
}

fn parse_push(pair: Pair<Rule>) -> Result<AbstractOp, ParseError> {
    let mut pair = pair.into_inner();
    let size = pair.next().unwrap();
    let size: usize = size.as_str().parse().unwrap();
    let operand = pair.next().unwrap();

    let spec = Op::<()>::push(size).unwrap();
    let expr = expression::parse(operand)?;

    if let Ok(val) = expr.eval() {
        let max = BigInt::pow(&BigInt::from(2u32), (8 * size).try_into().unwrap());
        if val >= max {
            return error::ImmediateTooLarge.fail();
        }
    }

    Ok(AbstractOp::Op(spec.with(expr).unwrap()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ops::{
        Expression, ExpressionMacroDefinition, ExpressionMacroInvocation, Imm,
        InstructionMacroDefinition, InstructionMacroInvocation, Terminal,
    };
    use assert_matches::assert_matches;
    use etk_ops::cancun::*;
    use hex_literal::hex;
    use num_bigint::Sign;
    use std::path::PathBuf;

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
            push0
        "#;
        let expected = nodes![
            Op::from(Stop),
            Op::from(GetPc),
            Op::from(Gas),
            Op::from(Xor),
            Op::from(Push0)
        ];
        assert_matches!(parse_asm(asm), Ok(e) if e == expected);
    }

    #[test]
    fn parse_single_line() {
        let asm = r#"
            push1 0b0; push1 0b1
        "#;
        let expected = nodes![
            Op::from(Push1(Imm::from([0]))),
            Op::from(Push1(Imm::from([1])))
        ];
        assert_matches!(parse_asm(asm), Ok(e) if e == expected);
    }

    #[test]
    fn parse_mixed_lines() {
        let asm = r#"
            push1 0b0; push1 0b1
            push1 0b1
        "#;
        let expected = nodes![
            Op::from(Push1(Imm::from([0]))),
            Op::from(Push1(Imm::from([1]))),
            Op::from(Push1(Imm::from([1])))
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
        let expected = nodes![
            Op::from(Push1(Imm::from([0]))),
            Op::from(Push1(Imm::from([1])))
        ];
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
            Op::from(Push1(Imm::from([0]))),
            Op::from(Push1(Imm::from([7]))),
            Op::from(Push2(Imm::from([1, 0]))),
        ];
        println!("{:?}\n\n{:?}", parse_asm(asm), expected);
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
            Op::from(Push1(0u8.into())),
            Op::from(Push1(Imm::from([1]))),
            Op::from(Push2(Imm::from([0, 42]))),
            Op::from(Push2(Imm::from(hex!("0100")))),
            Op::from(Push4(Imm::from(hex!("ffffffff")))),
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
            Op::from(Push1(Imm::from(hex!("01")))),
            Op::from(Push1(Imm::from(hex!("42")))),
            Op::from(Push2(Imm::from(hex!("0102")))),
            Op::from(Push4(Imm::from(hex!("01020304")))),
            Op::from(Push8(Imm::from(hex!("0102030405060708")))),
            Op::from(Push16(Imm::from(hex!("0102030405060708090a0b0c0d0e0f10")))),
            Op::from(Push24(Imm::from(hex!(
                "0102030405060708090a0b0c0d0e0f101112131415161718"
            )))),
            Op::from(Push32(Imm::from(hex!(
                "0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20"
            )))),
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
            Op::from(Swap1),
            Op::from(Swap4),
            Op::from(Swap16),
            Op::from(Dup1),
            Op::from(Dup4),
            Op::from(Dup16),
            Op::from(Log0),
            Op::from(Log4),
        ];
        assert_matches!(parse_asm(asm), Ok(e) if e == expected);
    }

    #[test]
    fn parse_jumpdest_no_label() {
        let asm = "jumpdest";
        let expected = nodes![Op::from(JumpDest)];
        assert_matches!(parse_asm(asm), Ok(e) if e == expected);
    }

    #[test]
    fn parse_jumpdest_label() {
        let asm = "start:\njumpdest";
        let expected = nodes![AbstractOp::Label("start".into()), Op::from(JumpDest),];
        assert_matches!(parse_asm(asm), Ok(e) if e == expected);
    }

    #[test]
    fn parse_push_label() {
        let asm = r#"
            push2 snake_case
            jumpi
        "#;
        let expected = nodes![
            Op::from(Push2(Imm::with_label("snake_case"))),
            Op::from(JumpI)
        ];
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
            Op::from(Push1(Imm::with_label("push1"))),
            Op::from(JumpI),
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
            push32 topic("transfer(address,uint256)")
        "#;
        let expected = nodes![
            Op::from(Push4(Imm::from(hex!("06fdde03")))),
            Op::from(Push4(Imm::from(hex!("70a08231")))),
            Op::from(Push4(Imm::from(hex!("a9059cbb")))),
            Op::from(Push4(Imm::from(hex!("095ea7b3")))),
            Op::from(Push32(Imm::from(hex!(
                "a9059cbb2ab09eb219583f4a59a5d0623ade346d962bcd4e46b11da047c9049b"
            )))),
        ];
        println!("{:?}\n\n{:?}", parse_asm(asm), expected);
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
            Op::from(Push1(Imm::from(1u8))),
            Node::Include(PathBuf::from("foo.asm")),
            Op::from(Push1(Imm::from(2u8))),
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
            Op::from(Push1(Imm::from(1u8))),
            Node::IncludeHex(PathBuf::from("foo.hex")),
            Op::from(Push1(Imm::from(2u8))),
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
            Op::from(Push1(Imm::from(1u8))),
            Node::Import(PathBuf::from("foo.asm")),
            Op::from(Push1(Imm::from(2u8))),
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
            Op::from(Push1(Imm::from(1u8))),
            Node::Import(PathBuf::from("hello.asm")),
            Op::from(Push1(Imm::from(2u8))),
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
            Op::from(Push1(Imm::from(1u8))),
            AbstractOp::Push(Imm::with_label("hello")),
            Op::from(Push1(Imm::from(2u8))),
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
                push1 $foo + $bar
                %push(0x42)
                %another_macro()
            %end
            %my_macro(0x42, 10)
            "#,
        );
        let expected = nodes![
            AbstractOp::MacroDefinition(
                InstructionMacroDefinition {
                    name: "my_macro".into(),
                    parameters: vec!["foo".into(), "bar".into()],
                    contents: vec![
                        AbstractOp::new(GasPrice),
                        AbstractOp::new(Pop),
                        AbstractOp::new(Push1(
                            Expression::Plus(
                                Terminal::Variable("foo".to_string()).into(),
                                Terminal::Variable("bar".to_string()).into()
                            )
                            .into()
                        )),
                        AbstractOp::Push(0x42u8.into()),
                        AbstractOp::Macro(InstructionMacroInvocation {
                            name: "another_macro".into(),
                            parameters: vec![]
                        })
                    ]
                }
                .into()
            ),
            AbstractOp::Macro(InstructionMacroInvocation {
                name: "my_macro".into(),
                parameters: vec![
                    BigInt::from_bytes_be(Sign::Plus, &vec![0x42]).into(),
                    BigInt::from_bytes_be(
                        Sign::Plus,
                        &vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10]
                    )
                    .into()
                ]
            })
        ];

        assert_eq!(parse_asm(&asm).unwrap(), expected)
    }

    #[test]
    fn parse_expression() {
        let asm = format!(
            r#"
            push1 1+-1
            push1 2*foo
            push1 (1+(2*foo))-(bar/42)
            push1 0x20+0o1+0b10
            "#,
        );
        let expected = nodes![
            Op::from(Push1(Imm::with_expression(Expression::Plus(
                1.into(),
                BigInt::from(-1).into(),
            )))),
            Op::from(Push1(Imm::with_expression(Expression::Times(
                2.into(),
                Terminal::Label("foo".into()).into()
            )))),
            Op::from(Push1(Imm::with_expression(Expression::Minus(
                Box::new(Expression::Plus(
                    1.into(),
                    Box::new(Expression::Times(
                        2.into(),
                        Terminal::Label("foo".into()).into()
                    ))
                )),
                Box::new(Expression::Divide(
                    Terminal::Label("bar".into()).into(),
                    42.into()
                ))
            )))),
            Op::from(Push1(Imm::with_expression(Expression::Plus(
                Box::new(Expression::Plus(
                    Terminal::Number(0x20.into()).into(),
                    1.into()
                )),
                2.into()
            ))))
        ];
        assert_eq!(parse_asm(&asm).unwrap(), expected)
    }

    #[test]
    fn parse_push_macro_with_expression() {
        let asm = format!(
            r#"
            push1 1
            %push( 1 + 1 )
            push1 2
            "#,
        );
        let expected = nodes![
            Op::from(Push1(Imm::from(1u8))),
            AbstractOp::Push(Imm::with_expression(Expression::Plus(1.into(), 1.into()))),
            Op::from(Push1(Imm::from(2u8))),
        ];
        assert_matches!(parse_asm(&asm), Ok(e) if e == expected)
    }

    #[test]
    fn parse_expression_macro() {
        let asm = format!(
            r#"
            %def foobar()
                1+2
            %end
            push1 foobar()
            "#,
        );
        let expected = nodes![
            ExpressionMacroDefinition {
                name: "foobar".into(),
                parameters: vec![],
                content: Imm::with_expression(Expression::Plus(1.into(), 2.into())),
            },
            Op::from(Push1(Imm::with_macro(ExpressionMacroInvocation {
                name: "foobar".into(),
                parameters: vec![]
            }))),
        ];
        assert_eq!(parse_asm(&asm).unwrap(), expected);
    }
}
