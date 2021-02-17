use crate::sym::{Expr, Var};

use gencfg_asm::ops::{Imm, Op};

use std::collections::{HashMap, VecDeque};
use std::convert::TryInto;

use super::BasicBlock;

#[derive(Debug, Clone)]
pub enum Exit {
    Terminate,
    Always(Expr),
    Branch {
        condition: Expr,
        when_true: Expr,
        when_false: usize,
    },
}

#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct Inputs {
    pub stack: Vec<Var>,
    pub storage: Vec<Expr>,
    pub memory: Vec<Expr>,
}

#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct Outputs {
    pub stack: Vec<Expr>,
    pub storage: HashMap<Expr, Expr>,
    pub memory: HashMap<Expr, Expr>,
}

#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct AnnotatedBlock {
    pub offset: usize,
    pub inputs: Inputs,
    pub outputs: Outputs,
    pub exit: Exit,
}

impl AnnotatedBlock {
    pub fn annotate(basic: &BasicBlock) -> Self {
        let mut annotator = Annotator::new(basic);
        let exit = annotator.annotate();

        let mut stacks = annotator.stacks.into_iter();
        let stack_inputs = stacks
            .next()
            .unwrap()
            .into_iter()
            .map(|i| i.as_var().unwrap())
            .collect();
        let stack_outputs = stacks.last().unwrap();

        Self {
            offset: basic.offset,
            outputs: Outputs {
                stack: stack_outputs.into(),
                memory: Default::default(),  // TODO
                storage: Default::default(), // TODO
            },
            inputs: Inputs {
                stack: stack_inputs,
                memory: Default::default(),  // TODO
                storage: Default::default(), // TODO
            },
            exit,
        }
    }
}

#[derive(Debug)]
struct Annotator<'a> {
    basic: &'a BasicBlock,
    vars: u16,
    stacks: Vec<VecDeque<Expr>>, // TODO: I don't think we actually need to keep the
                                 //       intermediary stacks. Probably only need the
                                 //       current, previous, and first.
}

impl<'a> Annotator<'a> {
    pub fn new(basic: &'a BasicBlock) -> Self {
        let mut stacks = Vec::with_capacity(basic.ops.len() + 1);
        stacks.push(VecDeque::new());

        Self {
            stacks,
            basic,
            vars: 0,
        }
    }

    fn expand_stack(&mut self, by: usize) {
        for _ in 0..by {
            self.vars += 1;
            let var = Var::with_id(self.vars);
            for stack in self.stacks.iter_mut() {
                stack.push_back(var.into());
            }
        }
    }

    fn advance(&mut self) {
        let last = self.stacks.last().cloned().unwrap_or_default();
        self.stacks.push(last);
    }

    fn current_stack(&mut self) -> &mut VecDeque<Expr> {
        self.stacks.last_mut().unwrap()
    }

    fn pop(&mut self) -> Expr {
        if self.current_stack().is_empty() {
            self.expand_stack(1);
        }

        self.current_stack().pop_front().unwrap()
    }

    fn peek(&mut self, depth: usize) -> &Expr {
        let len = self.current_stack().len();
        if len < depth + 1 {
            self.expand_stack(1 + depth - len);
        }

        self.current_stack().get(depth).unwrap()
    }

    fn swap(&mut self, depth: usize) {
        let len = self.current_stack().len();
        if len < depth + 1 {
            self.expand_stack(1 + depth - len);
        }

        let deep = self.current_stack().swap_remove_front(depth).unwrap();
        self.current_stack().push_front(deep);
    }

    fn push(&mut self, expr: Expr) {
        self.current_stack().push_front(expr);
    }

    fn push_const<A: AsRef<[u8]>>(&mut self, imm: &Imm<A>) {
        match imm {
            Imm::Constant(t) => self.push(Expr::constant(t)),
            Imm::Label(_) => panic!("unresolved label"),
        }
    }

    pub fn annotate(&mut self) -> Exit {
        let mut pc = self.basic.offset;

        for (idx, op) in self.basic.ops.iter().enumerate() {
            self.advance();
            let is_last = idx == self.basic.ops.len() - 1;

            match op {
                Op::Stop => {
                    assert!(is_last);
                    return Exit::Terminate;
                }

                Op::Add => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.add(&rhs));
                }

                Op::Mul => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.mul(&rhs));
                }

                Op::Sub => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.sub(&rhs));
                }

                Op::Div => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.div(&rhs));
                }
                Op::SDiv => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.s_div(&rhs));
                }
                Op::Mod => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.modulo(&rhs));
                }
                Op::SMod => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.s_modulo(&rhs));
                }
                Op::AddMod => {
                    let add0 = self.pop();
                    let add1 = self.pop();
                    let mod_ = self.pop();
                    self.push(add0.add_mod(&add1, &mod_))
                }
                Op::MulMod => {
                    let add0 = self.pop();
                    let add1 = self.pop();
                    let mod_ = self.pop();
                    self.push(add0.mul_mod(&add1, &mod_))
                }
                Op::Exp => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.exp(&rhs));
                }
                Op::SignExtend => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.sign_extend(&rhs));
                }

                Op::Lt => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.lt(&rhs));
                }
                Op::Gt => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.gt(&rhs));
                }
                Op::SLt => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.s_lt(&rhs));
                }
                Op::SGt => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.s_gt(&rhs));
                }
                Op::Eq => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.is_eq(&rhs));
                }
                Op::IsZero => {
                    let arg = self.pop().is_zero();
                    self.push(arg);
                }
                Op::And => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.and(&rhs));
                }
                Op::Or => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.or(&rhs));
                }
                Op::Xor => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.xor(&rhs));
                }
                Op::Not => {
                    let arg = self.pop().is_zero();
                    self.push(arg);
                }
                Op::Byte => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.byte(&rhs));
                }
                Op::Shl => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.shl(&rhs));
                }
                Op::Shr => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.shr(&rhs));
                }
                Op::Sar => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.sar(&rhs));
                }
                Op::Keccak256 => {
                    let offset = self.pop();
                    let length = self.pop();
                    self.push(Expr::keccak256(&offset, &length));
                }

                Op::Address => self.push(Expr::address()),
                Op::Balance => self.push(Expr::balance()),
                Op::Origin => self.push(Expr::origin()),
                Op::Caller => self.push(Expr::caller()),
                Op::CallValue => self.push(Expr::call_value()),
                Op::CallDataLoad => {
                    let offset = self.pop();
                    self.push(Expr::call_data_load(&offset));
                }
                Op::CodeSize => self.push(Expr::code_size()),
                Op::GasPrice => self.push(Expr::gas_price()),
                Op::ExtCodeSize => {
                    let address = self.pop();
                    self.push(Expr::ext_code_size(&address));
                }
                Op::BlockHash => self.push(Expr::block_hash()),
                Op::Coinbase => self.push(Expr::coinbase()),
                Op::Timestamp => self.push(Expr::timestamp()),
                Op::Number => self.push(Expr::number()),
                Op::Difficulty => self.push(Expr::difficulty()),
                Op::GasLimit => self.push(Expr::gas_limit()),
                Op::ChainId => self.push(Expr::chain_id()),

                Op::MSize => self.push(Expr::m_size()),
                Op::Gas => self.push(Expr::gas()),

                Op::Pop => {
                    self.pop();
                }

                Op::CallDataSize => self.push(Expr::call_data_size()),
                Op::CallDataCopy => {
                    let _dest_offset = self.pop();
                    let _offset = self.pop();
                    let _len = self.pop();
                    todo!("set memory")
                }

                Op::CodeCopy => {
                    let _dest_offset = self.pop();
                    let _offset = self.pop();
                    let _len = self.pop();
                    todo!("set memory")
                }

                Op::ExtCodeCopy => {
                    let _addr = self.pop();
                    let _dest_offset = self.pop();
                    let _offset = self.pop();
                    let _len = self.pop();
                    todo!("set memory")
                }
                Op::ReturnDataSize => self.push(Expr::return_data_size()),
                Op::ReturnDataCopy => {
                    let _dest_offset = self.pop();
                    let _offset = self.pop();
                    let _len = self.pop();
                    todo!()
                }
                Op::ExtCodeHash => {
                    let addr = self.pop();
                    self.push(Expr::ext_code_hash(&addr));
                }
                Op::MLoad => {
                    let addr = self.pop();
                    self.push(addr.m_load());
                }
                Op::MStore => {
                    let _addr = self.pop();
                    let _value = self.pop();
                    todo!("set memory");
                }
                Op::MStore8 => {
                    let _addr = self.pop();
                    let _value = self.pop();
                    todo!("set memory");
                }
                Op::SLoad => {
                    let addr = self.pop();
                    self.push(addr.s_load());
                }
                Op::SStore => {
                    let _key = self.pop();
                    let _value = self.pop();
                    todo!("set storage");
                }
                Op::GetPc => self.push(Expr::pc(pc as u16)),

                Op::BeginSub => {
                    // No-op
                }
                Op::JumpDest(_) => {
                    // No-op
                }

                Op::Push1(imm) => self.push_const(imm),
                Op::Push2(imm) => self.push_const(imm),
                Op::Push3(imm) => self.push_const(imm),
                Op::Push4(imm) => self.push_const(imm),
                Op::Push5(imm) => self.push_const(imm),
                Op::Push6(imm) => self.push_const(imm),
                Op::Push7(imm) => self.push_const(imm),
                Op::Push8(imm) => self.push_const(imm),
                Op::Push9(imm) => self.push_const(imm),
                Op::Push10(imm) => self.push_const(imm),
                Op::Push11(imm) => self.push_const(imm),
                Op::Push12(imm) => self.push_const(imm),
                Op::Push13(imm) => self.push_const(imm),
                Op::Push14(imm) => self.push_const(imm),
                Op::Push15(imm) => self.push_const(imm),
                Op::Push16(imm) => self.push_const(imm),
                Op::Push17(imm) => self.push_const(imm),
                Op::Push18(imm) => self.push_const(imm),
                Op::Push19(imm) => self.push_const(imm),
                Op::Push20(imm) => self.push_const(imm),
                Op::Push21(imm) => self.push_const(imm),
                Op::Push22(imm) => self.push_const(imm),
                Op::Push23(imm) => self.push_const(imm),
                Op::Push24(imm) => self.push_const(imm),
                Op::Push25(imm) => self.push_const(imm),
                Op::Push26(imm) => self.push_const(imm),
                Op::Push27(imm) => self.push_const(imm),
                Op::Push28(imm) => self.push_const(imm),
                Op::Push29(imm) => self.push_const(imm),
                Op::Push30(imm) => self.push_const(imm),
                Op::Push31(imm) => self.push_const(imm),
                Op::Push32(imm) => self.push_const(imm),

                Op::Dup1 => {
                    let arg = self.peek(0).clone();
                    self.push(arg)
                }
                Op::Dup2 => {
                    let arg = self.peek(1).clone();
                    self.push(arg)
                }
                Op::Dup3 => {
                    let arg = self.peek(2).clone();
                    self.push(arg)
                }
                Op::Dup4 => {
                    let arg = self.peek(3).clone();
                    self.push(arg)
                }
                Op::Dup5 => {
                    let arg = self.peek(4).clone();
                    self.push(arg)
                }
                Op::Dup6 => {
                    let arg = self.peek(5).clone();
                    self.push(arg)
                }
                Op::Dup7 => {
                    let arg = self.peek(6).clone();
                    self.push(arg)
                }
                Op::Dup8 => {
                    let arg = self.peek(7).clone();
                    self.push(arg)
                }
                Op::Dup9 => {
                    let arg = self.peek(8).clone();
                    self.push(arg)
                }
                Op::Dup10 => {
                    let arg = self.peek(9).clone();
                    self.push(arg)
                }
                Op::Dup11 => {
                    let arg = self.peek(10).clone();
                    self.push(arg)
                }
                Op::Dup12 => {
                    let arg = self.peek(11).clone();
                    self.push(arg)
                }
                Op::Dup13 => {
                    let arg = self.peek(12).clone();
                    self.push(arg)
                }
                Op::Dup14 => {
                    let arg = self.peek(13).clone();
                    self.push(arg)
                }
                Op::Dup15 => {
                    let arg = self.peek(14).clone();
                    self.push(arg)
                }
                Op::Dup16 => {
                    let arg = self.peek(15).clone();
                    self.push(arg)
                }

                Op::Log0 => {
                    let _offset = self.pop();
                    let _length = self.pop();
                }
                Op::Log1 => {
                    let _offset = self.pop();
                    let _length = self.pop();
                    let _topic0 = self.pop();
                }
                Op::Log2 => {
                    let _offset = self.pop();
                    let _length = self.pop();
                    let _topic0 = self.pop();
                    let _topic1 = self.pop();
                }
                Op::Log3 => {
                    let _offset = self.pop();
                    let _length = self.pop();
                    let _topic0 = self.pop();
                    let _topic1 = self.pop();
                    let _topic2 = self.pop();
                }
                Op::Log4 => {
                    let _offset = self.pop();
                    let _length = self.pop();
                    let _topic0 = self.pop();
                    let _topic1 = self.pop();
                    let _topic2 = self.pop();
                    let _topic3 = self.pop();
                }

                Op::Swap1 => self.swap(1),
                Op::Swap2 => self.swap(2),
                Op::Swap3 => self.swap(3),
                Op::Swap4 => self.swap(4),
                Op::Swap5 => self.swap(5),
                Op::Swap6 => self.swap(6),
                Op::Swap7 => self.swap(7),
                Op::Swap8 => self.swap(8),
                Op::Swap9 => self.swap(9),
                Op::Swap10 => self.swap(10),
                Op::Swap11 => self.swap(11),
                Op::Swap12 => self.swap(12),
                Op::Swap13 => self.swap(13),
                Op::Swap14 => self.swap(14),
                Op::Swap15 => self.swap(15),
                Op::Swap16 => self.swap(16),

                Op::Revert | Op::Return => {
                    assert!(is_last);
                    let _offset = self.pop();
                    let _length = self.pop();
                    return Exit::Terminate;
                }

                Op::SelfDestruct => {
                    let _addr = self.pop();
                    return Exit::Terminate;
                }

                Op::Jump => {
                    assert!(is_last);
                    let dest = self.pop();
                    return Exit::Always(dest);
                }

                Op::JumpI => {
                    assert!(is_last);
                    let when_false = pc + 1;
                    let when_true = self.pop();
                    let condition = self.pop();
                    return Exit::Branch {
                        when_false,
                        when_true,
                        condition,
                    };
                }

                Op::Create => {
                    let value = self.pop();
                    let offset = self.pop();
                    let length = self.pop();
                    self.push(Expr::create(&value, &offset, &length))
                }

                Op::Call => {
                    let gas = self.pop();
                    let addr = self.pop();
                    let value = self.pop();
                    let args_offset = self.pop();
                    let args_len = self.pop();
                    let ret_offset = self.pop();
                    let ret_len = self.pop();
                    self.push(Expr::call(
                        &gas,
                        &addr,
                        &value,
                        &args_offset,
                        &args_len,
                        &ret_offset,
                        &ret_len,
                    ))
                }

                Op::CallCode => {
                    let gas = self.pop();
                    let addr = self.pop();
                    let value = self.pop();
                    let args_offset = self.pop();
                    let args_len = self.pop();
                    let ret_offset = self.pop();
                    let ret_len = self.pop();
                    self.push(Expr::call_code(
                        &gas,
                        &addr,
                        &value,
                        &args_offset,
                        &args_len,
                        &ret_offset,
                        &ret_len,
                    ))
                }

                Op::DelegateCall => {
                    let gas = self.pop();
                    let addr = self.pop();
                    let args_offset = self.pop();
                    let args_len = self.pop();
                    let ret_offset = self.pop();
                    let ret_len = self.pop();
                    self.push(Expr::delegate_call(
                        &gas,
                        &addr,
                        &args_offset,
                        &args_len,
                        &ret_offset,
                        &ret_len,
                    ))
                }

                Op::Create2 => {
                    let value = self.pop();
                    let offset = self.pop();
                    let length = self.pop();
                    let salt = self.pop();
                    self.push(Expr::create2(&value, &offset, &length, &salt))
                }

                Op::StaticCall => {
                    let gas = self.pop();
                    let addr = self.pop();
                    let args_offset = self.pop();
                    let args_len = self.pop();
                    let ret_offset = self.pop();
                    let ret_len = self.pop();
                    self.push(Expr::static_call(
                        &gas,
                        &addr,
                        &args_offset,
                        &args_len,
                        &ret_offset,
                        &ret_len,
                    ))
                }

                Op::JumpTo
                | Op::TxExecGas
                | Op::JumpIf
                | Op::JumpSub
                | Op::JumpSubV
                | Op::BeginData
                | Op::ReturnSub
                | Op::PutLocal
                | Op::GetLocal
                | Op::SLoadBytes
                | Op::SStoreBytes
                | Op::SSize
                | Op::Invalid
                | Op::Invalid0c
                | Op::Invalid0d
                | Op::Invalid0e
                | Op::Invalid0f
                | Op::Invalid1e
                | Op::Invalid1f
                | Op::Invalid21
                | Op::Invalid22
                | Op::Invalid23
                | Op::Invalid24
                | Op::Invalid25
                | Op::Invalid26
                | Op::Invalid27
                | Op::Invalid28
                | Op::Invalid29
                | Op::Invalid2a
                | Op::Invalid2b
                | Op::Invalid2c
                | Op::Invalid2d
                | Op::Invalid2e
                | Op::Invalid2f
                | Op::Invalid47
                | Op::Invalid48
                | Op::Invalid49
                | Op::Invalid4a
                | Op::Invalid4b
                | Op::Invalid4c
                | Op::Invalid4d
                | Op::Invalid4e
                | Op::Invalid4f
                | Op::Invalid5c
                | Op::Invalid5d
                | Op::Invalid5e
                | Op::Invalid5f
                | Op::InvalidA5
                | Op::InvalidA6
                | Op::InvalidA7
                | Op::InvalidA8
                | Op::InvalidA9
                | Op::InvalidAa
                | Op::InvalidAb
                | Op::InvalidAc
                | Op::InvalidAd
                | Op::InvalidAe
                | Op::InvalidAf
                | Op::InvalidB3
                | Op::InvalidB7
                | Op::InvalidBb
                | Op::InvalidBc
                | Op::InvalidBd
                | Op::InvalidBe
                | Op::InvalidBf
                | Op::InvalidC0
                | Op::InvalidC1
                | Op::InvalidC2
                | Op::InvalidC3
                | Op::InvalidC4
                | Op::InvalidC5
                | Op::InvalidC6
                | Op::InvalidC7
                | Op::InvalidC8
                | Op::InvalidC9
                | Op::InvalidCa
                | Op::InvalidCb
                | Op::InvalidCc
                | Op::InvalidCd
                | Op::InvalidCe
                | Op::InvalidCf
                | Op::InvalidD0
                | Op::InvalidD1
                | Op::InvalidD2
                | Op::InvalidD3
                | Op::InvalidD4
                | Op::InvalidD5
                | Op::InvalidD6
                | Op::InvalidD7
                | Op::InvalidD8
                | Op::InvalidD9
                | Op::InvalidDa
                | Op::InvalidDb
                | Op::InvalidDc
                | Op::InvalidDd
                | Op::InvalidDe
                | Op::InvalidDf
                | Op::InvalidE0
                | Op::InvalidE4
                | Op::InvalidE5
                | Op::InvalidE6
                | Op::InvalidE7
                | Op::InvalidE8
                | Op::InvalidE9
                | Op::InvalidEa
                | Op::InvalidEb
                | Op::InvalidEc
                | Op::InvalidEd
                | Op::InvalidEe
                | Op::InvalidEf
                | Op::InvalidF6
                | Op::InvalidF7
                | Op::InvalidF8
                | Op::InvalidF9
                | Op::InvalidFb => {
                    assert!(is_last);
                    return Exit::Terminate;
                }
            }

            pc += op.specifier().extra_len() as usize + 1;
        }

        let exit_off: u128 = pc.try_into().unwrap();
        Exit::Always(Expr::constant_offset(exit_off))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    trait CheckExit {
        fn check(&self, actual: &Exit);
    }

    struct ExitTerminate;
    impl CheckExit for ExitTerminate {
        fn check(&self, actual: &Exit) {
            match actual {
                Exit::Terminate => (),
                wrong => panic!("expected {:?}, got {:?}", Exit::Terminate, wrong),
            }
        }
    }

    struct ExitAlways(Expr);

    impl CheckExit for ExitAlways {
        fn check(&self, actual: &Exit) {
            let exit = match actual {
                Exit::Always(expr) => expr,
                wrong => panic!("expected Exit::Always(...), got {:?}", wrong),
            };

            assert_eq!(&self.0, exit);
        }
    }

    #[must_use]
    struct AnnotateTest<O, E, I, P> {
        ops: O,
        expected_exit: E,
        expected_input_stack: I,
        expected_output_stack: P,
    }

    impl<O, Oi, E, I, Ii, P, Pi> AnnotateTest<O, E, I, P>
    where
        O: IntoIterator<Item = Oi>,
        Oi: Into<Op>,
        E: CheckExit,
        I: IntoIterator<Item = Ii>,
        Ii: Into<Expr>,
        P: IntoIterator<Item = Pi>,
        Pi: Into<Expr>,
    {
        fn check(self) {
            let basic = BasicBlock {
                offset: 0x1234,
                ops: self.ops.into_iter().map(Into::into).collect(),
            };

            let mut annotator = Annotator::new(&basic);
            let exit = annotator.annotate();
            self.expected_exit.check(&exit);

            let input_stack = annotator.stacks.first().unwrap();
            let expected_input_stack: Vec<_> = self
                .expected_input_stack
                .into_iter()
                .map(Into::into)
                .collect();
            assert_eq!(input_stack, &expected_input_stack, "input stack incorrect");

            let output_stack = annotator.stacks.last().unwrap();
            let expected_output_stack: Vec<_> = self
                .expected_output_stack
                .into_iter()
                .map(Into::into)
                .collect();
            assert_eq!(
                output_stack, &expected_output_stack,
                "output stack incorrect"
            );
        }
    }

    #[test]
    fn annotate_stop() {
        AnnotateTest {
            ops: vec![Op::Stop],
            expected_exit: ExitTerminate,
            expected_input_stack: Vec::<Expr>::new(),
            expected_output_stack: Vec::<Expr>::new(),
        }
        .check();
    }

    #[test]
    fn annotate_add() {
        AnnotateTest {
            ops: vec![Op::Add],
            expected_exit: ExitAlways(Expr::constant_offset(0x1235u64)),
            expected_input_stack: vec![Var::with_id(1), Var::with_id(2)],
            expected_output_stack: vec![Expr::add(
                &Var::with_id(1).into(),
                &Var::with_id(2).into(),
            )],
        }
        .check();
    }

    #[test]
    fn annotate_mul() {
        AnnotateTest {
            ops: vec![Op::Mul],
            expected_exit: ExitAlways(Expr::constant_offset(0x1235u64)),
            expected_input_stack: vec![Var::with_id(1), Var::with_id(2)],
            expected_output_stack: vec![Expr::mul(
                &Var::with_id(1).into(),
                &Var::with_id(2).into(),
            )],
        }
        .check();
    }

    #[test]
    fn annotate_sub() {
        AnnotateTest {
            ops: vec![Op::Sub],
            expected_exit: ExitAlways(Expr::constant_offset(0x1235u64)),
            expected_input_stack: vec![Var::with_id(1), Var::with_id(2)],
            expected_output_stack: vec![Expr::sub(
                &Var::with_id(1).into(),
                &Var::with_id(2).into(),
            )],
        }
        .check();
    }

    // TODO: Test the rest of the opcodes.

    #[test]
    fn annotate_swap1() {
        AnnotateTest {
            ops: vec![Op::Swap1],
            expected_exit: ExitAlways(Expr::constant_offset(0x1235u64)),
            expected_input_stack: vec![Var::with_id(1), Var::with_id(2)],
            expected_output_stack: vec![Var::with_id(2), Var::with_id(1)],
        }
        .check();
    }

    #[test]
    fn annotate_swap2() {
        AnnotateTest {
            ops: vec![Op::Swap2],
            expected_exit: ExitAlways(Expr::constant_offset(0x1235u64)),
            expected_input_stack: vec![Var::with_id(1), Var::with_id(2), Var::with_id(3)],
            expected_output_stack: vec![Var::with_id(3), Var::with_id(2), Var::with_id(1)],
        }
        .check();
    }

    #[test]
    fn annotate_swap3() {
        AnnotateTest {
            ops: vec![Op::Swap3],
            expected_exit: ExitAlways(Expr::constant_offset(0x1235u64)),
            expected_input_stack: (1..5).map(Var::with_id),
            expected_output_stack: vec![
                Var::with_id(4),
                Var::with_id(2),
                Var::with_id(3),
                Var::with_id(1),
            ],
        }
        .check();
    }

    #[test]
    fn annotate_dup1() {
        AnnotateTest {
            ops: vec![Op::Dup1],
            expected_exit: ExitAlways(Expr::constant_offset(0x1235u64)),
            expected_input_stack: vec![Var::with_id(1)],
            expected_output_stack: vec![Var::with_id(1), Var::with_id(1)],
        }
        .check();
    }

    #[test]
    fn annotate_dup2() {
        AnnotateTest {
            ops: vec![Op::Dup2],
            expected_exit: ExitAlways(Expr::constant_offset(0x1235u64)),
            expected_input_stack: vec![Var::with_id(1), Var::with_id(2)],
            expected_output_stack: vec![Var::with_id(2), Var::with_id(1), Var::with_id(2)],
        }
        .check();
    }

    #[test]
    fn annotate_dup3() {
        AnnotateTest {
            ops: vec![Op::Dup3],
            expected_exit: ExitAlways(Expr::constant_offset(0x1235u64)),
            expected_input_stack: vec![Var::with_id(1), Var::with_id(2), Var::with_id(3)],
            expected_output_stack: vec![
                Var::with_id(3),
                Var::with_id(1),
                Var::with_id(2),
                Var::with_id(3),
            ],
        }
        .check();
    }

    #[test]
    fn annotate_push1() {
        AnnotateTest {
            ops: vec![Op::Push1([77].into())],
            expected_exit: ExitAlways(Expr::constant_offset(0x1236u64)),
            expected_input_stack: Vec::<Expr>::new(),
            expected_output_stack: vec![Expr::constant_offset(77u8)],
        }
        .check();
    }

    #[test]
    fn annotate_push2() {
        AnnotateTest {
            ops: vec![Op::Push2([0x12, 0x34].into())],
            expected_exit: ExitAlways(Expr::constant_offset(0x1237u64)),
            expected_input_stack: Vec::<Expr>::new(),
            expected_output_stack: vec![Expr::constant_offset(0x1234u64)],
        }
        .check();
    }
}
