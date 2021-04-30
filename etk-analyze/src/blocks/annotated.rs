use crate::sym::{Expr, Var};

use etk_asm::ops::ConcreteOp;

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

    fn push_const<A: AsRef<[u8]>>(&mut self, imm: &A) {
        self.push(Expr::constant(imm))
    }

    pub fn annotate(&mut self) -> Exit {
        let mut pc = self.basic.offset;

        for (idx, op) in self.basic.ops.iter().enumerate() {
            self.advance();
            let is_last = idx == self.basic.ops.len() - 1;

            match op {
                ConcreteOp::Stop => {
                    assert!(is_last);
                    return Exit::Terminate;
                }

                ConcreteOp::Add => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.add(&rhs));
                }

                ConcreteOp::Mul => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.mul(&rhs));
                }

                ConcreteOp::Sub => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.sub(&rhs));
                }

                ConcreteOp::Div => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.div(&rhs));
                }
                ConcreteOp::SDiv => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.s_div(&rhs));
                }
                ConcreteOp::Mod => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.modulo(&rhs));
                }
                ConcreteOp::SMod => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.s_modulo(&rhs));
                }
                ConcreteOp::AddMod => {
                    let add0 = self.pop();
                    let add1 = self.pop();
                    let mod_ = self.pop();
                    self.push(add0.add_mod(&add1, &mod_))
                }
                ConcreteOp::MulMod => {
                    let add0 = self.pop();
                    let add1 = self.pop();
                    let mod_ = self.pop();
                    self.push(add0.mul_mod(&add1, &mod_))
                }
                ConcreteOp::Exp => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.exp(&rhs));
                }
                ConcreteOp::SignExtend => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.sign_extend(&rhs));
                }

                ConcreteOp::Lt => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.lt(&rhs));
                }
                ConcreteOp::Gt => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.gt(&rhs));
                }
                ConcreteOp::SLt => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.s_lt(&rhs));
                }
                ConcreteOp::SGt => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.s_gt(&rhs));
                }
                ConcreteOp::Eq => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.is_eq(&rhs));
                }
                ConcreteOp::IsZero => {
                    let arg = self.pop().is_zero();
                    self.push(arg);
                }
                ConcreteOp::And => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.and(&rhs));
                }
                ConcreteOp::Or => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.or(&rhs));
                }
                ConcreteOp::Xor => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.xor(&rhs));
                }
                ConcreteOp::Not => {
                    let arg = self.pop().not();
                    self.push(arg);
                }
                ConcreteOp::Byte => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.byte(&rhs));
                }
                ConcreteOp::Shl => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.shl(&rhs));
                }
                ConcreteOp::Shr => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.shr(&rhs));
                }
                ConcreteOp::Sar => {
                    let lhs = self.pop();
                    let rhs = self.pop();
                    self.push(lhs.sar(&rhs));
                }
                ConcreteOp::Keccak256 => {
                    let offset = self.pop();
                    let length = self.pop();
                    self.push(Expr::keccak256(&offset, &length));
                }

                ConcreteOp::Address => self.push(Expr::address()),
                ConcreteOp::Balance => self.push(Expr::balance()),
                ConcreteOp::Origin => self.push(Expr::origin()),
                ConcreteOp::Caller => self.push(Expr::caller()),
                ConcreteOp::CallValue => self.push(Expr::call_value()),
                ConcreteOp::CallDataLoad => {
                    let offset = self.pop();
                    self.push(Expr::call_data_load(&offset));
                }
                ConcreteOp::CodeSize => self.push(Expr::code_size()),
                ConcreteOp::GasPrice => self.push(Expr::gas_price()),
                ConcreteOp::ExtCodeSize => {
                    let address = self.pop();
                    self.push(Expr::ext_code_size(&address));
                }
                ConcreteOp::BlockHash => self.push(Expr::block_hash()),
                ConcreteOp::Coinbase => self.push(Expr::coinbase()),
                ConcreteOp::Timestamp => self.push(Expr::timestamp()),
                ConcreteOp::Number => self.push(Expr::number()),
                ConcreteOp::Difficulty => self.push(Expr::difficulty()),
                ConcreteOp::GasLimit => self.push(Expr::gas_limit()),
                ConcreteOp::ChainId => self.push(Expr::chain_id()),

                ConcreteOp::MSize => self.push(Expr::m_size()),
                ConcreteOp::Gas => self.push(Expr::gas()),

                ConcreteOp::Pop => {
                    self.pop();
                }

                ConcreteOp::CallDataSize => self.push(Expr::call_data_size()),
                ConcreteOp::CallDataCopy => {
                    let _dest_offset = self.pop();
                    let _offset = self.pop();
                    let _len = self.pop();
                    todo!("set memory")
                }

                ConcreteOp::CodeCopy => {
                    let _dest_offset = self.pop();
                    let _offset = self.pop();
                    let _len = self.pop();
                    todo!("set memory")
                }

                ConcreteOp::ExtCodeCopy => {
                    let _addr = self.pop();
                    let _dest_offset = self.pop();
                    let _offset = self.pop();
                    let _len = self.pop();
                    todo!("set memory")
                }
                ConcreteOp::ReturnDataSize => self.push(Expr::return_data_size()),
                ConcreteOp::ReturnDataCopy => {
                    let _dest_offset = self.pop();
                    let _offset = self.pop();
                    let _len = self.pop();
                    todo!()
                }
                ConcreteOp::ExtCodeHash => {
                    let addr = self.pop();
                    self.push(Expr::ext_code_hash(&addr));
                }
                ConcreteOp::MLoad => {
                    let addr = self.pop();
                    self.push(addr.m_load());
                }
                ConcreteOp::MStore => {
                    let _addr = self.pop();
                    let _value = self.pop();
                    todo!("set memory");
                }
                ConcreteOp::MStore8 => {
                    let _addr = self.pop();
                    let _value = self.pop();
                    todo!("set memory");
                }
                ConcreteOp::SLoad => {
                    let addr = self.pop();
                    self.push(addr.s_load());
                }
                ConcreteOp::SStore => {
                    let _key = self.pop();
                    let _value = self.pop();
                    todo!("set storage");
                }
                ConcreteOp::GetPc => self.push(Expr::pc(pc as u16)),

                ConcreteOp::BeginSub => {
                    // No-op
                }
                ConcreteOp::JumpDest => {
                    // No-op
                }

                ConcreteOp::Push1(imm) => self.push_const(imm),
                ConcreteOp::Push2(imm) => self.push_const(imm),
                ConcreteOp::Push3(imm) => self.push_const(imm),
                ConcreteOp::Push4(imm) => self.push_const(imm),
                ConcreteOp::Push5(imm) => self.push_const(imm),
                ConcreteOp::Push6(imm) => self.push_const(imm),
                ConcreteOp::Push7(imm) => self.push_const(imm),
                ConcreteOp::Push8(imm) => self.push_const(imm),
                ConcreteOp::Push9(imm) => self.push_const(imm),
                ConcreteOp::Push10(imm) => self.push_const(imm),
                ConcreteOp::Push11(imm) => self.push_const(imm),
                ConcreteOp::Push12(imm) => self.push_const(imm),
                ConcreteOp::Push13(imm) => self.push_const(imm),
                ConcreteOp::Push14(imm) => self.push_const(imm),
                ConcreteOp::Push15(imm) => self.push_const(imm),
                ConcreteOp::Push16(imm) => self.push_const(imm),
                ConcreteOp::Push17(imm) => self.push_const(imm),
                ConcreteOp::Push18(imm) => self.push_const(imm),
                ConcreteOp::Push19(imm) => self.push_const(imm),
                ConcreteOp::Push20(imm) => self.push_const(imm),
                ConcreteOp::Push21(imm) => self.push_const(imm),
                ConcreteOp::Push22(imm) => self.push_const(imm),
                ConcreteOp::Push23(imm) => self.push_const(imm),
                ConcreteOp::Push24(imm) => self.push_const(imm),
                ConcreteOp::Push25(imm) => self.push_const(imm),
                ConcreteOp::Push26(imm) => self.push_const(imm),
                ConcreteOp::Push27(imm) => self.push_const(imm),
                ConcreteOp::Push28(imm) => self.push_const(imm),
                ConcreteOp::Push29(imm) => self.push_const(imm),
                ConcreteOp::Push30(imm) => self.push_const(imm),
                ConcreteOp::Push31(imm) => self.push_const(imm),
                ConcreteOp::Push32(imm) => self.push_const(imm),

                ConcreteOp::Dup1 => {
                    let arg = self.peek(0).clone();
                    self.push(arg)
                }
                ConcreteOp::Dup2 => {
                    let arg = self.peek(1).clone();
                    self.push(arg)
                }
                ConcreteOp::Dup3 => {
                    let arg = self.peek(2).clone();
                    self.push(arg)
                }
                ConcreteOp::Dup4 => {
                    let arg = self.peek(3).clone();
                    self.push(arg)
                }
                ConcreteOp::Dup5 => {
                    let arg = self.peek(4).clone();
                    self.push(arg)
                }
                ConcreteOp::Dup6 => {
                    let arg = self.peek(5).clone();
                    self.push(arg)
                }
                ConcreteOp::Dup7 => {
                    let arg = self.peek(6).clone();
                    self.push(arg)
                }
                ConcreteOp::Dup8 => {
                    let arg = self.peek(7).clone();
                    self.push(arg)
                }
                ConcreteOp::Dup9 => {
                    let arg = self.peek(8).clone();
                    self.push(arg)
                }
                ConcreteOp::Dup10 => {
                    let arg = self.peek(9).clone();
                    self.push(arg)
                }
                ConcreteOp::Dup11 => {
                    let arg = self.peek(10).clone();
                    self.push(arg)
                }
                ConcreteOp::Dup12 => {
                    let arg = self.peek(11).clone();
                    self.push(arg)
                }
                ConcreteOp::Dup13 => {
                    let arg = self.peek(12).clone();
                    self.push(arg)
                }
                ConcreteOp::Dup14 => {
                    let arg = self.peek(13).clone();
                    self.push(arg)
                }
                ConcreteOp::Dup15 => {
                    let arg = self.peek(14).clone();
                    self.push(arg)
                }
                ConcreteOp::Dup16 => {
                    let arg = self.peek(15).clone();
                    self.push(arg)
                }

                ConcreteOp::Log0 => {
                    let _offset = self.pop();
                    let _length = self.pop();
                }
                ConcreteOp::Log1 => {
                    let _offset = self.pop();
                    let _length = self.pop();
                    let _topic0 = self.pop();
                }
                ConcreteOp::Log2 => {
                    let _offset = self.pop();
                    let _length = self.pop();
                    let _topic0 = self.pop();
                    let _topic1 = self.pop();
                }
                ConcreteOp::Log3 => {
                    let _offset = self.pop();
                    let _length = self.pop();
                    let _topic0 = self.pop();
                    let _topic1 = self.pop();
                    let _topic2 = self.pop();
                }
                ConcreteOp::Log4 => {
                    let _offset = self.pop();
                    let _length = self.pop();
                    let _topic0 = self.pop();
                    let _topic1 = self.pop();
                    let _topic2 = self.pop();
                    let _topic3 = self.pop();
                }

                ConcreteOp::Swap1 => self.swap(1),
                ConcreteOp::Swap2 => self.swap(2),
                ConcreteOp::Swap3 => self.swap(3),
                ConcreteOp::Swap4 => self.swap(4),
                ConcreteOp::Swap5 => self.swap(5),
                ConcreteOp::Swap6 => self.swap(6),
                ConcreteOp::Swap7 => self.swap(7),
                ConcreteOp::Swap8 => self.swap(8),
                ConcreteOp::Swap9 => self.swap(9),
                ConcreteOp::Swap10 => self.swap(10),
                ConcreteOp::Swap11 => self.swap(11),
                ConcreteOp::Swap12 => self.swap(12),
                ConcreteOp::Swap13 => self.swap(13),
                ConcreteOp::Swap14 => self.swap(14),
                ConcreteOp::Swap15 => self.swap(15),
                ConcreteOp::Swap16 => self.swap(16),

                ConcreteOp::Revert | ConcreteOp::Return => {
                    assert!(is_last);
                    let _offset = self.pop();
                    let _length = self.pop();
                    return Exit::Terminate;
                }

                ConcreteOp::SelfDestruct => {
                    let _addr = self.pop();
                    return Exit::Terminate;
                }

                ConcreteOp::Jump => {
                    assert!(is_last);
                    let dest = self.pop();
                    return Exit::Always(dest);
                }

                ConcreteOp::JumpI => {
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

                ConcreteOp::Create => {
                    let value = self.pop();
                    let offset = self.pop();
                    let length = self.pop();
                    self.push(Expr::create(&value, &offset, &length))
                }

                ConcreteOp::Call => {
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

                ConcreteOp::CallCode => {
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

                ConcreteOp::DelegateCall => {
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

                ConcreteOp::Create2 => {
                    let value = self.pop();
                    let offset = self.pop();
                    let length = self.pop();
                    let salt = self.pop();
                    self.push(Expr::create2(&value, &offset, &length, &salt))
                }

                ConcreteOp::StaticCall => {
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

                ConcreteOp::JumpTo
                | ConcreteOp::TxExecGas
                | ConcreteOp::JumpIf
                | ConcreteOp::JumpSub
                | ConcreteOp::JumpSubV
                | ConcreteOp::BeginData
                | ConcreteOp::ReturnSub
                | ConcreteOp::PutLocal
                | ConcreteOp::GetLocal
                | ConcreteOp::SLoadBytes
                | ConcreteOp::SStoreBytes
                | ConcreteOp::SSize
                | ConcreteOp::Invalid
                | ConcreteOp::Invalid0c
                | ConcreteOp::Invalid0d
                | ConcreteOp::Invalid0e
                | ConcreteOp::Invalid0f
                | ConcreteOp::Invalid1e
                | ConcreteOp::Invalid1f
                | ConcreteOp::Invalid21
                | ConcreteOp::Invalid22
                | ConcreteOp::Invalid23
                | ConcreteOp::Invalid24
                | ConcreteOp::Invalid25
                | ConcreteOp::Invalid26
                | ConcreteOp::Invalid27
                | ConcreteOp::Invalid28
                | ConcreteOp::Invalid29
                | ConcreteOp::Invalid2a
                | ConcreteOp::Invalid2b
                | ConcreteOp::Invalid2c
                | ConcreteOp::Invalid2d
                | ConcreteOp::Invalid2e
                | ConcreteOp::Invalid2f
                | ConcreteOp::Invalid47
                | ConcreteOp::Invalid48
                | ConcreteOp::Invalid49
                | ConcreteOp::Invalid4a
                | ConcreteOp::Invalid4b
                | ConcreteOp::Invalid4c
                | ConcreteOp::Invalid4d
                | ConcreteOp::Invalid4e
                | ConcreteOp::Invalid4f
                | ConcreteOp::Invalid5c
                | ConcreteOp::Invalid5d
                | ConcreteOp::Invalid5e
                | ConcreteOp::Invalid5f
                | ConcreteOp::InvalidA5
                | ConcreteOp::InvalidA6
                | ConcreteOp::InvalidA7
                | ConcreteOp::InvalidA8
                | ConcreteOp::InvalidA9
                | ConcreteOp::InvalidAa
                | ConcreteOp::InvalidAb
                | ConcreteOp::InvalidAc
                | ConcreteOp::InvalidAd
                | ConcreteOp::InvalidAe
                | ConcreteOp::InvalidAf
                | ConcreteOp::InvalidB3
                | ConcreteOp::InvalidB7
                | ConcreteOp::InvalidBb
                | ConcreteOp::InvalidBc
                | ConcreteOp::InvalidBd
                | ConcreteOp::InvalidBe
                | ConcreteOp::InvalidBf
                | ConcreteOp::InvalidC0
                | ConcreteOp::InvalidC1
                | ConcreteOp::InvalidC2
                | ConcreteOp::InvalidC3
                | ConcreteOp::InvalidC4
                | ConcreteOp::InvalidC5
                | ConcreteOp::InvalidC6
                | ConcreteOp::InvalidC7
                | ConcreteOp::InvalidC8
                | ConcreteOp::InvalidC9
                | ConcreteOp::InvalidCa
                | ConcreteOp::InvalidCb
                | ConcreteOp::InvalidCc
                | ConcreteOp::InvalidCd
                | ConcreteOp::InvalidCe
                | ConcreteOp::InvalidCf
                | ConcreteOp::InvalidD0
                | ConcreteOp::InvalidD1
                | ConcreteOp::InvalidD2
                | ConcreteOp::InvalidD3
                | ConcreteOp::InvalidD4
                | ConcreteOp::InvalidD5
                | ConcreteOp::InvalidD6
                | ConcreteOp::InvalidD7
                | ConcreteOp::InvalidD8
                | ConcreteOp::InvalidD9
                | ConcreteOp::InvalidDa
                | ConcreteOp::InvalidDb
                | ConcreteOp::InvalidDc
                | ConcreteOp::InvalidDd
                | ConcreteOp::InvalidDe
                | ConcreteOp::InvalidDf
                | ConcreteOp::InvalidE0
                | ConcreteOp::InvalidE4
                | ConcreteOp::InvalidE5
                | ConcreteOp::InvalidE6
                | ConcreteOp::InvalidE7
                | ConcreteOp::InvalidE8
                | ConcreteOp::InvalidE9
                | ConcreteOp::InvalidEa
                | ConcreteOp::InvalidEb
                | ConcreteOp::InvalidEc
                | ConcreteOp::InvalidEd
                | ConcreteOp::InvalidEe
                | ConcreteOp::InvalidEf
                | ConcreteOp::InvalidF6
                | ConcreteOp::InvalidF7
                | ConcreteOp::InvalidF8
                | ConcreteOp::InvalidF9
                | ConcreteOp::InvalidFb => {
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
        Oi: Into<ConcreteOp>,
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
            ops: vec![ConcreteOp::Stop],
            expected_exit: ExitTerminate,
            expected_input_stack: Vec::<Expr>::new(),
            expected_output_stack: Vec::<Expr>::new(),
        }
        .check();
    }

    #[test]
    fn annotate_add() {
        AnnotateTest {
            ops: vec![ConcreteOp::Add],
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
            ops: vec![ConcreteOp::Mul],
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
            ops: vec![ConcreteOp::Sub],
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
            ops: vec![ConcreteOp::Swap1],
            expected_exit: ExitAlways(Expr::constant_offset(0x1235u64)),
            expected_input_stack: vec![Var::with_id(1), Var::with_id(2)],
            expected_output_stack: vec![Var::with_id(2), Var::with_id(1)],
        }
        .check();
    }

    #[test]
    fn annotate_swap2() {
        AnnotateTest {
            ops: vec![ConcreteOp::Swap2],
            expected_exit: ExitAlways(Expr::constant_offset(0x1235u64)),
            expected_input_stack: vec![Var::with_id(1), Var::with_id(2), Var::with_id(3)],
            expected_output_stack: vec![Var::with_id(3), Var::with_id(2), Var::with_id(1)],
        }
        .check();
    }

    #[test]
    fn annotate_swap3() {
        AnnotateTest {
            ops: vec![ConcreteOp::Swap3],
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
            ops: vec![ConcreteOp::Dup1],
            expected_exit: ExitAlways(Expr::constant_offset(0x1235u64)),
            expected_input_stack: vec![Var::with_id(1)],
            expected_output_stack: vec![Var::with_id(1), Var::with_id(1)],
        }
        .check();
    }

    #[test]
    fn annotate_dup2() {
        AnnotateTest {
            ops: vec![ConcreteOp::Dup2],
            expected_exit: ExitAlways(Expr::constant_offset(0x1235u64)),
            expected_input_stack: vec![Var::with_id(1), Var::with_id(2)],
            expected_output_stack: vec![Var::with_id(2), Var::with_id(1), Var::with_id(2)],
        }
        .check();
    }

    #[test]
    fn annotate_dup3() {
        AnnotateTest {
            ops: vec![ConcreteOp::Dup3],
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
            ops: vec![ConcreteOp::Push1([77].into())],
            expected_exit: ExitAlways(Expr::constant_offset(0x1236u64)),
            expected_input_stack: Vec::<Expr>::new(),
            expected_output_stack: vec![Expr::constant_offset(77u8)],
        }
        .check();
    }

    #[test]
    fn annotate_push2() {
        AnnotateTest {
            ops: vec![ConcreteOp::Push2([0x12, 0x34].into())],
            expected_exit: ExitAlways(Expr::constant_offset(0x1237u64)),
            expected_input_stack: Vec::<Expr>::new(),
            expected_output_stack: vec![Expr::constant_offset(0x1234u64)],
        }
        .check();
    }
}
