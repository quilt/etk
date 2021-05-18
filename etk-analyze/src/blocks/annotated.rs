use crate::sym::{Expr, Var};

use etk_asm::ops::{ConcreteOp, Metadata};

use std::collections::{HashMap, VecDeque};

use super::BasicBlock;

#[derive(Debug, Clone)]
pub enum Exit<T = Expr> {
    Terminate,
    FallThrough(usize),
    Unconditional(T),
    Branch {
        condition: T,
        when_true: T,
        when_false: usize,
    },
}

impl<T> Exit<T> {
    pub fn fall_through(&self) -> Option<usize> {
        match self {
            Self::FallThrough(f) => Some(*f),
            Self::Branch { when_false, .. } => Some(*when_false),
            _ => None,
        }
    }

    pub fn is_fall_through(&self) -> bool {
        matches!(self, Self::FallThrough(_))
    }

    pub fn is_terminate(&self) -> bool {
        matches!(self, Self::Terminate)
    }

    pub fn is_unconditional(&self) -> bool {
        matches!(self, Self::Unconditional(_))
    }

    pub fn is_branch(&self) -> bool {
        matches!(self, Self::Branch { .. })
    }
}

#[cfg(feature = "z3")]
mod z3_exit {
    use super::*;

    use z3::ast::BV;

    impl Exit<Expr> {
        pub(crate) fn erase(&self) -> Exit<()> {
            match self {
                Self::Terminate => Exit::Terminate,
                Self::FallThrough(f) => Exit::FallThrough(*f),
                Self::Unconditional(_) => Exit::Unconditional(()),
                Self::Branch { when_false, .. } => Exit::Branch {
                    condition: (),
                    when_true: (),
                    when_false: *when_false,
                },
            }
        }

        pub(crate) fn to_z3<'z>(&self, context: &'z z3::Context) -> Exit<BV<'z>> {
            match self {
                Self::Terminate => Exit::Terminate,
                Self::FallThrough(f) => Exit::FallThrough(*f),
                Self::Unconditional(e) => Exit::Unconditional(e.to_z3(context)),
                Self::Branch {
                    when_true,
                    when_false,
                    condition,
                } => {
                    let when_true = when_true.to_z3(&context);
                    let condition = condition.to_z3(&context);

                    Exit::Branch {
                        when_false: *when_false,
                        when_true,
                        condition,
                    }
                }
            }
        }
    }
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
    pub jump_target: bool,
    pub size: usize,
}

impl AnnotatedBlock {
    pub fn annotate(basic: &BasicBlock) -> Self {
        let jump_target = basic
            .ops
            .get(0)
            .map(Metadata::is_jump_target)
            .unwrap_or_default();

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
            jump_target,
            size: basic.size(),
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

struct StackWindow<'s> {
    vars: &'s mut u16,
    stacks: &'s mut Vec<VecDeque<Expr>>,
    pops: usize,
    pushes: usize,
}

impl<'s> Drop for StackWindow<'s> {
    fn drop(&mut self) {
        if !std::thread::panicking() {
            assert_eq!(self.pops, 0);
            assert_eq!(self.pushes, 0);
        }
    }
}

impl<'s> StackWindow<'s> {
    fn new(vars: &'s mut u16, stacks: &'s mut Vec<VecDeque<Expr>>, op: &ConcreteOp) -> Self {
        Self {
            vars,
            stacks,
            pops: op.pops(),
            pushes: op.pushes(),
        }
    }

    fn count_pops(&mut self, count: usize) {
        assert!(self.pops >= count);
        self.pops -= count;
    }

    fn count_pushes(&mut self, count: usize) {
        assert_eq!(self.pops, 0);
        assert!(self.pushes >= count);
        self.pushes -= count;
    }

    fn expand_stack(&mut self, by: usize) {
        for _ in 0..by {
            *self.vars += 1;
            let var = Var::with_id(*self.vars);
            for stack in self.stacks.iter_mut() {
                stack.push_back(var.into());
            }
        }
    }

    fn current_stack(&mut self) -> &mut VecDeque<Expr> {
        self.stacks.last_mut().unwrap()
    }

    fn pop(&mut self) -> Expr {
        self.count_pops(1);

        if self.current_stack().is_empty() {
            self.expand_stack(1);
        }

        self.current_stack().pop_front().unwrap()
    }

    fn peek(&mut self, depth: usize) -> &Expr {
        // A peek is basically N pops followed by N pushes.
        self.count_pops(depth + 1);
        self.count_pushes(depth + 1);

        let len = self.current_stack().len();
        if len < depth + 1 {
            self.expand_stack(1 + depth - len);
        }

        self.current_stack().get(depth).unwrap()
    }

    fn swap(&mut self, depth: usize) {
        // A swap is basically N pops followed by N pushes.
        self.count_pops(depth + 1);
        self.count_pushes(depth + 1);

        let len = self.current_stack().len();
        if len < depth + 1 {
            self.expand_stack(1 + depth - len);
        }

        let deep = self.current_stack().swap_remove_front(depth).unwrap();
        self.current_stack().push_front(deep);
    }

    fn push(&mut self, expr: Expr) {
        self.count_pushes(1);
        self.current_stack().push_front(expr);
    }

    fn push_const<A: AsRef<[u8]>>(&mut self, imm: &A) {
        self.push(Expr::constant(imm))
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

    fn advance(&mut self) {
        let last = self.stacks.last().cloned().unwrap_or_default();
        self.stacks.push(last);
    }

    fn annotate_one<'s>(pc: usize, stack: &mut StackWindow<'s>, op: &ConcreteOp) -> Option<Exit> {
        match op {
            ConcreteOp::Stop => {
                return Some(Exit::Terminate);
            }

            ConcreteOp::Add => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.add(&rhs));
            }

            ConcreteOp::Mul => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.mul(&rhs));
            }

            ConcreteOp::Sub => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.sub(&rhs));
            }

            ConcreteOp::Div => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.div(&rhs));
            }
            ConcreteOp::SDiv => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.s_div(&rhs));
            }
            ConcreteOp::Mod => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.modulo(&rhs));
            }
            ConcreteOp::SMod => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.s_modulo(&rhs));
            }
            ConcreteOp::AddMod => {
                let add0 = stack.pop();
                let add1 = stack.pop();
                let mod_ = stack.pop();
                stack.push(add0.add_mod(&add1, &mod_))
            }
            ConcreteOp::MulMod => {
                let add0 = stack.pop();
                let add1 = stack.pop();
                let mod_ = stack.pop();
                stack.push(add0.mul_mod(&add1, &mod_))
            }
            ConcreteOp::Exp => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.exp(&rhs));
            }
            ConcreteOp::SignExtend => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.sign_extend(&rhs));
            }

            ConcreteOp::Lt => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.lt(&rhs));
            }
            ConcreteOp::Gt => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.gt(&rhs));
            }
            ConcreteOp::SLt => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.s_lt(&rhs));
            }
            ConcreteOp::SGt => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.s_gt(&rhs));
            }
            ConcreteOp::Eq => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.is_eq(&rhs));
            }
            ConcreteOp::IsZero => {
                let arg = stack.pop().is_zero();
                stack.push(arg);
            }
            ConcreteOp::And => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.and(&rhs));
            }
            ConcreteOp::Or => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.or(&rhs));
            }
            ConcreteOp::Xor => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.xor(&rhs));
            }
            ConcreteOp::Not => {
                let arg = stack.pop().not();
                stack.push(arg);
            }
            ConcreteOp::Byte => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.byte(&rhs));
            }
            ConcreteOp::Shl => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.shl(&rhs));
            }
            ConcreteOp::Shr => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.shr(&rhs));
            }
            ConcreteOp::Sar => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.sar(&rhs));
            }
            ConcreteOp::Keccak256 => {
                let offset = stack.pop();
                let length = stack.pop();
                stack.push(Expr::keccak256(&offset, &length));
            }

            ConcreteOp::Address => stack.push(Expr::address()),
            ConcreteOp::Balance => {
                let address = stack.pop();
                stack.push(Expr::balance(&address));
            }
            ConcreteOp::Origin => stack.push(Expr::origin()),
            ConcreteOp::Caller => stack.push(Expr::caller()),
            ConcreteOp::CallValue => stack.push(Expr::call_value()),
            ConcreteOp::CallDataLoad => {
                let offset = stack.pop();
                stack.push(Expr::call_data_load(&offset));
            }
            ConcreteOp::CodeSize => stack.push(Expr::code_size()),
            ConcreteOp::GasPrice => stack.push(Expr::gas_price()),
            ConcreteOp::ExtCodeSize => {
                let address = stack.pop();
                stack.push(Expr::ext_code_size(&address));
            }
            ConcreteOp::BlockHash => {
                let address = stack.pop();
                stack.push(Expr::block_hash(&address));
            }
            ConcreteOp::Coinbase => stack.push(Expr::coinbase()),
            ConcreteOp::Timestamp => stack.push(Expr::timestamp()),
            ConcreteOp::Number => stack.push(Expr::number()),
            ConcreteOp::Difficulty => stack.push(Expr::difficulty()),
            ConcreteOp::GasLimit => stack.push(Expr::gas_limit()),
            ConcreteOp::ChainId => stack.push(Expr::chain_id()),
            ConcreteOp::SelfBalance => stack.push(Expr::self_balance()),
            ConcreteOp::BaseFee => stack.push(Expr::base_fee()),

            ConcreteOp::MSize => stack.push(Expr::m_size()),
            ConcreteOp::Gas => stack.push(Expr::gas()),

            ConcreteOp::Pop => {
                stack.pop();
            }

            ConcreteOp::CallDataSize => stack.push(Expr::call_data_size()),
            ConcreteOp::CallDataCopy => {
                let _dest_offset = stack.pop();
                let _offset = stack.pop();
                let _len = stack.pop();
                // TODO: Set memory
            }

            ConcreteOp::CodeCopy => {
                let _dest_offset = stack.pop();
                let _offset = stack.pop();
                let _len = stack.pop();
                // TODO: Set memory
            }

            ConcreteOp::ExtCodeCopy => {
                let _addr = stack.pop();
                let _dest_offset = stack.pop();
                let _offset = stack.pop();
                let _len = stack.pop();
                // TODO: Set memory
            }
            ConcreteOp::ReturnDataSize => stack.push(Expr::return_data_size()),
            ConcreteOp::ReturnDataCopy => {
                let _dest_offset = stack.pop();
                let _offset = stack.pop();
                let _len = stack.pop();
                // TODO: Set memory
            }
            ConcreteOp::ExtCodeHash => {
                let addr = stack.pop();
                stack.push(Expr::ext_code_hash(&addr));
            }
            ConcreteOp::MLoad => {
                let addr = stack.pop();
                stack.push(addr.m_load());
            }
            ConcreteOp::MStore => {
                let _addr = stack.pop();
                let _value = stack.pop();
                // TODO: set memory
            }
            ConcreteOp::MStore8 => {
                let _addr = stack.pop();
                let _value = stack.pop();
                // TODO: set memory
            }
            ConcreteOp::SLoad => {
                let addr = stack.pop();
                stack.push(addr.s_load());
            }
            ConcreteOp::SStore => {
                let _key = stack.pop();
                let _value = stack.pop();
                // TODO: set storage
            }
            ConcreteOp::GetPc => stack.push(Expr::pc(pc as u16)),

            ConcreteOp::JumpDest => {
                // No-op
            }

            ConcreteOp::Push1(imm) => stack.push_const(imm),
            ConcreteOp::Push2(imm) => stack.push_const(imm),
            ConcreteOp::Push3(imm) => stack.push_const(imm),
            ConcreteOp::Push4(imm) => stack.push_const(imm),
            ConcreteOp::Push5(imm) => stack.push_const(imm),
            ConcreteOp::Push6(imm) => stack.push_const(imm),
            ConcreteOp::Push7(imm) => stack.push_const(imm),
            ConcreteOp::Push8(imm) => stack.push_const(imm),
            ConcreteOp::Push9(imm) => stack.push_const(imm),
            ConcreteOp::Push10(imm) => stack.push_const(imm),
            ConcreteOp::Push11(imm) => stack.push_const(imm),
            ConcreteOp::Push12(imm) => stack.push_const(imm),
            ConcreteOp::Push13(imm) => stack.push_const(imm),
            ConcreteOp::Push14(imm) => stack.push_const(imm),
            ConcreteOp::Push15(imm) => stack.push_const(imm),
            ConcreteOp::Push16(imm) => stack.push_const(imm),
            ConcreteOp::Push17(imm) => stack.push_const(imm),
            ConcreteOp::Push18(imm) => stack.push_const(imm),
            ConcreteOp::Push19(imm) => stack.push_const(imm),
            ConcreteOp::Push20(imm) => stack.push_const(imm),
            ConcreteOp::Push21(imm) => stack.push_const(imm),
            ConcreteOp::Push22(imm) => stack.push_const(imm),
            ConcreteOp::Push23(imm) => stack.push_const(imm),
            ConcreteOp::Push24(imm) => stack.push_const(imm),
            ConcreteOp::Push25(imm) => stack.push_const(imm),
            ConcreteOp::Push26(imm) => stack.push_const(imm),
            ConcreteOp::Push27(imm) => stack.push_const(imm),
            ConcreteOp::Push28(imm) => stack.push_const(imm),
            ConcreteOp::Push29(imm) => stack.push_const(imm),
            ConcreteOp::Push30(imm) => stack.push_const(imm),
            ConcreteOp::Push31(imm) => stack.push_const(imm),
            ConcreteOp::Push32(imm) => stack.push_const(imm),

            ConcreteOp::Dup1 => {
                let arg = stack.peek(0).clone();
                stack.push(arg)
            }
            ConcreteOp::Dup2 => {
                let arg = stack.peek(1).clone();
                stack.push(arg)
            }
            ConcreteOp::Dup3 => {
                let arg = stack.peek(2).clone();
                stack.push(arg)
            }
            ConcreteOp::Dup4 => {
                let arg = stack.peek(3).clone();
                stack.push(arg)
            }
            ConcreteOp::Dup5 => {
                let arg = stack.peek(4).clone();
                stack.push(arg)
            }
            ConcreteOp::Dup6 => {
                let arg = stack.peek(5).clone();
                stack.push(arg)
            }
            ConcreteOp::Dup7 => {
                let arg = stack.peek(6).clone();
                stack.push(arg)
            }
            ConcreteOp::Dup8 => {
                let arg = stack.peek(7).clone();
                stack.push(arg)
            }
            ConcreteOp::Dup9 => {
                let arg = stack.peek(8).clone();
                stack.push(arg)
            }
            ConcreteOp::Dup10 => {
                let arg = stack.peek(9).clone();
                stack.push(arg)
            }
            ConcreteOp::Dup11 => {
                let arg = stack.peek(10).clone();
                stack.push(arg)
            }
            ConcreteOp::Dup12 => {
                let arg = stack.peek(11).clone();
                stack.push(arg)
            }
            ConcreteOp::Dup13 => {
                let arg = stack.peek(12).clone();
                stack.push(arg)
            }
            ConcreteOp::Dup14 => {
                let arg = stack.peek(13).clone();
                stack.push(arg)
            }
            ConcreteOp::Dup15 => {
                let arg = stack.peek(14).clone();
                stack.push(arg)
            }
            ConcreteOp::Dup16 => {
                let arg = stack.peek(15).clone();
                stack.push(arg)
            }

            ConcreteOp::Log0 => {
                let _offset = stack.pop();
                let _length = stack.pop();
            }
            ConcreteOp::Log1 => {
                let _offset = stack.pop();
                let _length = stack.pop();
                let _topic0 = stack.pop();
            }
            ConcreteOp::Log2 => {
                let _offset = stack.pop();
                let _length = stack.pop();
                let _topic0 = stack.pop();
                let _topic1 = stack.pop();
            }
            ConcreteOp::Log3 => {
                let _offset = stack.pop();
                let _length = stack.pop();
                let _topic0 = stack.pop();
                let _topic1 = stack.pop();
                let _topic2 = stack.pop();
            }
            ConcreteOp::Log4 => {
                let _offset = stack.pop();
                let _length = stack.pop();
                let _topic0 = stack.pop();
                let _topic1 = stack.pop();
                let _topic2 = stack.pop();
                let _topic3 = stack.pop();
            }

            ConcreteOp::Swap1 => stack.swap(1),
            ConcreteOp::Swap2 => stack.swap(2),
            ConcreteOp::Swap3 => stack.swap(3),
            ConcreteOp::Swap4 => stack.swap(4),
            ConcreteOp::Swap5 => stack.swap(5),
            ConcreteOp::Swap6 => stack.swap(6),
            ConcreteOp::Swap7 => stack.swap(7),
            ConcreteOp::Swap8 => stack.swap(8),
            ConcreteOp::Swap9 => stack.swap(9),
            ConcreteOp::Swap10 => stack.swap(10),
            ConcreteOp::Swap11 => stack.swap(11),
            ConcreteOp::Swap12 => stack.swap(12),
            ConcreteOp::Swap13 => stack.swap(13),
            ConcreteOp::Swap14 => stack.swap(14),
            ConcreteOp::Swap15 => stack.swap(15),
            ConcreteOp::Swap16 => stack.swap(16),

            ConcreteOp::Revert | ConcreteOp::Return => {
                let _offset = stack.pop();
                let _length = stack.pop();
                return Some(Exit::Terminate);
            }

            ConcreteOp::SelfDestruct => {
                let _addr = stack.pop();
                return Some(Exit::Terminate);
            }

            ConcreteOp::Jump => {
                let dest = stack.pop();
                return Some(Exit::Unconditional(dest));
            }

            ConcreteOp::JumpI => {
                let when_false = pc + 1;
                let when_true = stack.pop();
                let condition = stack.pop();
                return Some(Exit::Branch {
                    when_false,
                    when_true,
                    condition,
                });
            }

            ConcreteOp::Create => {
                let value = stack.pop();
                let offset = stack.pop();
                let length = stack.pop();
                stack.push(Expr::create(&value, &offset, &length))
            }

            ConcreteOp::Call => {
                let gas = stack.pop();
                let addr = stack.pop();
                let value = stack.pop();
                let args_offset = stack.pop();
                let args_len = stack.pop();
                let ret_offset = stack.pop();
                let ret_len = stack.pop();
                stack.push(Expr::call(
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
                let gas = stack.pop();
                let addr = stack.pop();
                let value = stack.pop();
                let args_offset = stack.pop();
                let args_len = stack.pop();
                let ret_offset = stack.pop();
                let ret_len = stack.pop();
                stack.push(Expr::call_code(
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
                let gas = stack.pop();
                let addr = stack.pop();
                let args_offset = stack.pop();
                let args_len = stack.pop();
                let ret_offset = stack.pop();
                let ret_len = stack.pop();
                stack.push(Expr::delegate_call(
                    &gas,
                    &addr,
                    &args_offset,
                    &args_len,
                    &ret_offset,
                    &ret_len,
                ))
            }

            ConcreteOp::Create2 => {
                let value = stack.pop();
                let offset = stack.pop();
                let length = stack.pop();
                let salt = stack.pop();
                stack.push(Expr::create2(&value, &offset, &length, &salt))
            }

            ConcreteOp::StaticCall => {
                let gas = stack.pop();
                let addr = stack.pop();
                let args_offset = stack.pop();
                let args_len = stack.pop();
                let ret_offset = stack.pop();
                let ret_len = stack.pop();
                stack.push(Expr::static_call(
                    &gas,
                    &addr,
                    &args_offset,
                    &args_len,
                    &ret_offset,
                    &ret_len,
                ))
            }

            ConcreteOp::Invalid
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
            | ConcreteOp::InvalidB0
            | ConcreteOp::InvalidB1
            | ConcreteOp::InvalidB2
            | ConcreteOp::InvalidB3
            | ConcreteOp::InvalidB4
            | ConcreteOp::InvalidB5
            | ConcreteOp::InvalidB6
            | ConcreteOp::InvalidB7
            | ConcreteOp::InvalidB8
            | ConcreteOp::InvalidB9
            | ConcreteOp::InvalidBa
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
            | ConcreteOp::InvalidE1
            | ConcreteOp::InvalidE2
            | ConcreteOp::InvalidE3
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
            | ConcreteOp::InvalidFb
            | ConcreteOp::InvalidFc => {
                return Some(Exit::Terminate);
            }
        }

        None
    }

    pub fn annotate(&mut self) -> Exit {
        let mut pc = self.basic.offset;

        for (idx, op) in self.basic.ops.iter().enumerate() {
            self.advance();
            let is_last = idx == self.basic.ops.len() - 1;

            let mut window = StackWindow::new(&mut self.vars, &mut self.stacks, op);

            if let Some(exit) = Self::annotate_one(pc, &mut window, op) {
                assert!(is_last);

                let exit_matches = match exit {
                    Exit::Terminate => op.is_exit(),
                    Exit::Branch { .. } => op.is_jump(),
                    Exit::Unconditional(_) => op.is_jump(),
                    Exit::FallThrough(_) => unreachable!(),
                };

                assert!(exit_matches, "bug: exit type doesn't match metadata");

                return exit;
            }

            assert!(!op.is_exit());

            pc += op.size() as usize;
        }

        Exit::FallThrough(pc)
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
                wrong => panic!("expected {:?}, got {:?}", Exit::<()>::Terminate, wrong),
            }
        }
    }

    struct ExitFallThrough(usize);

    impl CheckExit for ExitFallThrough {
        fn check(&self, actual: &Exit) {
            let exit = match actual {
                Exit::FallThrough(f) => f,
                wrong => panic!(
                    "expected {:?}, got {:?}",
                    Exit::<()>::FallThrough(self.0),
                    wrong
                ),
            };

            assert_eq!(&self.0, exit);
        }
    }

    struct ExitUnconditional(Expr);

    impl CheckExit for ExitUnconditional {
        fn check(&self, actual: &Exit) {
            let exit = match actual {
                Exit::Unconditional(expr) => expr,
                wrong => panic!("expected Exit::Unconditional(...), got {:?}", wrong),
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
            expected_exit: ExitFallThrough(0x1235),
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
            expected_exit: ExitFallThrough(0x1235),
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
            expected_exit: ExitFallThrough(0x1235),
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
            expected_exit: ExitFallThrough(0x1235),
            expected_input_stack: vec![Var::with_id(1), Var::with_id(2)],
            expected_output_stack: vec![Var::with_id(2), Var::with_id(1)],
        }
        .check();
    }

    #[test]
    fn annotate_swap2() {
        AnnotateTest {
            ops: vec![ConcreteOp::Swap2],
            expected_exit: ExitFallThrough(0x1235),
            expected_input_stack: vec![Var::with_id(1), Var::with_id(2), Var::with_id(3)],
            expected_output_stack: vec![Var::with_id(3), Var::with_id(2), Var::with_id(1)],
        }
        .check();
    }

    #[test]
    fn annotate_swap3() {
        AnnotateTest {
            ops: vec![ConcreteOp::Swap3],
            expected_exit: ExitFallThrough(0x1235),
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
            expected_exit: ExitFallThrough(0x1235),
            expected_input_stack: vec![Var::with_id(1)],
            expected_output_stack: vec![Var::with_id(1), Var::with_id(1)],
        }
        .check();
    }

    #[test]
    fn annotate_dup2() {
        AnnotateTest {
            ops: vec![ConcreteOp::Dup2],
            expected_exit: ExitFallThrough(0x1235),
            expected_input_stack: vec![Var::with_id(1), Var::with_id(2)],
            expected_output_stack: vec![Var::with_id(2), Var::with_id(1), Var::with_id(2)],
        }
        .check();
    }

    #[test]
    fn annotate_dup3() {
        AnnotateTest {
            ops: vec![ConcreteOp::Dup3],
            expected_exit: ExitFallThrough(0x1235),
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
            expected_exit: ExitFallThrough(0x1236),
            expected_input_stack: Vec::<Expr>::new(),
            expected_output_stack: vec![Expr::constant_offset(77u8)],
        }
        .check();
    }

    #[test]
    fn annotate_push2() {
        AnnotateTest {
            ops: vec![ConcreteOp::Push2([0x12, 0x34].into())],
            expected_exit: ExitFallThrough(0x1237),
            expected_input_stack: Vec::<Expr>::new(),
            expected_output_stack: vec![Expr::constant_offset(0x1234u64)],
        }
        .check();
    }

    #[test]
    fn annotate_jump() {
        AnnotateTest {
            ops: vec![
                ConcreteOp::Push1([0xbb].into()),
                ConcreteOp::Push1([0xaa].into()),
                ConcreteOp::Jump,
            ],
            expected_exit: ExitUnconditional(Expr::constant_offset(0xaau64)),
            expected_input_stack: Vec::<Expr>::new(),
            expected_output_stack: vec![Expr::constant_offset(0xbbu64)],
        }
        .check();
    }
}
