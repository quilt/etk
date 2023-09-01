//! Representation of EVM instruction blocks as expressions applied to inputs
//! (ie. stack/memory/storage).
use crate::sym::{Expr, Var};

use etk_ops::prague::*;

use std::collections::VecDeque;

use super::BasicBlock;

/// Possible ways for an [`AnnotatedBlock`] to exit.
#[derive(Debug, Clone)]
pub enum Exit<T = Expr> {
    /// Unconditional program halt.
    ///
    /// Includes `stop` (`0x00`), `return` (`0xF3`), `revert` (`0xfd`), etc.
    Terminate,

    /// Unconditionally continue to the subsequent block, which has the given
    /// offset.
    ///
    /// Commonly occurs when the next block begins with a `jumpdest` (`0x5b`).
    FallThrough(usize),

    /// Unconditionally jump to the given offset.
    Unconditional(T),

    /// Conditionally jump to one of the given offsets.
    Branch {
        /// Expression that determines whether to fall through to the next block
        /// or jump.
        condition: T,

        /// Offset to jump to if `condition` is truthy.
        when_true: T,

        /// Offset of block to fall through to if `condition` is not truthy.
        when_false: usize,
    },
}

impl<T> Exit<T> {
    /// Get the offset of the fall through block, or `None` if this block can
    /// never fall through.
    ///
    /// Both [`Exit::FallThrough`] and [`Exit::Branch`] have fall through
    /// offsets.
    pub fn fall_through(&self) -> Option<usize> {
        match self {
            Self::FallThrough(f) => Some(*f),
            Self::Branch { when_false, .. } => Some(*when_false),
            _ => None,
        }
    }

    /// Return `true` if this block is an [`Exit::FallThrough`], or `false`
    /// otherwise.
    pub fn is_fall_through(&self) -> bool {
        matches!(self, Self::FallThrough(_))
    }

    /// Return `true` if this block is an [`Exit::Terminate`], or `false`
    /// otherwise.
    pub fn is_terminate(&self) -> bool {
        matches!(self, Self::Terminate)
    }

    /// Return `true` if this block is an [`Exit::Unconditional`], or `false`
    /// otherwise.
    pub fn is_unconditional(&self) -> bool {
        matches!(self, Self::Unconditional(_))
    }

    /// Return `true` if this block is an [`Exit::Branch`], or `false`
    /// otherwise.
    pub fn is_branch(&self) -> bool {
        matches!(self, Self::Branch { .. })
    }
}

/// Represents values that are accessed during execution of an
/// [`AnnotatedBlock`].
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct Inputs {
    /// Ordered list of inputs that are required to be on the EVM stack when
    /// entering this block.
    pub stack: Vec<Var>,
}

/// Represents values that are modified during execution of an
/// [`AnnotatedBlock`].
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct Outputs {
    /// Ordered list of expressions pushed to the stack after exiting this
    /// block.
    pub stack: Vec<Expr>,
}

/// Represents a block of EVM instructions as a set of expressions.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct AnnotatedBlock {
    /// Position of the first instruction in the block.
    pub offset: usize,

    /// Values which are accessed during execution of this block.
    pub inputs: Inputs,

    /// Values which are created/modified during execution of this block.
    pub outputs: Outputs,

    /// Describes how execution continues after the last instruction of this
    /// block.
    pub exit: Exit,

    /// Whether this block begins with a `jumpdest` (`0x5b`).
    pub jump_target: bool,

    /// Length of this block.
    pub size: usize,
}

impl AnnotatedBlock {
    /// Construct an [`AnnotatedBlock`] from a [`BasicBlock`].
    pub fn annotate(basic: &BasicBlock) -> Self {
        let jump_target = basic
            .ops
            .get(0)
            .map(Operation::is_jump_target)
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
            },
            inputs: Inputs {
                stack: stack_inputs,
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
    fn new(vars: &'s mut u16, stacks: &'s mut Vec<VecDeque<Expr>>, op: &Op<[u8]>) -> Self {
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
    fn new(basic: &'a BasicBlock) -> Self {
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

    fn annotate_one(pc: usize, stack: &mut StackWindow, op: &Op<[u8]>) -> Option<Exit> {
        match op {
            Op::Stop(_) => {
                return Some(Exit::Terminate);
            }

            Op::Add(_) => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.add(&rhs));
            }

            Op::Mul(_) => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.mul(&rhs));
            }

            Op::Sub(_) => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.sub(&rhs));
            }

            Op::Div(_) => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.div(&rhs));
            }
            Op::SDiv(_) => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.s_div(&rhs));
            }
            Op::Mod(_) => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.modulo(&rhs));
            }
            Op::SMod(_) => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.s_modulo(&rhs));
            }
            Op::AddMod(_) => {
                let add0 = stack.pop();
                let add1 = stack.pop();
                let mod_ = stack.pop();
                stack.push(add0.add_mod(&add1, &mod_))
            }
            Op::MulMod(_) => {
                let add0 = stack.pop();
                let add1 = stack.pop();
                let mod_ = stack.pop();
                stack.push(add0.mul_mod(&add1, &mod_))
            }
            Op::Exp(_) => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.exp(&rhs));
            }
            Op::SignExtend(_) => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.sign_extend(&rhs));
            }

            Op::Lt(_) => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.lt(&rhs));
            }
            Op::Gt(_) => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.gt(&rhs));
            }
            Op::SLt(_) => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.s_lt(&rhs));
            }
            Op::SGt(_) => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.s_gt(&rhs));
            }
            Op::Eq(_) => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.is_eq(&rhs));
            }
            Op::IsZero(_) => {
                let arg = stack.pop().is_zero();
                stack.push(arg);
            }
            Op::And(_) => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.and(&rhs));
            }
            Op::Or(_) => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.or(&rhs));
            }
            Op::Xor(_) => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.xor(&rhs));
            }
            Op::Not(_) => {
                let arg = stack.pop().not();
                stack.push(arg);
            }
            Op::Byte(_) => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.byte(&rhs));
            }
            Op::Shl(_) => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.shl(&rhs));
            }
            Op::Shr(_) => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.shr(&rhs));
            }
            Op::Sar(_) => {
                let lhs = stack.pop();
                let rhs = stack.pop();
                stack.push(lhs.sar(&rhs));
            }
            Op::Keccak256(_) => {
                let offset = stack.pop();
                let length = stack.pop();
                stack.push(Expr::keccak256(&offset, &length));
            }

            Op::Address(_) => stack.push(Expr::address()),
            Op::Balance(_) => {
                let address = stack.pop();
                stack.push(Expr::balance(&address));
            }
            Op::Origin(_) => stack.push(Expr::origin()),
            Op::Caller(_) => stack.push(Expr::caller()),
            Op::CallValue(_) => stack.push(Expr::call_value()),
            Op::CallDataLoad(_) => {
                let offset = stack.pop();
                stack.push(Expr::call_data_load(&offset));
            }
            Op::CodeSize(_) => stack.push(Expr::code_size()),
            Op::GasPrice(_) => stack.push(Expr::gas_price()),
            Op::ExtCodeSize(_) => {
                let address = stack.pop();
                stack.push(Expr::ext_code_size(&address));
            }
            Op::BlockHash(_) => {
                let address = stack.pop();
                stack.push(Expr::block_hash(&address));
            }
            Op::Coinbase(_) => stack.push(Expr::coinbase()),
            Op::Timestamp(_) => stack.push(Expr::timestamp()),
            Op::Number(_) => stack.push(Expr::number()),
            Op::Difficulty(_) => stack.push(Expr::difficulty()),
            Op::GasLimit(_) => stack.push(Expr::gas_limit()),
            Op::ChainId(_) => stack.push(Expr::chain_id()),
            Op::SelfBalance(_) => stack.push(Expr::self_balance()),
            Op::BaseFee(_) => stack.push(Expr::base_fee()),

            Op::MSize(_) => stack.push(Expr::m_size()),
            Op::Gas(_) => stack.push(Expr::gas()),

            Op::Pop(_) => {
                stack.pop();
            }

            Op::CallDataSize(_) => stack.push(Expr::call_data_size()),
            Op::CallDataCopy(_) => {
                let _dest_offset = stack.pop();
                let _offset = stack.pop();
                let _len = stack.pop();
                // TODO: Set memory
            }

            Op::CodeCopy(_) => {
                let _dest_offset = stack.pop();
                let _offset = stack.pop();
                let _len = stack.pop();
                // TODO: Set memory
            }

            Op::ExtCodeCopy(_) => {
                let _addr = stack.pop();
                let _dest_offset = stack.pop();
                let _offset = stack.pop();
                let _len = stack.pop();
                // TODO: Set memory
            }
            Op::ReturnDataSize(_) => stack.push(Expr::return_data_size()),
            Op::ReturnDataCopy(_) => {
                let _dest_offset = stack.pop();
                let _offset = stack.pop();
                let _len = stack.pop();
                // TODO: Set memory
            }
            Op::ExtCodeHash(_) => {
                let addr = stack.pop();
                stack.push(Expr::ext_code_hash(&addr));
            }
            Op::MLoad(_) => {
                let addr = stack.pop();
                stack.push(addr.m_load());
            }
            Op::MStore(_) => {
                let _addr = stack.pop();
                let _value = stack.pop();
                // TODO: set memory
            }
            Op::MStore8(_) => {
                let _addr = stack.pop();
                let _value = stack.pop();
                // TODO: set memory
            }
            Op::SLoad(_) => {
                let addr = stack.pop();
                stack.push(addr.s_load());
            }
            Op::SStore(_) => {
                let _key = stack.pop();
                let _value = stack.pop();
                // TODO: set storage
            }
            Op::GetPc(_) => stack.push(Expr::pc(pc as u16)),

            Op::JumpDest(_) => {
                // No-op
            }
            Op::MCopy(_) => {
                let _dest_offset = stack.pop();
                let _offset = stack.pop();
                let _len = stack.pop();
                // TODO: Set memory
            }

            Op::Push0(_) => stack.push_const(&[0; 1]),
            Op::Push1(Push1(imm)) => stack.push_const(imm),
            Op::Push2(Push2(imm)) => stack.push_const(imm),
            Op::Push3(Push3(imm)) => stack.push_const(imm),
            Op::Push4(Push4(imm)) => stack.push_const(imm),
            Op::Push5(Push5(imm)) => stack.push_const(imm),
            Op::Push6(Push6(imm)) => stack.push_const(imm),
            Op::Push7(Push7(imm)) => stack.push_const(imm),
            Op::Push8(Push8(imm)) => stack.push_const(imm),
            Op::Push9(Push9(imm)) => stack.push_const(imm),
            Op::Push10(Push10(imm)) => stack.push_const(imm),
            Op::Push11(Push11(imm)) => stack.push_const(imm),
            Op::Push12(Push12(imm)) => stack.push_const(imm),
            Op::Push13(Push13(imm)) => stack.push_const(imm),
            Op::Push14(Push14(imm)) => stack.push_const(imm),
            Op::Push15(Push15(imm)) => stack.push_const(imm),
            Op::Push16(Push16(imm)) => stack.push_const(imm),
            Op::Push17(Push17(imm)) => stack.push_const(imm),
            Op::Push18(Push18(imm)) => stack.push_const(imm),
            Op::Push19(Push19(imm)) => stack.push_const(imm),
            Op::Push20(Push20(imm)) => stack.push_const(imm),
            Op::Push21(Push21(imm)) => stack.push_const(imm),
            Op::Push22(Push22(imm)) => stack.push_const(imm),
            Op::Push23(Push23(imm)) => stack.push_const(imm),
            Op::Push24(Push24(imm)) => stack.push_const(imm),
            Op::Push25(Push25(imm)) => stack.push_const(imm),
            Op::Push26(Push26(imm)) => stack.push_const(imm),
            Op::Push27(Push27(imm)) => stack.push_const(imm),
            Op::Push28(Push28(imm)) => stack.push_const(imm),
            Op::Push29(Push29(imm)) => stack.push_const(imm),
            Op::Push30(Push30(imm)) => stack.push_const(imm),
            Op::Push31(Push31(imm)) => stack.push_const(imm),
            Op::Push32(Push32(imm)) => stack.push_const(imm),

            Op::Dup1(_) => {
                let arg = stack.peek(0).clone();
                stack.push(arg)
            }
            Op::Dup2(_) => {
                let arg = stack.peek(1).clone();
                stack.push(arg)
            }
            Op::Dup3(_) => {
                let arg = stack.peek(2).clone();
                stack.push(arg)
            }
            Op::Dup4(_) => {
                let arg = stack.peek(3).clone();
                stack.push(arg)
            }
            Op::Dup5(_) => {
                let arg = stack.peek(4).clone();
                stack.push(arg)
            }
            Op::Dup6(_) => {
                let arg = stack.peek(5).clone();
                stack.push(arg)
            }
            Op::Dup7(_) => {
                let arg = stack.peek(6).clone();
                stack.push(arg)
            }
            Op::Dup8(_) => {
                let arg = stack.peek(7).clone();
                stack.push(arg)
            }
            Op::Dup9(_) => {
                let arg = stack.peek(8).clone();
                stack.push(arg)
            }
            Op::Dup10(_) => {
                let arg = stack.peek(9).clone();
                stack.push(arg)
            }
            Op::Dup11(_) => {
                let arg = stack.peek(10).clone();
                stack.push(arg)
            }
            Op::Dup12(_) => {
                let arg = stack.peek(11).clone();
                stack.push(arg)
            }
            Op::Dup13(_) => {
                let arg = stack.peek(12).clone();
                stack.push(arg)
            }
            Op::Dup14(_) => {
                let arg = stack.peek(13).clone();
                stack.push(arg)
            }
            Op::Dup15(_) => {
                let arg = stack.peek(14).clone();
                stack.push(arg)
            }
            Op::Dup16(_) => {
                let arg = stack.peek(15).clone();
                stack.push(arg)
            }

            Op::Log0(_) => {
                let _offset = stack.pop();
                let _length = stack.pop();
            }
            Op::Log1(_) => {
                let _offset = stack.pop();
                let _length = stack.pop();
                let _topic0 = stack.pop();
            }
            Op::Log2(_) => {
                let _offset = stack.pop();
                let _length = stack.pop();
                let _topic0 = stack.pop();
                let _topic1 = stack.pop();
            }
            Op::Log3(_) => {
                let _offset = stack.pop();
                let _length = stack.pop();
                let _topic0 = stack.pop();
                let _topic1 = stack.pop();
                let _topic2 = stack.pop();
            }
            Op::Log4(_) => {
                let _offset = stack.pop();
                let _length = stack.pop();
                let _topic0 = stack.pop();
                let _topic1 = stack.pop();
                let _topic2 = stack.pop();
                let _topic3 = stack.pop();
            }

            Op::JumpF(JumpF(imm)) => {
                let expr = Expr::constant(imm);
                return Some(Exit::Unconditional(expr));
            }

            Op::Swap1(_) => stack.swap(1),
            Op::Swap2(_) => stack.swap(2),
            Op::Swap3(_) => stack.swap(3),
            Op::Swap4(_) => stack.swap(4),
            Op::Swap5(_) => stack.swap(5),
            Op::Swap6(_) => stack.swap(6),
            Op::Swap7(_) => stack.swap(7),
            Op::Swap8(_) => stack.swap(8),
            Op::Swap9(_) => stack.swap(9),
            Op::Swap10(_) => stack.swap(10),
            Op::Swap11(_) => stack.swap(11),
            Op::Swap12(_) => stack.swap(12),
            Op::Swap13(_) => stack.swap(13),
            Op::Swap14(_) => stack.swap(14),
            Op::Swap15(_) => stack.swap(15),
            Op::Swap16(_) => stack.swap(16),

            Op::Revert(_) | Op::Return(_) => {
                let _offset = stack.pop();
                let _length = stack.pop();
                return Some(Exit::Terminate);
            }

            Op::SelfDestruct(_) => {
                let _addr = stack.pop();
                return Some(Exit::Terminate);
            }

            Op::Jump(_) => {
                let dest = stack.pop();
                return Some(Exit::Unconditional(dest));
            }

            Op::JumpI(_) => {
                let when_false = pc + 1;
                let when_true = stack.pop();
                let condition = stack.pop();
                return Some(Exit::Branch {
                    when_false,
                    when_true,
                    condition,
                });
            }

            Op::Create(_) => {
                let value = stack.pop();
                let offset = stack.pop();
                let length = stack.pop();
                stack.push(Expr::create(&value, &offset, &length))
            }

            Op::Call(_) => {
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

            Op::CallCode(_) => {
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

            Op::DelegateCall(_) => {
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

            Op::Create2(_) => {
                let value = stack.pop();
                let offset = stack.pop();
                let length = stack.pop();
                let salt = stack.pop();
                stack.push(Expr::create2(&value, &offset, &length, &salt))
            }

            Op::StaticCall(_) => {
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

            Op::Invalid(_)
            | Op::Invalid0c(_)
            | Op::Invalid0d(_)
            | Op::Invalid0e(_)
            | Op::Invalid0f(_)
            | Op::Invalid1e(_)
            | Op::Invalid1f(_)
            | Op::Invalid21(_)
            | Op::Invalid22(_)
            | Op::Invalid23(_)
            | Op::Invalid24(_)
            | Op::Invalid25(_)
            | Op::Invalid26(_)
            | Op::Invalid27(_)
            | Op::Invalid28(_)
            | Op::Invalid29(_)
            | Op::Invalid2a(_)
            | Op::Invalid2b(_)
            | Op::Invalid2c(_)
            | Op::Invalid2d(_)
            | Op::Invalid2e(_)
            | Op::Invalid2f(_)
            | Op::Invalid49(_)
            | Op::Invalid4a(_)
            | Op::Invalid4b(_)
            | Op::Invalid4c(_)
            | Op::Invalid4d(_)
            | Op::Invalid4e(_)
            | Op::Invalid4f(_)
            | Op::Invalid5c(_)
            | Op::Invalid5d(_)
            | Op::InvalidA5(_)
            | Op::InvalidA6(_)
            | Op::InvalidA7(_)
            | Op::InvalidA8(_)
            | Op::InvalidA9(_)
            | Op::InvalidAa(_)
            | Op::InvalidAb(_)
            | Op::InvalidAc(_)
            | Op::InvalidAd(_)
            | Op::InvalidAe(_)
            | Op::InvalidAf(_)
            | Op::InvalidB0(_)
            | Op::InvalidB1(_)
            | Op::InvalidB2(_)
            | Op::InvalidB3(_)
            | Op::InvalidB4(_)
            | Op::InvalidB5(_)
            | Op::InvalidB6(_)
            | Op::InvalidB7(_)
            | Op::InvalidB8(_)
            | Op::InvalidB9(_)
            | Op::InvalidBa(_)
            | Op::InvalidBb(_)
            | Op::InvalidBc(_)
            | Op::InvalidBd(_)
            | Op::InvalidBe(_)
            | Op::InvalidBf(_)
            | Op::InvalidC0(_)
            | Op::InvalidC1(_)
            | Op::InvalidC2(_)
            | Op::InvalidC3(_)
            | Op::InvalidC4(_)
            | Op::InvalidC5(_)
            | Op::InvalidC6(_)
            | Op::InvalidC7(_)
            | Op::InvalidC8(_)
            | Op::InvalidC9(_)
            | Op::InvalidCa(_)
            | Op::InvalidCb(_)
            | Op::InvalidCc(_)
            | Op::InvalidCd(_)
            | Op::InvalidCe(_)
            | Op::InvalidCf(_)
            | Op::InvalidD0(_)
            | Op::InvalidD1(_)
            | Op::InvalidD2(_)
            | Op::InvalidD3(_)
            | Op::InvalidD4(_)
            | Op::InvalidD5(_)
            | Op::InvalidD6(_)
            | Op::InvalidD7(_)
            | Op::InvalidD8(_)
            | Op::InvalidD9(_)
            | Op::InvalidDa(_)
            | Op::InvalidDb(_)
            | Op::InvalidDc(_)
            | Op::InvalidDd(_)
            | Op::InvalidDe(_)
            | Op::InvalidDf(_)
            | Op::InvalidE0(_)
            | Op::InvalidE1(_)
            | Op::InvalidE2(_)
            | Op::InvalidE3(_)
            | Op::InvalidE4(_)
            | Op::InvalidE6(_)
            | Op::InvalidE7(_)
            | Op::InvalidE8(_)
            | Op::InvalidE9(_)
            | Op::InvalidEa(_)
            | Op::InvalidEb(_)
            | Op::InvalidEc(_)
            | Op::InvalidEd(_)
            | Op::InvalidEe(_)
            | Op::InvalidEf(_)
            | Op::InvalidF6(_)
            | Op::InvalidF7(_)
            | Op::InvalidF8(_)
            | Op::InvalidF9(_)
            | Op::InvalidFb(_)
            | Op::InvalidFc(_) => {
                return Some(Exit::Terminate);
            }
        }

        None
    }

    fn annotate(&mut self) -> Exit {
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

            pc += op.size();
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
        Oi: Into<Op<[u8]>>,
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
            ops: vec![Stop],
            expected_exit: ExitTerminate,
            expected_input_stack: Vec::<Expr>::new(),
            expected_output_stack: Vec::<Expr>::new(),
        }
        .check();
    }

    #[test]
    fn annotate_add() {
        AnnotateTest {
            ops: vec![Add],
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
            ops: vec![Mul],
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
            ops: vec![Sub],
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
            ops: vec![Swap1],
            expected_exit: ExitFallThrough(0x1235),
            expected_input_stack: vec![Var::with_id(1), Var::with_id(2)],
            expected_output_stack: vec![Var::with_id(2), Var::with_id(1)],
        }
        .check();
    }

    #[test]
    fn annotate_swap2() {
        AnnotateTest {
            ops: vec![Swap2],
            expected_exit: ExitFallThrough(0x1235),
            expected_input_stack: vec![Var::with_id(1), Var::with_id(2), Var::with_id(3)],
            expected_output_stack: vec![Var::with_id(3), Var::with_id(2), Var::with_id(1)],
        }
        .check();
    }

    #[test]
    fn annotate_swap3() {
        AnnotateTest {
            ops: vec![Swap3],
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
            ops: vec![Dup1],
            expected_exit: ExitFallThrough(0x1235),
            expected_input_stack: vec![Var::with_id(1)],
            expected_output_stack: vec![Var::with_id(1), Var::with_id(1)],
        }
        .check();
    }

    #[test]
    fn annotate_dup2() {
        AnnotateTest {
            ops: vec![Dup2],
            expected_exit: ExitFallThrough(0x1235),
            expected_input_stack: vec![Var::with_id(1), Var::with_id(2)],
            expected_output_stack: vec![Var::with_id(2), Var::with_id(1), Var::with_id(2)],
        }
        .check();
    }

    #[test]
    fn annotate_dup3() {
        AnnotateTest {
            ops: vec![Dup3],
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
            ops: vec![Push1([77])],
            expected_exit: ExitFallThrough(0x1236),
            expected_input_stack: Vec::<Expr>::new(),
            expected_output_stack: vec![Expr::constant_offset(77u8)],
        }
        .check();
    }

    #[test]
    fn annotate_push2() {
        AnnotateTest {
            ops: vec![Push2([0x12, 0x34])],
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
                Op::from(Push1([0xbb])),
                Op::from(Push1([0xaa])),
                Op::from(Jump),
            ],
            expected_exit: ExitUnconditional(Expr::constant_offset(0xaau64)),
            expected_input_stack: Vec::<Expr>::new(),
            expected_output_stack: vec![Expr::constant_offset(0xbbu64)],
        }
        .check();
    }
}
