//! Expressions, symbols, and variables for symbolic execution.
use std::convert::TryInto;
use std::fmt;
use std::num::NonZeroU16;

/// A variable.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct Var(NonZeroU16);

impl Var {
    pub(crate) fn with_id<T>(id: T) -> Self
    where
        T: TryInto<NonZeroU16>,
        T::Error: std::fmt::Debug,
    {
        Var(id.try_into().unwrap())
    }
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "var{}", self.0)
    }
}

/// Representation of an expression tree (ex. `add(2, sub(9, 4))`)
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Expr {
    ops: Vec<Sym>,
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.walk(&mut DisplayVisit(f))
    }
}

impl From<Var> for Expr {
    fn from(v: Var) -> Expr {
        Self {
            ops: vec![Sym::Var(v)],
        }
    }
}

impl Expr {
    fn concat(op: Sym, args: &[&Self]) -> Self {
        assert_eq!(op.children() as usize, args.len());

        let capacity = 1 + args.iter().map(|x| x.ops.len()).sum::<usize>();
        let mut ops = Vec::with_capacity(capacity);
        ops.push(op);
        for arg in args {
            ops.extend_from_slice(&arg.ops);
        }

        Self { ops }
    }

    /// Create an [`Expr`] representing `address` (`0x30`).
    pub fn address() -> Self {
        Self {
            ops: vec![Sym::Address],
        }
    }

    /// Create an [`Expr`] representing `origin` (`0x32`).
    pub fn origin() -> Self {
        Self {
            ops: vec![Sym::Origin],
        }
    }

    /// Create an [`Expr`] representing `caller` (`0x33`).
    pub fn caller() -> Self {
        Self {
            ops: vec![Sym::Caller],
        }
    }

    /// Create an [`Expr`] representing `callvalue` (`0x34`).
    pub fn call_value() -> Self {
        Self {
            ops: vec![Sym::CallValue],
        }
    }

    /// Create an [`Expr`] representing `calldatasize` (`0x36`).
    pub fn call_data_size() -> Self {
        Self {
            ops: vec![Sym::CallDataSize],
        }
    }

    /// Create an [`Expr`] representing `codesize` (`0x38`).
    pub fn code_size() -> Self {
        Self {
            ops: vec![Sym::CodeSize],
        }
    }

    /// Create an [`Expr`] representing `gasprice` (`0x3a`).
    pub fn gas_price() -> Self {
        Self {
            ops: vec![Sym::GasPrice],
        }
    }

    /// Create an [`Expr`] representing `returndatasize` (`0x3d`).
    pub fn return_data_size() -> Self {
        Self {
            ops: vec![Sym::ReturnDataSize],
        }
    }

    /// Create an [`Expr`] representing `coinbase` (`0x41`).
    pub fn coinbase() -> Self {
        Self {
            ops: vec![Sym::Coinbase],
        }
    }

    /// Create an [`Expr`] representing `timestamp` (`0x42`).
    pub fn timestamp() -> Self {
        Self {
            ops: vec![Sym::Timestamp],
        }
    }

    /// Create an [`Expr`] representing `number` (`0x43`).
    pub fn number() -> Self {
        Self {
            ops: vec![Sym::Number],
        }
    }

    /// Create an [`Expr`] representing `difficulty` (`0x44`).
    pub fn difficulty() -> Self {
        Self {
            ops: vec![Sym::Difficulty],
        }
    }

    /// Create an [`Expr`] representing `gaslimit` (`0x45`).
    pub fn gas_limit() -> Self {
        Self {
            ops: vec![Sym::GasLimit],
        }
    }

    /// Create an [`Expr`] representing `chainid` (`0x46`).
    pub fn chain_id() -> Self {
        Self {
            ops: vec![Sym::ChainId],
        }
    }

    /// Create an [`Expr`] representing `selfbalance` (`0x47`).
    pub fn self_balance() -> Self {
        Self {
            ops: vec![Sym::SelfBalance],
        }
    }

    /// Create an [`Expr`] representing `basefee` (`0x48`).
    pub fn base_fee() -> Self {
        Self {
            ops: vec![Sym::BaseFee],
        }
    }

    /// Create an [`Expr`] representing `blobbasefee` (`0x4e`).
    pub fn blob_base_fee() -> Self {
        Self {
            ops: vec![Sym::BlobBaseFee],
        }
    }

    /// Create an [`Expr`] representing `pc` (`0x58`).
    pub fn pc(offset: u16) -> Self {
        Self {
            ops: vec![Sym::GetPc(offset)],
        }
    }

    /// Create an [`Expr`] representing `msize` (`0x59`).
    pub fn m_size() -> Self {
        Self {
            ops: vec![Sym::MSize],
        }
    }

    /// Create an [`Expr`] representing `gas` (`0x5a`).
    pub fn gas() -> Self {
        Self {
            ops: vec![Sym::Gas],
        }
    }

    /// Create an [`Expr`] representing `create` (`0xf0`).
    pub fn create(value: &Self, offset: &Self, length: &Self) -> Self {
        Self::concat(Sym::Create, &[value, offset, length])
    }

    /// Create an [`Expr`] representing `create2` (`0xf5`).
    pub fn create2(value: &Self, offset: &Self, length: &Self, salt: &Self) -> Self {
        Self::concat(Sym::Create2, &[value, offset, length, salt])
    }

    /// Create an [`Expr`] representing `callcode` (`0xf2`).
    pub fn call_code(
        gas: &Self,
        addr: &Self,
        value: &Self,
        args_offset: &Self,
        args_len: &Self,
        ret_offset: &Self,
        ret_len: &Self,
    ) -> Self {
        Self::concat(
            Sym::CallCode,
            &[gas, addr, value, args_offset, args_len, ret_offset, ret_len],
        )
    }

    /// Create an [`Expr`] representing `call` (`0xf1`).
    pub fn call(
        gas: &Self,
        addr: &Self,
        value: &Self,
        args_offset: &Self,
        args_len: &Self,
        ret_offset: &Self,
        ret_len: &Self,
    ) -> Self {
        Self::concat(
            Sym::Call,
            &[gas, addr, value, args_offset, args_len, ret_offset, ret_len],
        )
    }

    /// Create an [`Expr`] representing `staticcall` (`0xfa`).
    pub fn static_call(
        gas: &Self,
        addr: &Self,
        args_offset: &Self,
        args_len: &Self,
        ret_offset: &Self,
        ret_len: &Self,
    ) -> Self {
        Self::concat(
            Sym::StaticCall,
            &[gas, addr, args_offset, args_len, ret_offset, ret_len],
        )
    }

    /// Create an [`Expr`] representing `delegatecall` (`0xf4`).
    pub fn delegate_call(
        gas: &Self,
        addr: &Self,
        args_offset: &Self,
        args_len: &Self,
        ret_offset: &Self,
        ret_len: &Self,
    ) -> Self {
        Self::concat(
            Sym::DelegateCall,
            &[gas, addr, args_offset, args_len, ret_offset, ret_len],
        )
    }

    /// Create an [`Expr`] representing `add` (`0x01`).
    pub fn add(&self, rhs: &Self) -> Self {
        Self::concat(Sym::Add, &[self, rhs])
    }

    /// Create an [`Expr`] representing `sub` (`0x03`).
    pub fn sub(&self, rhs: &Self) -> Self {
        Self::concat(Sym::Sub, &[self, rhs])
    }

    /// Create an [`Expr`] representing `mul` (`0x02`).
    pub fn mul(&self, rhs: &Self) -> Self {
        Self::concat(Sym::Mul, &[self, rhs])
    }

    /// Create an [`Expr`] representing `div` (`0x04`).
    pub fn div(&self, rhs: &Self) -> Self {
        Self::concat(Sym::Div, &[self, rhs])
    }

    /// Create an [`Expr`] representing `sdiv` (`0x05`).
    pub fn s_div(&self, rhs: &Self) -> Self {
        Self::concat(Sym::SDiv, &[self, rhs])
    }

    /// Create an [`Expr`] representing `mod` (`0x06`).
    pub fn modulo(&self, rhs: &Self) -> Self {
        Self::concat(Sym::Mod, &[self, rhs])
    }

    /// Create an [`Expr`] representing `smod` (`0x07`).
    pub fn s_modulo(&self, rhs: &Self) -> Self {
        Self::concat(Sym::SMod, &[self, rhs])
    }

    /// Create an [`Expr`] representing `addmod` (`0x08`).
    pub fn add_mod(&self, add: &Self, modulo: &Self) -> Self {
        Self::concat(Sym::AddMod, &[self, add, modulo])
    }

    /// Create an [`Expr`] representing `mulmod` (`0x09`).
    pub fn mul_mod(&self, mul: &Self, modulo: &Self) -> Self {
        Self::concat(Sym::MulMod, &[self, mul, modulo])
    }

    /// Create an [`Expr`] representing `exp` (`0x0a`).
    pub fn exp(&self, rhs: &Self) -> Self {
        Self::concat(Sym::Exp, &[self, rhs])
    }

    /// Create an [`Expr`] representing `lt` (`0x10`).
    pub fn lt(&self, rhs: &Self) -> Self {
        Self::concat(Sym::Lt, &[self, rhs])
    }

    /// Create an [`Expr`] representing `gt` (`0x11`).
    pub fn gt(&self, rhs: &Self) -> Self {
        Self::concat(Sym::Gt, &[self, rhs])
    }

    /// Create an [`Expr`] representing `slt` (`0x12`).
    pub fn s_lt(&self, rhs: &Self) -> Self {
        Self::concat(Sym::SLt, &[self, rhs])
    }

    /// Create an [`Expr`] representing `sgt` (`0x13`).
    pub fn s_gt(&self, rhs: &Self) -> Self {
        Self::concat(Sym::SGt, &[self, rhs])
    }

    /// Create an [`Expr`] representing `eq` (`0x14`).
    pub fn is_eq(&self, rhs: &Self) -> Self {
        Self::concat(Sym::Eq, &[self, rhs])
    }

    /// Create an [`Expr`] representing `and` (`0x16`).
    pub fn and(&self, rhs: &Self) -> Self {
        Self::concat(Sym::And, &[self, rhs])
    }

    /// Create an [`Expr`] representing `or` (`0x17`).
    pub fn or(&self, rhs: &Self) -> Self {
        Self::concat(Sym::Or, &[self, rhs])
    }

    /// Create an [`Expr`] representing `xor` (`0x18`).
    pub fn xor(&self, rhs: &Self) -> Self {
        Self::concat(Sym::Xor, &[self, rhs])
    }

    /// Create an [`Expr`] representing `byte` (`0x1a`).
    pub fn byte(&self, value: &Self) -> Self {
        Self::concat(Sym::Byte, &[self, value])
    }

    /// Create an [`Expr`] representing `shl` (`0x1b`).
    pub fn shl(&self, rhs: &Self) -> Self {
        Self::concat(Sym::Shl, &[self, rhs])
    }

    /// Create an [`Expr`] representing `shr` (`0x1c`).
    pub fn shr(&self, value: &Self) -> Self {
        Self::concat(Sym::Shr, &[self, value])
    }

    /// Create an [`Expr`] representing `sar` (`0x1d`).
    pub fn sar(&self, rhs: &Self) -> Self {
        Self::concat(Sym::Sar, &[self, rhs])
    }

    /// Create an [`Expr`] representing `keccak256` (`0x20`).
    pub fn keccak256(offset: &Self, len: &Self) -> Self {
        Self::concat(Sym::Keccak256, &[offset, len])
    }

    /// Create an [`Expr`] representing `signextend` (`0x0b`).
    pub fn sign_extend(&self, b: &Self) -> Self {
        Self::concat(Sym::SignExtend, &[self, b])
    }

    /// Create an [`Expr`] representing `iszero` (`0x15`).
    pub fn is_zero(&self) -> Self {
        Self::concat(Sym::IsZero, &[self])
    }

    /// Create an [`Expr`] representing `not` (`0x19`).
    pub fn not(&self) -> Self {
        Self::concat(Sym::Not, &[self])
    }

    /// Create an [`Expr`] representing `blockhash` (`0x40`).
    pub fn block_hash(&self) -> Self {
        Self::concat(Sym::BlockHash, &[self])
    }

    /// Create an [`Expr`] representing `balance` (`0x31`).
    pub fn balance(&self) -> Self {
        Self::concat(Sym::Balance, &[self])
    }

    /// Create an [`Expr`] representing `calldataload` (`0x35`).
    pub fn call_data_load(&self) -> Self {
        Self::concat(Sym::CallDataLoad, &[self])
    }

    /// Create an [`Expr`] representing `extcodesize` (`0x3b`).
    pub fn ext_code_size(&self) -> Self {
        Self::concat(Sym::ExtCodeSize, &[self])
    }

    /// Create an [`Expr`] representing `extcodehash` (`0x3f`).
    pub fn ext_code_hash(&self) -> Self {
        Self::concat(Sym::ExtCodeHash, &[self])
    }

    /// Create an [`Expr`] representing `mload` (`0x51`).
    pub fn m_load(&self) -> Self {
        Self::concat(Sym::MLoad, &[self])
    }

    /// Create an [`Expr`] representing `sload` (`0x54`).
    pub fn s_load(&self) -> Self {
        Self::concat(Sym::SLoad, &[self])
    }

    /// If this expression represents a single [`Var`] instance, return it.
    /// Otherwise return `None`.
    pub fn as_var(&self) -> Option<Var> {
        match self.ops.as_slice() {
            [Sym::Var(v)] => Some(*v),
            _ => None,
        }
    }

    /// Create an [`Expr`] representing a constant value.
    pub fn constant<A>(arr: A) -> Self
    where
        A: AsRef<[u8]>,
    {
        let arr = arr.as_ref();
        let mut buf = [0u8; 32];
        let start = buf.len() - arr.len();
        buf[start..].copy_from_slice(arr);
        Self {
            ops: vec![Sym::Const(buf.into())],
        }
    }

    #[cfg(test)]
    pub(crate) fn constant_offset<T: Into<u128>>(offset: T) -> Self {
        let offset: u128 = offset.into();
        let mut buf = [0u8; 32];
        buf[16..].copy_from_slice(&offset.to_be_bytes());

        Self {
            ops: vec![Sym::Const(buf.into())],
        }
    }
}

// TODO: Implement UpperHex and LowerHex for Expr

struct DisplayVisit<'a, 'b>(&'a mut fmt::Formatter<'b>);

impl<'a, 'b> Visit for DisplayVisit<'a, 'b> {
    type Error = fmt::Error;

    fn empty(&mut self) -> fmt::Result {
        write!(self.0, "{{}}")
    }

    fn exit(&mut self, op: &Sym) -> fmt::Result {
        match op {
            Sym::Const(_) => Ok(()),
            Sym::Var(_) => Ok(()),
            Sym::IsZero => write!(self.0, " = 0)"),
            _ => write!(self.0, ")"),
        }
    }

    fn between(&mut self, op: &Sym, idx: u8) -> fmt::Result {
        let txt = match op {
            Sym::Add => " + ",
            Sym::Mul => " × ",
            Sym::Sub => " - ",
            Sym::Div => " ÷ ",
            Sym::SDiv => " ÷⃡ ",
            Sym::Mod => " ﹪ ",
            Sym::SMod => " ﹪⃡ ",
            Sym::AddMod => match idx {
                0 => " + ",
                1 => ") ﹪ ",
                _ => unreachable!(),
            },
            Sym::MulMod => match idx {
                0 => " × ",
                1 => ") ﹪ ",
                _ => unreachable!(),
            },
            Sym::Exp => " ** ",
            Sym::Lt => " < ",
            Sym::Gt => " > ",
            Sym::SLt => " <⃡ ",
            Sym::SGt => " >⃡ ",
            Sym::Eq => " = ",
            Sym::And => " & ",
            Sym::Or => " | ",
            Sym::Xor => " ^ ",
            q if q.children() < 2 => unreachable!(),
            _ => ", ",
        };

        write!(self.0, "{}", txt)
    }

    fn enter(&mut self, op: &Sym) -> fmt::Result {
        match op {
            Sym::Const(v) => {
                // TODO: Technically this should be in decimal, not hex.
                write!(self.0, "0x{}", hex::encode(**v))
            }
            Sym::Var(v) => write!(self.0, "{}", v),
            Sym::AddMod => write!(self.0, "(("),
            Sym::MulMod => write!(self.0, "(("),
            Sym::Keccak256 => write!(self.0, "keccak256("),
            Sym::Byte => write!(self.0, "byte("),
            Sym::SignExtend => write!(self.0, "signextend("),
            Sym::Not => write!(self.0, "~("),
            Sym::CallDataLoad => write!(self.0, "calldata("),
            Sym::ExtCodeSize => write!(self.0, "extcodesize("),
            Sym::ExtCodeHash => write!(self.0, "extcodehash("),
            Sym::MLoad => write!(self.0, "mload("),
            Sym::SLoad => write!(self.0, "sload("),
            Sym::Address => write!(self.0, "address("),
            Sym::Balance => write!(self.0, "balance("),
            Sym::Origin => write!(self.0, "origin("),
            Sym::Caller => write!(self.0, "caller("),
            Sym::CallValue => write!(self.0, "callvalue("),
            Sym::CallDataSize => write!(self.0, "calldatasize("),
            Sym::CodeSize => write!(self.0, "codesize("),
            Sym::GasPrice => write!(self.0, "gasprice("),
            Sym::ReturnDataSize => write!(self.0, "returndatasize("),
            Sym::BlockHash => write!(self.0, "blockhash("),
            Sym::Coinbase => write!(self.0, "coinbase("),
            Sym::Timestamp => write!(self.0, "timestamp("),
            Sym::Number => write!(self.0, "number("),
            Sym::Difficulty => write!(self.0, "difficulty("),
            Sym::GasLimit => write!(self.0, "gaslimit("),
            Sym::ChainId => write!(self.0, "chainid("),
            Sym::SelfBalance => write!(self.0, "selfbalance("),
            Sym::BaseFee => write!(self.0, "basefee("),
            Sym::GetPc(pc) => write!(self.0, "pc({}", pc),
            Sym::MSize => write!(self.0, "msize("),
            Sym::Gas => write!(self.0, "gas("),
            Sym::Create => write!(self.0, "create("),
            Sym::CallCode => write!(self.0, "callcode("),
            Sym::Call => write!(self.0, "call("),
            Sym::StaticCall => write!(self.0, "staticcall("),
            Sym::DelegateCall => write!(self.0, "delegatecall("),
            Sym::Shl => write!(self.0, "shl("),
            Sym::Shr => write!(self.0, "shr("),
            Sym::Sar => write!(self.0, "sar("),
            _ => write!(self.0, "("),
        }
    }
}

impl Expr {
    /// Traverse the expression's tree, calling the appropriate functions on
    /// `visitor`.
    pub fn walk<V>(&self, visitor: &mut V) -> Result<(), V::Error>
    where
        V: Visit,
    {
        if self.ops.is_empty() {
            visitor.empty()
        } else {
            Self::inner_walk(&self.ops, visitor)?;
            // TODO: Figure out if it's okay that there's sometimes Syms left
            //       over after walking.
            Ok(())
        }
    }

    fn inner_walk<'a, V>(mut ops: &'a [Sym], visitor: &mut V) -> Result<&'a [Sym], V::Error>
    where
        V: Visit,
    {
        if ops.is_empty() {
            unreachable!();
        }

        let op = &ops[0];

        visitor.enter(op)?;

        for idx in 0..op.children() {
            ops = Self::inner_walk(&ops[1..], visitor)?;

            if (idx + 1) < op.children() {
                visitor.between(op, idx)?;
            }
        }

        visitor.exit(op)?;

        Ok(ops)
    }
}

/// An interface for visiting the operations in an [`Expr`].
pub trait Visit {
    /// An error type.
    type Error;

    /// Called if the [`Expr`] is empty.
    fn empty(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    /// Called when visiting a [`Sym`] for the first time.
    fn enter(&mut self, _: &Sym) -> Result<(), Self::Error> {
        Ok(())
    }

    /// Called between each child of a [`Sym`].
    fn between(&mut self, _: &Sym, _: u8) -> Result<(), Self::Error> {
        Ok(())
    }

    /// Called when leaving a [`Sym`] for the last time.
    fn exit(&mut self, _: &Sym) -> Result<(), Self::Error> {
        Ok(())
    }
}

/// A node in the tree representation of an [`Expr`].
///
/// For example, the expression `2 + 3` would be represented as something like
/// `[Sym::Add, Sym::Const(2), Sym::Const(3)]`.
// TODO: std::mem::size_of::<Sym>() is like 16 bytes. That's HUGE.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Sym {
    /// A constant value.
    Const(Box<[u8; 32]>),

    /// A variable value.
    Var(Var),

    /// An `add` (`0x01`) operation.
    Add,

    /// A `mul` (`0x02`) operation.
    Mul,

    /// A `sub` (`0x03`) operation.
    Sub,

    /// A `div` (`0x04`) operation.
    Div,

    /// A `sdiv` (`0x05`) operation.
    SDiv,

    /// A `mod` (`0x06`) operation.
    Mod,

    /// A `smod` (`0x07`) operation.
    SMod,

    /// A `addmod` (`0x08`) operation.
    AddMod,

    /// A `mulmod` (`0x09`) operation.
    MulMod,

    /// An `exp` (`0x0a`) operation.
    Exp,

    /// An `lt` (`0x10`) operation.
    Lt,

    /// A `gt` (`0x11`) operation.
    Gt,

    /// An `slt` (`0x12`) operation.
    SLt,

    /// An `sgt` (`0x13`) operation.
    SGt,

    /// An `eq` (`0x14`) operation.
    Eq,

    /// An `and` (`0x16`) operation.
    And,

    /// An `or` (`0x17`) operation.
    Or,

    /// A `xor` (`0x18`) operation.
    Xor,

    /// A `byte` (`0x1a`) operation.
    Byte,

    /// A `shl` (`0x1b`) operation.
    Shl,

    /// A `shr` (`0x1c`) operation.
    Shr,

    /// A `sar` (`0x1d`) operation.
    Sar,

    /// A `keccak256` (`0x20`) operation.
    Keccak256,

    /// A `signextend` (`0x0b`) operation.
    SignExtend,

    /// An `iszero` (`0x15`) operation.
    IsZero,

    /// A `not` (`0x18`) operation.
    Not,

    /// A `calldataload` (`0x35`) operation.
    CallDataLoad,

    /// An `extcodesize` (`0x3b`) operation.
    ExtCodeSize,

    /// An `extcodehash` (`0x3f`) operation.
    ExtCodeHash,

    /// An `mload` (`0x51`) operation.
    MLoad,

    /// An `sload` (`0x54`) operation.
    SLoad,

    /// A `balance` (`0x31`) operation.
    Balance,

    /// A `blockhash` (`0x40`) operation.
    BlockHash,

    /// An `address` (`0x30`) operation.
    Address,

    /// An `origin` (`0x32`) operation.
    Origin,

    /// A `caller` (`0x33`) operation.
    Caller,

    /// A `callvalue` (`0x34`) operation.
    CallValue,

    /// A `calldatasize` (`0x36`) operation.
    CallDataSize,

    /// A `codesize` (`0x38`) operation.
    CodeSize,

    /// A `gasprice` (`0x3a`) operation.
    GasPrice,

    /// A `returndatasize` (`0x3d`) operation.
    ReturnDataSize,

    /// A `coinbase` (`0x41`) operation.
    Coinbase,

    /// A `timestamp` (`0x42`) operation.
    Timestamp,

    /// A `number` (`0x43`) operation.
    Number,

    /// A `difficulty` (`0x44`) operation.
    Difficulty,

    /// A `gaslimit` (`0x45`) operation.
    GasLimit,

    /// A `chainid` (`0x46`) operation.
    ChainId,

    /// A `selfbalance` (`0x47`) operation.
    SelfBalance,

    /// A `basefee` (`0x48`) operation.
    BaseFee,

    /// A `blobbasefee` (`0x4e`) operation.
    BlobBaseFee,

    /// A `pc` (`0x58`) operation.
    GetPc(u16),

    /// An `msize` (`0x59`) operation.
    MSize,

    /// A `gas` (`0x5a`) operation.
    Gas,

    /// A `create` (`0xf0`) operation.
    Create,

    /// A `create2` (`0xf5`) operation.
    Create2,

    /// A `callcode` (`0xf2`) operation.
    CallCode,

    /// A `call` (`0xf1`) operation.
    Call,

    /// A `staticcall` (`0xfa`) operation.
    StaticCall,

    /// A `delegatecall` (`0xf4`) operation.
    DelegateCall,
}

impl Sym {
    fn children(&self) -> u8 {
        match self {
            Sym::Add
            | Sym::Mul
            | Sym::Sub
            | Sym::Div
            | Sym::SDiv
            | Sym::Mod
            | Sym::SMod
            | Sym::Exp
            | Sym::Lt
            | Sym::Gt
            | Sym::SLt
            | Sym::SGt
            | Sym::Eq
            | Sym::And
            | Sym::Or
            | Sym::Xor
            | Sym::Byte
            | Sym::Shl
            | Sym::Shr
            | Sym::Sar
            | Sym::SignExtend
            | Sym::Keccak256 => 2,

            Sym::IsZero
            | Sym::Not
            | Sym::CallDataLoad
            | Sym::ExtCodeSize
            | Sym::ExtCodeHash
            | Sym::BlockHash
            | Sym::Balance
            | Sym::MLoad
            | Sym::SLoad => 1,

            Sym::Address
            | Sym::Origin
            | Sym::Caller
            | Sym::CallValue
            | Sym::CallDataSize
            | Sym::CodeSize
            | Sym::GasPrice
            | Sym::ReturnDataSize
            | Sym::Coinbase
            | Sym::Timestamp
            | Sym::Number
            | Sym::Difficulty
            | Sym::GasLimit
            | Sym::ChainId
            | Sym::SelfBalance
            | Sym::BaseFee
            | Sym::BlobBaseFee
            | Sym::GetPc(_)
            | Sym::MSize
            | Sym::Gas
            | Sym::Const(_)
            | Sym::Var(_) => 0,

            Sym::AddMod | Sym::MulMod | Sym::Create => 3,

            Sym::Create2 => 4,

            Sym::Call | Sym::CallCode => 7,

            Sym::DelegateCall | Sym::StaticCall => 6,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn expr_display_add_mod() {
        let expected = "((caller() + origin()) ﹪ var1)";
        let var = Var::with_id(NonZeroU16::new(1).unwrap());
        let input = Expr {
            ops: vec![Sym::AddMod, Sym::Caller, Sym::Origin, Sym::Var(var)],
        };

        let actual = input.to_string();
        assert_eq!(expected, actual);
    }

    #[test]
    fn expr_display_call() {
        let expected = "call(gas(), caller(), callvalue(), sload(pc(3)), mload(origin()), number(), timestamp())";
        let input = Expr {
            ops: vec![
                Sym::Call,
                Sym::Gas,
                Sym::Caller,
                Sym::CallValue,
                Sym::SLoad,
                Sym::GetPc(3),
                Sym::MLoad,
                Sym::Origin,
                Sym::Number,
                Sym::Timestamp,
            ],
        };

        let actual = input.to_string();
        assert_eq!(expected, actual);
    }

    #[test]
    fn expr_display_add() {
        let expected = "(0x0000000000000000000000000000000000000000000000000000000000000000 + 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)";
        let input = Expr {
            ops: vec![
                Sym::Add,
                Sym::Const(Box::new([0x00; 32])),
                Sym::Const(Box::new([0xff; 32])),
            ],
        };

        let actual = input.to_string();
        assert_eq!(expected, actual);
    }
}
