use std::convert::TryInto;
use std::fmt;
use std::num::NonZeroU16;

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct Var(NonZeroU16);

impl Var {
    pub fn with_id<T>(id: T) -> Self
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

    pub fn address() -> Self {
        Self {
            ops: vec![Sym::Address],
        }
    }

    pub fn origin() -> Self {
        Self {
            ops: vec![Sym::Origin],
        }
    }

    pub fn caller() -> Self {
        Self {
            ops: vec![Sym::Caller],
        }
    }

    pub fn call_value() -> Self {
        Self {
            ops: vec![Sym::CallValue],
        }
    }

    pub fn call_data_size() -> Self {
        Self {
            ops: vec![Sym::CallDataSize],
        }
    }

    pub fn code_size() -> Self {
        Self {
            ops: vec![Sym::CodeSize],
        }
    }

    pub fn gas_price() -> Self {
        Self {
            ops: vec![Sym::GasPrice],
        }
    }

    pub fn return_data_size() -> Self {
        Self {
            ops: vec![Sym::ReturnDataSize],
        }
    }

    pub fn coinbase() -> Self {
        Self {
            ops: vec![Sym::Coinbase],
        }
    }

    pub fn timestamp() -> Self {
        Self {
            ops: vec![Sym::Timestamp],
        }
    }

    pub fn number() -> Self {
        Self {
            ops: vec![Sym::Number],
        }
    }

    pub fn difficulty() -> Self {
        Self {
            ops: vec![Sym::Difficulty],
        }
    }

    pub fn gas_limit() -> Self {
        Self {
            ops: vec![Sym::GasLimit],
        }
    }

    pub fn chain_id() -> Self {
        Self {
            ops: vec![Sym::ChainId],
        }
    }

    pub fn pc(offset: u16) -> Self {
        Self {
            ops: vec![Sym::GetPc(offset)],
        }
    }

    pub fn m_size() -> Self {
        Self {
            ops: vec![Sym::MSize],
        }
    }

    pub fn gas() -> Self {
        Self {
            ops: vec![Sym::Gas],
        }
    }

    pub fn create(value: &Self, offset: &Self, length: &Self) -> Self {
        Self::concat(Sym::Create, &[value, offset, length])
    }

    pub fn create2(value: &Self, offset: &Self, length: &Self, salt: &Self) -> Self {
        Self::concat(Sym::Create2, &[value, offset, length, salt])
    }

    pub fn ext_code_copy(addr: &Self, dest_offset: &Self, offset: &Self, length: &Self) -> Self {
        Self::concat(Sym::ExtCodeCopy, &[addr, dest_offset, offset, length])
    }

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

    pub fn add(&self, rhs: &Self) -> Self {
        Self::concat(Sym::Add, &[self, rhs])
    }

    pub fn sub(&self, rhs: &Self) -> Self {
        Self::concat(Sym::Sub, &[self, rhs])
    }

    pub fn mul(&self, rhs: &Self) -> Self {
        Self::concat(Sym::Mul, &[self, rhs])
    }

    pub fn div(&self, rhs: &Self) -> Self {
        Self::concat(Sym::Div, &[self, rhs])
    }

    pub fn s_div(&self, rhs: &Self) -> Self {
        Self::concat(Sym::SDiv, &[self, rhs])
    }

    pub fn modulo(&self, rhs: &Self) -> Self {
        Self::concat(Sym::Mod, &[self, rhs])
    }

    pub fn s_modulo(&self, rhs: &Self) -> Self {
        Self::concat(Sym::SMod, &[self, rhs])
    }

    pub fn add_mod(&self, add: &Self, modulo: &Self) -> Self {
        Self::concat(Sym::AddMod, &[self, add, modulo])
    }

    pub fn mul_mod(&self, mul: &Self, modulo: &Self) -> Self {
        Self::concat(Sym::MulMod, &[self, mul, modulo])
    }

    pub fn exp(&self, rhs: &Self) -> Self {
        Self::concat(Sym::Exp, &[self, rhs])
    }

    pub fn lt(&self, rhs: &Self) -> Self {
        Self::concat(Sym::Lt, &[self, rhs])
    }

    pub fn gt(&self, rhs: &Self) -> Self {
        Self::concat(Sym::Gt, &[self, rhs])
    }

    pub fn s_lt(&self, rhs: &Self) -> Self {
        Self::concat(Sym::SLt, &[self, rhs])
    }

    pub fn s_gt(&self, rhs: &Self) -> Self {
        Self::concat(Sym::SGt, &[self, rhs])
    }

    pub fn is_eq(&self, rhs: &Self) -> Self {
        Self::concat(Sym::Eq, &[self, rhs])
    }

    pub fn and(&self, rhs: &Self) -> Self {
        Self::concat(Sym::And, &[self, rhs])
    }

    pub fn or(&self, rhs: &Self) -> Self {
        Self::concat(Sym::Or, &[self, rhs])
    }

    pub fn xor(&self, rhs: &Self) -> Self {
        Self::concat(Sym::Xor, &[self, rhs])
    }

    pub fn byte(&self, rhs: &Self) -> Self {
        Self::concat(Sym::Byte, &[self, rhs])
    }

    pub fn shl(&self, rhs: &Self) -> Self {
        Self::concat(Sym::Shl, &[self, rhs])
    }

    pub fn shr(&self, rhs: &Self) -> Self {
        Self::concat(Sym::Shr, &[self, rhs])
    }

    pub fn sar(&self, rhs: &Self) -> Self {
        Self::concat(Sym::Sar, &[self, rhs])
    }

    pub fn keccak256(offset: &Self, len: &Self) -> Self {
        Self::concat(Sym::Keccak256, &[offset, len])
    }

    pub fn sign_extend(&self, b: &Self) -> Self {
        Self::concat(Sym::SignExtend, &[self, b])
    }

    pub fn is_zero(&self) -> Self {
        Self::concat(Sym::IsZero, &[self])
    }

    pub fn not(&self) -> Self {
        Self::concat(Sym::Not, &[self])
    }

    pub fn block_hash(&self) -> Self {
        Self::concat(Sym::BlockHash, &[self])
    }

    pub fn balance(&self) -> Self {
        Self::concat(Sym::Balance, &[self])
    }

    pub fn call_data_load(&self) -> Self {
        Self::concat(Sym::CallDataLoad, &[self])
    }

    pub fn ext_code_size(&self) -> Self {
        Self::concat(Sym::ExtCodeSize, &[self])
    }

    pub fn ext_code_hash(&self) -> Self {
        Self::concat(Sym::ExtCodeHash, &[self])
    }

    pub fn m_load(&self) -> Self {
        Self::concat(Sym::MLoad, &[self])
    }

    pub fn s_load(&self) -> Self {
        Self::concat(Sym::SLoad, &[self])
    }

    pub fn as_var(&self) -> Option<Var> {
        match self.ops.as_slice() {
            [Sym::Var(v)] => Some(*v),
            _ => None,
        }
    }

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
            Sym::Shl => " <<< ",
            Sym::Shr => " >>> ",
            Sym::Sar => " >> ",
            q if q.children() < 2 => unreachable!(),
            _ => ", ",
        };

        write!(self.0, "{}", txt)
    }

    fn enter(&mut self, op: &Sym) -> fmt::Result {
        match op {
            Sym::Const(v) => {
                // TODO: Technically this should be in decimal, not hex.
                write!(self.0, "0x{}", hex::encode(&**v))
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
            Sym::GetPc(pc) => write!(self.0, "pc({}", pc),
            Sym::MSize => write!(self.0, "msize("),
            Sym::Gas => write!(self.0, "gas("),
            Sym::Create => write!(self.0, "create("),
            Sym::ExtCodeCopy => write!(self.0, "extcodecopy("),
            Sym::CallCode => write!(self.0, "callcode("),
            Sym::Call => write!(self.0, "call("),
            Sym::StaticCall => write!(self.0, "staticcall("),
            Sym::DelegateCall => write!(self.0, "delegatecall("),
            _ => write!(self.0, "("),
        }
    }
}

impl Expr {
    fn walk<V>(&self, visitor: &mut V) -> Result<(), V::Error>
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

trait Visit {
    type Error;

    fn empty(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn enter(&mut self, _: &Sym) -> Result<(), Self::Error> {
        Ok(())
    }

    fn between(&mut self, _: &Sym, _: u8) -> Result<(), Self::Error> {
        Ok(())
    }

    fn exit(&mut self, _: &Sym) -> Result<(), Self::Error> {
        Ok(())
    }
}

// TODO: std::mem::size_of::<Sym>() is like 16 bytes. That's HUGE.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
enum Sym {
    Const(Box<[u8; 32]>),
    Var(Var),

    Add,
    Mul,
    Sub,
    Div,
    SDiv,
    Mod,
    SMod,
    AddMod,
    MulMod,
    Exp,
    Lt,
    Gt,
    SLt,
    SGt,
    Eq,
    And,
    Or,
    Xor,
    Byte,
    Shl,
    Shr,
    Sar,
    Keccak256,

    SignExtend,
    IsZero,
    Not,
    CallDataLoad,
    ExtCodeSize,
    ExtCodeHash,
    MLoad,
    SLoad,
    Balance,
    BlockHash,

    Address,
    Origin,
    Caller,
    CallValue,
    CallDataSize,
    CodeSize,
    GasPrice,
    ReturnDataSize,
    Coinbase,
    Timestamp,
    Number,
    Difficulty,
    GasLimit,
    ChainId,
    GetPc(u16),
    MSize,
    Gas,

    Create,

    Create2,
    ExtCodeCopy,

    CallCode,
    Call,

    StaticCall,
    DelegateCall,
}

impl Sym {
    pub fn children(&self) -> u8 {
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
            | Sym::GetPc(_)
            | Sym::MSize
            | Sym::Gas
            | Sym::Const(_)
            | Sym::Var(_) => 0,

            Sym::AddMod | Sym::MulMod | Sym::Create => 3,

            Sym::ExtCodeCopy | Sym::Create2 => 4,

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
