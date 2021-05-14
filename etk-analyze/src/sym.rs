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

    pub fn byte(&self, value: &Self) -> Self {
        Self::concat(Sym::Byte, &[self, value])
    }

    pub fn shl(&self, rhs: &Self) -> Self {
        Self::concat(Sym::Shl, &[self, rhs])
    }

    pub fn shr(&self, value: &Self) -> Self {
        Self::concat(Sym::Shr, &[self, value])
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

            Sym::Create2 => 4,

            Sym::Call | Sym::CallCode => 7,

            Sym::DelegateCall | Sym::StaticCall => 6,
        }
    }
}

#[cfg(feature = "z3")]
mod z3_visit {
    use super::*;

    use z3::ast::{Ast, Dynamic, BV};
    use z3::{FuncDecl, Sort};

    impl Expr {
        pub(crate) fn to_z3<'z>(&self, context: &'z z3::Context) -> BV<'z> {
            let mut visitor = Z3Visit {
                context,
                arguments: vec![],
            };

            self.walk(&mut visitor).unwrap();

            assert_eq!(visitor.arguments.len(), 1);
            visitor.arguments.remove(0)
        }
    }

    struct Z3Visit<'z> {
        context: &'z z3::Context,
        arguments: Vec<BV<'z>>,
    }

    impl<'z> Z3Visit<'z> {
        fn make_const(&self, bytes: &[u8; 32]) -> BV<'z> {
            // TODO: This is absolutely not the right way to do this.
            let u0 = u64::from_be_bytes(bytes[0..8].try_into().unwrap());
            let u1 = u64::from_be_bytes(bytes[8..16].try_into().unwrap());
            let u2 = u64::from_be_bytes(bytes[16..24].try_into().unwrap());
            let u3 = u64::from_be_bytes(bytes[24..32].try_into().unwrap());

            let bv0 = BV::from_u64(self.context, u0, 64);
            let bv1 = BV::from_u64(self.context, u1, 64);
            let bv2 = BV::from_u64(self.context, u2, 64);
            let bv3 = BV::from_u64(self.context, u3, 64);

            bv0.concat(&bv1).concat(&bv2).concat(&bv3).simplify()
        }

        fn make_var(&self, var: &Var) -> BV<'z> {
            let name = format!("etk{}", var.0);
            BV::new_const(self.context, name, 256)
        }

        fn make_address(&self, name: &str) -> BV<'z> {
            // TODO: Addresses are only 160 bytes.
            BV::new_const(self.context, name, 256)
        }
    }

    impl<'z> Visit for Z3Visit<'z> {
        type Error = std::convert::Infallible;

        fn exit(&mut self, sym: &Sym) -> Result<(), Self::Error> {
            let node = match sym {
                Sym::Const(value) => self.make_const(value),
                Sym::Var(var) => self.make_var(var),

                Sym::Address => self.make_address("address"),
                Sym::Origin => self.make_address("origin"),
                Sym::Caller => self.make_address("caller"),
                Sym::CallValue => BV::new_const(self.context, "callvalue", 256),
                Sym::CallDataSize => BV::new_const(self.context, "calldatasize", 256),
                Sym::CodeSize => BV::new_const(self.context, "codesize", 256),
                Sym::GasPrice => BV::new_const(self.context, "gasprice", 256),
                Sym::ReturnDataSize => BV::fresh_const(self.context, "returndatasize", 256),
                Sym::Coinbase => self.make_address("coinbase"),
                Sym::Timestamp => BV::new_const(self.context, "timestamp", 256),
                Sym::Number => BV::new_const(self.context, "number", 256),
                Sym::Difficulty => BV::new_const(self.context, "difficulty", 256),
                Sym::GasLimit => BV::new_const(self.context, "gaslimit", 256),
                Sym::ChainId => BV::new_const(self.context, "chainid", 256),
                Sym::GetPc(pc) => BV::from_u64(self.context, *pc as u64, 256),
                Sym::MSize => BV::fresh_const(self.context, "msize", 256),
                Sym::Gas => BV::fresh_const(self.context, "gas", 256),

                Sym::Add => {
                    let rhs = self.arguments.pop().unwrap();
                    let lhs = self.arguments.pop().unwrap();

                    lhs + rhs
                }

                Sym::Sub => {
                    let rhs = self.arguments.pop().unwrap();
                    let lhs = self.arguments.pop().unwrap();

                    lhs - rhs
                }

                Sym::Mul => {
                    let rhs = self.arguments.pop().unwrap();
                    let lhs = self.arguments.pop().unwrap();

                    lhs * rhs
                }

                Sym::Div => {
                    let rhs = self.arguments.pop().unwrap();
                    let lhs = self.arguments.pop().unwrap();

                    let zero = BV::from_u64(self.context, 0, 256);
                    rhs._eq(&zero).ite(&zero, &lhs.bvudiv(&rhs))
                }

                Sym::SDiv => {
                    let rhs = self.arguments.pop().unwrap();
                    let lhs = self.arguments.pop().unwrap();

                    let zero = BV::from_u64(self.context, 0, 256);
                    rhs._eq(&zero).ite(&zero, &lhs.bvsdiv(&rhs))
                }

                Sym::Mod => {
                    let rhs = self.arguments.pop().unwrap();
                    let lhs = self.arguments.pop().unwrap();

                    let zero = BV::from_u64(self.context, 0, 256);
                    rhs._eq(&zero).ite(&zero, &lhs.bvurem(&rhs))
                }

                Sym::SMod => {
                    let rhs = self.arguments.pop().unwrap();
                    let lhs = self.arguments.pop().unwrap();

                    let zero = BV::from_u64(self.context, 0, 256);
                    rhs._eq(&zero).ite(&zero, &lhs.bvsmod(&rhs))
                }

                Sym::Exp => {
                    let rhs = self.arguments.pop().unwrap();
                    let lhs = self.arguments.pop().unwrap();

                    // TODO: Probably incorrect, certainly inefficient.
                    //       Something something discrete log problem?
                    lhs.to_int(false).power(&rhs.to_int(false)).to_ast(256)
                }

                Sym::Lt => {
                    let rhs = self.arguments.pop().unwrap();
                    let lhs = self.arguments.pop().unwrap();

                    lhs.bvult(&rhs).ite(
                        &BV::from_u64(&self.context, 1, 256),
                        &BV::from_u64(&self.context, 0, 256),
                    )
                }

                Sym::Gt => {
                    let rhs = self.arguments.pop().unwrap();
                    let lhs = self.arguments.pop().unwrap();

                    lhs.bvugt(&rhs).ite(
                        &BV::from_u64(&self.context, 1, 256),
                        &BV::from_u64(&self.context, 0, 256),
                    )
                }

                Sym::SLt => {
                    let rhs = self.arguments.pop().unwrap();
                    let lhs = self.arguments.pop().unwrap();

                    lhs.bvslt(&rhs).ite(
                        &BV::from_u64(&self.context, 1, 256),
                        &BV::from_u64(&self.context, 0, 256),
                    )
                }

                Sym::SGt => {
                    let rhs = self.arguments.pop().unwrap();
                    let lhs = self.arguments.pop().unwrap();

                    lhs.bvsgt(&rhs).ite(
                        &BV::from_u64(&self.context, 1, 256),
                        &BV::from_u64(&self.context, 0, 256),
                    )
                }

                Sym::Eq => {
                    let rhs = self.arguments.pop().unwrap();
                    let lhs = self.arguments.pop().unwrap();

                    lhs._eq(&rhs).ite(
                        &BV::from_u64(&self.context, 1, 256),
                        &BV::from_u64(&self.context, 0, 256),
                    )
                }

                Sym::And => {
                    let rhs = self.arguments.pop().unwrap();
                    let lhs = self.arguments.pop().unwrap();

                    lhs.bvand(&rhs)
                }

                Sym::Or => {
                    let rhs = self.arguments.pop().unwrap();
                    let lhs = self.arguments.pop().unwrap();

                    lhs.bvor(&rhs)
                }

                Sym::Xor => {
                    let rhs = self.arguments.pop().unwrap();
                    let lhs = self.arguments.pop().unwrap();

                    lhs.bvxor(&rhs)
                }

                Sym::Shl => {
                    let rhs = self.arguments.pop().unwrap();
                    let lhs = self.arguments.pop().unwrap();

                    rhs.bvshl(&lhs)
                }

                Sym::Shr => {
                    let rhs = self.arguments.pop().unwrap();
                    let lhs = self.arguments.pop().unwrap();

                    rhs.bvlshr(&lhs)
                }

                Sym::Sar => {
                    let rhs = self.arguments.pop().unwrap();
                    let lhs = self.arguments.pop().unwrap();

                    rhs.bvashr(&lhs)
                }

                Sym::Not => {
                    let arg = self.arguments.pop().unwrap();
                    arg.bvnot()
                }

                Sym::IsZero => {
                    let arg = self.arguments.pop().unwrap();
                    let zero = BV::from_u64(self.context, 0, 256);
                    arg._eq(&zero).ite(
                        &BV::from_u64(&self.context, 1, 256),
                        &BV::from_u64(&self.context, 0, 256),
                    )
                }

                Sym::Keccak256 => {
                    let _offset = self.arguments.pop().unwrap();
                    let _len = self.arguments.pop().unwrap();

                    // TODO: Better handling, once memory is implemented.
                    BV::fresh_const(self.context, "keccak256", 256)
                }

                Sym::SignExtend => {
                    let _bits = self.arguments.pop().unwrap();
                    let _value = self.arguments.pop().unwrap();

                    todo!()
                }

                Sym::CallDataLoad => {
                    let offset = self.arguments.pop().unwrap();

                    let sort = Sort::bitvector(&self.context, 256);

                    let func = FuncDecl::new(&self.context, "calldataload", &[&sort], &sort);

                    let apply = func.apply(&[&Dynamic::from_ast(&offset)]);
                    apply.as_bv().unwrap()
                }

                Sym::ExtCodeSize => {
                    let _addr = self.arguments.pop().unwrap();
                    BV::fresh_const(self.context, "extcodesize", 256)
                }

                Sym::ExtCodeHash => {
                    let _addr = self.arguments.pop().unwrap();
                    BV::fresh_const(self.context, "extcodehash", 256)
                }

                Sym::MLoad => {
                    let _addr = self.arguments.pop().unwrap();
                    BV::fresh_const(self.context, "mload", 256)
                }

                Sym::SLoad => {
                    let _addr = self.arguments.pop().unwrap();
                    BV::fresh_const(self.context, "sload", 256)
                }

                Sym::Balance => {
                    let _addr = self.arguments.pop().unwrap();
                    BV::fresh_const(self.context, "balance", 256)
                }

                Sym::BlockHash => {
                    let num = self.arguments.pop().unwrap();

                    let sort = Sort::bitvector(&self.context, 256);

                    let func = FuncDecl::new(&self.context, "blockhash", &[&sort], &sort);

                    let apply = func.apply(&[&Dynamic::from_ast(&num)]);
                    apply.as_bv().unwrap()
                }

                Sym::AddMod => {
                    let modulus = self.arguments.pop().unwrap();
                    let rhs = self.arguments.pop().unwrap();
                    let lhs = self.arguments.pop().unwrap();

                    let zero = BV::from_u64(self.context, 0, 256);
                    let addmod = (rhs + lhs).bvurem(&modulus);
                    modulus._eq(&zero).ite(&zero, &addmod)
                }

                Sym::MulMod => {
                    let modulus = self.arguments.pop().unwrap();
                    let rhs = self.arguments.pop().unwrap();
                    let lhs = self.arguments.pop().unwrap();

                    let zero = BV::from_u64(self.context, 0, 256);
                    let addmod = (rhs * lhs).bvurem(&modulus);
                    modulus._eq(&zero).ite(&zero, &addmod)
                }

                Sym::Create => {
                    let _length = self.arguments.pop();
                    let _offset = self.arguments.pop();
                    let _value = self.arguments.pop();

                    BV::fresh_const(self.context, "create", 256)
                }

                Sym::Create2 => {
                    let _salt = self.arguments.pop();
                    let _length = self.arguments.pop();
                    let _offset = self.arguments.pop();
                    let _value = self.arguments.pop();

                    BV::fresh_const(self.context, "create2", 256)
                }

                Sym::CallCode => {
                    let _ret_len = self.arguments.pop();
                    let _ret_offset = self.arguments.pop();
                    let _args_len = self.arguments.pop();
                    let _args_offset = self.arguments.pop();
                    let _value = self.arguments.pop();
                    let _addr = self.arguments.pop();
                    let _gas = self.arguments.pop();

                    BV::fresh_const(self.context, "callcode", 256)
                }

                Sym::Call => {
                    let _ret_len = self.arguments.pop();
                    let _ret_offset = self.arguments.pop();
                    let _args_len = self.arguments.pop();
                    let _args_offset = self.arguments.pop();
                    let _value = self.arguments.pop();
                    let _addr = self.arguments.pop();
                    let _gas = self.arguments.pop();

                    BV::fresh_const(self.context, "call", 256)
                }

                Sym::StaticCall => {
                    let _ret_len = self.arguments.pop();
                    let _ret_offset = self.arguments.pop();
                    let _args_len = self.arguments.pop();
                    let _args_offset = self.arguments.pop();
                    let _addr = self.arguments.pop();
                    let _gas = self.arguments.pop();

                    BV::fresh_const(self.context, "staticcall", 256)
                }

                Sym::DelegateCall => {
                    let _ret_len = self.arguments.pop();
                    let _ret_offset = self.arguments.pop();
                    let _args_len = self.arguments.pop();
                    let _args_offset = self.arguments.pop();
                    let _addr = self.arguments.pop();
                    let _gas = self.arguments.pop();

                    BV::fresh_const(self.context, "delegatecall", 256)
                }

                Sym::Byte => {
                    let value = self.arguments.pop().unwrap();
                    let position = self.arguments.pop().unwrap();

                    let c248 = BV::from_u64(self.context, 248, 256);
                    let c8 = BV::from_u64(self.context, 8, 256);
                    let c255 = BV::from_u64(self.context, 255, 256);

                    let shift = c248 - (position * c8);
                    let shifted = value.bvlshr(&shift);

                    shifted.bvand(&c255)
                }
            };

            self.arguments.push(node);
            Ok(())
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

#[cfg(all(test, feature = "z3"))]
mod z3_tests {
    use hex_literal::hex;

    use super::*;

    use z3::ast::{Ast, BV};
    use z3::SatResult;

    #[test]
    fn sym_to_z3_const() {
        let bytes: [u8; 32] =
            hex!("abcdef0123456789aabbccddeeff001122334455667788999876543210fedcba");
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(bytes)
            .to_z3(&ctx)
            .bvadd(&BV::from_u64(&ctx, 1, 256)); // Add 1 to check endianness.

        let expected_highest = BV::from_u64(&ctx, 0xabcdef0123456789, 64);
        let expected_higher = BV::from_u64(&ctx, 0xaabbccddeeff0011, 64);
        let expected_lower = BV::from_u64(&ctx, 0x2233445566778899, 64);
        let expected_lowest = BV::from_u64(&ctx, 0x9876543210fedcbb, 64);

        let actual_lowest = expr.extract(63, 0);
        let actual_lower = expr.extract(127, 64);
        let actual_higher = expr.extract(191, 128);
        let actual_highest = expr.extract(255, 192);

        // TODO: So this is probably overkill, buuuuut that's fine.
        let solver = z3::Solver::new(&ctx);
        solver.assert(&actual_highest._eq(&expected_highest));
        solver.assert(&actual_higher._eq(&expected_higher));
        solver.assert(&actual_lower._eq(&expected_lower));
        solver.assert(&actual_lowest._eq(&expected_lowest));

        assert_eq!(SatResult::Sat, solver.check());
    }

    #[test]
    fn add_one_and_two() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[1]).add(&Expr::constant(&[2]));
        let ast = expr.to_z3(&ctx).simplify();
        assert_eq!(ast.as_u64(), Some(3));
    }

    #[test]
    fn add_one_and_max() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[1]).add(&Expr::constant(&[0xff; 32]));
        let ast = expr.to_z3(&ctx).simplify();
        assert_eq!(ast.as_u64(), Some(0));
    }

    #[test]
    fn sub_two_from_three() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).sub(&Expr::constant(&[2]));
        let ast = expr.to_z3(&ctx).simplify();
        assert_eq!(ast.as_u64(), Some(1));
    }

    #[test]
    fn sub_max_from_three() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).sub(&Expr::constant(&[0xff; 32]));
        let ast = expr.to_z3(&ctx).simplify();
        assert_eq!(ast.as_u64(), Some(4));
    }

    #[test]
    fn mul_three_by_four() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).mul(&Expr::constant(&[4]));
        let ast = expr.to_z3(&ctx).simplify();
        assert_eq!(ast.as_u64(), Some(12));
    }

    #[test]
    fn mul_max_by_max() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[0xff; 32]).mul(&Expr::constant(&[0xff; 32]));
        let ast = expr.to_z3(&ctx).simplify();
        assert_eq!(ast.as_u64(), Some(1));
    }

    #[test]
    fn div_max_by_max() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[0xff; 32]).div(&Expr::constant(&[0xff; 32]));
        let ast = expr.to_z3(&ctx).simplify();
        assert_eq!(ast.as_u64(), Some(1));
    }

    #[test]
    fn div_one_by_zero() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[1]).div(&Expr::constant(&[0]));
        let ast = expr.to_z3(&ctx).simplify();
        assert_eq!(ast.as_u64(), Some(0));
    }

    #[test]
    fn div_zero_by_zero() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[0]).div(&Expr::constant(&[0]));
        let ast = expr.to_z3(&ctx).simplify();
        assert_eq!(ast.as_u64(), Some(0));
    }

    #[test]
    fn div_zero_by_one() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[0]).div(&Expr::constant(&[1]));
        let ast = expr.to_z3(&ctx).simplify();
        assert_eq!(ast.as_u64(), Some(0));
    }

    #[test]
    fn sdiv_max_by_max() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[0xff; 32]).s_div(&Expr::constant(&[0xff; 32]));
        let ast = expr.to_z3(&ctx).simplify();
        assert_eq!(ast.as_u64(), Some(1));
    }

    #[test]
    fn sdiv_zero_by_zero() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[0]).s_div(&Expr::constant(&[0]));
        let ast = expr.to_z3(&ctx).simplify();
        assert_eq!(ast.as_u64(), Some(0));
    }

    #[test]
    fn sdiv_one_by_max() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[1]).s_div(&Expr::constant(&[0xff; 32]));
        let ast = expr.to_z3(&ctx).simplify();

        let expected = Expr::constant(&[0xff; 32]).to_z3(&ctx);

        assert_eq!(ast, expected);
    }

    #[test]
    fn mod_three_by_two() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).modulo(&Expr::constant(&[2]));
        let ast = expr.to_z3(&ctx).simplify();

        let expected = BV::from_u64(&ctx, 1, 256);

        assert_eq!(ast, expected);
    }

    #[test]
    fn mod_three_by_zero() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).modulo(&Expr::constant(&[0]));
        let ast = expr.to_z3(&ctx).simplify();

        let expected = BV::from_u64(&ctx, 0, 256);

        assert_eq!(ast, expected);
    }

    #[test]
    fn mod_one_by_max() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[1]).modulo(&Expr::constant(&[0xff; 32]));
        let ast = expr.to_z3(&ctx).simplify();

        let expected = BV::from_u64(&ctx, 1, 256);

        assert_eq!(ast, expected);
    }

    #[test]
    fn mod_max_by_one() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[0xff; 32]).modulo(&Expr::constant(&[1]));
        let ast = expr.to_z3(&ctx).simplify();

        let expected = BV::from_u64(&ctx, 0, 256);

        assert_eq!(ast, expected);
    }

    #[test]
    fn smod_zero_by_zero() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[0]).s_modulo(&Expr::constant(&[0]));
        let ast = expr.to_z3(&ctx).simplify();
        assert_eq!(ast.as_u64(), Some(0));
    }

    #[test]
    fn smod_one_by_zero() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[1]).s_modulo(&Expr::constant(&[0]));
        let ast = expr.to_z3(&ctx).simplify();
        assert_eq!(ast.as_u64(), Some(0));
    }

    #[test]
    fn smod_neg_one_by_neg_two() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let mut neg_two = [0xff; 32];
        neg_two[31] = 0xfe;

        let expr = Expr::constant(&[0xff; 32]).s_modulo(&Expr::constant(&neg_two));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = Expr::constant(&[0xff; 32]).to_z3(&ctx);
        assert_eq!(ast, expected);
    }

    #[test]
    fn smod_neg_two_by_neg_one() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let mut neg_two = [0xff; 32];
        neg_two[31] = 0xfe;

        let expr = Expr::constant(&neg_two).s_modulo(&Expr::constant(&[0xff; 32]));
        let ast = expr.to_z3(&ctx).simplify();
        assert_eq!(ast.as_u64(), Some(0));
    }

    #[test]
    fn exp_three_raised_four() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).exp(&Expr::constant(&[4]));
        let ast = expr.to_z3(&ctx).simplify();
        assert_eq!(ast.as_u64(), Some(0x51));
    }

    #[test]
    fn exp_three_raised_zero() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).exp(&Expr::constant(&[0]));
        let ast = expr.to_z3(&ctx).simplify();
        assert_eq!(ast.as_u64(), Some(1));
    }

    #[test]
    fn exp_max_raised_two() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[0xff; 32]).exp(&Expr::constant(&[2]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 1, 256);

        let solver = z3::Solver::new(&ctx);
        solver.assert(&ast._eq(&expected));

        assert_eq!(SatResult::Sat, solver.check());
    }

    #[test]
    fn two_lt_three() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[2]).lt(&Expr::constant(&[3]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 1, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn three_lt_two() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).lt(&Expr::constant(&[2]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn three_lt_three() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).lt(&Expr::constant(&[3]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn two_gt_three() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[2]).gt(&Expr::constant(&[3]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn three_gt_two() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).gt(&Expr::constant(&[2]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 1, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn three_gt_three() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).gt(&Expr::constant(&[3]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn two_sgt_three() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[2]).s_gt(&Expr::constant(&[3]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn three_sgt_two() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).s_gt(&Expr::constant(&[2]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 1, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn three_sgt_three() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).s_gt(&Expr::constant(&[3]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn three_sgt_neg_one() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).s_gt(&Expr::constant(&[0xff; 32]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 1, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn two_slt_three() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[2]).s_lt(&Expr::constant(&[3]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 1, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn three_slt_two() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).s_lt(&Expr::constant(&[2]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn three_slt_three() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).s_lt(&Expr::constant(&[3]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn three_slt_neg_one() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).s_lt(&Expr::constant(&[0xff; 32]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn three_eq_three() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).is_eq(&Expr::constant(&[3]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 1, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn three_eq_max() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).is_eq(&Expr::constant(&[0xff; 32]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn three_and_max() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).and(&Expr::constant(&[0xff; 32]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 3, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn three_and_one() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).and(&Expr::constant(&[1]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 1, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn three_or_max() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).or(&Expr::constant(&[0xff; 32]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = Expr::constant(&[0xff; 32]).to_z3(&ctx);
        assert_eq!(ast, expected);
    }

    #[test]
    fn four_or_one() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[4]).or(&Expr::constant(&[1]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 5, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn three_xor_one() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).xor(&Expr::constant(&[1]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 2, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn byte_32() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let value: [_; 32] =
            hex!("00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff");

        let expr = Expr::constant(&[32]).byte(&Expr::constant(&value));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0x0, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn byte_31() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let value: [_; 32] =
            hex!("00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff");

        let expr = Expr::constant(&[31]).byte(&Expr::constant(&value));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0xff, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn byte_30() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let value: [_; 32] =
            hex!("00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff");

        let expr = Expr::constant(&[30]).byte(&Expr::constant(&value));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0xee, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn byte_0() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let value: [_; 32] =
            hex!("AB112233445566778899aabbccddeeff00112233445566778899aabbccddeeff");

        let expr = Expr::constant(&[0]).byte(&Expr::constant(&value));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0xab, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn shl_one_by_four() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[4]).shl(&Expr::constant(&[1]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0x10, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn shr_selector_by_224() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let mut value = [0u8; 32];
        value[0] = 0x23;
        value[1] = 0xb8;
        value[2] = 0x72;
        value[3] = 0xdd;

        let expr = Expr::constant(&[224]).shr(&Expr::constant(&value));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0x23b872dd, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn shr_max_by_248() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[248]).shr(&Expr::constant(&[0xff; 32]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0xff, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn sar_max_by_248() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[248]).sar(&Expr::constant(&[0xff; 32]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = Expr::constant(&[0xff; 32]).to_z3(&ctx);
        assert_eq!(ast, expected);
    }

    #[test]
    fn sar_one_by_one() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[1]).sar(&Expr::constant(&[1]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn is_zero_one() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[1]).is_zero();
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn is_zero_zero() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[0]).is_zero();
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 1, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn not_max() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[0xff; 32]).not();
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn add_mod_five_and_eight_mod_three() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[5]).add_mod(&Expr::constant(&[8]), &Expr::constant(&[3]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 1, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn add_mod_five_and_eight_mod_zero() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[5]).add_mod(&Expr::constant(&[8]), &Expr::constant(&[0]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn mul_mod_five_and_eight_mod_three() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[5]).mul_mod(&Expr::constant(&[8]), &Expr::constant(&[3]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 1, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn mul_mod_five_and_eight_mod_zero() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[5]).mul_mod(&Expr::constant(&[8]), &Expr::constant(&[0]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0, 256);
        assert_eq!(ast, expected);
    }
}
