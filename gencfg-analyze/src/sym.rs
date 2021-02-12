use std::fmt;

#[derive(Debug, Clone)]
pub struct Expr {
    ops: Vec<Sym>,
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.walk(&mut DisplayVisit(f))
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
            Sym::Var(v) => write!(self.0, "var{}", v),
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
            Sym::GetPc => write!(self.0, "pc("),
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
#[derive(Debug, Clone)]
enum Sym {
    Const(Box<[u8; 32]>),
    Var(u16),

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

    Address,
    Balance,
    Origin,
    Caller,
    CallValue,
    CallDataSize,
    CodeSize,
    GasPrice,
    ReturnDataSize,
    BlockHash,
    Coinbase,
    Timestamp,
    Number,
    Difficulty,
    GasLimit,
    ChainId,
    GetPc,
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
            | Sym::Keccak256 => 2,

            Sym::SignExtend
            | Sym::IsZero
            | Sym::Not
            | Sym::CallDataLoad
            | Sym::ExtCodeSize
            | Sym::ExtCodeHash
            | Sym::MLoad
            | Sym::SLoad => 1,

            Sym::Address
            | Sym::Balance
            | Sym::Origin
            | Sym::Caller
            | Sym::CallValue
            | Sym::CallDataSize
            | Sym::CodeSize
            | Sym::GasPrice
            | Sym::ReturnDataSize
            | Sym::BlockHash
            | Sym::Coinbase
            | Sym::Timestamp
            | Sym::Number
            | Sym::Difficulty
            | Sym::GasLimit
            | Sym::ChainId
            | Sym::GetPc
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
        let expected = "((caller() + origin()) ﹪ var0)";
        let input = Expr {
            ops: vec![Sym::AddMod, Sym::Caller, Sym::Origin, Sym::Var(0)],
        };

        let actual = input.to_string();
        assert_eq!(expected, actual);
    }

    #[test]
    fn expr_display_call() {
        let expected = "call(gas(), caller(), callvalue(), sload(pc()), mload(origin()), number(), timestamp())";
        let input = Expr {
            ops: vec![
                Sym::Call,
                Sym::Gas,
                Sym::Caller,
                Sym::CallValue,
                Sym::SLoad,
                Sym::GetPc,
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
