//! Definitions of all instructions supported by the assembler.

mod error {
    use super::expression;
    use etk_ops::london::Op;
    use num_bigint::BigInt;
    use snafu::{Backtrace, Snafu};

    #[derive(Snafu, Debug)]
    #[snafu(context(suffix(false)), visibility(pub(crate)))]
    pub(crate) enum Error {
        ContextIncomplete {
            #[snafu(backtrace)]
            source: expression::Error,
        },
        ExpressionTooLarge {
            source: std::array::TryFromSliceError,
            value: BigInt,
            spec: Op<()>,
            backtrace: Backtrace,
        },
        ExpressionNegative {
            value: BigInt,
            backtrace: Backtrace,
        },
    }

    /// The error that can arise while parsing a specifier from a string.
    #[derive(Debug, Snafu)]
    #[snafu(display("unknown specifier: {}", text))]
    #[snafu(context(suffix(Context)), visibility(pub(super)))]
    #[non_exhaustive]
    pub struct UnknownSpecifierError {
        text: String,
        backtrace: Backtrace,
    }
}

pub(crate) mod expression;
pub(crate) mod imm;
mod macros;
mod types;

pub(crate) use self::error::Error;

use etk_ops::london::{Op, Operation, Push32};

pub use self::error::UnknownSpecifierError;
pub use self::expression::{Context, Expression, Terminal};
pub use self::imm::{Imm, TryFromSliceError};

pub use self::macros::{
    ExpressionMacroDefinition, ExpressionMacroInvocation, InstructionMacroDefinition,
    InstructionMacroInvocation, MacroDefinition,
};
pub use self::types::Abstract;

use std::cmp::{Eq, PartialEq};
use std::convert::{TryFrom, TryInto};
use std::fmt;

use snafu::{ensure, ResultExt};

pub(crate) trait Assemble {
    fn assemble(&self, buf: &mut Vec<u8>);
}

impl<T> Assemble for T
where
    T: Operation,
    T::ImmediateRef: AsRef<[u8]>,
{
    fn assemble(&self, buf: &mut Vec<u8>) {
        buf.push(self.code_byte());
        if let Some(immediate) = self.immediate().map(AsRef::as_ref) {
            buf.extend_from_slice(immediate);
        }
    }
}

pub(crate) trait Concretize {
    type Concrete;

    fn concretize(&self, ctx: Context) -> Result<Self::Concrete, error::Error>;
}

impl Concretize for Op<Abstract> {
    type Concrete = Op<[u8]>;

    fn concretize(&self, ctx: Context) -> Result<Self::Concrete, error::Error> {
        let expr = match self.immediate() {
            Some(i) => &i.tree,
            None => return Ok(Op::new(self.code()).unwrap()),
        };

        let value = expr
            .eval_with_context(ctx)
            .context(error::ContextIncomplete)?;

        let (sign, mut bytes) = value.to_bytes_be();

        ensure!(
            sign != num_bigint::Sign::Minus,
            error::ExpressionNegative { value }
        );

        if bytes.len() < self.extra_len() {
            let mut new = vec![0u8; self.extra_len() - bytes.len()];
            new.append(&mut bytes);
            bytes = new;
        }

        let result = self
            .code()
            .with(bytes.as_slice())
            .context(error::ExpressionTooLarge {
                value,
                spec: self.code(),
            })?;

        Ok(result)
    }
}

trait Expr {
    fn expr(&self) -> Option<&Expression>;
    fn expr_mut(&mut self) -> Option<&mut Expression>;
}

impl<T> Expr for T
where
    T: Operation<ImmediateRef = Imm>,
{
    fn expr(&self) -> Option<&Expression> {
        self.immediate().map(|i| &i.tree)
    }

    fn expr_mut(&mut self) -> Option<&mut Expression> {
        self.immediate_mut().map(|i| &mut i.tree)
    }
}

/// The access mode (read, write, both) of an instruction.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Access {
    /// Indicates that the instruction might read.
    Read,

    /// Indicates that the instruction might write.
    Write,

    /// Indicates that the instruction may read and/or write.
    ReadWrite,
}

impl Access {
    /// Returns true if the instruction might read.
    pub fn reads(self) -> bool {
        matches!(self, Self::Read | Self::ReadWrite)
    }

    /// Returns true if the instruction might write.
    pub fn writes(self) -> bool {
        matches!(self, Self::Write | Self::ReadWrite)
    }
}

/// Like an [`Op`], except it also supports virtual instructions.
///
/// In addition to the real EVM instructions, `AbstractOp` also supports defining
/// labels, and pushing variable length immediate arguments.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum AbstractOp {
    /// A real `Op`, as opposed to a label or variable sized push.
    Op(Op<Abstract>),

    /// A label, which is a virtual instruction.
    Label(String),

    /// A variable sized push, which is a virtual instruction.
    Push(Imm),

    /// A user-defined macro definition, which is a virtual instruction.
    MacroDefinition(MacroDefinition),

    /// A user-defined macro, which is a virtual instruction.
    Macro(InstructionMacroInvocation),
}

impl AbstractOp {
    /// Construct a new `AbstractOp` from an `Operation`.
    pub fn new<O>(op: O) -> Self
    where
        O: Into<Op<Abstract>>,
    {
        Self::Op(op.into())
    }

    pub(crate) fn concretize(self, ctx: Context) -> Result<Op<[u8]>, error::Error> {
        match self {
            Self::Op(op) => op.concretize(ctx),
            Self::Push(imm) => {
                let value = imm
                    .tree
                    .eval_with_context(ctx)
                    .context(error::ContextIncomplete)?;

                let (sign, bytes) = value.to_bytes_be();

                ensure!(
                    sign != num_bigint::Sign::Minus,
                    error::ExpressionNegative { value }
                );

                if bytes.len() > 32 {
                    // TODO: Fix hack to get a TryFromSliceError.
                    let err = <[u8; 32]>::try_from(bytes.as_slice())
                        .context(error::ExpressionTooLarge {
                            value,
                            spec: Push32(()),
                        })
                        .unwrap_err();
                    return Err(err);
                }

                let size = std::cmp::max(1, (value.bits() + 8 - 1) / 8);
                let spec = Op::<()>::push(size.try_into().unwrap()).unwrap();

                let start = bytes.len() + 1 - spec.size();
                AbstractOp::new(spec.with(&bytes[start..]).unwrap()).concretize(ctx)
            }
            Self::Label(_) => panic!("labels cannot be concretized"),
            Self::Macro(_) => panic!("macros cannot be concretized"),
            Self::MacroDefinition(_) => panic!("macro definitions cannot be concretized"),
        }
    }

    /// The expression to be pushed on the stack. Only relevant for push instructions.
    pub(crate) fn expr(&self) -> Option<&Expression> {
        match self {
            Self::Op(op) => op.expr(),
            Self::Push(Imm { tree, .. }) => Some(tree),
            _ => None,
        }
    }

    /// The expression to be pushed on the stack. Only relevant for push instructions.
    pub(crate) fn expr_mut(&mut self) -> Option<&mut Expression> {
        match self {
            Self::Op(op) => op.expr_mut(),
            Self::Push(Imm { tree, .. }) => Some(tree),
            _ => None,
        }
    }

    /// Return the total encoded size for this instruction, including the
    /// immediate if one is required.
    ///
    /// If the size of this instruction is undefined (for example a variable sized
    /// push), this function returns `None`.
    pub fn size(&self) -> Option<usize> {
        match self {
            Self::Op(op) => Some(op.size()),
            Self::Label(_) => Some(0),
            Self::Push(_) => None,
            Self::Macro(_) => None,
            Self::MacroDefinition(_) => None,
        }
    }

    /// Return the specifier that corresponds to this `AbstractOp`.
    pub fn specifier(&self) -> Option<Op<()>> {
        match self {
            Self::Op(op) => Some(op.code()),
            _ => None,
        }
    }
}

impl From<Op<[u8]>> for AbstractOp {
    fn from(cop: Op<[u8]>) -> Self {
        let code = cop.code();
        let cop = match cop.into_immediate() {
            Some(i) => code.with(i).unwrap(),
            None => Op::new(code).unwrap(),
        };
        Self::Op(cop)
    }
}

impl From<InstructionMacroDefinition> for AbstractOp {
    fn from(item: InstructionMacroDefinition) -> Self {
        AbstractOp::MacroDefinition(item.into())
    }
}

impl From<ExpressionMacroDefinition> for AbstractOp {
    fn from(item: ExpressionMacroDefinition) -> Self {
        AbstractOp::MacroDefinition(item.into())
    }
}

impl fmt::Display for AbstractOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Op(op) => {
                write!(f, "{}", op.code())?;
                if let Some(imm) = op.immediate() {
                    write!(f, " {imm}")?;
                }
                Ok(())
            }
            Self::Push(txt) => write!(f, r#"%push({txt})"#),
            Self::Label(lbl) => write!(f, r#"{lbl}:"#),
            Self::Macro(m) => write!(f, "{m}"),
            Self::MacroDefinition(defn) => write!(f, "{defn}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::convert::TryInto;

    use super::*;

    #[test]
    fn u8_into_imm1() {
        let x: u8 = 0xdc;
        let imm: Imm = x.into();
        let res: Imm = Terminal::Number(x.into()).into();
        assert_eq!(imm, res);
    }

    #[test]
    fn u16_try_into_imm1() {
        let x: u16 = 0xFF;
        let imm: Imm = x.try_into().unwrap();
        let res: Imm = Terminal::Number(x.into()).into();
        assert_eq!(imm, res);
    }

    #[test]
    fn u8_into_imm2() {
        let x: u8 = 0xdc;
        let imm: Imm = x.into();
        let res: Imm = Terminal::Number(x.into()).into();
        assert_eq!(imm, res);
    }

    #[test]
    fn u16_into_imm2() {
        let x: u16 = 0xfedc;
        let imm: Imm = x.into();
        let res: Imm = Terminal::Number(x.into()).into();
        assert_eq!(imm, res);
    }

    #[test]
    fn u128_into_imm32() {
        let x: u128 = 0x1023456789abcdef0123456789abcdef;
        let imm: Imm = x.into();
        let res: Imm = Terminal::Number(x.into()).into();
        assert_eq!(imm, res);
    }
}
