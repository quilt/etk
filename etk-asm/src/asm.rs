//! Single-scope assembler implementation and related types.
//!
//! See [`Assembler`] for more details on the low-level assembly process, or the
//! [`mod@crate::ingest`] module for a higher-level interface.

mod error {
    use crate::ops::Expression;
    use crate::ParseError;
    use etk_ops::cancun::Op;
    use num_bigint::BigInt;
    use snafu::{Backtrace, Snafu};

    /// Errors that can occur while assembling instructions.
    #[derive(Snafu, Debug)]
    #[non_exhaustive]
    #[snafu(context(suffix(false)), visibility(pub(super)))]
    pub enum Error {
        /// A label was declared multiple times.
        #[snafu(display("label `{}` declared multiple times", label))]
        #[non_exhaustive]
        DuplicateLabel {
            /// The name of the conflicting label.
            label: String,

            /// The location of the error.
            backtrace: Backtrace,
        },

        /// A macro was declared multiple times.
        #[snafu(display("macro `{}` declared multiple times", name))]
        #[non_exhaustive]
        DuplicateMacro {
            /// The name of the conflicting macro.
            name: String,

            /// The location of the error.
            backtrace: Backtrace,
        },

        /// A push instruction was too small for the result of the expression.
        #[snafu(display(
            "the expression `{}={}` was too large for the specifier {}",
            expr,
            value,
            spec
        ))]
        #[non_exhaustive]
        ExpressionTooLarge {
            /// The oversized expression.
            expr: Expression,

            /// The evaluated value of the expression.
            value: BigInt,

            /// The specifier.
            spec: Op<()>,

            /// The location of the error.
            backtrace: Backtrace,
        },

        /// An expression evaluated to a negative number.
        #[snafu(display(
            "the expression `{}={}` is negative and can't be represented as push operand",
            expr,
            value
        ))]
        ExpressionNegative {
            /// The oversized expression.
            expr: Expression,

            /// The evaluated value of the expression.
            value: BigInt,

            /// The location of the error.
            backtrace: Backtrace,
        },

        /// The value provided to an unsized push (`%push`) was too large.
        #[snafu(display("value was too large for any push"))]
        #[non_exhaustive]
        UnsizedPushTooLarge {
            /// The location of the error.
            backtrace: Backtrace,
        },

        /// A label was used without being defined.
        #[snafu(display("labels `{:?}` were never defined", labels))]
        #[non_exhaustive]
        UndeclaredLabels {
            /// The labels that were used without being defined.
            labels: Vec<String>,

            /// The location of the error.
            backtrace: Backtrace,
        },

        /// An instruction macro was used without being defined.
        #[snafu(display("instruction macro `{}` was never defined", name))]
        #[non_exhaustive]
        UndeclaredInstructionMacro {
            /// The macro that was used without being defined.
            name: String,

            /// The location of the error.
            backtrace: Backtrace,
        },

        /// An expression macro was used without being defined.
        #[snafu(display("expression macro `{}` was never defined", name))]
        #[non_exhaustive]
        UndeclaredExpressionMacro {
            /// The macro that was used without being defined.
            name: String,

            /// The location of the error.
            backtrace: Backtrace,
        },

        /// An import or include failed to parse.
        #[snafu(display("include or import failed to parse: {}", source))]
        #[snafu(context(false))]
        #[non_exhaustive]
        ParseInclude {
            /// The next source of this error.
            #[snafu(backtrace)]
            source: ParseError,
        },
    }
}

pub use self::error::Error;
use crate::ops::expression::{self, Terminal};
use crate::ops::{self, AbstractOp, Assemble, Expression, Imm, MacroDefinition};
use etk_ops::cancun::Op;
use rand::Rng;
use snafu::OptionExt;
use std::collections::{hash_map, HashMap, HashSet, VecDeque};

/// An item to be assembled, which can be either an [`AbstractOp`] or a raw byte
/// sequence.
#[derive(Debug, Clone)]
pub enum RawOp {
    /// An instruction to be assembled.
    Op(AbstractOp),

    /// Raw bytes, for example from `%include_hex`, to be included verbatim in
    /// the output.
    Raw(Vec<u8>),
}

impl RawOp {
    fn size(&self) -> Option<usize> {
        match self {
            Self::Op(op) => op.size(),
            Self::Raw(raw) => Some(raw.len()),
        }
    }

    fn expr(&self) -> Option<&Expression> {
        match self {
            Self::Op(op) => op.expr(),
            Self::Raw(_) => None,
        }
    }
}

impl From<AbstractOp> for RawOp {
    fn from(op: AbstractOp) -> Self {
        Self::Op(op)
    }
}

impl From<Vec<u8>> for RawOp {
    fn from(vec: Vec<u8>) -> Self {
        Self::Raw(vec)
    }
}

/// Assembles a series of [`RawOp`] into raw bytes, tracking and resolving macros and labels,
/// and handling dynamic pushes.
///
/// ## Example
///
/// ```rust
/// use etk_asm::asm::Assembler;
/// use etk_asm::ops::AbstractOp;
/// use etk_ops::cancun::{Op, GetPc};
/// # use etk_asm::asm::Error;
/// #
/// # use hex_literal::hex;
/// let mut asm = Assembler::new();
/// asm.push_all(vec![
///     AbstractOp::new(GetPc),
/// ])?;
/// let output = asm.take();
/// asm.finish()?;
/// # assert_eq!(output, hex!("58"));
/// # Result::<(), Error>::Ok(())
/// ```
#[derive(Debug)]
pub struct Assembler {
    /// Assembled ops, ready to be taken.
    ready: Vec<u8>,

    unrolled: Vec<RawOp>,

    /// Labels, in `pending`, associated with an `AbstractOp::Label`.
    declared_labels: HashMap<String, Option<usize>>,

    /// Macros, in `pending`, associated with an `AbstractOp::Macro`.
    declared_macros: HashMap<String, MacroDefinition>,
}

impl Default for Assembler {
    fn default() -> Self {
        Self {
            ready: Default::default(),
            unrolled: Default::default(),
            declared_labels: Default::default(),
            declared_macros: Default::default(),
        }
    }
}

impl Assembler {
    /// Create a new `Assembler`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Collect any assembled instructions that are ready to be output.
    pub fn take(&mut self) -> Vec<u8> {
        self.finish().unwrap();
        std::mem::take(&mut self.ready)
    }

    /// Feed instructions into the `Assembler`.
    ///
    /// Returns the number of bytes that can be collected with [`Assembler::take`].
    pub fn push_all<I, O>(&mut self, ops: I) -> Result<usize, Error>
    where
        I: IntoIterator<Item = O>,
        O: Into<RawOp>,
    {
        for op in ops {
            self.push(op)?;
        }

        Ok(self.unrolled.len())
    }

    /// Insert explicilty declared macros and labels, via `AbstractOp`, and implictly declared
    /// macros and labels via usage in `Op`.
    pub fn declare_content(&mut self, rop: &RawOp) -> Result<(), Error> {
        match rop {
            RawOp::Op(AbstractOp::Label(ref label)) => {
                match self.declared_labels.entry(label.to_owned()) {
                    hash_map::Entry::Occupied(_) => {
                        return error::DuplicateLabel { label }.fail();
                    }
                    hash_map::Entry::Vacant(v) => {
                        v.insert(None); // Still need to calculate final position.
                    }
                }
            }
            RawOp::Op(AbstractOp::MacroDefinition(ref defn)) => {
                match self.declared_macros.entry(defn.name().to_owned()) {
                    hash_map::Entry::Occupied(_) => {
                        return error::DuplicateMacro { name: defn.name() }.fail()
                    }
                    hash_map::Entry::Vacant(v) => {
                        v.insert(defn.to_owned());
                    }
                }
            }
            _ => (),
        };

        Ok(())
    }

    /// Concretize ops given calculated labels
    pub fn finish(&mut self) -> Result<(), Error> {
        for op in self.unrolled.iter() {
            if let RawOp::Op(ref aop) = op {
                let cop = aop
                    .clone()
                    .concretize((&self.declared_labels, &self.declared_macros).into());

                cop.unwrap().assemble(&mut self.ready);
            }
        }
        Ok(())
    }

    /// Feed a single instruction into the `Assembler`.
    ///
    /// Returns the number of bytes that can be collected with [`Assembler::take`]
    pub fn push<O>(&mut self, rop: O) -> Result<usize, Error>
    where
        O: Into<RawOp>,
    {
        let rop = rop.into();

        // Expand instruction macros immediately.
        if let RawOp::Op(AbstractOp::Macro(ref m)) = rop {
            self.expand_macro(&m.name, &m.parameters)?;
            return Ok(self.ready.len());
        }

        // When a label is declared, we need to save its position for the final concretization.
        if let RawOp::Op(AbstractOp::Label(ref label)) = rop {
            self.declared_labels
                .insert(label.to_owned(), Some(self.unrolled.len()));
        }

        self.unrolled.push(rop);
        Ok(self.unrolled.len())
    }

    fn expand_macro(
        &mut self,
        name: &str,
        parameters: &[Expression],
    ) -> Result<Option<usize>, Error> {
        // Remap labels to macro scope.
        match self.declared_macros.get(name).cloned() {
            Some(MacroDefinition::Instruction(mut m)) => {
                if m.parameters.len() != parameters.len() {
                    panic!("invalid number of parameters for macro {}", name);
                }

                let parameters: HashMap<String, Expression> = m
                    .parameters
                    .into_iter()
                    .zip(parameters.iter().cloned())
                    .collect();

                let mut labels = HashMap::<String, String>::new();
                let mut rng = rand::thread_rng();

                // First pass, find locally defined labels and rename them.
                for op in m.contents.iter_mut() {
                    match op {
                        AbstractOp::Label(ref mut label) => {
                            let mangled = format!("{}_{}_{}", m.name, label, rng.gen::<u64>());
                            let old = labels.insert(label.to_owned(), mangled.clone());
                            if old.is_some() {
                                return error::DuplicateLabel {
                                    label: label.to_string(),
                                }
                                .fail();
                            }
                            *label = mangled;
                        }
                        _ => continue,
                    }
                }

                // Second pass, update local label invocations.
                for op in m.contents.iter_mut() {
                    if let Some(expr) = op.expr_mut() {
                        for lbl in expr.labels(&self.declared_macros).unwrap() {
                            if labels.contains_key(&lbl) {
                                expr.replace_label(&lbl, &labels[&lbl]);
                            }
                        }
                    }

                    // Attempt to fill in parameters
                    if let Some(expr) = op.expr_mut() {
                        for (name, value) in parameters.iter() {
                            expr.fill_variable(name, value)
                        }
                    }
                }

                Ok(Some(self.push_all(m.contents)?))
            }
            _ => {
                return error::UndeclaredInstructionMacro {
                    name: name.to_string(),
                }
                .fail()
            }
        }
    }
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
    use num_bigint::{BigInt, Sign};

    #[test]
    fn assemble_variable_push_const_while_pending() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let sz = asm.push_all(vec![
            AbstractOp::Op(Push1(Imm::with_label("label1")).into()),
            AbstractOp::Push(Terminal::Number(0xaabb.into()).into()),
            AbstractOp::Label("label1".into()),
        ])?;
        assert_eq!(5, sz);
        assert_eq!(asm.take(), hex!("600561aabb"));
        Ok(())
    }

    #[test]
    fn assemble_variable_pushes_abab() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let sz = asm.push_all(vec![
            AbstractOp::new(JumpDest),
            AbstractOp::Push(Imm::with_label("label1")),
            AbstractOp::Push(Imm::with_label("label2")),
            AbstractOp::Label("label1".into()),
            AbstractOp::new(GetPc),
            AbstractOp::Label("label2".into()),
            AbstractOp::new(GetPc),
        ])?;
        assert_eq!(7, sz);
        assert_eq!(asm.take(), hex!("5b600560065858"));
        Ok(())
    }

    #[test]
    fn assemble_variable_pushes_abba() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let sz = asm.push_all(vec![
            AbstractOp::new(JumpDest),
            AbstractOp::Push(Imm::with_label("label1")),
            AbstractOp::Push(Imm::with_label("label2")),
            AbstractOp::Label("label2".into()),
            AbstractOp::new(GetPc),
            AbstractOp::Label("label1".into()),
            AbstractOp::new(GetPc),
        ])?;
        assert_eq!(7, sz);
        assert_eq!(asm.take(), hex!("5b600660055858"));
        Ok(())
    }

    #[test]
    fn assemble_variable_push1_multiple() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let sz = asm.push_all(vec![
            AbstractOp::new(JumpDest),
            AbstractOp::Push(Imm::with_label("auto")),
            AbstractOp::Push(Imm::with_label("auto")),
            AbstractOp::Label("auto".into()),
        ])?;
        assert_eq!(5, sz);
        assert_eq!(asm.take(), hex!("5b60056005"));
        Ok(())
    }

    #[test]
    fn assemble_variable_push_const() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let sz = asm.push_all(vec![AbstractOp::Push(
            Terminal::Number((0x00aaaaaaaaaaaaaaaaaaaaaaaa as u128).into()).into(),
        )])?;
        assert_eq!(13, sz);
        assert_eq!(asm.take(), hex!("6baaaaaaaaaaaaaaaaaaaaaaaa"));
        Ok(())
    }

    #[test]
    fn assemble_variable_push_too_large() {
        let v = BigInt::from_bytes_be(Sign::Plus, &[1u8; 33]);

        let mut asm = Assembler::new();
        let err = asm
            .push_all(vec![AbstractOp::Push(Terminal::Number(v).into())])
            .unwrap_err();

        assert_matches!(err, Error::ExpressionTooLarge { .. });
    }

    #[test]
    fn assemble_variable_push_negative() {
        let mut asm = Assembler::new();
        let err = asm
            .push_all(vec![AbstractOp::Push(Terminal::Number((-1).into()).into())])
            .unwrap_err();

        assert_matches!(err, Error::ExpressionNegative { .. });
    }

    #[test]
    fn assemble_variable_push_const0() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let sz = asm.push_all(vec![AbstractOp::Push(
            Terminal::Number((0x00 as u128).into()).into(),
        )])?;
        assert_eq!(2, sz);
        assert_eq!(asm.take(), hex!("6000"));
        Ok(())
    }

    #[test]
    fn assemble_variable_push1_known() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let sz = asm.push_all(vec![
            AbstractOp::new(JumpDest),
            AbstractOp::Label("auto".into()),
            AbstractOp::Push(Imm::with_label("auto")),
        ])?;
        assert_eq!(3, sz);
        assert_eq!(asm.take(), hex!("5b6001"));
        Ok(())
    }

    #[test]
    fn assemble_variable_push1() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let sz = asm.push_all(vec![
            AbstractOp::Push(Imm::with_label("auto")),
            AbstractOp::Label("auto".into()),
            AbstractOp::new(JumpDest),
        ])?;
        assert_eq!(3, sz);
        assert_eq!(asm.take(), hex!("60025b"));
        Ok(())
    }

    #[test]
    fn assemble_variable_push1_reuse() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let sz = asm.push_all(vec![
            AbstractOp::Push(Imm::with_label("auto")),
            AbstractOp::Label("auto".into()),
            AbstractOp::new(JumpDest),
            AbstractOp::new(Push1(Imm::with_label("auto"))),
        ])?;
        assert_eq!(5, sz);
        assert_eq!(asm.take(), hex!("60025b6002"));
        Ok(())
    }

    #[test]
    fn assemble_variable_push2() -> Result<(), Error> {
        let mut asm = Assembler::new();
        asm.push(AbstractOp::Push(Imm::with_label("auto")))?;
        for _ in 0..255 {
            asm.push(AbstractOp::new(GetPc))?;
        }

        asm.push_all(vec![
            AbstractOp::Label("auto".into()),
            AbstractOp::new(JumpDest),
        ])?;

        let mut expected = vec![0x61, 0x01, 0x02];
        expected.extend_from_slice(&[0x58; 255]);
        expected.push(0x5b);
        assert_eq!(asm.take(), expected);

        asm.finish()?;

        Ok(())
    }

    #[test]
    fn assemble_undeclared_label() -> Result<(), Error> {
        let mut asm = Assembler::new();
        asm.push_all(vec![AbstractOp::new(Push1(Imm::with_label("hi")))])?;
        let err = asm.finish().unwrap_err();
        assert_matches!(err, Error::UndeclaredLabels { labels, .. } if labels == vec!["hi"]);
        Ok(())
    }

    #[test]
    fn assemble_jumpdest_no_label() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let sz = asm.push_all(vec![AbstractOp::new(JumpDest)])?;
        assert_eq!(1, sz);
        assert!(asm.declared_labels.is_empty());
        assert_eq!(asm.take(), hex!("5b"));
        Ok(())
    }

    #[test]
    fn assemble_jumpdest_with_label() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let ops = vec![AbstractOp::Label("lbl".into()), AbstractOp::new(JumpDest)];

        let sz = asm.push_all(ops)?;
        assert_eq!(1, sz);
        assert_eq!(asm.declared_labels.len(), 1);
        assert_eq!(asm.declared_labels.get("lbl"), Some(&Some(0)));
        assert_eq!(asm.take(), hex!("5b"));
        Ok(())
    }

    #[test]
    fn assemble_jumpdest_jump_with_label() -> Result<(), Error> {
        let ops = vec![
            AbstractOp::Label("lbl".into()),
            AbstractOp::new(JumpDest),
            AbstractOp::new(Push1(Imm::with_label("lbl"))),
        ];

        let mut asm = Assembler::new();
        let sz = asm.push_all(ops)?;
        assert_eq!(sz, 3);
        assert_eq!(asm.take(), hex!("5b6000"));

        Ok(())
    }

    #[test]
    fn assemble_labeled_pc() -> Result<(), Error> {
        let ops = vec![
            AbstractOp::new(Push1(Imm::with_label("lbl"))),
            AbstractOp::Label("lbl".into()),
            AbstractOp::new(GetPc),
        ];

        let mut asm = Assembler::new();
        let sz = asm.push_all(ops)?;
        assert_eq!(sz, 3);
        assert_eq!(asm.take(), hex!("600258"));

        Ok(())
    }

    #[test]
    fn assemble_jump_jumpdest_with_label() -> Result<(), Error> {
        let ops = vec![
            AbstractOp::new(Push1(Imm::with_label("lbl"))),
            AbstractOp::Label("lbl".into()),
            AbstractOp::new(JumpDest),
        ];

        let mut asm = Assembler::new();
        let sz = asm.push_all(ops)?;
        assert_eq!(sz, 3);
        assert_eq!(asm.take(), hex!("60025b"));

        Ok(())
    }

    #[test]
    fn assemble_label_too_large() {
        let mut ops: Vec<_> = vec![AbstractOp::new(GetPc); 255];
        ops.push(AbstractOp::Label("b".into()));
        ops.push(AbstractOp::new(JumpDest));
        ops.push(AbstractOp::Label("a".into()));
        ops.push(AbstractOp::new(JumpDest));
        ops.push(AbstractOp::new(Push1(Imm::with_label("a"))));
        let mut asm = Assembler::new();
        let err = asm.push_all(ops).unwrap_err();
        assert_matches!(err, Error::ExpressionTooLarge { expr: Expression::Terminal(Terminal::Label(label)), .. } if label == "a");
    }

    #[test]
    fn assemble_label_just_right() -> Result<(), Error> {
        let mut ops: Vec<_> = vec![AbstractOp::new(GetPc); 255];
        ops.push(AbstractOp::Label("b".into()));
        ops.push(AbstractOp::new(JumpDest));
        ops.push(AbstractOp::Label("a".into()));
        ops.push(AbstractOp::new(JumpDest));
        ops.push(AbstractOp::new(Push1(Imm::with_label("b"))));
        let mut asm = Assembler::new();
        let sz = asm.push_all(ops)?;
        assert_eq!(sz, 259);

        let assembled = asm.take();
        asm.finish()?;

        let mut expected = vec![0x58; 255];
        expected.push(0x5b);
        expected.push(0x5b);
        expected.push(0x60);
        expected.push(0xff);

        assert_eq!(assembled, expected);

        Ok(())
    }

    #[test]
    fn assemble_instruction_macro_label_underscore() -> Result<(), Error> {
        let ops = vec![
            InstructionMacroDefinition {
                name: "my_macro".into(),
                parameters: vec![],
                contents: vec![AbstractOp::Label("a".into())],
            }
            .into(),
            InstructionMacroDefinition {
                name: "my".into(),
                parameters: vec![],
                contents: vec![AbstractOp::Label("macro_a".into())],
            }
            .into(),
            AbstractOp::Macro(InstructionMacroInvocation {
                name: "my_macro".into(),
                parameters: vec![],
            }),
            AbstractOp::Macro(InstructionMacroInvocation {
                name: "my".into(),
                parameters: vec![],
            }),
        ];

        let mut asm = Assembler::new();
        let sz = asm.push_all(ops)?;
        assert_eq!(sz, 0);
        let out = asm.take();
        assert_eq!(out, []);

        Ok(())
    }

    #[test]
    fn assemble_instruction_macro_twice() -> Result<(), Error> {
        let ops = vec![
            InstructionMacroDefinition {
                name: "my_macro".into(),
                parameters: vec![],
                contents: vec![
                    AbstractOp::Label("a".into()),
                    AbstractOp::new(JumpDest),
                    AbstractOp::new(Push1(Imm::with_label("a"))),
                    AbstractOp::new(Push1(Imm::with_label("b"))),
                ],
            }
            .into(),
            AbstractOp::Label("b".into()),
            AbstractOp::new(JumpDest),
            AbstractOp::new(Push1(Imm::with_label("b"))),
            AbstractOp::Macro(InstructionMacroInvocation {
                name: "my_macro".into(),
                parameters: vec![],
            }),
            AbstractOp::Macro(InstructionMacroInvocation {
                name: "my_macro".into(),
                parameters: vec![],
            }),
        ];

        let mut asm = Assembler::new();
        let sz = asm.push_all(ops)?;
        assert_eq!(sz, 13);
        let out = asm.take();
        assert_eq!(out, hex!("5b60005b600360005b60086000"));

        Ok(())
    }

    #[test]
    fn assemble_instruction_macro() -> Result<(), Error> {
        let ops = vec![
            InstructionMacroDefinition {
                name: "my_macro".into(),
                parameters: vec![],
                contents: vec![
                    AbstractOp::Label("a".into()),
                    AbstractOp::new(JumpDest),
                    AbstractOp::new(Push1(Imm::with_label("a"))),
                    AbstractOp::new(Push1(Imm::with_label("b"))),
                ],
            }
            .into(),
            AbstractOp::Label("b".into()),
            AbstractOp::new(JumpDest),
            AbstractOp::new(Push1(Imm::with_label("b"))),
            AbstractOp::Macro(InstructionMacroInvocation {
                name: "my_macro".into(),
                parameters: vec![],
            }),
        ];

        let mut asm = Assembler::new();
        let sz = asm.push_all(ops)?;
        assert_eq!(sz, 8);
        let out = asm.take();
        assert_eq!(out, hex!("5b60005b60036000"));

        Ok(())
    }

    #[test]
    fn assemble_instruction_macro_delayed_definition() -> Result<(), Error> {
        let ops = vec![
            AbstractOp::Label("b".into()),
            AbstractOp::new(JumpDest),
            AbstractOp::new(Push1(Imm::with_label("b"))),
            AbstractOp::Macro(InstructionMacroInvocation {
                name: "my_macro".into(),
                parameters: vec![],
            }),
            InstructionMacroDefinition {
                name: "my_macro".into(),
                parameters: vec![],
                contents: vec![
                    AbstractOp::Label("a".into()),
                    AbstractOp::new(JumpDest),
                    AbstractOp::new(Push1(Imm::with_label("a"))),
                    AbstractOp::new(Push1(Imm::with_label("b"))),
                ],
            }
            .into(),
        ];

        let mut asm = Assembler::new();
        let sz = asm.push_all(ops)?;
        assert_eq!(sz, 8);
        let out = asm.take();
        assert_eq!(out, hex!("5b60005b60036000"));

        Ok(())
    }

    #[test]
    fn assemble_instruction_macro_with_variable_push() -> Result<(), Error> {
        let ops = vec![
            AbstractOp::Macro(InstructionMacroInvocation {
                name: "my_macro".into(),
                parameters: vec![],
            }),
            InstructionMacroDefinition {
                name: "my_macro".into(),
                parameters: vec![],
                contents: vec![
                    AbstractOp::new(JumpDest),
                    AbstractOp::Push(Imm::with_label("label1")),
                    AbstractOp::Push(Imm::with_label("label2")),
                    AbstractOp::Label("label1".into()),
                    AbstractOp::new(GetPc),
                    AbstractOp::Label("label2".into()),
                    AbstractOp::new(GetPc),
                ],
            }
            .into(),
        ];

        let mut asm = Assembler::new();
        let sz = asm.push_all(ops)?;
        assert_eq!(7, sz);
        assert_eq!(asm.take(), hex!("5b600560065858"));

        Ok(())
    }

    #[test]
    fn assemble_undeclared_instruction_macro() -> Result<(), Error> {
        let ops = vec![AbstractOp::Macro(
            InstructionMacroInvocation::with_zero_parameters("my_macro".into()),
        )];
        let mut asm = Assembler::new();
        asm.push_all(ops)?;
        let err = asm.finish().unwrap_err();
        assert_matches!(err, Error::UndeclaredInstructionMacro { name, .. } if name == "my_macro");

        Ok(())
    }

    #[test]
    fn assemble_duplicate_instruction_macro() -> Result<(), Error> {
        let ops: Vec<AbstractOp> = vec![
            InstructionMacroDefinition {
                name: "my_macro".into(),
                parameters: vec![],
                contents: vec![AbstractOp::new(Caller)],
            }
            .into(),
            InstructionMacroDefinition {
                name: "my_macro".into(),
                parameters: vec![],
                contents: vec![AbstractOp::new(Caller)],
            }
            .into(),
        ];
        let mut asm = Assembler::new();
        let err = asm.push_all(ops).unwrap_err();
        assert_matches!(err, Error::DuplicateMacro { name, .. } if name == "my_macro");

        Ok(())
    }

    #[test]
    fn assemble_duplicate_labels_in_instruction_macro() -> Result<(), Error> {
        let ops = vec![
            InstructionMacroDefinition {
                name: "my_macro".into(),
                parameters: vec![],
                contents: vec![AbstractOp::Label("a".into()), AbstractOp::Label("a".into())],
            }
            .into(),
            AbstractOp::Macro(InstructionMacroInvocation::with_zero_parameters(
                "my_macro".into(),
            )),
        ];
        let mut asm = Assembler::new();
        let err = asm.push_all(ops).unwrap_err();
        assert_matches!(err, Error::DuplicateLabel { label, .. } if label == "a");

        Ok(())
    }

    // TODO: do we allow label shadowing in macros?
    #[test]
    fn assemble_conflicting_labels_in_instruction_macro() -> Result<(), Error> {
        let ops = vec![
            AbstractOp::Label("a".into()),
            AbstractOp::new(Caller),
            InstructionMacroDefinition {
                name: "my_macro()".into(),
                parameters: vec![],
                contents: vec![
                    AbstractOp::Label("a".into()),
                    AbstractOp::new(Push1(Imm::with_label("a"))),
                ],
            }
            .into(),
            AbstractOp::Macro(InstructionMacroInvocation::with_zero_parameters(
                "my_macro()".into(),
            )),
            AbstractOp::new(Push1(Imm::with_label("a"))),
        ];
        let mut asm = Assembler::new();
        let sz = asm.push_all(ops)?;
        assert_eq!(sz, 5);

        let out = asm.take();
        asm.finish()?;

        assert_eq!(out, hex!("3360016000"));

        Ok(())
    }

    #[test]
    fn assemble_instruction_macro_with_parameters() -> Result<(), Error> {
        let ops = vec![
            InstructionMacroDefinition {
                name: "my_macro".into(),
                parameters: vec!["foo".into(), "bar".into()],
                contents: vec![
                    AbstractOp::new(Push1(Imm::with_variable("foo"))),
                    AbstractOp::new(Push1(Imm::with_variable("bar"))),
                ],
            }
            .into(),
            AbstractOp::Label("b".into()),
            AbstractOp::new(JumpDest),
            AbstractOp::new(Push1(Imm::with_label("b"))),
            AbstractOp::Macro(InstructionMacroInvocation {
                name: "my_macro".into(),
                parameters: vec![
                    BigInt::from_bytes_be(Sign::Plus, &vec![0x42]).into(),
                    Terminal::Label("b".to_string()).into(),
                ],
            }),
        ];

        let mut asm = Assembler::new();
        let sz = asm.push_all(ops)?;
        assert_eq!(sz, 7);
        let out = asm.take();
        assert_eq!(out, hex!("5b600060426000"));

        Ok(())
    }

    #[test]
    fn assemble_expression_push() -> Result<(), Error> {
        let ops = vec![AbstractOp::new(Push1(Imm::with_expression(
            Expression::Plus(1.into(), 1.into()),
        )))];

        let mut asm = Assembler::new();
        let sz = asm.push_all(ops)?;
        assert_eq!(sz, 2);
        let out = asm.take();
        assert_eq!(out, hex!("6002"));

        Ok(())
    }

    #[test]
    fn assemble_expression_negative() -> Result<(), Error> {
        let ops = vec![AbstractOp::new(Push1(Imm::with_expression(
            BigInt::from(-1).into(),
        )))];
        let mut asm = Assembler::new();
        let err = asm.push_all(ops).unwrap_err();
        assert_matches!(err, Error::ExpressionNegative { value, .. } if value == BigInt::from(-1));

        Ok(())
    }

    #[test]
    fn assemble_expression_undeclared_label() -> Result<(), Error> {
        let mut asm = Assembler::new();
        asm.push_all(vec![AbstractOp::new(Push1(Imm::with_expression(
            Terminal::Label(String::from("hi")).into(),
        )))])?;
        let err = asm.finish().unwrap_err();
        assert_matches!(err, Error::UndeclaredLabels { labels, .. } if labels == vec!["hi"]);
        Ok(())
    }

    #[test]
    fn assemble_variable_push_expression_with_undeclared_labels() -> Result<(), Error> {
        let mut asm = Assembler::new();
        asm.push_all(vec![
            AbstractOp::new(JumpDest),
            AbstractOp::Push(Imm::with_expression(Expression::Plus(
                Terminal::Label("foo".into()).into(),
                Terminal::Label("bar".into()).into(),
            ))),
            AbstractOp::new(Gas),
        ])?;
        let err = asm.finish().unwrap_err();
        assert_matches!(err, Error::UndeclaredLabels { labels, .. } if (labels.contains(&"foo".to_string())) && labels.contains(&"bar".to_string()));
        Ok(())
    }

    #[test]
    fn assemble_variable_push1_expression() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let sz = asm.push_all(vec![
            AbstractOp::new(JumpDest),
            AbstractOp::Label("auto".into()),
            AbstractOp::Push(Imm::with_expression(Expression::Plus(
                1.into(),
                Terminal::Label(String::from("auto")).into(),
            ))),
        ])?;
        assert_eq!(3, sz);
        assert_eq!(asm.take(), hex!("5b6002"));
        Ok(())
    }

    #[test]
    fn assemble_expression_with_labels() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let sz = asm.push_all(vec![
            AbstractOp::new(JumpDest),
            AbstractOp::Push(Imm::with_expression(Expression::Plus(
                Terminal::Label(String::from("foo")).into(),
                Terminal::Label(String::from("bar")).into(),
            ))),
            AbstractOp::new(Gas),
            AbstractOp::Label("foo".into()),
            AbstractOp::Label("bar".into()),
        ])?;
        assert_eq!(4, sz);
        assert_eq!(asm.take(), hex!("5b60085a"));
        Ok(())
    }

    #[test]
    fn assemble_expression_macro_push() -> Result<(), Error> {
        let ops = vec![
            ExpressionMacroDefinition {
                name: "foo".into(),
                parameters: vec![],
                content: Imm::with_expression(Expression::Plus(1.into(), 1.into())),
            }
            .into(),
            AbstractOp::new(Push1(Imm::with_macro(ExpressionMacroInvocation {
                name: "foo".into(),
                parameters: vec![],
            }))),
        ];

        let mut asm = Assembler::new();
        let sz = asm.push_all(ops)?;
        assert_eq!(sz, 2);
        let out = asm.take();
        assert_eq!(out, hex!("6002"));

        Ok(())
    }
}
