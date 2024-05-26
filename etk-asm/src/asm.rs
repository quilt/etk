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

        /// An instruction macro was used without being defined.
        #[snafu(display("variable `{}` inside macro, was never defined", var))]
        #[non_exhaustive]
        UndeclaredVariableMacro {
            /// The variable that was used without being defined.
            var: String,

            /// The location of the error.
            backtrace: Backtrace,
        },

        /// Code containing secions does not start with section declaration.
        #[snafu(display("EOF code does not start with section declaration"))]
        #[non_exhaustive]
        EOFCodeDoesNotStartWithSection,

        /// Code containing secions does not start with section declaration.
        #[snafu(display("EOF data section is not the last section"))]
        #[non_exhaustive]
        EOFDataSectionIsNotTheLast,
    }
}

pub use self::error::Error;
use crate::ops::expression::Error::{UndefinedVariable, UnknownLabel, UnknownMacro};
use crate::ops::{self, AbstractOp, Assemble, EOFSectionKind, Expression, MacroDefinition};
use indexmap::IndexMap;
use num_bigint::BigInt;
use rand::Rng;
use std::collections::{hash_map, HashMap, HashSet};

/// An item to be assembled, which can be either an [`AbstractOp`],
/// the inclusion of a new scope or a raw byte sequence.
#[derive(Debug, Clone)]
pub enum RawOp {
    /// An instruction to be assembled.
    Op(AbstractOp),

    /// A new scope to be created with its corresponding list of operations.
    Scope(Vec<RawOp>),

    /// Raw bytes, for example from `%include_hex`, to be included verbatim in
    /// the output.
    Raw(Vec<u8>),
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

impl From<&AbstractOp> for RawOp {
    fn from(op: &AbstractOp) -> Self {
        Self::Op(op.clone())
    }
}

/// Assembles a series of [`RawOp`] into raw bytes, tracking and resolving macros and labels,
/// and handling variable-sized pushes.
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
/// let code = vec![AbstractOp::new(GetPc)];
/// let result = asm.assemble(&code)?;
/// # assert_eq!(result, hex!("58"));
/// # Result::<(), Error>::Ok(())
/// ```
#[derive(Debug, Default)]
pub struct Assembler {
    /// Assembled ops.
    ready: Vec<RawOp>,

    /// Number of bytes used by the operations in `ready``.
    concrete_len: usize,

    /// Labels associated with an `AbstractOp::Label`.
    declared_labels: IndexMap<String, Option<LabelDef>>,

    /// Macros associated with an `AbstractOp::Macro`.
    declared_macros: HashMap<String, MacroDefinition>,

    /// Labels that have been referred to (ex. with push) but
    /// have not been declared with an `AbstractOp::Label`.
    undeclared_labels: HashSet<String>,

    /// Pushes that are variable-sized and need to be backpatched.
    variable_sized_push: Vec<PushDef>,

    /// Positions of sections, if assembling EOF
    sections: Vec<SectionDef>,
}

/// A label definition.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct LabelDef {
    position: usize,
    updated: bool,
}

impl LabelDef {
    /// Create a new `LabelDef`.
    pub fn new(position: usize) -> Self {
        Self {
            position,
            updated: false,
        }
    }

    /// Get the position of the label.
    pub fn position(&self) -> usize {
        self.position
    }
}

/// A push definition.
#[derive(Clone, Debug, PartialEq)]
pub struct PushDef {
    position: usize,
    op: AbstractOp,
}

impl PushDef {
    /// Create a new `PushDef`.
    pub fn new(op: AbstractOp, position: usize) -> Self {
        Self { op, position }
    }

    /// Get the position of the push.
    pub fn position(&self) -> usize {
        self.position
    }

    /// Get the op from the push.
    pub fn op(&self) -> &AbstractOp {
        &self.op
    }
}

/// An EOF section definition.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct SectionDef {
    position: usize,
    kind: EOFSectionKind,
}

impl Assembler {
    /// Create a new `Assembler`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Feed instructions into the `Assembler`.
    ///
    /// Returns the code of the assembled program.
    pub fn assemble<O>(&mut self, ops: &[O]) -> Result<Vec<u8>, Error>
    where
        O: Into<RawOp> + Clone,
    {
        self.declare_macros(ops)?;

        for op in ops {
            self.push(op.clone().into())?;
        }

        let output = self.backpatch_and_emit()?;
        self.ready.clear();
        Ok(output)
    }

    /// Pre-define macros, via `AbstractOp`, into the `Assembler`.
    ///
    /// This is used to define macros that are used in the same scope.
    fn declare_macros<O>(&mut self, ops: &[O]) -> Result<(), Error>
    where
        O: Into<RawOp> + Clone,
    {
        for op in ops {
            let rop = op.clone().into();
            if let RawOp::Op(AbstractOp::MacroDefinition(ref defn)) = rop {
                match self.declared_macros.entry(defn.name().to_owned()) {
                    hash_map::Entry::Occupied(_) => {
                        return error::DuplicateMacro { name: defn.name() }.fail()
                    }
                    hash_map::Entry::Vacant(v) => {
                        v.insert(defn.to_owned());
                    }
                }
            }
        }

        Ok(())
    }

    /// Feed a single instruction into the `Assembler`.
    fn push<O>(&mut self, rop: O) -> Result<usize, Error>
    where
        O: Into<RawOp>,
    {
        let rop = rop.into();
        self.declare_label(&rop)?;

        match rop {
            RawOp::Op(AbstractOp::Label(label)) => {
                self.undeclared_labels.retain(|l| *l != label);

                let old = self
                    .declared_labels
                    .insert(
                        label,
                        Some(LabelDef {
                            position: self.concrete_len,
                            updated: false,
                        }),
                    )
                    .expect("label should exist");
                assert_eq!(old, None, "label should have been undefined");
            }
            RawOp::Op(AbstractOp::MacroDefinition(_)) => {}
            RawOp::Op(AbstractOp::Macro(ref m)) => {
                self.expand_macro(&m.name, &m.parameters)?;
            }
            RawOp::Op(AbstractOp::EOFSection(kind)) => self.sections.push(SectionDef {
                position: self.concrete_len,
                kind,
            }),
            RawOp::Op(ref op) => {
                match op
                    .clone()
                    .concretize((&self.declared_labels, &self.declared_macros).into())
                {
                    Ok(cop) => {
                        self.concrete_len += cop.size();
                        self.ready.push(rop.clone())
                    }
                    Err(ops::Error::ExpressionTooLarge { value, spec, .. }) => {
                        return error::ExpressionTooLarge {
                            expr: op.expr().unwrap().clone(),
                            value,
                            spec,
                        }
                        .fail()
                    }
                    Err(ops::Error::ExpressionNegative { value, .. }) => {
                        return error::ExpressionNegative {
                            expr: op.expr().unwrap().clone(),
                            value,
                        }
                        .fail()
                    }
                    Err(ops::Error::ContextIncomplete {
                        source: UnknownLabel { .. },
                    }) => {
                        let labels = op
                            .expr()
                            .unwrap()
                            .labels(&self.declared_macros)
                            .unwrap()
                            .into_iter()
                            .collect::<Vec<String>>();

                        if let AbstractOp::Push(_) = op {
                            // Here, we set the size of the push to 2 bytes (min possible value),
                            //  as we don't know the final value of the label yet.
                            self.concrete_len += 2;
                            self.variable_sized_push.push(PushDef {
                                position: self.concrete_len,
                                op: op.clone(),
                            });
                        } else {
                            self.concrete_len += op.size().unwrap();
                        }

                        self.undeclared_labels.extend(labels);
                        self.ready.push(rop.clone());
                    }
                    Err(ops::Error::ContextIncomplete {
                        source: UnknownMacro { name, .. },
                    }) => return error::UndeclaredInstructionMacro { name }.fail(),
                    Err(ops::Error::ContextIncomplete {
                        source: UndefinedVariable { name, .. },
                    }) => return error::UndeclaredVariableMacro { var: name }.fail(),
                }
            }
            RawOp::Raw(raw) => {
                self.concrete_len += raw.len();
                self.ready.push(RawOp::Raw(raw.to_vec()));
            }
            RawOp::Scope(scope) => {
                let mut asm = Self::new();
                let scope_result = asm.assemble(&scope)?;
                self.concrete_len += scope_result.len();
                self.ready.push(RawOp::Raw(scope_result));
            }
        }

        Ok(self.concrete_len)
    }

    fn backpatch_labels_and_sections(&mut self) -> Result<(), Error> {
        for pushdef in self.variable_sized_push.iter() {
            if let AbstractOp::Push(imm) = &pushdef.op {
                let exp = imm
                    .tree
                    .eval_with_context((&self.declared_labels, &self.declared_macros).into());

                if let Ok(val) = exp {
                    let val_bits = BigInt::bits(&val).max(1);
                    let imm_size = 1 + ((val_bits - 1) / 8);

                    if imm_size > 1 {
                        for label_value in self.declared_labels.values_mut() {
                            let labeldef = label_value.as_ref().unwrap();
                            if labeldef.position < pushdef.position {
                                // don't move labels that are declared earlier than this push
                                continue;
                            };
                            self.concrete_len += imm_size as usize - 1;

                            *label_value = Some(LabelDef {
                                position: labeldef.position + imm_size as usize - 1,
                                updated: true,
                            });
                        }
                        for section in self.sections.iter_mut() {
                            if section.position < pushdef.position {
                                // don't move sections that are declared earlier than this push
                                continue;
                            };

                            section.position += imm_size as usize - 1;
                            // TODO check whether `updated` flag is needed
                        }
                    }
                }
            }
        }

        Ok(())
    }

    /// Backpatch variable-sized operations and emit the assembled program.
    ///
    /// This function performs the final steps in the assembly process. It ensures that all labels
    /// and variable-sized ops in the code have been properly resolved and finalized. This includes
    /// handling variable-sized push instructions, where the actual size of the push may not be known
    /// until all labels and expressions have been evaluated.
    ///
    /// Handle Variable-sized Pushes: The size of a push operation may depend on the value being pushed, especially
    /// when labels are involved. As labels could be resolved to different addresses during the
    /// assembly process, the final value of a label (and thus the size of the push) might only be
    /// known at this stage. This function recalculates the size of each push operation based on the
    /// final resolved values of labels and expressions. If a push operation requires more space than
    /// initially estimated, the function adjusts the code accordingly.
    fn backpatch_and_emit(&mut self) -> Result<Vec<u8>, Error> {
        if !self.undeclared_labels.is_empty() {
            return error::UndeclaredLabels {
                labels: self
                    .undeclared_labels
                    .iter()
                    .map(|l| l.to_owned())
                    .collect::<Vec<String>>(),
            }
            .fail();
        }
        self.backpatch_labels_and_sections()?;
        let output = match self.emit_bytecode() {
            Ok(value) => value,
            Err(value) => return value,
        };

        Ok(output)
    }

    fn emit_bytecode(&mut self) -> Result<Vec<u8>, Result<Vec<u8>, Error>> {
        let mut output = Vec::new();
        if !self.sections.is_empty() {
            if let Err(err) = self.emit_eof_header(&mut output) {
                return Err(Err(err)); // Convert the error to the nested `Result` type
            }
        }

        for op in self.ready.iter() {
            let op = match op {
                RawOp::Op(ref op) => op,
                RawOp::Raw(raw) => {
                    output.extend(raw);
                    continue;
                }
                RawOp::Scope(_) => unreachable!("scopes should be expanded"),
            };

            match op
                .clone()
                .concretize((&self.declared_labels, &self.declared_macros).into())
            {
                Ok(cop) => cop.assemble(&mut output),
                Err(ops::Error::ContextIncomplete {
                    source: UnknownLabel { .. },
                }) => {
                    return Err(error::UndeclaredLabels {
                        labels: self.undeclared_labels.iter().cloned().collect::<Vec<_>>(),
                    }
                    .fail());
                }
                Err(ops::Error::ContextIncomplete {
                    source: UnknownMacro { name, .. },
                }) => {
                    return Err(error::UndeclaredInstructionMacro { name }.fail());
                }
                Err(ops::Error::ContextIncomplete {
                    source: UndefinedVariable { name, .. },
                }) => {
                    return Err(error::UndeclaredVariableMacro { var: name }.fail());
                }
                Err(_) => unreachable!("all ops should be concretizable"),
            }
        }
        Ok(output)
    }

    fn emit_eof_header(&self, output: &mut Vec<u8>) -> Result<(), Error> {
        // Error if some code preceeds 0th section declaration
        if self.sections.first().unwrap().position != 0 {
            return error::EOFCodeDoesNotStartWithSection.fail();
        }

        // Error if data section is not the last
        if let Some(index) = self
            .sections
            .iter()
            .position(|&section| section.kind == EOFSectionKind::Data)
        {
            if index != self.sections.len() - 1 {
                return error::EOFDataSectionIsNotTheLast.fail();
            }
        }

        // Calculate section sizes
        let mut code_section_sizes = Vec::with_capacity(self.sections.len());
        let mut data_section_size = 0;
        for section_bounds in self.sections.windows(2) {
            if let [start, end] = section_bounds {
                code_section_sizes.push(end.position - start.position);
            }
        }

        // add last section
        if let Some(&last_section) = self.sections.last() {
            let last_section_size = self.concrete_len - last_section.position;
            if last_section.kind == EOFSectionKind::Code {
                code_section_sizes.push(last_section_size);
            } else {
                data_section_size = last_section_size
            }
        }

        output.extend_from_slice(&[0xef, 0x00, 0x01]);
        // Type section header
        output.push(0x01);
        let type_section_size = (code_section_sizes.len() * 4) as u16;
        output.extend_from_slice(&type_section_size.to_be_bytes());
        // Code section headers
        output.push(0x02);

        let code_section_num = code_section_sizes.len() as u16;
        output.extend_from_slice(&code_section_num.to_be_bytes());

        for code_section_size in &code_section_sizes {
            let size = *code_section_size as u16;
            output.extend_from_slice(&size.to_be_bytes());
        }
        // data section header + terminator
        output.push(0x04);
        output.extend_from_slice(&data_section_size.to_be_bytes());
        // terminator
        output.push(0x00);
        // types section
        for _ in code_section_sizes {
            // TODO all functions are 0 inputs, non-returning, 0 max stack for now
            output.extend_from_slice(&[0x00, 0x80, 0x00, 0x00]);
        }
        Ok(())
    }

    fn declare_label(&mut self, rop: &RawOp) -> Result<(), Error> {
        if let RawOp::Op(AbstractOp::Label(label)) = rop {
            if self.declared_labels.contains_key(label) {
                return error::DuplicateLabel {
                    label: label.to_owned(),
                }
                .fail();
            }
            self.declared_labels.insert(label.to_owned(), None);
        }
        Ok(())
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

                for op in m.contents.iter() {
                    self.push(op)?;
                }
                Ok(Some(self.concrete_len))
            }
            _ => error::UndeclaredInstructionMacro { name }.fail(),
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
        let code = vec![
            AbstractOp::Op(Push1(Imm::with_label("label1")).into()),
            AbstractOp::Push(Terminal::Number(0xaabb.into()).into()),
            AbstractOp::Label("label1".into()),
        ];
        let result = asm.assemble(&code)?;
        assert_eq!(result, hex!("600561aabb"));
        Ok(())
    }

    #[test]
    fn assemble_variable_pushes_abab() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let code = vec![
            AbstractOp::new(JumpDest),
            AbstractOp::Push(Imm::with_label("label1")),
            AbstractOp::Push(Imm::with_label("label2")),
            AbstractOp::Label("label1".into()),
            AbstractOp::new(GetPc),
            AbstractOp::Label("label2".into()),
            AbstractOp::new(GetPc),
        ];
        let result = asm.assemble(&code)?;
        assert_eq!(result, hex!("5b600560065858"));
        Ok(())
    }

    #[test]
    fn assemble_variable_pushes_abba() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let code = vec![
            AbstractOp::new(JumpDest),
            AbstractOp::Push(Imm::with_label("label1")),
            AbstractOp::Push(Imm::with_label("label2")),
            AbstractOp::Label("label2".into()),
            AbstractOp::new(GetPc),
            AbstractOp::Label("label1".into()),
            AbstractOp::new(GetPc),
        ];
        let result = asm.assemble(&code)?;
        assert_eq!(result, hex!("5b600660055858"));
        Ok(())
    }

    #[test]
    fn assemble_variable_push1_multiple() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let code = vec![
            AbstractOp::new(JumpDest),
            AbstractOp::Push(Imm::with_label("auto")),
            AbstractOp::Push(Imm::with_label("auto")),
            AbstractOp::Label("auto".into()),
        ];
        let result = asm.assemble(&code)?;
        assert_eq!(result, hex!("5b60056005"));
        Ok(())
    }

    #[test]
    fn assemble_variable_push_const() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let code = vec![AbstractOp::Push(
            Terminal::Number((0x00aaaaaaaaaaaaaaaaaaaaaaaa as u128).into()).into(),
        )];
        let result = asm.assemble(&code)?;
        assert_eq!(result, hex!("6baaaaaaaaaaaaaaaaaaaaaaaa"));
        Ok(())
    }

    #[test]
    fn assemble_variable_push_too_large() {
        let v = BigInt::from_bytes_be(Sign::Plus, &[1u8; 33]);

        let mut asm = Assembler::new();
        let code = vec![AbstractOp::Push(Terminal::Number(v).into())];
        let err = asm.assemble(&code).unwrap_err();

        assert_matches!(err, Error::ExpressionTooLarge { .. });
    }

    #[test]
    fn assemble_variable_push_negative() {
        let mut asm = Assembler::new();
        let code = vec![AbstractOp::Push(Terminal::Number((-1).into()).into())];
        let err = asm.assemble(&code).unwrap_err();

        assert_matches!(err, Error::ExpressionNegative { .. });
    }

    #[test]
    fn assemble_variable_push_const0() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let code = vec![AbstractOp::Push(
            Terminal::Number((0x00 as u128).into()).into(),
        )];
        let result = asm.assemble(&code)?;
        assert_eq!(result, hex!("6000"));
        Ok(())
    }

    #[test]
    fn assemble_variable_push1_known() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let code = vec![
            AbstractOp::new(JumpDest),
            AbstractOp::Label("auto".into()),
            AbstractOp::Push(Imm::with_label("auto")),
        ];
        let result = asm.assemble(&code)?;
        assert_eq!(result, hex!("5b6001"));
        Ok(())
    }

    #[test]
    fn assemble_variable_push1() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let code = vec![
            AbstractOp::Push(Imm::with_label("auto")),
            AbstractOp::Label("auto".into()),
            AbstractOp::new(JumpDest),
        ];
        let result = asm.assemble(&code)?;
        assert_eq!(result, hex!("60025b"));
        Ok(())
    }

    #[test]
    fn assemble_variable_push1_reuse() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let code = vec![
            AbstractOp::Push(Imm::with_label("auto")),
            AbstractOp::Label("auto".into()),
            AbstractOp::new(JumpDest),
            AbstractOp::new(Push1(Imm::with_label("auto"))),
        ];
        let result = asm.assemble(&code)?;
        assert_eq!(result, hex!("60025b6002"));
        Ok(())
    }

    #[test]
    fn assemble_variable_push2() -> Result<(), Error> {
        let mut code = vec![];
        code.push(AbstractOp::Push(Imm::with_label("auto")));
        for _ in 0..255 {
            code.push(AbstractOp::new(GetPc));
        }

        code.push(AbstractOp::Label("auto".into()));
        code.push(AbstractOp::new(JumpDest));

        let mut asm = Assembler::new();
        let result = asm.assemble(&code)?;

        let mut expected = vec![0x61, 0x01, 0x02];
        expected.extend_from_slice(&[0x58; 255]);
        expected.push(0x5b);
        assert_eq!(result, expected);

        Ok(())
    }

    #[test]
    fn assemble_variable_push3() -> Result<(), Error> {
        let mut code = vec![];
        code.push(AbstractOp::Push(Imm::with_label("auto")));
        for _ in 0..65537 {
            code.push(AbstractOp::new(GetPc));
        }

        code.push(AbstractOp::Label("auto".into()));
        code.push(AbstractOp::new(JumpDest));

        let mut asm = Assembler::new();
        let result = asm.assemble(&code)?;

        let mut expected = vec![0x62, 0x01, 0x00, 0x05];
        expected.extend_from_slice(&[0x58; 65537]);
        expected.push(0x5b);

        assert_eq!(result, expected);

        Ok(())
    }

    #[test]
    fn assemble_undeclared_label() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let code = vec![AbstractOp::new(Push1(Imm::with_label("hi")))];
        let err = asm.assemble(&code).unwrap_err();
        assert_matches!(err, Error::UndeclaredLabels { labels, .. } if labels == vec!["hi"]);
        Ok(())
    }

    #[test]
    fn assemble_jumpdest_no_label() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let code = vec![AbstractOp::new(JumpDest)];
        let result = asm.assemble(&code)?;
        assert!(asm.declared_labels.is_empty());
        assert_eq!(result, hex!("5b"));
        Ok(())
    }

    #[test]
    fn assemble_jumpdest_with_label() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let ops = vec![AbstractOp::Label("lbl".into()), AbstractOp::new(JumpDest)];

        let result = asm.assemble(&ops)?;
        assert_eq!(asm.declared_labels.len(), 1);
        assert_eq!(
            asm.declared_labels.get("lbl"),
            Some(&Some(LabelDef {
                position: 0,
                updated: false
            }))
        );
        assert_eq!(result, hex!("5b"));
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
        let result = asm.assemble(&ops)?;
        assert_eq!(result, hex!("5b6000"));

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
        let result = asm.assemble(&ops)?;
        assert_eq!(result, hex!("600258"));

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
        let result = asm.assemble(&ops)?;
        assert_eq!(result, hex!("60025b"));

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
        let err = asm.assemble(&ops).unwrap_err();
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
        let result = asm.assemble(&ops)?;

        let mut expected = vec![0x58; 255];
        expected.push(0x5b);
        expected.push(0x5b);
        expected.push(0x60);
        expected.push(0xff);

        assert_eq!(result, expected);

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
        let result = asm.assemble(&ops)?;
        assert_eq!(result, []);

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
        let result = asm.assemble(&ops)?;
        assert_eq!(result, hex!("5b60005b600360005b60086000"));

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
        let result = asm.assemble(&ops)?;
        assert_eq!(result, hex!("5b60005b60036000"));

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
        let result = asm.assemble(&ops)?;
        assert_eq!(result, hex!("5b60005b60036000"));

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
        let result = asm.assemble(&ops)?;
        assert_eq!(result, hex!("5b600560065858"));

        Ok(())
    }

    #[test]
    fn assemble_undeclared_instruction_macro() -> Result<(), Error> {
        let ops = vec![AbstractOp::Macro(
            InstructionMacroInvocation::with_zero_parameters("my_macro".into()),
        )];
        let mut asm = Assembler::new();
        let err = asm.assemble(&ops).unwrap_err();
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
        let err = asm.assemble(&ops).unwrap_err();
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
        let err = asm.assemble(&ops).unwrap_err();
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
        let result = asm.assemble(&ops)?;

        assert_eq!(result, hex!("3360016000"));

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
        let result = asm.assemble(&ops)?;
        assert_eq!(result, hex!("5b600060426000"));

        Ok(())
    }

    #[test]
    fn assemble_expression_push() -> Result<(), Error> {
        let ops = vec![AbstractOp::new(Push1(Imm::with_expression(
            Expression::Plus(1.into(), 1.into()),
        )))];

        let mut asm = Assembler::new();
        let result = asm.assemble(&ops)?;
        assert_eq!(result, hex!("6002"));

        Ok(())
    }

    #[test]
    fn assemble_expression_negative() -> Result<(), Error> {
        let ops = vec![AbstractOp::new(Push1(Imm::with_expression(
            BigInt::from(-1).into(),
        )))];
        let mut asm = Assembler::new();
        let err = asm.assemble(&ops).unwrap_err();
        assert_matches!(err, Error::ExpressionNegative { value, .. } if value == BigInt::from(-1));

        Ok(())
    }

    #[test]
    fn assemble_expression_undeclared_label() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let ops = vec![AbstractOp::new(Push1(Imm::with_expression(
            Terminal::Label(String::from("hi")).into(),
        )))];
        let err = asm.assemble(&ops).unwrap_err();
        assert_matches!(err, Error::UndeclaredLabels { labels, .. } if labels == vec!["hi"]);
        Ok(())
    }

    #[test]
    fn assemble_variable_push_before_push2() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let ops = vec![
            AbstractOp::Push(Imm::with_expression(Expression::Plus(
                Terminal::Label("foo".into()).into(),
                BigInt::from(256).into(),
            ))),
            AbstractOp::new(Push2(Imm::with_label("foo1"))),
            AbstractOp::Label("foo".into()),
            AbstractOp::Label("foo1".into()),
        ];
        let result = asm.assemble(&ops)?;
        assert_eq!(result, hex!("610106610006"));
        Ok(())
    }

    #[test]
    fn assemble_variable_push_before_push2_inverted() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let ops = vec![
            AbstractOp::Push(Imm::with_expression(Expression::Plus(
                Terminal::Label("z".into()).into(),
                BigInt::from(256).into(),
            ))),
            AbstractOp::new(Push2(Imm::with_label("a"))),
            AbstractOp::Label("z".into()),
            AbstractOp::Label("a".into()),
        ];
        let result = asm.assemble(&ops)?;
        assert_eq!(result, hex!("610106610006"));
        Ok(())
    }

    #[test]
    fn assemble_variable_push_mixed_labels() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let ops = vec![
            AbstractOp::Push(Imm::with_expression(Expression::Plus(
                Terminal::Label("foo".into()).into(),
                BigInt::from(256).into(),
            ))),
            AbstractOp::new(Push2(Imm::with_label("foo"))),
            AbstractOp::Push(Imm::with_expression(Expression::Plus(
                Terminal::Label("bar".into()).into(),
                BigInt::from(256).into(),
            ))),
            AbstractOp::new(Gas),
            AbstractOp::Label("foo".into()),
            AbstractOp::new(Gas),
            AbstractOp::Label("bar".into()),
        ];
        let result = asm.assemble(&ops)?;

        assert_eq!(result, hex!("61010a61000a61010b5a5a"));
        Ok(())
    }

    #[test]
    fn assemble_double_update_variable_push() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let ops = vec![
            AbstractOp::Push(Imm::with_expression(Expression::Plus(
                Terminal::Label("foo".into()).into(),
                BigInt::from(256).into(),
            ))),
            AbstractOp::new(Push2(Imm::with_label("foo1"))),
            AbstractOp::Push(Imm::with_expression(Expression::Plus(
                Terminal::Label("foo".into()).into(),
                BigInt::from(256).into(),
            ))),
            AbstractOp::Label("foo".into()),
            AbstractOp::Label("foo1".into()),
        ];
        let result = asm.assemble(&ops)?;
        assert_eq!(result, hex!("610109610009610109"));
        Ok(())
    }

    #[test]
    fn assemble_double_update_variable_push2() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let ops = vec![
            AbstractOp::Push(Imm::with_expression(Expression::Plus(
                Terminal::Label("foo".into()).into(),
                BigInt::from(256).into(),
            ))),
            AbstractOp::new(Push2(Imm::with_label("foo1"))),
            AbstractOp::Push(Imm::with_expression(Expression::Plus(
                Terminal::Label("foo".into()).into(),
                BigInt::from(256).into(),
            ))),
            AbstractOp::new(Push2(Imm::with_label("foo1"))),
            AbstractOp::Label("foo".into()),
            AbstractOp::Label("foo1".into()),
        ];
        let result = asm.assemble(&ops)?;
        assert_eq!(result, hex!("61010c61000c61010c61000c"));
        Ok(())
    }

    #[test]
    fn assemble_variable_push_expression_with_undeclared_labels() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let ops = vec![
            AbstractOp::new(JumpDest),
            AbstractOp::Push(Imm::with_expression(Expression::Plus(
                Terminal::Label("foo".into()).into(),
                Terminal::Label("bar".into()).into(),
            ))),
            AbstractOp::new(Gas),
        ];
        let err = asm.assemble(&ops).unwrap_err();
        // The expressions have short-circuit evaluation, so only the first label is caught in the error.
        assert_matches!(err, Error::UndeclaredLabels { labels, .. } if (labels.contains(&"foo".to_string())));
        Ok(())
    }

    #[test]
    fn assemble_variable_push2_comparison_with_undeclared_labels() -> Result<(), Error> {
        let mut asm = Assembler::new();

        // %push(lbl1 - lbl2)
        // push2 lbl1 + lbl2
        // pc # repeat 126 times.
        // lbl1:
        // lbl2:
        let mut ops = vec![AbstractOp::new(GetPc); 130];
        ops[0] = AbstractOp::Push(Imm::with_expression(Expression::Minus(
            Terminal::Label(String::from("lbl1")).into(),
            Terminal::Label(String::from("lbl2")).into(),
        )));
        ops[1] = AbstractOp::new(Push2(
            Expression::Plus(
                Terminal::Label(String::from("lbl1")).into(),
                Terminal::Label(String::from("lbl2")).into(),
            )
            .into(),
        ));
        ops[128] = AbstractOp::Label("lbl1".into());
        ops[129] = AbstractOp::Label("lbl2".into());

        let expected = asm.assemble(&ops)?;

        let mut asm = Assembler::new();

        // %push(lbl1 - lbl2)
        // %push(lbl1 + lbl2)
        // pc # repeat 126 times.
        // lbl1:
        // lbl2:
        ops[1] = AbstractOp::Push(Imm::with_expression(Expression::Plus(
            Terminal::Label(String::from("lbl1")).into(),
            Terminal::Label(String::from("lbl2")).into(),
        )));
        let result = asm.assemble(&ops)?;

        // Sanity check the expected result: should use push1 then push2.
        assert_eq!(expected[0], 0x60);
        assert_eq!(expected[2], 0x61);

        // Assert that the two results are identical.
        assert_eq!(expected, result);
        Ok(())
    }

    #[test]
    fn assemble_variable_push1_expression() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let ops = vec![
            AbstractOp::new(JumpDest),
            AbstractOp::Label("auto".into()),
            AbstractOp::Push(Imm::with_expression(Expression::Plus(
                1.into(),
                Terminal::Label(String::from("auto")).into(),
            ))),
        ];
        let result = asm.assemble(&ops)?;
        assert_eq!(result, hex!("5b6002"));
        Ok(())
    }

    #[test]
    fn assemble_expression_with_labels() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let ops = vec![
            AbstractOp::new(JumpDest),
            AbstractOp::Push(Imm::with_expression(Expression::Plus(
                Terminal::Label(String::from("foo")).into(),
                Terminal::Label(String::from("bar")).into(),
            ))),
            AbstractOp::new(Gas),
            AbstractOp::Label("foo".into()),
            AbstractOp::Label("bar".into()),
        ];
        let result = asm.assemble(&ops)?;
        assert_eq!(result, hex!("5b60085a"));
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
        let result = asm.assemble(&ops)?;
        assert_eq!(result, hex!("6002"));

        Ok(())
    }

    #[test]
    fn assemble_instruction_macro_with_undeclared_variables() {
        let ops = vec![
            InstructionMacroDefinition {
                name: "my_macro".into(),
                parameters: vec!["foo".into()],
                contents: vec![AbstractOp::new(Push1(Imm::with_variable("bar")))],
            }
            .into(),
            AbstractOp::Label("b".into()),
            AbstractOp::new(JumpDest),
            AbstractOp::new(Push1(Imm::with_label("b"))),
            AbstractOp::Macro(InstructionMacroInvocation {
                name: "my_macro".into(),
                parameters: vec![BigInt::from_bytes_be(Sign::Plus, &vec![0x42]).into()],
            }),
        ];

        let mut asm = Assembler::new();
        let err = asm.assemble(&ops).unwrap_err();

        assert_matches!(err, Error::UndeclaredVariableMacro { var, .. } if var == "bar");
    }

    #[test]
    fn assemble_instruction_macro_two_delayed_definitions_mirrored() -> Result<(), Error> {
        let ops = vec![
            AbstractOp::new(GetPc),
            AbstractOp::Macro(InstructionMacroInvocation {
                name: "macro1".into(),
                parameters: vec![],
            }),
            AbstractOp::Macro(InstructionMacroInvocation {
                name: "macro0".into(),
                parameters: vec![],
            }),
            InstructionMacroDefinition {
                name: "macro0".into(),
                parameters: vec![],
                contents: vec![AbstractOp::new(JumpDest)],
            }
            .into(),
            InstructionMacroDefinition {
                name: "macro1".into(),
                parameters: vec![],
                contents: vec![AbstractOp::new(Caller)],
            }
            .into(),
        ];

        let mut asm = Assembler::new();
        let result = asm.assemble(&ops)?;
        assert_eq!(result, hex!("58335b"));

        Ok(())
    }

    #[test]
    fn assemble_instruction_macro_two_delayed_definitions() -> Result<(), Error> {
        let ops = vec![
            AbstractOp::new(GetPc),
            AbstractOp::Macro(InstructionMacroInvocation {
                name: "macro0".into(),
                parameters: vec![],
            }),
            AbstractOp::Macro(InstructionMacroInvocation {
                name: "macro1".into(),
                parameters: vec![],
            }),
            InstructionMacroDefinition {
                name: "macro0".into(),
                parameters: vec![],
                contents: vec![AbstractOp::new(JumpDest)],
            }
            .into(),
            InstructionMacroDefinition {
                name: "macro1".into(),
                parameters: vec![],
                contents: vec![AbstractOp::new(Caller)],
            }
            .into(),
        ];

        let mut asm = Assembler::new();
        let result = asm.assemble(&ops)?;
        assert_eq!(result, hex!("585b33"));

        Ok(())
    }

    #[test]
    fn assemble_eof_not_starting_with_section() {
        let mut asm = Assembler::new();

        let code = vec![
            AbstractOp::new(Push0),
            AbstractOp::new(Stop),
            AbstractOp::EOFSection(EOFSectionKind::Code),
            AbstractOp::new(Stop),
        ];

        let err = asm.assemble(&code).unwrap_err();

        assert_matches!(err, Error::EOFCodeDoesNotStartWithSection {});
    }

    #[test]
    fn assemble_eof_data_section_not_the_last() {
        let mut asm = Assembler::new();

        let code = vec![
            AbstractOp::EOFSection(EOFSectionKind::Code),
            AbstractOp::new(Push0),
            AbstractOp::new(Stop),
            AbstractOp::EOFSection(EOFSectionKind::Data),
            AbstractOp::new(JumpDest),
            AbstractOp::EOFSection(EOFSectionKind::Code),
            AbstractOp::new(Stop),
        ];

        let err = asm.assemble(&code).unwrap_err();

        assert_matches!(err, Error::EOFDataSectionIsNotTheLast {});
    }
}
