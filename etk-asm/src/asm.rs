//! Single-scope assembler implementation and related types.
//!
//! See [`Assembler`] for more details on the low-level assembly process, or the
//! [`mod@crate::ingest`] module for a higher-level interface.

mod error {
    use crate::ops::imm::TryFromIntError;
    use crate::ParseError;

    use snafu::{Backtrace, Snafu};

    /// Errors that can occur while assembling instructions.
    #[derive(Snafu, Debug)]
    #[non_exhaustive]
    #[snafu(visibility = "pub(super)")]
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
        #[snafu(display("macro `{}` declared multiple times", macro_name))]
        #[non_exhaustive]
        DuplicateMacro {
            /// The name of the conflicting macro.
            macro_name: String,

            /// The location of the error.
            backtrace: Backtrace,
        },

        /// A push instruction was too small for the address of a label.
        #[snafu(display("value of label `{}` was too large for the given opcode", label))]
        #[non_exhaustive]
        LabelTooLarge {
            /// The name of the oversized label.
            label: String,

            /// The next source of this error.
            #[snafu(backtrace)]
            source: TryFromIntError,
        },

        /// The value provided to a sized push was too large.
        #[snafu(display("value was too large for chosen push"))]
        #[non_exhaustive]
        SizedPushTooLarge {
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
            /// The label that was used without being defined.
            labels: Vec<String>,

            /// The location of the error.
            backtrace: Backtrace,
        },

        /// A macro was used without being defined.
        #[snafu(display("macro `{}` was never defined", macro_name))]
        #[non_exhaustive]
        UndeclaredInstructionMacro {
            /// The macro that was used without being defined.
            macro_name: String,

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

use crate::ops::imm::{self, Terminal};
use crate::ops::{AbstractOp, Expression, Imm, MacroDefinition, Specifier};

pub use self::error::Error;

use snafu::{OptionExt, ResultExt};

use std::collections::{hash_map, HashMap, HashSet, VecDeque};
use std::convert::TryInto;

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
    fn size(&self) -> Option<u32> {
        match self {
            Self::Op(op) => op.size(),
            Self::Raw(raw) => Some(raw.len().try_into().expect("raw too big")),
        }
    }

    fn labels(
        &self,
        macros: &HashMap<String, MacroDefinition>,
    ) -> Option<Result<Vec<String>, imm::Error>> {
        match self {
            Self::Op(op) => op.labels(macros),
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
/// use etk_asm::ops::{Op, AbstractOp};
/// # use etk_asm::asm::Error;
/// #
/// # use hex_literal::hex;
/// let mut asm = Assembler::new();
/// asm.push_all(vec![
///     AbstractOp::Op(Op::GetPc),
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

    /// Ops that cannot be encoded yet.
    pending: VecDeque<RawOp>,

    /// Sum of the size of all the ops in `pending`, or `None` if `pending` contains
    /// an unsized op.
    pending_len: Option<u32>,

    /// Total number of `u8` that have been appended to `ready`.
    concrete_len: u32,

    /// Labels, in `pending`, associated with an `AbstractOp::Label`.
    declared_labels: HashMap<String, Option<u32>>,

    /// Macros, in `pending`, associated with an `AbstractOp::Macro`.
    declared_macros: HashMap<String, MacroDefinition>,

    /// Labels, in `pending`, that have been referred to (ex. with push) but
    /// have not been declared with an `AbstractOp::Label`.
    undeclared_labels: HashSet<String>,
}

impl Default for Assembler {
    fn default() -> Self {
        Self {
            ready: Default::default(),
            pending: Default::default(),
            pending_len: Some(0),
            concrete_len: 0,
            declared_labels: Default::default(),
            declared_macros: Default::default(),
            undeclared_labels: Default::default(),
        }
    }
}

impl Assembler {
    /// Create a new `Assembler`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Indicate that the input sequence is complete. Returns any errors that
    /// may remain.
    pub fn finish(self) -> Result<(), Error> {
        unimplemented!();
        /*
        if let Some(undef) = self.pending.front() {
            return match undef {
                // Still waiting for a label to concretize a sized push.
                RawOp::Op(AbstractOp::Op(op)) => {
                    if let Some(label) = op.immediate_label() {
                        error::UndeclaredLabels {
                            labels: vec![label.into()],
                        }
                        .fail()
                    } else if let Some(expr) = op.immediate_expression() {
                        let labels: Vec<String> = expr
                            .labels()
                            .into_iter()
                            .filter(|lbl| !self.declared_labels.contains_key(*lbl))
                            .cloned()
                            .collect();
                        error::UndeclaredLabels { labels }.fail()
                    } else {
                        unreachable!()
                    }
                }
                // Still waiting for a label to concretize an unsized push.
                RawOp::Op(AbstractOp::Push(imm)) => match imm {
                    Imm::Label(label) => error::UndeclaredLabels {
                        labels: vec![label.into()],
                    }
                    .fail(),
                    Imm::Expression(expr) => {
                        let labels: Vec<String> = expr
                            .labels()
                            .into_iter()
                            .filter(|lbl| !self.declared_labels.contains_key(*lbl))
                            .cloned()
                            .collect();
                        error::UndeclaredLabels { labels }.fail()
                    }
                    _ => unreachable!(),
                },
                // Still waiting for a macro definition to expand a macro invocation.
                RawOp::Op(AbstractOp::Macro(m)) => error::UndeclaredInstructionMacro {
                    macro_name: m.name.clone(),
                }
                .fail(),
                _ => unreachable!(),
            };
        }

        if !self.ready.is_empty() {
            panic!("not all assembled bytecode has been taken");
        }

        Ok(())
        */
    }

    /// Collect any assembled instructions that are ready to be output.
    pub fn take(&mut self) -> Vec<u8> {
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

        Ok(self.ready.len())
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
                        v.insert(None);
                        self.undeclared_labels.remove(label);
                    }
                }
            }
            RawOp::Op(AbstractOp::MacroDefinition(ref defn)) => {
                match self.declared_macros.entry(defn.name().to_owned()) {
                    hash_map::Entry::Occupied(_) => {
                        return error::DuplicateMacro {
                            macro_name: defn.name(),
                        }
                        .fail()
                    }
                    hash_map::Entry::Vacant(v) => {
                        v.insert(defn.to_owned());
                    }
                }
            }
            _ => (),
        };

        // 1. get all labels used by `rop`
        // 2. check if they've been defined
        // 3. if not, note them as "undeclared"
        if let Some(Ok(labels)) = rop.labels(&self.declared_macros) {
            for label in labels {
                if !self.declared_labels.contains_key(&label) {
                    self.undeclared_labels.insert(label.to_owned());
                }
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

        self.declare_content(&rop)?;

        // Expand instruction macros immediately. We do this here because it's the same process
        // regardless if we `push_read` or `push_pending` -- in fact, `expand_macro` pushes each op
        // individually which calls the correct unchecked push.
        if let RawOp::Op(AbstractOp::Macro(ref m)) = rop {
            self.expand_macro(&m.name, &m.parameters)?;
            return Ok(self.ready.len());
        }

        self.push_unchecked(rop)?;

        Ok(self.ready.len())
    }

    fn push_unchecked(&mut self, rop: RawOp) -> Result<(), Error> {
        if self.pending.is_empty() {
            self.push_ready(rop)
        } else {
            self.push_pending(rop)
        }
    }

    fn push_ready(&mut self, rop: RawOp) -> Result<(), Error> {
        match rop {
            RawOp::Op(AbstractOp::Label(label)) => {
                let old = self
                    .declared_labels
                    .insert(label, Some(self.concrete_len))
                    .expect("label should exist");
                assert_eq!(old, None, "label should have been undefined");
                Ok(())
            }
            RawOp::Op(AbstractOp::MacroDefinition(_)) => Ok(()),
            RawOp::Op(AbstractOp::Macro(ref m)) => {
                match self.declared_macros.get(&m.name) {
                    // Do nothing if the instruction macro has been defined.
                    Some(MacroDefinition::Instruction(_)) => (),
                    _ => {
                        assert_eq!(self.pending_len, Some(0));
                        self.pending_len = None;
                        self.pending.push_back(rop);
                    }
                }
                Ok(())
            }
            RawOp::Op(op) => {
                let concrete = op
                    .concretize(
                        &self.declared_labels,
                        &HashMap::new(),
                        &self.declared_macros,
                    )
                    .unwrap();
                self.concrete_len += concrete.size();

                concrete.assemble(&mut self.ready);

                Ok(())
            }
            RawOp::Raw(raw) => {
                let len: u32 = raw.len().try_into().expect("raw too long");
                self.concrete_len += len;
                self.ready.extend(raw);
                Ok(())
            }
        }
    }

    // TODO: move below `push_pending`
    fn pop_pending(&mut self) -> Result<(), Error> {
        let popped = self.pending.pop_front().unwrap();

        let size;

        match popped {
            RawOp::Raw(raw) => {
                size = raw.len() as u32;
                self.ready.extend(raw);
            }
            RawOp::Op(AbstractOp::Macro(m)) => match self.expand_macro(&m.name, &m.parameters)? {
                Some(n) => size = n as u32,
                None => size = 0,
            },
            RawOp::Op(aop) => {
                let cop = aop
                    .concretize(
                        &self.declared_labels,
                        &HashMap::new(),
                        &self.declared_macros,
                    )
                    .unwrap();
                size = cop.size();
                cop.assemble(&mut self.ready);
            }
        }

        self.concrete_len += size;

        if self.pending.is_empty() {
            self.pending_len = Some(0);
        } else if let Some(ref mut pending_len) = self.pending_len {
            *pending_len -= size;
        }

        Ok(())
    }

    fn push_pending(&mut self, rop: RawOp) -> Result<(), Error> {
        // Update total size of pending ops.
        if let Some(ref mut pending_len) = self.pending_len {
            match rop.size() {
                Some(size) => *pending_len += size,
                None => self.pending_len = None,
            }
        }

        // Handle labels.
        match (self.pending_len, rop) {
            (Some(pending_len), RawOp::Op(AbstractOp::Label(lbl))) => {
                // The label has a defined address.
                let address = self.concrete_len + pending_len;
                let item = self.declared_labels.get_mut(&*lbl).unwrap();
                *item = Some(address);
            }
            (None, rop @ RawOp::Op(AbstractOp::Label(_))) => {
                self.pending.push_back(rop);
                if self.undeclared_labels.is_empty() {
                    self.choose_sizes()?;
                }
            }
            (_, RawOp::Op(AbstractOp::MacroDefinition(_))) => (),
            (_, rop) => {
                // Not a label.
                self.pending.push_back(rop);
            }
        }

        // Repeatedly check if the front of the pending list is ready.
        while let Some(next) = self.pending.front() {
            let op = match next.to_owned() {
                RawOp::Op(AbstractOp::Push(Imm {
                    tree: Expression::Terminal(Terminal::Label(_)),
                    ..
                })) => {
                    if self.undeclared_labels.is_empty() {
                        unreachable!()
                    } else {
                        // Still waiting on more labels.
                        break;
                    }
                }
                RawOp::Op(AbstractOp::Push(Imm {
                    tree: Expression::Terminal(Terminal::Bytes(_)),
                    ..
                })) => unreachable!(),
                RawOp::Op(AbstractOp::Label(_)) => unreachable!(),
                RawOp::Op(op) => op,
                RawOp::Raw(_) => {
                    self.pop_pending()?;
                    continue;
                }
            };

            match op.concretize(
                &self.declared_labels,
                &HashMap::new(),
                &self.declared_macros,
            ) {
                Ok(cop) => {
                    unimplemented!()
                    // let front = self.pending.front_mut().unwrap();
                    // *front = RawOp::Op(cop.into());
                }
                Err(_) => unimplemented!(),
            }

            self.pop_pending()?;
        }

        Ok(())
    }

    fn choose_sizes(&mut self) -> Result<(), Error> {
        let minimum = Specifier::push_for(self.concrete_len).unwrap();

        let mut undefined_labels: HashMap<String, Specifier> = self
            .declared_labels
            .iter()
            .filter(|(_, v)| v.is_none())
            .map(|(k, _)| (k.clone(), minimum))
            .collect();

        let mut subasm;

        loop {
            // Create a sub-assembler to try assembling with the sizes in
            // `undefined_labels`.
            subasm = Self::default();
            subasm.concrete_len = self.concrete_len;
            subasm.declared_labels = self.declared_labels.clone();

            let result: Result<Vec<_>, Error> = self
                .pending
                .iter()
                .map(|op| {
                    let new = match op {
                        RawOp::Op(AbstractOp::Push(Imm {
                            tree: Expression::Terminal(Terminal::Label(lbl)),
                            ..
                        })) => {
                            // Replace unsized push with our current guess.
                            let spec = undefined_labels[lbl];
                            let aop = AbstractOp::with_expression(
                                spec,
                                Terminal::Label(lbl.clone()).into(),
                            );
                            RawOp::Op(aop)
                        }
                        // TODO: 1.56.0 supports bindings_after_at
                        // https://github.com/rust-lang/rust/issues/65490
                        RawOp::Op(AbstractOp::Push(Imm { tree, .. })) => {
                            // Replace unsized push with our current guess.
                            let labels = tree.labels(&subasm.declared_macros).unwrap();
                            if labels.is_empty() {
                                match op {
                                    RawOp::Op(aop @ AbstractOp::Push(_)) => {
                                        let cop = aop
                                            .clone()
                                            .concretize(
                                                &subasm.declared_labels,
                                                &HashMap::new(),
                                                &subasm.declared_macros,
                                            )
                                            // TODO don't unwrap
                                            .unwrap();
                                        RawOp::Op(cop.into())
                                    }
                                    _ => unreachable!(),
                                }
                            } else {
                                let spec = undefined_labels[&labels[0]];
                                let aop = AbstractOp::with_expression(
                                    spec,
                                    Terminal::Label(labels[0].to_string()).into(),
                                );
                                RawOp::Op(aop)
                            }
                        }
                        RawOp::Op(
                            aop
                            @
                            AbstractOp::Push(Imm {
                                tree: Expression::Terminal(Terminal::Bytes(_)),
                                ..
                            }),
                        ) => {
                            let cop = aop
                                .clone()
                                .concretize(
                                    &subasm.declared_labels,
                                    &HashMap::new(),
                                    &subasm.declared_macros,
                                )
                                //TODO fix this
                                .unwrap();
                            RawOp::Op(cop.into())
                        }
                        op => op.clone(),
                    };

                    subasm.push_pending(new)
                })
                .collect();

            match result {
                Ok(_) => {
                    assert!(subasm.pending.is_empty());
                    break;
                }
                Err(Error::LabelTooLarge { label, .. }) => {
                    // If a label is too large for an op, increase the width of
                    // that label.
                    let item = undefined_labels.get_mut(&label).unwrap();

                    let new_size = item.upsize().context(error::UnsizedPushTooLarge)?;
                    *item = new_size;
                }
                Err(e) => return Err(e),
            }
        }

        // Insert the results of the sub-assembler into self.
        let raw = subasm.take();
        self.pending_len = Some(raw.len().try_into().unwrap());
        self.pending.clear();
        self.pending.push_back(RawOp::Raw(raw));
        self.declared_labels = subasm.declared_labels;

        Ok(())
    }

    fn expand_macro(
        &mut self,
        name: &str,
        parameters: &[Imm<Vec<u8>>],
    ) -> Result<Option<usize>, Error> {
        // Remap labels to macro scope.
        match self.declared_macros.get(name).cloned() {
            Some(MacroDefinition::Instruction(mut m)) => {
                if m.parameters.len() != parameters.len() {
                    panic!("invalid number of parameters for macro {}", name);
                }

                let mut labels = HashMap::<String, String>::new();

                // First pass, find locally defined labels and rename them.
                for op in m.contents.iter_mut() {
                    match op {
                        AbstractOp::Label(ref mut label) => {
                            // TODO: add mangled extension later
                            let mangled = format!("{}_{}", m.name, label);
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

                /*
                // Second pass, update local label invocations.
                for op in m.contents.iter_mut() {
                    if let Some(label) = op.immediate_label() {
                        if let Some(label) = labels.get(label) {
                            *op = AbstractOp::with_label(op.specifier().unwrap(), label);
                        }
                    } else if let Some(variable) = op.immediate_variable() {
                        if let Some(idx) = m.parameters.iter().position(|x| x == variable) {
                            match &parameters[idx] {
                                Imm::Label(lbl) => {
                                    *op = AbstractOp::with_label(op.specifier().unwrap(), lbl)
                                }
                                Imm::Constant(c) => {
                                    let mut trimmed = &c[..];
                                    while !trimmed.is_empty() && trimmed[0] == 0 {
                                        trimmed = &trimmed[1..];
                                    }
                                    if trimmed.len() < op.pushes() {
                                        return error::SizedPushTooLarge {}.fail();
                                    }
                                    let mut normalized =
                                        vec![0; op.size().unwrap() as usize - 1 - trimmed.len()];
                                    normalized.extend_from_slice(trimmed);

                                    *op = AbstractOp::with_immediate(
                                        op.specifier().unwrap(),
                                        &normalized,
                                    )
                                    .unwrap()
                                }
                                Imm::Variable(_) => unreachable!(),
                                Imm::Expression(_) => unimplemented!(),
                                Imm::Macro(_) => unimplemented!(),
                            }
                        }
                    }
                }
                */

                Ok(Some(self.push_all(m.contents)?))
            }
            _ => error::UndeclaredInstructionMacro { macro_name: name }.fail(),
        }
    }
}

#[cfg(test)]
mod tests {
    use assert_matches::assert_matches;

    use crate::ops::{
        Expression, ExpressionMacroDefinition, ExpressionMacroInvocation, Imm,
        InstructionMacroDefinition, InstructionMacroInvocation, Op,
    };

    use hex_literal::hex;

    use super::*;

    #[test]
    fn assemble_variable_push_const_while_pending() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let sz = asm.push_all(vec![
            AbstractOp::Op(Op::Push1(Imm::with_label("label1"))),
            AbstractOp::Push(Expression::Terminal(Terminal::Bytes(vec![0x00, 0xaa, 0xbb])).into()),
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
            AbstractOp::Op(Op::JumpDest),
            AbstractOp::Push(Imm::with_label("label1")),
            AbstractOp::Push(Imm::with_label("label2")),
            AbstractOp::Label("label1".into()),
            AbstractOp::Op(Op::GetPc),
            AbstractOp::Label("label2".into()),
            AbstractOp::Op(Op::GetPc),
        ])?;
        assert_eq!(7, sz);
        assert_eq!(asm.take(), hex!("5b600560065858"));
        Ok(())
    }

    #[test]
    fn assemble_variable_pushes_abba() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let sz = asm.push_all(vec![
            AbstractOp::Op(Op::JumpDest),
            AbstractOp::Push(Imm::with_label("label1")),
            AbstractOp::Push(Imm::with_label("label2")),
            AbstractOp::Label("label2".into()),
            AbstractOp::Op(Op::GetPc),
            AbstractOp::Label("label1".into()),
            AbstractOp::Op(Op::GetPc),
        ])?;
        assert_eq!(7, sz);
        assert_eq!(asm.take(), hex!("5b600660055858"));
        Ok(())
    }

    #[test]
    fn assemble_variable_push1_multiple() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let sz = asm.push_all(vec![
            AbstractOp::Op(Op::JumpDest),
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
            Expression::Terminal(Terminal::Bytes(hex!("00aaaaaaaaaaaaaaaaaaaaaaaa").into())).into(),
        )])?;
        assert_eq!(13, sz);
        assert_eq!(asm.take(), hex!("6baaaaaaaaaaaaaaaaaaaaaaaa"));
        Ok(())
    }

    #[test]
    fn assemble_variable_push1_known() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let sz = asm.push_all(vec![
            AbstractOp::Op(Op::JumpDest),
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
            AbstractOp::Op(Op::JumpDest),
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
            AbstractOp::Op(Op::JumpDest),
            AbstractOp::Op(Op::Push1(Imm::with_label("auto"))),
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
            asm.push(AbstractOp::Op(Op::GetPc))?;
        }

        asm.push_all(vec![
            AbstractOp::Label("auto".into()),
            AbstractOp::Op(Op::JumpDest),
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
        asm.push_all(vec![AbstractOp::Op(Op::Push1(Imm::with_label("hi")))])?;
        let err = asm.finish().unwrap_err();
        assert_matches!(err, Error::UndeclaredLabels { labels, .. } if labels == vec!["hi"]);
        Ok(())
    }

    #[test]
    fn assemble_jumpdest_no_label() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let sz = asm.push_all(vec![AbstractOp::Op(Op::JumpDest)])?;
        assert_eq!(1, sz);
        assert!(asm.declared_labels.is_empty());
        assert_eq!(asm.take(), hex!("5b"));
        Ok(())
    }

    #[test]
    fn assemble_jumpdest_with_label() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let ops = vec![
            AbstractOp::Label("lbl".into()),
            AbstractOp::Op(Op::JumpDest),
        ];

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
            AbstractOp::Op(Op::JumpDest),
            AbstractOp::Op(Op::Push1(Imm::with_label("lbl"))),
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
            AbstractOp::Op(Op::Push1(Imm::with_label("lbl"))),
            AbstractOp::Label("lbl".into()),
            AbstractOp::Op(Op::GetPc),
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
            AbstractOp::Op(Op::Push1(Imm::with_label("lbl"))),
            AbstractOp::Label("lbl".into()),
            AbstractOp::Op(Op::JumpDest),
        ];

        let mut asm = Assembler::new();
        let sz = asm.push_all(ops)?;
        assert_eq!(sz, 3);
        assert_eq!(asm.take(), hex!("60025b"));

        Ok(())
    }

    #[test]
    fn assemble_label_too_large() {
        let mut ops: Vec<_> = vec![AbstractOp::Op(Op::GetPc); 255];
        ops.push(AbstractOp::Label("b".into()));
        ops.push(AbstractOp::Op(Op::JumpDest));
        ops.push(AbstractOp::Label("a".into()));
        ops.push(AbstractOp::Op(Op::JumpDest));
        ops.push(AbstractOp::Op(Op::Push1(Imm::with_label("a"))));
        let mut asm = Assembler::new();
        let err = asm.push_all(ops).unwrap_err();
        assert_matches!(err, Error::LabelTooLarge { label, .. } if label == "a");
    }

    #[test]
    fn assemble_label_just_right() -> Result<(), Error> {
        let mut ops: Vec<_> = vec![AbstractOp::Op(Op::GetPc); 255];
        ops.push(AbstractOp::Label("b".into()));
        ops.push(AbstractOp::Op(Op::JumpDest));
        ops.push(AbstractOp::Label("a".into()));
        ops.push(AbstractOp::Op(Op::JumpDest));
        ops.push(AbstractOp::Op(Op::Push1(Imm::with_label("b"))));
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
    fn assemble_instruction_macro() -> Result<(), Error> {
        let ops = vec![
            InstructionMacroDefinition {
                name: "my_macro".into(),
                parameters: vec![],
                contents: vec![
                    AbstractOp::Label("a".into()),
                    AbstractOp::Op(Op::JumpDest),
                    AbstractOp::Op(Op::Push1(Imm::with_label("a"))),
                    AbstractOp::Op(Op::Push1(Imm::with_label("b"))),
                ],
            }
            .into(),
            AbstractOp::Label("b".into()),
            AbstractOp::Op(Op::JumpDest),
            AbstractOp::Op(Op::Push1(Imm::with_label("b"))),
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
    fn assemble_undeclared_instruction_macro() -> Result<(), Error> {
        let ops = vec![AbstractOp::Macro(
            InstructionMacroInvocation::with_zero_parameters("my_macro".into()),
        )];
        let mut asm = Assembler::new();
        let err = asm.push_all(ops).unwrap_err();
        assert_matches!(err, Error::UndeclaredInstructionMacro { macro_name, .. } if macro_name == "my_macro");

        Ok(())
    }

    #[test]
    fn assemble_duplicate_instruction_macro() -> Result<(), Error> {
        let ops: Vec<AbstractOp> = vec![
            InstructionMacroDefinition {
                name: "my_macro".into(),
                parameters: vec![],
                contents: vec![AbstractOp::Op(Op::Caller)],
            }
            .into(),
            InstructionMacroDefinition {
                name: "my_macro".into(),
                parameters: vec![],
                contents: vec![AbstractOp::Op(Op::Caller)],
            }
            .into(),
        ];
        let mut asm = Assembler::new();
        let err = asm.push_all(ops).unwrap_err();
        assert_matches!(err, Error::DuplicateMacro { macro_name, .. } if macro_name == "my_macro");

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
            AbstractOp::Op(Op::Caller),
            InstructionMacroDefinition {
                name: "my_macro()".into(),
                parameters: vec![],
                contents: vec![
                    AbstractOp::Label("a".into()),
                    AbstractOp::Op(Op::Push1(Imm::with_label("a"))),
                ],
            }
            .into(),
            AbstractOp::Macro(InstructionMacroInvocation::with_zero_parameters(
                "my_macro()".into(),
            )),
            AbstractOp::Op(Op::Push1(Imm::with_label("a"))),
        ];
        let mut asm = Assembler::new();
        let sz = asm.push_all(ops)?;
        assert_eq!(sz, 5);

        let out = asm.take();
        asm.finish()?;

        assert_eq!(out, hex!("3360016000"));

        Ok(())
    }

    /*
    #[test]
    fn assemble_instruction_macro_with_parameters() -> Result<(), Error> {
        let ops = vec![
            InstructionMacroDefinition {
                name: "my_macro".into(),
                parameters: vec!["foo".into(), "bar".into()],
                contents: vec![
                    AbstractOp::Op(Op::Push1(Imm::with_variable("foo"))),
                    AbstractOp::Op(Op::Push1(Imm::with_variable("bar"))),
                ],
            }
            .into(),
            AbstractOp::Label("b".into()),
            AbstractOp::Op(Op::JumpDest),
            AbstractOp::Op(Op::Push1(Imm::with_label("b"))),
            AbstractOp::Macro(InstructionMacroInvocation {
                name: "my_macro".into(),
                parameters: vec![Imm::<Vec<u8>>::from(vec![0x42]), Imm::with_label("b")],
            }),
        ];

        let mut asm = Assembler::new();
        let sz = asm.push_all(ops)?;
        assert_eq!(sz, 7);
        let out = asm.take();
        assert_eq!(out, hex!("5b600060426000"));

        Ok(())
    }
    */

    #[test]
    fn assemble_expression_push() -> Result<(), Error> {
        let ops = vec![AbstractOp::Op(Op::Push1(Imm::with_expression(
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
    fn assemble_expression_undeclared_label() -> Result<(), Error> {
        let mut asm = Assembler::new();
        asm.push_all(vec![AbstractOp::Op(Op::Push1(Imm::with_expression(
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
            AbstractOp::Op(Op::JumpDest),
            AbstractOp::Push(Imm::with_expression(Expression::Plus(
                Terminal::Label("foo".into()).into(),
                Terminal::Label("bar".into()).into(),
            ))),
            AbstractOp::Op(Op::Gas),
        ])?;
        let err = asm.finish().unwrap_err();
        assert_matches!(err, Error::UndeclaredLabels { labels, .. } if labels == vec!["bar", "foo"]);
        Ok(())
    }

    #[test]
    fn assemble_variable_push1_expression() -> Result<(), Error> {
        let mut asm = Assembler::new();
        let sz = asm.push_all(vec![
            AbstractOp::Op(Op::JumpDest),
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
            AbstractOp::Op(Op::JumpDest),
            AbstractOp::Push(Imm::with_expression(Expression::Plus(
                Terminal::Label(String::from("foo")).into(),
                Terminal::Label(String::from("bar")).into(),
            ))),
            AbstractOp::Op(Op::Gas),
            AbstractOp::Label("foo".into()),
            AbstractOp::Label("bar".into()),
        ])?;
        assert_eq!(4, sz);
        assert_eq!(asm.take(), hex!("5b60045a"));
        Ok(())
    }

    #[test]
    fn assemble_expression_macro_push() -> Result<(), Error> {
        let ops = vec![
            ExpressionMacroDefinition {
                name: "foo".into(),
                parameters: vec![],
                content: Imm::with_expression(Expression::Plus(
                    Terminal::Number(1).into(),
                    Terminal::Number(1).into(),
                )),
            }
            .into(),
            AbstractOp::Op(Op::Push1(Imm::with_macro(ExpressionMacroInvocation {
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
