use super::{AbstractOp, Imm};
use std::convert::From;
use std::fmt;

/// Macro definition.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum MacroDefinition {
    /// Instruction macro definition.
    Instruction(InstructionMacroDefinition),

    /// Expression macro definition.
    Expression(ExpressionMacroDefinition),
}

impl MacroDefinition {
    /// Returns the name of the defined macro.
    pub fn name(&self) -> &String {
        match self {
            Self::Instruction(m) => &m.name,
            Self::Expression(m) => &m.name,
        }
    }

    /// Returns the specified parameters of the defined macro.
    pub fn parameters(&self) -> &Vec<String> {
        match self {
            Self::Instruction(m) => &m.parameters,
            Self::Expression(m) => &m.parameters,
        }
    }

    /// Unwraps an `ExpressionMacroDefinition` from a `MacroDefinition`.
    pub fn unwrap_expression(&self) -> &ExpressionMacroDefinition {
        match self {
            Self::Instruction(_) => {
                panic!("unwrapped expression macro, but found instruction macro")
            }
            Self::Expression(m) => m,
        }
    }
}

impl fmt::Display for MacroDefinition {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Instruction(m) => write!(f, "%{}({})", m.name, m.parameters.join(", ")),
            Self::Expression(m) => write!(f, "{}({})", m.name, m.parameters.join(", ")),
        }
    }
}

impl From<InstructionMacroDefinition> for MacroDefinition {
    fn from(item: InstructionMacroDefinition) -> Self {
        MacroDefinition::Instruction(item)
    }
}

impl From<ExpressionMacroDefinition> for MacroDefinition {
    fn from(item: ExpressionMacroDefinition) -> Self {
        MacroDefinition::Expression(item)
    }
}

/// Instruction macro definition op fields.
#[derive(Debug, Default, Clone, Eq, PartialEq)]
pub struct InstructionMacroDefinition {
    /// The name that identifies the macro.
    pub name: String,
    /// The name identifiers for the macro's parameters.
    pub parameters: Vec<String>,
    /// The body of the macro.
    pub contents: Vec<AbstractOp>,
}

/// Instruction macro invocation op.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct InstructionMacroInvocation {
    /// The name of the macro being invoked.
    pub name: String,
    /// The parameters that are being passed into the invocation.
    pub parameters: Vec<Imm<Vec<u8>>>,
}

impl InstructionMacroInvocation {
    /// Construct an instruction macro invocation with zero parameters.
    pub fn with_zero_parameters(name: String) -> Self {
        Self {
            name,
            parameters: vec![],
        }
    }
}

impl fmt::Display for InstructionMacroInvocation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "%{}({})",
            self.name,
            self.parameters
                .iter()
                .map(Imm::to_string)
                .collect::<Vec<String>>()
                .join(", ")
        )
    }
}

/// Expression macro definition op fields.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ExpressionMacroDefinition {
    /// The name that identifies the macro.
    pub name: String,
    /// The name identifiers for the macro's parameters.
    pub parameters: Vec<String>,
    /// The body of the macro.
    pub content: Imm<Vec<u8>>,
}

/// Expression macro invocation imm.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ExpressionMacroInvocation {
    /// The name of the macro being invoked.
    pub name: String,
    /// The parameters that are being passed into the invocation.
    pub parameters: Vec<Imm<Vec<u8>>>,
}

impl fmt::Display for ExpressionMacroInvocation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}({})",
            self.name,
            self.parameters
                .iter()
                .map(Imm::to_string)
                .collect::<Vec<String>>()
                .join(", ")
        )
    }
}
