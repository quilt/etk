//! The EVM Toolkit Assembler.
//!
//! You can find more information about the command-line tools in
//! [The ETK Book](https://quilt.github.io/etk/).
//!
//! The [`ingest`] module is high-level and similar to the command-line interface.
//!
//! The [`mod@asm`] module provides low-level access to the internals of the assembler.
//!
//! All of the instructions are defined in the [`mod@ops`] module, and simple
//! disassembly functionality is available in the [`disasm`] module.
#![recursion_limit = "512"]
#![deny(unsafe_code)]
#![deny(missing_docs)]
#![deny(unreachable_pub)]
#![deny(missing_debug_implementations)]

pub mod asm;
mod ast;
pub mod disasm;
pub mod ingest;
pub mod ops;
mod parse;

pub use self::parse::error::ParseError;
