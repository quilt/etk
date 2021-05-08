//! Blocks are sections of EVM instructions.

pub mod annotated;
pub mod basic;

pub use self::annotated::AnnotatedBlock;
pub use self::basic::BasicBlock;
