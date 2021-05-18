//! Analysis tools from the Ethereum Toolkit.
//!
//! Highly unstable and incomplete.

#![deny(unsafe_code)]
// TODO: #![deny(missing_docs)]
// TODO: #![deny(unreachable_pub)]
#![deny(missing_debug_implementations)]

pub mod blocks;
#[cfg(feature = "cfg")]
pub mod cfg;
mod sym;
