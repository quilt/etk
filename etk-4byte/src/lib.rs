//! EVM Toolkit Function Selector Database.
//!
//! To roughly quote [4byte.directory](https://www.4byte.directory):
//!
//! > Function calls in the Ethereum Virtual Machine are specified by the first
//! > four bytes of data sent with a transaction. These function selectors are
//! > defined as the first four bytes of the Keccak-256 hash of the canonical
//! > representation of the function signature. Since this is a one-way
//! > operation, it is not possible to derive the human-readable representation
//! > of the function (signature) from the four byte selector. This database is
//! > meant to allow mapping those bytes signatures back to their
//! > human-readable versions.
#![deny(unsafe_code)]
#![deny(missing_docs)]
#![deny(unreachable_pub)]
#![deny(missing_debug_implementations)]

include!(concat!(env!("CARGO_MANIFEST_DIR"), "/src/codegen.rs.in"));

/// Attempt to retrieve the human-readable signature given a selector.
///
/// ## Example
///
/// ```
/// use etk_4byte::reverse_selector;
///
/// let signatures = reverse_selector(0x3bb2dead);
///
/// assert_eq!(signatures[0], "initialFundsReleaseNumerator()");
/// assert_eq!(signatures[1], "resolveAddressLight(address)");
/// ```
pub fn reverse_selector(selector: u32) -> &'static [&'static str] {
    SIGNATURES.get(&selector).unwrap_or(&(&[] as &[&str]))
}
