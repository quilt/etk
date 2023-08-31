use indexmap::IndexMap;

use quote::{format_ident, quote};

use serde::Deserialize;

use std::fs::File;
use std::io::{Read, Write};
use std::path::PathBuf;

#[derive(Debug)]
pub enum Error {
    Io { source: std::io::Error },
    Toml { source: toml::de::Error },
    OutOfOrder { name: String },
}

impl From<std::io::Error> for Error {
    fn from(source: std::io::Error) -> Self {
        Self::Io { source }
    }
}

impl From<toml::de::Error> for Error {
    fn from(source: toml::de::Error) -> Self {
        Self::Toml { source }
    }
}

#[derive(Debug, Deserialize, Clone)]
struct Op {
    code: u8,
    mnemonic: String,
    pushes: u8,
    pops: u8,

    #[serde(default)]
    extra_len: u8,

    #[serde(default)]
    exits: bool,

    #[serde(default)]
    jump: bool,

    #[serde(default)]
    jump_target: bool,
}

fn read_fork(name: &str) -> Result<[(String, Op); 256], Error> {
    let root = std::env::var_os("CARGO_MANIFEST_DIR").unwrap();

    let mut input_path = PathBuf::from(root);
    input_path.push("src");
    input_path.push(&format!("{}.toml", name));

    let mut input_bytes = Vec::new();
    File::open(&input_path)?.read_to_end(&mut input_bytes)?;

    let input_map: IndexMap<String, Op> = toml::from_slice(&input_bytes)?;
    let input: Vec<_> = input_map.into_iter().collect();

    let mut ops: Vec<(String, Op)> = (0..=u8::MAX)
        .map(|code| {
            let name = format!("Invalid{:X}{:x}", (code & 0xF0) >> 4, code & 0x0F);
            let op = Op {
                code,
                mnemonic: format!("invalid_{:02x}", code),
                extra_len: 0,
                pushes: 0,
                pops: 0,
                exits: true,
                jump: false,
                jump_target: false,
            };
            (name, op)
        })
        .collect();

    for idx in 0..input.len() {
        let name = &input[idx].0;
        let op = &input[idx].1;

        if idx < input.len() - 1 && op.code >= input[idx + 1].1.code {
            return Err(Error::OutOfOrder {
                name: input[idx + 1].0.clone(),
            });
        }

        ops[input[idx].1.code as usize] = (name.clone(), op.clone());
    }

    Ok(ops.try_into().unwrap())
}

fn generate_fork(fork_name: &str) -> Result<(), Error> {
    let ops = read_fork(fork_name)?;

    let mut tokens = quote! {
        /// Trait for types that represent an EVM instruction.
        pub trait Operation {
            /// The return type of [`Operation::code`].
            type Code: Operation<Code = Self::Code> + Into<u8>;

            /// The return root type of [`Operation::immediate_mut`] and
            /// [`Operation::immediate`].
            type ImmediateRef: ?Sized;

            /// The type of the immediate argument for this operation.
            type Immediate:
                std::borrow::Borrow<Self::ImmediateRef> + std::borrow::BorrowMut<Self::ImmediateRef>;

            /// Get a shared reference to the immediate argument of this operation,
            /// if one exists.
            fn immediate(&self) -> Option<&Self::ImmediateRef>;

            /// Get a mutable reference to the immediate argument of this operation,
            /// if one exists.
            fn immediate_mut(&mut self) -> Option<&mut Self::ImmediateRef>;

            /// Consume this operation and return its immediate argument, if one
            /// exists.
            fn into_immediate(self) -> Option<Self::Immediate>;

            /// Length of immediate argument.
            fn extra_len(&self) -> usize;

            /// The action (opcode) of this operation, without any immediates.
            fn code(&self) -> Self::Code;

            /// The byte (opcode) that indicates this operation.
            fn code_byte(&self) -> u8 {
                self.code().into()
            }

            /// Human-readable name for this operation.
            fn mnemonic(&self) -> &str;

            /// Returns true if the current instruction changes the program counter (other
            /// than incrementing it.)
            fn is_jump(&self) -> bool;

            /// Returns true if the current instruction is a valid destination for jumps.
            fn is_jump_target(&self) -> bool;

            /// Returns true if the current instruction causes the EVM to stop executing
            /// the contract.
            fn is_exit(&self) -> bool;

            /// How many stack elements this instruction pops.
            fn pops(&self) -> usize;

            /// How many stack elements this instruction pushes.
            fn pushes(&self) -> usize;
        }
    };

    let mut code_matches = quote! {};
    let mut size_matches = quote! {};
    let mut new_matches = quote! {};
    let mut display_matches = quote! {};
    let mut from_u8_matches = quote! {};
    let mut from_str_matches = quote! {};
    let mut from_slice_matches = quote! {};
    let mut variants = quote! {};
    let mut immediate_matches = quote! {};
    let mut immediate_mut_matches = quote! {};
    let mut into_immediate_matches = quote! {};
    let names: Vec<_> = ops.iter().map(|(n, _)| format_ident!("{}", n)).collect();
    let immediate_ops: Vec<_> = ops
        .iter()
        .filter(|(_, op)| op.extra_len > 0)
        .map(|(n, _)| format_ident!("{}", n))
        .collect();

    for (name, op) in &ops {
        let name = format_ident!("{}", name);
        let mnemonic = &op.mnemonic;
        let code = op.code;
        let extra_len = op.extra_len as usize;
        let jump = op.jump;
        let jump_target = op.jump_target;
        let pops = op.pops;
        let pushes = op.pushes;
        let exit = op.exits;

        let generics;
        let variant_generics;
        let code_generics;
        let where_clause;
        let immediate_type;
        let immediate;
        let immediate_mut;
        let struct_;
        let immediate_into;
        let code_type;
        let code_impl;
        let from_impl;

        if extra_len > 0 {
            immediate_type = quote! { I };
            generics = quote! { <#immediate_type> };
            where_clause = quote! { where #immediate_type: super::Immediate<#extra_len> };

            let var_ident = format_ident!("P{}", extra_len);
            variant_generics = quote! { <T::#var_ident> };
            code_generics = quote! { <()> };

            struct_ = quote! {
                pub struct #name #generics (
                    #[doc = "The immediate argument for this operation."]
                    pub #immediate_type
                ) #where_clause;
            };

            immediate = quote! { Some(&self.0) };
            immediate_mut = quote! { Some(&mut self.0) };
            immediate_into = quote! { Some(self.0) };
            code_type = quote! { #name<()> };
            code_impl = quote! { #name(()) };

            from_impl = quote! {
                impl <#immediate_type, T> From<#name<#immediate_type>> for Op<T> where
                    #immediate_type: super::Immediate<#extra_len>,
                    T: ?Sized + super::Immediates<#var_ident=#immediate_type>,
                {
                    fn from(op: #name<#immediate_type>) -> Self {
                        Self::#name(op)
                    }
                }
            };

            code_matches.extend(quote! {
                Self::#name(_) => Op::#name(#name(())),
            });

            display_matches.extend(quote! {
                Self::#name(v) => v.mnemonic(),
            });

            new_matches.extend(quote! {
                Op::#name(_) => None,
            });

            from_u8_matches.extend(quote! {
                #code => Self::#name(#name(())),
            });

            from_str_matches.extend(quote! {
                #mnemonic => Self::#name(#name(())),
            });

            immediate_matches.extend(quote! {
                Self::#name(v) => v.immediate().map(std::borrow::Borrow::borrow),
            });

            immediate_mut_matches.extend(quote! {
                Self::#name(v) => v.immediate_mut().map(std::borrow::BorrowMut::borrow_mut),
            });

            into_immediate_matches.extend(quote! {
                Self::#name(v) => v.into_immediate().map(Into::into),
            });

            from_slice_matches.extend(quote! {
                #code => Self::#name(#name(bytes[1..].try_into()?)),
            });
        } else {
            where_clause = quote! {};
            generics = quote! {};
            struct_ = quote! { pub struct #name; };
            immediate_type = quote! { super::Void };
            immediate = quote! { None };
            immediate_mut = quote! { None };
            immediate_into = quote! { None };
            variant_generics = quote! {};
            code_generics = quote! {};
            code_type = quote! { Self };
            code_impl = quote! { #name };

            from_impl = quote! {
                impl<T> From<#name> for Op<T> where
                    T: ?Sized + super::Immediates,
                {
                    fn from(op: #name) -> Self {
                        Self::#name(op)
                    }
                }
            };

            code_matches.extend(quote! {
                Self::#name(_) => Op::#name(#name),
            });

            display_matches.extend(quote! {
                Self::#name(v) => v.mnemonic(),
            });

            new_matches.extend(quote! {
                Op::#name(_) => Some(Self::#name(#name)),
            });

            from_u8_matches.extend(quote! {
                #code => Self::#name(#name),
            });

            from_str_matches.extend(quote! {
                #mnemonic => Self::#name(#name),
            });

            immediate_matches.extend(quote! {
                Self::#name(_) => None,
            });

            immediate_mut_matches.extend(quote! {
                Self::#name(_) => None,
            });

            into_immediate_matches.extend(quote! {
                Self::#name(_) => None,
            });

            from_slice_matches.extend(quote! {
                #code => Self::#name(#name),
            });
        }

        size_matches.extend(quote! {
            Self::#name(v) => 1 + v.extra_len(),
        });

        tokens.extend(quote! {
            #[doc = concat!("Representation of the `", #mnemonic, "` instruction.")]
            #[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
            #struct_

            impl #generics Operation for #name #generics #where_clause {
                type Immediate = #immediate_type;
                type ImmediateRef = #immediate_type;
                type Code = #code_type;

                fn immediate(&self) -> Option<&Self::ImmediateRef> { #immediate }
                fn immediate_mut(&mut self) -> Option<&mut Self::ImmediateRef> { #immediate_mut }
                fn into_immediate(self) -> Option<Self::Immediate> { #immediate_into }

                fn code(&self) -> Self::Code { #code_impl }

                fn extra_len(&self) -> usize { #extra_len }

                fn mnemonic(&self) -> &str { #mnemonic }

                fn is_jump(&self) -> bool { #jump }
                fn is_jump_target(&self) -> bool { #jump_target }
                fn is_exit(&self) -> bool { #exit }
                fn pops(&self) -> usize { #pops as usize }
                fn pushes(&self) -> usize { #pushes as usize}
            }

            impl From<#name #code_generics> for u8 {
                fn from(_: #name #code_generics) -> Self {
                    #code
                }
            }

            #from_impl
        });

        variants.extend(quote! {
            #[doc = concat!("The `", #mnemonic, "` instruction (See [`struct@", stringify!(#name), "`].)")]
            #name ( #name #variant_generics ),
        });
    }

    let mut debug_bound = quote! {};
    let mut clone_bound = quote! {};
    let mut partial_eq_bound = quote! {};
    let mut eq_bound = quote! {};
    let mut ord_bound = quote! {};
    let mut partial_ord_bound = quote! {};
    let mut hash_bound = quote! {};
    let mut bounds = Vec::with_capacity(32);

    for ii in 1..=32usize {
        let ident = format_ident!("P{}", ii);

        debug_bound.extend(quote! {
            T::#ident: std::fmt::Debug,
        });

        clone_bound.extend(quote! {
            T::#ident: Clone,
        });

        partial_eq_bound.extend(quote! {
            T::#ident: std::cmp::PartialEq,
        });

        eq_bound.extend(quote! {
            T::#ident: std::cmp::Eq,
        });

        ord_bound.extend(quote! {
            T::#ident: std::cmp::Ord,
        });

        partial_ord_bound.extend(quote! {
            T::#ident: std::cmp::PartialOrd,
        });

        hash_bound.extend(quote! {
            T::#ident: std::hash::Hash,
        });

        bounds.push(quote! { #ident });
    }

    let debug_bound = debug_bound.to_string();
    let clone_bound = clone_bound.to_string();
    let partial_eq_bound = partial_eq_bound.to_string();
    let eq_bound = eq_bound.to_string();
    let ord_bound = ord_bound.to_string();
    let partial_ord_bound = partial_ord_bound.to_string();
    let hash_bound = hash_bound.to_string();

    tokens.extend(quote! {
        #[doc = concat!("All instructions in the ", #fork_name, " fork.")]
        #[derive(educe::Educe)]
        #[educe(
            Clone(bound = #clone_bound),
            Debug(bound = #debug_bound),
            PartialEq(bound = #partial_eq_bound),
            Eq(bound = #eq_bound),
            Ord(bound = #ord_bound),
            PartialOrd(bound = #partial_ord_bound),
            Hash(bound = #hash_bound),
        )]
        pub enum Op<T> where T: super::Immediates + ?Sized {
            #variants
        }

        // TODO: For some reason deriving Copy with educe didn't work.
        impl<T> Copy for Op<T>
        where
            T: super::Immediates + ?Sized,
            #(T::#bounds: Copy,)*
        {
        }

        impl<T> Operation for Op<T> where T: super::Immediates + ?Sized {
            type Code = Op<()>;
            type Immediate = T::Immediate;
            type ImmediateRef = T::ImmediateRef;

            fn immediate(&self) -> Option<&Self::ImmediateRef> {
                match self {
                    #immediate_matches
                }
            }

            fn immediate_mut(&mut self) -> Option<&mut Self::ImmediateRef> {
                match self {
                    #immediate_mut_matches
                }
            }

            fn into_immediate(self) -> Option<Self::Immediate> {
                match self {
                    #into_immediate_matches
                }
            }

            fn extra_len(&self) -> usize {
                match self {
                    #(
                    Self::#names(n) => n.extra_len(),
                    )*
                }
            }

            fn mnemonic(&self) -> &str {
                match self {
                    #(
                    Self::#names(n) => n.mnemonic(),
                    )*
                }
            }

            fn code(&self) -> Self::Code {
                match self {
                    #(
                    Self::#names(n) => Op::#names(n.code()),
                    )*
                }
            }

            fn is_jump(&self) -> bool {
                match self {
                    #(
                    Self::#names(n) => n.is_jump(),
                    )*
                }
            }

            fn is_jump_target(&self) -> bool {
                match self {
                    #(
                    Self::#names(n) => n.is_jump_target(),
                    )*
                }
            }

            fn is_exit(&self) -> bool {
                match self {
                    #(
                    Self::#names(n) => n.is_exit(),
                    )*
                }
            }

            fn pops(&self) -> usize {
                match self {
                    #(
                    Self::#names(n) => n.pops(),
                    )*
                }
            }

            fn pushes(&self) -> usize {
                match self {
                    #(
                    Self::#names(n) => n.pushes(),
                    )*
                }
            }
        }

        impl From<Op<()>> for u8 {
            fn from(op: Op<()>) -> u8 {
                match op {
                    #(
                    Op::#names(n) => n.code_byte(),
                    )*
                }
            }
        }

        impl<T> Op<T> where T: super::Immediates + ?Sized {
            /// Create a new `Op`.
            ///
            /// Returns `None` if the specified operation requires an immediate
            /// argument. See [`Op::with`] for more details.
            pub fn new(code: Op<()>) -> Option<Self> {
                match code {
                    #new_matches
                }
            }

            /// Returns the opcode of this operation.
            ///
            /// An opcode is the part of the operation that specifies the which
            /// operation to perform (for example `0x00` for `stop`.)
            pub fn code(&self) -> Op<()> {
                match self {
                    #code_matches
                }
            }

            /// Returns the total length of this operation, including its immediate.
            pub fn size(&self) -> usize {
                match self {
                    #size_matches
                }
            }
        }

        impl<T, E> Op<T> where
            T: super::Immediates + ?Sized,
            E: 'static + std::fmt::Display + std::error::Error,
            #( for <'a> &'a [u8]: TryInto<T::#bounds, Error = E>,)*
        {
            /// Parse a byte slice into an `Op`, with its immediate.
            ///
            /// Returns an error if [`TryInto::try_into`] fails, or if the byte
            /// slice contains an immediate for an opcode that does not take one.
            /// Errors usually occur when the byte slice is the wrong length for
            /// the given instruction.
            pub fn from_slice(bytes: &[u8]) -> Result<Self, super::FromSliceError<E>> {
                let result = match bytes[0] {
                    #from_slice_matches
                };
                if result.extra_len() == 0 && bytes.len() > 1 {
                    return super::NoImmediateSnafu.fail();
                }
                Ok(result)
            }
        }

        impl std::fmt::Display for Op<()> {
            fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
                let mnemonic = match self {
                    #display_matches
                };

                write!(fmt, "{}", mnemonic)
            }
        }

        impl From<u8> for Op<()> {
            fn from(opcode: u8) -> Self {
                match opcode {
                    #from_u8_matches
                }
            }
        }

        impl std::str::FromStr for Op<()> {
            type Err = super::FromStrError;

            fn from_str(mnemonic: &str) -> Result<Self, Self::Err> {
                let op = match mnemonic {
                    #from_str_matches
                    _ => return super::FromStrSnafu { mnemonic }.fail(),
                };

                Ok(op)
            }
        }

        impl Op<()> {
            /// Create the smallest push instruction capable of representing `n`.
            pub fn push_for(n: u128) -> Option<Self> {
                let bits = 0u128.leading_zeros() - n.leading_zeros();
                let bytes = std::cmp::max(1, (bits + 8 - 1) / 8);
                Self::push(bytes.try_into().unwrap())
            }

            /// Create a new push instruction with the given immediate size.
            pub fn push(sz: usize) -> Option<Self> {
                // TODO: Automate generating this?
                let result = match sz {
                    1 => Self::Push1(Push1(())),
                    2 => Self::Push2(Push2(())),
                    3 => Self::Push3(Push3(())),
                    4 => Self::Push4(Push4(())),
                    5 => Self::Push5(Push5(())),
                    6 => Self::Push6(Push6(())),
                    7 => Self::Push7(Push7(())),
                    8 => Self::Push8(Push8(())),
                    9 => Self::Push9(Push9(())),
                    10 => Self::Push10(Push10(())),
                    11 => Self::Push11(Push11(())),
                    12 => Self::Push12(Push12(())),
                    13 => Self::Push13(Push13(())),
                    14 => Self::Push14(Push14(())),
                    15 => Self::Push15(Push15(())),
                    16 => Self::Push16(Push16(())),
                    17 => Self::Push17(Push17(())),
                    18 => Self::Push18(Push18(())),
                    19 => Self::Push19(Push19(())),
                    20 => Self::Push20(Push20(())),
                    21 => Self::Push21(Push21(())),
                    22 => Self::Push22(Push22(())),
                    23 => Self::Push23(Push23(())),
                    24 => Self::Push24(Push24(())),
                    25 => Self::Push25(Push25(())),
                    26 => Self::Push26(Push26(())),
                    27 => Self::Push27(Push27(())),
                    28 => Self::Push28(Push28(())),
                    29 => Self::Push29(Push29(())),
                    30 => Self::Push30(Push30(())),
                    31 => Self::Push31(Push31(())),
                    32 => Self::Push32(Push32(())),
                    _ => return None,
                };

                Some(result)
            }

            /// Join this opcode with an immediate argument.
            ///
            /// Panics if this opcode does not take an immediate argument. See
            /// [`Op::new`].
            pub fn with<T, I, E>(self, immediate: I) -> Result<Op<T>, E>
            where
                T: ?Sized + super::Immediates,
                #(I: TryInto<T::#bounds, Error = E>,)*
            {
                let result = match self {
                    #(
                    Self::#immediate_ops(_) => Op::#immediate_ops(#immediate_ops(immediate.try_into()?)),
                    )*
                    _ => panic!("only relative jumps/push operations can be combined"),
                };

                Ok(result)
            }

            /// Converts a push instruction to the next larger push size.
            ///
            /// For example, a `push2` will become a `push3`.
            ///
            /// ## Panics
            ///
            /// This function panics if `self` is not a push instruction.
            pub fn upsize(self) -> Option<Self> {
                let extra = match self.extra_len() {
                    0 => panic!("only push ops can be upsized"),
                    e => e,
                };

                Self::push(extra + 1)
            }
        }

        #[cfg(test)]
        mod tests {
            use super::*;

            #[test]
            fn code_from_u8() {
                for ii in 0..=u8::MAX {
                    let parsed = Op::try_from(ii).unwrap();
                    if ii == 0xfe {
                        assert_eq!(Op::from(Invalid), parsed);
                    } else {
                        assert_ne!(Op::from(Invalid), parsed);
                    }
                }
            }

            #[test]
            fn code_through_str() {
                for ii in 0..=u8::MAX {
                    let spec = Op::try_from(ii).unwrap();
                    let txt = spec.to_string();
                    let parsed: Op<_> = txt.parse().unwrap();
                    assert_eq!(spec, parsed);
                }
            }

            #[test]
            fn op_new() {
                for ii in 0..=u8::MAX {
                    let spec = Op::try_from(ii).unwrap();
                    let op = Op::<[u8]>::new(spec);
                    if spec.extra_len() > 0 {
                        assert_eq!(op, None);
                    } else {
                        let op = op.unwrap();
                        assert_eq!(op.code(), spec);
                    }
                }
            }

            #[test]
            fn code_push_for_zero() {
                let spec = Op::push_for(0);
                assert_eq!(spec, Some(Op::Push1(Push1(()))));
            }

            #[test]
            fn code_push_for_one() {
                let spec = Op::push_for(1);
                assert_eq!(spec, Some(Op::Push1(Push1(()))));
            }

            #[test]
            fn code_push_for_255() {
                let spec = Op::push_for(255);
                assert_eq!(spec, Some(Op::Push1(Push1(()))));
            }

            #[test]
            fn code_push_for_256() {
                let spec = Op::push_for(256);
                assert_eq!(spec, Some(Op::Push2(Push2(()))));
            }

            #[test]
            fn code_push_for_65535() {
                let spec = Op::push_for(65535);
                assert_eq!(spec, Some(Op::Push2(Push2(()))));
            }

            #[test]
            fn code_push_for_65536() {
                let spec = Op::push_for(65536);
                assert_eq!(spec, Some(Op::Push3(Push3(()))));
            }

            #[test]
            fn code_push_for_16777215() {
                let spec = Op::push_for(16777215);
                assert_eq!(spec, Some(Op::Push3(Push3(()))));
            }

            #[test]
            fn code_push_for_16777216() {
                let spec = Op::push_for(16777216);
                assert_eq!(spec, Some(Op::Push4(Push4(()))));
            }

            #[test]
            fn code_push_for_4294967295() {
                let spec = Op::push_for(4294967295);
                assert_eq!(spec, Some(Op::Push4(Push4(()))));
            }

            #[test]
            fn code_to_u8_selfdestruct() {
                let spec = Op::from(SelfDestruct);
                assert_eq!(0xffu8, spec.into());
            }
        }
    });

    let out_dir = std::env::var_os("OUT_DIR").unwrap();
    let mut out_path = PathBuf::from(out_dir);
    out_path.push(&format!("{}.rs", fork_name));

    File::create(&out_path)?.write_all(tokens.to_string().as_bytes())?;

    Ok(())
}

fn main() {
    generate_fork("london").unwrap();
    generate_fork("shanghai").unwrap();
    generate_fork("cancun").unwrap();
    generate_fork("prague").unwrap();
}
