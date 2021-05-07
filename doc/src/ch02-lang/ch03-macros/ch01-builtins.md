# Built-In Macros

Built-in macros are implemented by the assembler, and provide additional features beyond basic instructions, constants, or labels.

## Instruction Macros

### `%import("...")`

The `%import` macro expands to the instructions read from another file as if they had been typed here. The path is resolved relative to the current file.

#### Source: `main.etk`

```ignore
push1 some_label
jump

%import("other.etk")
```

#### Source: `other.etk`

```ignore
some_label:
    jumpdest
    stop
```

#### After Expansion

```ignore
push1 0x03
jump

jumpdest
stop
```

### `%include("...")`

The `%include` macro expands to the instructions read from another file, but unlike `%import`, the included file is assembled independently from the current file:

 - Labels from the included file are _not_ available in the including file, and vise versa.
 - The address of the first instruction in the included file will be zero.

The path is resolved relative to the current file.

#### Source: `main.etk`

```ignore
some_label:                 ; <- Not visible in `other.etk`.
    push1 some_label        ; <- Pushes a zero on the stack.

%include("other.etk")
```

#### Source: `other.etk`

```ignore
different_label:            ; <- Not visible in `main.etk`.
    push1 different_label   ; <- ALSO pushes a zero on the stack.
```

#### After Expansion

```ignore
push1 0x00
push1 0x00
```

### `%include_hex("...")`

The `%include_hex` macro functions exactly like `%include`, except instead of assembling the given path, it includes the raw hexadecimal bytes.

### `%push(...)`

The `%push` macro will expand to a reasonably sized `push` instruction for the given argument.

For example:

```rust
# extern crate etk_asm;
# let src = r#"
%push(hello)

hello:
    jumpdest
# "#;
# let mut output = Vec::new();
# let mut ingest = etk_asm::ingest::Ingest::new(&mut output);
# ingest.ingest(file!(), src).unwrap();
# assert_eq!(output, &[0x60, 0x02, 0x5b]);
```

Will look something like the following after expansion:

```ignore
push1 0x02
jumpdest
```

## Expression Macros

### `selector("...")`

The `selector` macro is useful when writing contracts that adhere to the [Solidity ABI][abi]. Specifically, the `selector` macro expands to the four byte selector of the given function signature.

For example:

```rust
# extern crate etk_asm;
# let src = r#"
push4 selector("_burn(address,bytes32,uint256)")    ; <- expands to 0x63936327
# "#;
# let mut output = Vec::new();
# let mut ingest = etk_asm::ingest::Ingest::new(&mut output);
# ingest.ingest(file!(), src).unwrap();
# assert_eq!(output, &[0x63, 0x63, 0x93, 0x63, 0x27]);
```

The fully expanded source would look like:

```ignore
push4 0x63936327
```

[abi]: https://docs.soliditylang.org/en/latest/abi-spec.html#function-selector
