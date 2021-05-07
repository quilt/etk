# Macros

A macro is a rule or pattern that maps a given input to a replacement output. In other words, the assembler replaces a _macro invocation_ with some other text (the _macro expansion_.)

## Types

Macros in ETK take one of two forms: instruction macros, and expression macros. Both types of macros are written as a name followed by arguments in parentheses.

### Instruction Macros

An instruction macro looks like this:

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

Instruction macros always begin with `%`, and expand to one or more instructions. In this case, `%push(hello)` would expand to:

```ignore
push1 hello

hello:
    jumpdest
```

### Expression Macros

Expression macros _do not_ begin with `%`, and cannot replace instructions. Instead, expression macros can take the place of labels or numeric literals. For example:

```rust
# extern crate etk_asm;
# let src = r#"
push4 selector("_burn(address,bytes32,uint256)")
# "#;
# let mut output = Vec::new();
# let mut ingest = etk_asm::ingest::Ingest::new(&mut output);
# ingest.ingest(file!(), src).unwrap();
# assert_eq!(output, &[0x63, 0x63, 0x93, 0x63, 0x27]);
```

Here, `selector(...)` is an expression macro that expands to `0x63936327`. The fully expanded source would look like:

```ignore
push4 0x63936327
```

