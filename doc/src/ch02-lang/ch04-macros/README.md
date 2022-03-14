# Macros

A macro is a rule or pattern that maps a given input to a replacement output. In other words, the assembler replaces a _macro invocation_ with some other text (the _macro expansion_.)

## Types

Macros in ETK take one of two forms: instruction macros, and expression macros. Both types of macros are written as a name followed by arguments in parentheses.

### Instruction Macros

An instruction macro looks like this:

```rust
# extern crate etk_asm;
# let src = r#"
%macro push_sum(a, b)
    push1 $a + $b
%end

%push_sum(4, 2)
# "#;
# let mut output = Vec::new();
# let mut ingest = etk_asm::ingest::Ingest::new(&mut output);
# ingest.ingest(file!(), src).unwrap();
# assert_eq!(output, &[0x60, 0x06]);
```

Instruction macros always begin with `%`, and expand to one or more instructions. In this case, `%my_macro(4, 2)` would expand to:

```ignore
push1 0x06
```

### Expression Macros

Expression macros _do not_ begin with `%`, and cannot replace instructions. Instead, expression macros can be used in expressions. For example:

```rust
# extern crate etk_asm;
# let src = r#"
%def add_one(num)
    $num+1
%end

push1 add_one(41)
# "#;
# let mut output = Vec::new();
# let mut ingest = etk_asm::ingest::Ingest::new(&mut output);
# ingest.ingest(file!(), src).unwrap();
# assert_eq!(output, &[0x60, 0x2a]);
```

Here, `add_one(...)` is an expression macro that returns the `num+1`. The fully expanded source would look like:

```ignore
push1 42
```

