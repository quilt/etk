# Instruction Macros

An **instruction macro** is a type of macro that can expand to an arbitrary number of instructions. This is useful for defining routines that are repeated many times or routines with expressions that are parameterized.

## Defining an Instruction Macro

Instruction macros can accept an arbitrary number of parameters. Parameters are referenced within the macro definition by prepending `$` to the parameter's name.

```rust
# extern crate etk_asm;
# extern crate etk_ops;
# let src = r#"
%macro my_macro()
    push1 42
%end

%macro sum(x, y, z)
    push1 $x+$y+$z
%end
# "#;
# let mut ingest = etk_asm::ingest::Ingest::new(Vec::new(), etk_ops::HardFork::Cancun);
# ingest.ingest(file!(), src).unwrap();
```

## Using a Instruction Macro

Expression macros can be invoked anywhere an instruction is expected.

```rust
# extern crate etk_asm;
# extern crate etk_ops;
# let src = r#"
# %macro my_macro()
#    push1 42
# %end
# %macro sum(x, y, z)
#     push1 $x+$y+$z
# %end
%my_macro()
%sum(1, 2, 3)
# "#;
# let mut output = Vec::new();
# let mut ingest = etk_asm::ingest::Ingest::new(&mut output, etk_ops::HardFork::Cancun);
# ingest.ingest(file!(), src).unwrap();
# assert_eq!(output, &[0x60, 0x2a, 0x60, 0x06]);
```
