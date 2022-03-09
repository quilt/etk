# Expression Macros

An **expression macro** is a type of expression which is resolved during assembly. This is useful for defining constant values or constant functions on values, such as defining getters on memory pointers.

## Defining an Expression Macro

Expression macros can accept an arbitrary number of parameters. Parameters are referenced within the macro definition by prepending `$` to the parameter's name.

```rust
# extern crate etk_asm;
# let src = r#"
%def my_macro()
    42
%end

%def sum(x, y, z)
    $x+$y+$z
%end
# "#;
# let mut ingest = etk_asm::ingest::Ingest::new(Vec::new());
# ingest.ingest(file!(), src).unwrap();
```

## Using an Expression Macro

Expression macros can be invoked anywhere an expression is expected.

```rust
# extern crate etk_asm;
# let src = r#"
# %def my_macro()
#    42
# %end
# %def sum(x, y, z)
#     $x+$y+$z
# %end
push1 my_macro()
push1 sum(1, 2, my_macro())
# "#;
# let mut output = Vec::new();
# let mut ingest = etk_asm::ingest::Ingest::new(&mut output);
# ingest.ingest(file!(), src).unwrap();
# assert_eq!(output, &[0x60, 0x2a, 0x60, 0x2d]);
```
