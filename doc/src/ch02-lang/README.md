# Language & Syntax

The ETK assembly language takes inspiration from [NASM] and other similar assemblers, but has its own particular flavor.

[NASM]: https://www.nasm.us/

## Syntax

### Friendly Example

This example should increment a value from 0 to 255 on the stack, then halt execution.

```rust
# extern crate etk_asm;
# let src = r#"
push1 0x00

loop:
    jumpdest
    push1 0x01
    add
    dup1
    push1 0xFF
    gt
    push1 loop
    jumpi

pop
stop                # This halts execution
# "#;
# let mut ingest = etk_asm::ingest::Ingest::new(Vec::new());
# ingest.ingest(file!(), src).unwrap();
```

The first line&mdash;`push1 0x00`&mdash;describes a push instruction of length one, with a value of `0`. When assembled, this line would become `0x6000`.

Next, we have `loop:`, which introduces a label named _loop_. Labels can be used as arguments to push instructions, usually for jumps or subroutines.

Finally, we have `# This halts execution`, which is a comment. Comments are introduced with `#` and continue to the end of the line. Comments are ignored as far as the assembler is concerned.

There are a couple other features, like macros, which will be covered in later chapters.

### Formal Syntax

For the language nerds, the ETK assembly language syntax is defined by the following [Pest] grammar:

```pest
{{#include ../../../etk-asm/src/parse/asm.pest}}
```

[Pest]: https://pest.rs/
