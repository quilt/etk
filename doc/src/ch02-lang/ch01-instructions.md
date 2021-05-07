# Instructions

Instructions, also known as opcodes or `Op`s internally, are the building blocks of ETK smart contracts. Each instruction has a human-readable mnemonic (like `dup3`) and the machine readable equivalent (which would be `0x82`). The `push` family of instructions also encode an immediate value (or argument.)


## List of Instructions

```ignore
{{#include ../../../etk-asm/tests/asm/every-op/main.etk}}
```
