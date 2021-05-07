# Assembler: `eas`

The assembler command converts human-readable mnemonics (ex. `push2`, `caller`) into the raw bytes the EVM interpreter expects, encoded in hexadecimal. In addition to this conversion, the assembler performs transformations on the source in the form of expression- and instruction- macros, which we'll get into later.


Invoking the assembler is pretty simple:

```bash
eas input.etk output.hex
```

The input argument (`input.etk` here) is the path to an assembly file, and is required. `output.hex` is the path where the assembled instructions will be written, encoded in hex. If the output path is omitted, the assembled instructions are written to the standard output.

## A Note on Paths

The input argument determines the _root_ of the project. If `/home/user/foobar/main.etk` is the input argument, the root would be `/home/user/foobar`. Only files within the root directory can be included or imported.
