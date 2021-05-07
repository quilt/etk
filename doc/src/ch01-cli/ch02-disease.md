# Disassembler: `disease`

The disassembler command `disease` is roughly the inverse of the assembler. It transforms a string of bytes into human-readable mnemonics.

The basic invocation of `disease` looks like:

```bash
disease --bin-file contract.bin         # Disassemble a binary file
disease --hex-file contract.hex         # Disassemble a hexadecimal file
disease --code 0x5b600056               # Disassemble the command line argument
```

## Specifying Input

### `--bin-file`, or `-b`

When you use the `--bin-file` argument, `disease` will read the code from the specified file, and interpret it as raw binary bytes. Few tools use this format.

### `--hex-file`, or `-x`

With the `--hex-file` argument, the specified file is instead interpreted as hexadecimal.

### `--code`, or `-c`

Great for short snippets, the `--code` argument instructs `disease` to disassemble the hexadecimal string given directly on the command line.

## Specifying Output

### `--out-file`, or `-o`

If provided, `--out-file` causes the disassembled source to be written to the given path. Without `--out-file`, the disassembly is written to the standard output.

