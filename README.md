# EVM Toolkit (ETK)

[![license](https://img.shields.io/badge/license-MIT%2FApache--2.0-blue)](https://github.com/quilt/etk)
[![ci status](https://github.com/lightclient/eipv/workflows/ci/badge.svg)](https://github.com/quilt/etk/actions)

ETK is a collection of tools for writing, reading, and analyzing EVM bytecode.

## The ETK Book

ETK has some more friendly documentation!

 - [For the `master` branch](https://quilt.github.io/etk)

## Quickstart

### Tools

* Assembler (eas)
* Disassembler (disease)

### Installation

```console
cargo install --git https://github.com/quilt/etk.git etk-asm etk-analyze
```

### Usage

```console
$ eas contract.etk out.hex
$ disease --hex-file out.hex
    0:  calldatasize
    1:  push1 0x01
    2:  dup1
    ...
```

### Assembly Format

#### Opcodes

Opcodes can be used via their [mnemonic](etk-asm/src/parse/asm.pest).

#### Immediates

Some opcodes accept immediate operands. The only EVM instruction that suports
immediates natively is the `PUSH` family. ETK also allows for `jumpdest`
instructions to take an immediate label.

```asm
; push a constant
push1 1

; push a label
push4 label

; label a jumpdest
label:
jumpdest
```

#### Expanders

Expanders are built-in macros for common use cases. For example, selector
generation is a requirement for being ABI compatible.

```asm
; push the first four bytes of `keccak("transfer(address, uint256)")` to the
; stack.
push4 selector("transfer(address, uint256)")
```

#### Macros

Coming soon!

### Example Program

```asm
; -- Instructions --            -- Current stack layout --

; Read the calldata into memory.
calldatasize                    ; [calldatasize]
push1 0                         ; [calldatasize, calldata_ptr]
dup1                            ; [calldatasize, calldata_ptr, mem_ptr]
calldatacopy                    ; []

; Extract only the function selector
push1 0                         ; [selector_ptr]
mload                           ; [dirty_selector]
push1 0xe0                      ; [dirty_selector, 28*8]
shr                             ; [selector]

; Jump to the coresponding function.
dup1                            ; [selector, selector]
push4 selector("flag()")        ; [selector, selector, decimals]
eq                              ; [selector, is_decimals]
push4 flag                      ; [selector, is_decimals, decimals]
jumpi                           ; [selector]

dup1                            ; [selector, selector]
push4 selector("set_flag()")    ; [selector, selector, decimals]
eq                              ; [selector, is_decimals]
push4 set                       ; [selector, is_decimals, decimals]
jumpi                           ; [selector]

stop

; return the current value of the flag
flag:
jumpdest
pop                             ; []
push1 0                         ; [0]
sload                           ; [flag]
push1 0                         ; [flag, 0]
mstore                          ; []
push1 0                         ; [0]
push1 32                        ; [0, 32]
return

; set the flat to "1"
set:
jumpdest
pop                             ; []
push1 1                         ; [1]
push1 0                         ; [1, 0]
mstore                          ; []

stop
```
