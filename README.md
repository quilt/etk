# EVM Toolkit (ETK)

ETK is a collection of tools for writing, reading, and analyzing EVM bytecode.

## Tools

* Assembler (eas)
* Disassembler (disease)

## Installation

```console
git clone git@github.com:quilt/etk.git
cd etk
cargo install --path etk-asm --features cli
cargo install --path etk-analyze --features cli
```

## Usage

```console
$ eas contract.asm out.bin
$ disease --bin-file out.bin
    0:  CALLDATASIZE
    1:  PUSH1 0x01
    2:  DUP1
    ...
```

## Assembly Format

### Opcodes

Opcodes can be used via their [mnemonic](etk-asm/src/parse/asm.pest).

### Immediates

Some opcodes accept immediate operands. The only EVM instruction that suports
immediates natively is the `PUSH` family. ETK also allows for `jumpdest`
instructions to take an immediate label.

```asm
; push a constant
push1 1

; push a label
push4 .label

; label a jumpdest
jumpdest .label
```

### Expanders

Expanders are built-in macros for common use cases. For example, selector
generation is a requirement for being ABI compatible.

```asm
; push the first four bytes of `keccak("transfer(address, uint256)")` to the
; stack.
push4 selector("transfer(address, uint256)")
```

### Macros

Coming soon!

## Example Program

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
push1 e0                        ; [dirty_selector, 28*8]
shr                             ; [selector]

; Jump to the coresponding function.
dup1                            ; [selector, selector]
push4 selector("flag()")        ; [selector, selector, decimals]
eq                              ; [selector, is_decimals]
push4 .flag                     ; [selector, is_decimals, .decimals]
jumpi                           ; [selector]

dup1                            ; [selector, selector]
push4 selector("set_flag()")    ; [selector, selector, decimals]
eq                              ; [selector, is_decimals]
push4 .set                      ; [selector, is_decimals, .decimals]
jumpi                           ; [selector]

stop

; return the current value of the flag
jumpdest .flag
pop                             ; []
push1 0                         ; [0]
sload                           ; [flag]
push1 0                         ; [flag, 0]
mstore                          ; []
push1 0                         ; [0]
push1 20                        ; [0, 32] 
return

; set the flat to "1"
jumpdest .set
pop                             ; []
push1 1                         ; [1]
push1 0                         ; [1, 0]
mstore                          ; []

stop
```
