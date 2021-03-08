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

```asm
; Read the calldata into memory.
calldatasize			        ; [calldatasize]
push1 0						    ; [calldatasize, calldata_ptr]
dup1						    ; [calldatasize, calldata_ptr, mem_ptr]
calldatacopy			        ; []

; Extract only the function selector
push1 0						    ; [selector_ptr]
mload           		        ; [dirty_selector]
push1 e0					    ; [dirty_selector, 28*8]
shr		      				    ; [selector]

; Jump to the coresponding function.
dup1						    ; [selector, selector]
push4 selector("flag()")	; [selector, selector, decimals]
eq						        ; [selector, is_decimals]
push4 .flag					    ; [selector, is_decimals, .decimals]
jumpi	                        ; [selector]

dup1						    ; [selector, selector]
push4 selector("set_flag()")	; [selector, selector, decimals]
eq						        ; [selector, is_decimals]
push4 .set					    ; [selector, is_decimals, .decimals]
jumpi	                        ; [selector]

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
