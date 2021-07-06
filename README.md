# EVM Toolkit (`etk`)

[![license](https://img.shields.io/badge/license-MIT%2FApache--2.0-blue)](https://github.com/quilt/etk)
[![chat](https://img.shields.io/badge/chat-telegram-informational)](https://t.me/joinchat/c-Cusp7Zh1tiM2Vh)
[![ci status](https://github.com/lightclient/eipv/workflows/ci/badge.svg)](https://github.com/quilt/etk/actions)

`etk` is a collection of tools for writing, reading, and analyzing EVM bytecode.

## Documentation

The [`etk` book](https://quilt.github.io/etk) is the most comprehensive guide to using `etk`.
* [Introduction](https://quilt.github.io/etk)
* [Usage](https://quilt.github.io/etk/ch01-cli/index.html)
    * [`eas`](https://quilt.github.io/etk/ch01-cli/ch01-eas.html)
    * [`disease`](https://quilt.github.io/etk/ch01-cli/ch02-disease.html)
* [Language & Syntax](https://quilt.github.io/etk/ch02-lang/index.html)

There are also several examples in the [`etk-asm/tests/asm`](etk-asm/tests/asm) directory. For further questions, join us on [Telegram](https://t.me/joinchat/c-Cusp7Zh1tiM2Vh).

## Quickstart

### Installation

`etk` requires `rustc` version `1.51`.

```console
cargo install --features cli etk-asm etk-analyze
```

#### Syntax Highlighting
* [`vim-etk`](https://github.com/quilt/vim-etk)

### Usage
`contract.etk`:
```asm
push1 42
push1 13
add
pop
```
```console
$ eas contract.etk out.hex
$ disease --hex-file out.hex
   0:   PUSH1 0x2a
   2:   PUSH1 0x0d
   4:   ADD
   5:   POP
```
### Dependencies
`ecfg` requires z3 to build
Ubuntu Installation Instructions (example):
```console
sudo apt-get update -y
sudo apt-get install -y z3
sudo apt-get install -y libz3-dev
```
Check the system logs to confirm that there are no related errors.
