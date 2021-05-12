# Command-Line Tools

ETK provides a set of command-line tools, and can also be used as Rust crates. Let's dive into the command line tools first.

## Install from Source

ETK and its tools can be installed by compiling the source code on your local machine.

### Pre-requisite

ETK is written in [Rust][rust] and needs to be compiled with **cargo**. The minimum supported Rust version `1.51`. If you don't have Rust installed, [install] it now.

[rust]: https://www.rust-lang.org/
[install]: https://www.rust-lang.org/tools/install

### Install Development Version

The development version contains all the latest features, bugs, and maybe even some bug-fixes that will eventually be released in the next version. If you can't wait for the next release, you can install the development version from git yourself.

Open a terminal and use cargo to install ETK:

```bash
cargo install \
    --git 'https://github.com/quilt/etk' \
    --features cli \
    etk-asm \
    etk-analyze
```

### Install Released Version

Once you have Rust and cargo installed, you just have to type this snippet in your terminal:

```bash
cargo install --features cli etk-asm etk-analyze
```

## Install from Binaries

Precompiled binaries will be provided for select platforms on a best-effort basis. Visit [the releases page][releases] to download the appropriate version, once we create one, for your platform.

[releases]: https://github.com/quilt/etk/releases

## Install Syntax Highlighting

Syntax highlighting for `vim` is available via [`vim-etk`](https://github.com/quilt/vim-etk).
