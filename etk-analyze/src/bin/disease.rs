#[path = "disease/opts.rs"]
mod opts;

use crate::opts::Opts;

use etk_analyze::blocks::basic::Separator;

use etk_asm::disasm::{Disassembler, Offset};

use etk_cli::errors::WithSources;

use snafu::{Backtrace, Snafu};

use std::fs::File;
use std::io::Write;

use structopt::StructOpt;

#[derive(Debug, Snafu)]
enum Error {
    #[snafu(context(false))]
    Io {
        source: std::io::Error,
        backtrace: Backtrace,
    },
}

fn main() {
    let result = run();

    let root = match result {
        Ok(_) => return,
        Err(e) => e,
    };

    eprintln!("{}", WithSources(root));
    std::process::exit(1);
}

fn run() -> Result<(), Error> {
    let opts = Opts::from_args();

    let mut input = opts.src.open()?;
    let mut disasm = Disassembler::new();

    std::io::copy(&mut input, &mut disasm)?;

    let mut out: Box<dyn Write> = match opts.out_file {
        Some(path) => Box::new(File::create(path)?),
        None => Box::new(std::io::stdout()),
    };

    let mut separator = Separator::new();

    separator.push_all(disasm.ops());

    let basic_blocks = separator
        .take()
        .into_iter()
        .chain(separator.finish().into_iter());

    for block in basic_blocks {
        let mut offset = block.offset;
        for op in block.ops {
            let len = op.size();
            let off = Offset::new(offset, op);
            offset += len as usize;

            writeln!(out, "{}", off)?;
        }

        writeln!(out)?;
    }

    Ok(())
}
