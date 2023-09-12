#[path = "ecfg/opts.rs"]
mod opts;

use crate::opts::Opts;

use etk_analyze::cfg::ControlFlowGraph;

use etk_asm::disasm::Disassembler;

use etk_cli::errors::WithSources;

use etk_dasm::blocks::basic::Separator;
use etk_dasm::blocks::AnnotatedBlock;

use snafu::{Backtrace, Snafu};

use std::fs::File;
use std::io::Write;

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
    let opts: Opts = clap::Parser::parse();

    let mut input = opts.src.open()?;
    let mut disasm = Disassembler::new();

    std::io::copy(&mut input, &mut disasm)?;

    let mut out: Box<dyn Write> = match opts.out_file {
        Some(path) => Box::new(File::create(path)?),
        None => Box::new(std::io::stdout()),
    };

    let mut separator = Separator::new();

    separator.push_all(disasm.ops());

    let blocks = separator
        .take()
        .into_iter()
        .chain(separator.finish())
        .map(|x| AnnotatedBlock::annotate(&x));

    let mut cfg = ControlFlowGraph::new(blocks);
    cfg.refine_shallow();

    writeln!(out, "{}", cfg.render()).unwrap();

    Ok(())
}
