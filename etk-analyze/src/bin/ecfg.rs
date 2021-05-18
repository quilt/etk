#[path = "ecfg/opts.rs"]
mod opts;

use crate::opts::Opts;

use etk_analyze::blocks::basic::Separator;
use etk_analyze::blocks::AnnotatedBlock;
use etk_analyze::cfg::ControlFlowGraph;

use etk_asm::disasm::Disassembler;

use std::fs::File;
use std::io::Write;

use structopt::StructOpt;

type Error = Box<dyn std::error::Error + 'static>;

fn main() {
    let result = run();

    let root = match result {
        Ok(_) => return,
        Err(e) => e,
    };

    let mut current = Some(&*root as &dyn std::error::Error);

    while let Some(e) = current.take() {
        eprintln!("Error: {}", e);
        eprintln!("Caused by:");
        current = e.source();
    }

    eprintln!("Nothing.");
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

    let blocks = separator
        .take()
        .into_iter()
        .chain(separator.finish().into_iter())
        .map(|x| AnnotatedBlock::annotate(&x));

    let mut cfg = ControlFlowGraph::new(blocks);
    cfg.refine_shallow();

    writeln!(out, "{}", cfg.render()).unwrap();

    Ok(())
}
