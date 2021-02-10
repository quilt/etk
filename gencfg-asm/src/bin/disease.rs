#[path = "disease/opts.rs"]
mod opts;

use crate::opts::Opts;

use gencfg_asm::disasm::Disassembler;

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

    for op in disasm.ops() {
        writeln!(out, "{}", op)?;
    }

    Ok(())
}
