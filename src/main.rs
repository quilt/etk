use gencfg_asm::{asm::Assembler, parse_asm};
use std::fs;
use std::path::PathBuf;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
#[structopt(name = "assembler")]
struct Opt {
    #[structopt(parse(from_os_str))]
    input: PathBuf,
}

fn main() {
    let opt = Opt::from_args();
    let asm = fs::read_to_string(opt.input).unwrap();
    let parsed = match parse_asm(&asm) {
        Ok(p) => p,
        Err(e) => panic!("Parse error: {}"),
    };
    let mut assembler = Assembler::new();
    assembler.push_all(parsed).unwrap();
    println!("{}", hex::encode(assembler.take()));
}
