use etk_cli::errors::WithSources;
use etk_cli::io::HexWrite;

use etk_asm::ingest::{Error, Ingest};
use etk_ops::HardFork;

use std::fs::File;
use std::io::prelude::*;
use std::path::PathBuf;

use clap::StructOpt;

#[derive(Debug, StructOpt)]
#[structopt(name = "eas")]
struct Opt {
    #[structopt(parse(from_os_str))]
    input: PathBuf,
    #[structopt(parse(from_os_str))]
    out: Option<PathBuf>,

    #[structopt(long, parse(from_os_str))]
    hardfork: Option<HardFork>,
}

fn create(path: PathBuf) -> File {
    match File::create(&path) {
        Err(why) => panic!("couldn't create `{}`: {}", path.display(), why),
        Ok(file) => file,
    }
}

fn main() {
    let err = match run() {
        Ok(_) => return,
        Err(e) => e,
    };

    eprintln!("{}", WithSources(err));
    std::process::exit(1);
}

fn run() -> Result<(), Error> {
    let opt: Opt = clap::Parser::parse();

    let mut out: Box<dyn Write> = match opt.out {
        Some(o) => Box::new(create(o)),
        None => Box::new(std::io::stdout()),
    };

    let opthard = opt.hardfork.clone();
    let mut hardfork = match opt.hardfork {
        Some(h) => h,
        None => HardFork::default(),
    };

    println!("Hardfork: {:?}.", hardfork);

    let hex_out = HexWrite::new(&mut out);

    let mut ingest = Ingest::new(hex_out, hardfork);
    ingest.ingest_file(opt.input)?;

    out.write_all(b"\n").unwrap();

    Ok(())
}
