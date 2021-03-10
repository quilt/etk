use etk_asm::{asm::Assembler, parse_asm};
use std::fs::{self, File};
use std::io::prelude::*;
use std::path::PathBuf;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
#[structopt(name = "eas")]
struct Opt {
    #[structopt(parse(from_os_str))]
    input: PathBuf,
    #[structopt(parse(from_os_str))]
    out: Option<PathBuf>,
}

fn main() {
    let opt = Opt::from_args();
    let asm = fs::read_to_string(opt.input).unwrap();
    let parsed = match parse_asm(&asm) {
        Ok(p) => p,
        Err(e) => panic!("Parse error: {:?}", e),
    };
    let mut assembler = Assembler::new();
    assembler.push_all(parsed).unwrap();
    let output = hex::encode(assembler.take());
    assembler.finish().unwrap();

    if let Some(out_file) = opt.out {
        let display = out_file.display();
        let mut file = match File::create(&out_file) {
            Err(why) => panic!("couldn't create {}: {}", display, why),
            Ok(file) => file,
        };

        match file.write_all(output.as_bytes()) {
            Err(why) => panic!("couldn't write to {}: {}", display, why),
            Ok(_) => println!("successfully wrote to {}", display),
        }
    } else {
        print!("{}", output);
    }
}
