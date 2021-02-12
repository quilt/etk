use gencfg_cli::io::InputSource;

use std::path::PathBuf;

use structopt::StructOpt;

#[derive(Debug, StructOpt)]
pub struct Opts {
    #[structopt(flatten)]
    pub src: InputSource,

    #[structopt(
        short = "o",
        long = "out-file",
        help = "path to output file (defaults to stdout)"
    )]
    pub out_file: Option<PathBuf>,
}

