use std::env;
use std::fs::File;
use std::io::{BufRead, BufReader, BufWriter, Error, Write};
use std::path::{Path, PathBuf};

fn main() -> Result<(), Error> {
    let in_path: PathBuf = [env!("CARGO_MANIFEST_DIR"), "src", "signatures.txt"]
        .iter()
        .collect();

    let in_file = File::open(in_path)?;
    let input = BufReader::new(in_file).lines();

    let path = Path::new(&env::var("OUT_DIR").unwrap()).join("codegen.rs");
    std::fs::create_dir_all(path.parent().unwrap())?;

    let mut output = BufWriter::new(File::create(&path).unwrap());

    let mut map = phf_codegen::Map::new();

    for result in input {
        let line = result?;
        let mut parts = line.split(' ');
        let selector: u32 = parts.next().unwrap().parse().unwrap();

        let signatures = parts.collect::<Vec<_>>().join(r#"", ""#);
        let signature_array = format!(r#"&["{}"]"#, signatures);
        map.entry(selector, &signature_array);
    }

    writeln!(
        &mut output,
        "static SIGNATURES: phf::Map<u32, &'static [&'static str]> = {};",
        map.build(),
    )?;

    Ok(())
}
