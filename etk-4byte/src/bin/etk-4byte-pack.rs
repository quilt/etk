use std::collections::BTreeMap;
use std::convert::TryInto;
use std::env;
use std::fs::File;
use std::io::{BufRead, BufReader, BufWriter, Error};
use std::path::PathBuf;

fn main() -> Result<(), Error> {
    let in_path: PathBuf = [env!("CARGO_MANIFEST_DIR"), "src", "signatures.txt"]
        .iter()
        .collect();

    let in_file = File::open(in_path)?;
    let input = BufReader::new(in_file).lines();

    // Storing the strings together at the end gets better compression. That's
    // my theory, anyway.
    let mut strings: Vec<Vec<String>> = Vec::with_capacity(900000);
    let mut map: BTreeMap<u32, u32> = BTreeMap::new();

    for result in input {
        let line = result?;
        let mut parts = line.split(' ');

        let selector: u32 = parts.next().unwrap().parse().unwrap();
        let signatures: Vec<_> = parts.map(|x| x.to_owned()).collect();

        let index: u32 = strings.len().try_into().unwrap();
        strings.push(signatures);

        if map.insert(selector, index).is_some() {
            unreachable!();
        }
    }

    let path: PathBuf = [env!("CARGO_MANIFEST_DIR"), "src", "database.br"]
        .iter()
        .collect();
    std::fs::create_dir_all(path.parent().unwrap())?;

    let mut file = File::create(&path)?;

    let mut compress = brotli::CompressorWriter::new(&mut file, 4096, 9, 25);
    let mut output = BufWriter::new(&mut compress);

    bincode::serialize_into(&mut output, &(map, strings)).unwrap();

    Ok(())
}
