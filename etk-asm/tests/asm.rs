use assert_matches::assert_matches;

use etk_asm::ingest::{Error, Ingest};

use hex_literal::hex;

use std::path::{Path, PathBuf};

fn source<P>(paths: &[P]) -> PathBuf
where
    P: AsRef<Path>,
{
    let rel: PathBuf = paths.into_iter().collect();
    let mut root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    root.push("tests");
    root.push("asm");
    root.join(&rel)
}

#[test]
fn simple_constructor() -> Result<(), Error> {
    let mut output = Vec::new();
    let mut ingester = Ingest::new(&mut output);
    ingester.ingest_file(source(&["simple-constructor", "ctor.etk"]))?;

    assert_eq!(
        output,
        hex!(
            "
            5858600f01803803919082908239f35b6020601f537f0b68656c6c6f20776f
            726c640000000000000000000000000000000000000000603f5260606000f3
            "
        ),
    );

    Ok(())
}

#[test]
fn out_of_bounds() {
    let mut output = Vec::new();
    let mut ingester = Ingest::new(&mut output);
    let err = ingester
        .ingest_file(source(&["out-of-bounds", "main", "main.etk"]))
        .unwrap_err();

    assert_matches!(err, Error::DirectoryTraversal { .. });
}

#[test]
fn subdirectory() -> Result<(), Error> {
    let mut output = Vec::new();
    let mut ingester = Ingest::new(&mut output);
    ingester.ingest_file(source(&["subdirectory", "main.etk"]))?;

    assert_eq!(output, hex!("63c001c0de60ff"));

    Ok(())
}

#[test]
fn variable_jump() -> Result<(), Error> {
    let mut output = Vec::new();
    let mut ingester = Ingest::new(&mut output);
    ingester.ingest_file(source(&["variable-jump", "main.etk"]))?;

    assert_eq!(output, hex!("6003565b"));

    Ok(())
}
