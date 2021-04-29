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
