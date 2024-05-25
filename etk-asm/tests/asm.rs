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
            5858600f01803803919082908239f36020601f537f0b68656c6c6f20776f
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

#[test]
fn instruction_macro() -> Result<(), Error> {
    let mut output = Vec::new();
    let mut ingester = Ingest::new(&mut output);
    ingester.ingest_file(source(&["instruction-macro", "main.etk"]))?;

    assert_eq!(
        output,
        hex!("5b5860005660406005600d601561000061004260086100006100426008")
    );

    Ok(())
}

#[test]
fn instruction_macro_with_empty_lines() -> Result<(), Error> {
    let mut output = Vec::new();
    let mut ingester = Ingest::new(&mut output);
    ingester.ingest_file(source(&["instruction-macro", "empty_lines.etk"]))?;

    assert_eq!(output, hex!("6000600060006000600060006000"));

    Ok(())
}

#[test]
fn instruction_macro_with_two_instructions_per_line() {
    let mut output = Vec::new();
    let mut ingester = Ingest::new(&mut output);
    let err = ingester
        .ingest_file(source(&[
            "instruction-macro",
            "macro-with-2-instructions-per-line.etk",
        ]))
        .unwrap_err();

    assert_matches!(err, Error::Parse { .. });
}

#[test]
fn undefined_label_undefined_macro() {
    let mut output = Vec::new();
    let mut ingester = Ingest::new(&mut output);
    let err = ingester
        .ingest_file(source(&[
            "instruction-macro",
            "undefined-label-undefined-macro.etk",
        ]))
        .unwrap_err();

    assert_matches!(err, etk_asm::ingest::Error::Assemble { source:
             etk_asm::asm::Error::UndeclaredInstructionMacro { name, .. }, .. 
    } if name == "revert".to_string());
}

#[test]
fn every_op() -> Result<(), Error> {
    let mut output = Vec::new();
    let mut ingester = Ingest::new(&mut output);
    ingester.ingest_file(source(&["every-op", "main.etk"]))?;

    assert_eq!(
        output,
        hex!(
            "
        00
        01
        02
        03
        04
        05
        06
        07
        08
        09
        0a
        0b

        10
        11
        12
        13
        14
        15
        16
        17
        18
        19
        1a
        1b
        1c
        1d

        20

        30
        31
        32
        33
        34
        35
        36
        37
        38
        39
        3a
        3b
        3c
        3d
        3e
        3f
        40
        41
        42
        43
        44
        45
        46
        47
        48

        50
        51
        52
        53
        54
        55
        56
        57
        58
        59
        5a
        5b
        5e

        60 aa
        61 aabb
        62 aabbcc
        63 aabbccdd
        64 aabbccddee
        65 aabbccddeeff
        66 aabbccddeeff00
        67 aabbccddeeff0011
        68 aabbccddeeff001122
        69 aabbccddeeff00112233
        6a aabbccddeeff0011223344
        6b aabbccddeeff001122334455
        6c aabbccddeeff00112233445566
        6d aabbccddeeff0011223344556677
        6e aabbccddeeff001122334455667788
        6f aabbccddeeff00112233445566778899
        70 aabbccddeeff00112233445566778899aa
        71 aabbccddeeff00112233445566778899aabb
        72 aabbccddeeff00112233445566778899aabbcc
        73 aabbccddeeff00112233445566778899aabbccdd
        74 aabbccddeeff00112233445566778899aabbccddee
        75 aabbccddeeff00112233445566778899aabbccddeeff
        76 aabbccddeeff00112233445566778899aabbccddeeff00
        77 aabbccddeeff00112233445566778899aabbccddeeff0011
        78 aabbccddeeff00112233445566778899aabbccddeeff001122
        79 aabbccddeeff00112233445566778899aabbccddeeff00112233
        7a aabbccddeeff00112233445566778899aabbccddeeff0011223344
        7b aabbccddeeff00112233445566778899aabbccddeeff001122334455
        7c aabbccddeeff00112233445566778899aabbccddeeff00112233445566
        7d aabbccddeeff00112233445566778899aabbccddeeff0011223344556677
        7e aabbccddeeff00112233445566778899aabbccddeeff001122334455667788
        7f aabbccddeeff00112233445566778899aabbccddeeff00112233445566778899
        80
        81
        82
        83
        84
        85
        86
        87
        88
        89
        8a
        8b
        8c
        8d
        8e
        8f
        90
        91
        92
        93
        94
        95
        96
        97
        98
        99
        9a
        9b
        9c
        9d
        9e
        9f
        a0
        a1
        a2
        a3
        a4

        f0
        f1
        f2
        f3
        f4
        f5

        fa

        fd
        fe
        ff
    "
        )
    );

    Ok(())
}

#[test]
fn test_variable_sized_push_and_include() -> Result<(), Error> {
    let mut output = Vec::new();
    let mut ingester = Ingest::new(&mut output);
    ingester.ingest_file(source(&["variable-push", "main.etk"]))?;

    assert_eq!(output, hex!("61025758585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585801010101010158585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858015b"));

    Ok(())
}

#[test]
fn test_variable_sized_push2() -> Result<(), Error> {
    let mut output = Vec::new();
    let mut ingester = Ingest::new(&mut output);
    ingester.ingest_file(source(&["variable-push2", "main1.etk"]))?;
    assert_eq!(output, hex!("61010158"));

    let mut output = Vec::new();
    let mut ingester = Ingest::new(&mut output);
    ingester.ingest_file(source(&["variable-push2", "main2.etk"]))?;
    assert_eq!(output, hex!("61010158"));

    let mut output = Vec::new();
    let mut ingester = Ingest::new(&mut output);
    ingester.ingest_file(source(&["variable-push2", "main3.etk"]))?;
    assert_eq!(output, hex!("610107015801"));

    let mut output = Vec::new();
    let mut ingester = Ingest::new(&mut output);
    ingester.ingest_file(source(&["variable-push2", "main4.etk"]))?;
    let first_push = output.get(0..2).unwrap();
    assert_eq!(first_push, hex!("6004"));

    Ok(())
}

#[test]
fn test_include_hex() -> Result<(), Error> {
    let mut output = Vec::new();
    let mut ingester = Ingest::new(&mut output);
    ingester.ingest_file(source(&["include-hex", "main1.etk"]))?;

    assert_eq!(output, hex!("6002600c5f3960025ff300 cafeb0ba cafebabe"));

    let mut output = Vec::new();
    let mut ingester = Ingest::new(&mut output);
    let err = ingester
        .ingest_file(source(&["include-hex", "subdirectory", "main2.etk"]))
        .unwrap_err();

    assert_matches!(err, Error::DirectoryTraversal { .. });

    Ok(())
}
