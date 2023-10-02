//! High-level interface for assembling instructions.
//!
//! See the [`Ingest`] documentation for examples and more information.
mod error {
    use crate::asm::Error as AssembleError;
    use crate::ParseError;

    use snafu::{Backtrace, Snafu};

    use std::path::PathBuf;

    /// Errors that may arise during the assembly process.
    #[derive(Debug, Snafu)]
    #[non_exhaustive]
    #[snafu(context(suffix(false)), visibility(pub(super)))]
    pub enum Error {
        /// An included/imported file was outside of the root directory.
        #[snafu(display(
            "`{}` is outside of the root directory `{}`",
            file.display(),
            root.display()
        ))]
        #[non_exhaustive]
        DirectoryTraversal {
            /// The root directory.
            root: PathBuf,

            /// The file that was to be included or imported.
            file: PathBuf,
        },

        /// An i/o error.
        #[snafu(display(
            "an i/o error occurred on path `{}` ({})",
            path.as_ref().map(|p| p.display().to_string()).unwrap_or_default(),
            message,
        ))]
        #[non_exhaustive]
        Io {
            /// The underlying source of this error.
            source: std::io::Error,

            /// Extra information about the i/o error.
            message: String,

            /// The location of the error.
            backtrace: Backtrace,

            /// The optional path where the error occurred.
            path: Option<PathBuf>,
        },

        /// An error that occurred while parsing a file.
        #[snafu(context(false))]
        #[non_exhaustive]
        #[snafu(display("parsing failed"))]
        Parse {
            /// The underlying source of this error.
            #[snafu(backtrace)]
            source: ParseError,
        },

        /// An error that occurred while assembling a file.
        #[snafu(context(false))]
        #[non_exhaustive]
        #[snafu(display("assembling failed"))]
        Assemble {
            /// The underlying source of this error.
            #[snafu(backtrace)]
            source: AssembleError,
        },

        /// An included fail failed to parse as hexadecimal.
        #[snafu(display("included file `{}` is invalid hex: {}", path.to_string_lossy(), source))]
        #[non_exhaustive]
        InvalidHex {
            /// Path to the offending file.
            path: PathBuf,

            /// The underlying source of this error.
            source: Box<dyn std::error::Error>,

            /// The location of the error.
            backtrace: Backtrace,
        },

        /// A recursion limit was reached while including or importing a file.
        #[snafu(display("too many levels of recursion/includes"))]
        #[non_exhaustive]
        RecursionLimit {
            /// The location of the error.
            backtrace: Backtrace,
        },
    }
}

use crate::asm::{Assembler, RawOp};
use crate::ast::Node;
use crate::parse::parse_asm;

pub use self::error::Error;

use snafu::{ensure, ResultExt};

use std::fs::{read_to_string, File};
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};

#[derive(Debug, Clone)]
struct Root {
    original: PathBuf,
    canonicalized: PathBuf,
}

impl Root {
    /// TODO: Temporal DOC
    fn new(mut file: PathBuf) -> Result<Self, Error> {
        // Pop the filename.
        if !file.pop() {
            return Err(io::Error::from(io::ErrorKind::NotFound)).context(error::Io {
                message: "no parent",
                path: Some(file),
            });
        }

        let file = std::env::current_dir()
            .context(error::Io {
                message: "getting cwd",
                path: None,
            })?
            .join(file);

        let metadata = file.metadata().with_context(|_| error::Io {
            message: "getting metadata",
            path: file.clone(),
        })?;

        // Root must be a directory.
        if !metadata.is_dir() {
            let err = io::Error::from(io::ErrorKind::NotFound);
            return Err(err).context(error::Io {
                message: "root is not directory",
                path: file,
            });
        }

        let canonicalized = std::fs::canonicalize(&file).with_context(|_| error::Io {
            message: "canonicalizing root",
            path: file.clone(),
        })?;

        Ok(Self {
            original: file,
            canonicalized,
        })
    }

    fn check<P>(&self, path: P) -> Result<(), Error>
    where
        P: AsRef<Path>,
    {
        let path = path.as_ref();

        let canonicalized = std::fs::canonicalize(path).with_context(|_| error::Io {
            message: "canonicalizing include/import",
            path: path.to_owned(),
        })?;

        // Don't allow directory traversals above the first file.
        if canonicalized.starts_with(&self.canonicalized) {
            Ok(())
        } else {
            error::DirectoryTraversal {
                root: self.original.clone(),
                file: path.to_owned(),
            }
            .fail()
        }
    }
}

#[derive(Debug)]
struct Program {
    depth: usize,
    root: Option<Root>,
    actual_path: PathBuf,
}

impl Program {
    fn new(root: Option<Root>) -> Self {
        Self {
            depth: 0,
            root: root.clone(),
            actual_path: root.map(|r| r.original).unwrap_or(PathBuf::new()),
        }
    }

    fn push_path(&mut self, path: PathBuf) -> Result<PathBuf, Error> {
        ensure!(self.depth <= 255, error::RecursionLimit);
        self.depth += 1;

        let path = if let Some(ref root) = self.root {
            let candidate = self.actual_path.join(path);
            root.check(&candidate)?;
            candidate
        } else {
            self.root = Some(Root::new(path.clone())?);
            path
        };

        Ok(path)
    }

    fn pop_path(&mut self, oldpath: PathBuf) {
        self.depth -= 1;
        self.actual_path = oldpath;
    }
}

/// A high-level interface for assembling files into EVM bytecode.
///
/// ## Example
///
/// ```rust
/// use etk_asm::ingest::Ingest;
/// #
/// # use etk_asm::ingest::Error;
/// #
/// # use hex_literal::hex;
///
/// let text = r#"
///     push2 lbl
///     lbl:
///     jumpdest
/// "#;
///
/// let mut output = Vec::new();
/// let mut ingest = Ingest::new(&mut output);
/// ingest.ingest("./example.etk", &text)?;
///
/// # let expected = hex!("6100035b");
/// # assert_eq!(output, expected);
/// # Result::<(), Error>::Ok(())
/// ```
#[derive(Debug)]
pub struct Ingest<W> {
    output: W,
}

impl<W> Ingest<W> {
    /// Make a new `Ingest` that writes assembled bytes to `output`.
    pub fn new(output: W) -> Self {
        Self { output }
    }
}

impl<W> Ingest<W>
where
    W: Write,
{
    /// Assemble instructions from the file located at `path`.
    pub fn ingest_file<P>(&mut self, path: P) -> Result<(), Error>
    where
        P: Into<PathBuf>,
    {
        let path = path.into();

        let mut file = File::open(&path).with_context(|_| error::Io {
            message: "opening source",
            path: path.clone(),
        })?;
        let mut text = String::new();
        file.read_to_string(&mut text).with_context(|_| error::Io {
            message: "reading source",
            path: path.clone(),
        })?;

        self.ingest(path, &text)?;
        Ok(())
    }

    /// TODO: Documentation
    pub fn ingest<P>(&mut self, path: P, text: &str) -> Result<(), Error>
    where
        P: Into<PathBuf>,
    {
        let mut program = Program::new(Some(Root::new(path.into())?));
        let nodes = self.preprocess(&mut program, &text)?;
        let mut asm = Assembler::new();
        self.run(nodes, &mut asm)?;

        let raw = asm.take();

        self.output.write_all(&raw).context(error::Io {
            message: "writing output",
            path: None,
        })?;

        Ok(())
    }

    /// Assemble instructions from `src` as if they were read from a file located
    /// at `path`.
    fn preprocess(&mut self, program: &mut Program, src: &str) -> Result<Vec<RawOp>, Error> {
        let nodes = parse_asm(&src)?;
        let mut raws = Vec::new();
        for node in nodes {
            match node {
                Node::Op(op) => {
                    raws.push(RawOp::Op(op));
                }
                Node::Raw(raw) => {
                    raws.push(RawOp::Raw(raw));
                }
                Node::Import(imp_path) => {
                    let new_raws = self.resolve_and_ingest(program, imp_path)?;
                    raws.extend(new_raws);
                }
                Node::Include(inc_path) => {
                    let inc_raws = self.resolve_and_ingest(program, inc_path)?;
                    raws.push(RawOp::Scope(inc_raws));
                }
                Node::IncludeHex(hex_path) => {
                    let file =
                        std::fs::read_to_string::<&PathBuf>(&hex_path).with_context(|_| {
                            error::Io {
                                message: "reading hex include",
                                path: <PathBuf as Into<PathBuf>>::into(hex_path.clone()).to_owned(),
                            }
                        })?;

                    let raw = hex::decode(file.trim())
                        .map_err(|e| Box::new(e) as Box<dyn std::error::Error>)
                        .context(error::InvalidHex {
                            path: <PathBuf as Into<PathBuf>>::into(hex_path).to_owned(),
                        })?;

                    raws.push(RawOp::Raw(raw))
                }
            }
        }

        Ok(raws)
    }

    fn resolve_and_ingest<P: AsRef<Path>>(
        &mut self,
        program: &mut Program,
        path: P,
    ) -> Result<Vec<RawOp>, Error>
    where
        P: Into<PathBuf>,
    {
        let path = path.into();
        let oldpath = program.push_path(path.clone())?;
        let code = read_to_string::<&PathBuf>(&path).with_context(|_| error::Io {
            message: "reading file before parsing",
            path: path.to_owned(),
        })?;
        let new_raws = self.preprocess(program, &code)?;
        program.pop_path(oldpath);
        Ok(new_raws)
    }

    fn run(&mut self, ops: Vec<RawOp>, asm: &mut Assembler) -> Result<(), Error> {
        asm.inspect_macros(ops.clone())?;

        for rawop in ops {
            match rawop {
                RawOp::Op(op) => {
                    asm.push(RawOp::Op(op))?;
                }
                RawOp::Scope(scope_ops) => {
                    let mut new_asm = Assembler::new_internal(asm.get_concrete_len());
                    self.run(scope_ops, &mut new_asm)?;
                    let raw = new_asm.take();
                    asm.push(RawOp::Raw(raw))?;
                }
                RawOp::Raw(hex) => {
                    asm.push(RawOp::Raw(hex))?;
                }
            }
        }

        asm.finish()?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use assert_matches::assert_matches;

    use crate::asm::Error as AsmError;

    use hex_literal::hex;

    use std::fmt::Display;
    use std::io::Write;

    use super::*;

    use tempfile::NamedTempFile;

    fn new_file<S: Display>(s: S) -> (NamedTempFile, PathBuf) {
        let mut f = NamedTempFile::new().unwrap();
        let root = f.path().parent().unwrap().join("root.asm");

        write!(f, "{}", s).unwrap();
        (f, root)
    }

    #[test]
    fn ingest_import() -> Result<(), Error> {
        let (f, root) = new_file("push1 42");

        let text = format!(
            r#"
            push1 1
            %import("{}")
            push1 2
        "#,
            f.path().display()
        );

        let mut output = Vec::new();
        let mut ingest = Ingest::new(&mut output);
        ingest.ingest(root, &text)?;
        assert_eq!(output, hex!("6001602a6002"));

        Ok(())
    }

    #[test]
    fn ingest_include() -> Result<(), Error> {
        let (f, root) = new_file(
            r#"
                a:
                jumpdest
                pc
                push1 a
                jump
            "#,
        );

        let text = format!(
            r#"
            push1 1
            %include("{}")
            push1 2
        "#,
            f.path().display()
        );

        let mut output = Vec::new();
        let mut ingest = Ingest::new(&mut output);
        ingest.ingest(root, &text)?;
        assert_eq!(output, hex!("60015b586000566002"));

        Ok(())
    }

    #[test]
    fn ingest_import_twice() {
        let (f, root) = new_file(
            r#"
                a:
                jumpdest
                push1 a
            "#,
        );

        let text = format!(
            r#"
                push1 1
                %import("{0}")
                %import("{0}")
                push1 2
            "#,
            f.path().display()
        );

        let mut output = Vec::new();
        let mut ingest = Ingest::new(&mut output);
        let err = ingest.ingest(root, &text).unwrap_err();

        assert_matches!(
            err,
            Error::Assemble {
                source: AsmError::DuplicateLabel { label, ..}
            } if label == "a"
        );
    }

    #[test]
    fn ingest_include_hex() -> Result<(), Error> {
        let (f, root) = new_file("deadbeef0102f6");

        let text = format!(
            r#"
                push1 1
                %include_hex("{}")
                push1 2
            "#,
            f.path().display(),
        );

        let mut output = Vec::new();
        let mut ingest = Ingest::new(&mut output);
        ingest.ingest(root, &text)?;
        assert_eq!(output, hex!("6001deadbeef0102f66002"));

        Ok(())
    }

    #[test]
    fn ingest_include_hex_label() -> Result<(), Error> {
        let (f, root) = new_file("deadbeef0102f6");

        let text = format!(
            r#"
                push1 1
                %include_hex("{}")
                a:
                jumpdest
                push1 a
                push1 0xff
            "#,
            f.path().display(),
        );

        let mut output = Vec::new();
        let mut ingest = Ingest::new(&mut output);
        ingest.ingest(root, &text)?;
        assert_eq!(output, hex!("6001deadbeef0102f65b600960ff"));

        Ok(())
    }

    #[test]
    fn ingest_pending_then_raw() -> Result<(), Error> {
        let (f, root) = new_file("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");

        let text = format!(
            r#"
                push2 lbl
                %include_hex("{}")
                lbl:
                jumpdest
            "#,
            f.path().display(),
        );

        let mut output = Vec::new();
        let mut ingest = Ingest::new(&mut output);
        ingest.ingest(root, &text)?;

        let expected = hex!("61001caaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa5b");
        assert_eq!(output, expected);

        Ok(())
    }

    #[test]
    fn ingest_import_in_import() -> Result<(), Error> {
        let (end, _) = new_file(
            r#"
                end:
                jumpdest
                push1 start
                push1 middle
            "#,
        );

        let (middle, root) = new_file(format!(
            r#"
                %import("{}")
                middle:
                jumpdest
                push2 start
                push2 end
            "#,
            end.path().display(),
        ));

        let text = format!(
            r#"
                push3 end
                push3 middle
                start:
                jumpdest
                %import("{}")
            "#,
            middle.path().display(),
        );

        let mut output = Vec::new();
        let mut ingest = Ingest::new(&mut output);
        ingest.ingest(root, &text)?;

        let expected = hex!("620000096200000e5b5b6008600e5b610008610009");
        assert_eq!(output, expected);

        Ok(())
    }

    #[test]
    fn ingest_import_in_include() -> Result<(), Error> {
        let (end, _) = new_file(
            r#"
                included:
                jumpdest
                push2 backward
                push2 forward
            "#,
        );

        let (middle, root) = new_file(format!(
            r#"
                pc
                push1 backward
                forward:
                jumpdest
                %import("{}")
                backward:
                jumpdest
                push1 forward
                push1 included
            "#,
            end.path().display(),
        ));

        let text = format!(
            r#"
                push3 backward
                forward:
                jumpdest
                %include("{}")
                backward:
                jumpdest
                push3 forward
            "#,
            middle.path().display(),
        );

        let mut output = Vec::new();
        let mut ingest = Ingest::new(&mut output);
        ingest.ingest(root, &text)?;

        let expected = hex!("620000155b58600b5b5b61000b6100035b600360045b62000004");
        assert_eq!(output, expected);

        Ok(())
    }

    #[test]
    fn ingest_directory_traversal() {
        let (f, _) = new_file("pc");

        let text = format!(
            r#"
                %include("{}")
            "#,
            f.path().display(),
        );

        let mut output = Vec::new();
        let mut ingest = Ingest::new(&mut output);
        let root = std::env::current_exe().unwrap();
        let err = ingest.ingest(root, &text).unwrap_err();

        assert_matches!(err, Error::DirectoryTraversal { .. });
    }

    #[test]
    fn ingest_recursive() {
        let (mut f, root) = new_file("");
        let path = f.path().display().to_string();
        write!(f, r#"%import("{}")"#, path).unwrap();

        let text = format!(
            r#"
                %import("{}")
            "#,
            path,
        );

        let mut output = Vec::new();
        let mut ingest = Ingest::new(&mut output);
        let err = ingest.ingest(root, &text).unwrap_err();

        assert_matches!(err, Error::RecursionLimit { .. });
    }
}
