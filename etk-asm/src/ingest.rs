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
    #[snafu(visibility = "pub(super)")]
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

fn parse_file<P: AsRef<Path>>(path: P) -> Result<Vec<Node>, Error> {
    let asm = read_to_string(path.as_ref()).with_context(|| error::Io {
        message: "reading file before parsing",
        path: path.as_ref().to_owned(),
    })?;
    let nodes = parse_asm(&asm)?;

    Ok(nodes)
}

#[derive(Debug)]
enum Scope {
    Same,
    Independent(Box<Assembler>),
}

impl Scope {
    fn same() -> Self {
        Self::Same
    }

    fn independent() -> Self {
        Self::Independent(Box::new(Assembler::new()))
    }
}

#[derive(Debug)]
struct Source {
    path: PathBuf,
    nodes: std::vec::IntoIter<Node>,
    scope: Scope,
}

#[derive(Debug)]
struct Root {
    original: PathBuf,
    canonicalized: PathBuf,
}

impl Root {
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

        let metadata = file.metadata().with_context(|| error::Io {
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

        let canonicalized = std::fs::canonicalize(&file).with_context(|| error::Io {
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

        let canonicalized = std::fs::canonicalize(path).with_context(|| error::Io {
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

#[must_use]
struct PartialSource<'a, W> {
    stack: &'a mut SourceStack<W>,
    path: PathBuf,
    scope: Scope,
}

impl<'a, W> PartialSource<'a, W> {
    fn path(&self) -> &Path {
        &self.path
    }

    fn push(self, nodes: Vec<Node>) -> &'a mut Source {
        self.stack.sources.push(Source {
            path: self.path,
            nodes: nodes.into_iter(),
            scope: self.scope,
        });

        self.stack.sources.last_mut().unwrap()
    }
}

#[derive(Debug)]
struct SourceStack<W> {
    output: W,
    sources: Vec<Source>,
    root: Option<Root>,
}

impl<W> SourceStack<W> {
    fn new(output: W) -> Self {
        Self {
            output,
            sources: Default::default(),
            root: Default::default(),
        }
    }

    fn resolve(&mut self, path: PathBuf, scope: Scope) -> Result<PartialSource<W>, Error> {
        ensure!(self.sources.len() <= 255, error::RecursionLimit);

        let path = if let Some(ref root) = self.root {
            let last = self.sources.last().unwrap();
            let dir = match last.path.parent() {
                Some(s) => s,
                None => Path::new("./"),
            };
            let candidate = dir.join(path);
            root.check(&candidate)?;
            candidate
        } else {
            assert!(self.sources.is_empty());
            self.root = Some(Root::new(path.clone())?);
            path
        };

        Ok(PartialSource {
            stack: self,
            path,
            scope,
        })
    }

    fn peek(&mut self) -> Option<&mut Source> {
        self.sources.last_mut()
    }
}

impl<W> SourceStack<W>
where
    W: Write,
{
    fn pop(&mut self) -> Result<(), Error> {
        let popped = self.sources.pop().unwrap();

        if self.sources.is_empty() {
            self.root = None;
        }

        let mut asm = match popped.scope {
            Scope::Independent(a) => a,
            Scope::Same => return Ok(()),
        };

        let raw = asm.take();
        asm.finish()?;

        if raw.is_empty() {
            return Ok(());
        }

        if self.sources.is_empty() {
            self.output.write_all(&raw).context(error::Io {
                message: "writing output",
                path: None,
            })?;
            Ok(())
        } else {
            self.write(RawOp::Raw(raw))
        }
    }

    fn write(&mut self, mut op: RawOp) -> Result<(), Error> {
        if self.sources.is_empty() {
            panic!("no sources!");
        }

        for frame in self.sources[1..].iter_mut().rev() {
            let asm = match frame.scope {
                Scope::Same => continue,
                Scope::Independent(ref mut a) => a,
            };

            if 0 == asm.push(op)? {
                return Ok(());
            } else {
                op = RawOp::Raw(asm.take());
            }
        }

        let first_asm = match self.sources[0].scope {
            Scope::Independent(ref mut a) => a,
            Scope::Same => panic!("sources[0] must be independent"),
        };

        first_asm.push(op)?;

        Ok(())
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
    sources: SourceStack<W>,
}

impl<W> Ingest<W> {
    /// Make a new `Ingest` that writes assembled bytes to `output`.
    pub fn new(output: W) -> Self {
        Self {
            sources: SourceStack::new(output),
        }
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

        let mut file = File::open(&path).with_context(|| error::Io {
            message: "opening source",
            path: path.clone(),
        })?;
        let mut text = String::new();
        file.read_to_string(&mut text).with_context(|| error::Io {
            message: "reading source",
            path: path.clone(),
        })?;

        self.ingest(path, &text)
    }

    /// Assemble instructions from `src` as if they were read from a file located
    /// at `path`.
    pub fn ingest<P>(&mut self, path: P, src: &str) -> Result<(), Error>
    where
        P: Into<PathBuf>,
    {
        let nodes = parse_asm(src)?;
        let partial = self.sources.resolve(path.into(), Scope::independent())?;
        partial.push(nodes);

        while let Some(source) = self.sources.peek() {
            let node = match source.nodes.next() {
                Some(n) => n,
                None => {
                    self.sources.pop()?;
                    continue;
                }
            };

            match node {
                Node::Op(op) => {
                    self.sources.write(RawOp::Op(op))?;
                }
                Node::Raw(raw) => {
                    self.sources.write(RawOp::Raw(raw))?;
                }
                Node::Import(path) => {
                    let partial = self.sources.resolve(path, Scope::same())?;
                    let parsed = parse_file(partial.path())?;
                    partial.push(parsed);
                }
                Node::Include(path) => {
                    let partial = self.sources.resolve(path, Scope::independent())?;
                    let parsed = parse_file(partial.path())?;
                    partial.push(parsed);
                }
                Node::IncludeHex(path) => {
                    let partial = self.sources.resolve(path, Scope::same())?;

                    let file =
                        std::fs::read_to_string(partial.path()).with_context(|| error::Io {
                            message: "reading hex include",
                            path: partial.path().to_owned(),
                        })?;

                    let raw = hex::decode(file.trim())
                        .map_err(|e| Box::new(e) as Box<dyn std::error::Error>)
                        .context(error::InvalidHex {
                            path: partial.path().to_owned(),
                        })?;

                    partial.push(vec![Node::Raw(raw)]);
                }
            }
        }

        if !self.sources.sources.is_empty() {
            panic!("extra sources?");
        }

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
