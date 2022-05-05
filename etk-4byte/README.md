etk-4byte
=========

Ethereum function selector reverse lookup database, populated from [4byte.directory](https://www.4byte.directory/).

## Updating the Database

Since `etk-4byte` is a purely offline database, it needs regular updates. To fetch the latest database and convert it to the expected format, run:

```bash
$ cargo run --features=generate --bin etk-4byte-generate > src/signatures.txt
$ cargo run --features=generate --bin etk-4byte-phf
```

Then recompile.
