# Labels & Pushes

Manually counting out jump destination addresses would be a monumentally pointless task, so the assembler supports assigning names (or _labels_) to specific locations in code:

```rust
# extern crate etk_asm;
# let src = r#"
label0:             # <- This is a label called "label0",
                    #    and it has the value 0, since it is
                    #    before any instructions in scope.

    jumpdest
    push1 label0    # <- Here we push the value of "label0",
                    #    which is zero, onto the stack.

    jump            # Now we jump to zero, which is a
                    # `jumpdest` instruction, looping forever.
# "#;
# let mut ingest = etk_asm::ingest::Ingest::new(Vec::new());
# ingest.ingest(file!(), src).unwrap();
```

## Uses

The obvious (and only, currently) place to use a label is in a push instruction. That said, there are a couple interesting ways to use labels that might not be immediately obvious.

### Jump Address

You can push a label, then jump to it like in the above example.

### Length

That's not all! You can also use labels to calculate lengths:

```rust
# extern crate etk_asm;
# let src = r#"
push1 start
push1 end
sub                 # <- Will leave a 3 on the stack.
stop

start:
    pc
    pc
    pc
end:
# "#;
# let mut ingest = etk_asm::ingest::Ingest::new(Vec::new());
# ingest.ingest(file!(), src).unwrap();
```

Calculating the length of a blob of instructions is _very_ useful in contract initialization code (also known as constructors).
