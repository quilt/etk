//! A list of EVM instructions with a single point of entry and a single exit.
use etk_asm::disasm::Offset;
use etk_asm::ops::{ConcreteOp, Metadata};

use std::convert::TryInto;

/// A list of EVM instructions with a single point of entry and a single exit.
#[derive(Debug, Eq, PartialEq)]
pub struct BasicBlock {
    /// Position of the first instruction of this block in the entire program.
    pub offset: usize,

    /// List of instructions contained in the block.
    pub ops: Vec<ConcreteOp>,
}

impl BasicBlock {
    /// Sum of the length of every instruction in this block.
    pub fn size(&self) -> usize {
        let sum: u32 = self.ops.iter().map(ConcreteOp::size).sum();
        sum.try_into().unwrap()
    }
}

/// Separate a sequence of [`ConcreteOp`] into [`BasicBlock`].
#[derive(Debug, Default)]
pub struct Separator {
    complete_blocks: Vec<BasicBlock>,
    in_progress: Option<BasicBlock>,
}

impl Separator {
    /// Create a default instance.
    pub fn new() -> Self {
        Self::default()
    }

    /// Read instructions from `iter` until it is empty.
    ///
    /// Returns `true` if any [`BasicBlock`] are ready.
    pub fn push_all<I>(&mut self, iter: I) -> bool
    where
        I: IntoIterator<Item = Offset<ConcreteOp>>,
    {
        let mut available = false;
        for item in iter.into_iter() {
            available |= self.push(item);
        }
        available
    }

    /// Push a single instruction, returns `true` if a [`BasicBlock`] has been
    /// completed.
    pub fn push(&mut self, off: Offset<ConcreteOp>) -> bool {
        if off.item.is_jump_target() {
            // If we receive a jumpdest, start a new block beginning with it.
            let completed = self.in_progress.replace(BasicBlock {
                offset: off.offset,
                ops: vec![off.item],
            });

            if let Some(completed_block) = completed {
                self.complete_blocks.push(completed_block);
                return true;
            } else {
                return false;
            }
        }

        let is_jump = off.item.is_jump() | off.item.is_exit();

        // Append to in-progress block, or start a new block.
        match self.in_progress {
            Some(ref mut p) => p.ops.push(off.item),
            None => {
                self.in_progress = Some(BasicBlock {
                    offset: off.offset,
                    ops: vec![off.item],
                });
            }
        }

        // If we pushed a jump, end the basic block.
        if is_jump {
            let in_progress = self.in_progress.take().unwrap();
            self.complete_blocks.push(in_progress);
            true
        } else {
            false
        }
    }

    /// Remove all completed [`BasicBlock`].
    pub fn take(&mut self) -> Vec<BasicBlock> {
        std::mem::take(&mut self.complete_blocks)
    }

    /// Retrieve the last [`BasicBlock`] after all instructions have been
    /// consumed.
    #[must_use]
    pub fn finish(&mut self) -> Option<BasicBlock> {
        if self.complete_blocks.is_empty() {
            self.in_progress.take()
        } else {
            panic!("not all basic blocks have been taken");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn three_pushes() {
        let ops = vec![
            Offset::new(0x00, ConcreteOp::Push1([5])),
            Offset::new(0x02, ConcreteOp::Push1([6])),
            Offset::new(0x04, ConcreteOp::Push1([7])),
        ];

        let blocks = [];

        let last = Some(BasicBlock {
            offset: 0x00,
            ops: vec![
                ConcreteOp::Push1([5]),
                ConcreteOp::Push1([6]),
                ConcreteOp::Push1([7]),
            ],
        });

        let mut sep = Separator::new();
        let completed = sep.push_all(ops.into_iter());
        assert!(!completed);
        assert_eq!(sep.take(), blocks);
        assert_eq!(sep.finish(), last);
    }

    #[test]
    fn three_jumpdests() {
        let ops = vec![
            Offset::new(0x00, ConcreteOp::JumpDest),
            Offset::new(0x01, ConcreteOp::JumpDest),
            Offset::new(0x02, ConcreteOp::JumpDest),
        ];

        let blocks = [
            BasicBlock {
                offset: 0x00,
                ops: vec![ConcreteOp::JumpDest],
            },
            BasicBlock {
                offset: 0x01,
                ops: vec![ConcreteOp::JumpDest],
            },
        ];

        let last = Some(BasicBlock {
            offset: 0x02,
            ops: vec![ConcreteOp::JumpDest],
        });

        let mut sep = Separator::new();
        let completed = sep.push_all(ops.into_iter());
        assert!(completed);
        assert_eq!(sep.take(), blocks);
        assert_eq!(sep.finish(), last);
    }

    #[test]
    fn jumpdest_jump_jumpdest_jump() {
        let ops = vec![
            Offset::new(0x00, ConcreteOp::JumpDest),
            Offset::new(0x01, ConcreteOp::Jump),
            Offset::new(0x02, ConcreteOp::JumpDest),
            Offset::new(0x03, ConcreteOp::Jump),
        ];

        let blocks = [
            BasicBlock {
                offset: 0x00,
                ops: vec![ConcreteOp::JumpDest, ConcreteOp::Jump],
            },
            BasicBlock {
                offset: 0x02,
                ops: vec![ConcreteOp::JumpDest, ConcreteOp::Jump],
            },
        ];

        let last = None;

        let mut sep = Separator::new();
        let completed = sep.push_all(ops.into_iter());
        assert!(completed);
        assert_eq!(sep.take(), blocks);
        assert_eq!(sep.finish(), last);
    }

    #[test]
    fn jump_jumpdest_jump_jumpdest() {
        let ops = vec![
            Offset::new(0x00, ConcreteOp::Jump),
            Offset::new(0x01, ConcreteOp::JumpDest),
            Offset::new(0x02, ConcreteOp::Jump),
            Offset::new(0x03, ConcreteOp::JumpDest),
        ];

        let blocks = [
            BasicBlock {
                offset: 0x00,
                ops: vec![ConcreteOp::Jump],
            },
            BasicBlock {
                offset: 0x01,
                ops: vec![ConcreteOp::JumpDest, ConcreteOp::Jump],
            },
        ];

        let last = Some(BasicBlock {
            offset: 0x03,
            ops: vec![ConcreteOp::JumpDest],
        });

        let mut sep = Separator::new();
        let completed = sep.push_all(ops.into_iter());
        assert!(completed);
        assert_eq!(sep.take(), blocks);
        assert_eq!(sep.finish(), last);
    }

    #[test]
    fn three_jumps() {
        let ops = vec![
            Offset::new(0x00, ConcreteOp::Jump),
            Offset::new(0x01, ConcreteOp::Jump),
            Offset::new(0x02, ConcreteOp::Jump),
        ];

        let blocks = [
            BasicBlock {
                offset: 0x00,
                ops: vec![ConcreteOp::Jump],
            },
            BasicBlock {
                offset: 0x01,
                ops: vec![ConcreteOp::Jump],
            },
            BasicBlock {
                offset: 0x02,
                ops: vec![ConcreteOp::Jump],
            },
        ];

        let last = None;

        let mut sep = Separator::new();
        let completed = sep.push_all(ops.into_iter());
        assert!(completed);
        assert_eq!(sep.take(), blocks);
        assert_eq!(sep.finish(), last);
    }
}
