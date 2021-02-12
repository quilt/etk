use gencfg_asm::disasm::Offset;
use gencfg_asm::ops::Op;

#[derive(Debug, Eq, PartialEq)]
pub struct BasicBlock {
    pub offset: usize,
    pub ops: Vec<Op>,
}

#[derive(Debug, Default)]
pub struct Separator {
    complete_blocks: Vec<BasicBlock>,
    in_progress: Option<BasicBlock>,
}

impl Separator {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn push_all<I>(&mut self, iter: I) -> bool
    where
        I: IntoIterator<Item = Offset<Op>>,
    {
        let mut available = false;
        for item in iter.into_iter() {
            available |= self.push(item);
        }
        available
    }

    pub fn push(&mut self, off: Offset<Op>) -> bool {
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

    pub fn take(&mut self) -> Vec<BasicBlock> {
        std::mem::take(&mut self.complete_blocks)
    }

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
            Offset::new(0x00, Op::Push1(5.into())),
            Offset::new(0x02, Op::Push1(6.into())),
            Offset::new(0x04, Op::Push1(7.into())),
        ];

        let blocks = [];

        let last = Some(BasicBlock {
            offset: 0x00,
            ops: vec![
                Op::Push1(5.into()),
                Op::Push1(6.into()),
                Op::Push1(7.into()),
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
            Offset::new(0x00, Op::JumpDest(None)),
            Offset::new(0x01, Op::JumpDest(None)),
            Offset::new(0x02, Op::JumpDest(None)),
        ];

        let blocks = [
            BasicBlock {
                offset: 0x00,
                ops: vec![Op::JumpDest(None)],
            },
            BasicBlock {
                offset: 0x01,
                ops: vec![Op::JumpDest(None)],
            },
        ];

        let last = Some(BasicBlock {
            offset: 0x02,
            ops: vec![Op::JumpDest(None)],
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
            Offset::new(0x00, Op::JumpDest(None)),
            Offset::new(0x01, Op::Jump),
            Offset::new(0x02, Op::JumpDest(None)),
            Offset::new(0x03, Op::Jump),
        ];

        let blocks = [
            BasicBlock {
                offset: 0x00,
                ops: vec![Op::JumpDest(None), Op::Jump],
            },
            BasicBlock {
                offset: 0x02,
                ops: vec![Op::JumpDest(None), Op::Jump],
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
            Offset::new(0x00, Op::Jump),
            Offset::new(0x01, Op::JumpDest(None)),
            Offset::new(0x02, Op::Jump),
            Offset::new(0x03, Op::JumpDest(None)),
        ];

        let blocks = [
            BasicBlock {
                offset: 0x00,
                ops: vec![Op::Jump],
            },
            BasicBlock {
                offset: 0x01,
                ops: vec![Op::JumpDest(None), Op::Jump],
            },
        ];

        let last = Some(BasicBlock {
            offset: 0x03,
            ops: vec![Op::JumpDest(None)],
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
            Offset::new(0x00, Op::Jump),
            Offset::new(0x01, Op::Jump),
            Offset::new(0x02, Op::Jump),
        ];

        let blocks = [
            BasicBlock {
                offset: 0x00,
                ops: vec![Op::Jump],
            },
            BasicBlock {
                offset: 0x01,
                ops: vec![Op::Jump],
            },
            BasicBlock {
                offset: 0x02,
                ops: vec![Op::Jump],
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
