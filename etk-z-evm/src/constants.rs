use crate::Offset;

use etk_ops::london::{JumpDest, Op, Stop};

use std::collections::BTreeMap;

#[derive(Debug)]
pub struct Constants {
    destinations: BTreeMap<Offset, usize>,
    ops: Vec<Op<[u8]>>,
}

impl Constants {
    pub fn new(ops: Vec<Op<[u8]>>) -> Self {
        let mut offset = Offset(0);
        let mut destinations = BTreeMap::new();

        for (idx, op) in ops.iter().enumerate() {
            if op.code() == Op::JumpDest(JumpDest) {
                destinations.insert(offset, idx);
            }

            offset += op.size().try_into().unwrap();
        }

        Self { ops, destinations }
    }

    pub fn op(&self, index: usize) -> Op<[u8]> {
        self.ops.get(index).unwrap_or(&Op::Stop(Stop)).clone()
    }

    pub fn destination(&self, offset: Offset) -> Option<usize> {
        self.destinations.get(&offset).copied()
    }

    pub fn destinations(&self) -> impl Iterator<Item = (Offset, usize)> + '_ {
        self.destinations.iter().map(|(o, i)| (*o, *i))
    }
}

#[cfg(test)]
mod tests {
    use etk_ops::london::*;

    use super::*;

    #[test]
    fn new() {
        let ops = vec![
            Op::Push32(Push32([0; 32])),
            Op::JumpDest(JumpDest),
            Op::Push2(Push2([0; 2])),
            Op::JumpDest(JumpDest),
        ];

        let constants = Constants::new(ops);

        let dests: Vec<_> = constants.destinations.into_iter().collect();

        assert_eq!(dests, [(Offset(33), 1), (Offset(37), 3)]);
    }
}
