use crate::Offset;

use etk_asm::ops::ConcreteOp;

use std::collections::BTreeMap;

#[derive(Debug)]
pub struct Constants {
    destinations: BTreeMap<Offset, usize>,
    ops: Vec<ConcreteOp>,
}

impl Constants {
    pub fn new(ops: Vec<ConcreteOp>) -> Self {
        let mut offset = Offset(0);
        let mut destinations = BTreeMap::new();

        for (idx, op) in ops.iter().enumerate() {
            if op == &ConcreteOp::JumpDest {
                destinations.insert(offset, idx);
            }

            offset += op.size();
        }

        Self { ops, destinations }
    }

    pub fn op(&self, index: usize) -> ConcreteOp {
        self.ops.get(index).unwrap_or(&ConcreteOp::Stop).clone()
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
    use super::*;

    #[test]
    fn new() {
        let ops = vec![
            ConcreteOp::Push32([0; 32]),
            ConcreteOp::JumpDest,
            ConcreteOp::Push2([0; 2]),
            ConcreteOp::JumpDest,
        ];

        let constants = Constants::new(ops);

        let dests: Vec<_> = constants.destinations.into_iter().collect();

        assert_eq!(dests, [(Offset(33), 1), (Offset(37), 3)]);
    }
}
