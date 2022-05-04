use crate::resolve::{resolve, Error};

use std::collections::BTreeMap;
use std::ops::RangeBounds;

use z3::ast::{Ast, Int, BV};
use z3::{SatResult, Solver};

#[derive(Debug, Default, Clone)]
pub struct Memory<'ctx> {
    store: BTreeMap<[u8; 32], BV<'ctx>>,
}

impl<'ctx> Memory<'ctx> {
    fn range(&self, at: &[u8; 32]) -> impl RangeBounds<[u8; 32]> {
        let mut low = *at;
        low[31] &= 0xe0;

        let mut high_hi = u128::from_be_bytes(at[0..16].try_into().unwrap());
        let high_lo = u128::from_be_bytes(at[16..32].try_into().unwrap());

        let (high_lo, overflow) = high_lo.overflowing_add(32);

        if overflow {
            high_hi = high_hi.checked_add(1).unwrap();
        }

        let mut high = [0u8; 32];
        high[0..16].copy_from_slice(&high_hi.to_be_bytes());
        high[16..32].copy_from_slice(&high_lo.to_be_bytes());

        low..high
    }

    fn memory_gas(solver: &Solver<'ctx>, len: &BV<'ctx>) -> Result<Int<'ctx>, Error> {
        let len = resolve(solver, len)?;
        for v in &len[0..24] {
            if *v != 0 {
                todo!("memory length larger than u64::MAX");
            }
        }

        let mut len = u64::from_be_bytes(len[24..].try_into().unwrap());
        len = match len.checked_add(31) {
            Some(l) => l,
            None => todo!("memory length larger than u64::MAX"),
        };

        let n_words = len / 32;
        let linear = n_words * 3;
        let quadradic = (n_words * n_words) / 512;
        let total = quadradic + linear;
        Ok(Int::from_u64(solver.get_context(), total))
    }

    pub fn expansion_gas(
        &self,
        solver: &Solver<'ctx>,
        at: &BV<'ctx>,
        length: &BV<'ctx>,
    ) -> Int<'ctx> {
        let ctx = solver.get_context();

        self.try_expansion_gas(solver, at, length)
            .unwrap_or_else(|_| {
                // TODO: there should be a way to calculate `expansion_gas` without solving,
                //       but until I figure that out, this'll have to do.
                let arb = Int::fresh_const(ctx, "mem-gas");
                solver.assert(&arb.ge(&Int::from_u64(ctx, 0)));
                arb
            })
    }

    pub fn try_expansion_gas(
        &self,
        solver: &Solver<'ctx>,
        at: &BV<'ctx>,
        length: &BV<'ctx>,
    ) -> Result<Int<'ctx>, Error> {
        let ctx = at.get_ctx();
        let before = crate::to_bv(ctx, &self.len());
        let after = at + length;

        Ok(after.bvugt(&before).ite(
            &(Self::memory_gas(solver, &after)? - Self::memory_gas(solver, &before)?),
            &Int::from_u64(ctx, 0),
        ))
    }

    pub fn len(&self) -> [u8; 32] {
        let mut last = match self.store.keys().last() {
            Some(s) => *s,
            None => return [0; 32],
        };

        for v in &last[0..16] {
            if *v != 0 {
                todo!("memory address larger than u128::MAX");
            }
        }

        let mut last_pointer = u128::from_be_bytes(last[16..].try_into().unwrap());

        last_pointer = match last_pointer.checked_add(32) {
            Some(s) => s,
            None => todo!("memory address larger than u128::MAX"),
        };

        last[16..].copy_from_slice(&last_pointer.to_be_bytes());

        last
    }

    pub fn store8(
        &mut self,
        _solver: &Solver<'ctx>,
        _at: &BV<'ctx>,
        _value: &BV<'ctx>,
    ) -> Result<(), Error> {
        todo!()
    }

    pub fn store(
        &mut self,
        solver: &Solver<'ctx>,
        at: &BV<'ctx>,
        value: &BV<'ctx>,
    ) -> Result<(), Error> {
        let at = resolve(solver, at)?;
        let range = self.range(&at);
        let items: Vec<_> = self.store.range_mut(range).collect();

        if at[31] % 32 != 0 || (!items.is_empty() && items.len() != 1) {
            // Only support aligned access for now.
            todo!("store not aligned to word boundary");
        }

        self.store.insert(at, value.clone());

        Ok(())
    }

    pub fn load(&mut self, solver: &Solver<'ctx>, at: &BV<'ctx>) -> Result<BV<'ctx>, Error> {
        let at = resolve(solver, at)?;
        let range = self.range(&at);
        let items: Vec<_> = self.store.range_mut(range).collect();

        if at[31] % 32 != 0 || (!items.is_empty() && items.len() != 1) {
            // Only support aligned access for now.
            todo!("load not aligned to word boundary");
        }

        let r = self
            .store
            .entry(at)
            .or_insert_with(|| BV::from_u64(solver.get_context(), 0, 256))
            .clone();

        Ok(r)
    }

    #[cfg(test)]
    pub fn get(&self, key: &[u8; 32]) -> Option<&BV<'ctx>> {
        self.store.get(key)
    }

    #[cfg(test)]
    pub fn set(&mut self, key: [u8; 32], value: BV<'ctx>) {
        self.store.insert(key, value);
    }
}

#[cfg(test)]
mod tests {
    use crate::to_bv;

    use std::ops::Bound;

    use super::*;

    use z3::{Config, Context};

    #[test]
    fn resolve_constant() {
        let mut cfg = Config::new();
        cfg.set_model_generation(true);

        let ctx = Context::new(&cfg);
        let solver = Solver::new(&ctx);

        let expected = [
            0x12, 0x34, 0x56, 0x78, 0x9a, 0xbc, 0xde, 0xf0, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66,
            0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff, 0x00, 0x23, 0x45, 0x67, 0x89,
            0xab, 0xcd, 0xef, 0xff,
        ];

        let input = to_bv(&ctx, &expected);
        let actual = resolve(&solver, &input).unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn resolve_unrestricted() {
        let mut cfg = Config::new();
        cfg.set_model_generation(true);

        let ctx = Context::new(&cfg);
        let solver = Solver::new(&ctx);

        let input = BV::fresh_const(&ctx, "x", 256);
        let actual = resolve(&solver, &input).unwrap_err();

        assert!(matches!(actual, Error::Ambiguous { .. }));
    }

    #[test]
    fn resolve_two_choices() {
        let mut cfg = Config::new();
        cfg.set_model_generation(true);

        let ctx = Context::new(&cfg);
        let solver = Solver::new(&ctx);

        let input = BV::fresh_const(&ctx, "x", 256);
        solver.assert(&(input._eq(&to_bv(&ctx, &[1])) | input._eq(&to_bv(&ctx, &[2]))));

        let actual = resolve(&solver, &input).unwrap_err();

        assert!(matches!(actual, Error::Ambiguous { .. }));
    }

    #[test]
    fn range_aligned() {
        let mut cfg = Config::new();
        cfg.set_model_generation(true);

        let ctx = Context::new(&cfg);

        let mut mem = Memory::default();

        let zero = BV::fresh_const(&ctx, "zero", 256);
        mem.store.insert([0u8; 32], zero.clone());

        let thirty_two = BV::fresh_const(&ctx, "tt", 256);
        mem.store.insert([32u8; 32], thirty_two.clone());

        let sixty_four = BV::fresh_const(&ctx, "sf", 256);
        mem.store.insert([64u8; 32], sixty_four.clone());

        let mut key = [0u8; 32];
        key[31] = 32;

        let range = mem.range(&key);

        let mut end = [0u8; 32];
        end[31] = 64;
        assert_eq!(range.end_bound(), Bound::Excluded(&end));
        assert_eq!(range.start_bound(), Bound::Included(&key));
    }

    #[test]
    fn range_unaligned() {
        let mut cfg = Config::new();
        cfg.set_model_generation(true);

        let ctx = Context::new(&cfg);

        let mut mem = Memory::default();

        let zero = BV::fresh_const(&ctx, "zero", 256);
        mem.store.insert([0u8; 32], zero.clone());

        let thirty_two = BV::fresh_const(&ctx, "tt", 256);
        mem.store.insert([32u8; 32], thirty_two.clone());

        let sixty_four = BV::fresh_const(&ctx, "sf", 256);
        mem.store.insert([64u8; 32], sixty_four.clone());

        let mut key = [0u8; 32];
        key[31] = 31;

        let range = mem.range(&key);

        let start = [0u8; 32];
        assert_eq!(range.start_bound(), Bound::Included(&start));

        for _ in 0..32 {
            assert!(range.contains(&key));
            key[31] += 1;
        }

        assert!(!range.contains(&key));
    }

    #[test]
    fn aligned_store_load() {
        let mut cfg = Config::new();
        cfg.set_model_generation(true);

        let ctx = Context::new(&cfg);
        let solver = Solver::new(&ctx);

        let mut mem = Memory::default();

        let address = BV::from_u64(&ctx, 64, 256);
        let value = BV::from_u64(&ctx, 42069, 256);

        mem.store(&solver, &address, &value).unwrap();

        let actual = mem.load(&solver, &address).unwrap();

        assert_eq!(value, actual);
    }
}
