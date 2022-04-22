use z3::ast::BV;

#[derive(Debug)]
pub struct Overflow;

#[derive(Debug)]
pub struct Underflow;

#[derive(Debug, Default, Clone)]
pub struct Stack<'ctx> {
    items: Vec<BV<'ctx>>,
}

impl<'ctx> Stack<'ctx> {
    pub fn is_full(&self) -> bool {
        self.items.len() >= 1024
    }

    pub fn push(&mut self, value: BV<'ctx>) -> Result<(), Overflow> {
        if self.is_full() {
            return Err(Overflow);
        }

        self.items.push(value);

        Ok(())
    }

    pub fn peek(&self, from_top: usize) -> Result<&BV<'ctx>, Underflow> {
        self.items
            .get(self.items.len() - from_top - 1)
            .ok_or(Underflow)
    }

    pub fn pop(&mut self) -> Result<BV<'ctx>, Underflow> {
        let value = self.items.pop().ok_or(Underflow)?;
        Ok(value)
    }

    pub fn swap_n(&mut self, with: usize) -> Result<(), Underflow> {
        if with == 0 || with > 16 {
            panic!("invalid with");
        }

        if self.items.len() <= with {
            return Err(Underflow);
        }

        let end = self.items.len() - 1;
        let with_idx = end - with;

        self.items.swap(end, with_idx);

        Ok(())
    }

    pub fn len(&self) -> usize {
        self.items.len()
    }
}

#[cfg(test)]
mod tests {
    use z3::{Config, Context};

    use super::*;

    #[test]
    fn default() {
        let stack = Stack::default();
        assert_eq!(stack.len(), 0);
    }

    #[test]
    fn push_pop() {
        let cfg = Config::default();
        let ctx = Context::new(&cfg);
        let mut stack = Stack::default();
        stack.push(BV::from_u64(&ctx, 1234, 256)).unwrap();

        assert_eq!(stack.len(), 1);

        let value = stack.pop().unwrap();

        assert_eq!(stack.len(), 0);
        assert_eq!(BV::from_u64(&ctx, 1234, 256), value);
    }

    #[test]
    fn pop_underflow() {
        let mut stack = Stack::default();
        stack.pop().unwrap_err();
    }

    #[test]
    fn push_overflow() {
        let cfg = Config::default();
        let ctx = Context::new(&cfg);
        let mut stack = Stack::default();
        while stack.len() < 1024 {
            stack.push(BV::from_u64(&ctx, 1234, 256)).unwrap();
        }

        stack.push(BV::from_u64(&ctx, 0, 256)).unwrap_err();
    }

    #[test]
    fn swap() {
        let cfg = Config::default();
        let ctx = Context::new(&cfg);
        let mut stack = Stack::default();
        stack.push(BV::from_u64(&ctx, 1, 256)).unwrap();
        stack.push(BV::from_u64(&ctx, 2, 256)).unwrap();
        stack.swap_n(1).unwrap();

        let value = stack.pop().unwrap();

        assert_eq!(stack.len(), 1);
        assert_eq!(BV::from_u64(&ctx, 1, 256), value);

        let value = stack.pop().unwrap();

        assert_eq!(stack.len(), 0);
        assert_eq!(BV::from_u64(&ctx, 2, 256), value);
    }

    #[test]
    fn swap_n() {
        let cfg = Config::default();
        let ctx = Context::new(&cfg);

        for swap in 1..17 {
            let mut stack = Stack::default();

            for idx in 0..17 {
                stack.push(BV::from_u64(&ctx, idx, 256)).unwrap();
            }

            let last = stack.items.last().cloned().unwrap();
            let mid = stack.items[stack.len() - swap - 1].clone();

            stack.swap_n(swap).unwrap();

            assert_eq!(stack.items.last().unwrap(), &mid);
            assert_eq!(stack.items[stack.len() - swap - 1], last);
        }
    }
}
