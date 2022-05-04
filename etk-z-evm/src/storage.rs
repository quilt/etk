use std::cell::RefCell;
use std::collections::BTreeMap;
use std::rc::Rc;

use z3::ast::BV;
use z3::{Context, Solver};

use crate::resolve::resolve;

#[derive(Debug, Copy, Clone)]
pub struct Key<'a, 'ctx> {
    solver: &'a Solver<'ctx>,
    address: &'a BV<'ctx>,
    slot: &'a BV<'ctx>,
}

impl<'a, 'ctx> Key<'a, 'ctx> {
    pub(crate) fn new(solver: &'a Solver<'ctx>, address: &'a BV<'ctx>, slot: &'a BV<'ctx>) -> Self {
        Self {
            solver,
            address,
            slot,
        }
    }

    pub fn solver(&self) -> &'a Solver<'ctx> {
        self.solver
    }

    pub fn context(&self) -> &'ctx Context {
        self.solver.get_context()
    }

    pub fn address(&self) -> &'a BV<'ctx> {
        self.address
    }

    pub fn slot(&self) -> &'a BV<'ctx> {
        self.slot
    }
}

pub trait Storage<'ctx> {
    type Error: 'static + snafu::Error;

    fn get(&self, key: Key<'_, 'ctx>) -> Result<BV<'ctx>, Self::Error>;
    fn set(&mut self, key: Key<'_, 'ctx>, value: &BV<'ctx>) -> Result<BV<'ctx>, Self::Error>;
    fn original(&self, key: Key<'_, 'ctx>) -> Result<BV<'ctx>, Self::Error>;
}

#[derive(Debug, Default)]
pub struct InMemory<'ctx> {
    accounts: BTreeMap<[u8; 20], BTreeMap<[u8; 32], BV<'ctx>>>,
}

impl<'ctx> InMemory<'ctx> {
    fn account(
        &self,
        key: Key<'_, 'ctx>,
    ) -> Result<Option<&BTreeMap<[u8; 32], BV<'ctx>>>, crate::resolve::Error> {
        let long_address = resolve(key.solver(), key.address())?;
        let truncated: [u8; 20] = long_address[12..].try_into().unwrap();
        Ok(self.accounts.get(&truncated))
    }

    fn account_mut(
        &mut self,
        key: Key<'_, 'ctx>,
    ) -> Result<&mut BTreeMap<[u8; 32], BV<'ctx>>, crate::resolve::Error> {
        let long_address = resolve(key.solver(), key.address())?;
        let truncated: [u8; 20] = long_address[12..].try_into().unwrap();
        Ok(self.accounts.entry(truncated).or_default())
    }
}

impl<'ctx> Storage<'ctx> for InMemory<'ctx> {
    type Error = crate::resolve::Error;

    fn set(&mut self, key: Key<'_, 'ctx>, value: &BV<'ctx>) -> Result<BV<'ctx>, Self::Error> {
        let account = self.account_mut(key)?;
        let slot = resolve(key.solver(), key.slot())?;

        let old = account
            .insert(slot, value.clone())
            .unwrap_or_else(|| BV::from_u64(key.context(), 0, 256));

        Ok(old)
    }

    fn get(&self, key: Key<'_, 'ctx>) -> Result<BV<'ctx>, Self::Error> {
        let zero = BV::from_u64(key.context(), 0, 256);

        let account = match self.account(key)? {
            Some(a) => a,
            None => return Ok(zero),
        };

        let slot = resolve(key.solver(), key.slot())?;

        let old = account.get(&slot).cloned().unwrap_or(zero);

        Ok(old)
    }

    fn original(&self, key: Key<'_, 'ctx>) -> Result<BV<'ctx>, Self::Error> {
        Ok(BV::from_u64(key.context(), 0, 256))
    }
}

#[derive(Debug, Clone)]
struct Change<'ctx> {
    address: BV<'ctx>,
    slot: BV<'ctx>,
    previous_value: BV<'ctx>,
}

#[derive(Debug)]
#[must_use]
pub(crate) struct Delta<'ctx, S> {
    storage: Rc<RefCell<S>>,
    change: Option<Change<'ctx>>,
}

impl<'ctx, S> Delta<'ctx, S> {
    pub fn new(storage: S) -> Self {
        Self {
            storage: Rc::new(RefCell::new(storage)),
            change: None,
        }
    }

    pub fn reset(&mut self) {
        self.change = None;
    }
}

impl<'ctx, S> Storage<'ctx> for Delta<'ctx, S>
where
    S: Storage<'ctx>,
{
    type Error = S::Error;

    fn get(&self, key: Key<'_, 'ctx>) -> Result<BV<'ctx>, Self::Error> {
        self.storage.borrow().get(key)
    }

    fn original(&self, key: Key<'_, 'ctx>) -> Result<BV<'ctx>, Self::Error> {
        self.storage.borrow().original(key)
    }

    fn set(&mut self, key: Key<'_, 'ctx>, value: &BV<'ctx>) -> Result<BV<'ctx>, Self::Error> {
        let previous_value = self.storage.borrow_mut().set(key, value)?;
        self.change = Some(Change {
            previous_value: previous_value.clone(),
            address: key.address().clone(),
            slot: key.slot().clone(),
        });
        Ok(previous_value)
    }
}

impl<'ctx, S> Clone for Delta<'ctx, S> {
    fn clone(&self) -> Self {
        Self {
            storage: self.storage.clone(),
            change: self.change.clone(),
        }
    }
}

impl<'ctx, S> Delta<'ctx, S>
where
    S: Storage<'ctx>,
{
    pub fn get(
        &self,
        solver: &Solver<'ctx>,
        address: &BV<'ctx>,
        slot: &BV<'ctx>,
    ) -> Result<BV<'ctx>, S::Error> {
        let key = Key {
            address,
            slot,
            solver,
        };
        self.storage.borrow_mut().get(key)
    }

    pub fn undo(&self, solver: &Solver<'ctx>) -> Result<(), S::Error> {
        if let Some(ref change) = self.change {
            let key = Key {
                address: &change.address,
                slot: &change.slot,
                solver,
            };
            self.storage.borrow_mut().set(key, &change.previous_value)?;
        }

        Ok(())
    }
}
