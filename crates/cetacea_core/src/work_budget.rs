//! Aggregate metering for one checker operation, including nested imports.
//! This bounds charged work, not elapsed time or all allocations.
use std::cell::Cell;
use std::marker::PhantomData;
use std::rc::Rc;

const DEFAULT_LIMIT: u64 = 250_000_000;
pub(crate) const EXHAUSTED: &str = "checker resource limit: aggregate work budget exhausted; split the file or simplify expensive computations";

thread_local! {
    static ACTIVE: Cell<Option<u64>> = const { Cell::new(None) };
    static DEPTH: Cell<usize> = const { Cell::new(0) };
}

/// Nested operations share the outer allowance. The guard cannot move to a
/// different thread because its counters belong to the calling thread.
pub(crate) struct Scope(PhantomData<Rc<()>>);

impl Scope {
    pub(crate) fn enter() -> Self {
        Self::with_limit(DEFAULT_LIMIT)
    }

    fn with_limit(limit: u64) -> Self {
        DEPTH.with(|depth| {
            if depth.get() == 0 {
                ACTIVE.with(|remaining| remaining.set(Some(limit)));
            }
            depth.set(depth.get() + 1);
        });
        Self(PhantomData)
    }
}

impl Drop for Scope {
    fn drop(&mut self) {
        DEPTH.with(|depth| {
            depth.set(depth.get() - 1);
            if depth.get() == 0 {
                ACTIVE.with(|remaining| remaining.set(None));
            }
        });
    }
}

pub(crate) fn spend() -> Result<(), &'static str> {
    spend_many(1)
}

pub(crate) fn spend_many(amount: u64) -> Result<(), &'static str> {
    ACTIVE.with(|remaining| match remaining.get() {
        None => Ok(()),
        Some(value) if value < amount => {
            remaining.set(Some(0));
            Err(EXHAUSTED)
        }
        Some(value) => {
            remaining.set(Some(value - amount));
            Ok(())
        }
    })
}

#[cfg(test)]
pub(crate) fn set_remaining_for_test(limit: u64) {
    ACTIVE.with(|remaining| {
        assert!(remaining.get().is_some());
        remaining.set(Some(limit));
    });
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn successive_normalizations_share_one_allowance() {
        use crate::hol::terms::{normalize, CoreTerm, TermContext, TermSignature};
        use crate::hol::types::TypeSignature;
        let types = TypeSignature::default();
        let constants = TermSignature::default();
        let context = TermContext::default();
        {
            let _scope = Scope::with_limit(20);
            let mut successes = 0;
            for _ in 0..30 {
                if normalize(&types, &constants, &context, &CoreTerm::Truth).is_ok() {
                    successes += 1;
                } else {
                    break;
                }
            }
            assert!(successes > 1 && successes < 30);
            let error = normalize(&types, &constants, &context, &CoreTerm::Truth).unwrap_err();
            assert!(error.to_string().contains(EXHAUSTED));
        }
        assert!(normalize(&types, &constants, &context, &CoreTerm::Truth).is_ok());
    }

    #[test]
    fn nested_scopes_cannot_refresh_exhausted_work() {
        {
            let _outer = Scope::with_limit(2);
            spend().unwrap();
            {
                let _inner = Scope::enter();
                spend().unwrap();
                assert_eq!(spend(), Err(EXHAUSTED));
            }
            assert_eq!(spend(), Err(EXHAUSTED));
        }
        let _next = Scope::with_limit(1);
        spend().unwrap();
    }

    #[test]
    fn unwinding_restores_the_next_operation() {
        let _ = std::panic::catch_unwind(|| {
            let _scope = Scope::with_limit(0);
            assert!(spend().is_err());
            panic!("test unwind");
        });
        let _next = Scope::with_limit(1);
        spend().unwrap();
    }
}
