//! An optional log of primitive rule applications.
//!
//! The kernel is LCF style: a theorem is a value only the rules can
//! build, and no proof object is kept. For teaching and diagnostics it
//! is still useful to know *which* rules a proof step ran, and where a
//! tag such as `classical` first entered. While recording is switched
//! on for the current thread, every primitive rule is counted in a log.
//!
//! The log is write-only as far as the kernel is concerned. Nothing in
//! this crate reads it, no rule's result depends on it, and a caller
//! cannot use it to construct a [`Thm`]. It is a view of what the
//! kernel did, not evidence the kernel relies on, so it adds nothing to
//! the trusted base beyond these few lines.

use std::cell::RefCell;

use crate::thm::Thm;

/// How many times each primitive rule ran, in order of first use.
///
/// The log keeps counts and nothing else. In particular it holds no
/// terms: a simplification step can apply millions of rules, and a log
/// that kept each conclusion alive would hold every intermediate term of
/// the computation in memory.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RuleCounts(Vec<(&'static str, u64)>);

impl RuleCounts {
    /// Rule names with their counts, in order of first use.
    pub fn iter(&self) -> impl Iterator<Item = (&'static str, u64)> + '_ {
        self.0.iter().copied()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// How many times `rule` ran.
    pub fn count(&self, rule: &str) -> u64 {
        self.0
            .iter()
            .find(|(name, _)| *name == rule)
            .map(|(_, count)| *count)
            .unwrap_or(0)
    }

    fn bump(&mut self, rule: &'static str) {
        match self.0.iter_mut().find(|(name, _)| *name == rule) {
            Some((_, count)) => *count += 1,
            None => self.0.push((rule, 1)),
        }
    }
}

thread_local! {
    static LOG: RefCell<Option<RuleCounts>> = const { RefCell::new(None) };
}

/// Starts a recording on this thread. Returns the enclosing recording,
/// if any, to hand back to [`finish`].
pub fn start() -> Option<RuleCounts> {
    LOG.with(|log| log.borrow_mut().replace(RuleCounts::default()))
}

/// Ends the recording begun by the matching [`start`], restores the
/// enclosing one, and returns what was counted.
pub fn finish(enclosing: Option<RuleCounts>) -> RuleCounts {
    LOG.with(|log| std::mem::replace(&mut *log.borrow_mut(), enclosing))
        .unwrap_or_default()
}

/// True while a recording is active, so callers can skip work that only
/// feeds the log.
pub fn is_recording() -> bool {
    LOG.with(|log| log.borrow().is_some())
}

/// Runs `work` with recording switched off, then resumes. For callers
/// that build reusable machinery (such as a table of rewrite rules)
/// whose construction is not part of the step being recorded.
pub fn paused<T>(work: impl FnOnce() -> T) -> T {
    let held = LOG.with(|log| log.borrow_mut().take());
    let result = work();
    LOG.with(|log| *log.borrow_mut() = held);
    result
}

pub(crate) fn note(rule: &'static str, _thm: &Thm) {
    LOG.with(|log| {
        if let Some(counts) = log.borrow_mut().as_mut() {
            counts.bump(rule);
        }
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rules::{refl, sym, trans};
    use crate::term::Term;
    use crate::types::Type;

    #[test]
    fn rules_are_counted_only_while_recording() {
        let x = Term::free("x", Type::prop());
        refl(&x).unwrap();
        assert!(!is_recording());
        let outer = start();
        assert!(outer.is_none());
        let eq = refl(&x).unwrap();
        let eq = sym(&eq).unwrap();
        // A nested recording sees only its own rules and hands the outer
        // one back untouched.
        let inner = start();
        trans(&eq, &eq).unwrap();
        trans(&eq, &eq).unwrap();
        let nested = finish(inner);
        assert_eq!(nested.iter().collect::<Vec<_>>(), vec![("trans", 2)]);
        // Paused work is not counted.
        paused(|| refl(&x).unwrap());
        let counted = finish(outer);
        assert_eq!(
            counted.iter().collect::<Vec<_>>(),
            vec![("refl", 1), ("sym", 1)]
        );
        assert_eq!(counted.count("refl"), 1);
        assert_eq!(counted.count("imp_intro"), 0);
        assert!(!is_recording());
    }
}
