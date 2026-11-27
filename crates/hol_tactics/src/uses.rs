//! A record of which named theorems a proof cited.
//!
//! Course policies restrict the library theorems a section may use, so
//! the session needs to know what a script actually resolved, including
//! in a proof that later failed. Every place a proof expression resolves
//! a name to a theorem reports it here. Hypotheses that shadow a theorem
//! name are not reported, which a purely syntactic scan could not tell.
//!
//! This log is bookkeeping for feedback and grading policy. It is not
//! part of the trusted base: soundness never depends on it.

use std::cell::RefCell;

use hol_kernel::Name;
use hol_syntax::Span;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TheoremUse {
    /// The theorem's full name in the environment.
    pub name: Name,
    /// Where the script cited it.
    pub span: Span,
    /// True for a theorem that came from an imported file.
    pub is_imported: bool,
}

thread_local! {
    static LOG: RefCell<Option<Vec<TheoremUse>>> = const { RefCell::new(None) };
}

/// Starts recording on this thread, returning whatever an enclosing
/// recording had gathered so the caller can restore it with [`finish`].
pub fn start() -> Option<Vec<TheoremUse>> {
    LOG.with(|log| log.borrow_mut().replace(Vec::new()))
}

/// Stops recording, restores the enclosing recording, and returns the
/// uses gathered since the matching [`start`].
pub fn finish(enclosing: Option<Vec<TheoremUse>>) -> Vec<TheoremUse> {
    LOG.with(|log| std::mem::replace(&mut *log.borrow_mut(), enclosing))
        .unwrap_or_default()
}

pub(crate) fn record(name: &Name, span: Span, is_imported: bool) {
    LOG.with(|log| {
        if let Some(uses) = log.borrow_mut().as_mut() {
            uses.push(TheoremUse {
                name: name.clone(),
                span,
                is_imported,
            });
        }
    });
}
