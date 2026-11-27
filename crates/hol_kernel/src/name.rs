//! Interned-ish names. Cloning a `Name` is a reference-count bump.

use std::fmt;
use std::rc::Rc;

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Name(Rc<str>);

impl Name {
    pub fn new(text: &str) -> Name {
        Name(Rc::from(text))
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }

    /// `x` becomes `x'`, `x'` becomes `x''`, and so on.
    pub fn primed(&self) -> Name {
        Name::new(&format!("{}'", self.0))
    }
}

impl From<&str> for Name {
    fn from(text: &str) -> Name {
        Name::new(text)
    }
}

impl From<&Name> for Name {
    fn from(name: &Name) -> Name {
        name.clone()
    }
}

impl From<String> for Name {
    fn from(text: String) -> Name {
        Name::new(&text)
    }
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl fmt::Debug for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", &*self.0)
    }
}

/// Picks a name based on `base` for which `taken` is false, priming as
/// needed.
pub fn fresh_name(base: &Name, taken: impl Fn(&Name) -> bool) -> Name {
    let mut candidate = base.clone();
    while taken(&candidate) {
        candidate = candidate.primed();
    }
    candidate
}
