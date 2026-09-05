//! A readable printer for terms and theorems. The elaborator will own the
//! student-facing printer; this one exists for kernel errors and tests.
//!
//! Binders print with their display names, primed when a name would
//! clash with a free variable or an enclosing binder.

use std::collections::BTreeSet;
use std::fmt;

use crate::logic::{AND, EQ, EXISTS, FORALL, IMP, MEM, OR};
use crate::name::{fresh_name, Name};
use crate::term::{Term, TermView};
use crate::thm::Thm;

const PREC_BINDER: u8 = 5;
const PREC_IFF: u8 = 8;
const PREC_IMP: u8 = 10;
const PREC_OR: u8 = 20;
const PREC_AND: u8 = 30;
const PREC_NOT: u8 = 40;
const PREC_EQ: u8 = 50;
const PREC_APP: u8 = 100;

struct Printer<'a> {
    free: &'a BTreeSet<Name>,
    bound: Vec<Name>,
}

impl Printer<'_> {
    fn taken(&self, name: &Name) -> bool {
        self.free.contains(name) || self.bound.contains(name)
    }

    fn term(&mut self, f: &mut fmt::Formatter<'_>, t: &Term, prec: u8) -> fmt::Result {
        if let Some(lam) = quantifier(t, FORALL) {
            return self.binder(f, "forall", lam, prec);
        }
        if let Some(lam) = quantifier(t, EXISTS) {
            return self.binder(f, "exists", lam, prec);
        }
        if let Some(p) = t.dest_not() {
            return paren(f, prec > PREC_NOT, |f| {
                f.write_str("not ")?;
                self.term(f, p, PREC_NOT + 1)
            });
        }
        if let Some((a, b)) = t.dest_iff() {
            return self.infix(f, a, "<->", b, PREC_IFF, PREC_IFF + 1, PREC_IFF + 1, prec);
        }
        if let Some((a, b)) = t.dest_binary(EQ) {
            return self.infix(f, a, "=", b, PREC_EQ, PREC_EQ + 1, PREC_EQ + 1, prec);
        }
        if let Some((a, b)) = t.dest_binary(IMP) {
            return self.infix(f, a, "->", b, PREC_IMP, PREC_IMP + 1, PREC_IMP, prec);
        }
        if let Some((a, b)) = t.dest_binary(OR) {
            return self.infix(f, a, "\\/", b, PREC_OR, PREC_OR + 1, PREC_OR, prec);
        }
        if let Some((a, b)) = t.dest_binary(AND) {
            return self.infix(f, a, "/\\", b, PREC_AND, PREC_AND + 1, PREC_AND, prec);
        }
        if let Some((x, set)) = t.dest_binary(MEM) {
            return self.infix(f, x, "in", set, PREC_EQ, PREC_EQ + 1, PREC_EQ + 1, prec);
        }
        match t.view() {
            TermView::Free(name, _) => write!(f, "{name}"),
            TermView::Const(name, _) => write!(f, "{name}"),
            TermView::Bound(index, _) => {
                let depth = self.bound.len();
                match (index as usize) < depth {
                    true => write!(f, "{}", self.bound[depth - 1 - index as usize]),
                    false => write!(f, "#{index}"),
                }
            }
            TermView::App(func, arg) => paren(f, prec > PREC_APP, |f| {
                self.term(f, func, PREC_APP)?;
                f.write_str(" ")?;
                self.term(f, arg, PREC_APP + 1)
            }),
            TermView::Lam(name, ty, body) => {
                let fresh = fresh_name(name, |candidate| self.taken(candidate));
                paren(f, prec > PREC_BINDER, |f| {
                    write!(f, "fun {fresh} : {ty} => ")?;
                    self.bound.push(fresh.clone());
                    let result = self.term(f, body, PREC_BINDER);
                    self.bound.pop();
                    result
                })
            }
        }
    }

    fn binder(
        &mut self,
        f: &mut fmt::Formatter<'_>,
        keyword: &str,
        lam: &Term,
        prec: u8,
    ) -> fmt::Result {
        let TermView::Lam(name, ty, inner) = lam.view() else {
            unreachable!("quantifier over a lambda");
        };
        let fresh = fresh_name(name, |candidate| self.taken(candidate));
        paren(f, prec > PREC_BINDER, |f| {
            write!(f, "{keyword} {fresh} : {ty}. ")?;
            self.bound.push(fresh.clone());
            let result = self.term(f, inner, PREC_BINDER);
            self.bound.pop();
            result
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn infix(
        &mut self,
        f: &mut fmt::Formatter<'_>,
        a: &Term,
        op: &str,
        b: &Term,
        own: u8,
        left: u8,
        right: u8,
        prec: u8,
    ) -> fmt::Result {
        // A binder in the rightmost position extends as far as possible,
        // so it needs no parentheses.
        let right = if is_binder_form(b) { 0 } else { right };
        paren(f, prec > own, |f| {
            self.term(f, a, left)?;
            write!(f, " {op} ")?;
            self.term(f, b, right)
        })
    }
}

fn is_binder_form(t: &Term) -> bool {
    t.is_lam() || quantifier(t, FORALL).is_some() || quantifier(t, EXISTS).is_some()
}

fn quantifier<'a>(t: &'a Term, name: &str) -> Option<&'a Term> {
    let (head, args) = t.strip_app();
    if args.len() == 1 && head.is_const_named(name) && args[0].is_lam() {
        Some(args[0])
    } else {
        None
    }
}

fn paren(
    f: &mut fmt::Formatter<'_>,
    needed: bool,
    inner: impl FnOnce(&mut fmt::Formatter<'_>) -> fmt::Result,
) -> fmt::Result {
    if needed {
        f.write_str("(")?;
    }
    inner(f)?;
    if needed {
        f.write_str(")")?;
    }
    Ok(())
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let free = self.free_var_names();
        let mut printer = Printer {
            free: &free,
            bound: Vec::new(),
        };
        printer.term(f, self, 0)
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "`{self}`")
    }
}

impl fmt::Display for Thm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (index, hyp) in self.hyps().iter().enumerate() {
            if index > 0 {
                f.write_str(", ")?;
            }
            write!(f, "{hyp}")?;
        }
        if !self.hyps().is_empty() {
            f.write_str(" ")?;
        }
        write!(f, "|- {}", self.concl())?;
        let tags = self.tags();
        if !tags.is_empty() {
            write!(f, " [{tags}]")?;
        }
        Ok(())
    }
}

impl fmt::Debug for Thm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self}")
    }
}
