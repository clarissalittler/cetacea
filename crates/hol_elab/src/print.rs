//! Printing kernel terms back in surface syntax: `f(x, y)`, `x in A`,
//! `forall x y : T, P(x)`, `{ x : T | P }`, decimal numerals, and folded
//! definitions.

use std::collections::BTreeSet;

use hol_kernel::{fresh_name, Name, Term, TermView, Type, EXISTS, FORALL, SET_OF};

use crate::env::Env;

const PREC_IMP: u8 = 10;
const PREC_IFF: u8 = 20;
const PREC_OR: u8 = 30;
const PREC_AND: u8 = 40;
const PREC_NOT: u8 = 50;
const PREC_REL: u8 = 60;
const PREC_ADD: u8 = 70;
const PREC_MUL: u8 = 80;
const PREC_APP: u8 = 100;
const PREC_BINDER: u8 = 5;

pub fn print_term(env: &Env, term: &Term) -> String {
    let free = term.free_var_names();
    let mut printer = Printer {
        _env: env,
        free: &free,
        bound: Vec::new(),
        out: String::new(),
    };
    printer.term(term, 0);
    printer.out
}

pub fn print_type(ty: &Type) -> String {
    ty.to_string()
}

struct Printer<'a> {
    _env: &'a Env,
    free: &'a BTreeSet<Name>,
    bound: Vec<Name>,
    out: String,
}

fn infix_symbol(name: &str, ty: &Type) -> Option<(&'static str, u8, bool)> {
    // (symbol, precedence, right associative)
    Some(match name {
        // Conjunction and disjunction parse right-associatively but print
        // nested groups with explicit parentheses, as textbooks do.
        "and" => ("/\\", PREC_AND, false),
        "or" => ("\\/", PREC_OR, false),
        "imp" => ("->", PREC_IMP, true),
        "eq" => {
            let is_prop = ty.as_fun().map(|(dom, _)| dom.is_prop()).unwrap_or(false);
            if is_prop {
                ("<->", PREC_IFF, true)
            } else {
                ("=", PREC_REL, false)
            }
        }
        "mem" => ("in", PREC_REL, false),
        "subset" => ("subset", PREC_REL, false),
        "add" => ("+", PREC_ADD, false),
        "sub" => ("-", PREC_ADD, false),
        "mul" => ("*", PREC_MUL, false),
        "le" => ("<=", PREC_REL, false),
        "lt" => ("<", PREC_REL, false),
        _ => return None,
    })
}

impl Printer<'_> {
    fn taken(&self, name: &Name) -> bool {
        self.free.contains(name) || self.bound.contains(name)
    }

    fn paren(&mut self, needed: bool, inner: impl FnOnce(&mut Self)) {
        if needed {
            self.out.push('(');
        }
        inner(self);
        if needed {
            self.out.push(')');
        }
    }

    fn numeral(&self, term: &Term) -> Option<u64> {
        let mut count = 0u64;
        let mut current = term;
        loop {
            match current.view() {
                TermView::Const(name, _) if name.as_str() == "zero" => return Some(count),
                TermView::App(f, x) if f.is_const_named("succ") => {
                    count += 1;
                    current = x;
                }
                _ => return None,
            }
        }
    }

    fn term(&mut self, t: &Term, prec: u8) {
        if let Some(n) = self.numeral(t) {
            self.out.push_str(&n.to_string());
            return;
        }
        if let Some(lam) = t.dest_forall() {
            return self.quantifier("forall", FORALL, lam, prec);
        }
        if let Some(lam) = t.dest_exists() {
            return self.quantifier("exists", EXISTS, lam, prec);
        }
        if let Some(p) = t.dest_not() {
            return self.paren(prec > PREC_NOT, |p_| {
                p_.out.push_str("not ");
                p_.term(p, PREC_NOT);
            });
        }
        let (head, args) = t.strip_app();
        if let Some((name, ty)) = head.as_const() {
            if args.len() == 2 {
                if let Some((symbol, own, right_assoc)) = infix_symbol(name.as_str(), ty) {
                    let (left_prec, right_prec) = if right_assoc {
                        (own + 1, own)
                    } else {
                        (own + 1, own + 1)
                    };
                    let right_is_binder = is_binder_form(args[1]);
                    return self.paren(prec > own, |p| {
                        p.term(args[0], left_prec);
                        p.out.push(' ');
                        p.out.push_str(symbol);
                        p.out.push(' ');
                        p.term(args[1], if right_is_binder { 0 } else { right_prec });
                    });
                }
            }
            if name.as_str() == SET_OF && args.len() == 1 && args[0].is_lam() {
                return self.set_builder(args[0]);
            }
            if (name.as_str() == "empty" || name.as_str() == "univ") && args.is_empty() {
                if let Type::Con(_, targs) = ty {
                    if targs.len() == 1 {
                        self.out.push_str(&format!("{name}({})", targs[0]));
                        return;
                    }
                }
            }
            if args.is_empty() {
                self.out.push_str(name.as_str());
                return;
            }
            return self.application(name.as_str(), &args, prec);
        }
        match t.view() {
            TermView::Free(name, _) => {
                if args.is_empty() {
                    self.out.push_str(name.as_str());
                } else {
                    let name = name.to_string();
                    self.application(&name, &args, prec);
                }
            }
            TermView::Bound(index, _) => {
                let depth = self.bound.len();
                let name = if (index as usize) < depth {
                    self.bound[depth - 1 - index as usize].to_string()
                } else {
                    format!("#{index}")
                };
                if args.is_empty() {
                    self.out.push_str(&name);
                } else {
                    self.application(&name, &args, prec);
                }
            }
            TermView::Const(..) => unreachable!("handled above"),
            TermView::App(..) => {
                // Head is a lambda or another application: print curried.
                self.paren(prec > PREC_APP, |p| {
                    p.term(head, PREC_APP + 1);
                    p.out.push('(');
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 {
                            p.out.push_str(", ");
                        }
                        p.term(arg, 0);
                    }
                    p.out.push(')');
                });
            }
            TermView::Lam(..) => self.lambda(t, prec),
        }
    }

    fn application(&mut self, name: &str, args: &[&Term], _prec: u8) {
        self.out.push_str(name);
        self.out.push('(');
        for (i, arg) in args.iter().enumerate() {
            if i > 0 {
                self.out.push_str(", ");
            }
            self.term(arg, 0);
        }
        self.out.push(')');
    }

    /// Collects a run of nested binders of one kind, pushing fresh names
    /// onto the bound stack. Returns the binders and the innermost body.
    fn collect_binders(
        &mut self,
        lam: &Term,
        next: impl Fn(&Term) -> Option<Term>,
    ) -> (Vec<(Name, Type)>, Term) {
        let mut binders = Vec::new();
        let mut current = lam.clone();
        loop {
            let TermView::Lam(name, ty, body) = current.view() else {
                unreachable!("binder run starts with a lambda");
            };
            let fresh = fresh_name(name, |candidate| self.taken(candidate));
            binders.push((fresh.clone(), ty.clone()));
            self.bound.push(fresh);
            let body = body.clone();
            match next(&body) {
                Some(inner) => current = inner,
                None => return (binders, body),
            }
        }
    }

    /// Writes `x y : T, ` groups, one group per run of equal types, joined
    /// by `sep` (`, forall ` or `, fun `).
    fn binder_groups(&mut self, binders: &[(Name, Type)], keyword: &str, terminator: &str) {
        let mut i = 0;
        while i < binders.len() {
            if i > 0 {
                self.out.push_str(", ");
                self.out.push_str(keyword);
                self.out.push(' ');
            }
            let ty = &binders[i].1;
            let mut j = i;
            while j < binders.len() && &binders[j].1 == ty {
                if j > i {
                    self.out.push(' ');
                }
                self.out.push_str(binders[j].0.as_str());
                j += 1;
            }
            self.out.push_str(&format!(" : {ty}"));
            i = j;
        }
        self.out.push_str(terminator);
    }

    /// Prints `forall x y : T, body`, merging consecutive binders of the
    /// same quantifier and type.
    fn quantifier(&mut self, keyword: &str, const_name: &str, lam: &Term, prec: u8) {
        self.paren(prec > PREC_BINDER, |p| {
            p.out.push_str(keyword);
            p.out.push(' ');
            let (binders, body) = p.collect_binders(lam, |body| quantifier_body(body, const_name));
            p.binder_groups(&binders, keyword, ", ");
            p.term(&body, PREC_BINDER);
            for _ in &binders {
                p.bound.pop();
            }
        });
    }

    fn lambda(&mut self, t: &Term, prec: u8) {
        self.paren(prec > PREC_BINDER, |p| {
            p.out.push_str("fun ");
            let (binders, body) = p.collect_binders(t, |body| body.is_lam().then(|| body.clone()));
            p.binder_groups(&binders, "fun", " => ");
            p.term(&body, PREC_BINDER);
            for _ in &binders {
                p.bound.pop();
            }
        });
    }

    fn set_builder(&mut self, lam: &Term) {
        let TermView::Lam(name, ty, body) = lam.view() else {
            unreachable!();
        };
        let fresh = fresh_name(name, |candidate| self.taken(candidate));
        self.out.push_str(&format!("{{ {fresh} : {ty} | "));
        self.bound.push(fresh);
        let body = body.clone();
        self.term(&body, 0);
        self.bound.pop();
        self.out.push_str(" }");
    }
}

fn quantifier_body(body: &Term, const_name: &str) -> Option<Term> {
    let (head, args) = body.strip_app();
    if args.len() == 1 && head.is_const_named(const_name) && args[0].is_lam() {
        Some(args[0].clone())
    } else {
        None
    }
}

fn is_binder_form(t: &Term) -> bool {
    t.dest_forall().is_some() || t.dest_exists().is_some() || t.is_lam()
}

/// A short description of a term's role for error messages.
pub fn describe_term(env: &Env, term: &Term) -> String {
    let text = print_term(env, term);
    if term.ty().is_prop() {
        format!("the proposition `{text}`")
    } else {
        format!("`{text}` of type `{}`", term.ty())
    }
}
