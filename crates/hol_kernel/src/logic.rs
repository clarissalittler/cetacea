//! The primitive logical constants and typed builders and destructors
//! for formulas.
//!
//! `not P` is `imp P False` and `P <-> Q` is `eq P Q` at type `Prop`;
//! neither is a separate constant. Sets are the opaque type `Set A` with
//! `mem` and `setOf` (see [`crate::Theory`]).

use crate::error::{bail, Result};
use crate::name::Name;
use crate::signature::Signature;
use crate::term::Term;
use crate::types::Type;

pub const TRUE: &str = "True";
pub const FALSE: &str = "False";
pub const AND: &str = "and";
pub const OR: &str = "or";
pub const IMP: &str = "imp";
pub const FORALL: &str = "forall";
pub const EXISTS: &str = "exists";
pub const EQ: &str = "eq";
pub const MEM: &str = "mem";
pub const SET_OF: &str = "setOf";

/// The generic type variable used in the declared types of the
/// polymorphic primitives.
fn alpha() -> Type {
    Type::var("A")
}

fn binary_prop() -> Type {
    Type::funs(&[Type::prop(), Type::prop()], Type::prop())
}

/// Declares the logical primitives and the set primitives.
pub(crate) fn declare_logic(sig: &mut Signature) {
    let a = alpha();
    let pred = Type::fun(a.clone(), Type::prop());
    sig.add_const(Name::new(TRUE), Type::prop()).expect("fresh");
    sig.add_const(Name::new(FALSE), Type::prop())
        .expect("fresh");
    sig.add_const(Name::new(AND), binary_prop()).expect("fresh");
    sig.add_const(Name::new(OR), binary_prop()).expect("fresh");
    sig.add_const(Name::new(IMP), binary_prop()).expect("fresh");
    sig.add_const(Name::new(FORALL), Type::fun(pred.clone(), Type::prop()))
        .expect("fresh");
    sig.add_const(Name::new(EXISTS), Type::fun(pred.clone(), Type::prop()))
        .expect("fresh");
    sig.add_const(
        Name::new(EQ),
        Type::funs(&[a.clone(), a.clone()], Type::prop()),
    )
    .expect("fresh");
    sig.add_const(
        Name::new(MEM),
        Type::funs(&[a.clone(), Type::set(a.clone())], Type::prop()),
    )
    .expect("fresh");
    sig.add_const(Name::new(SET_OF), Type::fun(pred, Type::set(a)))
        .expect("fresh");
}

fn require_prop(rule: &'static str, t: &Term) -> Result<()> {
    t.require_closed(rule)?;
    if !t.ty().is_prop() {
        bail!(
            rule,
            "`{t}` has type `{}`, but a proposition was expected",
            t.ty()
        );
    }
    Ok(())
}

impl Term {
    pub fn true_() -> Term {
        Term::constant_unchecked(Name::new(TRUE), Type::prop())
    }

    pub fn false_() -> Term {
        Term::constant_unchecked(Name::new(FALSE), Type::prop())
    }

    fn binary(rule: &'static str, name: &str, p: &Term, q: &Term) -> Result<Term> {
        require_prop(rule, p)?;
        require_prop(rule, q)?;
        let op = Term::constant_unchecked(Name::new(name), binary_prop());
        Ok(Term::app_raw(&Term::app_raw(&op, p), q))
    }

    pub fn and(p: &Term, q: &Term) -> Result<Term> {
        Term::binary("and", AND, p, q)
    }

    pub fn or(p: &Term, q: &Term) -> Result<Term> {
        Term::binary("or", OR, p, q)
    }

    pub fn imp(p: &Term, q: &Term) -> Result<Term> {
        Term::binary("imp", IMP, p, q)
    }

    /// `not P` is `P -> False`.
    pub fn not(p: &Term) -> Result<Term> {
        Term::imp(p, &Term::false_())
    }

    pub fn eq(a: &Term, b: &Term) -> Result<Term> {
        a.require_closed("eq")?;
        b.require_closed("eq")?;
        if a.ty() != b.ty() {
            bail!(
                "eq",
                "cannot equate `{a}` of type `{}` with `{b}` of type `{}`",
                a.ty(),
                b.ty()
            );
        }
        let op = Term::constant_unchecked(
            Name::new(EQ),
            Type::funs(&[a.ty().clone(), a.ty().clone()], Type::prop()),
        );
        Ok(Term::app_raw(&Term::app_raw(&op, a), b))
    }

    /// `P <-> Q` is `P = Q` at type `Prop`.
    pub fn iff(p: &Term, q: &Term) -> Result<Term> {
        require_prop("iff", p)?;
        require_prop("iff", q)?;
        Term::eq(p, q)
    }

    fn quantifier(rule: &'static str, name: &str, var: &Term, body: &Term) -> Result<Term> {
        require_prop(rule, body)?;
        let lam = Term::lam(var, body)?;
        Term::quantifier_over(rule, name, &lam)
    }

    fn quantifier_over(rule: &'static str, name: &str, pred: &Term) -> Result<Term> {
        let Some((dom, cod)) = pred.ty().as_fun() else {
            bail!(rule, "`{pred}` is not a predicate");
        };
        if !cod.is_prop() {
            bail!(rule, "`{pred}` is not a predicate");
        }
        let q =
            Term::constant_unchecked(Name::new(name), Type::fun(pred.ty().clone(), Type::prop()));
        let _ = dom;
        Ok(Term::app_raw(&q, pred))
    }

    /// `forall x. body`, abstracting the free variable `var`.
    pub fn forall(var: &Term, body: &Term) -> Result<Term> {
        Term::quantifier("forall", FORALL, var, body)
    }

    /// `exists x. body`, abstracting the free variable `var`.
    pub fn exists(var: &Term, body: &Term) -> Result<Term> {
        Term::quantifier("exists", EXISTS, var, body)
    }

    /// `forall` applied to an existing predicate lambda.
    pub fn forall_pred(pred: &Term) -> Result<Term> {
        pred.require_closed("forall")?;
        Term::quantifier_over("forall", FORALL, pred)
    }

    /// `exists` applied to an existing predicate lambda.
    pub fn exists_pred(pred: &Term) -> Result<Term> {
        pred.require_closed("exists")?;
        Term::quantifier_over("exists", EXISTS, pred)
    }

    pub fn foralls(vars: &[Term], body: &Term) -> Result<Term> {
        let mut current = body.clone();
        for var in vars.iter().rev() {
            current = Term::forall(var, &current)?;
        }
        Ok(current)
    }

    pub fn existss(vars: &[Term], body: &Term) -> Result<Term> {
        let mut current = body.clone();
        for var in vars.iter().rev() {
            current = Term::exists(var, &current)?;
        }
        Ok(current)
    }

    /// `p1 -> p2 -> ... -> q`.
    pub fn imps(premises: &[Term], conclusion: &Term) -> Result<Term> {
        let mut current = conclusion.clone();
        for premise in premises.iter().rev() {
            current = Term::imp(premise, &current)?;
        }
        Ok(current)
    }

    /// `x in A`.
    pub fn mem(x: &Term, set: &Term) -> Result<Term> {
        let elem = x.ty().clone();
        let op = Term::constant_unchecked(
            Name::new(MEM),
            Type::funs(&[elem.clone(), Type::set(elem)], Type::prop()),
        );
        Term::apps(&op, &[x.clone(), set.clone()])
    }

    /// `setOf(pred)` for a predicate lambda.
    pub fn set_of(pred: &Term) -> Result<Term> {
        let Some((dom, cod)) = pred.ty().as_fun() else {
            bail!("setOf", "`{pred}` is not a predicate");
        };
        if !cod.is_prop() {
            bail!("setOf", "`{pred}` is not a predicate");
        }
        let op = Term::constant_unchecked(
            Name::new(SET_OF),
            Type::fun(pred.ty().clone(), Type::set(dom.clone())),
        );
        Term::app(&op, pred)
    }

    pub fn is_true(&self) -> bool {
        self.is_const_named(TRUE)
    }

    pub fn is_false(&self) -> bool {
        self.is_const_named(FALSE)
    }

    /// Destructs `c a b` for a binary constant named `name`.
    pub fn dest_binary(&self, name: &str) -> Option<(&Term, &Term)> {
        let (head, args) = self.strip_app();
        if args.len() == 2 && head.is_const_named(name) {
            Some((args[0], args[1]))
        } else {
            None
        }
    }

    pub fn dest_and(&self) -> Option<(&Term, &Term)> {
        self.dest_binary(AND)
    }

    pub fn dest_or(&self) -> Option<(&Term, &Term)> {
        self.dest_binary(OR)
    }

    pub fn dest_imp(&self) -> Option<(&Term, &Term)> {
        self.dest_binary(IMP)
    }

    pub fn dest_eq(&self) -> Option<(&Term, &Term)> {
        self.dest_binary(EQ)
    }

    pub fn dest_not(&self) -> Option<&Term> {
        let (p, q) = self.dest_imp()?;
        q.is_false().then_some(p)
    }

    /// For `P <-> Q`, an equality at type `Prop`.
    pub fn dest_iff(&self) -> Option<(&Term, &Term)> {
        let (a, b) = self.dest_eq()?;
        a.ty().is_prop().then_some((a, b))
    }

    fn dest_quantifier(&self, name: &str) -> Option<&Term> {
        let (head, args) = self.strip_app();
        if args.len() == 1 && head.is_const_named(name) && args[0].is_lam() {
            Some(args[0])
        } else {
            None
        }
    }

    /// For `forall x. P`, the predicate lambda `λx. P`.
    pub fn dest_forall(&self) -> Option<&Term> {
        self.dest_quantifier(FORALL)
    }

    /// For `exists x. P`, the predicate lambda `λx. P`.
    pub fn dest_exists(&self) -> Option<&Term> {
        self.dest_quantifier(EXISTS)
    }

    pub fn dest_mem(&self) -> Option<(&Term, &Term)> {
        self.dest_binary(MEM)
    }
}
