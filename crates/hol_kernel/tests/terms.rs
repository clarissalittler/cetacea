//! Term construction, alpha-equivalence, capture-free substitution, and
//! printing.

mod common;

use std::collections::BTreeSet;

use hol_kernel::{Name, Term, Theory, Type, TypeSubst};

fn sort(name: &str) -> Type {
    Type::con(name, vec![])
}

fn relation(theory: &mut Theory, name: &str, ty: &Type) -> Term {
    theory
        .new_const(name, Type::funs(&[ty.clone(), ty.clone()], Type::prop()))
        .unwrap();
    theory
        .constant(name, Type::funs(&[ty.clone(), ty.clone()], Type::prop()))
        .unwrap()
}

#[test]
fn application_checks_types() {
    let mut theory = Theory::new();
    theory.new_type("Person", 0).unwrap();
    let person = sort("Person");
    theory.new_const("alice", person.clone()).unwrap();
    theory
        .new_const("Student", Type::fun(person.clone(), Type::prop()))
        .unwrap();
    let alice = theory.constant("alice", person.clone()).unwrap();
    let student = theory
        .constant("Student", Type::fun(person.clone(), Type::prop()))
        .unwrap();

    let ok = Term::app(&student, &alice).unwrap();
    assert!(ok.ty().is_prop());
    assert_eq!(ok.to_string(), "Student alice");

    let err = Term::app(&alice, &alice).unwrap_err();
    assert!(err.message.contains("non-function type"), "{err}");

    let n = Term::free("n", sort("Prop"));
    let err = Term::app(&student, &n).unwrap_err();
    assert!(
        err.message
            .contains("expected an argument of type `Person`"),
        "{err}"
    );
}

#[test]
fn constants_must_be_instances_of_their_declared_type() {
    let theory = Theory::new();
    let bad = theory
        .constant(
            "eq",
            Type::funs(&[Type::prop(), sort("Prop")], Type::prop()),
        )
        .map(|_| ());
    assert!(bad.is_ok(), "eq at Prop -> Prop -> Prop is an instance");
    let mut theory = Theory::new();
    theory.new_type("Nat", 0).unwrap();
    let bad = theory.constant("eq", Type::funs(&[sort("Nat"), Type::prop()], Type::prop()));
    let err = bad.unwrap_err();
    assert!(err.message.contains("not an instance"), "{err}");

    let err = theory
        .constant("eq", Type::con("Bogus", vec![]))
        .unwrap_err();
    assert!(err.message.contains("unknown type constructor"), "{err}");
}

#[test]
fn lambda_terms_are_alpha_equivalent() {
    let a = sort("Prop");
    let x = Term::free("x", a.clone());
    let y = Term::free("y", a.clone());
    let id_x = Term::lam(&x, &x).unwrap();
    let id_y = Term::lam(&y, &y).unwrap();
    assert_eq!(id_x, id_y);
    assert_eq!(id_x.to_string(), "fun x : Prop => x");
    assert_eq!(id_y.to_string(), "fun y : Prop => y");

    let const_xy = Term::lam(&x, &y).unwrap();
    assert_ne!(id_x, const_xy);
}

#[test]
fn substitution_does_not_capture() {
    let mut theory = Theory::new();
    theory.new_type("T", 0).unwrap();
    let t = sort("T");
    let r = relation(&mut theory, "R", &t);
    let x = Term::free("x", t.clone());
    let z = Term::free("z", t.clone());
    let w = Term::free("w", t.clone());

    // fun z => R x z, then substitute z for x.
    let body = Term::apps(&r, &[x.clone(), z.clone()]).unwrap();
    let lam = Term::lam(&z, &body).unwrap();
    let substituted = lam.subst_free(&[(x.clone(), z.clone())]).unwrap();

    let expected = Term::lam(&w, &Term::apps(&r, &[z.clone(), w.clone()]).unwrap()).unwrap();
    let captured = Term::lam(&z, &Term::apps(&r, &[z.clone(), z.clone()]).unwrap()).unwrap();
    assert_eq!(substituted, expected);
    assert_ne!(substituted, captured);
    assert_eq!(substituted.to_string(), "fun z' : T => R z z'");
}

#[test]
fn opening_a_binder_avoids_free_variables() {
    let mut theory = Theory::new();
    theory.new_type("T", 0).unwrap();
    let t = sort("T");
    let r = relation(&mut theory, "R", &t);
    let x = Term::free("x", t.clone());
    let y = Term::free("y", t.clone());
    let lam = Term::lam(&x, &Term::apps(&r, &[x.clone(), y.clone()]).unwrap()).unwrap();
    // Rename the free y to x so the body mentions a free x under a binder
    // displayed as x.
    let clashing = lam.subst_free(&[(y.clone(), x.clone())]).unwrap();
    assert_eq!(clashing.to_string(), "fun x' : T => R x' x");

    let (var, opened) = clashing.open_fresh(&BTreeSet::new()).unwrap();
    assert_eq!(var.as_free().unwrap().0, &Name::new("x'"));
    assert_eq!(opened, Term::apps(&r, &[var.clone(), x.clone()]).unwrap());

    let mut avoid = BTreeSet::new();
    avoid.insert(Name::new("x'"));
    let (var, _) = clashing.open_fresh(&avoid).unwrap();
    assert_eq!(var.as_free().unwrap().0, &Name::new("x''"));
}

#[test]
fn lambda_bodies_cannot_be_used_as_terms() {
    let x = Term::free("x", Type::prop());
    let lam = Term::lam(&x, &x).unwrap();
    let hol_kernel::TermView::Lam(_, _, body) = lam.view() else {
        panic!("lambda");
    };
    assert!(!body.is_closed());
    let err = Term::app(&lam, body).unwrap_err();
    assert!(err.message.contains("dangling"), "{err}");
    let err = Term::eq(body, body).unwrap_err();
    assert!(err.message.contains("dangling"), "{err}");
    let err = hol_kernel::refl(body).unwrap_err();
    assert!(err.message.contains("dangling"), "{err}");
}

#[test]
fn beta_reduction_substitutes() {
    let mut theory = Theory::new();
    theory.new_type("T", 0).unwrap();
    let t = sort("T");
    let r = relation(&mut theory, "R", &t);
    let x = Term::free("x", t.clone());
    let a = Term::free("a", t.clone());
    let lam = Term::lam(&x, &Term::apps(&r, &[x.clone(), x.clone()]).unwrap()).unwrap();
    let redex = Term::app(&lam, &a).unwrap();
    assert_eq!(
        redex.beta_head().unwrap(),
        Term::apps(&r, &[a.clone(), a.clone()]).unwrap()
    );
    assert!(a.beta_head().is_none());

    let wrong_type = Term::free("p", Type::prop());
    let err = lam.beta_apply(&wrong_type).unwrap_err();
    assert!(err.message.contains("binder has type `T`"), "{err}");
}

#[test]
fn type_instantiation_reaches_every_type() {
    let a = Type::var("A");
    let x = Term::free("x", a.clone());
    let p = Term::free("P", Type::fun(a.clone(), Type::prop()));
    let stmt = Term::forall(&x, &Term::app(&p, &x).unwrap()).unwrap();
    let mut subst = TypeSubst::new();
    subst.insert(Name::new("A"), Type::prop());
    let instance = stmt.subst_type(&subst);
    assert_eq!(instance.to_string(), "forall x : Prop. P x");
    let mut vars = BTreeSet::new();
    instance.type_vars(&mut vars);
    assert!(vars.is_empty());
}

#[test]
fn formulas_print_with_expected_precedence() {
    let p = common::prop_var("P");
    let q = common::prop_var("Q");
    let r = common::prop_var("R");
    let and = Term::and(&p, &q).unwrap();
    let imp = Term::imp(&and, &r).unwrap();
    assert_eq!(imp.to_string(), "P /\\ Q -> R");
    let nested = Term::imp(&p, &Term::imp(&q, &r).unwrap()).unwrap();
    assert_eq!(nested.to_string(), "P -> Q -> R");
    let left_nested = Term::imp(&Term::imp(&p, &q).unwrap(), &r).unwrap();
    assert_eq!(left_nested.to_string(), "(P -> Q) -> R");
    let not = Term::not(&Term::or(&p, &q).unwrap()).unwrap();
    assert_eq!(not.to_string(), "not (P \\/ Q)");
    let iff = Term::iff(&p, &q).unwrap();
    assert_eq!(iff.to_string(), "P <-> Q");
    let x = Term::free("x", Type::prop());
    let quantified = Term::imp(&p, &Term::forall(&x, &Term::or(&x, &q).unwrap()).unwrap()).unwrap();
    assert_eq!(quantified.to_string(), "P -> forall x : Prop. x \\/ Q");
    let ex = Term::exists(&x, &Term::and(&x, &x).unwrap()).unwrap();
    assert_eq!(
        Term::and(&ex, &p).unwrap().to_string(),
        "(exists x : Prop. x /\\ x) /\\ P"
    );
}

#[test]
fn free_variable_bookkeeping() {
    let t = sort("Prop");
    let x = Term::free("x", t.clone());
    let y = Term::free("y", t.clone());
    let body = Term::and(&x, &y).unwrap();
    let lam = Term::lam(&x, &body).unwrap();
    assert!(lam.contains_var(&y));
    assert!(!lam.contains_var(&x));
    let names: Vec<String> = lam
        .free_var_names()
        .into_iter()
        .map(|n| n.to_string())
        .collect();
    assert_eq!(names, vec!["y".to_string()]);
    let applied = Term::apps(
        &Term::free("f", Type::funs(&[t.clone(), t.clone()], t.clone())),
        &[x.clone(), y.clone()],
    )
    .unwrap();
    let (head, args) = applied.strip_app();
    assert_eq!(head.as_free().unwrap().0.as_str(), "f");
    assert_eq!(args.len(), 2);
}
