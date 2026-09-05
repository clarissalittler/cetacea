//! Primitive rules: positive uses, side-condition violations, and tag
//! propagation.

mod common;

use hol_kernel::{
    abs, add_hyp, and_intro, and_left, and_right, assume, beta, beta_norm_conv, eq_mp, eta,
    excluded_middle, exists_elim, exists_intro, false_elim, forall_elim, forall_intro, funext,
    iff_intro, iff_left, iff_right, imp_elim, imp_intro, inst, inst_type, mk_comb, or_elim,
    or_left, or_right, refl, sorry, subst, sym, trans, true_intro, Name, Tags, Term, Theory, Type,
    TypeSubst,
};

use common::prop_var;

fn sort(name: &str) -> Type {
    Type::con(name, vec![])
}

fn setup() -> (Theory, Type, Term, Term) {
    let mut theory = Theory::new();
    theory.new_type("T", 0).unwrap();
    let t = sort("T");
    theory
        .new_const("P", Type::fun(t.clone(), Type::prop()))
        .unwrap();
    theory
        .new_const("R", Type::funs(&[t.clone(), t.clone()], Type::prop()))
        .unwrap();
    let p = theory
        .constant("P", Type::fun(t.clone(), Type::prop()))
        .unwrap();
    let r = theory
        .constant("R", Type::funs(&[t.clone(), t.clone()], Type::prop()))
        .unwrap();
    (theory, t, p, r)
}

#[test]
fn implication_intro_and_elim() {
    let p = prop_var("P");
    let q = prop_var("Q");
    let hp = assume(&p).unwrap();
    assert_eq!(hp.to_string(), "P |- P");
    let pq = assume(&Term::imp(&p, &q).unwrap()).unwrap();
    let hq = imp_elim(&pq, &hp).unwrap();
    assert_eq!(hq.hyps().len(), 2);
    let closed = imp_intro(&p, &imp_intro(&Term::imp(&p, &q).unwrap(), &hq).unwrap()).unwrap();
    assert_eq!(closed.to_string(), "|- P -> (P -> Q) -> Q");
    assert!(closed.tags().is_empty());

    let err = imp_elim(&pq, &assume(&q).unwrap()).unwrap_err();
    assert!(err.message.contains("expects `P`"), "{err}");
    let err = imp_elim(&hp, &hp).unwrap_err();
    assert!(err.message.contains("expected an implication"), "{err}");
}

#[test]
fn conjunction_and_disjunction() {
    let p = prop_var("P");
    let q = prop_var("Q");
    let both = and_intro(&assume(&p).unwrap(), &assume(&q).unwrap()).unwrap();
    assert_eq!(both.to_string(), "P, Q |- P /\\ Q");
    assert_eq!(and_left(&both).unwrap().concl(), &p);
    assert_eq!(and_right(&both).unwrap().concl(), &q);

    // P \/ Q -> Q \/ P by or_elim, discharging exactly the branch hyps.
    let disj = assume(&Term::or(&p, &q).unwrap()).unwrap();
    let left = or_right(&q, &assume(&p).unwrap()).unwrap();
    let right = or_left(&assume(&q).unwrap(), &p).unwrap();
    let swapped = or_elim(&disj, &left, &right).unwrap();
    assert_eq!(swapped.to_string(), "P \\/ Q |- Q \\/ P");

    // A branch hypothesis that is not the disjunct survives.
    let stray = prop_var("S");
    let left_with_stray = add_hyp(&left, &stray).unwrap();
    let result = or_elim(&disj, &left_with_stray, &right).unwrap();
    assert!(result.has_hyp(&stray));
    assert!(!result.has_hyp(&p));

    let err = or_elim(&disj, &left, &assume(&q).unwrap()).unwrap_err();
    assert!(err.message.contains("different things"), "{err}");
}

#[test]
fn truth_and_falsity() {
    assert_eq!(true_intro().to_string(), "|- True");
    let p = prop_var("P");
    let from_false = false_elim(&assume(&Term::false_()).unwrap(), &p).unwrap();
    assert_eq!(from_false.to_string(), "False |- P");
    let err = false_elim(&assume(&p).unwrap(), &p).unwrap_err();
    assert!(err.message.contains("expected a proof of `False`"), "{err}");
}

#[test]
fn universal_intro_requires_eigenvariable() {
    let (_, t, p, _) = setup();
    let x = Term::free("x", t.clone());
    let px = Term::app(&p, &x).unwrap();
    let hyp = assume(&px).unwrap();
    let err = forall_intro(&x, &hyp).unwrap_err();
    assert!(err.message.contains("occurs free in a hypothesis"), "{err}");

    let discharged = imp_intro(&px, &hyp).unwrap();
    let general = forall_intro(&x, &discharged).unwrap();
    assert_eq!(general.to_string(), "|- forall x : T. P x -> P x");

    let a = Term::free("a", t.clone());
    let instance = forall_elim(&general, &a).unwrap();
    assert_eq!(instance.to_string(), "|- P a -> P a");

    let err = forall_elim(&general, &prop_var("Q")).unwrap_err();
    assert!(err.message.contains("binder has type `T`"), "{err}");
    let err = forall_elim(&instance, &a).unwrap_err();
    assert!(err.message.contains("expected a universal"), "{err}");
}

#[test]
fn universal_elimination_does_not_capture() {
    let (_, t, _, r) = setup();
    let x = Term::free("x", t.clone());
    let y = Term::free("y", t.clone());
    let z = Term::free("z", t.clone());
    // forall x. exists y. R x y
    let inner = Term::exists(&y, &Term::apps(&r, &[x.clone(), y.clone()]).unwrap()).unwrap();
    let stmt = Term::forall(&x, &inner).unwrap();
    let th = assume(&stmt).unwrap();
    let instance = forall_elim(&th, &y).unwrap();
    let expected = Term::exists(&z, &Term::apps(&r, &[y.clone(), z.clone()]).unwrap()).unwrap();
    let captured = Term::exists(&y, &Term::apps(&r, &[y.clone(), y.clone()]).unwrap()).unwrap();
    assert_eq!(instance.concl(), &expected);
    assert_ne!(instance.concl(), &captured);
    assert_eq!(instance.concl().to_string(), "exists y' : T. R y y'");
}

#[test]
fn existential_intro_and_elim() {
    let (_, t, p, _) = setup();
    let x = Term::free("x", t.clone());
    let a = Term::free("a", t.clone());
    let ex = Term::exists(&x, &Term::app(&p, &x).unwrap()).unwrap();
    let pa = assume(&Term::app(&p, &a).unwrap()).unwrap();
    let intro = exists_intro(&ex, &a, &pa).unwrap();
    assert_eq!(intro.to_string(), "P a |- exists x : T. P x");

    let wrong = exists_intro(&ex, &x, &pa).unwrap_err();
    assert!(
        wrong.message.contains("requires a proof of `P x`"),
        "{wrong}"
    );

    // exists x. P x |- exists y. P y \/ False via elimination.
    let b = Term::free("b", t.clone());
    let pb = assume(&Term::app(&p, &b).unwrap()).unwrap();
    let goal_body = Term::or(&Term::app(&p, &x).unwrap(), &Term::false_()).unwrap();
    let goal = Term::exists(&x, &goal_body).unwrap();
    let branch = exists_intro(&goal, &b, &or_left(&pb, &Term::false_()).unwrap()).unwrap();
    let result = exists_elim(&intro, &b, &branch).unwrap();
    assert_eq!(result.to_string(), "P a |- exists x : T. P x \\/ False");

    // The eigenvariable may not escape into the conclusion.
    let escaping = exists_elim(&intro, &b, &pb).unwrap_err();
    assert!(
        escaping.message.contains("occurs in the conclusion"),
        "{escaping}"
    );

    // Nor may it occur in another hypothesis.
    let other = add_hyp(&branch, &Term::app(&p, &b).unwrap()).unwrap();
    let _ = other;
    let extra_hyp = add_hyp(&branch, &Term::eq(&b, &a).unwrap()).unwrap();
    let err = exists_elim(&intro, &b, &extra_hyp).unwrap_err();
    assert!(err.message.contains("hypothesis other than"), "{err}");

    // Nor in the existential theorem itself.
    let err = exists_elim(&intro, &a, &branch).unwrap_err();
    assert!(err.message.contains("existential theorem"), "{err}");
}

#[test]
fn equality_rules() {
    let (_, t, p, _) = setup();
    let a = Term::free("a", t.clone());
    let b = Term::free("b", t.clone());
    let c = Term::free("c", t.clone());
    let ab = assume(&Term::eq(&a, &b).unwrap()).unwrap();
    let bc = assume(&Term::eq(&b, &c).unwrap()).unwrap();
    assert_eq!(refl(&a).unwrap().to_string(), "|- a = a");
    assert_eq!(sym(&ab).unwrap().concl().to_string(), "b = a");
    assert_eq!(trans(&ab, &bc).unwrap().concl().to_string(), "a = c");
    let err = trans(&ab, &ab).unwrap_err();
    assert!(err.message.contains("middle terms differ"), "{err}");

    let cong = mk_comb(&refl(&p).unwrap(), &ab).unwrap();
    assert_eq!(cong.to_string(), "a = b |- P a <-> P b");
    let err = mk_comb(&ab, &ab).unwrap_err();
    assert!(err.message.contains("non-function"), "{err}");

    let pa = assume(&Term::app(&p, &a).unwrap()).unwrap();
    let pb = eq_mp(&cong, &pa).unwrap();
    assert_eq!(pb.to_string(), "P a, a = b |- P b");
    let err = eq_mp(&cong, &pb).unwrap_err();
    assert!(err.message.contains("does not match"), "{err}");
}

#[test]
fn abstraction_beta_and_eta() {
    let (_, t, p, _) = setup();
    let x = Term::free("x", t.clone());
    let a = Term::free("a", t.clone());
    let px = Term::app(&p, &x).unwrap();
    let eq = refl(&px).unwrap();
    let lam_eq = abs(&x, &eq).unwrap();
    assert_eq!(
        lam_eq.to_string(),
        "|- (fun x : T => P x) = fun x : T => P x"
    );
    let err = abs(&x, &assume(&Term::eq(&px, &px).unwrap()).unwrap()).unwrap_err();
    assert!(err.message.contains("occurs free in a hypothesis"), "{err}");

    let lam = Term::lam(&x, &px).unwrap();
    let redex = Term::app(&lam, &a).unwrap();
    assert_eq!(
        beta(&redex).unwrap().to_string(),
        "|- (fun x : T => P x) a <-> P a"
    );
    let err = beta(&a).unwrap_err();
    assert!(err.message.contains("not a beta redex"), "{err}");

    assert_eq!(eta(&lam).unwrap().to_string(), "|- (fun x : T => P x) = P");
    let not_eta = Term::lam(&x, &Term::app(&p, &a).unwrap()).unwrap();
    let err = eta(&not_eta).unwrap_err();
    assert!(err.message.contains("not of the form"), "{err}");
    let self_applied = Term::lam(
        &x,
        &Term::apps(
            &Term::free("f", Type::funs(&[t.clone(), t.clone()], Type::prop())),
            &[x.clone(), x.clone()],
        )
        .unwrap(),
    )
    .unwrap();
    let err = eta(&self_applied).unwrap_err();
    assert!(err.message.contains("not free in `f`"), "{err}");
}

#[test]
fn biconditionals_are_equalities_at_prop() {
    let p = prop_var("P");
    let q = prop_var("Q");
    let pq = assume(&Term::imp(&p, &q).unwrap()).unwrap();
    let qp = assume(&Term::imp(&q, &p).unwrap()).unwrap();
    let iff = iff_intro(&pq, &qp).unwrap();
    assert_eq!(iff.to_string(), "P -> Q, Q -> P |- P <-> Q");
    assert!(iff.concl().dest_eq().is_some());
    assert_eq!(iff_left(&iff).unwrap().concl().to_string(), "P -> Q");
    assert_eq!(iff_right(&iff).unwrap().concl().to_string(), "Q -> P");
    let err = iff_intro(&pq, &pq).unwrap_err();
    assert!(err.message.contains("not converses"), "{err}");
}

#[test]
fn instantiation_of_types_and_terms() {
    let a = Type::var("A");
    let x = Term::free("x", a.clone());
    let generic = forall_intro(&x, &refl(&x).unwrap()).unwrap();
    assert_eq!(generic.to_string(), "|- forall x : A. x = x");
    let mut subst = TypeSubst::new();
    subst.insert(Name::new("A"), Type::prop());
    let at_prop = inst_type(&generic, &subst);
    assert_eq!(at_prop.to_string(), "|- forall x : Prop. x <-> x");
    let instance = forall_elim(&at_prop, &prop_var("P")).unwrap();
    assert_eq!(instance.to_string(), "|- P <-> P");

    let p = prop_var("P");
    let q = prop_var("Q");
    let th = imp_intro(&p, &assume(&p).unwrap()).unwrap();
    let swapped = inst(&th, &[(p.clone(), q.clone())]).unwrap();
    assert_eq!(swapped.to_string(), "|- Q -> Q");
    let err = inst(
        &th,
        &[(
            p.clone(),
            Term::free("n", Type::con("Set", vec![Type::prop()])),
        )],
    )
    .unwrap_err();
    assert!(err.message.contains("cannot substitute"), "{err}");
}

#[test]
fn tags_propagate_by_union() {
    let p = prop_var("P");
    let q = prop_var("Q");
    let em = excluded_middle(&p).unwrap();
    assert_eq!(em.to_string(), "|- P \\/ not P [classical]");
    assert!(em.tags().classical);

    let hole = sorry(&q).unwrap();
    assert!(hole.tags().sorry);
    let combined = and_intro(&em, &hole).unwrap();
    assert!(combined.tags().classical && combined.tags().sorry);

    let mut theory = Theory::new();
    let ax = theory
        .new_axiom("magic", &Term::imp(&q, &p).unwrap())
        .unwrap();
    assert_eq!(ax.tags(), &Tags::axiom("magic"));
    let used = imp_elim(&ax, &hole).unwrap();
    assert_eq!(used.to_string(), "|- P [sorry, axiom magic]");

    // Discharging a hypothesis keeps the tags.
    let discharged = imp_intro(&p, &used).unwrap();
    assert_eq!(discharged.tags(), used.tags());
}

#[test]
fn derived_substitution_and_extensionality() {
    let (_, t, p, _) = setup();
    let a = Term::free("a", t.clone());
    let b = Term::free("b", t.clone());
    let x = Term::free("x", t.clone());
    let ab = assume(&Term::eq(&a, &b).unwrap()).unwrap();
    let pa = assume(&Term::app(&p, &a).unwrap()).unwrap();
    let template = Term::lam(&x, &Term::app(&p, &x).unwrap()).unwrap();
    let pb = subst(&ab, &template, &pa).unwrap();
    assert_eq!(pb.to_string(), "P a, a = b |- P b");

    let f = Term::free("f", Type::fun(t.clone(), t.clone()));
    let g = Term::free("g", Type::fun(t.clone(), t.clone()));
    let pointwise = assume(
        &Term::forall(
            &x,
            &Term::eq(&Term::app(&f, &x).unwrap(), &Term::app(&g, &x).unwrap()).unwrap(),
        )
        .unwrap(),
    )
    .unwrap();
    let at_x = forall_elim(&pointwise, &x).unwrap();
    let ext = funext(&x, &at_x).unwrap();
    assert_eq!(ext.to_string(), "forall x : T. f x = g x |- f = g");
    // The eigenvariable must not be free in the hypotheses.
    let leaky =
        assume(&Term::eq(&Term::app(&f, &x).unwrap(), &Term::app(&g, &x).unwrap()).unwrap())
            .unwrap();
    let err = funext(&x, &leaky).unwrap_err();
    assert!(err.message.contains("occurs free in a hypothesis"), "{err}");
}

#[test]
fn beta_normalization_reaches_normal_form() {
    let (_, t, _, r) = setup();
    let x = Term::free("x", t.clone());
    let y = Term::free("y", t.clone());
    let a = Term::free("a", t.clone());
    let b = Term::free("b", t.clone());
    let curried = Term::lams(
        &[x.clone(), y.clone()],
        &Term::apps(&r, &[x.clone(), y.clone()]).unwrap(),
    )
    .unwrap();
    let applied = Term::apps(&curried, &[a.clone(), b.clone()]).unwrap();
    let conv = beta_norm_conv(&applied).unwrap();
    assert_eq!(
        conv.concl().dest_eq().unwrap().1,
        &Term::apps(&r, &[a.clone(), b.clone()]).unwrap()
    );
    assert!(conv.tags().is_empty());
    // Redexes under binders are reduced too.
    let under = Term::lam(
        &x,
        &Term::app(
            &Term::lam(&y, &Term::apps(&r, &[y.clone(), x.clone()]).unwrap()).unwrap(),
            &a,
        )
        .unwrap(),
    )
    .unwrap();
    let conv = beta_norm_conv(&under).unwrap();
    assert_eq!(
        conv.concl().dest_eq().unwrap().1.to_string(),
        "fun x : T => R a x"
    );
}
