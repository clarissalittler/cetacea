//! End-to-end: prove `forall n. add n zero = n` and `succ n = zero -> False`
//! from the datatype package and the recursive-function package using
//! only kernel rules.

mod common;

use hol_kernel::{
    assume, beta_norm, discharge, false_elim, forall_elim, forall_intro, generalize, imp_elim,
    mk_comb, refl, spec, trans, Tags, Term, Type,
};

use common::{add, declare_add, nat, nat_theory, succ, succ_fn, zero};

#[test]
fn add_n_zero_by_induction() {
    let (mut theory, info) = nat_theory();
    let equations = declare_add(&mut theory);
    let z = zero(&theory);

    // P := fun n => add n zero = n
    let n = Term::free("n", nat());
    let motive = Term::lam(&n, &Term::eq(&add(&theory, &n, &z), &n).unwrap()).unwrap();

    // Instantiate the induction principle and normalize the redexes.
    let instantiated = forall_elim(&info.induction, &motive).unwrap();
    let principle = beta_norm(&instantiated).unwrap();
    assert_eq!(
        principle.to_string(),
        "|- add zero zero = zero -> (forall x1 : Nat. add x1 zero = x1 -> add (succ x1) zero = succ x1) -> forall v : Nat. add v zero = v [datatype Nat]"
    );

    // Base case from the first equation.
    let base = spec(&equations[0], std::slice::from_ref(&z)).unwrap();

    // Step: assume the hypothesis for a fresh k and rewrite.
    let k = Term::free("k", nat());
    let ih_formula = Term::eq(&add(&theory, &k, &z), &k).unwrap();
    let ih = assume(&ih_formula).unwrap();
    let unfold = spec(&equations[1], &[k.clone(), z.clone()]).unwrap();
    let congruence = mk_comb(&refl(&succ_fn(&theory)).unwrap(), &ih).unwrap();
    let step_body = trans(&unfold, &congruence).unwrap();
    let step = generalize(
        std::slice::from_ref(&k),
        &discharge(&[ih_formula], &step_body).unwrap(),
    )
    .unwrap();

    let result = imp_elim(&imp_elim(&principle, &base).unwrap(), &step).unwrap();
    let v = Term::free("v", nat());
    let expected = Term::forall(&v, &Term::eq(&add(&theory, &v, &z), &v).unwrap()).unwrap();
    assert_eq!(result.concl(), &expected);
    assert!(result.hyps().is_empty());
    assert_eq!(result.tags(), &Tags::datatype("Nat"));
}

#[test]
fn succ_is_never_zero() {
    let (theory, info) = nat_theory();
    let n = Term::free("n", nat());
    let z = zero(&theory);
    // The package gives zero = succ y -> False; flip it with symmetry.
    let distinct = spec(&info.distinct[0], std::slice::from_ref(&n)).unwrap();
    let hyp = Term::eq(&succ(&theory, &n), &z).unwrap();
    let assumed = assume(&hyp).unwrap();
    let flipped = hol_kernel::sym(&assumed).unwrap();
    let absurd = imp_elim(&distinct, &flipped).unwrap();
    let anything = false_elim(&absurd, &Term::eq(&n, &n).unwrap()).unwrap();
    let closed = forall_intro(&n, &discharge(&[hyp], &anything).unwrap()).unwrap();
    assert_eq!(
        closed.to_string(),
        "|- forall n : Nat. succ n = zero -> n = n [datatype Nat]"
    );
}

#[test]
fn induction_principle_cannot_be_forged_without_the_tag() {
    // Any theorem that goes through the package carries the datatype
    // tag, so a course policy can see induction was used.
    let (_, info) = nat_theory();
    let p = Term::free("Q", Type::fun(nat(), Type::prop()));
    let instance = forall_elim(&info.induction, &p).unwrap();
    assert!(instance.tags().datatypes.contains(&"Nat".into()));
}
