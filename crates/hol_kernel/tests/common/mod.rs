#![allow(dead_code)]

use hol_kernel::{CtorSpec, DatatypeInfo, DatatypeSpec, RecFunSpec, Term, Theory, Type};

pub fn nat() -> Type {
    Type::con("Nat", vec![])
}

pub fn nat_theory() -> (Theory, DatatypeInfo) {
    let mut theory = Theory::new();
    let info = theory
        .new_datatype(&DatatypeSpec {
            name: "Nat".into(),
            params: vec![],
            ctors: vec![
                CtorSpec {
                    name: "zero".into(),
                    args: vec![],
                },
                CtorSpec {
                    name: "succ".into(),
                    args: vec![nat()],
                },
            ],
        })
        .expect("Nat is a valid datatype");
    (theory, info)
}

pub fn zero(theory: &Theory) -> Term {
    theory.constant("zero", nat()).unwrap()
}

pub fn succ_fn(theory: &Theory) -> Term {
    theory.constant("succ", Type::fun(nat(), nat())).unwrap()
}

pub fn succ(theory: &Theory, n: &Term) -> Term {
    Term::app(&succ_fn(theory), n).unwrap()
}

pub fn add_fn(theory: &Theory) -> Term {
    theory
        .constant("add", Type::funs(&[nat(), nat()], nat()))
        .unwrap()
}

pub fn add(theory: &Theory, a: &Term, b: &Term) -> Term {
    Term::apps(&add_fn(theory), &[a.clone(), b.clone()]).unwrap()
}

/// Declares `add : Nat -> Nat -> Nat` by structural recursion on its
/// first argument and returns the two equations.
pub fn declare_add(theory: &mut Theory) -> Vec<hol_kernel::Thm> {
    theory
        .new_const("add", Type::funs(&[nat(), nat()], nat()))
        .unwrap();
    let n = Term::free("n", nat());
    let m = Term::free("m", nat());
    let eq_zero =
        Term::forall(&m, &Term::eq(&add(theory, &zero(theory), &m), &m).unwrap()).unwrap();
    let eq_succ = Term::foralls(
        &[n.clone(), m.clone()],
        &Term::eq(
            &add(theory, &succ(theory, &n), &m),
            &succ(theory, &add(theory, &n, &m)),
        )
        .unwrap(),
    )
    .unwrap();
    theory
        .new_recfun(&[RecFunSpec {
            name: "add".into(),
            rec_arg: 0,
            equations: vec![eq_zero, eq_succ],
        }])
        .expect("add is structurally recursive")
}

pub fn prop_var(name: &str) -> Term {
    Term::free(name, Type::prop())
}
