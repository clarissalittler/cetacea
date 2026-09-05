//! Definitional principles: definitions, axioms, set principles, the
//! datatype package, and the recursive-function package, including the
//! shapes they must reject.

mod common;

use hol_kernel::{CtorSpec, DatatypeSpec, RecFunSpec, Tags, Term, Theory, Type};

use common::{add, declare_add, nat, nat_theory, succ, zero};

#[test]
fn base_theory_has_set_principles() {
    let theory = Theory::new();
    let mem_set_of = theory.theorem("Set.mem_setOf").unwrap();
    assert_eq!(
        mem_set_of.to_string(),
        "|- forall P : A -> Prop. forall x : A. x in setOf P <-> P x"
    );
    let ext = theory.theorem("Set.ext").unwrap();
    assert_eq!(
        ext.to_string(),
        "|- forall S : Set A. forall T : Set A. (forall x : A. x in S <-> x in T) -> S = T"
    );
    assert!(mem_set_of.tags().is_empty());
    assert!(ext.tags().is_empty());
}

#[test]
fn definitions_are_conservative() {
    let mut theory = Theory::new();
    let a = Type::var("A");
    let x = Term::free("x", a.clone());
    let id = theory.new_def("id", &Term::lam(&x, &x).unwrap()).unwrap();
    assert_eq!(id.to_string(), "|- id = fun x : A => x");
    assert!(id.tags().is_empty());
    assert!(theory.is_defined(&"id".into()));
    assert_eq!(theory.definition("id"), Some(&id));
    // The constant is now usable at instances.
    let at_prop = theory
        .constant("id", Type::fun(Type::prop(), Type::prop()))
        .unwrap();
    assert!(at_prop.ty().is_fun_like());

    let err = theory
        .new_def("id", &Term::lam(&x, &x).unwrap())
        .unwrap_err();
    assert!(err.message.contains("already declared"), "{err}");

    let err = theory.new_def("open", &x).unwrap_err();
    assert!(err.message.contains("free variable `x`"), "{err}");

    // A Prop-typed body mentioning a type variable is rejected: it would
    // let `hidden` depend on a type that is not part of its type.
    let hidden = Term::forall(&x, &Term::eq(&x, &x).unwrap()).unwrap();
    let err = theory.new_def("hidden", &hidden).unwrap_err();
    assert!(err.message.contains("type variable `A`"), "{err}");
}

trait FunLike {
    fn is_fun_like(&self) -> bool;
}

impl FunLike for Type {
    fn is_fun_like(&self) -> bool {
        self.as_fun().is_some()
    }
}

#[test]
fn axioms_are_tagged_and_unique() {
    let mut theory = Theory::new();
    let p = common::prop_var("P");
    let ax = theory.new_axiom("p_holds", &p).unwrap();
    assert_eq!(ax.tags(), &Tags::axiom("p_holds"));
    assert_eq!(theory.theorem("p_holds"), Some(&ax));
    let err = theory.new_axiom("p_holds", &p).unwrap_err();
    assert!(err.message.contains("already exists"), "{err}");
    let err = theory
        .new_axiom("bad", &Term::free("x", Type::var("A")))
        .unwrap_err();
    assert!(err.message.contains("not a proposition"), "{err}");
}

#[test]
fn declarations_check_types() {
    let mut theory = Theory::new();
    let err = theory
        .new_const("ghost", Type::con("Ghost", vec![]))
        .unwrap_err();
    assert!(err.message.contains("unknown type constructor"), "{err}");
    let err = theory
        .new_const("bad_set", Type::con("Set", vec![]))
        .unwrap_err();
    assert!(err.message.contains("takes 1 argument"), "{err}");
    theory.new_type("Person", 0).unwrap();
    let err = theory.new_type("Person", 0).unwrap_err();
    assert!(err.message.contains("already declared"), "{err}");
}

#[test]
fn nat_datatype_principles() {
    let (theory, info) = nat_theory();
    assert_eq!(info.ctors.len(), 2);
    assert!(info.ctors[0].injective.is_none());
    assert_eq!(
        info.ctors[1].injective.as_ref().unwrap().to_string(),
        "|- forall x1 : Nat. forall y1 : Nat. succ x1 = succ y1 -> x1 = y1 [datatype Nat]"
    );
    assert_eq!(info.distinct.len(), 1);
    assert_eq!(
        info.distinct[0].to_string(),
        "|- forall y1 : Nat. not zero = succ y1 [datatype Nat]"
    );
    assert_eq!(
        info.cases.to_string(),
        "|- forall v : Nat. v = zero \\/ exists x1 : Nat. v = succ x1 [datatype Nat]"
    );
    assert_eq!(
        info.induction.to_string(),
        "|- forall P : Nat -> Prop. P zero -> (forall x1 : Nat. P x1 -> P (succ x1)) -> forall v : Nat. P v [datatype Nat]"
    );
    assert_eq!(theory.theorem("Nat.induct"), Some(&info.induction));
    assert_eq!(theory.theorem("Nat.cases"), Some(&info.cases));
    assert!(theory.theorem("Nat.succ.inj").is_some());
    assert!(theory.theorem("Nat.zero.succ.distinct").is_some());
    assert_eq!(
        theory.ctor_datatype(&"succ".into()).unwrap().name.as_str(),
        "Nat"
    );
}

fn list_spec() -> DatatypeSpec {
    let a = Type::var("A");
    DatatypeSpec {
        name: "List".into(),
        params: vec!["A".into()],
        ctors: vec![
            CtorSpec {
                name: "nil".into(),
                args: vec![],
            },
            CtorSpec {
                name: "cons".into(),
                args: vec![a.clone(), Type::con("List", vec![a])],
            },
        ],
    }
}

#[test]
fn polymorphic_list_datatype() {
    let mut theory = Theory::new();
    let info = theory.new_datatype(&list_spec()).unwrap();
    assert_eq!(info.ctors[1].recursive, vec![false, true]);
    assert_eq!(
        info.ctors[1].injective.as_ref().unwrap().to_string(),
        "|- forall x1 : A. forall x2 : List A. forall y1 : A. forall y2 : List A. cons x1 x2 = cons y1 y2 -> x1 = y1 /\\ x2 = y2 [datatype List]"
    );
    assert_eq!(
        info.induction.to_string(),
        "|- forall P : List A -> Prop. P nil -> (forall x1 : A. forall x2 : List A. P x2 -> P (cons x1 x2)) -> forall v : List A. P v [datatype List]"
    );
    // Constructors are usable at instances.
    let nil_prop = theory
        .constant("nil", Type::con("List", vec![Type::prop()]))
        .unwrap();
    assert_eq!(nil_prop.ty().to_string(), "List Prop");
}

#[test]
fn datatype_package_rejects_unsupported_shapes() {
    let mut theory = Theory::new();
    theory.new_type("Nat", 0).unwrap();
    let bad = Type::con("Bad", vec![]);

    let negative = DatatypeSpec {
        name: "Bad".into(),
        params: vec![],
        ctors: vec![
            CtorSpec {
                name: "leaf".into(),
                args: vec![],
            },
            CtorSpec {
                name: "mk".into(),
                args: vec![Type::fun(bad.clone(), nat())],
            },
        ],
    };
    let err = theory.new_datatype(&negative).unwrap_err();
    assert!(err.message.contains("nested or negative position"), "{err}");
    assert!(!theory.signature().has_type(&"Bad".into()));

    let positive_under_fun = DatatypeSpec {
        name: "Bad".into(),
        params: vec![],
        ctors: vec![
            CtorSpec {
                name: "leaf".into(),
                args: vec![],
            },
            CtorSpec {
                name: "mk".into(),
                args: vec![Type::fun(nat(), bad.clone())],
            },
        ],
    };
    let err = theory.new_datatype(&positive_under_fun).unwrap_err();
    assert!(err.message.contains("nested or negative position"), "{err}");

    let empty = DatatypeSpec {
        name: "Bad".into(),
        params: vec![],
        ctors: vec![CtorSpec {
            name: "mk".into(),
            args: vec![bad.clone()],
        }],
    };
    let err = theory.new_datatype(&empty).unwrap_err();
    assert!(err.message.contains("would be empty"), "{err}");

    let no_ctors = DatatypeSpec {
        name: "Bad".into(),
        params: vec![],
        ctors: vec![],
    };
    let err = theory.new_datatype(&no_ctors).unwrap_err();
    assert!(err.message.contains("no constructors"), "{err}");

    let duplicate = DatatypeSpec {
        name: "Bad".into(),
        params: vec![],
        ctors: vec![
            CtorSpec {
                name: "a".into(),
                args: vec![],
            },
            CtorSpec {
                name: "a".into(),
                args: vec![],
            },
        ],
    };
    let err = theory.new_datatype(&duplicate).unwrap_err();
    assert!(err.message.contains("duplicate constructor"), "{err}");

    let stray_var = DatatypeSpec {
        name: "Bad".into(),
        params: vec![],
        ctors: vec![CtorSpec {
            name: "mk".into(),
            args: vec![Type::var("B")],
        }],
    };
    let err = theory.new_datatype(&stray_var).unwrap_err();
    assert!(
        err.message.contains("undeclared type variable `B`"),
        "{err}"
    );

    theory.new_datatype(&list_spec()).unwrap();
    let nested = DatatypeSpec {
        name: "Rose".into(),
        params: vec![],
        ctors: vec![
            CtorSpec {
                name: "rleaf".into(),
                args: vec![],
            },
            CtorSpec {
                name: "rnode".into(),
                args: vec![Type::con("List", vec![Type::con("Rose", vec![])])],
            },
        ],
    };
    let err = theory.new_datatype(&nested).unwrap_err();
    assert!(err.message.contains("nested or negative position"), "{err}");

    let wrong_params = DatatypeSpec {
        name: "Tree".into(),
        params: vec!["A".into()],
        ctors: vec![
            CtorSpec {
                name: "tleaf".into(),
                args: vec![],
            },
            CtorSpec {
                name: "tnode".into(),
                args: vec![Type::con("Tree", vec![nat()])],
            },
        ],
    };
    let err = theory.new_datatype(&wrong_params).unwrap_err();
    assert!(err.message.contains("nested or negative position"), "{err}");

    let existing_type = DatatypeSpec {
        name: "Nat".into(),
        params: vec![],
        ctors: vec![CtorSpec {
            name: "z".into(),
            args: vec![],
        }],
    };
    let err = theory.new_datatype(&existing_type).unwrap_err();
    assert!(err.message.contains("already declared"), "{err}");

    let ctor_clash = DatatypeSpec {
        name: "Bit".into(),
        params: vec![],
        ctors: vec![CtorSpec {
            name: "nil".into(),
            args: vec![],
        }],
    };
    let err = theory.new_datatype(&ctor_clash).unwrap_err();
    assert!(
        err.message.contains("clashes with an existing constant"),
        "{err}"
    );
}

#[test]
fn structural_recursion_over_nat() {
    let (mut theory, _) = nat_theory();
    let equations = declare_add(&mut theory);
    assert_eq!(equations.len(), 2);
    assert_eq!(
        equations[0].to_string(),
        "|- forall m : Nat. add zero m = m"
    );
    assert_eq!(
        equations[1].to_string(),
        "|- forall n : Nat. forall m : Nat. add (succ n) m = succ (add n m)"
    );
    assert!(equations[1].tags().is_empty());
    assert_eq!(theory.theorem("add.eq.succ"), Some(&equations[1]));
    assert!(theory.is_defined(&"add".into()));

    // Redefinition is refused.
    let err = theory
        .new_recfun(&[RecFunSpec {
            name: "add".into(),
            rec_arg: 0,
            equations: vec![],
        }])
        .unwrap_err();
    assert!(err.message.contains("already defined"), "{err}");
}

#[test]
fn recursion_on_a_later_argument_and_varying_parameters() {
    let (mut theory, _) = nat_theory();
    theory
        .new_const("addr", Type::funs(&[nat(), nat()], nat()))
        .unwrap();
    let addr = |a: &Term, b: &Term| {
        Term::apps(
            &theory
                .constant("addr", Type::funs(&[nat(), nat()], nat()))
                .unwrap(),
            &[a.clone(), b.clone()],
        )
        .unwrap()
    };
    let n = Term::free("n", nat());
    let m = Term::free("m", nat());
    // addr n zero = n ; addr n (succ m) = addr (succ n) m
    let eq_zero = Term::forall(&n, &Term::eq(&addr(&n, &zero(&theory)), &n).unwrap()).unwrap();
    let eq_succ = Term::foralls(
        &[n.clone(), m.clone()],
        &Term::eq(&addr(&n, &succ(&theory, &m)), &addr(&succ(&theory, &n), &m)).unwrap(),
    )
    .unwrap();
    let thms = theory
        .new_recfun(&[RecFunSpec {
            name: "addr".into(),
            rec_arg: 1,
            equations: vec![eq_zero, eq_succ],
        }])
        .unwrap();
    assert_eq!(thms.len(), 2);
}

#[test]
fn mutual_recursion_defines_recursive_predicates() {
    let (mut theory, _) = nat_theory();
    let pred_ty = Type::fun(nat(), Type::prop());
    theory.new_const("even", pred_ty.clone()).unwrap();
    theory.new_const("odd", pred_ty.clone()).unwrap();
    let even = theory.constant("even", pred_ty.clone()).unwrap();
    let odd = theory.constant("odd", pred_ty.clone()).unwrap();
    let n = Term::free("n", nat());
    let z = zero(&theory);
    let even_zero = Term::eq(&Term::app(&even, &z).unwrap(), &Term::true_()).unwrap();
    let even_succ = Term::forall(
        &n,
        &Term::eq(
            &Term::app(&even, &succ(&theory, &n)).unwrap(),
            &Term::app(&odd, &n).unwrap(),
        )
        .unwrap(),
    )
    .unwrap();
    let odd_zero = Term::eq(&Term::app(&odd, &z).unwrap(), &Term::false_()).unwrap();
    let odd_succ = Term::forall(
        &n,
        &Term::eq(
            &Term::app(&odd, &succ(&theory, &n)).unwrap(),
            &Term::app(&even, &n).unwrap(),
        )
        .unwrap(),
    )
    .unwrap();
    let thms = theory
        .new_recfun(&[
            RecFunSpec {
                name: "even".into(),
                rec_arg: 0,
                equations: vec![even_zero, even_succ],
            },
            RecFunSpec {
                name: "odd".into(),
                rec_arg: 0,
                equations: vec![odd_zero, odd_succ],
            },
        ])
        .unwrap();
    assert_eq!(thms.len(), 4);
    assert_eq!(
        thms[1].to_string(),
        "|- forall n : Nat. even (succ n) <-> odd n"
    );
    assert!(theory.is_defined(&"even".into()));
    assert!(theory.is_defined(&"odd".into()));
}

#[test]
fn recursive_function_package_rejects_non_structural_definitions() {
    let (mut theory, _) = nat_theory();
    let unary = Type::fun(nat(), nat());
    theory.new_const("f", unary.clone()).unwrap();
    theory
        .new_const("h", Type::funs(&[unary.clone(), nat()], nat()))
        .unwrap();
    let f = theory.constant("f", unary.clone()).unwrap();
    let h = theory
        .constant("h", Type::funs(&[unary.clone(), nat()], nat()))
        .unwrap();
    let n = Term::free("n", nat());
    let z = zero(&theory);
    let f_of = |t: &Term| Term::app(&f, t).unwrap();
    let base = Term::eq(&f_of(&z), &z).unwrap();
    let spec = |equations: Vec<Term>| RecFunSpec {
        name: "f".into(),
        rec_arg: 0,
        equations,
    };
    let check = |theory: &mut Theory, equations: Vec<Term>, expected: &str| {
        let err = theory.new_recfun(&[spec(equations)]).unwrap_err();
        assert!(err.message.contains(expected), "{err}");
        assert!(!theory.is_defined(&"f".into()));
    };

    // f (succ n) = f (succ n): the call is not smaller.
    let sn = succ(&theory, &n);
    let looping = Term::forall(&n, &Term::eq(&f_of(&sn), &f_of(&sn)).unwrap()).unwrap();
    check(
        &mut theory,
        vec![base.clone(), looping],
        "not structurally smaller",
    );

    // f zero = f zero: no recursive variable at all.
    let base_loop = Term::eq(&f_of(&z), &f_of(&z)).unwrap();
    let ok_step = Term::forall(&n, &Term::eq(&f_of(&sn), &f_of(&n)).unwrap()).unwrap();
    check(
        &mut theory,
        vec![base_loop, ok_step.clone()],
        "not structurally smaller",
    );

    // f (succ n) = f (f n): the outer call's argument is not a variable.
    let nested = Term::forall(&n, &Term::eq(&f_of(&sn), &f_of(&f_of(&n))).unwrap()).unwrap();
    check(
        &mut theory,
        vec![base.clone(), nested],
        "not structurally smaller",
    );

    // f (succ n) = h f n: f escapes unapplied.
    let escaped = Term::forall(
        &n,
        &Term::eq(
            &f_of(&sn),
            &Term::apps(&h, &[f.clone(), n.clone()]).unwrap(),
        )
        .unwrap(),
    )
    .unwrap();
    check(&mut theory, vec![base.clone(), escaped], "occurs unapplied");

    // Missing constructor case.
    check(
        &mut theory,
        vec![base.clone()],
        "no equation for constructor `succ`",
    );

    // Duplicate constructor case.
    check(
        &mut theory,
        vec![base.clone(), base.clone(), ok_step.clone()],
        "two equations for constructor `zero`",
    );

    // Non-variable in a non-recursive position.
    theory
        .new_const("g", Type::funs(&[nat(), nat()], nat()))
        .unwrap();
    let g = theory
        .constant("g", Type::funs(&[nat(), nat()], nat()))
        .unwrap();
    let m = Term::free("m", nat());
    let g_bad = Term::foralls(
        std::slice::from_ref(&n),
        &Term::eq(&Term::apps(&g, &[sn.clone(), z.clone()]).unwrap(), &n).unwrap(),
    )
    .unwrap();
    let g_base = Term::forall(
        &m,
        &Term::eq(&Term::apps(&g, &[z.clone(), m.clone()]).unwrap(), &m).unwrap(),
    )
    .unwrap();
    let err = theory
        .new_recfun(&[RecFunSpec {
            name: "g".into(),
            rec_arg: 0,
            equations: vec![g_base.clone(), g_bad],
        }])
        .unwrap_err();
    assert!(err.message.contains("is not a variable"), "{err}");

    // Repeated pattern variable.
    let g_dup = Term::forall(
        &n,
        &Term::eq(&Term::apps(&g, &[sn.clone(), n.clone()]).unwrap(), &n).unwrap(),
    )
    .unwrap();
    let err = theory
        .new_recfun(&[RecFunSpec {
            name: "g".into(),
            rec_arg: 0,
            equations: vec![g_base.clone(), g_dup],
        }])
        .unwrap_err();
    assert!(err.message.contains("occurs twice"), "{err}");

    // Right side mentions a variable not bound on the left.
    let stray = Term::free("k", nat());
    let g_stray = Term::foralls(
        &[n.clone(), m.clone(), stray.clone()],
        &Term::eq(&Term::apps(&g, &[sn.clone(), m.clone()]).unwrap(), &stray).unwrap(),
    )
    .unwrap();
    let err = theory
        .new_recfun(&[RecFunSpec {
            name: "g".into(),
            rec_arg: 0,
            equations: vec![g_base.clone(), g_stray],
        }])
        .unwrap_err();
    assert!(err.message.contains("not bound on the left"), "{err}");

    // Recursing on a non-datatype argument.
    theory
        .new_const("k", Type::fun(Type::prop(), nat()))
        .unwrap();
    let err = theory
        .new_recfun(&[RecFunSpec {
            name: "k".into(),
            rec_arg: 0,
            equations: vec![],
        }])
        .unwrap_err();
    assert!(err.message.contains("not a datatype"), "{err}");

    // Undeclared constant.
    let err = theory
        .new_recfun(&[RecFunSpec {
            name: "nope".into(),
            rec_arg: 0,
            equations: vec![],
        }])
        .unwrap_err();
    assert!(err.message.contains("not declared"), "{err}");
}

#[test]
fn recursive_equations_compute_by_rewriting() {
    let (mut theory, _) = nat_theory();
    let equations = declare_add(&mut theory);
    let one = succ(&theory, &zero(&theory));
    // add (succ zero) zero = succ (add zero zero) = succ zero
    let step = hol_kernel::spec(&equations[1], &[zero(&theory), zero(&theory)]).unwrap();
    let base = hol_kernel::spec(&equations[0], &[zero(&theory)]).unwrap();
    let succ_base =
        hol_kernel::mk_comb(&hol_kernel::refl(&common::succ_fn(&theory)).unwrap(), &base).unwrap();
    let result = hol_kernel::trans(&step, &succ_base).unwrap();
    assert_eq!(
        result.concl(),
        &Term::eq(&add(&theory, &one, &zero(&theory)), &one).unwrap()
    );
    assert!(result.tags().is_empty());
}
