//! The built-in prelude: ordered pairs as a datatype, and the set
//! operations as ordinary definitions over `Set T`. Installed into every
//! environment before any user file is checked.

use hol_kernel::{CtorSpec, DatatypeSpec, Name, RecFunSpec, Term, Type, MEM, SET_OF};
use hol_syntax::{parse_file, Command, Tier};

use crate::decl::elab_command;
use crate::diag::{Diagnostic, Result};
use crate::env::{ConstInfo, Env, SymbolKind};

/// Set operations, stated in the surface language at the HOL tier.
pub const PRELUDE_SOURCE: &str = "\
def subset (A : Type) (S T : Set A) : Prop := forall x : A, x in S -> x in T
def empty (A : Type) : Set A := { x : A | False }
def univ (A : Type) : Set A := { x : A | True }
def singleton (A : Type) (a : A) : Set A := { x : A | x = a }
def union (A : Type) (S T : Set A) : Set A := { x : A | x in S \\/ x in T }
def inter (A : Type) (S T : Set A) : Set A := { x : A | x in S /\\ x in T }
def diff (A : Type) (S T : Set A) : Set A := { x : A | x in S /\\ not (x in T) }
def compl (A : Type) (S : Set A) : Set A := { x : A | not (x in S) }
def complement (A : Type) (S : Set A) : Set A := compl(S)
def powerset (A : Type) (S : Set A) : Set (Set A) := { T : Set A | T subset S }
def prod (A : Type) (B : Type) (S : Set A) (T : Set B) : Set (Prod A B) := { p : Prod A B | fst(p) in S /\\ snd(p) in T }
";

/// A fresh environment with the prelude installed.
pub fn new_env() -> Env {
    let mut env = Env::bare();
    install(&mut env).expect("the prelude installs");
    env
}

pub fn install(env: &mut Env) -> Result<()> {
    let kernel = |e: hol_kernel::KernelError| Diagnostic::new(Default::default(), e.message);

    // `Set` is a kernel type constructor; membership and set
    // comprehension are kernel primitives.
    env.add_sort(Name::new(hol_kernel::SET), 1);
    let sig = env.theory().signature();
    let mem_ty = sig.const_type(&Name::new(MEM)).unwrap().clone();
    let set_of_ty = sig.const_type(&Name::new(SET_OF)).unwrap().clone();
    env.add_constant(ConstInfo {
        name: Name::new(MEM),
        ty: mem_ty,
        kind: SymbolKind::Builtin,
        arity: 2,
        span: None,
        min_tier: Tier::Fol,
    });
    env.add_constant(ConstInfo {
        name: Name::new(SET_OF),
        ty: set_of_ty,
        kind: SymbolKind::Builtin,
        arity: 1,
        span: None,
        min_tier: Tier::Fol,
    });

    // Ordered pairs.
    let a = Type::var("A");
    let b = Type::var("B");
    let info = env
        .theory_mut()
        .new_datatype(&DatatypeSpec {
            name: "Prod".into(),
            params: vec!["A".into(), "B".into()],
            ctors: vec![CtorSpec {
                name: "pair".into(),
                args: vec![a.clone(), b.clone()],
            }],
        })
        .map_err(kernel)?;
    env.add_sort(Name::new("Prod"), 2);
    let prod_ty = info.generic_type();
    let pair_ty = Type::funs(&[a.clone(), b.clone()], prod_ty.clone());
    env.add_constant(ConstInfo {
        name: Name::new("pair"),
        ty: pair_ty.clone(),
        kind: SymbolKind::Ctor,
        arity: 2,
        span: None,
        min_tier: Tier::Fol,
    });
    for (name, result, pick_first) in [("fst", a.clone(), true), ("snd", b.clone(), false)] {
        let fn_ty = Type::fun(prod_ty.clone(), result.clone());
        env.theory_mut()
            .new_const(name, fn_ty.clone())
            .map_err(kernel)?;
        let f = env.theory().constant(name, fn_ty.clone()).map_err(kernel)?;
        let pair = env
            .theory()
            .constant("pair", pair_ty.clone())
            .map_err(kernel)?;
        let x = Term::free("x", a.clone());
        let y = Term::free("y", b.clone());
        let lhs = Term::app(
            &f,
            &Term::apps(&pair, &[x.clone(), y.clone()]).map_err(kernel)?,
        )
        .map_err(kernel)?;
        let rhs = if pick_first { x.clone() } else { y.clone() };
        let equation =
            Term::foralls(&[x, y], &Term::eq(&lhs, &rhs).map_err(kernel)?).map_err(kernel)?;
        let thms = env
            .theory_mut()
            .new_recfun(&[RecFunSpec {
                name: name.into(),
                rec_arg: 0,
                equations: vec![equation],
            }])
            .map_err(kernel)?;
        env.add_constant(ConstInfo {
            name: Name::new(name),
            ty: fn_ty,
            kind: SymbolKind::Def,
            arity: 1,
            span: None,
            min_tier: Tier::Fol,
        });
        env.add_equations(Name::new(name), thms);
    }

    // Set extensionality is a kernel principle; expose it as the theorem
    // `set_ext` so proofs can `apply set_ext`.
    let ext = env
        .theory()
        .theorem(hol_kernel::SET_EXT)
        .expect("kernel principle")
        .clone();
    env.add_theorem(crate::env::TheoremInfo {
        name: Name::new("set_ext"),
        params: vec![crate::env::ParamInfo::TypeVar(Name::new("A"))],
        statement: ext.concl().clone(),
        thm: ext,
        status: crate::env::Status::Accepted,
        is_imported: true,
        span: None,
    });

    // Set operations, elaborated like any other definitions.
    let saved_tier = env.tier;
    let saved_importing = env.importing;
    env.tier = Tier::Hol;
    env.importing = true;
    let parsed = parse_file(PRELUDE_SOURCE);
    if let Some(error) = parsed.errors.first() {
        return Err(Diagnostic::new(
            error.span,
            format!("prelude parse error: {}", error.message),
        ));
    }
    for command in &parsed.file.commands {
        if let Command::Theorem { .. } | Command::Import { .. } = command {
            continue;
        }
        elab_command(env, command)
            .map_err(|d| Diagnostic::new(d.span, format!("prelude error: {}", d.message)))?;
    }
    env.tier = saved_tier;
    env.importing = saved_importing;
    Ok(())
}
