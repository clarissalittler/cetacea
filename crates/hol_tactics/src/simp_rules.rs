//! Built-in rewrite rules derived from the kernel: datatype no-confusion
//! (`succ n = zero <-> False`, `succ n = succ m <-> n = m`), reflexivity
//! (`x = x <-> True`), and propositional simplifications with `True` and
//! `False`. Every rule is a kernel theorem built from primitive rules.

use hol_elab::Env;
use hol_kernel::{
    and_intro, and_left, and_right, assume, false_elim, forall_intro, iff_intro, imp_elim,
    imp_intro, mk_comb, or_elim, or_left, or_right, refl, sym, true_intro, Name, Term, Thm, Type,
};

fn iff_of(forward: Thm, backward: Thm) -> hol_kernel::Result<Thm> {
    iff_intro(&forward, &backward)
}

/// `|- A <-> False` from `|- A -> False`.
fn negation_as_iff(neg: &Thm) -> hol_kernel::Result<Thm> {
    let (a, _) = neg.concl().dest_imp().expect("implication");
    let a = a.clone();
    let backward = imp_intro(&Term::false_(), &false_elim(&assume(&Term::false_())?, &a)?)?;
    iff_of(neg.clone(), backward)
}

/// Strips leading universal quantifiers with fresh free variables, and
/// returns the variables so the result can be re-generalized.
fn open_foralls(thm: &Thm) -> hol_kernel::Result<(Thm, Vec<Term>)> {
    let mut thm = thm.clone();
    let mut vars = Vec::new();
    let mut taken = thm.concl().free_var_names();
    while let Some(pred) = thm.concl().dest_forall() {
        let (var, _) = pred.open_fresh(&taken).expect("lambda");
        taken.insert(var.as_free().unwrap().0.clone());
        thm = hol_kernel::forall_elim(&thm, &var)?;
        vars.push(var);
    }
    Ok((thm, vars))
}

fn regeneralize(thm: Thm, vars: &[Term]) -> hol_kernel::Result<Thm> {
    let mut current = thm;
    for var in vars.iter().rev() {
        current = forall_intro(var, &current)?;
    }
    Ok(current)
}

/// No-confusion rules for every datatype in the environment.
pub fn datatype_rules(env: &Env) -> Vec<(String, Thm)> {
    let mut out = Vec::new();
    for (name, _) in env.sorts() {
        let Some(info) = env.theory().datatype(name.as_str()) else {
            continue;
        };
        for distinct in &info.distinct {
            if let Ok((opened, vars)) = open_foralls(distinct) {
                if let Ok(iff) = negation_as_iff(&opened) {
                    if let Ok(rule) = regeneralize(iff, &vars) {
                        out.push((format!("{name}.distinct"), rule));
                    }
                    // The mirrored orientation `d ys = c xs <-> False`.
                    if let Ok(flipped) = flip_negation(&opened) {
                        if let Ok(iff) = negation_as_iff(&flipped) {
                            if let Ok(rule) = regeneralize(iff, &vars) {
                                out.push((format!("{name}.distinct'"), rule));
                            }
                        }
                    }
                }
            }
        }
        for ctor in &info.ctors {
            let Some(injective) = &ctor.injective else {
                continue;
            };
            if let Ok(rule) = injectivity_iff(env, &ctor.name, injective) {
                out.push((format!("{}.inj", ctor.name), rule));
            }
        }
    }
    out
}

/// From `|- a = b -> False`, `|- b = a -> False`.
fn flip_negation(neg: &Thm) -> hol_kernel::Result<Thm> {
    let (eq, _) = neg.concl().dest_imp().expect("implication");
    let (a, b) = eq.dest_eq().expect("equation");
    let flipped = Term::eq(b, a)?;
    let derived = imp_elim(neg, &sym(&assume(&flipped)?)?)?;
    imp_intro(&flipped, &derived)
}

/// `forall xs ys. c xs = c ys <-> x1 = y1 /\ ...` from the injectivity
/// principle, whose converse is congruence.
fn injectivity_iff(env: &Env, ctor: &Name, injective: &Thm) -> hol_kernel::Result<Thm> {
    let (opened, vars) = open_foralls(injective)?;
    let (eq, conj) = opened.concl().dest_imp().expect("implication");
    let (lhs, rhs) = eq.dest_eq().expect("equation");
    let conj = conj.clone();
    // Converse: from the conjunction of component equalities, rebuild
    // the constructor equation by congruence.
    let assumed = assume(&conj)?;
    let components = split_conjunction(&assumed, vars.len() / 2)?;
    let (head, _) = lhs.strip_app();
    let mut congruence = refl(head)?;
    for component in &components {
        congruence = mk_comb(&congruence, component)?;
    }
    if congruence.concl() != &Term::eq(lhs, rhs)? {
        return Err(hol_kernel::KernelError::new(
            "injectivity",
            format!("congruence did not rebuild `{}` for `{ctor}`", eq),
        ));
    }
    let _ = env;
    let backward = imp_intro(&conj, &congruence)?;
    let iff = iff_of(opened, backward)?;
    regeneralize(iff, &vars)
}

/// Splits `|- a1 /\ (a2 /\ ...)` into `n` component theorems.
fn split_conjunction(thm: &Thm, n: usize) -> hol_kernel::Result<Vec<Thm>> {
    let mut out = Vec::new();
    let mut current = thm.clone();
    for i in 0..n {
        if i + 1 == n {
            out.push(current.clone());
        } else {
            out.push(and_left(&current)?);
            current = and_right(&current)?;
        }
    }
    Ok(out)
}

/// `forall x : A. (x = x) <-> True`.
pub fn reflexivity_rule() -> hol_kernel::Result<Thm> {
    let x = Term::free("x", Type::var("A"));
    let eq = Term::eq(&x, &x)?;
    let forward = imp_intro(&eq, &true_intro())?;
    let backward = imp_intro(&Term::true_(), &refl(&x)?)?;
    forall_intro(&x, &iff_of(forward, backward)?)
}

/// Propositional simplifications with `True` and `False`.
pub fn propositional_rules() -> hol_kernel::Result<Vec<(String, Thm)>> {
    let p = Term::free("P", Type::prop());
    let t = Term::true_();
    let f = Term::false_();
    let hp = assume(&p)?;
    let ht = true_intro();
    let mut out = Vec::new();

    // True /\ P <-> P
    let lhs = Term::and(&t, &p)?;
    let forward = imp_intro(&lhs, &and_right(&assume(&lhs)?)?)?;
    let backward = imp_intro(&p, &and_intro(&ht, &hp)?)?;
    out.push((
        "and_true_left".to_string(),
        forall_intro(&p, &iff_of(forward, backward)?)?,
    ));

    // P /\ True <-> P
    let lhs = Term::and(&p, &t)?;
    let forward = imp_intro(&lhs, &and_left(&assume(&lhs)?)?)?;
    let backward = imp_intro(&p, &and_intro(&hp, &ht)?)?;
    out.push((
        "and_true_right".to_string(),
        forall_intro(&p, &iff_of(forward, backward)?)?,
    ));

    // False /\ P <-> False, P /\ False <-> False
    for (name, lhs, take_left) in [
        ("and_false_left", Term::and(&f, &p)?, true),
        ("and_false_right", Term::and(&p, &f)?, false),
    ] {
        let assumed = assume(&lhs)?;
        let falsity = if take_left {
            and_left(&assumed)?
        } else {
            and_right(&assumed)?
        };
        let forward = imp_intro(&lhs, &falsity)?;
        let backward = imp_intro(&f, &false_elim(&assume(&f)?, &lhs)?)?;
        out.push((
            name.to_string(),
            forall_intro(&p, &iff_of(forward, backward)?)?,
        ));
    }

    // False \/ P <-> P, P \/ False <-> P
    for (name, lhs, false_left) in [
        ("or_false_left", Term::or(&f, &p)?, true),
        ("or_false_right", Term::or(&p, &f)?, false),
    ] {
        let assumed = assume(&lhs)?;
        let from_false = false_elim(&assume(&f)?, &p)?;
        let forward_body = if false_left {
            or_elim(&assumed, &from_false, &hp)?
        } else {
            or_elim(&assumed, &hp, &from_false)?
        };
        let forward = imp_intro(&lhs, &forward_body)?;
        let backward_body = if false_left {
            or_right(&f, &hp)?
        } else {
            or_left(&hp, &f)?
        };
        let backward = imp_intro(&p, &backward_body)?;
        out.push((
            name.to_string(),
            forall_intro(&p, &iff_of(forward, backward)?)?,
        ));
    }

    // True \/ P <-> True, P \/ True <-> True
    for (name, lhs, true_left) in [
        ("or_true_left", Term::or(&t, &p)?, true),
        ("or_true_right", Term::or(&p, &t)?, false),
    ] {
        let forward = imp_intro(&lhs, &ht)?;
        let backward_body = if true_left {
            or_left(&ht, &p)?
        } else {
            or_right(&p, &ht)?
        };
        let backward = imp_intro(&t, &backward_body)?;
        out.push((
            name.to_string(),
            forall_intro(&p, &iff_of(forward, backward)?)?,
        ));
    }

    // (True -> P) <-> P
    let lhs = Term::imp(&t, &p)?;
    let forward = imp_intro(&lhs, &imp_elim(&assume(&lhs)?, &ht)?)?;
    let backward = imp_intro(&p, &imp_intro(&t, &hp)?)?;
    out.push((
        "imp_true_left".to_string(),
        forall_intro(&p, &iff_of(forward, backward)?)?,
    ));

    // (P -> True) <-> True
    let lhs = Term::imp(&p, &t)?;
    let forward = imp_intro(&lhs, &ht)?;
    let backward = imp_intro(&t, &imp_intro(&p, &ht)?)?;
    out.push((
        "imp_true_right".to_string(),
        forall_intro(&p, &iff_of(forward, backward)?)?,
    ));

    // (False -> P) <-> True
    let lhs = Term::imp(&f, &p)?;
    let forward = imp_intro(&lhs, &ht)?;
    let backward = imp_intro(&t, &imp_intro(&f, &false_elim(&assume(&f)?, &p)?)?)?;
    out.push((
        "imp_false_left".to_string(),
        forall_intro(&p, &iff_of(forward, backward)?)?,
    ));

    // not True <-> False   (True -> False <-> False)
    let lhs = Term::not(&t)?;
    let forward = imp_intro(&lhs, &imp_elim(&assume(&lhs)?, &ht)?)?;
    let backward = imp_intro(&f, &false_elim(&assume(&f)?, &lhs)?)?;
    out.push(("not_true".to_string(), iff_of(forward, backward)?));

    // not False <-> True
    let lhs = Term::not(&f)?;
    let forward = imp_intro(&lhs, &ht)?;
    let backward = imp_intro(&t, &imp_intro(&f, &assume(&f)?)?)?;
    out.push(("not_false".to_string(), iff_of(forward, backward)?));

    Ok(out)
}
