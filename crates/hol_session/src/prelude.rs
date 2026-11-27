//! The Nat prelude: `Nat` as a datatype, arithmetic by structural
//! recursion, `le` as an opaque definition, and the computation lemmas
//! that `simp` uses, proved here with the ordinary tactics. The base
//! environment is built once per thread and cloned for each session.

use std::cell::RefCell;

use hol_elab::{ConstInfo, Env, SymbolKind};
use hol_kernel::{CtorSpec, DatatypeSpec, Name, Type};
use hol_syntax::{Mode, Tier};

use crate::{Options, Session, VirtualFs};

/// Arithmetic and ordering, in the surface language. Names under `Nat.`
/// are the simplification lemmas; the user-facing library restates the
/// familiar names in `lib/nat.ctea`.
pub const NAT_PRELUDE_SOURCE: &str = "\
defrec add (n m : Nat) : Nat
| zero => m
| succ k => succ(add(k, m))

defrec mul (n m : Nat) : Nat
| zero => 0
| succ k => add(m, mul(k, m))

defrec pred (n : Nat) : Nat
| zero => 0
| succ k => k

defrec sub (n m : Nat) : Nat on m
| zero => n
| succ k => pred(sub(n, k))

def le (n m : Nat) : Prop := sub(n, m) = 0
def lt (n m : Nat) : Prop := le(succ(n), m)

theorem Nat.add_zero_right_lemma (n : Nat) : add(n, 0) = n := by
  induction n with
  | zero =>
      refl
  | succ k ih =>
      simp
      exact ih

theorem Nat.add_succ_right_lemma (n m : Nat) : add(n, succ(m)) = succ(add(n, m)) := by
  induction n with
  | zero =>
      refl
  | succ k ih =>
      simp
      exact ih

theorem Nat.mul_zero_right_lemma (n : Nat) : mul(n, 0) = 0 := by
  induction n with
  | zero =>
      refl
  | succ k ih =>
      simp
      exact ih

theorem Nat.add_assoc_lemma (n m k : Nat) : add(add(n, m), k) = add(n, add(m, k)) := by
  induction n with
  | zero =>
      refl
  | succ n0 ih =>
      simp
      exact ih

theorem Nat.add_comm_lemma (n m : Nat) : add(n, m) = add(m, n) := by
  induction n with
  | zero =>
      refl
  | succ k ih =>
      simp
      exact ih

theorem Nat.add_left_comm_lemma (a b c : Nat) : add(a, add(b, c)) = add(b, add(a, c)) := by
  rewrite <- Nat.add_assoc_lemma {n := a; m := b; k := c}
  rewrite -> Nat.add_comm_lemma {n := a; m := b}
  rewrite -> Nat.add_assoc_lemma {n := b; m := a; k := c}
  refl

theorem Nat.mul_succ_right_lemma (n m : Nat) : mul(n, succ(m)) = add(n, mul(n, m)) := by
  induction n with
  | zero =>
      refl
  | succ k ih =>
      simp
      rewrite -> ih
      exact Nat.add_left_comm_lemma

theorem Nat.sub_zero_left_lemma (n : Nat) : sub(0, n) = 0 := by
  induction n with
  | zero =>
      refl
  | succ k ih =>
      simp
      rewrite -> ih
      refl

theorem Nat.sub_succ_succ_lemma (n m : Nat) : sub(succ(n), succ(m)) = sub(n, m) := by
  induction m with
  | zero =>
      refl
  | succ k ih =>
      simp at ih
      simp
      rewrite -> ih
      refl

theorem Nat.le_zero_lemma (m : Nat) : le(0, m) <-> True := by
  unfold le
  simp
  split
  intro h
  trivial
  intro h
  refl

theorem Nat.le_succ_zero_lemma (n : Nat) : le(succ(n), 0) <-> False := by
  unfold le
  simp
  split
  intro h
  exact h
  intro h
  exact h

theorem Nat.le_succ_succ_lemma (n m : Nat) : le(succ(n), succ(m)) <-> le(n, m) := by
  unfold le
  simp
  split
  intro h
  exact h
  intro h
  exact h
";

/// Lemmas registered as `simp` rules, in order.
const SIMP_LEMMAS: &[&str] = &[
    "Nat.add_zero_right_lemma",
    "Nat.add_succ_right_lemma",
    "Nat.mul_zero_right_lemma",
    "Nat.mul_succ_right_lemma",
    "Nat.sub_zero_left_lemma",
    "Nat.sub_succ_succ_lemma",
    "Nat.le_zero_lemma",
    "Nat.le_succ_zero_lemma",
    "Nat.le_succ_succ_lemma",
];

thread_local! {
    static BASE_ENV: RefCell<Option<Env>> = const { RefCell::new(None) };
}

/// The environment every session starts from: the set prelude plus Nat.
pub fn base_env() -> Env {
    BASE_ENV.with(|cell| {
        if let Some(env) = cell.borrow().as_ref() {
            return env.clone();
        }
        let env = build_base_env();
        *cell.borrow_mut() = Some(env.clone());
        env
    })
}

fn build_base_env() -> Env {
    let mut env = hol_elab::new_env();
    install_nat(&mut env).expect("the Nat prelude installs");
    env
}

fn install_nat(env: &mut Env) -> Result<(), String> {
    let nat = Type::con("Nat", vec![]);
    let info = env
        .theory_mut()
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
                    args: vec![nat.clone()],
                },
            ],
        })
        .map_err(|e| e.to_string())?;
    env.add_sort(Name::new("Nat"), 0);
    for ctor in &info.ctors {
        env.add_constant(ConstInfo {
            name: ctor.name.clone(),
            ty: Type::funs(&ctor.args, nat.clone()),
            kind: SymbolKind::Ctor,
            arity: ctor.args.len(),
            span: None,
            min_tier: Tier::FolNat,
        });
    }

    // Register the simp lemmas by name first, so each one is available
    // to the proofs that follow it.
    for lemma in SIMP_LEMMAS {
        env.add_simp_lemma(Name::new(lemma));
    }

    // Elaborate and prove the rest with the ordinary machinery.
    let saved_tier = env.tier;
    let saved_mode = env.mode;
    env.tier = Tier::Hol;
    env.mode = Mode::Constructive;
    env.importing = true;
    let fs = VirtualFs::default();
    let mut session = Session::with_env(&fs, Options::default(), env.clone());
    session.check_source(Some("prelude/nat.ctea"), NAT_PRELUDE_SOURCE, true);
    let (checked_env, diagnostics) = session.into_parts();
    if let Some(error) = diagnostics
        .iter()
        .find(|d| d.severity == crate::Severity::Error)
    {
        return Err(format!("Nat prelude: {}", error.render()));
    }
    *env = checked_env;
    env.tier = saved_tier;
    env.mode = saved_mode;
    env.importing = false;

    // Arithmetic symbols need the fol_nat tier; `le` computes by lemmas.
    for name in ["add", "mul", "pred", "sub", "le", "lt"] {
        if let Some(info) = env.constant_by_exact_name(&Name::new(name)).cloned() {
            env.add_constant(ConstInfo {
                min_tier: Tier::FolNat,
                ..info
            });
        }
    }
    env.set_opaque(Name::new("le"));
    Ok(())
}
