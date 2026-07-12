// Bundled example sources for the Cetacea browser UI.
// Generated from the repository files listed in each entry's `path`.
// Import lines are rewritten from on-disk relative paths (e.g.
// `import ../../../std/prelude.ctea`) to the virtual `std/...` paths that
// the wasm module registers, so the examples check in the browser.

window.CETACEA_EXAMPLES = [
  {
    id: "hol-finite",
    label: "HOL Finite: cardinality of One",
    path: "docs/hol/examples/finite_one.ctea",
    source: `import std/hol/finite@1 as F

mode constructive

data One
| only

theorem one_has_card :
  F.HasCard(F.cons(only, F.nil), succ(0)) := by
  apply F.has_card_intro {
    A := One;
    xs := F.cons(only, F.nil);
    n := succ(0)
  }
  apply (F.nodup_cons {
    A := One;
    h := only;
    t := (F.nil : F.List One)
  }).right
  split
  intro member
  exact F.member_nil {A := One; x := only} member
  exact F.nodup_nil {A := One}
  rewrite -> F.length_cons {
    A := One;
    h := only;
    t := (F.nil : F.List One)
  }
  rewrite -> F.length_nil {A := One}
  refl
  intro x
  induction x with
  | only =>
      have heq : only = only := by
        refl
      apply (F.member_cons {
        A := One;
        x := only;
        h := only;
        t := (F.nil : F.List One)
      }).right
      left
      exact heq
`,
  },
  {
    id: "hol-list",
    label: "HOL List: length of append",
    path: "docs/hol/examples/list_length_append.ctea",
    source: `import std/hol/list@1 as L

mode constructive

theorem length_append_from_surface
  (A : Type) (xs ys : L.List A) :
  L.length(L.append(xs, ys)) = add(L.length(xs), L.length(ys)) := by
  apply L.list_induction {
    A := A;
    P := fun ws : L.List A =>
      L.length(L.append(ws, ys)) =
        add(L.length((ws : L.List A)), L.length(ys));
    xs := xs
  }
  rewrite -> L.append_nil_left {A := A; xs := ys}
  rewrite -> L.length_nil {A := A}
  refl
  intro h
  intro t
  intro ih
  rewrite -> L.append_cons {A := A; h := h; t := t; ys := ys}
  rewrite -> L.length_cons {
    A := A;
    h := h;
    t := L.append(t, ys)
  }
  rewrite -> L.length_cons {A := A; h := h; t := t}
  rewrite -> ih
  refl
`,
  },
  {
    id: "prop",
    label: "Propositional logic",
    path: "examples/prop.ctea",
    source: `mode constructive

theorem and_comm (P Q : Prop) : P /\\ Q -> Q /\\ P := by
  intro h
  split
  exact h.right
  exact h.left

theorem imp_trans (P Q R : Prop) : (P -> Q) -> (Q -> R) -> P -> R := by
  intro hpq
  intro hqr
  intro hp
  apply hqr
  apply hpq
  exact hp

theorem or_comm (P Q : Prop) : P \\/ Q -> Q \\/ P := by
  intro h
  cases h with
  | left hp =>
      right
      exact hp
  | right hq =>
      left
      exact hq

theorem not_not_em (P : Prop) : not not (P \\/ not P) := by
  intro h
  apply h
  right
  intro p
  apply h
  left
  exact p

mode classical

theorem em (P : Prop) : P \\/ not P := by
  by_cases h : P
  left
  exact h
  right
  exact h

theorem dne (P : Prop) : not not P -> P := by
  intro hnn
  by_contra hn
  apply hnn
  exact hn

`,
  },
  {
    id: "fol",
    label: "First-order logic",
    path: "examples/fol.ctea",
    source: `mode constructive

sort Person

const alice : Person

func mother : Person -> Person

pred Student(Person)
pred Happy(Person)

def HappyMother (x : Person) : Prop := Happy(mother(x))

theorem student_exists : Student(alice) -> exists x : Person, Student(x) := by
  intro h
  exists alice
  exact h

theorem happy_mother : Happy(mother(alice)) -> Happy(mother(alice)) := by
  intro h
  exact h

theorem alice_eq_refl : alice = alice := by
  refl

theorem mother_eq_refl : mother(alice) = mother(alice) := by
  refl

theorem rewrite_happy
  : alice = mother(alice) -> Happy(alice) -> Happy(mother(alice)) := by
  intro h
  intro ha
  rewrite h
  exact ha

theorem happy_mother_def_elim : HappyMother(alice) -> Happy(mother(alice)) := by
  intro h
  exact h

theorem happy_mother_def_intro : Happy(mother(alice)) -> HappyMother(alice) := by
  intro h
  unfold HappyMother
  exact h

theorem happy_mother_def_simp : Happy(mother(alice)) -> HappyMother(alice) := by
  intro h
  simp
  exact h

theorem forall_and_left
  (P : Person -> Prop)
  (Q : Person -> Prop)
  : (forall x : Person, P(x) /\\ Q(x)) -> forall x : Person, P(x) := by
  intro h
  intro x
  exact (h x).left

theorem exists_and_left
  (P : Person -> Prop)
  (Q : Person -> Prop)
  : (exists x : Person, P(x) /\\ Q(x)) -> exists x : Person, P(x) := by
  intro h
  cases h with
  | intro x hx =>
      exists x
      exact hx.left

theorem not_exists_to_forall_not
  (P : Person -> Prop)
  : not (exists x : Person, P(x)) -> forall x : Person, not P(x) := by
  intro h
  intro x
  intro hp
  apply h
  exists x
  exact hp

theorem forall_apply
  (P : Person -> Prop)
  (Q : Person -> Prop)
  (a : Person)
  : (forall x : Person, P(x) -> Q(x)) -> P(a) -> Q(a) := by
  intro h
  intro hp
  apply h
  exact hp

theorem forall_self
  (A : Type)
  (P : A -> Prop)
  : (forall x : A, P(x)) -> forall x : A, P(x) := by
  intro h
  exact h

theorem use_forall_self
  (P : Person -> Prop)
  : (forall x : Person, P(x)) -> forall x : Person, P(x) := by
  exact forall_self

theorem use_forall_self_explicit
  (P : Person -> Prop)
  : (forall x : Person, P(x)) -> forall x : Person, P(x) := by
  exact forall_self {A := Person; P := P}
`,
  },
  {
    id: "set_nat",
    label: "Sets and natural numbers",
    path: "examples/set_nat.ctea",
    source: `mode constructive

sort Person

const alice : Person

axiom set_ext
  (T : Type)
  (A B : Set T)
  : (forall x : T, x in A <-> x in B) -> A = B

theorem add_zero_left (n : Nat) : add(0, n) = n := by
  simp
  refl

theorem add_succ_left (n m : Nat) : add(succ(n), m) = succ(add(n, m)) := by
  simp
  refl

theorem add_zero_right (n : Nat) : add(n, 0) = n := by
  simp
  refl

theorem singleton_member : alice in singleton(alice) := by
  simp
  refl

theorem empty_member_implies_false
  (T : Type)
  (x : T)
  : x in empty(T) -> False := by
  intro h
  exact h

theorem inter_subset_left
  (T : Type)
  (A B : Set T)
  : inter(A, B) subset A := by
  simp
  intro x
  intro hx
  exact hx.left

theorem subset_refl
  (T : Type)
  (A : Set T)
  : A subset A := by
  simp
  intro x
  intro hx
  exact hx

theorem union_subset
  (T : Type)
  (A B C : Set T)
  : A subset C -> B subset C -> union(A, B) subset C := by
  intro hAC
  intro hBC
  simp
  intro x
  intro hx
  cases hx with
  | left hxA =>
      apply hAC
      exact hxA
  | right hxB =>
      apply hBC
      exact hxB

theorem inter_comm
  (T : Type)
  (A B : Set T)
  : inter(A, B) = inter(B, A) := by
  apply set_ext
  intro x
  simp
  split
  intro hx
  split
  exact hx.right
  exact hx.left
  intro hx
  split
  exact hx.right
  exact hx.left
`,
  },
  {
    id: "cs250_01",
    label: "CS250 - 01 Propositional logic",
    path: "docs/cs250/code/01_propositional.ctea",
    source: `-- Companion file for docs/cs250/01_propositional.md.
-- Each theorem here corresponds to a snippet in the tutorial.

import std/prelude.ctea
mode constructive

theorem and_intro_demo (P Q : Prop) : P -> Q -> P /\\ Q := by
  intro hp
  intro hq
  split
  exact hp
  exact hq

theorem and_elim_left_demo (P Q : Prop) : P /\\ Q -> P := by
  intro h
  exact h.left

theorem or_intro_left_demo (P Q : Prop) : P -> P \\/ Q := by
  intro hp
  left
  exact hp

theorem or_elim_demo (P Q R : Prop) : (P -> R) -> (Q -> R) -> P \\/ Q -> R := by
  intro hpr
  intro hqr
  intro hpq
  cases hpq with
  | left hp =>
      apply hpr
      exact hp
  | right hq =>
      apply hqr
      exact hq

theorem imp_intro_demo (P Q : Prop) : P -> P -> Q -> P := by
  intro hp1
  intro hp2
  intro hq
  exact hp1

theorem modus_tollens_demo (P Q : Prop) : (P -> Q) -> not Q -> not P := by
  intro hpq
  intro hnq
  intro hp
  apply hnq
  apply hpq
  exact hp

-- Easy direction of de Morgan: constructively provable.
theorem demorgan_easy (P Q : Prop) : not P \\/ not Q -> not (P /\\ Q) := by
  intro h
  intro hpq
  cases h with
  | left hnp =>
      apply hnp
      exact hpq.left
  | right hnq =>
      apply hnq
      exact hpq.right

-- Easy direction of the OR de Morgan, also constructive.
theorem demorgan_or (P Q : Prop) : not (P \\/ Q) -> not P /\\ not Q := by
  intro h
  split
  intro hp
  apply h
  left
  exact hp
  intro hq
  apply h
  right
  exact hq

-- Module 2 Exercise 7: implication distributes over conjunction.
-- Applying \`and_left\`/\`and_right\` leaves the conjunction as a subgoal.
-- Cetacea infers the hidden theorem parameters from \`h\`'s conclusion.
theorem imp_dist_and_fwd (P Q R : Prop) : (P -> Q /\\ R) -> (P -> Q) /\\ (P -> R) := by
  intro h
  split
  -- prove P -> Q
  intro hp
  apply and_left
  apply h
  exact hp
  -- prove P -> R
  intro hp
  apply and_right
  apply h
  exact hp

theorem imp_dist_and_bwd (P Q R : Prop) : (P -> Q) /\\ (P -> R) -> P -> Q /\\ R := by
  intro h
  intro hp
  split
  apply h.left
  exact hp
  apply h.right
  exact hp

mode classical

-- Hard direction of de Morgan: needs classical logic.
theorem demorgan_hard (P Q : Prop) : not (P /\\ Q) -> not P \\/ not Q := by
  intro h
  by_contra hn
  apply h
  split
  by_contra hnp
  apply hn
  left
  exact hnp
  by_contra hnq
  apply hn
  right
  exact hnq

theorem em_demo (P : Prop) : P \\/ not P := by
  by_cases h : P
  left
  exact h
  right
  exact h
`,
  },
  {
    id: "cs250_03",
    label: "CS250 - 03 First-order logic",
    path: "docs/cs250/code/03_first_order.ctea",
    source: `-- Companion file for docs/cs250/03_first_order.md.

import std/prelude.ctea
mode constructive

sort Person

const alice : Person
const bob : Person

func mother : Person -> Person

pred Student(Person)
pred Knows(Person, Person)

theorem use_forall
  (P : Person -> Prop)
  : (forall x : Person, P(x)) -> P(alice) := by
  intro h
  exact h alice

theorem forall_self
  (A : Type)
  (P : A -> Prop)
  : (forall x : A, P(x)) -> forall x : A, P(x) := by
  intro h
  intro x
  exact h x

theorem alice_exists : Student(alice) -> exists x : Person, Student(x) := by
  intro h
  exists alice
  exact h

theorem ex_proj
  (P Q : Person -> Prop)
  : (exists x : Person, P(x) /\\ Q(x)) -> exists x : Person, P(x) := by
  intro h
  cases h with
  | intro x hx =>
      exists x
      exact hx.left

-- Equality
theorem alice_eq_self : alice = alice := by
  refl

theorem rewrite_demo
  (P : Person -> Prop)
  : alice = bob -> P(alice) -> P(bob) := by
  intro h
  intro hp
  rewrite h
  exact hp

-- For the reverse-direction rewrite we use eq_subst_left from std/eq.ctea
-- directly. (You can also flip with eq_symm and rewrite, but the rewrite
-- syntax doesn't accept a chained proof expression; using a helper
-- theorem is easier.)
theorem rewrite_back
  (P : Person -> Prop)
  : alice = bob -> P(bob) -> P(alice) := by
  intro h
  intro hp
  apply eq_subst_left {A := Person; P := P; x := alice; y := bob}
  exact h
  exact hp

-- Forall + Exists chaining: a flavor of Module 4 Exercise 6.
-- "If for every x there is a witness y with R(x, y), and we know R is
-- propagated by Q, then for every x there's a y with Q(x, y)."
theorem forall_exists_chain
  (A : Type)
  (R Q : A -> A -> Prop)
  : (forall x : A, exists y : A, R(x, y))
    -> (forall x : A, forall y : A, R(x, y) -> Q(x, y))
    -> forall x : A, exists y : A, Q(x, y) := by
  intro hex
  intro himp
  intro x
  cases hex x with
  | intro y hxy =>
      exists y
      apply himp x y
      exact hxy

mode classical

-- The "harder" direction of the de Morgan law for forall:
-- not (forall x, P(x)) -> exists x, not P(x).
theorem not_forall_to_exists_not
  (A : Type)
  (P : A -> Prop)
  : not (forall x : A, P(x)) -> exists x : A, not P(x) := by
  intro h
  by_contra hn
  apply h
  intro x
  by_contra hpx
  apply hn
  exists x
  exact hpx
`,
  },
  {
    id: "cs250_04",
    label: "CS250 - 04 Induction on Nat",
    path: "docs/cs250/code/04_induction_nat.ctea",
    source: `-- Companion file for docs/cs250/04_induction_nat.md.

import std/prelude.ctea
mode constructive

theorem add_zero_right_demo (n : Nat) : add(n, 0) = n := by
  simp
  refl

theorem add_comm_demo (n m : Nat) : add(n, m) = add(m, n) := by
  induction n with
  | zero =>
      simp
      refl
  | succ n0 ih =>
      simp
      rewrite ih
      refl

defrec double (n : Nat) : Nat
| zero => 0
| succ k rec => succ(succ(rec))

theorem double_succ_demo (n : Nat)
  : double(succ(n)) = succ(succ(double(n))) := by
  simp
  refl

-- Same proof, but using the textbook's right-recursive \`+\`.
func myadd : Nat -> Nat -> Nat

axiom myadd_zero_right (n : Nat) : myadd(n, 0) = n
axiom myadd_succ_right (n m : Nat) : myadd(n, succ(m)) = succ(myadd(n, m))

theorem myadd_succ_right_rev (n m : Nat)
  : succ(myadd(n, m)) = myadd(n, succ(m)) := by
  rewrite myadd_succ_right {n := n; m := m}
  refl

theorem myadd_zero_n (n : Nat) : myadd(0, n) = n := by
  induction n with
  | zero =>
      exact myadd_zero_right
  | succ k ih =>
      rewrite myadd_succ_right_rev {n := 0; m := k}
      rewrite ih
      refl

-- Module 4 Exercise 11: \`0 * n = 0\`.
-- Cetacea's built-in multiplication computes this directly.
theorem zero_mul_n_builtin (n : Nat) : mul(0, n) = 0 := by
  simp
  refl

-- Same exercise, but using the textbook's right-recursive multiplication.
func mymul : Nat -> Nat -> Nat

axiom mymul_zero_right (n : Nat) : mymul(n, 0) = 0
axiom mymul_succ_right (n m : Nat)
  : mymul(n, succ(m)) = add(mymul(n, m), n)

theorem zero_mymul_n (n : Nat) : mymul(0, n) = 0 := by
  induction n with
  | zero =>
      exact mymul_zero_right
  | succ k ih =>
      -- Goal: mymul(0, succ(k)) = 0.
      -- Strategy:
      --   mymul(0, succ(k)) = add(mymul(0, k), 0)     by mymul_succ_right
      --                     = mymul(0, k)             by add_zero_right
      --                     = 0                       by ih
      -- We chain via eq_trans from std/eq.ctea.
      apply eq_trans {A := Nat; x := mymul(0, succ(k)); y := mymul(0, k); z := 0}
      apply eq_trans {A := Nat; x := mymul(0, succ(k)); y := add(mymul(0, k), 0); z := mymul(0, k)}
      exact mymul_succ_right
      exact add_zero_right
      exact ih
`,
  },
  {
    id: "cs250_05",
    label: "CS250 - 05 Sets",
    path: "docs/cs250/code/05_sets.ctea",
    source: `-- Companion file for docs/cs250/05_sets.md.

import std/prelude.ctea
mode constructive

sort Person
sort Color

const alice : Person
const bob : Person
const red : Color
pred Tall(Person)

theorem alice_in_singleton : alice in singleton(alice) := by
  simp
  refl

theorem bob_in_pair : bob in {alice, bob} := by
  simp
  right
  refl

theorem complement_intro_demo
  (A : Set Person)
  : (alice in A -> False) -> alice in compl(A) := by
  intro h
  simp
  exact h

theorem pair_in_product
  : pair(alice, red) in prod(singleton(alice), singleton(red)) := by
  simp
  split
  refl
  refl

def TallSet : Set Person := { x : Person | Tall(x) }

theorem alice_in_tall_set : Tall(alice) -> alice in TallSet := by
  intro h
  simp
  exact h

theorem subset_refl_demo
  (T : Type)
  (A : Set T)
  : A subset A := by
  simp
  intro x
  intro hx
  exact hx

theorem inter_comm_demo
  (T : Type)
  (A B : Set T)
  : inter(A, B) = inter(B, A) := by
  apply set_ext
  intro x
  simp
  split
  intro hx
  split
  exact hx.right
  exact hx.left
  intro hx
  split
  exact hx.right
  exact hx.left

-- Module 1 Exercise 8: distributivity.
theorem inter_union_distrib
  (T : Type)
  (A B C : Set T)
  : inter(A, union(B, C)) = union(inter(A, B), inter(A, C)) := by
  apply set_ext
  intro x
  simp
  split
  intro hx
  cases hx.right with
  | left hxB =>
      left
      split
      exact hx.left
      exact hxB
  | right hxC =>
      right
      split
      exact hx.left
      exact hxC
  intro hx
  cases hx with
  | left hxAB =>
      split
      exact hxAB.left
      left
      exact hxAB.right
  | right hxAC =>
      split
      exact hxAC.left
      right
      exact hxAC.right

-- A finitary version of "A ⊆ B → 𝒫(A) ⊆ 𝒫(B)": every subset of A is
-- also a subset of B. \`apply subset_trans\` infers the intermediate set
-- from the local hypotheses.
theorem subsets_carry
  (A B C : Set Person)
  : A subset B -> C subset A -> C subset B := by
  intro hAB
  intro hCA
  apply subset_trans
  exact hCA
  exact hAB

theorem powerset_mono_demo
  (A B : Set Person)
  : A subset B -> powerset(A) subset powerset(B) := by
  intro hAB
  simp
  intro S
  intro hSA
  intro x
  intro hx
  apply hAB
  apply hSA
  exact hx
`,
  },
  {
    id: "cs250_06",
    label: "CS250 - 06 Relations",
    path: "docs/cs250/code/06_relations.ctea",
    source: `-- Companion file for docs/cs250/06_relations.md.

import std/prelude.ctea
mode constructive

sort Thing

def Reflexive (A : Type) (R : A -> A -> Prop) : Prop := forall x : A, R(x, x)

def Symmetric (A : Type) (R : A -> A -> Prop) : Prop := forall x y : A, R(x, y) -> R(y, x)

def Transitive (A : Type) (R : A -> A -> Prop) : Prop := forall x y z : A, R(x, y) -> R(y, z) -> R(x, z)

theorem refl_self
  (A : Type)
  (R : A -> A -> Prop)
  (a : A)
  : Reflexive(R) -> R(a, a) := by
  intro hrefl
  exact hrefl a

theorem eq_is_refl (A : Type) (x : A) : x = x := by
  refl

theorem equality_relation_reflexive : Reflexive(fun x y : Thing => x = y) := by
  simp
  intro x
  refl

-- "If R is symmetric and transitive AND there's some witness y with
-- R(x, y), then R(x, x)." The flawed argument from Module 1 §6 is
-- valid IF you know there's a witness.
theorem refl_from_witness
  (A : Type)
  (R : A -> A -> Prop)
  (x : A)
  : Symmetric(R)
    -> Transitive(R)
    -> (exists y : A, R(x, y))
    -> R(x, x) := by
  intro hsym
  intro htrans
  intro hwit
  cases hwit with
  | intro y hxy =>
      apply htrans x y x
      exact hxy
      apply hsym x y
      exact hxy

-- Equality as the canonical equivalence relation.
theorem eq_refl_demo (A : Type) (x : A) : x = x := by
  refl

theorem eq_sym_demo (A : Type) (x y : A) : x = y -> y = x := by
  exact eq_symm

theorem eq_trans_demo (A : Type) (x y z : A)
  : x = y -> y = z -> x = z := by
  exact eq_trans

-- An axiomatic equivalence relation: a sketch of how you'd handle
-- something like modular congruence.
sort Z

pred Cong(Z, Z)

axiom cong_refl  : forall x : Z, Cong(x, x)

axiom cong_sym
  : forall x : Z, forall y : Z, Cong(x, y) -> Cong(y, x)

axiom cong_trans
  : forall x : Z, forall y : Z, forall z : Z,
      Cong(x, y) -> Cong(y, z) -> Cong(x, z)

-- A small fact: Cong is a transitive symmetric relation, so it's
-- "diagonal-closed": if R(x, y) and R(x, z) then R(y, z).
theorem cong_diag (a b c : Z) : Cong(a, b) -> Cong(a, c) -> Cong(b, c) := by
  intro hab
  intro hac
  apply cong_trans b a c
  apply cong_sym a b
  exact hab
  exact hac
`,
  },
];
