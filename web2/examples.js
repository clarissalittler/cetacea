// Examples offered by the load menu. Each is a complete file.

export const EXAMPLES = [
  {
    name: "Getting started: conjunction",
    source: `-- Cetacea checks proofs as you type.
-- Put the cursor on a proof line to see the goal at that point.

theorem and_comm (P Q : Prop) : P /\\ Q -> Q /\\ P := by
  intro h
  split
  exact h.right
  exact h.left

-- Try finishing this one. Press "Suggest a tactic" when stuck.
theorem and_intro (P Q : Prop) : P -> Q -> P /\\ Q := by
  intro hp
  intro hq
  sorry
`,
  },
  {
    name: "Natural deduction: implication and disjunction",
    source: `import ../std/prelude.ctea

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

-- Negation is implication to False.
theorem modus_tollens (P Q : Prop) : (P -> Q) -> not Q -> not P := by
  intro hpq
  intro hnq
  intro hp
  apply hnq
  apply hpq
  exact hp
`,
  },
  {
    name: "A fallacy, caught",
    source: `-- Affirming the consequent is not valid. The checker says why.

theorem affirming_the_consequent (P Q : Prop) : (P -> Q) -> Q -> P := by
  intro hpq
  intro hq
  exact hq
`,
  },
  {
    name: "Quantifiers",
    source: `import ../std/prelude.ctea

sort Person

const alice : Person
pred Happy(Person)
pred Rich(Person)

theorem everyone_alice : (forall x : Person, Happy(x)) -> Happy(alice) := by
  intro h
  exact h alice

theorem someone_happy : Happy(alice) -> exists x : Person, Happy(x) := by
  intro h
  exists alice
  exact h

theorem exists_weaken
  : (exists x : Person, Happy(x) /\\ Rich(x)) -> exists x : Person, Happy(x) := by
  intro h
  obtain w hw := h
  exists w
  exact hw.left

theorem use_the_library
  : (forall x : Person, Happy(x) -> Rich(x))
    -> (forall x : Person, Happy(x))
    -> forall x : Person, Rich(x) := by
  exact forall_mono {A := Person; P := Happy; Q := Rich}
`,
  },
  {
    name: "Sets",
    source: `import ../std/prelude.ctea

sort Student

pred TakesCS(Student)
pred TakesMath(Student)

def CS : Set Student := { x : Student | TakesCS(x) }
def Math : Set Student := { x : Student | TakesMath(x) }

theorem cs_in_union : CS subset union(CS, Math) := by
  intro x
  intro hx
  left
  exact hx

theorem inter_comm_here (T : Type) (A B : Set T) : inter(A, B) = inter(B, A) := by
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
    name: "Induction on natural numbers",
    source: `logic fol_nat
import ../std/prelude.ctea

-- Numerals and + * - <= are built in; refl computes closed arithmetic.
theorem two_plus_two : 2 + 2 = 4 := by
  refl

theorem add_zero (n : Nat) : n + 0 = n := by
  induction n with
  | zero =>
      refl
  | succ k ih =>
      simp
      exact ih

-- A chain of equalities, each step justified.
theorem chain (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  calc a = b := h1
    _ = c := h2

-- This statement is false; the checker finds the counterexample.
theorem wrong (n m : Nat) : n + m = n := by
  refl
`,
  },
  {
    name: "Classical reasoning",
    source: `-- Constructive mode rejects excluded middle; classical mode allows it.

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
];
