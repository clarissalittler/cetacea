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
    name: "Quantifier order: a counterexample",
    source: `-- Each person can have an admirer without one person admiring everyone.
sort Person

theorem quantifier_swap (Admires : Person -> Person -> Prop)
  : (forall y : Person, exists x : Person, Admires(x, y))
    -> exists x : Person, forall y : Person, Admires(x, y) := by
  intro h
  show_goal

-- Read the finite world in the diagnostic:
-- every column has a true entry, but no row is true everywhere.
-- Reversing the implication gives a valid theorem. Try proving it!
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
    name: "Data types and structural induction",
    source: `logic hol
import ../std/prelude.ctea

-- A data type, a recursive function over it, and structural induction.
data Tree
| leaf
| node(Tree, Nat, Tree)

defrec size (t : Tree) : Nat
| leaf => 0
| node l v r => succ(size(l) + size(r))

defrec mirror (t : Tree) : Tree
| leaf => leaf
| node l v r => node(mirror(r), v, mirror(l))

theorem mirror_size (t : Tree) : size(mirror(t)) = size(t) := by
  induction t with
  | leaf =>
      refl
  | node l v r ihl ihr =>
      simp
      rewrite -> ihl
      rewrite -> ihr
      exact Nat.add_comm_lemma

-- Polymorphic lists come from the library: List A, length, append, map, elem.
theorem length_two (A : Type) (a b : A) : length(cons(a, cons(b, nil))) = 2 := by
  refl

-- Functions are values: extensionality.
theorem add_zero_fun : (fun n : Nat => n + 0) = (fun n : Nat => n) := by
  funext n
  refl
`,
  },
  {
    name: "Graphs: walks, reachability, colouring",
    source: `logic hol

import std/prelude.ctea
import std/graph.ctea

-- A small graph, and what the graph library can say about it.
--
--     a --- b --- c --- d        e --- f
--
-- Six vertices in two pieces: a path of four, and a separate edge.

data Vertex
| a
| b
| c
| d
| e
| f

-- The edges, each listed in both directions.
def Edge (x y : Vertex) : Prop :=
  (x = a /\\ y = b) \\/ (x = b /\\ y = a)
  \\/ (x = b /\\ y = c) \\/ (x = c /\\ y = b)
  \\/ (x = c /\\ y = d) \\/ (x = d /\\ y = c)
  \\/ (x = e /\\ y = f) \\/ (x = f /\\ y = e)

-- Questions about a finite graph with no unknowns are finite checks,
-- so \`decide\` settles them.
theorem edge_undirected : Undirected(Edge) := by
  unfold Undirected
  decide

theorem edge_loopless : Loopless(Edge) := by
  unfold Loopless
  decide

-- To show one vertex reaches another, give the walk.
theorem a_reaches_d : Reachable(Edge, a, d) := by
  unfold Reachable
  exists cons(b, cons(c, cons(d, nil)))
  decide

-- The graph is undirected, so the way back comes for free.
theorem d_reaches_a : Reachable(Edge, d, a) := by
  apply reachable_symm
  exact edge_undirected
  exact a_reaches_d

-- To show a vertex is NOT reachable, no list of walks will do: there
-- are infinitely many. Instead, fence the start in. No edge leaves the
-- set {a, b, c, d}, so a walk from \`a\` can never get out to \`e\`.
def Left : Set Vertex := { x : Vertex | x = a \\/ x = b \\/ x = c \\/ x = d }

theorem left_is_closed : Closed(Edge, Left) := by
  unfold Closed
  decide

theorem a_does_not_reach_e : not Reachable(Edge, a, e) := by
  apply not_reachable_of_closed {S := Left}
  exact left_is_closed
  decide
  decide

theorem not_connected : not Connected(Edge) := by
  intro h
  apply a_does_not_reach_e
  exact h a e

-- Two colours are enough: alternate along the path.
data Color
| red
| blue

defrec color (v : Vertex) : Color
| a => red
| b => blue
| c => red
| d => blue
| e => red
| f => blue

theorem two_colorable : ProperColoring(Edge, color) := by
  unfold ProperColoring
  decide
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
