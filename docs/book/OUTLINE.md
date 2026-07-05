# Proofs, Checked — Full Outline

Twelve chapters, from "what is a proposition?" to strong induction.
Chapters 1–4 are drafted; the rest are planned here so the whole arc is
visible. Each entry lists the Cetacea features the chapter leans on, so
drafting later chapters never requires features the reader hasn't met.

Constructive mode is the default from Chapter 1; classical reasoning is
introduced deliberately in Chapter 3 and treated as an explicit,
opt-in move thereafter.

---

## Chapter 1 — Propositions and How to State Them

*Drafted: [01-propositions.md](01-propositions.md)*

What a proposition is (and isn't), the five connectives, and how to
formalize everyday claims, with truth-value intuition for each
connective. The reader writes and checks a first Cetacea file, proves
conjunctions with `split`, takes them apart with `.left`/`.right`, and
meets implication via `intro`. Ends with the checker's error messages
for four beginner mistakes, read line by line.

**Cetacea features:** file shape, `mode constructive`, `theorem` with
`(P : Prop)` parameters, `intro`, `exact`, `split`, `.left`/`.right`,
`trivial`, `show_goal`, ASCII connectives (Unicode aliases mentioned).

## Chapter 2 — Natural Deduction: Proof as a Game with Rules

*Drafted: [02-natural-deduction.md](02-natural-deduction.md)*

Proofs are derivations built from introduction and elimination rules —
two rules per connective, one tactic per rule, summarized in a single
table the rest of the book keeps returning to. Covers modus ponens and
`apply`, disjunction with `left`/`right`/`cases`, and negation as
`P -> False`, with `exfalso` and `contradiction`. The famous fallacies
(affirming the consequent, denying the antecedent) are run through the
checker and rejected, countermodel notes and all.

**Cetacea features:** `apply`, `left`/`right`, `cases ... with`,
`exfalso`, `contradiction`, `<->` as a conjunction, the two
countermodel diagnostics ("statement is not a tautology" and "open goal
does not follow").

## Chapter 3 — The Classical Moves: Excluded Middle and Friends

*Drafted: [03-classical.md](03-classical.md)*

Why "it's either true or false" is a proof *step*, not a law of nature:
constructive proofs deliver evidence, classical proofs may only deliver
certainty. Introduces `by_cases` (excluded middle) and `by_contra`
(proof by contradiction), proves double-negation elimination and the
hard direction of De Morgan, and shows how Cetacea's mode system makes
the constructive/classical boundary a checked, visible feature rather
than a philosophical footnote.

**Cetacea features:** `mode classical`, `by_cases`, `by_contra`,
per-theorem mode reporting (a classical-mode file can still yield
`(constructive)` theorems), mode-violation error messages.

## Chapter 4 — Everyone, Someone, No One: Quantifiers

*Drafted: [04-quantifiers.md](04-quantifiers.md)*

Predicates turn propositions into statements *about* things; `forall`
and `exists` quantify over a declared domain. Each quantifier gets its
intro and elim rules (`intro x` / `exact h a`; `exists w` /
`cases ... with | intro w hw`), then the chapter works through
quantifier negation and the classic order-of-quantifiers trap —
including watching the checker refuse the invalid swap.

**Cetacea features:** `sort`, `const`, `pred`, quantifier tactics,
`exists` witness type-checking, `std/fol.ctea` lemmas, explicit theorem
instantiation with `{A := ...; P := ...}`.

## Chapter 5 — Equality: The Most Important Relation

Equality is a relation with two superpowers: everything equals itself,
and equals can be substituted for equals. The chapter introduces `refl`
for equalities that hold by computation, `rewrite` for substituting
with an equation, and the library lemmas `eq_symm` and `eq_trans`, then
practices equational reasoning as chains of rewrites — the formal
version of the "= ... = ..." calculations students already do.

**Cetacea features:** `=`, `refl`, `rewrite` / `rewrite ->` /
`rewrite all`, `simp [lemma]`, `simp at h`, `std/eq.ctea`
(`eq_symm`, `eq_trans`, `congr_pred`, substitution lemmas), Nat
computation (`add`, `mul` simplification).

## Chapter 6 — Sets: Collections You Can Reason About

Sets via membership: `x in A` is a proposition, `A subset B` is a
quantified implication, and every Venn-diagram identity becomes a
checkable theorem. Covers union, intersection, difference, complement,
set-builder notation, and the proof pattern for set equality: apply
extensionality, `intro x`, `simp` membership, prove both directions.
The two-column "element chasing" proofs of a discrete math course
become tactic scripts with the same skeleton every time.

**Cetacea features:** `Set T`, set term syntax (`union`, `inter`,
`diff`, `compl`, `{x, y, z}`, `{ x : T | P(x) }`), `simp` membership
expansion, the `set_ext` axiom, `std/set.ctea` lemmas, `def` for naming
sets.

## Chapter 7 — Relations: Structure Between Things

Binary predicates as relations, and the three properties that organize
them: reflexivity, symmetry, transitivity. The chapter uses `def` with
predicate parameters to state the properties once and instantiate them
many times, classifies familiar relations (equality, `le`, "knows"),
and builds toward equivalence relations and partial orders as bundles
of properties.

**Cetacea features:** `def` with `(T : Type) (R : T -> T -> Prop)`
parameters, `unfold`, `simp` definition unfolding, lambda predicates
(`fun x y : T => ...`), multi-argument `pred` declarations.

## Chapter 8 — Functions: Relations with Rules

A function is a relation where every input relates to exactly one
output — and this chapter makes that slogan literal by modeling
functions as graph predicates `G(x, y)` meaning "f(x) = y". Total,
single-valued, injective, and surjective each become one quantified
formula; the chapter proves the identity function bijective and that
composition preserves injectivity and surjectivity.

**Cetacea features:** `func` declarations, function graphs as lambdas,
`std/fun.ctea` (`Total`, `SingleValued`, `Injective`, `Surjective`,
composition theorems), explicit instantiation of predicate parameters.

## Chapter 9 — Induction: Climbing the Number Line

The natural numbers as `0` and `succ`, and induction as the proof
principle they come with: prove the base, prove each rung follows from
the one below, conclude for all. The chapter narrates the two arms of
`induction n with`, explains what an induction hypothesis really is,
and proves the additive identities and commutativity of addition — the
first proofs in the book where the statement is obvious and the proof
is genuinely work.

**Cetacea features:** `Nat`, `induction ... with | zero | succ k ih`,
`simp` for the `add`/`mul` equations, `rewrite ih`, `std/nat.ctea`,
the "induction binder would shadow" and hypothesis-dependence
restrictions.

## Chapter 10 — Recursion and Data: Building Your Own Worlds

Definition by recursion is induction's constructive twin. The chapter
introduces `defrec` over `Nat` (doubling, summing), then `data` for
user-defined types like lists and trees, and shows that `refl` can
prove concrete computations — evaluating a program and checking a
proof become the same activity. Binary operations such as list append
appear as axiomatized recursion equations, with an honest discussion of
what taking equations on trust means.

**Cetacea features:** `defrec` over `Nat` and over `data` types,
`data` declarations, `refl`/`simp` computation, `axiom` for recursion
equations, `std/list.ctea`, axiom tracking in `accepted` lines.

## Chapter 11 — Structural Induction: Proofs That Follow the Data

Every `data` type comes with its own induction principle: one case per
constructor, one induction hypothesis per recursive argument. The
chapter proves facts about lists (`length` of an append) and trees
(size of a mirror), and teaches the meta-skill of reading an induction
principle straight off a `data` declaration — the shape of the proof
is the shape of the data.

**Cetacea features:** structural `induction ... with` over data types,
multi-hypothesis arms (`| node l v r ihl ihr`), `rewrite` with
instantiated equation lemmas, combining `simp` and `rewrite` inside
arms.

## Chapter 12 — Strong Induction, and Where to Go Next

Sometimes the previous case isn't enough and you need *all* smaller
cases — strong induction, provided by the library theorem
`strong_induction` and applied with an explicit predicate lambda. After
working an example, the chapter closes the course: what Cetacea
deliberately leaves out (and where `docs/cs250/LIMITATIONS.md` says
so), how the ideas here map onto full-scale assistants like Lean, Rocq,
and Agda, and why "the proof is the program" is the idea to carry
forward.

**Cetacea features:** `strong_induction` and
`strong_induction_bounded` from `std/nat.ctea`, `apply` with explicit
`{P := fun m : Nat => ...; n := n}` instantiation, `le` lemmas, review
of the axiom/incomplete reporting model.
