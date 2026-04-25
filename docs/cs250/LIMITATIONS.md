# Limitations and Rough Edges (notes for the instructor)

This is a list of friction I hit while writing the CS 250 tutorials.
Some are real bugs, some are limitations of the documented surface,
some are paper cuts that show up in error messages. Roughly ordered by
how often a student is likely to bump into them.

## Real bugs (or close to)

### 1. There is no way to prove `True` from tactics

The kernel has a `Proof::TrueIntro` constructor (in
`crates/cetacea_core/src/lib.rs:307`), but no tactic surfaces it. So a
freshman writing the smallest possible theorem:

```text
theorem t : True := by
  exact True
```

gets `unknown hypothesis 'True'`. Trying `assumption`, `split`, `simp`,
and `refl` all fail with their respective "wrong shape" errors.

**Workaround:** declare `axiom triv : True` and `exact triv`.

**Suggested fix:** add a `Tactic::TrueIntro` (perhaps spelled
`trivial`, matching Lean / Coq) that produces `Proof::TrueIntro` when
the goal is `Formula::True`. Or have `exact` recognize the bare token
`True` as introducing it.

### 2. The diagnostic always shows the *original* `note: target:`, not the current open subgoal

Every kernel error ends with a line like
`  note: target: <whole theorem statement>`. That target string is the
original theorem being proved, not the current open goal at the point
of failure. So if the second of two `split` subgoals fails, the
diagnostic still shows the conjunction goal as the target.

The actually-useful part is in the *body* of the message — e.g. "exact
expression does not solve the goal: proof has type `Q`, but expected
`P`" tells you the current expected formula. But students will read the
`target:` line, not the body, and get confused about which subgoal they
were on.

**Suggested fix:** print the current open subgoal in `note: target:`
instead of the original theorem statement. Or prefix it with "(initial
target)" so it isn't misread as the current goal.

### 3. Parser errors lose the line number

Most kernel errors include `<file>:<line>`. But parse-time errors are
emitted as

```
error: could not parse `<file>`
  note: <some hint>
```

with no line. `unknown tactic 'exatc h'` is the kind of typo a student
will make, and the file might be 60 lines long.

**Suggested fix:** thread token positions through the parser and emit
`<file>:<line>` for parser errors too. (May already be planned; the
README mentions "Improve diagnostics with precise source spans.")

## Real limitations a CS 250 student will hit

### 4. No predicate or proposition parameters in `def`

```text
def Reflexive (R : T -> T -> Prop) : Prop := forall x : T, R(x, x)
```

is rejected with `formula definitions currently support only type and
term parameters`. Same for any `def` that quantifies over a `Prop`:

```text
def Conj_self (P : Prop) : Prop := P /\ P
```

Same error. This is significant for cs250 module 1, where reflexive /
symmetric / transitive *want* to be defined as predicates over `R`. The
workaround is to inline these properties into every theorem statement
that uses them, which gets verbose.

**Suggested fix:** the README's "Next Milestones" already lists
"broaden inference" — extending `def` to allow predicate and Prop
parameters would be the most pedagogically valuable extension.

### 5. No set-builder notation

```text
def TallSet : Set Person := { x : Person | Tall(x) }
```

doesn't parse. There's no syntax for constructing a set from a
predicate. You can only build sets from `empty(T)`, `singleton(x)`,
`union`, `inter`, `diff`. So you cannot define "the even numbers" or
"the truth set of P" directly — you have to characterize them via
biconditional.

This makes cs250 module 1 examples like `{n ∈ ℕ | n % 2 = 0}` not
expressible as Cetacea sets. It also blocks much of cs250 module 4
once you try to define "the truth set of a predicate."

### 6. `simp` does not reduce inside predicates or function arguments

```text
theorem t : Even(add(0, 0)) := by
  simp
```

fails with `simp made no progress on goal 'Even(add(0, 0))'`, even
though the same `add(0, 0)` *would* simp-reduce inside an equality goal
`add(0, 0) = 0`. So `simp` is picking up the equality structure of the
goal, not just rewriting subterms.

**Workaround:** use `apply eq_subst_left {...}` with explicit schema
arguments. This works but is much harder to teach than `simp`.

**Suggested fix:** make `simp` traverse function/predicate arguments
when looking for built-in computation rules to fire.

### 7. `rewrite` is one-directional and can't accept compound proof expressions

`rewrite h` finds the right-hand side of `h`'s equality in the goal and
replaces it with the left-hand side. There's no equivalent in the other
direction. This means almost every nat-induction proof needs a `_rev`
helper:

```text
theorem add_succ_right_rev (n m : Nat)
  : succ(add(n, m)) = add(n, succ(m)) := by
  rewrite add_succ_right {n := n; m := m}
  refl
```

The standard library knows this and provides `add_succ_right_rev`,
`add_zero_right_rev`, etc. But anyone who writes their own recursive
function via axioms needs the same dance.

Also: `rewrite eq_symm h` doesn't work — `rewrite` only accepts a
direct theorem reference or hypothesis, not a chained proof
expression. You can't compose with `eq_symm` inline.

### 8. Theorem instantiation is finicky when local variable names overlap with the lemma's parameter names

A student might write:

```text
theorem subsets_carry
  (T : Type)
  (A B S : Set T)
  : A subset B -> S subset A -> S subset B := by
  intro hAB
  intro hSA
  apply subset_trans
  exact hSA
  exact hAB
```

They get `cannot infer schema argument 'B'` because `subset_trans`'s
middle variable can't be guessed. So they try the explicit form:

```text
  apply subset_trans {T := T; A := S; B := A; C := B}
```

Now it complains `unknown term 'C'`, which is the *parameter name in
subset_trans*, not anything in scope. Confusing.

The only reliable fix I found was to **rename the local variables to
match the lemma's parameter names** (here, `A`, `B`, `C`). That's
clearly a workaround, not the intended workflow.

**Suggested fix:** the explicit-args parser should distinguish between
schema parameter names (LHS of `:=`) and term references (RHS), and the
diagnostic on the LHS should say something like `subset_trans has no
schema parameter 'C'` rather than `unknown term 'C'`.

### 9. No multi-binder `forall`/`exists`

```text
forall x y : A, R(x, y)
```

doesn't parse. Students have to nest:

```text
forall x : A, forall y : A, R(x, y)
```

Cosmetic, but the textbook uses multi-binder notation throughout.

### 10. Cannot parenthesize sub-proof-expressions

`apply (htrans x y x)` doesn't parse. Neither does `exact (h hp).left`.
You either have to use a step-by-step `apply` chain or split into a
helper theorem. Workable, but verbose.

### 11. `h x` (forall application in a proof expression) doesn't work for plain implications

You can write `exact h alice` when `h : forall x, P(x)`. You **cannot**
write `exact h hp` when `h : P -> Q` and `hp : P`. The error is
"first-order application expects a universal proof." So the standard
"function application" idiom diverges between universals and
implications.

**Workaround:** use `apply h` and discharge the antecedent on the next
line. Or wrap in a helper: `apply imp_apply` etc.

### 12. Schema-substituted theorem refs can't be combined with forall args

```text
apply subset_trans {T := Person} X Y Z
```

is rejected with `explicit theorem arguments can only be used with
theorem references`, even though `subset_trans` is a theorem reference.
You can give the schema OR the term arguments, but not both inline. The
practical effect is that some intermediate-difficulty `apply`s have no
clean form.

## Pedagogical mismatches with CS 250

### 13. `add` recurses on the wrong argument

The textbook (cs250 module 4 §6.1) defines `+` recursively on the
**second** argument:

$$
n + 0 = n
\qquad
n + \text{succ}(m) = \text{succ}(n + m)
$$

Cetacea's built-in `add` recurses on the **first** argument. So:

- The textbook's $n + 0 = n$ is "free" for them, but in Cetacea
  `add(n, 0) = n` requires induction.
- The textbook's $0 + n = n$ requires induction, but in Cetacea
  `add(0, n) = n` is "free" via simp.

Walking through the Module 4 worked example "$\forall n.\; 0 + n = n$"
in Cetacea is therefore *backwards*. Students will be confused unless
the convention mismatch is flagged loudly, ideally in the doc next to
where `add` is introduced.

**Suggestion:** add a sentence to `docs/USAGE.md`'s Nat section noting
the recursion convention, and consider whether to make the textbook
convention available as `addr` (right-recursive) or to provide both.

### 14. No multiplication, no comparison, no subtraction

`Nat` has only `0`, `succ`, and `add`. No `mul`, no `<=`, no `sub`. CS
250 module 4 Exercise 11 is multiplication, and Modules 5–6 are
modular arithmetic. Students who want to do those exercises in Cetacea
must axiomatize `mul` themselves, which they can do but it's a lot of
ceremony.

### 15. Induction is `Nat`-only

Cetacea has no general structural induction. Lists, trees, the BNF-
defined inductive types of cs250 module 10 — none of these are
expressible. So Module 8 (sequences/recursion), Module 9 (recurrences),
and Module 10 (structural induction) cannot be done in Cetacea at all.

This isn't a bug, just the size of the system. Worth mentioning
prominently in any course-facing doc.

### 16. No truth-table evaluation

Cetacea is a proof system; it doesn't evaluate formulas under
assignments. So all of Module 2 (truth tables) must be done outside
Cetacea — on paper or with `code/module02_logic.py`. The bridge to
Cetacea is "anything you'd verify via a truth table can be derived as a
theorem in Cetacea using the rules of Module 3." That's the right
framing for a course tutorial, but worth stating up front.

### 17. No proof-state introspection

There's no `show_goal` or `print_state` tactic. When a proof gets
stuck, you can't ask "what's my current open goal?" You can either:

(a) read the kernel error message body and infer it from "expected
`X`", or

(b) extract the failing step into a separate named theorem, so its
statement is the goal.

For a course where proof debugging is the *point*, this hurts. Even a
tactic that prints the current goal to stderr would help.

## Smaller gripes

### 18. Hypothesis name shadowing in `intro` is allowed silently

If a hypothesis name already exists in context, `intro h` with the same
name shadows it without warning. This is conventional but can confuse
beginners.

### 19. Indentation rules are forgiving but undocumented

The docs say `cases` arms are "indented by four spaces under the arm,"
but anything from one space to many works in practice. Students may
relax their indentation and then be confused by some other error that
*does* show up.

### 20. `cases h.left` style projections work in `exact` but not in
`cases`

You can write `exact h.left` but `cases h.left with | left ... =>` is
fine — actually, both work. Disregard. (Leaving the bullet because the
reverse used to be what I expected from a short read of the docs.)

## Things that actually work very well

To balance: a substantial part of CS 250 *does* go through cleanly.

- **Module 3** (proof systems) is a near-perfect fit: every intro/elim
  rule has a matching tactic, the constructive/classical distinction
  shows up live in the file output, and the "common fallacies" become
  proofs that visibly fail.
- **Module 4** (FOL, quantifier reasoning) works well end-to-end, with
  good standard-library support.
- **Set algebra** (Module 1's set operations, plus the cardinality
  intermezzo's "subset / union / intersection identities") all
  goes through, modulo the no-set-builder limitation.
- **Equality and rewriting** are fine for the typical needs of the
  course (transitivity, substitution into predicates).
- **Standard library** is exactly the right size for a one-term course
  — students can read every file in an afternoon.

If the bugs in §1–§3 above were fixed, this would be a remarkably
teachable system at this scope.
