# Limitations and Rough Edges (notes for the instructor)

This is a current list of friction points for using Cetacea with the CS
250 tutorials. The most severe bugs from the first draft have been
fixed; see the resolved section at the end for historical context.

## Current rough edges students may hit

### 1. Theorem instantiation still sometimes needs explicit arguments

`exact` and `apply` can infer many theorem parameters, but not all of
them. Transitive lemmas are much better than they used to be: when the
intermediate object appears in local hypotheses, `apply` can usually
infer it:

```text
apply subset_trans
```

`apply` also looks through simple consequences of local hypotheses, so a
local hypothesis such as `h : P -> Q /\ R` can guide `apply and_left`
or `apply and_right` without explicit `{P := ...; Q := ...}` arguments.

The remaining rough edge is the genuinely underdetermined case where
the missing object is not present in the goal, local hypotheses, or a
simple implication/conjunction consequence of a local hypothesis. Then
the user still needs to provide an explicit theorem parameter.

**Possible improvement:** add a more principled search procedure for
underconstrained theorem parameters.

### 2. `simp` has explicit theorem rules, not a global simp set

`simp` knows transparent definitions, set membership, subset expansion,
and built-in Nat computation. `simp at h` can simplify a named
hypothesis, and `simp at *` simplifies the goal plus all hypotheses. It
can also use listed equality theorems or local equality hypotheses in
the goal or in hypotheses, as in `simp [lemma]`, `simp [h]`,
`simp [lemma] at h`, and `simp [lemma] at *`.

The remaining limitations are:

- there is no global or attribute-based simp-set,
- no automatic imported-lemma discovery,
- no iff/proposition rewriting.

**Possible improvement:** add `@[simp]`-style rule registration and a
richer rewrite engine.

### 3. User-defined recursion is still unary

Cetacea's `defrec` now does unary primitive recursion over `Nat` *and*
over user-declared data types:

```text
defrec double (n : Nat) : Nat
| zero => 0
| succ k rec => succ(succ(rec))

defrec size (t : Tree) : Nat
| leaf => 0
| node l v r recl recr => succ(add(recl, recr))
```

In a data-type arm, you bind one name per constructor argument and then
one recursive-result name per recursive argument, in order. `simp` and
`refl` both compute these definitions, on concrete and on symbolic
constructor calls.

`defrec` now also takes additional fixed parameters after the recursive
one, so binary textbook operations are directly definable:

```text
defrec append (l : List) (r : List) : List
| nil => r
| cons h t rec => cons(h, rec)
```

`std/list.ctea` defines `append` this way — no axioms involved — and
proves `length_append` and `append_assoc` by structural induction. The
remaining gaps are recursion on a *later* argument, mutual recursion,
and pattern matching deeper than one constructor.

The standard library includes `pred`, `pred_succ`, and `succ_inj`
for the common successor-injectivity exercise.

### 4. Data types are monomorphic — but structural induction works

Cetacea now has user-declared inductive data types and structural
induction over them:

```text
data Tree
| leaf
| node(Tree, Nat, Tree)
```

`induction t with | leaf => ... | node l v r ihl ihr => ...` gives one
induction hypothesis per recursive constructor argument, which is
exactly Module 10's structural induction rule. With `std/list.ctea`
(lists of naturals, recursive `length` and `append`) and strong induction
in `std/nat.ctea`, the Module 8 sequence/recursion material, Module 9
recurrences, and Module 10 structural induction material are now largely
expressible; see the new `07_structural_induction.md` tutorial.

What is still missing is *polymorphism*: data types take no type
parameters, so there is no `List A` — `std/list.ctea`'s `List` is a
list of `Nat`, and a list of something else is a second, unrelated
declaration. Grammar/BNF examples with mutually recursive types are also
out, since data types cannot refer to each other.

### 5. Truth tables are not enumerated, but countermodels are reported

Cetacea is a proof system, not a truth-table evaluator, and it still
does not print truth tables. Module 2's full-table exercises should
still be done on paper or with the course Python tools.

However, the checker now runs a truth-table check behind the scenes when
a proof fails: if the statement (or the open goal, given its hypotheses)
is purely propositional and classically falsifiable, the error says so
and gives the falsifying row:

```text
note: the statement is not a tautology: it is false when P = false, Q = true.
No proof can close it; check the statement itself.
```

This is pedagogically the punchline of Module 2 anyway — students trying
to prove a non-theorem (typo'd homework statement, converse error) get
told *there is a countermodel* instead of grinding on tactics forever.
The variant wording "the open goal does not follow from the current
hypotheses ... Reconsider the earlier proof steps" distinguishes a wrong
statement from a wrong turn in the proof.

The useful bridge remains: formulas classified by truth tables can often
be re-derived as Cetacea theorems using the proof rules from Module 3.

### 6. Arithmetic is intentionally small

Nat currently has `0`, `succ`, `add`, `mul`, truncated `sub`, and
`le`. It does not have division, modular arithmetic, cardinalities, or a
decision procedure for arithmetic goals.

CS 250 modular arithmetic examples should be modeled axiomatically if
they are used in Cetacea at all.

Numeric Nat literals such as `2` and `42` parse as repeated `succ`
applications, so students can write small concrete examples directly.

### 7. Set theory is typed and finite in scope

Cetacea has typed sets, set builders, union, intersection, difference,
complement, universal sets, Cartesian products, powersets, subset, and
extensionality. It does not have cardinalities or comprehension beyond
predicate set builders. Nonempty finite sets can be written as
`{x, y, z}`; empty sets still need an explicit element type with
`empty(T)`.

The Module 1 set-identity and powerset-monotonicity proofs fit well.
Counting arguments and cardinality exercises do not.

### 8. Some diagnostics still have line granularity, and a few parser quirks

Parse errors now carry line-local token spans when the parser can identify the
offending token. Checking errors report useful line numbers, and failed tactics
report the failing tactic line plus the current goal. They still do not point at
an exact AST or tactic span within the line.

That is good enough for short tutorial files but can still be vague in
long theorem headers.

The parser now handles the most common tutorial shapes, including
wrapped explicit theorem-argument lists and inline predicate lambdas
whose binder names overlap with names introduced later in the proof.

### 9. Imports and names are global

There are no namespaces or qualified imports. Imported declarations enter
one global environment, and built-in names such as `add`, `mul`, `sub`,
and `le` cannot be reused for local functions or predicates.

This is simple and readable at the current project size, but larger
course libraries will eventually want namespaces.

### 10. Predicate lambdas are intentionally small

Definitions can take predicate parameters:

```text
def Reflexive (A : Type) (R : A -> A -> Prop) : Prop := forall x : A, R(x, x)
```

Predicate arguments can be declared predicate names such as `Likes` or inline
lambdas such as `fun x y : Person => x = y`. This covers the common CS 250
relation examples.

The remaining limitation is that these lambdas are first-order predicate
arguments only. They are not general function values, and they cannot be passed
where a term is expected.

## Smaller gripes

### Indentation is forgiving but under-specified

The block parser accepts a range of indentation styles. The tutorials use
one consistent style, but the accepted grammar is more permissive than
the prose explains.

### Some error messages are still terse

The checker is much clearer than it was, and theorem-instantiation
messages now use student-facing "theorem parameter" wording. Some
messages are still terse, especially when a proof expression has several
parts or when a normalized target formula is large.

## Resolved since the first tutorial draft

These were real blockers when the CS 250 notes were first written and
are now implemented:

- `True` goals can be closed with `trivial` or `exact True`.
- Failed tactics report the current open goal in the `target:` note.
- Failed tactics report the failing tactic line, including inside nested
  tactic blocks.
- Parse errors report useful line numbers.
- Formula and term definitions can take type, term, proposition, and
  predicate parameters.
- Set-builder terms `{ x : T | P(x) }` are supported.
- `simp` reduces built-in computation under predicate and function
  arguments.
- `simp at h` simplifies a named hypothesis, and `simp at *` simplifies
  all hypotheses plus the goal.
- Built-in `add` and `mul` simplify the CS 250 textbook's
  right-recursive equations as well as the implementation's
  left-recursive equations.
- Unary primitive recursive `Nat` functions can be declared with
  `defrec`, and `simp` computes their zero and successor equations.
- `simp [lemma]` can use listed equality theorems as rewrite rules in
  the goal.
- `simp [lemma] at h` and `simp [lemma] at *` can use listed equality
  theorems as rewrite rules in hypotheses.
- `simp [h]` can use local equality hypotheses as rewrite rules in the
  goal or in hypotheses.
- `\/` and `/\` parse right-associatively, matching textbook "Big And /
  Big Or" convention.
- `apply` can infer intermediate theorem parameters for transitive lemmas
  such as `subset_trans` and `eq_trans` from matching local hypotheses.
- `apply` can infer missing theorem parameters from simple implication
  and conjunction consequences of local hypotheses.
- `apply` normalizes theorem conclusions after explicit theorem-parameter
  substitution, so predicate-lambda examples such as successor injectivity
  match the simplified goal shape.
- `powerset(A)` is supported, with membership simplifying to subset.
- Nonempty finite set literals such as `{x, y}` parse as nested unions
  of singletons.
- `univ(T)` and `compl(A)` are supported, with membership simplifying to
  `True` and negated membership respectively.
- `Prod T U`, `pair(x, y)`, projections, and Cartesian product sets
  `prod(A, B)` are supported.
- `rewrite -> h` supports the forward direction, and `rewrite` accepts
  compound proof expressions such as `rewrite eq_symm h`.
- `rewrite all h` rewrites all matching occurrences in the target.
- Parenthesized proof expressions such as `exact (h hp).left` and
  `apply (htrans x y x)` parse.
- Parenthesized projections can take arguments, as in `exact (h.left) hp`.
- Explicit theorem-argument lists `{...}` can be wrapped across several
  tactic lines.
- Multi-binder `forall x y : T, ...` and `exists x y : T, ...` parse.
- Explicit theorem parameters can be combined with ordinary forall
  arguments.
- Nat has built-in `mul`, `sub`, and `le`.
- Numeric Nat literals such as `2` parse as repeated successors.
- The Nat standard library includes `pred`, `pred_succ`, and `succ_inj`.
- Predicate-lambda substitution is simultaneous and capture-avoiding, so
  examples such as `fun x y => x = y` work even when the surrounding
  theorem introduces variables named `x` and `y`.
- `show_goal` reports the current goal.
- `intro` rejects shadowing instead of silently replacing a local name.
- The `sorry` tactic (alias `admit`) closes any goal; the theorem is
  accepted but reported as `incomplete: uses sorry`, and the flag
  propagates to theorems that use a sorry'd theorem. This is the missing
  piece for distributing homework skeleton files.
- The CLI prints `accepted` lines for every passing theorem even when
  other theorems in the file fail, so students see partial credit
  instead of one error hiding everything below it.
- Accepted lines list the axioms a proof depends on, directly or
  transitively, as in
  `accepted theorem length_append (constructive; axioms: append_cons,
  append_nil)`.
- Failed propositional proofs get countermodel notes ("the statement is
  not a tautology: it is false when ..."), also surfaced as a
  "Warning: this goal is not provable" hint in the Goals panel.
- Inductive data types can be declared with `data`, with structural
  `induction ... with` over them, including two-recursive-argument
  constructors such as tree nodes.
- `defrec` works over declared data types, not just `Nat`, and takes
  additional fixed parameters, so binary operations such as `append` are
  defined directly rather than axiomatized.
- A `have` tactic supports forward reasoning (`have h : P`,
  `have h : P := proof`).
- Projections parse inside proof-expression arguments
  (`exact f h.left`, `rewrite -> hinj x y (h.left)`).
- The prelude now includes `std/list.ctea` (lists of naturals with
  recursive `length` and `append`) and `std/fun.ctea`
  (functions-as-graphs with `Total`, `SingleValued`, `Injective`,
  `Surjective`, and composition theorems).
- Strong induction is available as `strong_induction` and
  `strong_induction_bounded` in `std/nat.ctea`, with the supporting
  order lemmas `le_zero_inv` and `le_succ_inv`.
- Unicode connectives `∧ ∨ ¬ → ↔ ∀ ∃ ∈ ⊆` are accepted as aliases, so
  statements can be pasted from the course notes nearly verbatim; other
  non-ASCII characters get a helpful error instead of a parse mystery.
- `cases h with | intro hp hq =>` destructures conjunction hypotheses,
  not just existentials.
- `refl` computes: equality goals whose sides normalize to the same
  term, such as `add(n, 0) = n` or `mul(2, 3) = 6`, close without a
  preceding `simp`.
- `exists` validates its witness term and reports type mismatches at the
  tactic line.
- Goals-panel tactic hints are speculatively executed, so failing
  suggestions are no longer shown.
- The TUI has undo/redo (Ctrl-Z / Ctrl-Y), and the browser UI autosaves
  to localStorage, re-checks live, marks error lines inline, and has a
  load-example menu. The browser UI deploys automatically to GitHub
  Pages.
- Induction arm binders must be fresh: shadowing an existing variable or
  hypothesis is rejected, for structural arms and for the Nat
  `| succ k ih` arm alike.

### Soundness fixes

Worth recording for anyone assessing the kernel: an audit found and
fixed two variable-capture bugs in kernel/schema substitution and an
induction-binder shadowing hole that together could have accepted
ill-formed proofs. All three are fixed with regression tests, and
substitution is now capture-avoiding everywhere. The induction-binder
freshness rule above is the user-visible face of the shadowing fix.

## Things that work well

- **Module 3** proof systems are a strong fit: intro and elimination
  rules line up directly with tactics, and fallacies become visibly
  rejected proof scripts. The textbook's two famous fallacies — converse
  error and inverse error — both fail with student-readable diagnostics
  ("proof has type `q`, but expected `p`"), and the misuse of
  `\/`-elimination that the textbook flags as common is structurally
  prevented because `cases` requires both arms.
- **Module 4** quantifier reasoning works well, with useful standard
  library support, including the textbook's quantifier-negation rules
  in both directions and the "order matters" example for nested
  quantifiers.
- **Constructive vs classical separation** is enforced and gives an
  educational error: an attempted proof of double-negation elimination
  in constructive mode reports `by_contra introduces a classical proof
  of P`, which directly motivates the classical/constructive
  distinction.
- **Set algebra** goes through cleanly with typed sets, set builders,
  subset expansion, set extensionality, complement, universal sets,
  Cartesian products, finite literals, and powersets.
- **Relations** can be represented as predicate parameters, so
  reflexive/symmetric/transitive definitions can be written directly.
- **Functions as relations** now have direct support: `std/fun.ctea`
  models a function by its graph, with `Total`, `SingleValued`,
  `Injective`, and `Surjective` matching the course definitions
  one-for-one, plus identity and composition theorems.
- **Structural induction** (Modules 8–10) works on monomorphic lists and
  trees: `data`, `defrec` over data types, and `induction ... with` with
  one hypothesis per recursive argument line up exactly with the
  textbook rule, and strong induction on `Nat` covers the recurrence
  material.
- **Equality and rewriting** cover the usual course needs:
  reflexivity, symmetry, transitivity, substitution into predicates, and
  local equational rewriting. Computation-only equalities close with a
  bare `refl`.
- **Homework skeletons** are practical now: state the theorems, fill the
  bodies with `sorry`, and hand the file out. Per-theorem `accepted`
  lines, the `incomplete: uses sorry` flag, and axiom-dependency
  reporting make grading output honest, and countermodel notes stop
  students from grinding on unprovable goals.
- **The standard library** is small enough for students to read while
  still covering propositional logic, first-order logic, equality, sets,
  lists, function graphs, and Nat facts up through strong induction.
