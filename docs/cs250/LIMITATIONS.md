# Limitations and Rough Edges (notes for the instructor)

This is a current list of friction points for using Cetacea with the CS
250 tutorials. The most severe bugs from the first draft have been
fixed; see the resolved section at the end for historical context.

## Current rough edges students may hit

### 1. Theorem instantiation still sometimes needs explicit arguments

`exact` and `apply` can infer many theorem parameters, but not all of
them. Transitive lemmas are the common case where an intermediate term
is not forced by the goal:

```text
apply subset_trans {T := Person; A := C; B := A; C := B}
```

That works, but the syntax is a lot for beginners. The diagnostics are
better than they used to be, but the user still needs to know which
intermediate object to provide.

**Possible improvement:** add more goal-directed inference for
intermediate terms.

### 2. `simp` is built-in, not theorem-driven

`simp` knows transparent definitions, set membership, subset expansion,
and built-in Nat computation. `simp at h` can simplify a named
hypothesis, and `simp at *` simplifies the goal plus all hypotheses. It
does not use arbitrary imported lemmas as rewrite rules.

For example, a goal may simplify cleanly while a matching hypothesis
still needs an explicit `rewrite`, `exact`, or helper theorem.

**Possible improvement:** add a theorem-driven simplifier.

### 3. User-defined recursive functions are not available

Cetacea has transparent non-recursive definitions, but no syntax for
defining recursive functions over `Nat`. Built-in `add` and `mul` now
simplify both the implementation's left-recursive equations and the CS
250 textbook's right-recursive equations, but custom recursive examples
must still be introduced as uninterpreted functions with axiomatized
recursion equations.

That is fine for short course examples, but it is not a replacement for
a real recursive-function facility.

### 4. Induction is `Nat`-only

Cetacea has no general structural induction. Lists, trees, the BNF
types in later CS 250 modules, and user-defined inductive structures are
not expressible.

This means the Module 8 sequence/recursion material, Module 9
recurrences, and Module 10 structural induction material mostly need to
stay outside Cetacea.

### 5. Truth-table evaluation is outside Cetacea

Cetacea is a proof system, not a truth-table evaluator. Module 2's truth
tables should still be done on paper or with the course Python tools.

The useful bridge is: formulas classified by truth tables can often be
re-derived as Cetacea theorems using the proof rules from Module 3.

### 6. Arithmetic is intentionally small

Nat currently has `0`, `succ`, `add`, `mul`, truncated `sub`, and
`le`. It does not have division, modular arithmetic, cardinalities, or a
decision procedure for arithmetic goals.

CS 250 modular arithmetic examples should be modeled axiomatically if
they are used in Cetacea at all.

### 7. Set theory is typed and finite in scope

Cetacea has typed sets, set builders, union, intersection, difference,
powersets, subset, and extensionality. It does not have Cartesian
products as set objects, cardinalities, finite-set enumeration, or
comprehension beyond predicate set builders.

The Module 1 set-identity and powerset-monotonicity proofs fit well.
Counting arguments and cardinality exercises do not.

### 8. Diagnostics still have line granularity, not token spans

Parse and checking errors now report useful line numbers, and failed
tactics report the current goal. They still do not point at an exact
token span within the line.

That is good enough for short tutorial files but can still be vague in
long theorem headers.

### 9. Imports and names are global

There are no namespaces or qualified imports. Imported declarations enter
one global environment, and built-in names such as `add`, `mul`, `sub`,
and `le` cannot be reused for local functions or predicates.

This is simple and readable at the current project size, but larger
course libraries will eventually want namespaces.

### 10. Predicate arguments must be names

Definitions can take predicate parameters:

```text
def Reflexive (A : Type) (R : A -> A -> Prop) : Prop := forall x : A, R(x, x)
```

But predicate arguments are still predicate names, not arbitrary lambda
expressions. You can pass `Likes`, but not an inline predicate expression
like "the relation `fun x y => x = y`".

## Smaller gripes

### Indentation is forgiving but under-specified

The block parser accepts a range of indentation styles. The tutorials use
one consistent style, but the accepted grammar is more permissive than
the prose explains.

### Error messages are still implementation-flavored

The checker is much clearer than it was, but messages still mention
schema arguments, target formulas, and proof expressions in terms that
are more natural to implementers than first-time proof students.

## Resolved since the first tutorial draft

These were real blockers when the CS 250 notes were first written and
are now implemented:

- `True` goals can be closed with `trivial` or `exact True`.
- Failed tactics report the current open goal in the `target:` note.
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
- `powerset(A)` is supported, with membership simplifying to subset.
- `rewrite -> h` supports the forward direction, and `rewrite` accepts
  compound proof expressions such as `rewrite eq_symm h`.
- Parenthesized proof expressions such as `exact (h hp).left` and
  `apply (htrans x y x)` parse.
- Multi-binder `forall x y : T, ...` and `exists x y : T, ...` parse.
- Explicit theorem schema arguments can be combined with ordinary
  forall arguments.
- Nat has built-in `mul`, `sub`, and `le`.
- `show_goal` reports the current goal.
- `intro` rejects shadowing instead of silently replacing a local name.

## Things that work well

- **Module 3** proof systems are a strong fit: intro and elimination
  rules line up directly with tactics, and fallacies become visibly
  rejected proof scripts.
- **Module 4** quantifier reasoning works well, with useful standard
  library support.
- **Set algebra** goes through cleanly with typed sets, set builders,
  subset expansion, and set extensionality.
- **Relations** can be represented as predicate parameters, so
  reflexive/symmetric/transitive definitions can be written directly.
- **Equality and rewriting** cover the usual course needs:
  reflexivity, symmetry, transitivity, substitution into predicates, and
  local equational rewriting.
- **The standard library** is small enough for students to read while
  still covering propositional logic, first-order logic, equality, sets,
  and basic Nat facts.
