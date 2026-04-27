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
can also use listed equality theorems in the goal or in hypotheses, as
in `simp [lemma]`, `simp [lemma] at h`, and `simp [lemma] at *`.

The remaining limitations are:

- there is no global or attribute-based simp-set,
- no automatic imported-lemma discovery, and
- no iff/proposition rewriting.

**Possible improvement:** add `@[simp]`-style rule registration and a
richer rewrite engine.

### 3. User-defined recursion is intentionally narrow

Cetacea now has `defrec` for unary primitive recursion over `Nat`:

```text
defrec double (n : Nat) : Nat
| zero => 0
| succ k rec => succ(succ(rec))
```

The successor arm can refer to the predecessor `k`, the recursive
result `rec`, both, or neither. The simplifier computes concrete calls
such as `double(succ(succ(0)))` and symbolic successor calls such as
`double(succ(n))`.

This addresses the common small examples where a single natural number
drives the recursion. It is still not a general recursive-function
facility: there is no binary recursion, mutual recursion, pattern
matching beyond `0`/`succ`, or recursion over lists, trees, strings, and
other inductive structures. Binary textbook-style operations that are
not built in still need to be introduced as uninterpreted functions with
axiomatized recursion equations.

The standard library now includes `pred`, `pred_succ`, and `succ_inj`
for the common successor-injectivity exercise.

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

Numeric Nat literals such as `2` and `42` parse as repeated `succ`
applications, so students can write small concrete examples directly.

### 7. Set theory is typed and finite in scope

Cetacea has typed sets, set builders, union, intersection, difference,
complement, universal sets, powersets, subset, and extensionality. It
does not have Cartesian products as set objects, cardinalities, or
comprehension beyond predicate set builders. Nonempty finite sets can be
written as `{x, y, z}`; empty sets still need an explicit element type
with `empty(T)`.

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
- `rewrite -> h` supports the forward direction, and `rewrite` accepts
  compound proof expressions such as `rewrite eq_symm h`.
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
