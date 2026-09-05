# Cetacea 2: an HOL kernel with tiered front-ends

Status: design accepted, 5 September 2026. This plan describes a
ground-up rewrite of Cetacea on a higher-order-logic kernel, with a
front-end that presents three logic tiers (first-order logic;
first-order logic with natural-number induction; full HOL with
datatypes). The decisions in section 12 were settled with the
instructor on the same day. It is a plan, not a changelog.

Progress: M0 (the kernel, `crates/hol_kernel`) landed on 5 September
2026 with the primitive rules, tags, definitional principles, the
datatype and recursive-function packages, and an adversarial test
suite. Later milestones are not started.

## 1. Why rewrite, and why HOL

The current implementation is a many-sorted first-order prover with a
growing list of conservative extensions bolted on: predicate parameters,
first-order predicate lambdas, monomorphic `data`, unary `defrec`, typed
sets as a built-in term family, functions modeled as graphs. Every entry
in the friction log and the gap audit that is not a papercut traces back
to one of those bolts:

| Friction / gap | First-order cause | What HOL gives instead |
|---|---|---|
| Lambda propagation through nested defs, def names as predicate args, mixed-type lambdas | Predicates are a separate syntactic category from terms | A predicate is a term of type `A -> Prop`; substitution is ordinary substitution |
| Functions are not first-class; no function equality; composition only on graphs | Functions are uninterpreted symbols, not values | `f : A -> B` is a term; `Injective(f)`, `g ∘ f`, `f = g` are ordinary |
| Monomorphic `List`, `Tree`; no `List A` | No type variables | Rank-1 polymorphism at declarations and theorems, as in every HOL |
| No recursive propositions (`Sorted`, `NoDup`, `ValidPath`) | `defrec` returns terms, predicates are not terms | `defrec` returning `Prop` is just a recursive function |
| No cardinality or counting | No polymorphic lists and no recursive predicates | `Finite`, `card`, pigeonhole become library work |
| Trusted `set_ext` axiom | Sets are a built-in term family | Sets are predicates; extensionality follows from function extensionality |
| No iff rewriting; separate simp registry | `<->` is a conjunction of implications | `<->` is `=` at type `Prop`; `rewrite` and `simp` are uniform |
| Schema parameters versus foralls, "bare term args swallowed by binders" | Two instantiation mechanisms | One: instantiate type variables, then term variables |
| Two capture bugs in substitution history | Named variables in the kernel | Locally nameless representation |

The pedagogical story also gets simpler. Today the audit has to say
"FOL is the foundation and datatypes are conservative extensions". The
new story is "one small logic; the course starts inside a restricted
view of it and the restrictions come off tier by tier".

## 2. Goals and non-goals

Goals:

- A trusted kernel small enough to print in an appendix, with natural
  deduction rules as primitives so the intro/elim table from the book
  stays the literal rule set.
- Constructive versus classical, axiom dependencies, and `sorry` tracked
  per theorem exactly as today, but by kernel tags rather than a
  post-hoc walk over proof objects.
- Three tiers that are restrictions of one language, so a tier-1 file
  is a valid tier-3 file and moving up never invalidates old work.
- Feature parity with the current browser UI: live checking, goals at
  cursor, tactic hints, diagnostic repair suggestions, countermodels,
  theorem library search, proof explanation, examples, autosave, virtual
  standard library.
- Feature parity with the current CLI for grading: `--strict`,
  `--deny-sorry`, `--deny-axioms`, `--deny-classical`, `--json`.
- Source compatibility for the existing tier-1 and tier-2 corpus (74
  `.ctea` files, 79 book exercises) except for a short, deliberate list
  of syntax changes recorded in section 9.
- No installation for students; the CLI exists for the instructor and CI.

Non-goals:

- Reusing the current `cetacea_core` code. The syntax and the test
  corpus are reused; the implementation is not.
- Dependent types, universes, or a definitional datatype package in the
  style of HOL4's. Datatypes are admitted by a checked package that
  emits tagged principles (section 4.4).
- Heavy automation by default. Automation exists for tier 3 and is
  subject to assignment policy.

## 3. Architecture overview

```
crates/
  hol_kernel/     terms, types, Thm, primitive rules, definitional principles, tags
  hol_syntax/     lexer, parser, concrete AST with spans, tier grammar tables
  hol_elab/       type inference, name resolution, tier checking, sugar expansion
  hol_tactics/    goal states, tactic language, proof recording for explanations
  hol_feedback/   countermodels, evaluator/quickcheck, hints, repair suggestions
  hol_session/    whole-file checking, imports, per-declaration cache, JSON models
  hol_cli/        CLI and grading policies
  hol_wasm/       wasm-bindgen exports of hol_session
web/              Vite app: CodeMirror 6 editor, Web Worker hosting the wasm
std/              standard library in the new language, one file per tier layer
```

Rules of the road:

- Only `hol_kernel` can construct a `Thm`. Rust privacy enforces this.
- `hol_kernel` has no dependency on any other crate and no parser.
- Everything above the kernel may be wrong without compromising
  soundness; everything above `hol_elab` may be slow without blocking
  checking (hints and countermodels run on a budget).
- The web UI talks to the checker only through the JSON API in
  section 7, the same one the CLI uses for `--json`.

## 4. The kernel

### 4.1 Types and terms

```
Type  ::= TyVar a | TyCon name [Type]        -- Prop, Nat, Set T, List A, A -> B
Term  ::= Var name Type                      -- free variable
        | Bound index                        -- de Bruijn, locally nameless
        | Const name Type                    -- constant at a type instance
        | App Term Term
        | Lam name Type Term
```

`Prop` is a type constant. `A -> B` is `TyCon "fun" [A, B]`. There is
no separate formula syntax in the kernel; a formula is a term of type
`Prop`. Every term is type-checked at construction, so ill-typed terms
cannot exist.

Locally nameless representation (bound variables are indices, free
variables are named) makes substitution capture-free by construction.
This is the direct answer to the two capture holes recorded in the
project history.

### 4.2 Theorems

```
Thm { hyps: Vec<Term>, concl: Term, tags: TagSet }
TagSet ⊆ { Classical, Sorry, Axiom(name), Datatype(name) }
```

Tags propagate by union through every rule. The per-theorem status line
(`accepted theorem foo (constructive; axioms: set_ext)`,
`incomplete theorem bar (uses sorry)`) is a rendering of the tag set on
the final `Thm`. `--deny-classical`, `--deny-sorry`, and
`--deny-axioms` are predicates on tag sets. This replaces today's
transitive walk over proof objects with a mechanism that cannot be
bypassed by a tactic.

### 4.3 Primitive rules

The connectives `True`, `False`, `/\`, `\/`, `->`, `<->`, `not`,
`forall`, `exists`, and `=` are primitive constants with natural
deduction rules as kernel primitives. This is a deliberate departure
from HOL Light, which defines the connectives from equality. Defined
connectives would make `split` a derived rule about lambda terms, and
would make constructive tracking impossible because the definitions of
`\/` and `exists` are not constructively neutral in the presence of the
other axioms. With primitive rules the kernel is:

- `assume P`, `weaken`, `refl t`, `sym`, `trans`, `cong` (application
  congruence), `beta`, `eta`, `abs` (lambda congruence),
- intro and elim for each connective; `forall_elim` instantiates with a
  term, `exists_intro` takes a witness, `exists_elim` follows the
  eigenvariable condition,
- `subst` (rewrite under an equality, both directions),
- `inst_type` and `inst_term` for schematic theorems,
- axioms: `funext`, `propext` (both constructively neutral), `em`
  (tagged `Classical`),
- `sorry P` (tagged `Sorry`), `axiom name P` (tagged `Axiom(name)`).

`not P` is `P -> False` as today. `P <-> Q` is `P = Q` at `Prop`; the
`iff_intro` rule takes the two implications and uses `propext`, so
`split` on a biconditional behaves exactly as students expect while
rewriting with a biconditional becomes ordinary rewriting.

No choice operator, no definite description. Nothing in either course
needs them, and their absence keeps the constructive story honest.

### 4.4 Definitional principles

- `new_type name arity`: opaque type constructor (today's `sort`).
- `new_const name type`: uninterpreted constant (today's `const`,
  `func`, `pred`).
- `new_def c = body`: `c` fresh, `body` closed, type variables of `body`
  contained in those of `c`. Yields `c = body` as an untagged theorem.
  Today's `def` for both formulas and terms.
- `new_axiom name P`: yields `P` tagged `Axiom(name)`.
- `new_datatype`: takes a strictly positive declaration (recursive
  occurrences only as direct constructor arguments, possibly nested
  under other previously declared datatypes) and emits, tagged
  `Datatype(name)`: constructor injectivity, constructor distinctness,
  exhaustiveness (case analysis), and the induction principle. This
  package is trusted code, not derived, and is the one place where
  trust extends beyond the rule set. It is small and it is exactly the
  set of principles the gap audit required.
- `new_recfun`: takes defining equations, checks structural descent on
  one designated argument (any argument, not only the first; lexicographic
  descent is a later extension), and emits the equations as untagged
  theorems. Mutual recursion is a group of equations checked together.
  This is the equational rather than recursor-compiled approach because
  it keeps `simp` and `refl` computation trivial and keeps error messages
  about the student's own equations.

`Nat` is not built in. The prelude declares `data Nat | zero | succ(Nat)`
and `defrec` for `add`, `mul`, `sub`, `le`; the elaborator adds numeral
sugar and the printer prints successor towers as decimals. Every
principle the course relies on for `Nat` is then the same principle
students meet again for lists and trees.

### 4.5 Sets

`Set T` is a distinct type constructor, not a synonym for `T -> Prop`.
It is admitted by a fixed built-in instance of the same mechanism as a
typedef: constants `mem : T -> Set T -> Prop` and
`setOf : (T -> Prop) -> Set T` with the two principles
`mem(x, setOf(P)) = P(x)` and set extensionality. Union, intersection,
complement, powerset, product, and set builders are ordinary `def`s in
the prelude. Keeping `Set T` distinct means tier-1 error messages say
`Set Person` and never `Person -> Prop`, and it stops a student from
accidentally applying a set to an argument. This is the choice Isabelle
made for the same reason.

## 5. Surface language

The concrete syntax stays as close to today's as the kernel allows, so
the book and tutorials survive with light edits.

Declarations (all tiers unless noted):

```
sort Person                          -- new_type Person 0
const alice : Person
func mother : Person -> Person
pred Student(Person)                 -- const Student : Person -> Prop
def HappyMother (x : Person) : Prop := Happy(mother(x))
axiom name (params) : statement
theorem name (params) : statement := by ...
data Bit | off | on                  -- tier 2 for Nat-shaped use, tier 3 general
data List (A : Type) | nil | cons(A, List A)         -- tier 3
defrec length (l : List A) : Nat                     -- tier 2 over Nat, tier 3 general
| nil => 0
| cons h t => succ(length(t))
```

Terms and formulas:

- Application stays `f(x, y)`; the elaborator curries. Partial
  application `f(x)` of a binary `f` is allowed in tier 3 only.
- `fun x y : T => body` and `fun (x : A) (y : B) => body` as today; in
  tier 3 lambdas may appear anywhere a term may.
- Binder types are required in tiers 1 and 2 (quantifying over a
  domain is the lesson) and inferred if omitted in tier 3.
- Infix `+`, `*`, `-`, `<=`, `<` for `Nat` in tier 2 and up, with the
  prefix `add(n, m)` forms kept as aliases so the existing corpus
  parses. `∘` for composition in tier 3.
- Unicode aliases for connectives and quantifiers as today, plus
  editor abbreviations (`\and` becomes `∧`) in the browser.

Theorem parameters are ordinary free variables and type variables of
the statement. `(P : Prop)`, `(A : Type)`, `(R : A -> A -> Prop)`,
`(x : A)` all keep their spelling. Explicit instantiation
`{A := Person; P := Student}` keeps its spelling and now covers every
parameter uniformly.

Tactics: the current tactic set is kept name for name (`intro`,
`revert`, `exact`, `apply`, `split`, `left`, `right`, `cases ... with`,
`exists`, `refl`, `rewrite`, `unfold`, `simp`, `induction ... with`,
`exfalso`, `contradiction`, `by_cases`, `by_contra`, `have`, `show_goal`,
`sorry`, `trivial`, `assumption`). Additions:

- `show P`: restates the goal and fails if it does not match up to
  definitional unfolding. Cheap, and it is how students learn to say
  what they are proving.
- `obtain x hx := h` as a flat spelling of existential `cases`.
- `calc` blocks for equational chains, each step justified by a proof
  expression or `by` block. This is the single biggest ergonomic gain
  for induction proofs about arithmetic.
- `induction n generalizing m` to close the "hypothesis generalization"
  gap without `revert` gymnastics.
- `funext x` in tier 3.
- `decide` in tiers 2 and 3 for closed goals over datatypes, backed by
  the evaluator.

## 6. Tiers

A tier is an elaboration profile, not a separate logic. It is set by a
header line (`logic fol`, `logic fol_nat`, `logic hol`) or, when
absent, by the UI's tier selector; the CLI takes `--tier`. A tier
controls five things:

1. Which declaration forms parse.
2. What the type checker accepts (higher types in binders, lambdas in
   term position, type variables, partial application).
3. Which tactics exist and which are offered as hints.
4. How goals and diagnostics are printed (tier 1 never shows a lambda
   or a `->` type for a non-predicate; sets print as sets).
5. Which standard library layers load.

| | Tier 1: `fol` | Tier 2: `fol_nat` | Tier 3: `hol` |
|---|---|---|---|
| Course use | CS 250 modules 1 to 4, 6; book ch. 1 to 8 | CS 250 modules 4 (end), 8, 9, 6 arithmetic; book ch. 9, 12 | CS 250 module 10, CS 251, book ch. 10, 11 |
| Types | declared sorts, `Prop`, `Set T` | adds `Nat` | adds `data`, function types, type variables |
| Quantification | over sorts | over sorts and `Nat` | over any type |
| Predicate params | at theorem and def level only (schematic) | same | predicates are terms; quantify over them |
| Functions | uninterpreted `func` symbols | adds `defrec` over `Nat` with fixed extra params | first-class, `defrec` on any argument, mutual |
| Sets | as an opaque type with membership and algebra | same | may also be built with `setOf` and lambdas |
| Tactics | natural deduction, equality, `unfold`, `simp` on defs, classical pair | adds `induction`, `calc`, `decide`, strong induction from the library | adds `funext`, `induction` on data, `generalizing`, simp sets |
| Feedback | propositional and finite first-order countermodels | adds arithmetic testing | adds quickcheck-style testing over datatype values |
| Library | prop, fol, eq, set | nat, modular | list, fun, finite, card, graph |

Relations and functions-as-graphs (modules 6 and 8) stay in tier 1 as
they are today, because schematic predicate parameters were already a
first-order feature. Tier 3 is where functions become objects and the
same module can be redone with `f : A -> B` directly. Both versions of
the functions tutorial should exist, because the graph version is the
one that matches the course text.

Because tiers are restrictions, a tier-1 error message must be written
in tier-1 vocabulary. Concretely the elaborator carries the tier and
the diagnostic renderer has a tier-specific phrasing table. This is a
design constraint from day one, not a polish item.

## 7. Session API

One JSON API, used by the CLI's `--json`, the Wasm binding, and tests.
Requests carry the full source and an options object
`{ tier, policy: { deny_sorry, deny_axioms, deny_classical, deny_tactics } }`.

- `check(source, opts)` returns per-declaration status (`accepted`,
  `incomplete`, `trusted_axiom`, `failed`), tags, diagnostics with
  spans and repair suggestions, and policy violations.
- `goals_at(source, pos, opts)` returns the goal stack at a cursor
  position, with hypotheses, folded display forms, and hints.
- `step(source, theorem, index, opts)` returns the goal stack after the
  first `index` tactics.
- `explain(source, theorem, opts)` returns a line-by-line prose
  explanation built from the recorded tactic trace.
- `library(source, query, scope, opts)` returns matching theorems from
  the file and its imports, with statements rendered at the current tier.
- `complete(source, pos, opts)` returns tactic and name completions.

Implementation notes:

- Use `wasm-bindgen` and `serde` instead of the current manual
  alloc/free FFI and hand-built JSON strings.
- Run the checker in a Web Worker. The UI stays responsive and a
  runaway countermodel search can be cancelled by restarting the worker.
- Cache per declaration: key on the hash of the environment produced by
  the preceding declarations plus the declaration's own source. Editing
  a proof re-checks that theorem only. The current implementation
  re-checks the whole file on every keystroke, which will not survive
  tier-3 automation.
- Every diagnostic carries a span, not a line. The parser keeps spans
  on every AST node.

## 8. Browser UI

Keep the layout students know: editor on the left, goals, tactics,
explanation, library, and tactic reference on the right. Changes:

- CodeMirror 6 replaces the textarea and overlay. This gives syntax
  highlighting, inline diagnostic markers with hover text, name and
  tactic completion, Unicode abbreviation input, and multi-file tabs.
- Tier selector in the top bar, with the file header line taking
  precedence when present.
- Worker-hosted checker with a visible "checking" state and a cancel.
- Multiple files per project, stored in IndexedDB, exported and imported
  as a zip, and shareable as a compressed URL fragment for
  "here is my exact file" questions in office hours.
- Assignment mode: load an assignment manifest (section 10) that fixes
  tier, policy, allowed imports, and the theorem statements a student
  may not edit. The editor shows locked regions read-only.
- Build with Vite; deploy with the existing Pages workflow, which only
  changes in the build step.

## 9. Corpus migration and deliberate syntax changes

The existing corpus is the acceptance suite. Reuse
`scripts/check_all.sh` unchanged in spirit: positive files accept,
`mistakes`/`fallacies`/`negative` files reject every theorem, quoted
headlines match live output. Quoted output will change wholesale and is
re-captured once per milestone.

Deliberate changes to make now, because a rewrite is the only time they
are cheap:

1. Bare `rewrite h` becomes left-to-right, matching Lean and Rocq.
   The book already uses explicit arrows as house style, so the
   corpus edit is mechanical.
2. `Nat` arithmetic gains infix operators; prefix forms remain as
   aliases.
3. `cases h with | intro x hx =>` keeps working, and `obtain` is
   added; no removal.
4. Multi-line `def` bodies are allowed.
5. Theorem parameters may be hypotheses: `(h : P)` is sugar for a
   leading implication and a leading `intro h`.
6. The `_demo` collision workarounds go away because every file gets a
   module namespace by default and unqualified imports open it.

## 10. Course workflow

Carried over: `--strict`, `--deny-*`, `--json`, exit status semantics,
`sorry` propagation.

Added:

- `--deny-tactics simp,decide` so an assignment can require the
  natural deduction rules by hand.
- Assignment manifests: a small file listing tier, policy, allowed
  imports, and the expected theorem names with statements. The checker
  fails a submission whose statements differ from the manifest, closing
  the "student edits the theorem" hole the audit named.
- Tagged releases of the Pages site so a syllabus can link a frozen
  version for a term.

## 11. Milestones

Each milestone ends with something a student can use in a browser.
Sizes are relative to one another, not calendar estimates.

- M0 Kernel (small). Done. Types, terms, `Thm`, all primitive rules,
  definitional principles, tag propagation, and an adversarial test
  suite: capture, eigenvariable violations, ill-typed instantiation,
  non-positive datatypes, non-structural recursion. Nested datatypes
  (a `Rose` tree holding a `List Rose`) and lexicographic descent are
  deferred; the package rejects them with a message that says so.
- M1 Tier 1 end to end (medium). Parser with spans, elaborator, tier-1
  tactics, session API, CLI with `--json`. Acceptance: `std/prop`,
  `std/fol`, `std/eq`, `std/set`, book chapters 1 to 8 and CS 250
  tutorials 01 to 03, 05, 06, 08 all check with output re-quoted.
- M2 Browser (medium). Vite app, CodeMirror, worker, Pages deploy.
  Goals, hints, library, explanation, examples, autosave. Acceptance:
  a student can do every module-2 to module-4 exercise without the CLI.
- M3 Tier 2 (medium). `Nat` via the datatype package, numerals,
  infix, `defrec`, `induction`, `calc`, arithmetic countermodels,
  `std/nat`, `std/modular`. Acceptance: tutorials 04, 07 (Nat part),
  09; book chapters 9 and 12.
- M4 Tier 3 (large). Polymorphic `data`, general `defrec`, lambdas and
  higher types everywhere, `funext`, sets via `setOf`, recursive
  predicates, quickcheck feedback, `std/list`, `std/fun` with real
  functions, `std/finite` and `std/card` with pigeonhole as the
  acceptance theorem. Tutorials 07 and 08 redone; book chapters 10 and 11.
- M5 Course workflow (small). Manifests, locked statements,
  `--deny-tactics`, multi-file projects, share links, release tags.
- M6 Polish (ongoing). Completion, abbreviations, prose "erase the
  tactics" exercises, graph library.

M0 through M2 replace the current tool for CS 250's logic modules. M3
covers the rest of CS 250. M4 is what CS 251 needs.

## 12. Decisions

Settled with the instructor on 5 September 2026. Each one is binding
on the milestones above; reopen one only with a written reason here.

1. **Kernel rules.** Natural deduction intro and elim rules for the
   primitive connectives are kernel primitives. Connectives are not
   defined from equality.
2. **Trust tracking.** Tag sets on `Thm` (Classical, Sorry,
   Axiom(name), Datatype(name)) replace proof-object walks.
3. **Sets.** `Set T` is a distinct type constructor admitted as a
   typedef of `T -> Prop`, following Isabelle. Tier-1 messages never
   mention `T -> Prop`.
4. **Nat.** `Nat` is a prelude datatype. Numerals, decimal printing,
   and infix arithmetic are elaborator and printer sugar.
5. **Datatypes and recursion.** Datatypes are admitted by a checked
   package emitting tagged principles. Recursive definitions are
   admitted as equations after a structural-descent check on any one
   argument, with mutual recursion checked as a group.
6. **Implementation.** Rust with `wasm-bindgen` and `serde`, a fresh
   multi-crate workspace, and a Web Worker hosting the checker. No
   code reuse from `cetacea_core`.
7. **Sets and tiers.** Sets are a toggle independent of the tier
   ladder, on by default in every tier, because the course does sets
   in module 1.
8. **Prop and Bool.** Distinct. `Bool` is an ordinary datatype and
   `decide` bridges closed goals. Constructive tracking stays honest.
9. **Syntax breaks.** Bare `rewrite h` is left-to-right; multi-line
   `def` bodies; hypothesis parameters `(h : P)`; per-file namespaces
   replacing the `_demo` workarounds. Book output is re-quoted once
   per milestone.

Still open, lower stakes:

- Whether tier-3 lambdas print as `fun` or as set-builder and
  predicate sugar wherever possible. Leaning: sugar first.
- Whether to grow a declarative subset (`assume`, `show`, `obtain`,
  `calc`) inside the tactic language. Leaning: yes, inside, never as a
  second proof language.
