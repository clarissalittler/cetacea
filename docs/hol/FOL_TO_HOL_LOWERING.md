# Mechanical FOL-to-HOL Lowering Map

Date: 2026-07-10

## Purpose and compatibility contract

This is the Phase H3.5 lowering specification for the current Cetacea surface
language. It maps the legacy `Type`, `Term`, `Formula`, declaration, and
`DraftProof` forms to the parallel constructive HOL core. It is deliberately a
mechanical compatibility map, not a proposal to reinterpret existing course
files as a new language.

The compatibility elaborator must preserve:

- the canonical displayed surface statement;
- constructive versus explicitly classical proof use;
- accepted, incomplete, and trusted-axiom status;
- transitive theorem, axiom, incomplete, induction, recursion, and HOL
  dependencies;
- import identity and namespace behavior; and
- every positive and negative result in the 74-file semantic oracle.

Names are resolved before lowering. The core receives stable IDs, explicit type
arguments, and typed de Bruijn term variables. Checked declarations receive
hole-free kernel evidence; incomplete declarations retain separately checked
draft evidence that the kernel lookup path cannot consume. Source names and
spans remain in the elaborator for diagnostics.

## Type and parameter lowering

| Legacy form | HOL core form | Fragment rule / note |
|---|---|---|
| `Nat` | Predeclared inductive constructor `Nat#id` | First-order inductive type. `zero` and `succ` are checked constructors. |
| Named sort `S` | Zero-argument `TypeConstructorId` | First-order unless its declaration says otherwise. |
| Type schema parameter `(A : Type)` | `TypeParameter::first_order(id)` | Legacy `Type` arguments cannot be arrows or `Prop`, so this is narrower and more accurate than `Any`. |
| `Prod A B` | `CoreType::Product(A, B)` | First-order iff both components are first-order. H4a now includes typed pair/projection terms and definitional projection reduction. |
| `Set A` | Distinguished `Set#id A`, with a first-order parameter class | Implemented in H4a. `Set` rejects `Prop`, arrows, and unconstrained higher-order parameters; it is never lowered to `A -> Prop`. |
| New surface arrow type `A -> B` | `CoreType::Arrow(A, B)` | Higher-order when used as a quantified domain or data value. Existing arrows occur only in predicate-schema parameter kinds. |
| Proposition schema `(P : Prop)` | Rank-one proposition-symbol parameter | A meta-level schema parameter, not object-level `forall P : Prop`. This distinction preserves the propositional profile of `std/prop.ctea`. |
| Term schema `(x : A)` | Rank-one term parameter of type `A` | Stored in the theorem template context and explicitly instantiated at references. |
| Predicate schema `(R : A1 -> ... -> Prop)` | Rank-one saturated symbol parameter | Counts as FOL when used only fully applied to first-order arguments; passing, returning, partially applying, or quantifying over it is HOL. |

The H4 compatibility layer has the checked term/symbol-parameter context for
theorem templates. A template statement and proof are checked with those
parameters in scope, and a `TheoremRef` carries explicit type and term/symbol
arguments. Instantiation is simultaneous and capture-avoiding, including under
ambient binders. Saturated predicate-symbol templates retain an FOL receipt;
partial or value-level uses remain HOL. Surface parameter inference and all
legacy `ParamKind` forms are connected. Encoding legacy proposition and
predicate schemas as object-level quantifiers would incorrectly make almost the
entire propositional and FOL standard library HOL, so that shortcut remains
rejected.

## Declaration lowering

| Surface command | Lowering | Status |
|---|---|---|
| `import` | Load once by canonical path; aliases and namespaces receive stable qualified declaration IDs and receipts. | Connected through the legacy resolver; repeated path/alias pairs replay once. |
| `mode constructive` | Set elaborator allowance to constructive rules. | The receipt records actual features, not the source toggle. |
| `mode classical` | Permit explicit classical evidence; do not change HOL's constructive base. | Finished production tactic evidence lowers to explicit audited rules. |
| `sort S` | Declare a zero-parameter first-order type constructor. | Parser-independent declaration lowering is implemented transactionally. |
| `const c : A` | Declare a monomorphic constant `c : lower(A)`. | Parser-independent declaration lowering is implemented transactionally. |
| `func f : A1 -> ... -> B` | Declare a curried constant `A1 -> ... -> B`; surface applications must be saturated in FOL mode. | Parser-independent declaration lowering and persistent arity metadata are implemented. |
| `pred R(A1, ..., An)` | Declare a curried constant `A1 -> ... -> An -> Prop`; surface applications must be saturated in FOL mode. | Parser-independent declaration lowering and persistent arity metadata are implemented. |
| Formula `def D ... : Prop := F` | Check a polymorphic constant with a transparent body `lambda params. lower(F)`. | Parser-independent parameter/body lowering, checking, registration, and delta reduction are implemented. |
| Term `def d ... : A := t` | Check a polymorphic constant with a transparent body `lambda params. lower(t)`. | Parser-independent parameter/body lowering, checking, registration, and delta reduction are implemented. |
| `data D | ...` | Transactionally declare a zero-parameter inductive type; a field exactly equal to `D` is `Recursive`, every other field is checked existing data. | Parser-independent lowering is implemented for the corpus's direct recursion; nested/mutual recursion remains rejected. |
| `defrec f (x : D) extras : R` | Lower arms to a checked structural definition; constructor fields and recursive results become de Bruijn binders. | Parser-independent lowering uses legacy binder order and recursive index zero; focused `length` and `append` computations pass. |
| `axiom a ... : P` | Store a trusted declaration template and receipt; references are kernel-visible axioms with transitive trust. | Parser-independent parameter/statement lowering, storage, reference lowering, and transitive trust are implemented. |
| Completed `theorem t ... : P` | Elaborate tactics to a hole-free `HolKernelProof`, check it, store a theorem template, then derive its receipt. | Every existing `DraftProof` variant is connected to the opt-in production shadow driver. |
| Theorem containing `sorry` or depending on one | Retain typed draft evidence outside the kernel and store an incomplete receipt; it must never become `HolKernelProof`. | Parser-independent lowering retains holes outside the kernel and supports checked draft-to-draft references with transitive incomplete receipts. |

Failed type, positivity, termination, or duplicate-name checks now leave both
core signatures and the persistent compatibility name/arity/data catalogs
unchanged. Proof and import replay is transactional within the sidecar and a
shadow failure never changes legacy acceptance.

## Term lowering

Every application is curried in the core. The elaborator inserts explicit type
arguments, checks surface arity, and rejects partial application under a
restricted FOL profile.

| Legacy `Term` | HOL lowering |
|---|---|
| `Var(name)` | Nearest resolved term/symbol parameter or local `Bound(index)`; otherwise a resolved nullary constant. |
| `App(name, args)` | Resolved constant or transparent definition, followed by explicit type application and `CoreTerm::Apply` for each argument. |
| `PredLambda { params, body }` | Nested typed `CoreTerm::Lambda` ending in `lower(body) : Prop`. Beta/delta normalization may erase it; a retained predicate value is HOL. |
| `Zero`, `Succ(t)` | Predeclared checked constructors `zero` and `succ(t)`. Decimal literals are elaborator sugar. Parser-independent lowering is implemented. |
| `Add`, `Mul`, `Sub` | Applications of checked structural Nat definitions. The terminating structural equations and all closed numerals compute in the kernel; seven checked induction theorems discharge the additional legacy simp orientations through equality elimination. |
| `Pair`, `Fst`, `Snd` | H4a `CoreTerm::Pair`, `First`, and `Second`; both projections reduce definitionally and preserve FOL classification for first-order components. Parser-independent lowering is implemented. |
| `EmptySet`, `Universe`, `Singleton`, `Union`, `Inter`, `Diff`, `Complement`, `CartProd`, `Powerset` | H4a first-order set terms with checked element types and definitional membership equations. Parser-independent lowering is implemented. |
| `SetBuilder { x : A | P }` | H4a checked comprehension under an element binder; membership substitutes capture-avoidantly into `P`. The set value remains the first-order `Set A` wrapper. Parser-independent lowering is implemented. |

The compatibility prelude now installs inductive `Nat`, its constructors,
structural `add`, `mul`, truncated `sub`, and a nested-structural `le`; it also
installs the distinguished first-order `Set`. Primary open equations and every
closed numeral reduce definitionally. The legacy normalizer additionally uses
overlapping equations on either argument. Those equations are not stable under
substitution (the two `mul` orientations already give different open normal
forms after constructor substitution), so copying them into HOL conversion
would compromise the new kernel. H4 therefore installs checked secondary simp
lemmas and makes compatibility `simp`/`Convert` lowering emit their evidence.
That path is now implemented: conversion computes a terminating legacy-oriented
rewrite path, synthesizes capture-safe motives, supports both directions, and
retains even no-op theorem dependencies with a constant motive.
`pred` remains the ordinary checked `std/nat.ctea` structural definition; an
internal predecessor used by `sub` does not occupy that surface name.

Legacy set compatibility needs a narrow, audited primitive layer. Membership
normalization must reproduce the current equations for empty, universe,
singleton, union, intersection, difference, complement, cartesian product,
powerset, and comprehension. Subset lowers to
`forall x, member x A -> member x B`. Set equality is typed equality on
`Set A`; extensionality remains the explicit trusted `set_ext` declaration and
must not enter definitional equality.

## Formula lowering

| Legacy `Formula` | HOL `CoreTerm : Prop` |
|---|---|
| `True`, `False` | `CoreTerm::Truth`, `CoreTerm::Falsity` |
| `Atom(P)` | Resolved nullary proposition constant or proposition-symbol template parameter |
| `PredApp(R, args)` | Fully applied resolved predicate/symbol parameter |
| `Eq(left, right)` | `CoreTerm::Equality { ty: inferred_shared_type, ... }` |
| `In(x, A)` | Fully applied polymorphic `member[element_type] x A`, then legacy set reduction if applicable |
| `Subset(A, B)` | `forall x : element_type, member x A -> member x B` |
| `And`, `Or`, `Implies` | Corresponding primitive proposition form |
| `Forall x : A, P` | `CoreTerm::Forall { domain: lower(A), body: lower(P) }` |
| `Exists x : A, P` | `CoreTerm::Exists { domain: lower(A), body: lower(P) }` |

The parser-independent elaborator now lowers every current `Type`, `Term`, and
`Formula` form, including expected-type-directed predicate lambdas, explicit
rank-one instantiation, and shadowing-safe de Bruijn binders. It checks each
produced term immediately. Declaration/import resolution and proof lowering are
connected through the shadow driver. Definitions and beta/delta scaffolding are
normalized before statement classification. A formula that retains a
predicate value, partial application, arrow/`Prop` quantifier, or higher-order
equality is HOL. Saturated schema predicates over first-order domains remain
FOL.

## Proof-evidence lowering

Tactics are not trusted and need no one-to-one migration. They continue to
transform goals, but emit the following explicit core evidence.

| Legacy `DraftProof` | HOL evidence |
|---|---|
| `Hyp(name)` | `HolDraftProof::Hypothesis(index)` after local-name resolution |
| `TrueIntro` | `TruthIntro` |
| `FalseElim` | `FalseElim` with the lowered target |
| `AndIntro`, `AndElimLeft`, `AndElimRight` | Direct corresponding nodes |
| `OrIntroLeft`, `OrIntroRight`, `OrElim` | Direct nodes; case names resolve to hypothesis indices |
| `ImpIntro`, `ImpElim` | Direct nodes; the named premise becomes the nearest proof hypothesis |
| `EqRefl(t)` | `EqualityRefl(lower(t))` |
| `EqSubst` | `EqualityElim` with an explicit typed lambda motive synthesized from the equality, source formula, target formula, direction, and selected occurrence |
| `Convert` | Definitional conversions erase; legacy secondary arithmetic conversions become chains of checked theorem references and `EqualityElim` motives. |
| `ForallIntro`, `ForallElim` | Direct nodes with a typed term binder/argument |
| `ExistsIntro`, `ExistsElim` | Direct nodes with capture-avoiding binder shifting |
| `NatInd` | `Induction` over the predeclared `Nat` signature |
| `DataInd` | `Induction` over the resolved checked inductive signature; constructor fields and IHs follow metadata order |
| `TheoremRef { name, subst }` | Stable theorem ID plus explicit type and term/symbol arguments; dependencies come from the checked node, never a caller list |
| `Classical { rule, ... }` | An explicit classical rule or reference to a designated classical principle; audit inserts `Classical` and constructive mode rejects it |
| `Sorry` | Draft-only hole. The containing declaration is incomplete and never converts to kernel proof evidence. |

`EqSubst` is expressible in the H3 kernel, but the compatibility elaborator must
retain the rewrite occurrence chosen by the tactic (or deterministically
reconstruct the unique motive). It may not turn rewrite into a trusted
conversion.

The parser-independent proof lowerer now implements every row above. Named
hypotheses become checked indices; nested quantifier/existential contexts shift
existing hypotheses; Nat and data induction abstract the resolved scrutinee
into an explicit motive; theorem references lower type, proposition, predicate,
and term substitutions; and equality substitution enumerates one rewritten
occurrence to reconstruct a capture-safe motive, including reverse rewrites.
`Convert` first uses HOL definitional equality. When legacy arithmetic
normalization is stronger, it uses only the checked secondary prelude theorems
and explicit equality elimination. The overlapping shortcuts therefore remain
outside kernel conversion without blocking existing course proofs.

H4a has explicit proof nodes for excluded middle, proof by contradiction,
and double-negation elimination. Each checks its proposition and subevidence,
and the audit propagates `Classical` transitively. All three legacy
`ClassicalRule` cases are connected.

## Receipts, modes, and countermodels

The old constructive/classical mode and the new statement profile are separate:

- source mode controls which proof principles the elaborator may emit;
- statement classification produces `prop`, `fol`, `fol+induction`, or `hol`;
- checked evidence and dependencies add induction, recursion, HOL, classical,
  axiom, and incomplete requirements; and
- an assignment policy compares the full transitive receipt with its allowed
  profile and imports.

A first-order-looking theorem that references an HOL theorem remains HOL. H3.5
now demonstrates this with the Color/Bit cardinality statement: its direct
proof is `fol+induction`, while the proof through the generic function-quantified
transport theorem is `hol`.

Countermodel search stays on the legacy surface representation during H4. It
may run only when the new normalized statement receipt certifies a fragment the
particular model finder supports. No countermodel result participates in proof
checking.

## Compatibility prerequisites closed by the shadow gate

These are compatibility prerequisites, not optional language expansion. All
eight are now connected through the opt-in command/import shadow driver:

1. **Rank-one term/symbol theorem schemes.** The checked core template and
   explicit-reference substrate is implemented. The parser-independent scope
   now lowers `(P : Prop)`, `(x : A)`, and `(R : A -> ... -> Prop)` parameters
   and infers explicit type applications. Theorem declarations and references
   replay from the legacy driver's canonical parameter substitution.
2. **Checked transparent definitions and delta reduction.** Implemented in the
   H4a core for closed monomorphic and rank-one polymorphic bodies. Definitions
   are checked before their constant is installed, can refer only to earlier
   declarations, and therefore normalize acyclically. Definition receipts
   preserve transitive dependencies while concrete uses are delta-normalized
   before fragment classification. Surface `def`, selective `unfold`, `simp`,
   and `Convert` evidence is connected. Arithmetic conversions use checked
   compatibility theorems and equality elimination, not extra reduction.
3. **Legacy first-order sets.** Implemented in the H4a core. The distinguished
   wrapper accepts only first-order elements. Membership computes for empty and
   universal sets, singleton, Boolean operations, Cartesian products,
   powersets/subset, and capture-safe comprehensions. Quantification over sets
   remains FOL. Set equality does not compute extensionally: `set_ext` is stored
   and propagated as a visible trusted axiom, as in the legacy standard library.
   The compatibility prelude, surface lowering, declarations, and imports are
   connected.
4. **Product term computation.** Implemented in the H4a core. Pairing infers a
   product type; projections reject non-products, compute definitionally on
   pairs, traverse binders/type schemes capture-safely, and retain the least
   first-order fragment when both components are first-order. Declaration and
   proof integration is connected.
5. **Structural recursion argument position.** Implemented in the H4a core.
   The datatype argument has an explicit checked source index; definition types,
   reduction scrutinees, and generated recursive calls all preserve it.
   Out-of-range positions fail transactionally. The graph spike now uses
   natural `append left right`, while generic `map` continues to demonstrate a
   checked last recursive argument. Legacy `defrec` lowering selects source
   index zero and preserves the legacy branch-binder order.
6. **Trusted and incomplete declaration storage.** Implemented in the H4a core.
   Typed trusted axioms are kernel-visible and transitively reported. Typed
   drafts retain holes and may reference other incomplete declarations, but
   checked theorem lookup rejects them as evidence; incomplete receipts and
   draft bodies remain available for teaching/editor workflows.
   Declaration, reference, import, and driver integration is implemented in
   shadow mode.
7. **Explicit classical evidence.** The three core rules and transitive
   `Classical` feature are implemented, and all three legacy proof forms lower
   from finished production tactic evidence to explicit audited evidence.
8. **Instance-aware definition/theorem receipts.** Implemented in the H4a core.
   Every checked theorem reference records its instantiated statement and exact
   local term context. The dependency receipt reclassifies that statement while
   preserving the declaration's status, proof features, axioms, incomplete
   dependencies, and transitive closure. Thus an unrestricted generic identity
   is abstractly HOL, its `Nat` instance contributes only FOL, and its predicate
   instance still contributes HOL. Nested generic theorem references are
   recursively re-specialized, including references underneath local binders.
   Definition bodies normalize at their actual use and retain their transitive
   receipts. Surface reference lowering is connected.

The positive corpus's user datatypes (`List` and `Tree`) use only direct,
strictly positive recursion, so the H3 inductive subset is sufficient. The
corpus nevertheless exercises every gap above: proposition and predicate
schemas, transparent relation and set definitions, set comprehension, product
and Nat computation, defrec with extra parameters, trusted axioms, classical
proofs, and incomplete exercise files. The passing 74-file shadow gate therefore
exercises the full compatibility boundary rather than a propositional subset.

## H4 implementation order and exit evidence

1. Add term/symbol theorem-template parameters, trusted/incomplete declaration
   statuses, and explicit classical evidence with focused adversarial tests.
2. Add transparent nonrecursive definitions, product reduction, and a recursive
   argument index; prove each extension transactional and terminating.
3. Add the compatibility prelude for Nat and legacy `Set`, including golden
   reduction tests for every sound structural equation and checked lemmas for
   the legacy secondary simp orientations. Done: the primary equations remain
   definitional; seven internal induction theorems prove the secondary
   orientations, and compatibility conversion constructs explicit motives.
4. Lower types, terms, formulas, declarations, and proof nodes in isolation;
   compare canonical statements and receipts with the legacy checker.
   Done: parser-independent lowering covers every listed form, and the opt-in
   sidecar consumes the same canonical command/import stream without affecting
   legacy acceptance.
5. Run both engines on all 74 files. Every one of the 588 recorded root
   declarations must match status, constructive/classical use, axiom/incomplete
   closure, and canonical surface statement; every one of the 38 negative
   theorems must remain rejected individually. Done in shadow mode:
   `python3 scripts/hol_shadow.py check` reports 74/74 matching files,
   588/588 root receipts, 9,389/9,389 accepted declaration occurrences, and
   zero mismatches. The frozen legacy oracle independently retains the exact 38
   negative rejections and diagnostic identities.

At the parser-independent prelude/lowering checkpoint, the linked release CLI
is 2,747,480 bytes and the raw Wasm module is 1,349,914 bytes. The latter remains
below the 1.5 MB review trigger. The exact legacy oracle still reports 74 files,
588 root declarations, and 38 intended-negative theorems. After adding the
first transactional declaration slice, the corresponding artifacts are
2,760,416 and 1,349,967 bytes; Wasm growth is only 53 bytes because the new
parser-independent path is not yet reachable from the production facade. With
all theorem statuses and legacy proof nodes lowered, they are 2,766,776 and
1,349,297 bytes respectively. At the command-linked shadow checkpoint, the
native CLI is 3,346,328 bytes. The browser crate does not expose this native
migration tool and disables the `hol-shadow` Cargo feature, leaving the raw Wasm
module at 1,351,837 bytes—2,540 bytes over the prior checkpoint and below the
1.5 MB review line. Default routing remains a separate decision: passing the
shadow gate authorizes H5 policy/result integration and cutover evaluation, not
silent replacement of the legacy authority.

The first native teaching-policy slice raises the CLI artifact to 3,396,656
bytes. It consumes shadow receipts only in the native frontend, so the
feature-isolated Wasm module remains 1,351,837 bytes.

At the versioned assignment-manifest checkpoint, the native CLI is 3,482,976
bytes and the feature-isolated Wasm module is 1,351,852 bytes. Recording
resolved-import provenance and full canonical signatures changes the browser
artifact by only 15 bytes; manifest enforcement itself remains native-only.

The H5 pre-receipt classifier reuses the same parameter lowering and least-
fragment calculation before proof checking, without declaring a theorem.
Native shadow diagnostics dispatch propositional, first-order, or bounded Nat
countermodels only from that result; HOL and classification failures suppress
weaker-fragment claims. Shadow JSON exposes the audit record even when the proof
is rejected. The corpus gate classifies 600/600 elaborated root theorem
statements, including 36 proof-negative exercises; two intentionally ill-typed
negative signatures are rejected earlier by legacy statement validation.
The corresponding release artifacts are 3,495,424 bytes for the native CLI and
1,351,920 bytes for Wasm. The feature-disabled browser path retains only the
refactored legacy fallback dispatch, a 68-byte increase.

The native editor path now has an explicit opt-in sidecar seam. Each TUI or
line-mode goal/explanation analysis created with `--hol-shadow` replays its
command/import prefix through one compatibility checker, classifies the full
theorem signature before tactic stepping, carries that fragment through every
goal snapshot, and suppresses countermodel engines outside the certified
fragment. The legacy editor APIs are unchanged, and the feature-disabled Wasm
surface does not expose the new entry points. At this checkpoint the release
artifacts are 3,500,184 bytes for the native CLI and 1,351,199 bytes for Wasm.

H6 begins by replacing three test-local list declarations with one reusable,
transactional `ListLibrary`. Its unrestricted rank-one element parameter can
serve both HOL clients and concrete restricted clients: tests classify open Nat
membership as `fol+induction` and a `List Prop` predicate instance as `hol`.
Graph path concatenation and direct finite cardinality retain their constructive
`fol+induction` receipts after adopting the package; the generic cardinality
transport dependency remains honestly `hol`. The package is not connected to
surface imports yet. The corresponding release artifacts are 3,501,856 bytes
for the native CLI and 1,361,312 bytes for Wasm.
