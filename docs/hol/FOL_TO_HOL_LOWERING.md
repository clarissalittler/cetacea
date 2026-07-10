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
| `Set A` | Predeclared `Set#id A`, with a first-order parameter class | Do **not** lower legacy sets to `A -> Prop`: doing so would silently turn the set chapters into HOL. Membership and set computation remain checked primitives. |
| New surface arrow type `A -> B` | `CoreType::Arrow(A, B)` | Higher-order when used as a quantified domain or data value. Existing arrows occur only in predicate-schema parameter kinds. |
| Proposition schema `(P : Prop)` | Rank-one proposition-symbol parameter | A meta-level schema parameter, not object-level `forall P : Prop`. This distinction preserves the propositional profile of `std/prop.ctea`. |
| Term schema `(x : A)` | Rank-one term parameter of type `A` | Stored in the theorem template context and explicitly instantiated at references. |
| Predicate schema `(R : A1 -> ... -> Prop)` | Rank-one saturated symbol parameter | Counts as FOL when used only fully applied to first-order arguments; passing, returning, partially applying, or quantifying over it is HOL. |

The first H4a checkpoint now adds the checked term/symbol-parameter context for
theorem templates. A template statement and proof are checked with those
parameters in scope, and a `TheoremRef` carries explicit type and term/symbol
arguments. Instantiation is simultaneous and capture-avoiding, including under
ambient binders. Saturated predicate-symbol templates retain an FOL receipt;
partial or value-level uses remain HOL. Surface parameter inference and lowering
from the legacy `ParamKind` forms still remain. Encoding legacy proposition and
predicate schemas as object-level quantifiers would incorrectly make almost the
entire propositional and FOL standard library HOL, so that shortcut remains
rejected.

## Declaration lowering

| Surface command | Lowering | Status |
|---|---|---|
| `import` | Load once by canonical path; aliases and namespaces point to the same stable declaration IDs and receipts. | Resolver work; no kernel change. |
| `mode constructive` | Set elaborator allowance to constructive rules. | The receipt records actual features, not the source toggle. |
| `mode classical` | Permit explicit classical evidence; do not change HOL's constructive base. | Core rules and audit are implemented; surface tactic lowering remains. |
| `sort S` | Declare a zero-parameter first-order type constructor. | Supported by H3 signatures. |
| `const c : A` | Declare a monomorphic constant `c : lower(A)`. | Supported. |
| `func f : A1 -> ... -> B` | Declare a curried constant `A1 -> ... -> B`; surface applications must be saturated in FOL mode. | Supported by core types/terms. |
| `pred R(A1, ..., An)` | Declare a curried constant `A1 -> ... -> An -> Prop`; surface applications must be saturated in FOL mode. | Supported. |
| Formula `def D ... : Prop := F` | Check a polymorphic constant with a transparent body `lambda params. lower(F)`. | H4a core declarations and delta reduction are implemented; surface parameter/body lowering remains. |
| Term `def d ... : A := t` | Check a polymorphic constant with a transparent body `lambda params. lower(t)`. | Same implemented core substrate and remaining surface work. |
| `data D | ...` | Transactionally declare a zero-parameter inductive type; a field exactly equal to `D` is `Recursive`, every other field is checked existing data. | All positive corpus datatypes use supported direct recursion. Nested/mutual recursion remains rejected. |
| `defrec f (x : D) extras : R` | Lower arms to a checked structural definition; constructor fields and recursive results become de Bruijn binders. | Core currently puts the recursive argument last, while legacy syntax puts it first. H4 must add a checked recursive-argument position (preferred) or a transparent eta wrapper. |
| `axiom a ... : P` | Store a trusted declaration template and receipt; references are kernel-visible axioms with transitive trust. | H4a core storage and receipt propagation are implemented; surface lowering remains. |
| Completed `theorem t ... : P` | Elaborate tactics to a hole-free `HolKernelProof`, check it, store a theorem template, then derive its receipt. | H3 supports the monomorphic/type-schematic subset. |
| Theorem containing `sorry` or depending on one | Retain typed draft evidence outside the kernel and store an incomplete receipt; it must never become `HolKernelProof`. | H4a core storage is implemented, including draft-to-draft references and transitive incomplete receipts; surface lowering remains. |

Failed type, positivity, termination, duplicate-name, or proof checks must leave
all signatures and import tables unchanged, matching the transactional H3 APIs.

## Term lowering

Every application is curried in the core. The elaborator inserts explicit type
arguments, checks surface arity, and rejects partial application under a
restricted FOL profile.

| Legacy `Term` | HOL lowering |
|---|---|
| `Var(name)` | Nearest resolved term/symbol parameter or local `Bound(index)`; otherwise a resolved nullary constant. |
| `App(name, args)` | Resolved constant or transparent definition, followed by explicit type application and `CoreTerm::Apply` for each argument. |
| `PredLambda { params, body }` | Nested typed `CoreTerm::Lambda` ending in `lower(body) : Prop`. Beta/delta normalization may erase it; a retained predicate value is HOL. |
| `Zero`, `Succ(t)` | Predeclared `zero` and `succ(t)`. Decimal literals are elaborator sugar. |
| `Add`, `Mul`, `Sub` | Applications of checked structural Nat definitions with the legacy computation equations. |
| `Pair`, `Fst`, `Snd` | H4a `CoreTerm::Pair`, `First`, and `Second`; both projections reduce definitionally and preserve FOL classification for first-order components. Surface lowering remains. |
| `EmptySet`, `Universe`, `Singleton`, `Union`, `Inter`, `Diff`, `Complement`, `CartProd`, `Powerset` | Explicit polymorphic applications of predeclared legacy-set operators. |
| `SetBuilder { x : A | P }` | A checked set-comprehension term whose membership reduction is `member(y, setOf(lambda x. P)) = P[y/x]`. The set value remains the first-order `Set A` wrapper. |

Nat reduction must reproduce the current `add`, `mul`, truncated `sub`, `pred`,
and `le` equations. Legacy product support needs typed pair/projection core terms
or equivalently checked primitive reductions; the present H3 core has the
product type but not those term constructors.

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

The elaborator must lower definitions and beta/delta-normalize scaffolding before
statement classification. A formula that retains a predicate value, partial
application, arrow/`Prop` quantifier, or higher-order equality is HOL. Saturated
schema predicates over first-order domains remain FOL.

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
| `Convert` | No proof node. Check the inner evidence against the target up to checked beta/delta/datatype computation. |
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

H4a now has explicit proof nodes for excluded middle, proof by contradiction,
and double-negation elimination. Each checks its proposition and subevidence,
and the audit propagates `Classical` transitively. The compatibility tactic
elaborator still needs to map the three legacy `ClassicalRule` cases to those
nodes.

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

## Gaps that must close before dual checking

These are compatibility prerequisites, not optional language expansion:

1. **Rank-one term/symbol theorem schemes.** The checked core template and
   explicit-reference substrate is implemented. Surface inference/lowering is
   still required for pervasive `(P : Prop)`, `(x : A)`, and
   `(R : A -> ... -> Prop)` parameters.
2. **Checked transparent definitions and delta reduction.** Implemented in the
   H4a core for closed monomorphic and rank-one polymorphic bodies. Definitions
   are checked before their constant is installed, can refer only to earlier
   declarations, and therefore normalize acyclically. Definition receipts
   preserve transitive dependencies while concrete uses are delta-normalized
   before fragment classification. Surface `def`, selective `unfold`, `simp`,
   and `Convert` lowering remain.
3. **Legacy first-order sets.** Add the `Set A` wrapper and audited computation
   equations; retain `set_ext` as a visible trusted axiom.
4. **Product term computation.** Implemented in the H4a core. Pairing infers a
   product type; projections reject non-products, compute definitionally on
   pairs, traverse binders/type schemes capture-safely, and retain the least
   first-order fragment when both components are first-order. Surface AST
   lowering remains.
5. **Structural recursion argument position.** Preserve the legacy recursive
   first argument for definitions such as `append`, `replicate`, and `addl`.
6. **Trusted and incomplete declaration storage.** Implemented in the H4a core.
   Typed trusted axioms are kernel-visible and transitively reported. Typed
   drafts retain holes and may reference other incomplete declarations, but
   checked theorem lookup rejects them as evidence; incomplete receipts and
   draft bodies remain available for teaching/editor workflows. Surface
   declaration lowering is still required.
7. **Explicit classical evidence.** The three core rules and transitive
   `Classical` feature are implemented; legacy tactic lowering remains.
8. **Instance-aware definition/theorem receipts.** Schematic declarations must
   not taint a first-order instance merely because a parameter could later be
   instantiated at a higher-order type, while actual HOL dependencies must
   still propagate.

The positive corpus's user datatypes (`List` and `Tree`) use only direct,
strictly positive recursion, so the H3 inductive subset is sufficient. The
corpus nevertheless exercises every gap above: proposition and predicate
schemas, transparent relation and set definitions, set comprehension, product
and Nat computation, defrec with extra parameters, trusted axioms, classical
proofs, and incomplete exercise files. None can be postponed until after the
74-file dual-check gate.

## H4 implementation order and exit evidence

1. Add term/symbol theorem-template parameters, trusted/incomplete declaration
   statuses, and explicit classical evidence with focused adversarial tests.
2. Add transparent nonrecursive definitions, product reduction, and a recursive
   argument index; prove each extension transactional and terminating.
3. Add the compatibility prelude for Nat and legacy `Set`, including golden
   reduction tests for every current builtin equation.
4. Lower types, terms, formulas, declarations, and proof nodes in isolation;
   compare canonical statements and receipts with the legacy checker.
5. Run both engines on all 74 files. Every one of the 588 recorded root
   declarations must match status, constructive/classical use, axiom/incomplete
   closure, and canonical surface statement; every one of the 38 negative
   theorems must remain rejected individually.

Only after that exact dual-check result should the driver route ordinary course
files to the HOL kernel by default.
