# Roadmap: Fixing the Friction

A concrete plan for resolving the pain points in
[`docs/book/FRICTION.md`](book/FRICTION.md), grounded in root-cause
probes of each item (July 2026). Ordered into phases by
(teaching impact × regression risk); every item names its acceptance
test. Friction item numbers refer to FRICTION.md.

## Status

- Done: Phase 0, Phase 1, Phase 2, and Phase 3. The safety net is in CI; the
  instantiation collision, targeted hints, axiom labeling, predicate
  def-name arguments, nested lambda propagation, mixed-type lambdas, and
  book debt repayment, and def-aware matching are implemented.
- Next: Phase 4, inference and counterexamples.

## Findings from triage

- **Item 9 (instantiation "expected X, got X") is a completeness bug,
  not a soundness hole.** Reproduced: with a theorem parameter named
  `x` and a local variable also named `x`, explicit instantiation
  succeeds but the subsequent premise match fails. Mechanism: after
  explicit substitution, residual occurrences of the *local* `x` in the
  instantiated premise are re-interpreted as the *schema* parameter `x`
  during unification, and the binding-consistency check conservatively
  rejects. The adversarial dual (wrongly accepting a mismatched
  premise) is correctly rejected, and the kernel's own
  capture-avoiding `instantiate_theorem` backstops soundness.
- **Items 1/2/5 share one root.** Def-in-def with an *abstract*
  predicate parameter already works (`def PreEquiv (A) (R) :=
  Reflexive(R) /\ Symmetric(R)` checks, and `h.left` projects out of
  it). What fails: (a) instantiating such a def with a *lambda*
  argument — the lambda is not substituted into the nested def
  application, yielding ``unknown predicate `R` ``; (b) passing a
  `def`-defined relation name where a predicate argument is expected
  (``unknown predicate `SameThing` ``). Item 5 (composition theorems at
  concrete graphs) is the same lambda-propagation gap surfacing through
  theorem instantiation.
- **Item 11 confirmed in the parser:** `rewrite <-` and bare `rewrite`
  both parse to `RewriteDirection::Backward`; only `->` is Forward.

## Phase 0 — Safety net (do first, half a day)

**0.1 CI verification of every `.ctea` file.** Add a repo script
(`scripts/check_all.sh`) that runs the checker over `std/`,
`examples/`, `docs/cs250/code/`, `docs/book/code/`: positive files must
exit 0 with no unexpected `incomplete` flags; `*mistakes*`,
`*fallacies*`, `*negative*` files must exit 1. Wire it into
`.github/workflows/ci.yml` after `cargo test`.
*Why first:* several later fixes change error text or matching
behavior; the book quotes checker output verbatim, so we need an
automatic tripwire for drift. (A follow-up nicety: a script that
extracts quoted error blocks from book chapters and greps them against
fresh checker output.)

## Phase 1 — Correctness and quick wins (small, independent)

**1.1 Fix the instantiation name-collision bug (item 9).** In
`theorem_application_to_proof`, unification after explicit substitution
must only treat *unbound* schema parameters as open: filter the
`schema_params` handed to `UnifyState` down to parameters not already
fixed by explicit arguments (or freshen schema parameter names apart
from the local context before matching). Acceptance: the `congr_pred`
probe with colliding `x` checks; the adversarial variant still fails
with its accurate message; new regression tests for both.

**1.2 Targeted error hints (items 12, 13).** In
`tactic_error_suggestions`: (a) when `apply` fails against a theorem
that has predicate parameters, suggest
`apply thm {P := fun m : Nat => ...}` — `P` is never inferable, so the
error site knows the fix; (b) extend the "cannot induct while
hypothesis depends on it" message with the standard move (state the
theorem with `forall`, `intro` inside the arms). Acceptance: both
messages carry `try:` blocks; book ch12/ch9 mistakes quotes updated and
re-verified.

**1.3 Axiom label (item 16).** Print `accepted axiom foo (trusted)`
instead of `(constructive)`. Grep book/tutorials for quoted axiom
lines and update them (Phase 0's tripwire confirms).

## Phase 2 — Predicate-parameter expressiveness (the big teaching payoff)

The relations/functions arc (book ch7–8) is the biggest beneficiary.
Ship in four independent steps, each with its own acceptance tests.

**2.1 Def-names as predicate arguments (item 2).** Where a predicate
argument is expected and the name resolves to a `FormulaDef` whose
parameters are all terms (after inferable type parameters), eta-expand
it to `PredicateArg::Lambda` (`fun a b => SameThing(a, b)`) during
validation/elaboration. Acceptance:
`def SameMood (x y : Person) : Prop := ...` then `Reflexive(SameMood)`
checks; ch7's exercises drop their repeated lambdas.

**2.2 Lambda propagation through nested defs (items 1, 5).** In
`instantiate_formula_def` / the schema-substitution `PredApp` case:
when a def application's predicate argument is a lambda and the def
body applies another def to that parameter, substitute the lambda as
the inner def's predicate argument (rather than attempting — and
failing — a first-order predicate substitution). Beta-apply only where
the parameter is applied to terms. Acceptance:
`def Bijective (A) (B) (G) := Injective(G) /\ Surjective(G)` usable at
`Bijective(fun x y : T => x = y)`; `std/fun.ctea` gains a real
`Bijective` def; `compose_injective` instantiable at
`{F := fun x y : Nat => succ(x) = y; ...}` so "succ ∘ succ is
injective" becomes the ch8 payoff it wanted to be.

**2.3 Mixed-type lambdas (item 3).** `LambdaParam` already stores a
per-parameter type; the restriction is purely syntactic. Add
parenthesized per-binder annotations — `fun (x : Person) (y : Nat) =>
AgeIs(x, y)` — keeping the current `fun x y : T =>` shorthand.
Secondarily, when the expected predicate signature is fixed by the
def/theorem being applied, allow omitted annotations to be filled from
it. Acceptance: the graph of `age : Person -> Nat` is writable as a
lambda; ch8's "note on the lambda's typing" workaround paragraph is
deleted.

**2.4 Book debt repayment.** After 2.1–2.3: restore ch7 "name the
relation, then classify it" flow, ch8 mixed-type graphs and the
concrete-composition payoff, and update FRICTION.md's ledger. This is
where the phase proves it worked.

## Phase 3 — Def-aware matching (item 4; highest regression risk, do after Phase 2's tests exist)

Status: done.

`apply` normalizes goals (unfolding defs, computing built-ins) while
theorem statements stay folded, so folded library lemmas stop matching
the subgoals `apply` itself created, and whether `unfold` is needed
depends invisibly on goal history.

**3.1 Match under def-normalization.** In `apply_plan_for_goal` and
premise/`exact` matching, compare both sides after
`normalize_formula_defs` (matching is already unification; this makes
the *inputs* agree on unfolding).
**3.2 Present goals folded.** When emitting subgoals, retain the
original (folded) formula for display and hint purposes where the
parent goal was folded — separate "display formula" from "match
formula" in `Goal` if needed.
Acceptance: ch6's killed exercise (`apply subset_antisymm` then
`exact subset_union_left {...}`) works and returns to the book;
`apply modeq_zero_to_divides` works bare against a folded
`Divides(5, 20)` goal; an `unfold`-after-`apply` no longer errors with
"no occurrence". Regression net: full test suite + Phase 0 sweep, plus
the entire book corpus.

## Phase 4 — Inference and counterexamples

**4.1 `have` annotation-driven inference (item 7).** Elaborate
`have h : F := thm` by unifying `thm`'s statement against `F` (reuse
the `apply` machinery with `F` as the target) instead of bare
inference. Acceptance: `have hle : le(2, 2) := le_refl`.

**4.2 Positional args to theorem references (item 8).** Re-test after
Phases 2–3 (the `modeq_refl m x` failure routes through def-unfolded
statements); if still broken, either walk positional args through the
*folded* statement or emit a targeted error suggesting braces.

**4.3 First-order countermodels (item 6).** For failed goals whose
signature is small (abstract sorts, declared predicates, equality, no
arithmetic): enumerate domains of size 1–3 and all predicate
interpretations under a strict budget (≤ 2 sorts, ≤ 3 predicates,
≤ 2^12 interpretations); report in the established voice — "false in a
2-element domain where Knows = {(a,b)}". Bail silently over budget.

**4.4 Arithmetic countermodels.** For pure `Nat` (in)equality goals
with free variables, test all assignments over 0..8; report "false
when n = 2". Trigger wherever the propositional countermodel hook
already fires. Together 4.3/4.4 extend the book's best pedagogical
device ("the statement is wrong — stop proving") past chapter 3.

## Phase 5 — Papercuts (each small; batch with book re-verification)

**5.1 Decimal numerals in output (item 14).** Print `succ` towers as
decimals in `Term`'s `Display` (mixed forms like `succ(n)` stay
symbolic). Requires re-verifying every quoted error in the book/
tutorials — do it in one sweep with Phase 0's tripwire.
**5.2 `simp` no-progress (item 10).** Downgrade from error to accepted
no-op carrying a diagnostic note ("this `simp` did nothing — consider
deleting it"), so teaching scripts stop being fragile to upstream
normalization changes. Update the handful of tests asserting the
error.
**5.3 Rewrite directions (item 11).** Keep current semantics (flipping
bare `rewrite` would silently re-orient every existing proof).
Document all three forms in USAGE.md — explicitly stating `<-` ≡ bare ≡
right-to-left — and adopt explicit arrows as house style in the book
with one clear warning box for Lean-habituated readers.
**5.4 Occurrence-selection transparency (item 17).** When `rewrite`
has several candidate occurrences, note which was rewritten
("rewrote the first occurrence of `0`") so mistakes localize to the
right line.

## Parked (design before scheduling)

- **Namespaces (item 18):** qualified names (`nat.add_comm`) and import
  aliasing touch the parser, `Env`, and every lookup; the `_demo`
  convention holds until Phases 2–4 land. Design note first.
- **Aggressive goal computation (item 15):** behavior is defensible and
  chapters now narrate it; revisit only if Phase 3 doesn't already
  soften the surprise (folded display should).
- **Polymorphic data types:** unchanged from README milestones;
  requires polymorphic signatures threaded through the kernel.

## Standing rules

1. Every fix lands with a regression test reproducing the original
   friction entry verbatim.
2. Any change to checker output re-runs the full book/tutorial corpus
   (Phase 0 script) and updates quoted output in the same commit.
3. Anything touching substitution or instantiation gets an adversarial
   soundness probe alongside its completeness test — this codebase has
   earned that rule.
