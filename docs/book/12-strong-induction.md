# Chapter 12 — Strong Induction, and Where to Go Next

> **Files for this chapter:**
> [`code/ch12-examples.ctea`](code/ch12-examples.ctea) ·
> [`code/ch12-mistakes.ctea`](code/ch12-mistakes.ctea) (intended to fail) ·
> [`code/ch12-exercises.ctea`](code/ch12-exercises.ctea) ·
> [`code/ch12-solutions.ctea`](code/ch12-solutions.ctea)

## 12.1 When the rung below isn't the one you need

Chapter 9's induction hands the step case exactly one gift: the claim
for `k`, the rung immediately below `succ(k)`. Usually that's the
right gift. But mathematics is full of definitions that reach further
down. Fibonacci numbers look back two steps. "Divide by two and
repeat" arguments — halve a number, halve a list — land somewhere
around the *middle* of the ladder, not the rung below. For all of
these, the honest shape of the argument is: "assuming the claim for
**every** number smaller than this one, it holds here too." That's
**strong induction** (your textbook may say *complete* or
*course-of-values* induction), and it's the last proof principle in
this book.

Here's the toy that shows the problem in its purest form. A hallway
of numbered light bulbs is wired oddly: bulb 0 is off, and each bulb
`succ(k)` copies whatever bulb `pred(k)` shows — the bulb *two*
positions back (recall `pred` from `std/nat.ctea`: the predecessor,
with `pred(0) = 0`). In Cetacea, with the trust machinery from
Chapter 10 out in the open:

```text
func bulb : Nat -> Nat

axiom bulb_zero : bulb(0) = 0
axiom bulb_step (k : Nat) : bulb(succ(k)) = bulb(pred(k))
```

Claim: every bulb is off — `bulb(n) = 0` for all `n`. Follow the
wiring by hand: bulb 1 is `bulb(succ(0))`, which copies
`bulb(pred(0)) = bulb(0)` — off. Bulb 2 copies `bulb(pred(1))`,
which is `bulb(0)` again — off. Bulb 3 copies bulb 1, bulb 4 copies
bulb 2, bulb 5 copies bulb 3 — off, off, off: from here on, each
bulb genuinely reaches *two* positions back. Every light in the
hallway is off, two interleaved chains of dominoes falling. Obvious.
Now try to prove it.

## 12.2 Watching ordinary induction come up short

The mistakes file ([`code/ch12-mistakes.ctea`](code/ch12-mistakes.ctea),
intended to fail) makes the Chapter 9 attempt. The base case is
`bulb_zero`. In the step case, rewrite with the wiring equation and
offer the induction hypothesis:

```text
theorem one_rung_short (n : Nat) : bulb(n) = 0 := by
  induction n with
  | zero =>
      exact bulb_zero
  | succ k ih =>
      rewrite -> bulb_step {k := k}
      exact ih
```

```text
error: docs/book/code/ch12-mistakes.ctea:25: theorem `one_rung_short` failed: exact proof does not solve the goal: proof has type `bulb(k) = 0`, but expected `bulb(pred(k)) = 0`
  note: target: bulb(pred(k)) = 0
```

(The generic `help:` paragraph is trimmed, as usual by now.) There it
is, stated more crisply than any prose could: the hypothesis
is about `k`, the goal is about `pred(k)`, and they are different
rungs. Ordinary induction gave us the rung below; the wiring reaches
two below. This isn't a tactic problem — no rearrangement of `simp`s
and `rewrite`s will conjure `bulb(pred(k)) = 0` out of
`bulb(k) = 0`. We need a principle that hands the step case *more*.

## 12.3 Strong induction is a theorem (you could have proved it)

In `std/nat.ctea`:

```text
theorem strong_induction (P : Nat -> Prop) (n : Nat)
  : P(0)
    -> (forall k : Nat, (forall m : Nat, le(m, k) -> P(m)) -> P(succ(k)))
    -> P(n)
```

Read the step premise slowly, because it's the whole upgrade: to prove
`P(succ(k))`, you may assume — not just `P(k)` — but
`forall m : Nat, le(m, k) -> P(m)`: the claim at **every** rung up to
and including `k`. The entire history of the climb. Ordinary
induction's gift was one fact; strong induction's is a *universally
quantified* fact you can spend at any smaller number you like, as
many times as you like.

Notice what this is **not**: it is not a new tactic, not a new
primitive, not an axiom. It's a `theorem`, stated in the quantifier
language of Chapter 4 and *proved* in the standard library — by
ordinary Chapter 9 induction, constructively, from two little order
lemmas (`le_zero_inv` and `le_succ_inv`, via a helper called
`strong_induction_bounded`). Open `std/nat.ctea` and read the proof;
you have every tool it uses. This is the endgame the book has been
building toward: the library doesn't just *contain* proof principles,
it *manufactures* them, and "stronger" induction is a consequence of
plain induction, not an extra assumption about numbers. Your `accepted`
lines will confirm it — using `strong_induction` adds nothing to an
`axioms:` list.

Because it's a theorem, you invoke it like one: with `apply`. One
wrinkle: its parameter `P` is a *predicate*, and the checker won't
guess a lambda for you (Section 12.5 shows the refusal). You spell it
out, in the explicit-instantiation braces of Chapter 4:

```text
theorem sub_self_strong (n : Nat) : sub(n, n) = 0 := by
  apply strong_induction {P := fun m : Nat => sub(m, m) = 0; n := n}
  refl
  intro k
  intro hk
  simp
  apply hk
  exact le_refl
```

This is Chapter 9's `sub_self_demo` re-proved, as a first contact
where the logic is familiar and only the scaffolding is new. Walk it.
`P := fun m : Nat => sub(m, m) = 0` says which property of `m` we're
climbing with — the lambda is the statement with the induction
variable held blank, exactly like Chapter 4's predicates. The `apply`
then leaves the theorem's two premises as goals, in order:

1. `|- sub(0, 0) = 0` — the base. `refl`.
2. `|- forall k : Nat, (forall m : Nat, le(m, k) -> sub(m, m) = 0) -> sub(succ(k), succ(k)) = 0`
   — the step, as one big quantified formula.

The step goal is just Chapter 4 material: `intro k`, then `intro hk`
to assume the history, leaving

```text
k : Nat, hk : forall m : Nat, le(m, k) -> sub(m, m) = 0  |-  sub(succ(k), succ(k)) = 0
```

`simp` computes the goal down to `sub(k, k) = 0`. Now spend the
history: `apply hk` matches its conclusion against the goal
(instantiating `m := k`) and leaves the toll, `|- le(k, k)`, which
the library's `le_refl` pays. That last exchange is worth a beat:
strong induction made us *prove our target is low enough on the
ladder* before handing over the fact. At `m = k` — the old induction
hypothesis — the toll is trivial. The freedom to pick `m` lower is
what we're about to use for real.

## 12.4 All the bulbs are off

Two tolls need paying in the bulb proof, so first, two little order
lemmas — ordinary Chapter 9 inductions; neither is in the library:

```text
theorem le_n_succ_n (n : Nat) : le(n, succ(n)) := by
  induction n with
  | zero =>
      simp
      trivial
  | succ k ih =>
      simp
      exact ih

theorem pred_le (n : Nat) : le(pred(n), n) := by
  induction n with
  | zero =>
      simp
      trivial
  | succ k ih =>
      simp
      exact le_n_succ_n
```

(The second's `succ` arm is sneaky-simple: `simp` computes
`pred(succ(k))` to `k`, leaving `le(k, succ(k))` — the previous lemma
at `k`, no `ih` needed.)

Now the theorem the chapter came for:

```text
theorem all_bulbs_off (n : Nat) : bulb(n) = 0 := by
  apply strong_induction {P := fun m : Nat => bulb(m) = 0; n := n}
  exact bulb_zero
  intro k
  intro hk
  rewrite -> bulb_step {k := k}
  apply hk
  exact pred_le
```

Same scaffolding as `sub_self_strong`, and the interesting moment is
at the end. After `intro k`, `intro hk`, and the rewrite along the
wiring equation, the state is

```text
k : Nat, hk : forall m : Nat, le(m, k) -> bulb(m) = 0  |-  bulb(pred(k)) = 0
```

— precisely the goal that stumped ordinary induction in Section 12.2.
But `hk` is not one rung; it's the whole history. `apply hk`
instantiates it at `m := pred(k)` and asks only that we prove the
toll, `|- le(pred(k), k)` — and that's `pred_le`. Done. Compare the
two proofs line by line: where `one_rung_short` had `exact ih` and
died, `all_bulbs_off` has `apply hk; exact pred_le` and lives. Strong
induction is exactly that trade — every use of the hypothesis now
costs a small `le` proof, and in exchange you may reach *any* rung
below.

Run the examples file and read the verdicts, Chapter 10 eyes on:

```text
accepted theorem sub_self_strong (constructive)
accepted theorem le_n_succ_n (constructive)
accepted theorem pred_le (constructive)
trusted axiom bulb_zero
trusted axiom bulb_step
accepted theorem all_bulbs_off (constructive; axioms: bulb_step, bulb_zero)
```

`all_bulbs_off` carries the two wiring axioms we declared — the
receipt is honest — and nothing else. Strong induction, for all its
power, added no trust: it was proved, not postulated. That's the
book's whole ethic in one line of output.

## 12.5 Common mistakes

The mistakes file's first entry was dissected in Section 12.2. The
second is the scaffolding error everyone makes once:

**Forgetting to say what `P` is.** A bare `apply strong_induction`
feels like it should work — the goal is right there:

```text
error: docs/book/code/ch12-mistakes.ctea:31: theorem `which_predicate` failed: cannot use theorem `strong_induction` here: its conclusion `P(n)` does not match goal `bulb(n) = 0`
  note: target: bulb(n) = 0
  help: Provide the predicate parameter
    Theorem `strong_induction` has predicate parameter `P`, and predicate parameters are not inferred from the goal. Spell `P` out with a lambda.
    try:
      apply strong_induction {P := fun m : Nat => ...}
```

The checker must match the conclusion `P(n)` against `bulb(n) = 0`,
which means *inventing* the lambda `fun m : Nat => bulb(m) = 0` — and
inferring predicates is a genuinely harder problem than inferring
terms, one Cetacea deliberately doesn't attempt. (Which `P` did you
mean? `fun m => bulb(m) = 0`? `fun m => bulb(n) = 0`, constant in
`m`? Both match.) When a theorem parameter is a predicate, write the
braces. The lambda you write is the induction; choosing it *is* the
proof decision.

## 12.6 Exercises

Open [`code/ch12-exercises.ctea`](code/ch12-exercises.ctea). The
order lemmas are provided at the top; the recurrences are declared
with `func` and `axiom` like the chapter's bulbs — watch your
`axioms:` receipts.

- **Exercise 12.1** `le(0, mul(n, n))` — scaffolding practice: both
  goals after the `apply` close with `simp` then `trivial`. Get the
  lambda and the goal order right and it's four short lines.
- **Exercise 12.2** an `echo` that copies **one** step back
  (`echo(succ(k)) = echo(k)`; `echo(0) = 0`): prove `echo(n) = 0`.
  Strong induction covers ordinary induction as the special case
  "spend the history at `m := k`" — what proof of `le(k, k)` does the
  library hand you?
- **Exercise 12.3 (challenge)** a `siren` wired like the bulbs but
  with `siren(0) = 1`: prove `siren(n) = 1`. Model it on
  `all_bulbs_off`; `pred_le` is waiting at the top of the file.

Solutions: [`code/ch12-solutions.ctea`](code/ch12-solutions.ctea).

## 12.7 The end of the first-order spine

That's the original first-order course. You can state claims with connectives and
quantifiers; prove them with introduction and elimination rules; tell
constructive certainty from classical certainty and read the label;
compute with equality; build sets, relations, and functions; define
data and recursion; and climb every ladder from plain induction to
strong. On Cetacea's `hol` branch, the book now continues for two chapters
to test finite mathematics against the same teaching standard.

**What changed after the first draft.** The original ending listed
polymorphic data and cardinality as missing. Chapters 13 and 14 are the
executable result of removing those two limits: `List A` is a checked,
versioned library type; `HasCard` expresses finite enumeration; and assignment
policies keep concrete first-order exercises separate from genuinely
higher-order `map`. Arithmetic still stops short of division (`div` and `mod`),
and the broader honest inventory remains in
[`docs/cs250/LIMITATIONS.md`](../cs250/LIMITATIONS.md). Extending the book before
declaring the redesign finished lets real exercises find the next edges.

**The same ideas, at full scale.** Everything you learned transfers
to the industrial-strength proof assistants — **Lean**, **Rocq**
(long known as Coq), and **Agda** — because Cetacea is a deliberate
miniature of them. `theorem ... := by` with `intro`, `exact`,
`apply`, `cases`, `induction` is recognizably Lean; Rocq's tactic
names differ in spelling, not spirit; Agda drops tactics and has you
write the proof term directly. `data` and `defrec` are the training
wheels for their inductive types and recursive definitions —
polymorphic, this time. The `axioms:` receipt is Lean's
`#print axioms`. Where `std/` has a few dozen lemmas, Lean's mathlib
has hundreds of thousands, with a community formalizing research
mathematics in it. If this book was fun, that's the door. It will
feel familiar within the hour, in both the good ways and the
error-message ways.

**Proofs as programs.** One idea to pack for the trip, because it
quietly organized this whole book. You may have noticed a pattern of
resemblances: `intro h` assumes an input, so a proof of `P -> Q`
behaves like a *function* from proofs to proofs. A constructive proof
of `exists` *contains* a witness you could extract (Chapter 3's whole
story). A universal statement, we said in Chapter 4, is "a kind of
function." Definition by recursion and proof by induction have the
same arms (Chapter 10). This is not coincidence; it is the
**Curry–Howard correspondence**: propositions are types, proofs are
programs, and checking a proof is type-checking a program. It's why
`refl` could treat running `double(3)` as proving a theorem, why
constructive proofs compute and classical ones may not, and why the
tools above can double as programming languages. "The proof is the
program" is arguably the deepest idea a first logic course can hand
you — and you've been using it all term without being told.

One more run of the checker, then. Every theorem in this part of the book was
rejected before it was accepted — that was the deal from Chapter 1,
and it held: rejection is the normal state of a proof in progress.
As you continue into finite mathematics, that's the habit worth keeping. State
the claim. Run the check. Read the error like a friend wrote it.

```text
accepted
```

---

*Next: [Chapter 13 — Finite Types and Honest Counting](13-finite-types.md) ·
back to the [outline](OUTLINE.md).*
