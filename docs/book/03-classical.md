# Chapter 3 — The Classical Moves: Excluded Middle and Friends

> **Files for this chapter:**
> [`code/ch03-examples.ctea`](code/ch03-examples.ctea) ·
> [`code/ch03-mistakes.ctea`](code/ch03-mistakes.ctea) (intended to fail) ·
> [`code/ch03-exercises.ctea`](code/ch03-exercises.ctea) ·
> [`code/ch03-solutions.ctea`](code/ch03-solutions.ctea)

## 3.1 A proof that names no names

Here is one of the most charming proofs in mathematics. Claim: *there
exist irrational numbers `a` and `b` such that `a^b` is rational.*

Consider `x = sqrt(2) ^ sqrt(2)`. Either `x` is rational or it isn't.

- If `x` is rational: take `a = b = sqrt(2)`. Both irrational, and
  `a^b = x` is rational. Done.
- If `x` is irrational: take `a = x` and `b = sqrt(2)`. Then
  `a^b = (sqrt(2)^sqrt(2))^sqrt(2) = sqrt(2)^2 = 2`. Rational. Done.

Airtight — and yet, at the end, you cannot answer the question "so
*which* pair is it?" The proof establishes that a pair exists while
declining to produce one. It works by splitting on "either `x` is
rational or it isn't" without ever finding out which.

That splitting step has a name: the **law of excluded middle** — for
any proposition `P`, it holds that `P \/ not P`. There is no third
option, no middle ground. It sounds too obvious to even mention. So
here's the surprise this chapter is built around:

> **None of the rules from Chapter 2 can prove `P \/ not P`.**

Try it. To prove an "or" you must go `left` or `right` — commit to
proving `P` outright, or `not P` outright — about an *arbitrary,
unknown* `P`. Neither is possible. Every tactic you know preserves a
hidden property: whatever it proves, it proves with *evidence in hand*.
The Chapter 2 rules form what's called **constructive** (or
*intuitionistic*) logic; adding excluded middle yields **classical**
logic, the one truth tables silently assume. Cetacea speaks both, keeps
them cleanly separated, and makes you say out loud which one you're
using. This chapter is about the boundary.

## 3.2 What you can do without it

First, let's be precise about what's *not* missing. Chapter 2's
Exercise 2.6 proved double-negation *introduction*, fully
constructively:

```text
theorem not_not_intro (P : Prop) : P -> not not P := by
  intro hp
  intro hnp
  apply hnp
  exact hp
```

Read the statement with Chapter 2 eyes: `not not P` unfolds to
`(P -> False) -> False`. So: given `P`, and given a refutation of `P`,
produce absurdity — just apply the refutation. No case splits, no
appeals to "it must be one or the other." Evidence in, evidence out.

The reverse direction, `not not P -> P`, is the one the end of Chapter
2 dared you to prove. Unfold it: given a refutation of a refutation of
`P`, produce... an actual proof of `P`. From material that consists
entirely of functions expecting `P`-refutations, you must manufacture a
`P`. There is nothing to build it *from*. It's not that the proof is
hard to find; in constructive logic it provably does not exist.

Classically, though, "it's not false" and "it's true" are
interchangeable. To get that power, you ask for it — one line at the
top of the file (or anywhere above the theorems that need it):

```text
mode classical
```

With that switch flipped, two new tactics come online.

## 3.3 `by_cases`: excluded middle as a move

The tactic `by_cases h : P` splits any proof into two futures: one
where `h : P`, one where `h : not P`. It's `cases` on an invisible
`P \/ not P` that you get for free. Excluded middle itself is now a
two-case triviality:

```text
theorem em_demo (P : Prop) : P \/ not P := by
  by_cases h : P
  left
  exact h
  right
  exact h
```

After `by_cases h : P` there are two goals — first
`h : P |- P \/ not P`, then `h : not P |- P \/ not P` — and the
remaining tactics feed the goals in order, just as after `split`: the
first two lines close goal one, the last two close goal two. (No
indented arms here, unlike `cases ... with`.)

Notice what the proof of the "or" *doesn't* tell you: which side holds.
That's the sqrt(2) proof's structure exactly — and it's the trade
this whole chapter is about. A constructive proof of `A \/ B` always
tells you which of `A` or `B` it proved (it had to go `left` or
`right` with evidence). A classical proof only promises the disjunction
is true. Certainty, without the receipt.

## 3.4 `by_contra`: proof by contradiction

The second classical tactic is the beloved workhorse of math classes
everywhere. When your goal is `P`, the tactic `by_contra hn` says:
"suppose, for contradiction, `not P`" — it hands you `hn : not P` and
changes the goal to `False`. Now the dare from Chapter 2 falls in four
lines:

```text
theorem dne_demo (P : Prop) : not not P -> P := by
  intro hnn
  by_contra hn
  apply hnn
  exact hn
```

State after `by_contra`: `hnn : not not P, hn : not P |- False`. And
`hnn` is literally a `False`-producer that eats exactly what `hn` is.
`apply hnn`, `exact hn`, done. This theorem is **double-negation
elimination**, and it is exactly as strong as excluded middle: assume
either one and you can derive the other. Two doors into the same room.

A word on terminology, because it prevents a very common confusion.
Chapter 2's modus tollens plays a game that *looks* like proof by
contradiction: to prove `not P`, assume `P` and derive `False`. But
that's just the introduction rule for `not` — an ordinary `intro` —
and it's fully constructive. The classical move is proving a
*positive* statement `P` by refuting its refutation. Assume-and-refute
to prove a negation: free. Assume-and-refute to prove a *fact*: costs
classical.

## 3.5 De Morgan's hard direction

Chapter 2's Exercise 2.5 proved `not (P \/ Q) -> not P /\ not Q`
constructively, and its mirror partner `not P \/ not Q -> not (P /\ Q)`
is constructive too. De Morgan's laws seem cheap. But one direction of
one law holds out: from "not both," conclude "one or the other fails" —

```text
not (P /\ Q) -> not P \/ not Q
```

Feel the constructive obstruction first: to prove that "or" with
evidence, you must *point at* the failing conjunct. But the assumption
only says the pair can't both hold — it doesn't say which one gives
out. No receipt, no constructive proof. Classically, we don't need the
receipt:

```text
theorem demorgan_hard (P Q : Prop) : not (P /\ Q) -> not P \/ not Q := by
  intro h
  by_contra hn
  apply h
  split
  by_contra hnp
  apply hn
  left
  exact hnp
  by_contra hnq
  apply hn
  right
  exact hnq
```

This is the most intricate proof in the book so far, so let's narrate
it. After `intro h` and `by_contra hn`:

```text
h : not (P /\ Q), hn : not (not P \/ not Q)  |-  False
```

`apply h` — absurdity will come from feeding `h` the very thing it
denies: `|- P /\ Q`, which `split`s into `|- P` and `|- Q`.

Now the elegant part. To prove `P` (a positive fact — this is why the
inner `by_contra`s are needed), suppose `hnp : not P`. Then
`not P \/ not Q` holds — go `left` with `hnp` — but `hn` denies
exactly that disjunction. Contradiction, so `P` stands. The `Q` goal is
the same trick on the `right`. Three `by_contra`s in one proof:
classical logic doing what it does best, extracting positive facts from
a pile of negations.

## 3.6 The contrapositive, both ways

Every conditional `P -> Q` has a contrapositive `not Q -> not P`, and
"a statement and its contrapositive are equivalent" is a staple of
proof-writing courses. Cetacea splits that staple in half:

- **Forward** — `(P -> Q) -> (not Q -> not P)`: this is modus tollens
  (Section 2.5), proved constructively.
- **Backward** — `(not Q -> not P) -> (P -> Q)`: classical only.

```text
theorem contrapositive_rev (P Q : Prop) : (not Q -> not P) -> P -> Q := by
  intro h
  intro hp
  by_contra hnq
  apply h hnq
  exact hp
```

After `by_contra hnq` we hold `hnq : not Q`, so `h hnq` — the
hypothesis `h` applied to `hnq`, a proof expression just like the ones
`exact` takes — is a proof of `not P`. Applying *that* to the goal
`False` leaves `|- P`, and `hp` finishes.

So "prove the contrapositive instead" is, secretly, a classical
maneuver. The equivalence your instructor promised is a biconditional
whose two directions live in different logics — the surprise promised
back in Section 2.7.

## 3.7 Modes: the boundary as a checked feature

Why does Cetacea make you *ask* for classical logic instead of just
allowing it? Because "did I use excluded middle?" is genuinely useful
information, and hand-tracking it is hopeless. The mode system makes
the checker track it for you.

The rules of the game:

- Files start in `mode constructive`. Classical tactics (`by_cases`,
  `by_contra`) and classical library theorems (`em`, `dne`) are
  rejected, with an error naming the offending rule.
- `mode classical` unlocks them for everything after that line.
- The checker reports what each proof **actually used** — permission
  is not the same as use.

That last point is worth seeing. This theorem sits *after* `mode
classical` in the examples file:

```text
theorem mode_is_measured (P : Prop) : P -> P := by
  intro h
  exact h
```

Run the file and read the verdicts:

```text
accepted theorem not_not_intro (constructive)
accepted theorem em_demo (classical)
accepted theorem dne_demo (classical)
accepted theorem demorgan_hard (classical)
accepted theorem contrapositive_rev (classical)
accepted theorem mode_is_measured (constructive)
```

`mode_is_measured` had classical permission and didn't spend it, so it
is certified `(constructive)`. Think of the mode tags as nutrition
labels for proofs: a `(constructive)` disjunction proof contains a
computable answer to "which side?"; a `(classical)` one may not. Both
are real proofs. Only one tells you where the treasure is buried.

This is also why the book runs constructive-by-default: not because
classical reasoning is wrong, but because the label is only meaningful
if you reach for `mode classical` deliberately, when a proof genuinely
needs it — the way this chapter's proofs do.

## 3.8 Common mistakes: classical moves without a license

The file [`code/ch03-mistakes.ctea`](code/ch03-mistakes.ctea) contains
two perfectly correct classical proofs — in a file that never says
`mode classical`. Intended to fail; run it and read:

```text
error: /home/left_adjoint/cetacea/docs/book/code/ch03-mistakes.ctea:12: theorem `em_needs_permission` failed: by_cases uses excluded middle for `P` and requires classical mode
  note: target: P \/ (not P)
  help: Switch modes or avoid the classical rule
    This tactic uses classical reasoning. Put `mode classical` before the theorem, or prove a constructive version instead.
    try:
      mode classical
```

```text
error: /home/left_adjoint/cetacea/docs/book/code/ch03-mistakes.ctea:21: theorem `dne_needs_permission` failed: by_contra introduces a classical proof of `P`
  note: target: P
  help: Switch modes or avoid the classical rule
    This tactic uses classical reasoning. Put `mode classical` before the theorem, or prove a constructive version instead.
    try:
      mode classical
```

In both cases the checker names the classical rule you used, tells you
the two honest ways out ("switch modes or avoid the rule"), and offers
the one-line fix under `try:`. When you hit this error in your own
work, it's asking you a real question: *does this theorem need
classical logic, or did I just reach for `by_contra` out of habit?*
Surprisingly often, an `intro` (if the goal is a negation) or a
`cases` (if you're holding a disjunction) does the job constructively.

## 3.9 Exercises

Open [`code/ch03-exercises.ctea`](code/ch03-exercises.ctea). Exercise
3.1 sits in the constructive section of the file and must stay there;
the rest have classical permission. As always, clear the `sorry` flags
— and this time, also *read the mode tags* on your accepted theorems.

- **Exercise 3.1** `not not (P \/ not P)` — constructive! Excluded
  middle can't be proved constructively, but its double negation can,
  which is philosophically delicious. Hint: `intro h`, then `apply h`
  — you'll need to do it twice, going `right` the first time.
- **Exercise 3.2** `not P \/ P` — excluded middle, mirrored. Warm-up
  for `by_cases`.
- **Exercise 3.3** `(P -> Q) -> not P \/ Q` — every implication
  secretly asserts an "or." (The converse is constructive; this
  direction isn't.)
- **Exercise 3.4** `(not P -> Q) -> P \/ Q` — if denying `P` forces
  `Q`, one of them must hold.
- **Exercise 3.5** `not (P -> Q) -> P /\ not Q` — a broken promise
  pins down both truth values: the only way `P -> Q` fails is `P` true,
  `Q` false. The `P` half needs its own `by_contra`.
- **Exercise 3.6 (challenge)** `((P -> Q) -> P) -> P` — **Peirce's
  law**, the strangest beast in this menagerie: no negations anywhere
  in the statement, yet it is exactly as classical as excluded middle.
  Start with `by_contra hn`, and use `hn` to construct the `P -> Q`
  that the premise demands.

Solutions: [`code/ch03-solutions.ctea`](code/ch03-solutions.ctea).

---

*Next: [Chapter 4 — Everyone, Someone, No One](04-quantifiers.md), where
propositions finally get to be* about *things, and we meet the two
quantifiers that power all of mathematics.*
