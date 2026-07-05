# Chapter 1 — Propositions and How to State Them

> **Files for this chapter:**
> [`code/ch01-examples.ctea`](code/ch01-examples.ctea) ·
> [`code/ch01-mistakes.ctea`](code/ch01-mistakes.ctea) (intended to fail) ·
> [`code/ch01-exercises.ctea`](code/ch01-exercises.ctea) ·
> [`code/ch01-solutions.ctea`](code/ch01-solutions.ctea)

## 1.1 A claim you can check

Here's an argument you have made, in some form, dozens of times:

> The syllabus says the final is worth 40% and the projects are worth
> 40%. So the projects are worth 40%.

Obviously fine, right? You were told two things joined by an "and," and
you kept one of them. Nobody would ask you to justify that step.

But *why* is it fine? And how would you convince someone — or
something — that has no common sense at all, and accepts only moves
that follow explicit rules?

That question is the whole subject of this book. Logic is the study of
which conclusions follow from which assumptions, purely because of the
*shape* of the statements involved — not because of what they happen to
be about. The argument above works just as well as:

> It is raining and the bus is late. So the bus is late.

Same shape, different topic, equally airtight. By the end of this
chapter you will have stated that shape formally and had a program —
the Cetacea proof checker — verify your reasoning, one step at a time.
No partial credit, no "close enough," and also no doubt: when the
checker says `accepted`, your proof is correct.

## 1.2 What is a proposition?

A **proposition** is a statement that is either true or false. Not
"true for me," not a question, not a command — a definite claim.

These are propositions:

- "It is raining."
- "17 is prime."
- "Every even number greater than 2 is the sum of two primes."

Note that you don't need to *know* whether a statement is true for it
to be a proposition. Nobody knows whether the third one (Goldbach's
conjecture) is true. It's still a claim with a definite truth value —
we just haven't found out which.

These are **not** propositions:

- "Close the door." (a command — it can be obeyed, not true)
- "Is it Tuesday?" (a question)
- "x + 1 = 5" (depends on x; it becomes a proposition once you say
  what x is — we'll handle this properly in Chapter 4)

When we study the shapes of arguments, the internal details of a
proposition usually don't matter, so we abbreviate whole statements
with single capital letters. Let `P` stand for "it is raining" and `Q`
for "the bus is late." These letters are called **atomic** propositions
— atoms, because we don't split them further.

## 1.3 Connectives: building big claims out of small ones

Interesting claims are compound. We build them from atoms using five
**connectives**. Here they are, with the ASCII spellings you'll type in
Cetacea:

| English | Name | Cetacea | Example |
|---|---|---|---|
| "P and Q" | conjunction | `P /\ Q` | raining and late |
| "P or Q" | disjunction | `P \/ Q` | raining or late (or both!) |
| "not P" | negation | `not P` | not raining |
| "if P then Q" | implication | `P -> Q` | if it rains, the bus is late |
| "P if and only if Q" | biconditional | `P <-> Q` | rains exactly when late |

(If you've seen the textbook symbols ∧, ∨, ¬, →, ↔ — Cetacea accepts
those too, as exact aliases for the ASCII spellings. `P ∧ Q → Q` means
the same as `P /\ Q -> Q`. This book sticks to ASCII in code because
it's what your keyboard produces without a fight.)

Each connective has a precise meaning, given by how the truth of the
compound depends on the truth of the parts. For "and," the story is
short: `P /\ Q` is true when both parts are true, and false otherwise.

| P | Q | P /\ Q |
|---|---|---|
| T | T | **T** |
| T | F | F |
| F | T | F |
| F | F | F |

"Or" is true when *at least one* part is true — including when both
are. This is the "inclusive or": "soup or salad" in logic does not rule
out taking both. (English often means the exclusive kind; logic had to
pick one, and it picked inclusive. Chapter 2 will show the checker
firmly rejecting a proof that treats "or" as "and.")

| P | Q | P \/ Q |
|---|---|---|
| T | T | **T** |
| T | F | **T** |
| F | T | **T** |
| F | F | F |

"Not" just flips: `not P` is true exactly when `P` is false.

Implication `P -> Q` trips everyone up once, so let's be careful. It
claims: *whenever P holds, Q holds too.* It is false in exactly one
situation — `P` true, `Q` false — because that's the only situation
that breaks the promise. In particular, when `P` is false, the promise
`P -> Q` holds trivially; a claim like "if it rains, I'll bring an
umbrella" cannot be called a lie on a sunny day.

| P | Q | P -> Q |
|---|---|---|
| T | T | **T** |
| T | F | F |
| F | T | **T** |
| F | F | **T** |

Finally, `P <-> Q` says the two always match: it's `(P -> Q) /\ (Q -> P)`
— literally, in Cetacea; the checker treats `<->` as exactly that
conjunction of two implications, which will matter when we prove one in
Chapter 2.

**Formalizing practice.** Before any proving, it's worth translating a
few sentences. Let `R` = "it is raining", `B` = "the bus is late",
`U` = "I bring an umbrella".

- "It's raining but the bus is on time" → `R /\ not B`. ("But" is just
  "and" with attitude.)
- "If it rains, I bring an umbrella" → `R -> U`.
- "I bring an umbrella only if it rains" → `U -> R`. (Careful — "only
  if" points the arrow the other way! The sentence says umbrella-days
  are rain-days.)
- "It never rains without the bus being late" → `R -> B`.

There are also two special atomic propositions: `True`, which just
holds, and `False`, the proposition with no proof — the formal stand-in
for "impossible." `False` will become surprisingly important when we
get to negation in Chapter 2.

## 1.4 Your first Cetacea file

Time to make a claim and defend it. Create a file `first.ctea`
containing:

```text
mode constructive

theorem my_first_proof (P : Prop) : P -> P := by
  intro h
  exact h
```

Read it line by line:

- `mode constructive` — we'll explain modes properly in Chapter 3; for
  now it means "play by the strictest rules." It's the default, but we
  state it anyway, like writing your name on the exam.
- `theorem my_first_proof` — we're stating a claim and naming it.
- `(P : Prop)` — "let P be any proposition." Whatever we prove will
  hold no matter what P stands for. This is how atomic propositions
  enter a Cetacea file: as parameters of the theorem.
- `: P -> P` — the claim itself: if P, then P. Modest, but true.
- `:= by` — "and here's the proof, as a list of steps." Each step is
  called a **tactic**.

Now the proof. At every moment, the checker tracks a **goal**: what
you've got (hypotheses), and what you still owe (the target). We'll
write goal states like this throughout the book:

```text
P : Prop  |-  P -> P
```

Everything left of `|-` is what you have; right of it is what you must
prove. (Read `|-` aloud as "yields" or just "prove.")

The target is an implication, and the natural first move on an
implication is: *assume the "if" part, then establish the "then" part.*
That's the tactic `intro h` — it moves `P` from the target into your
hypotheses, under the name `h`:

```text
P : Prop, h : P  |-  P
```

Now you owe a proof of `P`, and you're holding one — it's `h`. The
tactic `exact h` says "the thing I owe is exactly `h`." Goal closed,
proof complete.

Check it (from the repository root):

```sh
target/debug/cetacea_cli first.ctea
```

```text
accepted theorem my_first_proof (constructive)
```

That `accepted` line is the entire point of this book. It means a
program with no goodwill, no context, and no imagination verified every
step. When it says accepted, you *know*.

One more, the easiest theorem in the world — `True` needs no
assumptions, and the tactic `trivial` proves it:

```text
theorem true_is_easy : True := by
  trivial
```

The companion file
[`code/ch01-examples.ctea`](code/ch01-examples.ctea) contains every
proof from this chapter (plus an `import` line that loads Cetacea's
standard library — we won't need it until later chapters, but all our
companion files start that way so you get used to seeing it). Run it
now and watch all eight theorems get accepted.

## 1.5 Proving an "and": `split`

Back to the syllabus. Suppose you have separately established that the
final is worth 40% (`P`) and that the projects are worth 40% (`Q`). Can
you conclude the conjunction `P /\ Q`? Of course — but now let's see
what "of course" looks like as checkable steps.

```text
theorem and_intro_demo (P Q : Prop) : P -> Q -> P /\ Q := by
  intro hp
  intro hq
  split
  exact hp
  exact hq
```

First, the statement. `P -> Q -> P /\ Q` reads "if P, then if Q, then
P and Q" — stacked arrows are how we say "from these two assumptions,
conclude this." (Arrows group to the right: it parses as
`P -> (Q -> (P /\ Q))`.)

Two `intro`s take the two assumptions, and we arrive at:

```text
hp : P, hq : Q  |-  P /\ Q
```

Here's the new move. To prove an "and," you must prove *both* sides —
there's no shortcut. The tactic `split` turns one goal into two:

```text
hp : P, hq : Q  |-  P        (first goal)
hp : P, hq : Q  |-  Q        (second goal)
```

The remaining tactics are served to the goals in order: `exact hp`
pays off the first, `exact hq` the second. Two goals opened, two goals
closed, theorem accepted.

This is the general shape of tactic proofs: some tactics *close* the
current goal (`exact`, `trivial`), and some *transform* it, possibly
into several goals (`intro`, `split`). Your proof is done when no goals
remain.

## 1.6 Using an "and": `.left` and `.right`

The syllabus argument at the top of the chapter went the other way: you
were *given* the conjunction and wanted one half. If `h` is a proof of
`P /\ Q`, then `h.left` is a proof of `P` and `h.right` is a proof of
`Q`:

```text
theorem and_elim_left_demo (P Q : Prop) : P /\ Q -> P := by
  intro h
  exact h.left

theorem and_elim_right_demo (P Q : Prop) : P /\ Q -> Q := by
  intro h
  exact h.right
```

So a proof of an "and" is like a box with two compartments: `split`
packs the box, `.left` and `.right` unpack it. Let's do both in one
proof — take a conjunction apart and rebuild it in the other order:

```text
theorem and_swap_demo (P Q : Prop) : P /\ Q -> Q /\ P := by
  intro h
  split
  exact h.right
  exact h.left
```

Follow the goals. After `intro h`:

```text
h : P /\ Q  |-  Q /\ P
```

After `split`, two goals — and notice the *order*: the target was
`Q /\ P`, so goal one is `Q` and goal two is `P`:

```text
h : P /\ Q  |-  Q        (first goal)
h : P /\ Q  |-  P        (second goal)
```

Which is why the proof says `exact h.right` *first*. Handing the
checker `h.left` here is this chapter's most common mistake, and in
Section 1.8 we'll do it on purpose and read the resulting error.

Projections chain, by the way: if `h : (P /\ Q) /\ R`, then
`h.left.right` proves `Q`. You'll want that for Exercise 1.4.

## 1.7 Implication, more seriously

You've already used `intro` twice, so you know the intro rule for
implication: to prove `P -> Q`, assume `P` and prove `Q`. Let's stress
it slightly. What if an assumption is useless?

```text
theorem keep_the_first (P Q : Prop) : P -> Q -> P := by
  intro hp
  intro hq
  exact hp
```

Perfectly legal: we assumed `Q` and never touched it. An implication
doesn't promise its hypothesis is *needed*, only that the conclusion
holds when the hypothesis does. (Look at the truth table for `->`
again if this feels slippery.)

Now the other direction — *using* an implication you've been given.
Suppose you hold `P`, and also a voucher `P -> Q` that converts proofs
of `P` into proofs of `Q`. Cashing the voucher is the job of the tactic
`apply`:

```text
theorem cash_the_check (P Q : Prop) : P /\ (P -> Q) -> Q := by
  intro h
  apply h.right
  exact h.left
```

After `intro h`, the state is:

```text
h : P /\ (P -> Q)  |-  Q
```

`h.right` is the voucher `P -> Q`, and our target is exactly its
conclusion. `apply h.right` reasons *backwards*: "you want `Q`; this
implication produces `Q`; so it's enough to produce `P`." The goal
becomes:

```text
h : P /\ (P -> Q)  |-  P
```

— which `h.left` settles. This backwards step is called *modus ponens*
and it is the engine of most proofs; Chapter 2 gives it a proper
treatment.

## 1.8 Common mistakes (let's make them on purpose)

The file [`code/ch01-mistakes.ctea`](code/ch01-mistakes.ctea) contains
four deliberately broken proofs — and unlike every other companion
file, it is *supposed* to fail. Run it:

```sh
target/debug/cetacea_cli docs/book/code/ch01-mistakes.ctea
```

You'll get one error per broken theorem (the checker doesn't stop at
the first — each theorem is judged independently). Let's read them.
Everything below is the checker's real output; only the leading path
will differ on your machine.

**Mistake 1: grabbing the wrong half.** The proof of `P /\ Q -> Q`
says `exact h.left`:

```text
error: /home/left_adjoint/cetacea/docs/book/code/ch01-mistakes.ctea:13: theorem `wrong_half` failed: exact proof does not solve the goal: proof has type `P`, but expected `Q`
  note: target: Q
  help: Match the proof to the target
    `exact` closes the goal only when the expression proves the current target `Q`. Check which hypothesis (or which projection, `.left`/`.right`) proves exactly this target; for an implication or theorem whose conclusion matches, use `apply`.
```

Learn the anatomy, because every Cetacea error has it: the **line
number** of the failing tactic, what you **offered** (`proof has type
P`), what was **owed** (`expected Q`, repeated in `note: target:`), and
a `help:` paragraph suggesting a fix. Here the fix is obvious:
`h.right`.

**Mistake 2: `split` before its time.** `split` works on a goal that
*is* a conjunction — `P -> Q -> P /\ Q` is an implication (the `/\` is
buried under two arrows):

```text
error: /home/left_adjoint/cetacea/docs/book/code/ch01-mistakes.ctea:17: theorem `split_too_soon` failed: split expects a conjunction goal
  note: target: P -> Q -> P /\ Q
  help: Use `split` only for conjunctions
    `split` works when the current target has the form `P /\ Q`; here it is `P -> Q -> P /\ Q`.
```

Rule of thumb: look at the target's *outermost* connective. Arrows
outside? `intro` first.

**Mistake 3: declaring victory at halftime.** `split`, prove the first
goal, forget the second:

```text
error: /home/left_adjoint/cetacea/docs/book/code/ch01-mistakes.ctea:20: theorem `forgot_a_goal` failed: unsolved goal `Q`
  note: target: Q
```

Every goal you open, you must close. The error names the orphan.

**Mistake 4: reusing a name.** Two `intro h` in a row:

```text
error: /home/left_adjoint/cetacea/docs/book/code/ch01-mistakes.ctea:29: theorem `name_reuse` failed: `intro` would shadow existing hypothesis `h`
  note: target: P -> P
```

Each hypothesis needs its own name. The convention this book follows:
`h` when there's only one, otherwise short mnemonic names like `hp`
("hypothesis proving P"), `hq`, `hpq` ("hypothesis proving P -> Q").

**Bonus: getting un-lost with `show_goal`.** The last theorem in the
mistakes file isn't wrong so much as unfinished: it inserts the tactic
`show_goal`, which deliberately stops the proof and reports where you
are:

```text
error: /home/left_adjoint/cetacea/docs/book/code/ch01-mistakes.ctea:36: theorem `peek_at_the_goal` failed: current goal is `Q`
  note: target: Q
```

Whenever a proof stops making sense, drop in a `show_goal`, run the
checker, see exactly what's owed, then delete the line and continue.
It's the formal-proof equivalent of a print statement, and you should
use it *constantly* while learning.

## 1.9 Exercises

Open [`code/ch01-exercises.ctea`](code/ch01-exercises.ctea). Each
exercise is a stated theorem whose proof is the single tactic `sorry` —
a placeholder that closes any goal but brands the theorem as
unfinished. The file already checks:

```text
accepted theorem ex1_1 (constructive; incomplete: uses sorry)
...
```

Replace each `sorry` with a real proof; you're done when every
`incomplete: uses sorry` flag is gone. Only `intro`, `exact`, `split`,
`trivial`, `apply`, and the `.left`/`.right` projections are needed.

- **Exercise 1.1** `Q -> Q` — the warm-up. One `intro`, one `exact`.
- **Exercise 1.2** `P -> Q -> Q /\ P` — build the "and" in the
  opposite order from the assumptions.
- **Exercise 1.3** `P -> P /\ P` — one assumption, two slots. That's
  allowed.
- **Exercise 1.4** `(P /\ Q) /\ R -> P /\ (Q /\ R)` — regrouping.
  You'll need chained projections like `h.left.right`, and a `split`
  inside a `split`.
- **Exercise 1.5** `P /\ (Q /\ R) -> Q` — dig out the middle. One
  line after the `intro`.
- **Exercise 1.6** `P /\ (P -> Q) -> P /\ Q` — keep the `P`, and cash
  the voucher to get the `Q`. Compare `cash_the_check`.

Solutions are in [`code/ch01-solutions.ctea`](code/ch01-solutions.ctea)
— but the checker gives you something better than solutions: instant,
precise feedback. Get stuck, add `show_goal`, read the state, try
again.

---

*Next: [Chapter 2 — Natural Deduction](02-natural-deduction.md), where
the moves you've been making get names, the last two connectives get
their rules, and we watch the checker demolish two famous fallacies.*
