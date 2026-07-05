# Chapter 6 — Sets: Collections You Can Reason About

> **Files for this chapter:**
> [`code/ch06-examples.ctea`](code/ch06-examples.ctea) ·
> [`code/ch06-mistakes.ctea`](code/ch06-mistakes.ctea) (intended to fail) ·
> [`code/ch06-exercises.ctea`](code/ch06-exercises.ctea) ·
> [`code/ch06-solutions.ctea`](code/ch06-solutions.ctea)

## 6.1 The registrar's question

The registrar's office wants to know: *is every student in the CS-and-
Math overlap also in the CS-or-Math pool?* You can see it's true — you
can practically *see* the Venn diagram, the little lens of the overlap
sitting inside the big two-circle blob. A diagram, though, is a picture
of an argument, not the argument. When the sets have thirty operations
applied to them and the claim is buried in chapter 6 of somebody's
database migration plan, "you can practically see it" stops being
available.

Here's the plan for making such claims checkable, and it's almost
insultingly simple: **a set is the collection of things for which a
proposition holds, and everything you can ask about sets reduces to
membership.** `x in A` — "x is a member of A" — is a proposition like
any other, and every Venn-diagram region is a connective applied to
memberships: the overlap is *and*, the pool is *or*, the outside is
*not*. Which means the entire toolkit of Chapters 1 through 4 —
`split`, `cases`, `intro`, `left`, `right` — is already a set-theory
toolkit. This chapter is one long cashing-in of things you already own.

## 6.2 Building sets, and what membership computes to

In Cetacea, `Set T` is the type of sets whose elements come from `T` —
a `Set Student` holds students, a `Set Nat` holds numbers. Our campus
for the chapter:

```text
sort Student

const ana : Student
const ben : Student

pred TakesCS(Student)
pred TakesMath(Student)
```

Sets get built a handful of ways. The most fundamental is
**set-builder notation** — carve out everything satisfying a
predicate — which pairs beautifully with `def`, the declaration that
names a thing once so the whole file can use it:

```text
def CS : Set Student := { x : Student | TakesCS(x) }
def Math : Set Student := { x : Student | TakesMath(x) }
```

Read: *CS is the set of students x such that x takes CS.* Alongside
set-builders you have `empty(T)` and `univ(T)` (the empty set and the
everything-set), `singleton(x)`, finite listings like `{ana, ben}`,
and the four workhorse operations `union(A, B)`, `inter(A, B)`,
`diff(A, B)` (in A but not B), and `compl(A)` (everything not in A).

Now the key mechanic of the whole chapter: **membership computes.**
Asking whether `x` is in a set built from these constructors is not a
mystery; `simp` unfolds it into the proposition it secretly is:

| Membership | computes to |
|---|---|
| `x in { y : T \| P(y) }` | `P(x)` |
| `x in singleton(a)` | `x = a` |
| `x in union(A, B)` | `x in A \/ x in B` |
| `x in inter(A, B)` | `x in A /\ x in B` |
| `x in diff(A, B)` | `x in A /\ not (x in B)` |
| `x in compl(A)` | `not (x in A)` |
| `x in empty(T)` | `False` |
| `x in univ(T)` | `True` |

Every proof in this chapter is that table plus Chapter 2. Watch it
work three times:

```text
theorem ana_in_cs : TakesCS(ana) -> ana in CS := by
  intro h
  simp
  exact h
```

`simp` unfolds the definition `CS` and the set-builder, turning the
goal `ana in CS` into `TakesCS(ana)` — which is exactly `h`.

```text
theorem ben_in_singleton : ben in singleton(ben) := by
  simp
  refl
```

Membership in a singleton becomes an *equality* — and Chapter 5 takes
it from there.

```text
theorem ben_in_pair : ben in {ana, ben} := by
  simp
  right
  refl
```

Membership in a finite listing becomes a *disjunction* of equalities
(`ben = ana \/ ben = ben`), and Chapter 2's `right` picks the winnable
side. Three chapters, one line each. Told you this chapter was a
cashing-in.

## 6.3 Subset: a `forall` in a trench coat

`A subset B` means every member of `A` is a member of `B`. That
sentence *is* the definition — a universal quantifier wrapped around an
implication:

```text
A subset B    means    forall x, x in A -> x in B
```

Like `not` in Chapter 2, `subset` is another disguise worn by
something you already know. `simp` takes the coat off. Here's the
registrar's easier cousin — CS students are in the CS-or-Math pool:

```text
theorem cs_subset_union : CS subset union(CS, Math) := by
  simp
  intro x
  intro hx
  left
  exact hx
```

After `simp`, the goal is a plain Chapter 4 object:

```text
|-  forall x : Student, TakesCS(x) -> TakesCS(x) \/ TakesMath(x)
```

(`simp` unfolded everything in one sweep: the subset, the two set
names, the set-builders, and the union membership.) Then: arbitrary
student, assume the premise, commit to a side. This four-tactic
skeleton — `simp`, `intro x`, `intro hx`, *finish with Chapter 2
moves* — is the standard opening for every subset proof you will ever
write.

The standard library (`std/set.ctea`, in the prelude you're already
importing) has the common subset facts pre-proved — `subset_refl`,
`subset_trans`, `subset_union_left`, `inter_subset_left`, and a dozen
more — so the theorem above is also a one-liner, Chapter 4 style:

```text
theorem cs_subset_union_library : CS subset union(CS, Math) := by
  exact subset_union_left {T := Student; A := CS; B := Math}
```

## 6.4 Element chasing

Textbooks call the general method **element chasing**: to move an
element from one set expression to another, unfold what its membership
means and push the pieces through. The overlap question from Section
6.1, formally — and note it's the table's `inter` row plus a
projection:

```text
theorem overlap_takes_cs : inter(CS, Math) subset CS := by
  simp
  intro x
  intro hx
  exact hx.left
```

After `simp` and the intros, `hx : TakesCS(x) /\ TakesMath(x)` — the
intersection *became* a conjunction — and `.left` is the answer.

Chasing works on hypotheses too, with Chapter 5's `simp at`:

```text
theorem diff_excludes : forall x : Student, x in diff(CS, Math) -> not (x in Math) := by
  intro x
  intro h
  simp at h
  intro hm
  apply h.right
  simp at hm
  exact hm
```

Walk it slowly, because this proof chases in both directions. `simp at
h` turns the difference-membership into
`h : TakesCS(x) /\ (TakesMath(x) -> False)` — the table's `diff` row:
in CS, *and* Math leads to absurdity. The goal `not (x in Math)` is an
implication in disguise (Chapter 2 never stops paying), so `intro hm`
assumes `hm : x in Math`, leaving goal `False`. `apply h.right` swaps
that debt for `TakesMath(x)`; one more `simp at hm` converts the raw
membership `hm` into exactly that, and we're done. Every step is
mechanical; the only skill is keeping your nerve.

## 6.5 Chains of subsets, and `have` again

Subset is transitive — `subset_trans` in the library — and longer
chains are where Chapter 5's `have` starts feeling like an old friend.
Four sets, three hops:

```text
theorem three_hops
  (T : Type)
  (A B C D : Set T)
  : A subset B -> B subset C -> C subset D -> A subset D := by
  intro h1
  intro h2
  intro h3
  have hAC : A subset C
  apply subset_trans
  exact h1
  exact h2
  apply subset_trans
  exact hAC
  exact h3
```

*First establish A ⊆ C; then chain it with the last hop.* Note that
`apply subset_trans` finds the intermediate set by looking at which
hypotheses you feed it — you never have to say "the middle one is `B`"
out loud. (When the middle term appears in no hypothesis, inference
can fail and ask you for explicit braces; you saw the pattern in
Chapter 4.)

## 6.6 Set equality: the extensionality ritual

When are two sets *equal*? Sets have no order, no repetition, no
packaging — a set is nothing but its members. So:

> Two sets are equal when they have exactly the same members.

This principle is called **extensionality**, and here's something the
other chapters didn't have: it cannot be *proved* from what came
before. It's a genuinely new assumption about what sets are. Cetacea
is honest about this — `std/set.ctea` declares it as an **axiom**, a
statement accepted without proof:

```text
axiom set_ext
  (T : Type)
  (A B : Set T)
  : (forall x : T, x in A <-> x in B) -> A = B
```

You've been watching the checker report `(constructive)` after every
accepted theorem. Axioms add a third piece of bookkeeping: any theorem
whose proof touches one is labeled with it, forever, transitively.
Run the examples file and look:

```text
accepted theorem inter_union_dist (constructive; axioms: set_ext)
```

Nothing is hidden: this theorem is true *given* extensionality, and
the checker will never let you forget the "given." (Chapter 10 has
more to say about living with axioms.)

Now the method. `set_ext` says: to prove `A = B`, prove
`forall x, x in A <-> x in B`. That unlocks a four-line ritual —

```text
apply set_ext      -- equality becomes a forall of iffs
intro x            -- take an arbitrary element
simp               -- memberships compute (the table!)
split              -- the iff becomes two implications
```

— after which you element-chase both directions with Chapter 2 moves.
Here it is proving that intersection distributes over union, a
Venn-diagram classic:

```text
theorem inter_union_dist
  (T : Type)
  (A B C : Set T)
  : inter(A, union(B, C)) = union(inter(A, B), inter(A, C)) := by
  apply set_ext
  intro x
  simp
  split
  intro h
  cases h.right with
  | left hb =>
      left
      split
      exact h.left
      exact hb
  | right hc =>
      right
      split
      exact h.left
      exact hc
  intro h
  cases h with
  | left hab =>
      split
      exact hab.left
      left
      exact hab.right
  | right hac =>
      split
      exact hac.left
      right
      exact hac.right
```

Long, but look at what it's long *with*: after the ritual the goal is

```text
(x in A /\ (x in B \/ x in C) -> x in A /\ x in B \/ x in A /\ x in C)
  /\ (x in A /\ x in B \/ x in A /\ x in C -> x in A /\ (x in B \/ x in C))
```

— pure Chapter 2, not a set operation in sight. The forward direction
cases on "B or C" and rebuilds; the backward direction cases on which
intersection you're in. If your discrete math course made you write
two-column element-chasing proofs, this is that, with a referee.

De Morgan's laws work the same way. Here's the direction that's fully
constructive — "outside the union" equals "outside both":

```text
theorem compl_union_demo
  (T : Type)
  (A B : Set T)
  : compl(union(A, B)) = inter(compl(A), compl(B)) := by
  apply set_ext
  intro x
  simp
  ...            -- see the examples file for the chase
```

And its mirror image, `compl(inter(A, B)) = union(compl(A), compl(B))`?
Try the ritual and you'll hit a wall in one direction: knowing `x`
isn't in *both* sets doesn't tell you *which* set it's missing from —
that's exactly the constructive gap from Chapter 3, where the
propositional version, `not (P /\ Q) -> not P \/ not Q`, was the "hard
direction" of De Morgan and needed `by_cases`. The examples
file finishes the chapter with the fix: a `mode classical` line, a
`by_cases ha : x in A`, and an accepted line that wears the whole
story on its sleeve:

```text
accepted theorem compl_inter_demo (classical; axioms: set_ext)
```

One theorem, two disclosures: it leaned on excluded middle, and it
leaned on extensionality. This is what "the checker keeps you honest"
means in practice — compare `compl_union_demo`, whose accepted line
says `(constructive; axioms: set_ext)`, and you can read off *which De
Morgan law is deeper* from the bookkeeping alone.

## 6.7 The other road: mutual inclusion

One more way to prove sets equal, no `<->` involved: show
`A subset B` and `B subset A` separately, and let the library theorem
`subset_antisymm` (itself proved from `set_ext`) combine them:

```text
theorem inter_self (T : Type) (A : Set T) : inter(A, A) = A := by
  apply subset_antisymm
  simp
  intro x
  intro hx
  exact hx.left
  simp
  intro x
  intro hx
  split
  exact hx
  exact hx
```

Two little subset proofs back to back — first ⊆, then ⊇. Whether you
prefer this or the extensionality ritual is mostly taste; mutual
inclusion shines when the two directions need genuinely different
arguments, or when you already own one of them as a lemma.

## 6.8 Common mistakes

Run [`code/ch06-mistakes.ctea`](code/ch06-mistakes.ctea) — intended to
fail.

**Mistake 1: proving set equality by staring.** `union(A, B)` and
`union(B, A)` are equal sets, so `refl` should see it... no. `refl`
compares *expressions*, and these are different expressions:

```text
error: /home/left_adjoint/cetacea/docs/book/code/ch06-mistakes.ctea:21: theorem `sets_equal_by_staring` failed: refl cannot prove `union(A, B) = union(B, A)` because the sides are not identical
  note: target: union(A, B) = union(B, A)
```

(The `help:` block suggests trying `simp` first — fair advice
elsewhere, but no simplification makes these two syntactically
identical.) Equal-as-sets is a *theorem about members*, not a fact
about spelling, and members mean the Section 6.6 ritual. This mistake
has a moral: extensionality isn't bureaucratic ceremony, it's the
actual mathematical content of "sets are equal."

**Mistake 2: `intro` before the coat comes off.**

```text
error: /home/left_adjoint/cetacea/docs/book/code/ch06-mistakes.ctea:25: theorem `subset_too_fast` failed: intro expects an implication or universal goal
  note: target: A subset A
  help: Match the goal shape
    `intro` only opens implication or universal goals. The current target is `A subset A`.
```

`A subset A` *is* a `forall` — but it's wearing the trench coat, and
`intro` only opens goals that visibly start with `forall` or `->`. One
`simp` first and the same `intro` succeeds. If you remember one
debugging reflex from this chapter: **when a tactic refuses a set
goal, `simp` and try again.**

**Mistake 3: flipping a subset.** Subset is not symmetric, and here's
what it looks like to find that out mid-proof. The attempt assumes
`A subset B` and tries to derive `B subset A`; the chase goes fine
until the hypothesis is asked to run backwards:

```text
error: /home/left_adjoint/cetacea/docs/book/code/ch06-mistakes.ctea:35: theorem `subset_flip` failed: cannot use this proof here: its conclusion `x1 in B` does not match goal `x in A`
  note: target: x in A
```

The hypothesis concludes *in B*; the goal wants *in A*; `apply` won't
bridge them. Note what's missing, though: no "statement is not a
tautology" note. Chapter 2's countermodel detector only covers
propositional statements, and this one is quantified — so the checker
reports the local dead end and leaves the verdict to you. (The
statement is indeed false: take `A` empty and `B` not.) Rejection plus
your own counterexample is how a quantified case gets closed —
Chapter 4 said the same about the quantifier-swap.

**Mistake 4: an element is not a one-element set.**

```text
error: /home/left_adjoint/cetacea/docs/book/code/ch06-mistakes.ctea:39: theorem `element_confusion` has invalid statement
  note: subset expects set arguments, but got `Student` and `Set Student`
  note: target: ana subset CS
```

`ana subset CS` is malformed — subset relates sets to sets. What the
writer meant is either `ana in CS` (membership) or
`singleton(ana) subset CS` (the one-element set). The `in`-versus-
`subset` confusion is the classic set-theory pitfall — on paper it
slides by for weeks; here it's an *invalid statement*, caught before
any tactic runs, same as Chapter 5's `clark = 0`.

## 6.9 Exercises

Open [`code/ch06-exercises.ctea`](code/ch06-exercises.ctea) — the
campus is declared at the top. Clear the `sorry` flags.

- **Exercise 6.1** `TakesMath(ben) -> ben in Math` — membership in a
  named set.
- **Exercise 6.2** `ana in {ana, ben}` — a disjunction of equalities;
  commit to the right side (which is the left one).
- **Exercise 6.3** `inter(CS, Math) subset union(CS, Math)` — the
  registrar's question from Section 6.1, at last. Element-chase: the
  conjunction comes in, a disjunction goes out.
- **Exercise 6.4** `diff(CS, Math) subset CS` — the difference stays
  inside the left set.
- **Exercise 6.5** `union(A, B) subset C -> A subset C` — feed the
  hypothesis an element it accepts: after the intros, `apply h` turns
  the goal `x in C` into a goal about the union.
- **Exercise 6.6** `union(A, A) = A` — first equality of your own:
  the four-line ritual, then both directions.
- **Exercise 6.7** `diff(A, empty(T)) = A` — taking away nothing
  changes nothing. In one direction you'll owe `x in empty(T) ->
  False`; remember what membership in `empty` computes to, and what
  Chapter 2 does with a `False` hypothesis.
- **Exercise 6.8 (challenge)** `compl(compl(A)) = A` — double
  complement. One inclusion is constructive; the other is
  double-negation elimination wearing a set costume, and the file
  grants `mode classical` for it. Expect your accepted line to read
  `(classical; axioms: set_ext)` — and now you know exactly why.

Solutions: [`code/ch06-solutions.ctea`](code/ch06-solutions.ctea).

---

*Next: [Chapter 7 — Relations](07-relations.md). Sets collect
individuals; relations connect pairs of them. We'll meet the three
questions to ask of any relation — and the chapter ends with a genuine
piece of number theory: clock arithmetic certified as an equivalence
relation.*
