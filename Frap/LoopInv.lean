import Frap.Hoare2

namespace Imp
namespace Hoare
open AExp
open BExp
open Com
open CEval
open DCom
open Decorated
attribute [local simp]
  aeval beval aequiv bequiv cequiv update x y z

/-
## Finding loop invariants

Once the outermost precondition and postcondition are chosen, the only creative part of a verifying program using Hoare logic is finding the right loop invariants.
The reason this is difficult is the same as the reason that inductive mathematical proofs are:
* Strengthening a loop invariant means that you have a stronger assumption to work with when trying to establish the postcondition of the loop body, but it also means that the loop body's postcondition is stronger and thus harder to prove.
* Similarly, strengthening an induction hypothesis means that you have a stronger assumption to work with when trying to complete the induction step of the proof, but it also means that the statement being proved inductively is stronger and thus harder to prove.

This lecture explains how to approach the challenge of finding loop invariants through a series of examples and exercises.

### Example: slow subtraction

The following program subtracts the value of `x` from the value of `y` by repeatedly decrementing both `x` and `y`.
We want to verify its correctness with respect to the pre- and postconditions shown:
```
  { x = m ∧ y = n }
    while x != 0 do
      y := y - 1;
      x := x - 1
    end
  { y = n - m }
```

To verify this program, we need to find an invariant `Inv` for the loop.
As a first step we can leave `Inv` as an unknown and build a skeleton for the proof by applying the rules for local consistency, working from the end of the program to the beginning, as usual, and without any thinking at all yet.

This leads to the following skeleton:
```
  (1) { x = m ∧ y = n } ->>                                (a)
  (2) { Inv }
        while x != 0 do
  (3)                     { Inv ∧ x ≠ 0 } ->>              (b)
  (4)                     { Inv[x ↦ x - 1][y ↦ y - 1] }
          y := y - 1;
  (5)                     { Inv[x ↦ x - 1] }
          x := x - 1
  (6)                     { Inv }
        end
  (7) { Inv ∧ ¬(x ≠ 0) } ->>                               (c)
  (8) { y = n - m }
```

By examining this skeleton, we can see that any valid `Inv` will have to respect three conditions:
* (a) it must be weak enough to be implied by the loop's precondition, i.e., (1) must imply (2);
* (b) it must be preserved by a single iteration of the loop, assuming that the loop guard also evaluates to true, i.e., (3) must imply (4);
* (c) it must be strong enough to imply the program's postcondition, i.e., (7) must imply (8).

These conditions are actually independent of the particular program and specification we are considering: every loop invariant has to satisfy them.

One way to find a loop invariant that simultaneously satisfies these three conditions is by using an iterative process: start with a "candidate" invariant (e.g., a guess or a heuristic choice) and check the three conditions above; if any of the checks fails, try to use the information that we get from the failure to produce another -- hopefully better -- candidate invariant, and repeat.

For instance, in the reduce-to-zero example from last lecture, we saw that, for a very simple loop, choosing `True` as a loop invariant did the job.
Maybe it will work here too.
To find out, let's try instantiating `Inv` with `True` in the skeleton above and see what we get...
```
  (1) { x = m ∧ y = n } ->>                                (a: OK)
  (2) { True }
        while x != 0 do
  (3)                     { True ∧ x ≠ 0 } ->>             (b: OK)
  (4)                     { True }
          y := y - 1;
  (5)                     { True }
          x := x - 1
  (6)                     { True }
        end
  (7) { True ∧ ¬(x ≠ 0) } ->>                              (c: No!)
  (8) { y = n - m }
```

If we want (c) to hold, we need to strengthen the loop invariant so that it implies the postcondition (8).
One simple way to do this is to let the loop invariant be the postcondition.
So let's return to our skeleton, instantiate Inv with `y = n - m`, and try checking conditions (a) to (c) again.
```
  (1) { x = m ∧ y = n } ->>                                (a: No!)
  (2) { y = n - m }
        while x != 0 do
  (3)                     { y = n - m ∧ x ≠ 0 } ->>        (b: No!)
  (4)                     { y - 1 = n - m }
          y := y - 1;
  (5)                     { y = n - m }
          x := x - 1
  (6)                     { y = n - m }
        end
  (7) { y = n - m ∧ ¬(x ≠ 0) } ->>                         (c: OK)
  (8) { y = n - m }
```

This failure is not very surprising: the variable `y` changes during the loop, while `m` and `n` are constant, so the assertion we chose didn't have much chance of being a loop invariant!

To do better, we need to generalize (7) to some statement that is equivalent to (8) when `x` is `0`, since this will be the case when the loop terminates, and that "fills the gap" in some appropriate way when `x` is nonzero.
Looking at how the loop works, we can observe that `x` and `y` are decremented together until `x` reaches `0`.
So, if `x = 2` and `y = 5` initially, after one iteration of the loop we obtain `x = 1` and `y = 4`; after two iterations `x = 0` and `y = 3`; and then the loop stops.
Notice that the difference between `y` and `x` stays constant between iterations: initially, `y = n` and `x = m`, and the difference is always `n - m`.
So let's try instantiating `Inv` in the skeleton above with `y - x = n - m`.
```
  (1) { x = m ∧ y = n } ->>                                (a: OK)
  (2) { y - x = n - m }
        while x != 0 do
  (3)                     { y - x = n - m ∧ x ≠ 0 } ->>    (b: OK)
  (4)                     { (y - 1) - (x - 1) = n - m }
          y := y - 1;
  (5)                     { y - (x - 1) = n - m }
          x := x - 1
  (6)                     { y - x = n - m }
        end
  (7) { y - x = n - m ∧ ¬(x ≠ 0) } ->>                     (c: OK)
  (8) { y = n - m }
```

Success!
Conditions (a), (b) and (c) all hold now.
(To verify (b), we need to check that, under the assumption that `x ≠ 0`, we have `y - x = (y - 1) - (x - 1)`; this holds for all natural numbers `x` and `y`.)

Here is the final version of the decorated program:
-/

def subtract_slowly_dec (m n : Nat) : Decorated := decorated
  (fun st => st x = m ∧ st y = n) $
    dc_pre (fun st => st y - st x = n - m) $
    dc_while <{x != 0}>
        (fun st => st y - st x = n - m ∧ st x ≠ 0)
        (dc_pre (fun st => (st y - 1) - (st x - 1) = n - m) $
      dc_seq
      (dc_asgn y <{y - 1}>
        (fun st => st y - (st x - 1) = n - m))
      (dc_asgn x <{x - 1}>
        (fun st => st y - st x = n - m))
    )
  (fun st => st y = n - m)

theorem subtract_slowly_outer_triple_valid m n
    : outer_triple_valid (subtract_slowly_dec m n) := by
  unfold subtract_slowly_dec
  verify

/-
### Exercise: slow assignment
exercise (2-star)

A roundabout way of assigning a number currently stored in `x` to the variable `y` is to start `y` at `0`, then decrement `x` until it hits `0`, incrementing `y` at each step.
Here is a program that implements this idea.
Fill in decorations and prove the decorated program correct.
(The proof should be very simple.)

```
  { x = m } ->>
  { **FILL IN HERE** }
    y := 0;
                      { **FILL IN HERE** }
    while x != 0 do
                      { **FILL IN HERE** } ->>
                      { **FILL IN HERE** }
      x := x - 1
                      { **FILL IN HERE** }
      y := y + 1
                      { **FILL IN HERE** }
    end
  { **FILL IN HERE** } ->>
  { y = m }
```
-/

def slow_assignment_dec (m : Nat) : Decorated := decorated
  (fun st => st x = m) $
    dc_pre (fun st => /-**FILL IN HERE**-/ True) $
    dc_seq
    (dc_asgn y <{0}>
        (fun st => /-**FILL IN HERE**-/ True)) $
    dc_post (dc_while <{x != 0}>
        (fun st => /-**FILL IN HERE**-/ True)
        (dc_pre (fun st => /-**FILL IN HERE**-/ True) $
        dc_seq
        (dc_asgn x <{x - 1}>
          (fun st => /-**FILL IN HERE**-/ True))
        (dc_asgn y <{y + 1}>
          (fun st => /-**FILL IN HERE**-/ True))
    )
  (fun st => /-**FILL IN HERE**-/ True))
  (fun st => st y = m)

theorem slow_assignment m
    : outer_triple_valid (slow_assignment_dec m) := by
  sorry

/-
### Example: parity

Here's a way of computing the parity of a value initially stored in `x`.
```
  { x = m }
    while 2 <= x do
      x := x - 2
    end
  { x = parity m }
```
The `parity` function used in the specification is defined in Lean as follows:
-/

open Nat

def parity x :=
  match x with
  | 0 => 0
  | 1 => 1
  | succ (succ x') => parity x'

/-
The postcondition does not hold at the beginning of the loop, since `m = parity m` does not hold for an arbitrary `m`, so we cannot hope to use that as a loop invariant.
To find a loop invariant that works, let's think a bit about what this loop does.
On each iteration it decrements `x` by `2`, which preserves the parity of `x`.
So the parity of `x` does not change, i.e., it is invariant.
The initial value of `x` is `m`, so the parity of `x` is always equal to the parity of `m`.
Using `parity x = parity m` as an invariant we obtain the following decorated program:
```
  { x = m } ->>                                            (a: OK)
  { parity x = parity m }
    while 2 <= x do
                    { parity x = parity m ∧ 2 ≤ x } ->>    (b: OK)
                    { parity (x - 2) = parity m }
      x := x - 2
                    { parity x = parity m }
    end
  { parity x = parity m ∧ ¬(2 ≤ x) } ->>                   (c: OK)
  { x = parity m }
```

With this loop invariant, conditions (a), (b), and (c) are all satisfied.
For verifying (c), we observe that, when `x < 2`, we have `parity x = x` (we can easily see this in the definition of parity).
For verifying (b), we observe that, when `2 ≤ x`, we have `parity x = parity (x-2)`.
-/

/-
exercise (3-star)
Translate the above informal decorated program into a formal one and prove it correct.
-/

def parity_dec (m : Nat) : Decorated := decorated
  (fun st => st x = m) $
  sorry

/-
You may find the following lemmas helpful.
-/

theorem parity_ge_2 x : 2 ≤ x → parity (x - 2) = parity x := by
  intro h
  cases x <;> simp [*] at *
  rename_i x
  cases x <;> simp [*, parity] at *

theorem parity_lt_2 x : ¬(2 ≤ x) → parity x = x := by
  intro
  cases x <;> simp [*, parity] at *
  rename_i x
  cases x <;> simp [*, parity] at *

theorem parity_outer_triple_valid m
    : outer_triple_valid (parity_dec m) := by
  sorry

/-
### Example: squaring

Here's a program that squares `x` by repeated addition:
```
  { x = m }
    y := 0;
    z := 0;
    while y != x do
      z := z + x;
      y := y + 1
    end
  { z = m * m }
```

The first thing to note is that the loop reads `x` but doesn't change its value.
In such cases, it can be a good idea to add `x = m` to the loop invariant.
If we look at how `z` progresses in the loop, `z = m` after the 1st iteration, `z = 2*m` after the 2nd iteration, and `z = m*m` at the end.
Since `y` tracks how many times we go through the loop, this leads us to derive a loop invariant candidate: `z = y * m ∧ x = m`, which makes the proof go through.
```
  { x = m } ->>
  { 0 = 0 * m ∧ x = m }
    y := 0;
                      { 0 = y * m ∧ x = m }
    z := 0;
                      { z = y * m ∧ x = m }
    while y != x do
                      { z = y * m ∧ x = m ∧ y ≠ x } ->>
                      { z + x = (y + 1) * m ∧ x = m }
      z := z + x;
                      { z = (y + 1) * m ∧ x = m }
      y := y + 1
                      { z = y * m ∧ x = m }
    end
  { z = y * m ∧ x = m ∧ ¬(y ≠ x) } ->>
  { z = m * m }
```
-/

/-
## Weakest preconditions

Some preconditions are more interesting than others.
For example, the Hoare triple
  `{ False } x := y + 1 { x ≤ 5 }`
is _not_ very interesting: although it is perfectly valid, it tells us nothing useful.
Since the precondition isn't satisfied by any state, it doesn't describe any situations where we can use the command `x := y + 1` to achieve the postcondition `x ≤ 5`.

By contrast,
  `{ y ≤ 4 ∧ z = 0 } x := y + 1 { x ≤ 5 }`
has a useful precondition: it tells us that, if we can somehow create a situation in which we know that `y ≤ 4 ∧ z = 0`, then running this command will produce a state satisfying the postcondition.
However, this precondition is not as useful as it could be, because the `z = 0` clause in the precondition actually has nothing to do with the postcondition `x ≤ 5`.

The _most_ useful precondition for this command is this one:
  `{ y ≤ 4 } x := y + 1 { x ≤ 5 }`
The assertion `y ≤ 4` is called the _weakest precondition_ of `x := y + 1` with respect to the postcondition `x ≤ 5`.

Think of _weakest_ here as meaning "easiest to satisfy": a weakest precondition is one that as many states as possible can satisfy.

`P` is a weakest precondition of command `c` for postcondition `Q` if
* `P` is a precondition, i.e., `{P} c {Q}`; and
* `P` is at least as weak as all other preconditions, i.e., if `{P'} c {Q}`, then `P' ->> P`.

Note that weakest preconditions need not be unique.
For example, `y ≤ 4` was a weakest precondition above, but so are the logically equivalent assertions `y < 5`, `y ≤ 2*2`, etc.
-/

def is_wp P c Q := ({* P *} c {* Q *}) ∧ ∀P', ({* P' *} c {* Q *}) → (P' ->> P)

/-
exercise (1-star)
What are weakest preconditions of the following commands for the following postconditions?

`{ ? } skip { x = 5 }`

`{ ? } x := y + z { x = 5 }`

`{ ? } x := y { x = y }`

`{ ? } if x = 0 then y := z + 1 else y := w + 2 end { y = 5 }`

`{ ? } x := 5 { x = 0 }`

`{ ? } while true do x := 0 end { x = 0 }`
-/

theorem is_wp_example
    : is_wp (fun st => st y ≤ 4) <{x := y + 1}> (fun st => st x ≤ 5) := by
  unfold is_wp; constructor
  . apply hoare_consequence_pre
    . apply hoare_asgn
    . verify_assertion
  . intro P' h st hP'
    unfold valid_hoare_triple at *
    have hst' : (st[x ↦ st y + 1]) x ≤ 5 := by
      apply h
      . assumption
      . constructor; simp
    simp at *; assumption

/-
# Hoare logic as a logic

The presentation of Hoare logic we've seen so far could be described as "model-theoretic": the proof rules for each of the constructors were presented as _theorems_ about the evaluation behavior of programs, and proofs of program correctness (validity of Hoare triples) were constructed by combining these theorems directly in Lean.

Another way of presenting Hoare logic is to define a completely separate proof system—a set of axioms and inference rules that talk about commands, Hoare triples, etc.—and then say that a proof of a Hoare triple is a valid derivation in _that_ logic.
We can do this by giving an inductive definition of _valid derivations_ in this new logic.

## Hoare logic and model theory

Recall the definition of valid Hoare triple:
`∀ (st st' : State), P st → CEval c st st' → Q st'`
-/

#print valid_hoare_triple

/-
This notion of _validity_ is based on the underlying model of how Imp programs execute.
That model itself is based on states.

So far, we have punned between the syntax of a Hoare triple, written `{P} c {Q}`, and its validity, as expressed by `valid_hoare_triple`.
In essence, we have said that the semantic meaning of that syntax is the proposition returned by `valid_hoare_triple`.
This way of giving semantic meaning to something syntactic is part of the branch of mathematical logic known as _model theory_.

Our approach to Hoare logic through model theory led us to state proof rules in terms of that same state-based model, and to prove program correctness in it, too.
But there is another approach, which is arguably more common in Hoare logic.
We turn to it, next.

## Hoare logic and proof theory

Instead of using states and evaluation as the basis for reasoning, let's take the proof rules as the basis.
These proof rules give us a set of axioms and inference rules that constitute a logic in their own right.
The Hoare triples in these proof rules has no other meaning than what the rules give them.
Forget about states and evaluations.
They are just syntax that the rules tell us how to manipulate in legal ways.

Through this new lens, a valid Hoare triple, such as `{ x = 0 } x := x + 1 { x = 1 }`, is _derivable_ by writing a proof tree using the proof rules.
On the other hand, an invalid Hoare triple, such as `{ x = 0 } skip { x = 1 }` is _not_ derivable, because there is no way to apply the rules to construct a proof tree with this triple at its root.

This approach gives meaning to triples not in terms of a model, but in terms of how they can be used to construct proof trees.
It's a different way of giving semantic meaning to something syntactic, and it's part of the branch of mathematical logic known as _proof theory_.

Our goal for the rest of this lecture is to formalize Hoare logic using proof theory, and then to prove that the model-theoretic and proof-theoretic formalizations are consistent with one another.

## Derivability

To formalize derivability of Hoare triples, we introduce inductive type `Derivable`, which describes legal proof trees using the Hoare rules.
-/

inductive Derivable : Assertion → Com → Assertion → Prop :=
  | h_skip P : Derivable P c_skip P
  | h_asgn Q x a : Derivable (fun st => Q (st[x ↦ aeval st a])) (c_asgn x a) Q
  | h_seq P c Q d R :
      Derivable Q d R → Derivable P c Q → Derivable P (c_seq c d) R
  | h_if P Q b c₁ c₂ :
      Derivable (fun st => P st ∧ beval st b) c₁ Q
      → Derivable (fun st => P st ∧ ¬(beval st b)) c₂ Q
      → Derivable P (c_if b c₁ c₂) Q
  | h_while P b c :
      Derivable (fun st => P st ∧ beval st b) c P
      → Derivable P (c_while b c) (fun st => P st ∧ ¬(beval st b))
  | h_consequence P Q P' Q' c :
      Derivable P' c Q'
      → (P ->> P')
      → (Q' ->> Q)
      → Derivable P c Q

open Derivable

/-
We don't need to include axioms corresponding to `hoare_consequence_pre` or `hoare_consequence_post`, because these can be proven easily from `h_consequence`.
-/

theorem h_consequence_pre P Q P' c
    : (Derivable P' c Q) → (P ->> P') → (Derivable P c Q) := by
  intro h hpre
  apply h_consequence <;> try assumption
  intro st hQ; assumption

theorem h_consequence_post P Q Q' c
    : Derivable P c Q' → (Q' ->> Q) → Derivable P c Q := by
  intro h hpre
  apply h_consequence <;> try assumption
  intro st hP; assumption

/-
As an example, let's construct a proof tree for
```
  { (x = 3)[x ↦ x+2][x ↦ x+1] }
    x := x + 1;
    x := x + 2
  { x = 3 }
```
-/

example :
    Derivable
      (fun st => (st x + 2) + 1 = 3)
        <{ x := x + 1; x := x + 2 }>
      (fun st => st x = 3) := by
  apply h_seq
  . apply h_asgn
  . apply h_consequence_pre
    . apply h_asgn
    . verify_assertion

/-
## Soundness and completeness

We now have two approaches to formulating Hoare logic:
* The model-theoretic approach uses `valid_hoare_triple` to characterize when a Hoare triple holds in a model, which is based on states.
* The proof-theoretic approach uses `Derivable` to characterize when a Hoare triple is derivable as the end of a proof tree.

Do these two approaches agree?
That is, are the valid Hoare triples exactly the derivable ones?
This is a standard question investigated in mathematical logic.
There are two pieces to answering it:
* A logic is _sound_ if everything that is derivable is valid.
* A logic is _complete_ if everything that is valid is derivable.

We can prove that Hoare logic is sound and complete.
-/

theorem hoare_sound P c Q : Derivable P c Q → valid_hoare_triple P c Q := by
  unfold valid_hoare_triple
  intro h
  induction h with
  | h_skip => apply hoare_skip
  | h_asgn => apply hoare_asgn
  | h_seq =>
    rename_i ih₁ ih₂
    apply hoare_seq
    . apply ih₁
    . apply ih₂
  | h_if =>
    rename_i ih₁ ih₂
    apply hoare_if
    . apply ih₁
    . apply ih₂
  | h_while =>
    rename_i ih
    apply hoare_while
    apply ih
  | h_consequence =>
    rename_i ih
    apply hoare_consequence
    . apply ih
    . assumption
    . assumption


/-
The proof of completeness is more challenging.
To carry out the proof, we need to invent some intermediate assertions using a technical device known as _weakest preconditions_.
Given a command `c` and a desired postcondition assertion `Q`, the weakest precondition `wp c Q` is an assertion `P` such that `{P} c {Q}` holds, and moreover, for any other assertion `P'`, if `{P'} c {Q}` holds then `P' ->> P`.

Another way of stating that idea is that `wp c Q` is the following assertion:
-/

def wp (c : Com) (Q : Assertion) : Assertion :=
  fun s => ∀ s', (s =[<[c]>]=> s') → Q s'

/-
The following two theorems show that the two ways of thinking about `wp` are the same.
-/

theorem wp_is_precondition c Q : {* wp c Q *} c {* Q *} := by
  unfold wp
  intro st st' hpre heval
  apply hpre; assumption

theorem wp_is_weakest c Q P' : {* P' *} c {* Q *} → (P' ->> wp c Q) := by
  intro ht st hP' st' heval
  apply ht <;> assumption

/-
Weakest preconditions are useful because they enable us to identify assertions that otherwise would require clever thinking.
The next two lemmas show that in action.
-/

/-
exercise (1-star)
What if we have a sequence `c₁; c₂`, but not an intermediate assertion for what should hold in between `c₁` and `c₂`?
No problem.
Prove that `wp c₂ Q` suffices as such an assertion.
-/

theorem wp_seq P Q c₁ c₂
    : Derivable P c₁ (wp c₂ Q) → Derivable (wp c₂ Q) c₂ Q
      → Derivable P (c_seq c₁ c₂) Q := by
  sorry

/-
exercise (2-star)
What if we have a `while` loop, but not an invariant for it?
No problem.
Prove that for any `Q`, assertion `wp (while b do c end) Q` is a loop invariant of `while b do c end`.
-/

theorem wp_invariant b c Q : valid_hoare_triple
    (fun st => wp (c_while b c) Q st ∧ beval st b) c (wp (c_while b c) Q) := by
  sorry

/-
Now we are ready to prove the completeness of Hoare logic.
For the `while` case, we'll use the invariant suggested by `wp_invariant`.
-/

theorem hoare_complete P c Q : valid_hoare_triple P c Q → Derivable P c Q := by
  unfold valid_hoare_triple
  intro ht
  induction c generalizing P Q with
  | c_skip =>
    apply h_consequence_pre
    . constructor
    . intro st hP
      apply ht
      . assumption
      . apply e_skip
  | c_asgn x a =>
    apply h_consequence_pre
    . constructor
    . intro st hP
      apply ht
      . assumption
      . apply e_asgn; rfl
  | c_seq c₁ c₂ ih₁ ih₂ =>
    apply wp_seq
    . apply ih₁
      unfold wp
      intro st st' hP he₁ st'' he₂
      apply ht <;> try assumption
      apply e_seq <;> assumption
    . apply ih₂
      apply wp_is_precondition
  | c_if b c₁ c₂ ih₁ ih₂ =>
    apply h_if
    . apply ih₁
      intro st st' hpre he1
      obtain ⟨⟩ := hpre
      apply ht
      . assumption
      . apply e_ifTrue
        . assumption
        . exact he1
    . apply ih₂
      intro st st' hpre he2
      obtain ⟨⟩ := hpre
      apply ht
      . assumption
      . apply e_ifFalse
        . simp [*] at *
        . exact he2
  | c_while b c ih =>
    apply h_consequence P Q _ (fun st => wp (c_while b c) Q st ∧ ¬(beval st b))
    . apply h_while
      apply ih
      apply wp_invariant
    . intro st hP st'
      apply ht
      exact hP
    . intro st; simp
      intro hinvpost hbfalse
      apply wp_is_precondition
      . exact hinvpost
      . apply e_whileFalse
        exact hbfalse

/-
## Decidability

We might hope that Hoare logic would be _decidable_; that is, that there would be an (terminating) algorithm (a _decision procedure_) that can determine whether or not a given Hoare triple is valid or derivable.
Sadly, such a decision procedure cannot exist.

Consider the triple `{True} c {False}`.
This triple is valid if and only if `c` is non-terminating.
So any algorithm that could determine validity of arbitrary triples could solve the Halting Problem.

Similarly, the triple `{True} skip {P}` is valid if and only if `∀ s, P s` is valid, where `P` is an arbitrary assertion of Lean's logic.
But this logic is far too powerful to be decidable.
-/

/-
## references
* [Software Foundations, Volume 2 Programming Language Foundations: Hoare Logic, Part 2](https://softwarefoundations.cis.upenn.edu/plf-current/Hoare2.html)
* [Software Foundations, Volume 2 Programming Language Foundations: Hoare Logic as a Logic](https://softwarefoundations.cis.upenn.edu/plf-current/HoareAsLogic.html)
-/
