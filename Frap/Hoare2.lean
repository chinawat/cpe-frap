import Frap.Hoare

namespace Imp
namespace Hoare
open AExp
open BExp
open Com
open CEval
attribute [local simp]
  aeval beval aequiv bequiv cequiv update x y z

/-
## Decorated programs

The beauty of Hoare Logic is that it is _structure_guided_: the structure of the proofs exactly follows the structure of programs.

We can record the essential ideas of a Hoare-logic proof — omitting low-level calculational detaials — by "decorating" a program with appropriate assertions on each of its commands.

Such a _decorated program_ carries within itself an argument for its own correctness.

For exampl,e consider the program:
```
  x := m;
  z := p;
  while x != 0 do
    z := z - 1;
    x := x - 1;
  end
```
Here is one possible specification for this program, in the form of a Hoare triple:
```
  { True }
    x := m;
    z := p;
    while x != 0 do
      z := z - 1;
      x := x - 1;
    end
  { z = p - m }
```
(Note the _parameter_ `m` and `p`, which stand for fixed-but-arbitrary numbers.)

Here is a decorated version of this program, embodying a proof of this specification:
```
  { True } ->>
  { m = m }
    x := m;
                      { x = m } ->>
                      { x = m ∧ p = p }
    z := p;
                      { x = m ∧ z = p } ->>
                      { z - x = p - m }
    while x != 0 do
                      { z - x = p - m ∧ x ≠ 0 } ->>
                      { (z-1) - (x-1) = p - m }
      z := z - 1;
                      { z - (x-1) = p - m }
      x := x - 1;
                      { z - x = p - m }
    end
  { z - x = p - m ∧ ¬(x ≠ 0) } ->>
  { z = p - m }
```

Concretely, a decorated program consists of the program's text interleaved with assertions (sometimes multiple assertions separated by implications).

A decorated program can be viewed as a compact representation of a proof in Hoare Logic: the assertions surrounding each command specify the Hoare triple to be proved for that part of the program using one of the Hoare Logic rules, and the structure of the program itself shows how to assemble all these individual steps into a proof for the whole program.

Our goal is to verify such decorated programs "mostly automatically."
But, before we can verify anything, we need to be able to _find_ a proof for a given specification, and for this we need to discover the right assertions.
This can be done in an almost mechanical way, with the exception of finding loop invariants.
In the remainder of this section, we explain in detail how to construct decorations for several short programs, all of which are loop-free or have simple loop invariants.
We'll return to finding more interesting loop invariants later in the chapter.

### Example: swapping

Consider the following program, which swaps the values of two variables using addition and subtraction (instead of by assigning to a temporary variable).
```
  x := x + y;
  y := x - y;
  x := x - y
```
We can give a proof, in the form of decorations, that this program is correct, i.e., it really swaps `x` and `y`, as follows.
```
  (1) { x = m ∧ y = n } ->>
  (2) { (x + y) - ((x + y) - y) = n ∧ (x + y) - y = m }
        x := x + y;
  (3)                 { x - (x - y) = n ∧ x - y = m }
        y := x - y;
  (4)                 { x - y = n ∧ y = m }
        x := x - y
  (5) { x = n ∧ y = m }
```
The decorations can be constructed as follows:
* We begin with the undecorated program (the unnumbered lines).
* We add the specification, i.e., the outer precondition (1) and postcondition (5).
  In the precondition, we use parameters `m` and `n` to remember the initial values of variables `x` and `y` so that we can refer to them in the postcondition (5).
* We work backwards, mechanically, starting from (5) and proceeding until we get to (2).
  At each step, we obtain the precondition of the assignment from its postcondition by substituting the assigned variable with the right-hand-side of the assignment.
  For instance, we obtain (4) by substituting `x` with `x - y` in (5), and we obtain (3) by substituting `y` with `x - y` in (4).

Finally, we verify that (1) logically implies (2), i.e., that the step from (1) to (2) is a valid use of the law of consequence, by doing a bit of high-school algebra.

### Example: simple conditionals

Here is a simple decorated program using conditionals:
```
  (1) { True }
        if x <= y then
  (2)                   { True ∧ x ≤ y } ->>
  (3)                   { (y - x) + x = y ∨ (y - x) + y = x }
          z := y - x
  (4)                   { z + x = y ∨ z + y = x }
        else
  (5)                   { True ∧ ¬(x ≤ y) } ->>
  (6)                   { (x - y) + x = y ∨ (x - y) + y = x }
          z := x - y
  (7)                   { z + x = y ∨ z + y = x }
        end
  (8) { z + x = y ∨ z + y = x }
```
These decorations can be constructed as follows:
* We start with the outer precondition (1) and postcondition (8).
* Following the format dictated by the `hoare_if` rule, we copy the postcondition (8) to (4) and (7).
  We conjoin the precondition (1) with the guard of the conditional to obtain (2).
  We conjoin (1) with the negated guard of the conditional to obtain (5).
* In order to use the assignment rule and obtain (3), we substitute `z` by `y - x` in (4).
  To obtain (6) we substitute `z` by `x - y` in (7).
* Finally, we verify that (2) implies (3) and (5) implies (6).
  Both of these implications crucially depend on the ordering of `x` and `y` obtained from the guard.
  For instance, knowing that `x ≤ y` ensures that subtracting `x` from `y` and then adding back `x` produces `y`, as required by the first disjunct of (3).
  Similarly, knowing that `¬(x ≤ y)` ensures that subtracting `y` from `x` and then adding back `y` produces `x`, as needed by the second disjunct of (6).
  Note that `n - m + m = n` does not hold for arbitrary natural numbers `n` and `m` (for example, `3 - 5 + 5 = 5`).

### Example: reduce to zero

Here is a `while` loop that is so simple that `True` suffices as a loop invariant.
```
  (1) { True }
        while x != 0 do
  (2)                     { True ∧ x ≠ 0 } ->>
  (3)                     { True }
          x := x - 1
  (4)                     { True }
        end
  (5) { True ∧ ¬(x ≠ 0) } -->
  (6) { x = 0 }
```
The decorations can be constructed as follows:
* Start with the outer precondition (1) and postcondition (6).
* Following the format dictated by the `hoare_while` rule, we copy (1) to (4).
  We conjoin (1) with the guard to obtain (2).
  We also conjoin (1) with the negation of the guard to obtain (5).
* Because the final postcondition (6) does not syntactically match (5), we add an implication between them.
* Using the assignment rule with assertion (4), we trivially substitute and obtain assertion (3).
* We add the implication between (2) and (3).
Finally we check that the implications do hold; both are trivial.

### From decorated programs to formal proofs

From an informal proof in the form of a decorated program, it is "easy in principle" to read off a formal proof using the Coq theorems corresponding to the Hoare Logic rules, but these proofs can be a bit long and fiddly.

Note that we do _not_ unfold the definition of `valid_hoare_triple` anywhere in this proof: the point of the game we're playing now is to use the Hoare rules as a self-contained logic for reasoning about programs.

For example...
-/

def reduce_to_zero : Com :=
  <{
    while x != 0 do
      x := x - 1
    end
  }>

theorem reduce_to_zero_correct' :
    {* fun _ => True *}
      reduce_to_zero
    {* fun st => st x = 0 *} := by
  -- first we need to transform the postconddition so that `hoare_while` will apply
  apply hoare_consequence_post
  . apply hoare_while
    -- loop body preservers loop invariant
    -- massage precondition so `hoare_asgn` applies
    apply hoare_consequence_pre
    . apply hoare_asgn
    . -- proving trivial implication (2) ->> (3)
      intro st _; simp
  . -- loop invariant and negated guard body imply postcondition
    simp; intro st _
    assumption

/-
To automate proofs involving assertions, the following declaration introduces a tactic that will help with proving assertions throughout the rest of this chapter.
You don't need to understand the details.
What's left after `verify_assertion` does its thing should be just the "interesting parts" of the proof, which, if we're lucky, might be nothing at all!
-/

macro "verify_assertion" : tactic =>
  `(tactic|
    (repeat' apply And.intro) <;>
    intro _ <;>
    intros <;>
    (try simp at *) <;>
    (repeat' apply And.intro <;> repeat' split) <;>
    (try simp [*] at *) <;>
    (try omega)
  )

/-
This makes it pretty easy to verify `reduce_to_zero`:
-/

theorem reduce_to_zero_correct''' :
    {* fun _ => True *}
      reduce_to_zero
    {* fun st => st x = 0 *} := by
  apply hoare_consequence_post
  . apply hoare_while
    apply hoare_consequence_pre
    . apply hoare_asgn
    . verify_assertion
  . verify_assertion

/-
This example shows that it is conceptually straightforward to read off the main elements of a formal proof from a decorated program.
Indeed, the process is so straightforward that it can be automated, as we will see next.

## Formal decorated programs

Our informal conventions for decorated programs amount to a way of "displaying" Hoare triples, in which commands are annotated with enough embedded assertions that checking the validity of a triple is reduced to simple logical and algebraic calculations showing that some assertions imply others.

In this section, we show that this presentation style can be made completely formal, and indeed that checking the validity of decorated programs can be largely automated.

### Syntax

The first thing we need to do is to formalize a variant of the syntax of Imp commands that includes embedded assertions, which we'll call "decorations."
We call the new commands _decorated commands_, or `DCom`s.

The formal syntax of decorated commands omits preconditions whenever possible, trying to embed just the postcondition.
* The `skip` command, for example, is decorated only with its postcondition
    `skip { Q }`
  on the assumption that the precondition will be provided by the context.
* Sequences `d₁; d₂` need no additional decorations.
  Why?
  Because inside `d₂` there will be a postcondition; this serves as the postcondition of `d₁; d₂`.
  Similarly, inside `d₁` there will also be a postcondition, which additionally serves as the _precondition_ for `d₂`.
* A loop `while b do d end` is decorated with its postconditioin and a precondition for the body:
    `while b do { P } d end { Q }`
  The postcondition embedded in `d` serves as the loop invariant.
* Implications `->>` can be added as decorations either for a precondition
    `->> { P } d`
  or a for a postcondition
    `d ->> { Q }`
Putting this all together gives us the formal syntax of decorated commands:
-/

inductive DCom :=
  | dc_skip (Q : Assertion)
  | dc_seq (d₁ d₂ : DCom)
  | dc_asgn (x : String) (a : AExp) (Q : Assertion)
  | dc_if (b : BExp) (P₁ : Assertion) (d₁ : DCom)
          (P₂ : Assertion) (d₂ : DCom) (Q : Assertion)
  | dc_while (b : BExp) (P : Assertion) (d : DCom)
              (Q : Assertion)
  | dc_pre (P : Assertion) (d : DCom)
  | dc_post (d : DCom) (Q : Assertion)

open DCom

/-
To provide the initial precondition that goes at the very top of a decorated program, we introduce a new type `Decorated`:
-/

inductive Decorated :=
  | decorated : Assertion → DCom → Decorated

open Decorated

/-
An example decorated program that decrements `x` to `0`:
```
  (1) { True }
        while x != 0 do
  (2)                     { True ∧ x ≠ 0 } ->>
  (3)                     { True }
          x := x - 1
  (4)                     { True }
        end
  (5) { True ∧ ¬(x ≠ 0) } -->
  (6) { x = 0 }
```
-/

def dec_while : Decorated := decorated (fun _ => True) (
  dc_post (
    dc_while <{x != 0}> (fun st => True ∧ st x ≠ 0) (
      dc_pre (fun _ => True) $
      dc_asgn x <{x - 1}> (fun _ => True)
    ) (fun st => True ∧ ¬(st x ≠ 0))
  ) (fun st => st x = 0)
)

attribute [local simp] dec_while

/-
It is easy to go from a dcom to a com by erasing all annotations.
-/

@[simp] def erase (d : DCom) : Com :=
  match d with
  | dc_skip _ => c_skip
  | dc_seq d₁ d₂ => c_seq (erase d₁) (erase d₂)
  | dc_asgn x a _ => c_asgn x a
  | dc_if b _ d₁ _ d₂ _ => c_if b (erase d₁) (erase d₂)
  | dc_while b _ d _ => c_while b (erase d)
  | dc_pre _ d => erase d
  | dc_post d _ => erase d

def erase_d (dec : Decorated) : Com :=
  match dec with
  | decorated _ d => erase d

/-
It is also straightforward to extract the precondition and postcondition from a decorated program.
-/

@[simp] def precondition_from (dec : Decorated) : Assertion :=
  match dec with
  | decorated P _ => P

@[simp] def post (d : DCom) : Assertion :=
  match d with
  | dc_skip P => P
  | dc_seq _ d₂ => post d₂
  | dc_asgn _ _ Q => Q
  | dc_if _ _ _ _ _ Q => Q
  | dc_while _ _ _ Q => Q
  | dc_pre _ d => post d
  | dc_post _ Q => Q

@[simp] def postcondition_from (dec : Decorated) : Assertion :=
  match dec with
  | decorated _ d => post d

/-
We can then express what it means for a decorated program to be correct as follows:
-/

def outer_triple_valid (dec : Decorated) :=
  {* precondition_from dec *}
    erase_d dec
  {* postcondition_from dec *}

/-
The outer Hoare triple of a decorated program is just a `Prop`; thus, to show that it is _valid_, we need to produce a proof of this proposition.

We will do this by extracting "proof obligations" from the decorations sprinkled through the program.

These obligations are often called _verification conditions_, because they are the facts that must be verified to see that the decorations are locally consistent and thus constitute a proof of validity of the outer triple.

### Extracting verification conditions

The function `verification_conditions` takes a decorated command `d` together with a precondition `P` and returns a _proposition_ that, if it can be proved, implies that the triple
  `{ P } erase d { post d }`
is valid.

It does this by walking over `d` and generating a big conjunction that includes
* local consistency checks for each form of command, plus
* uses of `->>` to bridge the gap between the assertions found inside a decorated command and the assertions imposed by the precondition from its context; these uses correspond to applications of the consequence rule.

_Local consistency_ is defined as follows:
* The decorated command
    `skip { Q }`
  is locally consistent with respect to a precondition `P` if `P ->> Q`.
* The sequential composition of `d₁` and `d₂` is locally consistent with respect to `P` if `d₁` is locally consistent with respect to `P` and `d₂` is locally consistent with respect to the postcondition of `d₁`.
* An assignment
    `x := a { Q }`
  is locally consistent with respect to a precondition `P` if
    `P ->> Q[x ↦ a]`
* A conditional
    `if b then {P₁} d₁ else {P₂} d₂ end {Q}`
  is locally consistent with respect to precondition `P` if
  (1) `P ∧ b ->> P₁`
  (2) `P ∧ ¬b ->> P₂`
  (3) `d₁` is locally consistent with respect to `P₁`
  (4) `d₂` is locally consistent with respect to `P₂`
  (5) `post d₁ ->> Q`
  (6) `post d₂ ->> Q`
* A loop
    `while b do {Q} d end {R}`
  is locally consistent with respect to precondition `P` if
  (1) `P ->> post d`
  (2) `post d ∧ b ->> Q`
  (3) `post d ∧ ¬b ->> R`
  (4) `d` is locally consistent with respect to `Q`
* A command with an extra assertion at the beginning
    `->> {Q} d`
  is locally consistent with respect to a precondition `P` if
  (1) `P ->> Q`
  (2) `d` is locally consistent with respect to `Q`
* A command with an extra assertion at the end
    `d ->> {Q}`
  is locally consistent with respect to a precondition `P` if
  (1) `d` is locally consistent with respect to `P`
  (2) `post d ->> Q`

With all this in mind, we can write is a _verification condition generator_ that takes a decorated command and reads off a proposition saying that all its decorations are locally consistent.

Formally, since a decorated command is "waiting for its precondition," the main VC generator takes a `DCom` plus a given predondition as arguments.
-/

@[simp] def verification_conditions (P : Assertion) (d : DCom) : Prop :=
  match d with
  | dc_skip Q =>
      P ->> Q
  | dc_seq d₁ d₂ =>
      verification_conditions P d₁
      ∧ verification_conditions (post d₁) d₂
  | dc_asgn x a Q =>
      (P ->> fun st => Q (st[x ↦ aeval st a]))
  | dc_if b P₁ d₁ P₂ d₂ Q =>
      ((fun st => P st ∧ beval st b) ->> P₁)
      ∧ ((fun st => P st ∧ ¬(beval st b)) ->> P₂)
      ∧ (post d₁ ->> Q) ∧ (post d₂ ->> Q)
      ∧ verification_conditions P₁ d₁
      ∧ verification_conditions P₂ d₂
  | dc_while b Q d R =>
      -- `post d` is both the loop invariant and the inital precondition
      (P ->> post d)
      ∧ ((fun st => post d st ∧ beval st b) ->> Q)
      ∧ ((fun st => post d st ∧ ¬(beval st b)) ->> R)
      ∧ verification_conditions Q d
  | dc_pre Q d =>
      (P ->> Q)
      ∧ verification_conditions Q d
  | dc_post d Q =>
      verification_conditions P d
      ∧ (post d ->> Q)

/-
The following key theorem states that `verification_conditions` does its job correctly.
Not surprisingly, each of the Hoare Logic rules gets used at some point in the proof.
-/

theorem verification_correct d P
    : verification_conditions P d → {* P *} erase d {* post d *} := by
  intro hvc
  induction d generalizing P with simp [erase, post, verification_conditions] at *
  | dc_skip =>
    apply hoare_consequence_pre
    . apply hoare_skip
    . assumption
  | dc_seq =>
    rename_i ih₁ ih₂
    cases hvc
    apply hoare_seq
    . apply ih₂; assumption
    . apply ih₁; assumption
  | dc_asgn =>
    apply hoare_consequence_pre
    . apply hoare_asgn
    . assumption
  | dc_if =>
    rename_i ih₁ ih₂
    rcases hvc with ⟨_, ⟨_, ⟨_, ⟨_, ⟨⟩⟩⟩⟩⟩
    apply hoare_if
    . apply hoare_consequence
      . apply ih₁; assumption
      . assumption
      . assumption
    . apply hoare_consequence
      . apply ih₂; assumption
      . simp; assumption
      . assumption
  | dc_while =>
    rename_i ih
    rcases hvc with ⟨_, ⟨_, ⟨⟩⟩⟩
    apply hoare_consequence
    . apply hoare_while
      apply hoare_consequence_pre
      . apply ih; assumption
      . assumption
    . assumption
    . simp; assumption
  | dc_pre =>
    rename_i ih
    cases hvc
    apply hoare_consequence_pre
    . apply ih; assumption
    . assumption
  | dc_post =>
    rename_i ih
    cases hvc
    apply hoare_consequence_post
    . apply ih; assumption
    . assumption

/-
Now that all the pieces are in place, we can define what it means to verify an entire program.
-/

@[simp] def verification_conditions_from (dec : Decorated) : Prop :=
  match dec with
  | decorated P d => verification_conditions P d

/-
This brings us to the main theorem of this section:
-/

theorem verification_conditions_correct dec
    : verification_conditions_from dec → outer_triple_valid dec := by
  apply verification_correct

/-
### More automation

The propositions generated by `verification_conditions` are fairly big and contain many conjuncts that are essentially trivial.
Fortunately, our `verify_assertion` tactic can generally take care of most or all of them.
-/

example : verification_conditions_from dec_while := by
  simp
  -- many conjuncts
  verify_assertion

/-
Here's a formal proof that `dec_while` is correct.
-/

theorem dec_while_correct : outer_triple_valid dec_while := by
  apply hoare_consequence_post
  . apply hoare_while
    apply hoare_consequence_pre
    . apply hoare_asgn
    . verify_assertion
  . verify_assertion


example : outer_triple_valid dec_while := by
  apply verification_correct
  verify_assertion

/-
To automate the overall process of verification, we can use `verification_correct` to extract the verification conditions, use `verify_assertion` to verify them as much as it can, and finally tidy up any remaining bits by hand.
-/

macro "verify" : tactic =>
  `(tactic|
    intros <;>
    apply verification_correct <;>
    verify_assertion
  )

/-
Here's the final, formal proof that `dec_while` is correct.
-/

theorem dec_while_correct'
    : outer_triple_valid dec_while := by
  verify

/-
Similarly, here is the formal decorated program for the "swapping by adding and subtracting" example that we saw earlier.
```
  (1) { x = m ∧ y = n } ->>
  (2) { (x + y) - ((x + y) - y) = n ∧ (x + y) - y = m }
        x := x + y;
  (3)                 { x - (x - y) = n ∧ x - y = m }
        y := x - y;
  (4)                 { x - y = n ∧ y = m }
        x := x - y
  (5) { x = n ∧ y = m }
```
-/

def swap_dec (m n : Nat) : Decorated := decorated
  (fun st => st x = m ∧ st y = n) $
  dc_pre (fun st => (st x + st y) - ((st x + st y) - st y) = n
                    ∧ (st x + st y) - st y = m) $
  dc_seq (
    dc_asgn x <{x + y}> (fun st => st x - (st x - st y) = n ∧ (st x - st y) = m)
  ) $
  dc_seq (
    dc_asgn y <{x - y}> (fun st => st x - st y = n ∧ st y = m)
  ) $
  dc_asgn x <{x - y}> (fun st => st x = n ∧ st y = m)

attribute [local simp] swap_dec

theorem swap_correct m n : outer_triple_valid (swap_dec m n) := by
  verify

/-
## references
* [Software Foundations, Volume 2 Programming Language Foundations: Hoare Logic, Part 2](https://softwarefoundations.cis.upenn.edu/plf-current/Hoare2.html)
-/
