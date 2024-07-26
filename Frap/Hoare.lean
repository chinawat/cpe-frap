import Frap.Trans

namespace Imp
open AExp
open BExp
open Com
open CEval
attribute [local simp]
  aeval beval aequiv bequiv cequiv

/-
## Proving inequivalence

We can prove that two programs are inequivalent by providing a counterexample initial state that, after executing each program from this initial state, results in two different states.
-/

theorem inequiv_loop_skip : ¬ cequiv loop c_skip := by
  intro contra
  unfold cequiv at contra
  apply loop_never_stops
  rw [contra empty]
  constructor

example : ¬ cequiv loop c_skip := by
  simp
  exists empty
  exists empty
  intro contra
  apply loop_never_stops
  rw [contra]
  constructor

namespace Hoare

/-
# Hoare logic

Our goal in this chapter is to carry out some simple examples of program verification -- i.e., to use the precise definition of Imp to prove formally that particular programs satisfy particular specifications of their behavior.

We'll develop a reasoning system called _Floyd-Hoare Logic_ -- often shortened to just _Hoare Logic_ -- in which each of the syntactic constructs of Imp is equipped with a generic "proof rule" that can be used to reason compositionally about the correctness of programs involving this construct.

Hoare Logic originated in the 1960s, and it continues to be the subject of intensive research right up to the present day.
It lies at the core of a multitude of tools that are being used in academia and industry to specify and verify real software systems.

Hoare Logic combines two beautiful ideas: a natural way of writing down _specifications_ of programs, and a _structured proof technique_ for proving that programs are correct with respect to such specifications -- where by "structured" we mean that the structure of proofs directly mirrors the structure of the programs that they are about.

## Assertions

An _assertion_ is a logical claim about the state of a program's memory -- formally, a property of `State`s.
-/

abbrev Assertion := State → Prop

/-
For example,
* `fun st => st x = 3` holds for states `st` in which value of `x` is 3
* `fun st => True` holds for all states
* `fun st => False` holds for no states

Given two assertions `P` and `Q`, we say that `P` _implies_ `Q`, written `P ->> Q`, if, whenever `P` holds in some state `st`, `Q` also holds.
-/

def assert_implies (P Q : Assertion) : Prop :=
  ∀ st, P st → Q st

declare_syntax_cat hoare

infix:36 " ->> " => assert_implies
syntax:36 term "<<->>" term : term
macro_rules
  | `(term|$p <<->> $q) => `($p ->> $q ∧ $q ->> $p)

/-
## Hoare triples

A _Hoare triple_ is a claim about the state before and after executing a command. The standard notation is
  `{P} c {Q}`
meaning:
* if command `c` begins executing in a state satisfying assertion `P`,
* and if `c` eventually terminates in some final state,
* then that final state will satisfy the assertion `Q`.

This is a _partial correctness_ statement: the program is correct if it terminates normally (i.e., no run-time error, no infinite loop or divergence).

Assertion `P` is called the _precondition_ of the triple, and `Q` is the _postcondition_.

For example,
* `{x = 0} x := x+1 {x = 1}` is a valid Hoare triple, stating that assignment command `x := x+1` will transform a state in which `x = 0` to a state in which `x = 1`.
* `∀ m, {x = m} x := x+1 {x = m+1}` is a _propositioni_ stating that the Hoare triple `{x = m} x := x+1 {x = m+1}` is valid for any choice of `m`.

Because single curly braces are already used for focusing proof goals in Lean, we'll write Hoare triples as follows:
  `{* P *} c {* Q *}`
-/

def valid_hoare_triple (P : Assertion) (c : Com) (Q : Assertion) : Prop :=
  ∀ st st', P st → (st =[<[c]>]=> st') → Q st'

syntax:30 "{*" term "*}" term "{*" term "*}" : term
macro_rules
  | `(term|{*$p*} $c {*$q*}) => `(valid_hoare_triple $p $c $q)

-- { True } x := 0 { True }
#check {* fun _ => True *} <{x := 0}> {* fun _ => True *}

example :
    {* fun _ => True *}
      <{x := 0}>
    {* fun _ => True *} := by
  -- unfold valid_hoare_triple
  intro st st' hPre _
  assumption

example : True := by
  constructor

#print True

/-
exercise (1-star)
Prove that if `Q` holds in every state, then any triple with `Q` as its postcondition is valid.
-/

theorem hoare_post_true P Q c : (∀ st, Q st) → {* P *} c {* Q *} := by
  sorry

/-
exercise (1-star)
Prove that if `P` holds in no state, then any triple with `P` as its precondition is valid.
-/

theorem hoare_pre_false P Q c : (∀ st, ¬ P st) → {* P *} c {* Q *} := by
  sorry

/-
## Proof rules

The goal of Hoare logic is to provide a _compositional_ method for proving the validity of specific Hoare triples.
That is, we want the structure of a program's correctness proof to mirror the structure of the program itself.
To this end, in the sections below, we'll introduce a rule for reasoning about each of the different syntactic forms of commands in Imp -- one for assignment, one for sequencing, one for conditionals, etc. -- plus a couple of "structural" rules for gluing things together.
We will then be able to prove programs correct using these proof rules, without ever unfolding the definition of `valid_hoare_triple`.

### Skip

Since `skip` doesn't change the state, it preserves any assertion `P`.
-/

theorem hoare_skip P : {* P *} <{skip}> {* P *} := by
  intro st st' hPre hEval
  cases hEval
  exact hPre

/-
### Sequencing

If command `c₁` takes any state where `P` holds to a state where `Q` holds, and if `c₂` takes any state where `Q` holds to a state where `R` holds, then doing `c₁` followed by `c₂` will take any state where `P` holds to one where `R` holds.

Note that, in the formal rule `hoare_seq`, the premises are given in backwards order (`c₂` before `c₁`).
This matches the natural flow of information in many of the situations where we'll use the rule, since the natural way to construct a Hoare-logic proof is to begin at the end of the program (with the final postcondition) and push postconditions backwards through commands until we reach the beginning.
-/

theorem hoare_seq P Q R c₁ c₂ :
    {* Q *} c₂ {* R *} → {* P *} c₁ {* Q *} → {* P *} c_seq c₁ c₂ {* R *} := by
  intro hc₂ hc₁ st st' hPre hEval
  cases hEval
  rename_i hE₁ hE₂
  apply hc₂
  . apply hc₁
    . exact hPre
    . exact hE₁
  . exact hE₂

/-
### Assignment

The rule for assignment is the most fundamental of the Hoare logic proof rules.
Here's how it works.

Consider this incomplete Hoare triple:
  `{ ??? }  x := y  { x = 1 }`
We want to assign `y` to `x` and finish in a state where `x` is `1`.
What could the precondition be?

One possibility is `y = 1`, because if `y` is already `1` then assigning it to `x` causes `x` to be `1`.
That leads to a valid Hoare triple:
  `{ y = 1 }  x := y  { x = 1 }`

It may seem as though coming up with that precondition must have taken some clever thought.
But there is a mechanical way we could have done it: if we take the postcondition `x = 1` and in it replace `x` with `y`---that is, replace the left-hand side of the assignment statement with the right-hand side---we get the precondition, `y = 1`.

That same idea works in more complicated cases.
For example:
  `{ ??? }  x := x + y  { x = 1 }`
If we replace the `x` in `x = 1` with `x + y`, we get `x + y = 1`.
That again leads to a valid Hoare triple:
  `{ x + y = 1 }  x := x + y  { x = 1 }`

Why does this technique work?
The postcondition identifies some property `Q` that we want to hold of the variable `x` being assigned.
In this case, `Q` is "equals `1`".
To complete the triple and make it valid, we need to identify a precondition that guarantees that property will hold of `x`.
Such a precondition must ensure that the same property holds of _whatever_ is being assigned to `x`.
So, in the example, we need "equals `1`" to hold of `x + y`.
That's exactly what the technique guarantees.

In general, the postcondition could be some arbitrary assertion `Q`, and the right-hand side of the assignment could be some arbitrary arithmetic expression `a`:
  `{ ??? }  x := a  { Q }`
The precondition would then be `Q`, but with any occurrences of `x` in it replaces by `a`.
Let's introduce a notation for this idea of replacing occurrences.
Define `Q [x ⊢> a]` to mean "`Q` where `a` is substituted in place of `x`".

This yields the Hoare logic rule for assignment.
  `{ Q [x ⊢> a] }  x := a  { Q }`
One way of reading this rule is: If you want statement `x := a` to terminate in a state that satisfies assertion `Q`, then it suffices to start in a state that also satisfies `Q`, except where `a` is substituted for every occurrence of `x`.

To many people, this rule seems "backwards" at first, because it proceeds from the postcondition to the precondition.
Actually it makes good sense to go in this direction: the postcondition is often what is more important, because it characterizes what we can assume afer running the code.

Here are some valid instances of the assignment rule:

  { (X ≤ 5) [X ⊢> X + 1] }   (that is, X + 1 ≤ 5)
    X := X + 1
  { X ≤ 5 }

  { (X = 3) [X ⊢> 3] }        (that is, 3 = 3)
    X := 3
  { X = 3 }

  { (0 ≤ X ∧ X ≤ 5) [X ⊢> 3] }  (that is, 0 ≤ 3 ∧ 3 ≤ 5)
    X := 3
  { 0 ≤ X ∧ X ≤ 5 }

-/

macro s:term "[" name:term "↦" val:term "]" : term =>
  `(insert' $s $name $val)

theorem hoare_asgn Q x a :
    {* fun st => Q (st[x ↦ aeval st a]) *} c_asgn x a {* Q *} := by
  intro st st' hPre hEval
  cases hEval
  simp [*] at *
  exact hPre

example :
    -- { (x < 5)[x ↦ x+1]}
    {* fun st => (fun st' => lookup' st' x < 5) (st[x ↦ aeval st <{x + 1}>]) *}
      <{x := x + 1}>
    -- { x < 5 }
    {* fun st => lookup' st x < 5 *} := by
  apply hoare_asgn (fun st => lookup' st x < 5)

/-
Complete these Hoare triples by providing an appropriate precondition using ∃, then prove then with `apply hoare_asgn`.
If you find that tactic doesn't suffice, double check that you have completed the triple properly.
-/

/-
exercise (2-star)
-/

example : ∃ P,
    {* P *}
      <{ x := 2 * x }>
    -- { x ≤ 10 }
    {* fun st => lookup' st x <= 10 *} := by
  sorry

/-
exercise (2-star)
-/

example : ∃ P,
    {* P *}
      <{ x := 3 }>
    -- { 0 ≤ x ∧ x ≤ 5 }
    {* fun st => 0 <= lookup' st x ∧ lookup' st x <= 5 *} := by
  sorry

/-
By using a _parameter_ `m` (a Lean number) to remember the original value of `x`, we can define a Hoare rule for assignment that does, intuitively, "work forwards" rather than backwards.
-/

theorem hoare_asgn_fwd m a (P : Assertion) :
    {* fun st => P st ∧ lookup' st x = m *}
      c_asgn x a
    {* fun st' => P (st'[x ↦ m]) ∧ lookup' st' x = aeval (st'[x ↦ m]) a *} := by
  intro st st' hPre hEval
  cases hEval
  cases hPre
  rename_i hP hxm
  constructor
  . -- need a lemma that `x = m → st = st[x ↦ m]`
    -- and a lemma that `(st[x ↦ n])[x ↦ m] = st[x ↦ m]`
    sorry
  . simp [map_lookup_insert_eq]
    sorry

/-
exercise (2-star)
Another way to define a forward rule for assignments is to existentially quantify over the previous value of the assigned variable.
Prove that it is correct.
-/

theorem hoare_asgn_fwd_exists a (P : Assertion) :
    {* P *}
      c_asgn x a
    {* fun st' => ∃ m, P (st'[x ↦ m]) ∧ lookup' st' x = aeval (st'[x ↦ m]) a *} := by
  sorry

/-
### Consequence

Sometimes the preconditions and postconditions we get from the Hoare rules won't quite be the ones we want in the particular situation at hand -- they may be logically equivalent but have a different syntactic form that fails to unify with the goal we are trying to prove, or they actually may be logically weaker (for preconditions) or stronger (for postconditions) than what we need.

For instance,
  `{(X = 3) [X ↦ 3]} X := 3 {X = 3}`,
follows directly from the assignment rule, but
  `{True} X := 3 {X = 3}`
does not.
This triple is valid, but it is not an instance of `hoare_asgn` because `True` and `(X = 3) [X ↦ 3]` are not syntactically equal assertions.

However, they are _logically equivalent_, so if one triple is valid, then the other must certainly be as well.
We can capture this observation with the following rule:
  `{ P' } c { Q } → (P <<->> P') → { P } c { Q }`

Taking this line of thought a bit further, we can see that strengthening the precondition or weakening the postcondition of a valid triple always produces another valid triple.
This observation is captured by two _Rules of Consequence_.
  `{ P' } c { Q } → (P ->> P') → { P } c { Q }`
  `{ P } c { Q' } → (Q' ->> Q) → { P } c { Q }`

Here are the formal versions:
-/

theorem hoare_consequence_pre P P' Q c :
    {* P' *} c {* Q *}
    → P ->> P'
    → {* P *} c {* Q *} := by
  intro hHoare hImp st st' hPre hEval
  apply hHoare
  . apply hImp; exact hPre
  . exact hEval

theorem hoare_consequence_post P Q Q' c :
    {* P *} c {* Q' *}
    → Q' ->> Q
    → {* P *} c {* Q *} := by
  intro hHoare hImp st st' hPre hEval
  apply hImp
  apply hHoare
  . exact hPre
  . exact hEval

example :
    -- { True }
    {* fun _ => True *}
      <{ x := 1 }>
    -- { x = 1 }
    {* fun st => lookup' st x = 1 *} := by
  apply hoare_consequence_pre
  . apply hoare_asgn
  . intro st _
    simp [map_lookup_insert_eq]

/-
Finally, here is a combined rule of consequence that allows us to vary both the precondition and the postcondition.
-/

theorem hoare_consequence P P' Q Q' c :
    {* P' *} c {* Q' *}
    → P ->> P'
    → Q' ->> Q
    → {* P *} c {* Q *} := by
  intro hHoare hPre hPost
  apply hoare_consequence_pre
  . apply hoare_consequence_post
    . exact hHoare
    . exact hPost
  . exact hPre

/-
### Conditionals

What sort of rule do we want for reasoning about conditional commands?

Certainly, if the same assertion `Q` holds after executing either of the branches, then it holds after the whole conditional.
So we might be tempted to write:
  `{ P } c₁ { Q } → { P } c₂ { Q } → { P } if b then c₁ else c₂ end { Q }`

However, this is rather weak.
For example, using this rule, we cannot show
  { True }
    if X = 0
      then Y := 2
      else Y := X + 1
    end
  { X ≤ Y }
since the rule tells us nothing about the state in which the assignments take place in the "then" and "else" branches.

Fortunately, we can say something more precise.
In the "then" branch, we know that the boolean expression `b` evaluates to true, and in the "else" branch, we know it evaluates to false.
Making this information available in the premises of the rule gives us more information to work with when reasoning about the behavior of `c₁` and `c₂` (i.e., the reasons why they establish the postcondition `Q`).
  { P ∧ b } c₁ { Q }
  → { P ∧ ¬b } c₂ { Q }
  → { P } if b then c₁ else c₂ end { Q }
-/

theorem hoare_if P Q b c₁ c₂ :
    {* fun st => P st ∧ beval st b *} c₁ {* Q *}
    → {* fun st => P st ∧ ¬(beval st b) *} c₂ {* Q *}
    → {* P *} c_if b c₁ c₂ {* Q *} := by
  intro hTrue hFalse st st' hPre hEval
  cases hEval
  . rename_i hb hc₁
    apply hTrue
    . constructor
      . exact hPre
      . exact hb
    . exact hc₁
  . rename_i hb hc₂
    apply hFalse
    . constructor
      . exact hPre
      . simp [hb]
    . exact hc₂

example :
    -- { True }
    {* fun _ => True *}
      <{if x = 0 then y := 2 else y := x + 1 end}>
    -- { x ≤ y }
    {* fun st => lookup' st x <= lookup' st y *} := by
  sorry

/-
exercise (2-star)
-/

example :
    -- { True }
    {* fun _ => True *}
      <{if x <= y then z := y - x else y := x + z end}>
    -- { y = x + z }
    {* fun st => lookup' st y = lookup' st x + lookup' st z *} := by
  sorry

/-
## While loops

The Hoare rule for `while` loops is based on the idea of a _command invariant_ (or just _invariant_): an assertion whose truth is guaranteed after executing a command, assuming it is true before.

That is, an assertion `P` is a command invariant of `c` if
  `{ P } c { P }`
holds.
Note that the command invariant might temporarily become false in the middle of executing `c`, but by the end of `c` it must be restored.

As a first attempt at a `while` rule, we could try:
  `{ P } c { P } → { P } while b do c end { P }`
That rule is valid: if `P` is a command invariant of `c`, as the premise requires, then no matter how many times the loop body executes, `P` is going to be true when the loop finally finishes.

But the rule also omits two crucial pieces of information.
First, the loop terminates when `b` becomes false. So we can strengthen the postcondition in the conclusion:
  `{ P } c { P } → { P } while b do c end { P ∧ ¬b }`
Second, the loop body will be executed only if `b` is true.
So we can also strengthen the precondition in the premise:
  `{ P ∧ b } c { P } → { P } while b do c end { P ∧ ¬b }`

That is the Hoare `while` rule.
Note how it combines aspects of skip and conditionals:
* If the loop body executes zero times, the rule is like `skip` in that the precondition survives to become (part of) the postcondition.
* Like a conditional, we can assume guard `b` holds on entry to the subcommand.
-/

theorem hoare_while P b c :
    {* fun st => P st ∧ beval st b *} c {* P *}
    → {* P *} c_while b c {* fun st => P st ∧ ¬(beval st b) *} := by
  intro hHoare st st' hPre hEval
  -- we proceed by induction on `hEval`
  generalize hloop : c_while b c = cmd at *
  induction hEval with simp at *
  | e_whileFalse =>
    constructor
    . exact hPre
    . simp [*]
  | e_whileTrue =>
    simp [*] at *
    rename_i ih
    apply ih
    apply hHoare
    . constructor
      . apply hPre
      . assumption
    . assumption

/-
## references
* [Software Foundations, Volume 2 Programming Language Foundations: Hoare Logic, Part 1](https://softwarefoundations.cis.upenn.edu/plf-current/Hoare.html)
* Anne Baanen, Alexander Bentkamp, Janmin Blanchette, Johannes Hölzl, Jannis Limperg. [The Hitchhiker's Guide to Logical Verification](https://raw.githubusercontent.com/blanchette/logical_verification_2023/main/hitchhikers_guide.pdf), version November 21, 2023.  Chapter 10.
-/
