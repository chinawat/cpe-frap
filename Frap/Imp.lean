import Lean.Data.HashMap

/-
# Towards an imperative programming language

We start formal reasoning about programs (for real) by introducing a programming language into Lean.
We begin with a language that everyone should be familiar with, in the _imperative language_ paradigm.
Constructs in an imperative language features statements and commands, such as assignments, conditionals, and loops.

## Arithmetic and boolean expressions

We begin with the definition of arithmetic and boolean expressions, defined inductively.

### Syntax
-/

namespace Hidden.AExp

inductive AExp where
  | a_num : Nat → AExp
  | a_plus : AExp → AExp → AExp
  | a_minus : AExp → AExp → AExp
  | a_mult : AExp → AExp → AExp

inductive BExp where
  | b_true : BExp
  | b_false : BExp
  | b_eq : AExp → AExp → BExp
  | b_neq : AExp → AExp → BExp
  | b_le : AExp → AExp → BExp
  | b_not : BExp → BExp
  | b_and : BExp → BExp → BExp
  | b_or : BExp → BExp → BExp

open AExp
open BExp

/-
### Evaluation

We evaluate arithmetic and boolean expressions recursively.
(Note: we can write subscripts such as `a₁` by typing `a\1`.)
-/

def aeval (a : AExp) : Nat :=
  match a with
  | a_num n => n
  | a_plus a₁ a₂ => (aeval a₁) + (aeval a₂)
  | a_minus a₁ a₂ => (aeval a₁) - (aeval a₂)
  | a_mult a₁ a₂ => (aeval a₁) * (aeval a₂)

def beval (b : BExp) : Bool :=
  match b with
  | b_true => true
  | b_false => false
  | b_eq a₁ a₂ => (aeval a₁) == (aeval a₂)
  | b_neq a₁ a₂ => (aeval a₁) != (aeval a₂)
  | b_le a₁ a₂ => (aeval a₁) <= (aeval a₂)
  | b_not b₁ => not (beval b₁)
  | b_and b₁ b₂ => and (beval b₁) (beval b₂)
  | b_or b₁ b₂ => or (beval b₁) (beval b₂)

/-
### Optimization

Right away, we can introduce some optimization prior to evaluation so that our expression tree is as compact as possible.
Here, we will optimize additions with zero on the left-hand side, and prove that the optimization preserves the meaning of the expression.
-/

def optimize_0plus (a : AExp) : AExp :=
  match a with
  | a_num _ => a
  | a_plus (a_num 0) a₂ => optimize_0plus a₂
  | a_plus a₁ a₂ => a_plus (optimize_0plus a₁) (optimize_0plus a₂)
  | a_minus a₁ a₂ => a_minus (optimize_0plus a₁) (optimize_0plus a₂)
  | a_mult a₁ a₂ => a_mult (optimize_0plus a₁) (optimize_0plus a₂)

example : optimize_0plus
      (a_plus (a_num 2)
              (a_plus (a_num 0)
                      (a_plus (a_num 0) (a_num 1))))
    = a_plus (a_num 2) (a_num 1) := by
  rfl

theorem optimize_0plus_sound (a : AExp)
    : aeval (optimize_0plus a) = aeval a := by
  induction a with
  | a_num _ => rfl
  | a_plus a₁ a₂ iha₁ iha₂ =>
      unfold optimize_0plus
      cases a₁ with simp [aeval] at *
      | a_num n =>
        cases n with simp [aeval]
        | zero => exact iha₂
        | succ _ => rw [iha₂]
      | a_plus => rw [iha₁, iha₂]
      | a_minus => rw [iha₁, iha₂]
      | a_mult => rw [iha₁, iha₂]
  | a_minus a₁ a₂ iha₁ iha₂ =>
      simp [optimize_0plus, aeval]
      rw [iha₁, iha₂]
  | a_mult a₁ a₂ iha₁ iha₂ =>
      simp [optimize_0plus, aeval]
      rw [iha₁, iha₂]

/-
exercise (2-star)
Define an optimizations for additions with zero on the right-hand side, and prove that the optimization preserves the meaning of the expression.
-/

def optimize_plus0 (a : AExp) : AExp :=
  sorry

example : optimize_plus0
      (a_plus (a_num 2)
              (a_plus (a_plus (a_num 1) (a_num 0))
                      (a_num 0)))
    = a_plus (a_num 2) (a_num 1) := by
  sorry

theorem optimize_plus0_sound (a : AExp)
    : aeval (optimize_plus0 a) = aeval a := by
  sorry

/-
## Evaluation as a relation

Previously, we defined a recursive function to compute the result of an expression.
While that approach usually works most of the time, it can make proofs less automatable and more convoluted.
An alternative is to define an inductive relation between expressions and their values.
-/

inductive AEvalR : AExp → Nat → Prop :=
  | e_a_num (n : Nat) : AEvalR (a_num n) n
  | e_a_plus (a₁ a₂ : AExp) (n₁ n₂ : Nat) :
      AEvalR a₁ n₁ → AEvalR a₂ n₂ → AEvalR (a_plus a₁ a₂) (n₁ + n₂)
  | e_a_minus (a₁ a₂ : AExp) (n₁ n₂ : Nat) :
      AEvalR a₁ n₁ → AEvalR a₂ n₂ → AEvalR (a_minus a₁ a₂) (n₁ - n₂)
  | e_a_mult (a₁ a₂ : AExp) (n₁ n₂ : Nat) :
      AEvalR a₁ n₁ → AEvalR a₂ n₂ → AEvalR (a_mult a₁ a₂) (n₁ * n₂)

/-
We can introduce a notation that makes expressions look more natural in Lean code.
We'll write `e ==> n` to mean that arithmetic expression `e` evaluates to value `n`.
-/
infix:90 " ==> " => AEvalR

/-
It is (almost) straightforward to prove that the relational and functional definitions of evaluation agree.
-/

example (a : AExp) (n : Nat)
    : a ==> n ↔ aeval a = n := by
  constructor
  . intro h
    induction h <;> simp [aeval, *]
  . intro h
    induction a with repeat simp [aeval, *] at *
    | a_num n' => constructor
    | a_plus a₁ a₂ ih₁ ih₂ =>
      sorry
    | _ => sorry

/-
In the proof above, we see that our induction is stuck, because the result of every `AExp` evaluation is `n`.
This is because when we perform induction, we have already introduced and fixed `n` as a parameter of the theorem.
As a result, the induction hypotheses become `aeval a₁ = n → a₁ ==> n` and `aeval a₂ = n → a₂ ==> n`.
But this statement ought to work for any value of `n`, so our induction hypotheses should be `∀ (n : Nat), aeval a₁ = n → a₁ ==> n` and `∀ (n : Nat), aeval a₂ = n → a₂ ==> n`.
We can reintroduce the universal quantifier by using a variant of the `induction` tactic that _generalizes_ over some variables before applying the induction but then introduces them in each goal.

Now, our proof goes through.
-/

theorem aeval_iff_AEvalR (a : AExp) (n : Nat)
    : a ==> n ↔ aeval a = n := by
  constructor
  . intro h
    induction h <;> simp [aeval, *]
  . intro h
    induction a generalizing n with repeat simp [aeval, *] at *
    | a_num n' => constructor
    | _ => rw [← h]; constructor <;> assumption

end Hidden.AExp

/-
### Computational vs relational definitions

In certain situations, relational definitions of evaluation works much better than computation ones.

For example, suppose we want to add division as another possible expression.
How do we deal with division by zero?
What should be the result returned from `aeval` function?
But in `AEvalR`, we can easily specify a precondition on when results will be available.
-/

namespace AEvalR_division

inductive AExp where
  | a_num : Nat → AExp
  | a_plus : AExp → AExp → AExp
  | a_minus : AExp → AExp → AExp
  | a_mult : AExp → AExp → AExp
  | a_div : AExp → AExp → AExp  -- new case

open AExp

inductive AEvalR : AExp → Nat → Prop :=
  | e_a_num (n : Nat) : AEvalR (a_num n) n
  | e_a_plus (a₁ a₂ : AExp) (n₁ n₂ : Nat) :
      AEvalR a₁ n₁ → AEvalR a₂ n₂ → AEvalR (a_plus a₁ a₂) (n₁ + n₂)
  | e_a_minus (a₁ a₂ : AExp) (n₁ n₂ : Nat) :
      AEvalR a₁ n₁ → AEvalR a₂ n₂ → AEvalR (a_minus a₁ a₂) (n₁ - n₂)
  | e_a_mult (a₁ a₂ : AExp) (n₁ n₂ : Nat) :
      AEvalR a₁ n₁ → AEvalR a₂ n₂ → AEvalR (a_mult a₁ a₂) (n₁ * n₂)
  | e_a_div (a₁ a₂ : AExp) (n₁ n₂ n₃ : Nat) :  -- new
      AEvalR a₁ n₁ → AEvalR a₂ n₂ → n₂ > 0
      → n₂ * n₃ = n₁ → AEvalR (a_div a₁ a₂) n₃

end AEvalR_division

/-
Or when we want to add a random number generator...
Here, we are saying what results are _possible_, without specifying any particular probability distributions for the results.
-/

namespace AEvalR_extended

inductive AExp where
  | a_any : AExp  -- new case
  | a_num : Nat → AExp
  | a_plus : AExp → AExp → AExp
  | a_minus : AExp → AExp → AExp
  | a_mult : AExp → AExp → AExp

open AExp

inductive AEvalR : AExp → Nat → Prop :=
  | e_a_any (n : Nat) : AEvalR a_any n  -- new
  | e_a_num (n : Nat) : AEvalR (a_num n) n
  | e_a_plus (a₁ a₂ : AExp) (n₁ n₂ : Nat) :
      AEvalR a₁ n₁ → AEvalR a₂ n₂ → AEvalR (a_plus a₁ a₂) (n₁ + n₂)
  | e_a_minus (a₁ a₂ : AExp) (n₁ n₂ : Nat) :
      AEvalR a₁ n₁ → AEvalR a₂ n₂ → AEvalR (a_minus a₁ a₂) (n₁ - n₂)
  | e_a_mult (a₁ a₂ : AExp) (n₁ n₂ : Nat) :
      AEvalR a₁ n₁ → AEvalR a₂ n₂ → AEvalR (a_mult a₁ a₂) (n₁ * n₂)

end AEvalR_extended

namespace Imp

/-
## Expressions with variables

In a typical imperative language, expressions may contain variables.
For simplicity (for now), we'll assume that all variables are global and that they only hold numbers.
-/

inductive AExp where
  | a_num : Nat → AExp
  | a_id : String → AExp  -- new case
  | a_plus : AExp → AExp → AExp
  | a_minus : AExp → AExp → AExp
  | a_mult : AExp → AExp → AExp

abbrev w := "w"
abbrev x := "x"
abbrev y := "y"
abbrev z := "z"

inductive BExp where
  | b_true : BExp
  | b_false : BExp
  | b_eq : AExp → AExp → BExp
  | b_neq : AExp → AExp → BExp
  | b_le : AExp → AExp → BExp
  | b_not : BExp → BExp
  | b_and : BExp → BExp → BExp
  | b_or : BExp → BExp → BExp

open AExp
open BExp

/-
Here, we declare a set of macros that will naturalize the appearance of expressions, so we have an easier time staring at them.

This is a somewhat advanced feature of Lean, so you don't need to understand it entirely yet, but it can be helpful when doing a larger project, as this will save you time writing down Lean terms.
-/

declare_syntax_cat imp

syntax num : imp
syntax str : imp
syntax:60 imp:60 "+" imp:61 : imp
syntax:60 imp:60 "-" imp:61 : imp
syntax:70 imp:70 "*" imp:71 : imp
syntax:50 imp:50 "=" imp:50 : imp
syntax:50 imp:50 "!=" imp:50 : imp
syntax:50 imp:50 "<=" imp:50 : imp
syntax:40 "!" imp:40 : imp
syntax:30 imp:30 "&&" imp:31 : imp
syntax:30 imp:30 "||" imp:31 : imp
syntax "True" : imp
syntax "False" : imp
syntax "(" imp ")" : imp
syntax "<{" imp "}>" : term
syntax ident : imp
syntax "<[" term "]>" : imp

macro_rules
  | `(term|<{$x}>) => `(imp|$x)
  | `(imp|$n:num) => `(a_num $n)
  | `(imp|$s:str) => `(a_id $s)
  | `(imp|$x + $y) => `(a_plus <{$x}> <{$y}>)
  | `(imp|$x - $y) => `(a_minus <{$x}> <{$y}>)
  | `(imp|$x * $y) => `(a_mult <{$x}> <{$y}>)
  | `(imp|True) => `(b_true)
  | `(imp|False) => `(b_false)
  | `(imp|$x = $y) => `(b_eq <{$x}> <{$y}>)
  | `(imp|$x != $y) => `(b_neq <{$x}> <{$y}>)
  | `(imp|$x <= $y) => `(b_le <{$x}> <{$y}>)
  | `(imp|!$x) => `(b_not <{$x}>)
  | `(imp|$x && $y) => `(b_and <{$x}> <{$y}>)
  | `(imp|$x || $y) => `(b_or <{$x}> <{$y}>)
  | `(imp|($x)) => `(<{$x}>)
  | `(imp|$x:ident) => `(a_id $(Lean.quote (toString x.getId)))
  | `(imp|<[$t:term]>) => pure t

/-
### States

To evaluate expressions with variables, we need a place to look up the value of a variable.
We will use an _association list_ for this purpose, with 0 as the default value.
Of course, in real systems, we would use a more efficient data structure, which we can _prove_ that it works the same way, i.e., we can interchange data structures for states without affecting the correctness of the evaluation.
-/

abbrev State := List (String × Nat)

open List

def empty : State := nil

def insert' (st : State) (k : String) (v : Nat) : State :=
  match st with
  | nil => [(k, v)]
  | cons (k', v') st' =>
    if k == k' then cons (k, v) st'
    else cons (k', v') (insert' st' k v)

def lookup' (st : State) (k : String) : Nat :=
  match st with
  | nil => 0
  | cons (k', v') st' =>
    if k == k' then v' else lookup' st' k

/-
We can prove properties about our association lists as states.
-/

theorem map_lookup_insert_eq st (x : String) (v : Nat)
    : lookup' (insert' st x v) x = v := by
  induction st with
  | nil => simp [lookup']
  | cons p st' ih =>
    obtain ⟨k', v'⟩ := p
    unfold insert'
    split
    . simp [lookup']
    . simp [lookup', *]

theorem map_lookup_insert_neq st (x x' : String) (v : Nat)
    : x' ≠ x
      → lookup' (insert' st x v) x' = lookup' st x' := by
  intro hneq
  induction st with
  | nil => simp [lookup', *]
  | cons p st' ih =>
    obtain ⟨k', v'⟩ := p
    unfold insert'
    split
    . simp [lookup', *] at *
      have h: x' ≠ k' := by
        intro hneq'; apply hneq
        rw [hneq']; apply Eq.symm; assumption
      simp [h]
    . simp [lookup', *]

/-
The evaluation functions now require a state as an argument.
-/

def aeval (st : State) (a : AExp) : Nat :=
  match a with
  | a_num n => n
  | a_id x => lookup' st x
  | a_plus a₁ a₂ => (aeval st a₁) + (aeval st a₂)
  | a_minus a₁ a₂ => (aeval st a₁) - (aeval st a₂)
  | a_mult a₁ a₂ => (aeval st a₁) * (aeval st a₂)

def beval (st : State) (b : BExp) : Bool :=
  match b with
  | b_true => true
  | b_false => false
  | b_eq a₁ a₂ => (aeval st a₁) == (aeval st a₂)
  | b_neq a₁ a₂ => (aeval st a₁) != (aeval st a₂)
  | b_le a₁ a₂ => (aeval st a₁) <= (aeval st a₂)
  | b_not b₁ => not (beval st b₁)
  | b_and b₁ b₂ => and (beval st b₁) (beval st b₂)
  | b_or b₁ b₂ => or (beval st b₁) (beval st b₂)

/-
We can try evaluating some expressions under given states.
-/

example : aeval (insert' empty x 5)
    <{3 + x * 2}>
    -- (a_plus (a_num 3) (a_mult (a_id x) (a_num 2)))
    = 13 := by
  simp [aeval, map_lookup_insert_eq]

example : aeval (insert' (insert' empty y 4) x 5)
    <{z + x * y}>
    = 20 := by
  simp [x, y, aeval, lookup', insert', map_lookup_insert_eq]

example : beval (insert' empty x 5)
    <{ True && !(x <= 4) }>
    = true := by
  simp [x, beval, insert', aeval, lookup']

/-
We can define evaluation as a relation, like before.
But we need to talk about state in our relation.
-/

inductive AEvalR : State → AExp → Nat → Prop :=
  | e_a_num (st : State) (n : Nat) : AEvalR st (a_num n) n
  | e_a_id (st : State) (x : String) (n : Nat) :
      lookup' st x = n → AEvalR st (a_id x) n
  | e_a_plus (st : State) (a₁ a₂ : AExp) (n₁ n₂ : Nat) :
      AEvalR st a₁ n₁ → AEvalR st a₂ n₂ → AEvalR st (a_plus a₁ a₂) (n₁ + n₂)
  | e_a_minus (st : State) (a₁ a₂ : AExp) (n₁ n₂ : Nat) :
      AEvalR st a₁ n₁ → AEvalR st a₂ n₂ → AEvalR st (a_minus a₁ a₂) (n₁ - n₂)
  | e_a_mult (st : State) (a₁ a₂ : AExp) (n₁ n₂ : Nat) :
      AEvalR st a₁ n₁ → AEvalR st a₂ n₂ → AEvalR st (a_mult a₁ a₂) (n₁ * n₂)

/-
Our proof of equivalence of the definitions only needs a little bit of tweaks.
-/

/-
exercise (2-star)
Prove that, on the augmented version of arithmetic expressions, the functional and relational definitions are equivalent.
-/

theorem aeval_iff_AEvalR (st : State) (a : AExp) (n : Nat)
    : AEvalR st a n ↔ aeval st a = n := by
  sorry

/-
## Behavioral equivalence

To talk about the correctness of program transformations, we need to be able to say when two expressions are _behaviorally equivalent_, i.e., they evaluate to the same result in every state.
-/

def aequiv (a₁ a₂ : AExp) : Prop :=
  ∀ (st : State), aeval st a₁ = aeval st a₂

def bequiv (b₁ b₂ : BExp) : Prop :=
  ∀ (st : State), beval st b₁ = beval st b₂

theorem aequiv_example
    : aequiv <{x - x}> <{0}> := by
  intro st
  simp [aeval]

theorem bequiv_example
    : bequiv <{x - x = 0}> <{True}> := by
  intro st
  simp [beval, aeval]

/-
## Commands

We now introduce commands in our imperative language:
* `skip`: do nothing
* `x := a`: assignment to a variable
* `c₁; c₂`: do `c₁`, then `c₂` (sequencing operation)
* `if b then c₁ else c₂`: conditional statement
* `while b do c end`: loop
-/

inductive Com :=
  | c_skip : Com
  | c_asgn : String → AExp → Com
  | c_seq : Com → Com → Com
  | c_if : BExp → Com → Com → Com
  | c_while : BExp → Com → Com

open Com

syntax "skip" : imp
syntax:20 imp:20 ":=" imp:21 : imp
syntax:20 imp:20 ";" imp:20 : imp
syntax:20 "if" imp:20 "then" imp:20 "else" imp:20 : imp
syntax:20 "while" imp:20 "do" imp:20 "end" : imp

macro_rules
  | `(imp|skip) => `(c_skip)
  | `(imp|$x:str := $y) => `(c_asgn $x <{$y}>)
  | `(imp|$x:ident := $y) => `(c_asgn $x <{$y}>)
  | `(imp|$c1 ; $c2) => `(c_seq <{$c1}> <{$c2}>)
  | `(imp|if $b then $c1 else $c2) => `(c_if <{$b}> <{$c1}> <{$c2}>)
  | `(imp|while $b do $c end) => `(c_while <{$b}> <{$c}>)

/-
We can write some simple programs in our macro language, _without worrying about their meaning_ just yet.
-/

def factorial_in_lean4 : Com :=
  <{ z := x;
     y := 1;
     while z != 0 do
       y := y * z;
       z := (z - 1)
     end }>

def plus2 : Com := <{ x := x + 2 }>

def xTimesYInZ : Com := <{ z := x * y }>

def subtract_slowly_body : Com :=
  <{ z := z - 1;
     x := x - 1 }>

def subtract_slowly : Com :=
  <{ while x != 0 do
       <[subtract_slowly_body]>
     end }>

def subtract_3_from_5_slowly : Com :=
  <{ x := 3;
     z := 5;
     <[subtract_slowly]> }>

def loop : Com :=
  <{ while True do
       skip
     end }>

/-
## references
* [Software Foundations, Volume 1 Logical Foundations: Simple Imperative Programs](https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html)
* [Software Foundations, Volume 2 Programming Language Foundations: Program Equivalence](https://softwarefoundations.cis.upenn.edu/plf-current/Equiv.html)
* [Lean Manual: Macro Overview](https://lean-lang.org/lean4/doc/macro_overview.html)
* [Lean Manual: Arithmetic DSL](https://lean-lang.org/lean4/doc/metaprogramming-arith.html)
* Anne Baanen, Alexander Bentkamp, Janmin Blanchette, Johannes Hölzl, Jannis Limperg. [The Hitchhiker's Guide to Logical Verification](https://raw.githubusercontent.com/blanchette/logical_verification_2023/main/hitchhikers_guide.pdf), version November 21, 2023.  Chapter 5.7.
-/
