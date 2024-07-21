import Frap.Imp

namespace Imp

namespace Hidden

/-
Recall the definition of commands from last time.
-/

inductive Com :=
  | c_skip : Com
  | c_asgn : String → AExp → Com
  | c_seq : Com → Com → Com
  | c_if : BExp → Com → Com → Com
  | c_while : BExp → Com → Com

end Hidden

open AExp
open BExp
open Com

/-
## Evaluating commands

An evaluation of a command takes the current state and a command, and produces the resulting state.

`ceval` : State × Com → State

### Evaluation as a function (failed atteempt)

Here's an attempt at defining an evaluation function for commands (with a bogus `while` case).
-/

def ceval_fun_no_while (st : State) (c : Com) : State :=
  match c with
  | c_skip => st
  | c_asgn x a =>
      insert' st x (aeval st a)
  | c_seq c₁ c₂ =>
      let st' := ceval_fun_no_while st c₁
      ceval_fun_no_while st' c₂
  | c_if b c₁ c₂ =>
      if beval st b
      then ceval_fun_no_while st c₁
      else ceval_fun_no_while st c₂
  | c_while _ _ => st  -- bogus

/-
We could try defining the `while` case that reflects the actual evaluation, as follows.
-/

-- def ceval_fun_failed (st : State) (c : Com) : State :=
--   match c with
--   | c_skip => st
--   | c_asgn x a =>
--       insert' st x (aeval st a)
--   | c_seq c₁ c₂ =>
--       let st' := ceval_fun_failed st c₁
--       ceval_fun_no_while st' c₂
--   | c_if b c₁ c₂ =>
--       if beval st b
--       then ceval_fun_failed st c₁
--       else ceval_fun_failed st c₂
--   | c_while b c' =>
--       if beval st b
--       then ceval_fun_failed st (<{<[c]>; while <[b]> do <[c]> end }>)
--       else st

/-
But Lean doesn't accept such a definition: "fail to show termination for `ceval_fun_failed`: argument #2 was not used for structural recursion; failed to eliminate recursive application".
Indeed, this function doesn't always terminate, especially when applied to the infinite loop `while True do skip`.

Here, we see a limitation of functional definitions for evaluating commands.
This is where a relational definition becomes necessary.

### Evaluation as a relation

We will use the notation `st =[ c ]=> st'` to mean that executing program `c` in a starting state `st` results in an ending state `st'`.
This can be pronounced "`c` takes state `st` to `st'`".
-/

inductive CEval : Com → State → State → Prop :=
  | e_skip : ∀ st,
      CEval c_skip st st
  | e_asgn : ∀ a n x st,
      aeval st a = n
      → CEval (c_asgn x a) st (insert' st x n)
  | e_seq : ∀ c₁ c₂ st st' st'',
      CEval c₁ st st' → CEval c₂ st' st''
      → CEval (c_seq c₁ c₂) st st''
  | e_ifTrue : ∀ b c₁ c₂ st st',
      beval st b = true → CEval c₁ st st'
      → CEval (c_if b c₁ c₂) st st'
  | e_ifFalse : ∀ b c₁ c₂ st st',
      beval st b = false → CEval c₂ st st'
      → CEval (c_if b c₁ c₂) st st'
  | e_whileFalse : ∀ b c st,
      beval st b = false
      → CEval (c_while b c) st st
  | e_whileTrue : ∀ b c st st' st'',
      beval st b = true
      → CEval c st st'
      → CEval (c_while b c) st' st''
      → CEval (c_while b c) st st''

open CEval
syntax:30 term " =[ " imp " ]=> " term : term
macro_rules
  | `(term|$st =[ $c ]=> $st') => `(CEval <{$c}> $st $st')

attribute [local simp]
  aeval beval insert' lookup' map_lookup_insert_eq map_lookup_insert_neq

/-
The cost of defining evaluation as a relation instead of a function is that we now need to construct a _proof_ that some program evaluates to some result state, rather than just letting Lean's computation mechanism do it for us.
-/

example : empty =[
      x := 2;
      if (x <= 1) then y := 3 else z := 4 end
    ]=> insert' (insert' empty x 2) z 4 := by
  constructor  -- c_seq
  . constructor  -- c_asgn
    rfl  -- aeval
  . apply e_ifFalse  -- c_if
    . simp
      -- simp [beval, aeval, map_lookup_insert_eq]  -- without `local simp` above
    . constructor  -- c_asgn
      rfl

/-
We now introduce another notation to facilitate working with states.
We'll write `x !-> v ; st` to mean that "update `x` with value `v` in state `st`".
-/

syntax term "!->" term "; " term : term
macro_rules
  | `(term|$x:term !-> $a:term ; $st) => `(insert' $st $x $a)

example : empty =[
      x := 2;
      if (x <= 1) then y := 3 else z := 4 end
    ]=> (z !-> 4; x !-> 2; empty) := by
  constructor  -- c_seq
  . constructor  -- c_asgn
    rfl  -- aeval
  . apply e_ifFalse  -- c_if
    . simp
      -- simp [beval, aeval, map_lookup_insert_eq]  -- without `local simp` above
    . constructor  -- c_asgn
      rfl

/-
exercise (2-star)
-/

example : empty =[
      x := 0;
      y := 1;
      z := 2
    ]=> (z !-> 2; y !-> 1; x !-> 0; empty) := by
  sorry

/-
### Determinism of evaluation

Changing from a computational to a relational definition of evaluation is a good move because it frees us from the artificial requirement that evaluation should be a total function.
But it also raises a question: Is the second definition of evaluation really a partial function?
Or is it possible that, beginning from the same state `st`, we could evaluate some command `c` in different ways to reach two different output states `st'` and `st''`?

In fact, this cannot happen: `ceval` _is_ a partial function.
-/

theorem ceval_deterministic c st st₁ st₂ :
    (st =[ <[c]> ]=> st₁) → (st =[ <[c]> ]=> st₂) → st₁ = st₂ := by
  intro he₁ he₂
  induction he₁ generalizing st₂ with
  | e_skip => cases he₂; rfl
  | e_asgn => cases he₂; simp [*] at *; congr
  | e_seq c₁ c₂ st' st'' _ _ _ ih₁ ih₂ =>
      apply ih₂
      cases he₂ with
      | e_seq _ _ _ st₂' =>
          have h : st'' = st₂' := by
            apply ih₁; assumption
          simp [*]
  | e_ifTrue _ _ _ _ _ _ _ ih =>
      cases he₂ with
      | e_ifTrue => -- b evaluates to true in 2nd execution
        apply ih; assumption
      | e_ifFalse => -- b evaluates to false in 2nd execution (contradiction)
          simp [*] at *
  | e_ifFalse _ _ _ _ _ _ _ ih =>
      cases he₂ with
      | e_ifTrue => -- b evaluates to true in 2nd execution (contradiction)
          simp [*] at *
      | e_ifFalse => -- b evaluates to false in 2nd execution
        apply ih; assumption
  | e_whileFalse =>
      cases he₂ with
      | e_whileFalse => rfl
      | e_whileTrue => simp [*] at *
  | e_whileTrue b c' st' st'' st''' hb _ _ ihc' ihloop =>
      cases he₂ with
      | e_whileFalse => simp [*] at *
      | e_whileTrue _ _ _ st_'' =>
          apply ihloop
          have h : st'' = st_'' := by apply ihc'; assumption
          simp [*]

/-
## Reasoning about Imp programs
-/

theorem plus2_spec n st st' :
    lookup' st x = n
    → (st =[ <[plus2]> ]=> st')
    → lookup' st' x = n + 2 := by
  intro hx heval
  cases heval  -- e_asgn
  simp [*] at *; omega

/-
We now can define when behavioral equivalence for commands.
Two commands are behaviorally equivalent if, for any given starting state, they either (1) both diverge or (2) both terminate in the same final state.
A compact way to express this is "if the first one terminates in a particular state then so does the second, and vice versa."
-/

def cequiv (c₁ c₂ : Com) : Prop :=
  ∀ st st' : State, (st =[<[c₁]>]=> st') ↔ (st =[<[c₂]>]=> st')

/-
We can also define an asymmetric variant of this relation: We say that c₁ _refines_ c₂ if they produce the same final states when c₁ terminates (but c₁ may not terminate in some cases where c₂ does).
-/

def refines (c₁ c₂ : Com) : Prop :=
  ∀ st st' : State, (st =[<[c₁]>]=> st') → (st =[<[c₂]>]=> st')

/-
For examples of command equivalence, let's start by looking at a trivial program equivalence involving `skip`.
-/

theorem skip_left c : cequiv <{ skip; <[c]> }> c := by
  intro st st'
  constructor
  . intro h
    cases h with
    | e_seq _ _ st₁' st₁'' st₁''' hc₁ hc₂ =>
        cases hc₁; assumption
  . intro h
    constructor
    . constructor
    . assumption

/-
Similarly, here is a simple equivalence that optimizes `if` commands.
-/

theorem if_true_simple c₁ c₂
    : cequiv <{if true then <[c₁]> else <[c₂]> end}> c₁ := by
  intro st st'
  constructor
  . intro h
    cases h <;> simp [*] at *
  . intro h
    constructor
    . simp  -- true
    . assumption

/-
Of course, no (human) programmer would write a conditional whose condition is literally `True`.
But they might write one whose condition is _equivalent_ to `True`:
  Theorem: If `b` is equivalent to `True`, then `if b then c₁ else c₂` is equivalent to `c₁`.
-/

theorem if_true b c₁ c₂
    : bequiv b <{true}> → cequiv <{if <[b]> then <[c₁]> else <[c₂]> end}> c₁ := by
  intro hb st st'
  constructor
  . intro h
    cases h with
    | e_ifTrue => assumption
    | e_ifFalse => unfold bequiv at hb; simp [*] at *
  . intro h
    apply e_ifTrue <;> unfold bequiv at hb
    . simp [*]
    . assumption

/-
exercise (3-star)
We can swap the branches of an `if` if we also negate its condition.
-/

theorem swap_if_branches b c₁ c₂
    : cequiv
        <{if <[b]> then <[c₁]> else <[c₂]> end}>
        <{if !<[b]> then <[c₂]> else <[c₁]> end}> := by
  sorry

/-
For `while` loops, we start with the easier theorem of the two.
-/

/-
exercise (2-star)
Prove that `while` loop with guard equivalent to false is equivalent to `skip`.
-/

theorem while_false b c : bequiv b <{false}> →
    cequiv <{while <[b]> do <[c]> end}> <{skip}> := by
  sorry

/-
## references
* [Software Foundations, Volume 1 Logical Foundations: Simple Imperative Programs](https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html)
* [Software Foundations, Volume 2 Programming Language Foundations: Program Equivalence](https://softwarefoundations.cis.upenn.edu/plf-current/Equiv.html)
-/
