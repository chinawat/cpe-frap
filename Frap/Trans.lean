import Frap.Equiv
import Frap.Exercises.Equiv

namespace Imp
open AExp
open BExp
open Com
open CEval
attribute [local simp]
  aeval beval aequiv bequiv cequiv

/-
Next. we want to prove that the `loop` program does not terminate.
That is, starting from any state `st`, evaluating the `loop` program doesn't result in any state `st'`.

First, let's sketch how the proof would go.
We'll prove by contradiction.
Suppose `loop` terminates.
We'll do induction on the evidence that `loop` terminates, i.e., on a derivation of `CEval loop st st'`.
-/

example st st' : ¬(st =[ <[loop]> ]=> st') := by
  intro contra
  -- induction contra
  sorry

/-
Here, we see that the `induction` tactic doesn't work (with error "index in target's type is not a variable (consider using the `cases` tactic instead)").
This is because the `loop` program in the evidence is a fixed program, and so it can't be instantiated to various forms of programs in different cases of `CEval`.

Let's try the `cases` tactic as suggested.
-/

example st st' : ¬(st =[ <[loop]> ]=> st') := by
  intro contra
  cases contra with
  | e_whileFalse => simp at *  -- contradiction
  | e_whileTrue =>
    -- Here, we need to derive a contradiction from the fact that
    -- evaluating the body of the loop and the remaining iterations of the loop
    -- doesn't terminate.
    -- We seem to need the induction hypothesis that the remaining iterations
    -- don't terminate either, but we don't have that here.
    sorry

/-
It looks like we do need the induction hypothesis for the proof to go through.
To make induction work, we'll need to generalize constants used in the induction hypothesis (`loop` in this case).
Most cases, however, result immediately in a contradiction, as the form of the command doesn't match the structure of `loop`.
The interesting cases are when the command is indeed a `while` loop.

We can generalize an expression with the `generalize` tactic.
We give this equality a name so it becomes a hypothesis we can use to discriminate against impossible cases, i.e., other command constructs.
-/

theorem loop_never_stops st st' : ¬(st =[ <[loop]> ]=> st') := by
  generalize heq : loop = com
  unfold loop at heq
  intro contra
  induction contra with simp at *
  | e_whileFalse _ _ _ hbf =>
    obtain ⟨hbt, _⟩ := heq
    rw [← hbt] at hbf
    simp at *
  | e_whileTrue _ _ _ _ _ _ _ _ ihc ihloop =>
    -- break down the assumption that guard is `true` and body is `skip`
    obtain ⟨⟩ := heq
    -- apply induction hypothesis that remaining iterations don't terminate
    apply ihloop <;> assumption

/-
To avoid writing down many wildcards only to name the last hypothesis, we can use the `rename_i` tactic, which will rename the last i hypotheses to the specified names.
-/

example : ¬(st =[ <[loop]> ]=> st') := by
  generalize heq : loop = com
  unfold loop at heq
  intro contra
  induction contra with simp at *
  | e_whileFalse =>
    rename_i hbf
    obtain ⟨hbt, _⟩ := heq
    rw [← hbt] at hbf
    simp at *
  | e_whileTrue =>
    rename_i ihloop
    -- apply induction hypothesis that remaining iterations don't terminate
    -- `simp [*]` does the job of breaking down conjunctions
    -- in the hypothesis for us
    apply ihloop <;> simp [*]

/-
Next, we prove that `while` loops whose guards are equivalent to `true` never terminate.
-/

theorem while_true_nonterm b c st st' :
    bequiv b <{true}> → ¬(st =[while <[b]> do <[c]> end]=> st') := by
  intro hb contra
  generalize heq : <{while <[b]> do <[c]> end}> = com at contra
  induction contra with simp at *
  | e_whileFalse =>
    rename_i st'' hbf
    have h : beval st'' b = true := by apply hb st''
    simp [*] at *
  | e_whileTrue =>
    rename_i ihwhile
    apply ihwhile <;> simp [*]

/-
exercise (2-star)
Hint: You'll want to use `while_true_nonterm` here.
-/

theorem while_true b c :
    bequiv b <{true}> → cequiv <{while <[b]> do <[c]> end}> loop := by
  sorry

theorem seq_assoc c₁ c₂ c₃
    : cequiv <{(<[c₁]>; <[c₂]>); <[c₃]>}> <{<[c₁]>; (<[c₂]>; <[c₃]>)}> := by
  intro st st'
  constructor
  . intro h; cases h
    rename_i h12 h3; cases h12
    apply e_seq
    . assumption
    . apply e_seq
      . assumption
      . assumption
  . intro h; cases h
    rename_i h1 h23; cases h23
    apply e_seq
    . apply e_seq
      . assumption
      . assumption
    . assumption

/-
## Properties of behavioral equivalence

We next consider some fundamental properties of program equivalence.

### Behavioral equivalence is an equivalence

First, let's verify that the equivalences on `AExp`s, `BExp`s, and `Com`s really are equivalences -- i.e., that they are reflexive, symmetric, and transitive.
The proofs are all easy.
-/

theorem refl_aequiv a : aequiv a a := by simp

theorem sym_aequiv a₁ a₂ : aequiv a₁ a₂ → aequiv a₂ a₁ := by
  intro h st; rw [h]

theorem trans_aequiv a₁ a₂ a₃ : aequiv a₁ a₂ → aequiv a₂ a₃ → aequiv a₁ a₃ := by
  intro h1 h2 st; rw [h1, h2]

theorem refl_bequiv b : bequiv b b := by simp

theorem sym_bequiv b₁ b₂ : bequiv b₁ b₂ → bequiv b₂ b₁ := by
  intro h st; rw [h]

theorem trans_bequiv b₁ b₂ b₃ : bequiv b₁ b₂ → bequiv b₂ b₃ → bequiv b₁ b₃ := by
  intro h1 h2 st; rw [h1, h2]

theorem refl_cequiv c : cequiv c c := by simp

theorem sym_cequiv c₁ c₂ : cequiv c₁ c₂ → cequiv c₂ c₁ := by
  intro h st st'; rw [h]

theorem trans_cequiv c₁ c₂ c₃ : cequiv c₁ c₂ → cequiv c₂ c₃ → cequiv c₁ c₃ := by
  intro h1 h2 st st'; rw [h1, h2]

/-
### Behavioral equivalence is a congruence

Less obviously, behavioral equivalence is also a _congruence_.
That is, the equivalence of two subprograms implies the equivalence of the larger programs in which they are embedded.

We will see a concrete example of why these congruence properties are important in the following section (in the proof of `fold_constants_com_sound`), but the main idea is that they allow us to replace a small part of a large program with an equivalent small part and know that the whole large programs are equivalent _without_ doing an explicit proof about the parts that didn't change -- i.e., the "proof burden" of a small change to a large program is proportional to the size of the change, not the program!
-/

theorem c_asgn_congruence x a a'
    : aequiv a a' → cequiv <{x := <[a]>}> <{x := <[a']>}> := by
  intro ha st st'
  constructor
  . intro h; cases h
    apply e_asgn
    rw [← ha]
    assumption
  . intro h; cases h
    apply e_asgn
    rw [ha]
    assumption

/-
The congruence property for loops is a little more interesting, since it requires induction.
-/

theorem c_while_congruence b b' c c'
    : bequiv b b' → cequiv c c'
      → cequiv <{while <[b]> do <[c]> end}> <{while <[b']> do <[c']> end}> := by
  /-
  we will prove one direction in a "have"
  in order to reuse it for the converse
  -/
  have H b b' c c' st st' : bequiv b b' → cequiv c c'
      → (st =[while <[b]> do <[c]> end]=> st')
      → (st =[while <[b']> do <[c']> end]=> st') := by
    generalize heq : <{while <[b]> do <[c]> end}> = com
    intro hb hc h
    induction h with simp [*] at *
    | e_whileFalse =>
      obtain ⟨hb', _⟩ := heq
      apply e_whileFalse
      rw [← hb, hb']; assumption
    | e_whileTrue =>
      obtain ⟨hb', hc'⟩ := heq
      apply e_whileTrue
      . rw [← hb, hb']; assumption
      . rw [← hc, hc']; assumption
      . assumption

  intro hb hc st st'
  constructor
  . apply H <;> assumption
  . apply H
    . apply sym_bequiv; assumption
    . apply sym_cequiv; assumption

/-
exercise (3-star)
-/

theorem c_seq_congruence c₁ c₁' c₂ c₂'
    : cequiv c₁ c₁' → cequiv c₂ c₂' → cequiv (c_seq c₁ c₂) (c_seq c₁' c₂') := by
  sorry

/-
exercise (3-star)
-/

theorem c_if_congruence b b' c₁ c₁' c₂ c₂'
    : bequiv b b' → cequiv c₁ c₁' → cequiv c₂ c₂'
      → cequiv (c_if b c₁ c₂) (c_if b' c₁' c₂') := by
  sorry

/-
For example, here are two equivalent programs and a proof of their equivalence using these congruence theorems...
-/

example : cequiv
    /- program 1 -/
    <{ X := 0;
       if X = 0 then Y := 0
       else Y := 42 end }>
    /- program 2 -/
    <{ X := 0;
       if X = 0 then Y := X - X -- <--- Changed here
       else Y := 42 end }> := by
  apply c_seq_congruence
  . apply refl_cequiv
  . apply c_if_congruence
    . apply refl_bequiv
    . apply c_asgn_congruence; simp
    . apply refl_cequiv

/-
## Program transformations

A _program transformation_ is a function that takes a program as input and produces a modified program as output.
Compiler optimizations such as constant folding are a canonical example, but there are many others.

A program transformation is said to be _sound_ if it preserves the behavior of the original program.
-/

def atrans_sound (atrans : AExp → AExp) :=
  ∀ (a : AExp), aequiv a (atrans a)

def btrans_sound (btrans : BExp → BExp) :=
  ∀ (b : BExp), bequiv b (btrans b)

def ctrans_sound (ctrans : Com → Com) :=
  ∀ (c : Com), cequiv c (ctrans c)

/-
### Constant-folding transformation

An expression is _constant_ if it contains no variable references.

Constant folding is an optimization that finds constant expressions and replaces them by their values.
-/

def fold_constants_aexp (a : AExp) : AExp :=
  match a with
  | a_num _
  | a_id _
    => a
  | a_plus a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2) with
    | (a_num n1, a_num n2) => a_num (n1 + n2)
    | (a1', a2') => a_plus a1' a2'
  | a_minus a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2) with
    | (a_num n1, a_num n2) => a_num (n1 - n2)
    | (a1', a2') => a_minus a1' a2'
  | a_mult a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2) with
    | (a_num n1, a_num n2) => a_num (n1 * n2)
    | (a1', a2') => a_mult a1' a2'

example : fold_constants_aexp <{(1 + 2) * x}> = <{3 * x}> := by
  simp [fold_constants_aexp]

example :
    fold_constants_aexp <{x - ((0 * 6) + y)}>
    = <{x - (0 + y)}> := by
  simp [fold_constants_aexp]

/-
Not only can we lift `fold_constants_aexp` to `BExp`s (in the `b_eq`, `b_neq`, and `b_le` cases); we can also look for constant boolean expressions and evaluate them in-place as well.
-/

def fold_constants_bexp (b : BExp) : BExp :=
  match b with
  | b_true
  | b_false
    => b
  | b_eq a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2) with
    | (a_num n1, a_num n2) => if n1 == n2 then b_true else b_false
    | (a1', a2') => b_eq a1' a2'
  | b_neq a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2) with
    | (a_num n1, a_num n2) => if n1 != n2 then b_true else b_false
    | (a1', a2') => b_neq a1' a2'
  | b_le a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2) with
    | (a_num n1, a_num n2) => if n1 <= n2 then b_true else b_false
    | (a1', a2') => b_le a1' a2'
  | b_not b1 =>
    match fold_constants_bexp b1 with
    | b_true => b_false
    | b_false => b_true
    | b1' => b_not b1'
  | b_and b1 b2 =>
    match (fold_constants_bexp b1, fold_constants_bexp b2) with
    | (b_true, b_true) => b_true
    | (b_true, b_false) => b_false
    | (b_false, b_true) => b_false
    | (b_false, b_false) => b_false
    | (b1', b2') => b_and b1' b2'
  | b_or b1 b2 =>
    match (fold_constants_bexp b1, fold_constants_bexp b2) with
    | (b_true, b_true) => b_true
    | (b_true, b_false) => b_true
    | (b_false, b_true) => b_true
    | (b_false, b_false) => b_false
    | (b1', b2') => b_or b1' b2'

example : fold_constants_bexp <{true && !(false && true)}> = <{true}> := by
  simp [fold_constants_bexp]

example : fold_constants_bexp <{ (x = y) && (0 = (2 - (1 + 1))) }>
    = <{ (x = y) && true }> := by
  simp [fold_constants_aexp, fold_constants_bexp]

/-
To fold constants in a command, we apply the appropriate folding functions on all embedded expressions.
-/

def fold_constants_com (c : Com) : Com :=
  match c with
  | c_skip => c
  | c_asgn x a => c_asgn x (fold_constants_aexp a)
  | c_seq c1 c2 => c_seq (fold_constants_com c1) (fold_constants_com c2)
  | c_if b c1 c2 =>
    match fold_constants_bexp b with
    | b_true => fold_constants_com c1
    | b_false => fold_constants_com c2
    | b' => c_if b' (fold_constants_com c1) (fold_constants_com c2)
  | c_while b c1 =>
    match fold_constants_bexp b with
    | b_true => loop
    | b_false => c_skip
    | b' => c_while b' (fold_constants_com c1)

example : fold_constants_com
    -- original program
    <{ x := 4 + 5;
       y := x - 3;
       if (x - y) = (2 + 4) then skip
       else y := 0 end;
       if 0 <= (4 - (2 + 1)) then y := 0
       else skip end;
       while y = 0 do
         x := x + 1
       end }>
    = -- after constant folding
    <{ x := 9;
       y := x - 3;
       if (x - y) = 6 then skip
       else y := 0 end;
       y := 0;
       while y = 0 do
         x := x + 1
       end }> := by
  simp [fold_constants_aexp, fold_constants_bexp, fold_constants_com]

/-
### Soundness of constant folding

Now we need to show that what we've done is correct.

Here's the proof for arithmetic expressions:
-/

theorem fold_constants_aexp_sound : atrans_sound fold_constants_aexp := by
  intro a st; induction a with simp [fold_constants_aexp]
  | a_plus _ _ ih1 ih2 =>
    split
    . rename_i hm
      simp at hm
      obtain ⟨⟩ := hm
      simp [*]
    . rename_i hm
      simp at hm
      obtain ⟨⟩ := hm
      simp [*]
  | a_minus _ _ ih1 ih2 =>
    split
    . rename_i hm
      simp at hm
      obtain ⟨⟩ := hm
      simp [*]
    . rename_i hm
      simp at hm
      obtain ⟨⟩ := hm
      simp [*]
  | a_mult _ _ ih1 ih2 =>
    split
    . rename_i hm
      simp at hm
      obtain ⟨⟩ := hm
      simp [*]
    . rename_i hm
      simp at hm
      obtain ⟨⟩ := hm
      simp [*]

/-
We can shorten the proof above by using the `<;>` tactic combinator.
-/

example : atrans_sound fold_constants_aexp := by
  intro a st; induction a with simp [fold_constants_aexp]
  | a_plus _ _ ih1 ih2 =>
    split <;> (
      rename_i hm
      simp at hm
      obtain ⟨⟩ := hm
      simp [*]
    )
  | a_minus _ _ ih1 ih2 =>
    split <;> (
      rename_i hm
      simp at hm
      obtain ⟨⟩ := hm
      simp [*]
    )
  | a_mult _ _ ih1 ih2 =>
    split <;> (
      rename_i hm
      simp at hm
      obtain ⟨⟩ := hm
      simp [*]
    )

/-
But since each of the three cases about does the same thing, we can shorten further.
-/

example : atrans_sound fold_constants_aexp := by
  intro a st; induction a <;> simp [fold_constants_aexp] <;> (
    rename_i ih1 ih2
    split <;> (
      rename_i hm
      simp at hm
      obtain ⟨⟩ := hm
      simp [*]
    )
  )

/-
Here's the proof for boolean expressions:
-/

theorem fold_constants_bexp_sound : btrans_sound fold_constants_bexp := by
  intro b st; induction b with simp [fold_constants_bexp]
  | b_eq a1 a2 =>
    rw [fold_constants_aexp_sound a1, fold_constants_aexp_sound a2]
    split
    . rename_i hm
      simp at hm
      obtain ⟨⟩ := hm
      split <;> simp [*]
    . rename_i hm
      simp at hm
      obtain ⟨⟩ := hm
      simp [*]
  | b_neq a1 a2 =>
    rw [fold_constants_aexp_sound a1, fold_constants_aexp_sound a2]
    split
    . rename_i hm
      simp at hm
      obtain ⟨⟩ := hm
      split <;> simp [*]
    . rename_i hm
      simp at hm
      obtain ⟨⟩ := hm
      simp [*]
  | b_le a1 a2 =>
    rw [fold_constants_aexp_sound a1, fold_constants_aexp_sound a2]
    split
    . rename_i hm
      simp at hm
      obtain ⟨⟩ := hm
      split <;> simp [*]
    . rename_i hm
      simp at hm
      obtain ⟨⟩ := hm
      simp [*]
  | b_not =>
    split <;> simp [*]
  | b_and =>
    simp [*]
    split <;> (
      rename_i hm
      simp at hm
      obtain ⟨⟩ := hm
      simp [*]
    )
  | b_or =>
    simp [*]
    split <;> (
      rename_i hm
      simp at hm
      obtain ⟨⟩ := hm
      simp [*]
    )

/-
We see that after doing each split, we need to focus on the last hypothesis and simplify it for further use.
We can create a tactic for this purpose using a macro.
-/

/--
`split'` is a shorthand for
`split <;> (try rename_i heq; simp at heq; obtain ⟨⟩ := heq)`
-/
local macro "split'" : tactic =>
  `(tactic| split <;> (try rename_i heq; simp at heq; obtain ⟨⟩ := heq))

/-
Both the proofs for `AExp`s and `BExp`s can now be shortened significantly.
-/

example : atrans_sound fold_constants_aexp := by
  intro a st; induction a <;> simp [fold_constants_aexp] <;> split' <;> simp [*]

example : btrans_sound fold_constants_bexp := by
  intro b st; induction b with simp [fold_constants_bexp]
  | b_eq a1 a2 =>
    rw [fold_constants_aexp_sound a1, fold_constants_aexp_sound a2]
    split' <;> (try split) <;> simp [*]
  | b_neq a1 a2 =>
    rw [fold_constants_aexp_sound a1, fold_constants_aexp_sound a2]
    split' <;> (try split) <;> simp [*]
  | b_le a1 a2 =>
    rw [fold_constants_aexp_sound a1, fold_constants_aexp_sound a2]
    split' <;> (try split) <;> simp [*]
  | b_not =>
    split' <;> simp [*]
  | b_and =>
    split' <;> simp [*]
  | b_or =>
    split' <;> simp [*]

example : btrans_sound fold_constants_bexp := by
  intro b st; induction b <;> simp [fold_constants_bexp] <;>
  first
  | rename_i a1 a2  -- cases for arithmetic comparisons
    rw [fold_constants_aexp_sound a1, fold_constants_aexp_sound a2]
    split' <;> (try split) <;> simp [*]
  | split' <;> simp [*]

/-
Finally, here's the proof for commands:
-/

theorem fold_constants_com_sound : ctrans_sound fold_constants_com := by
  intro c; induction c with simp [fold_constants_com]
  | c_asgn =>
    apply c_asgn_congruence
    apply fold_constants_aexp_sound
  | c_seq =>
    apply c_seq_congruence <;> assumption
  | c_if b c₁ c₂ ih1 ih2 =>
    split
    . apply trans_cequiv _ c₁
      . apply if_true
        rename_i heq; rw [← heq]
        apply fold_constants_bexp_sound
      . assumption
    . apply trans_cequiv _ c₂
      . apply if_false
        rename_i heq; rw [← heq]
        apply fold_constants_bexp_sound
      . assumption
    . apply c_if_congruence
      . apply fold_constants_bexp_sound
      . assumption
      . assumption
  | c_while b c' ih =>
    split
    . apply while_true
      rename_i heq; rw [← heq]
      apply fold_constants_bexp_sound
    . apply while_false
      rename_i heq; rw [← heq]
      apply fold_constants_bexp_sound
    . apply c_while_congruence
      . apply fold_constants_bexp_sound
      . assumption

/-
## references
* [Software Foundations, Volume 2 Programming Language Foundations: Program Equivalence](https://softwarefoundations.cis.upenn.edu/plf-current/Equiv.html)
-/
