import Lean.Data.HashMap

/-
## Arithmetic and boolean expressions

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

#eval beval (b_le (a_num 7) (a_num 5))

/-
### Optimization
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
exercise (3-star)
Since the `optimize_0plus` transformation doesn't change the value of `AExp`s, we should be able to apply it to all the `AExp`s that appear in a `BExp` without changing the `BExp`'s value.
Write a function that performs this transformation on `BExp`s and prove it is sound.
Use tactic combinators to make the proof as short and elegant as possible.
-/

def optimize_0plus_b (b : BExp) : BExp :=
  sorry

theorem optimize_0plus_b_sound (b : BExp)
    : beval (optimize_0plus_b b) = beval b := by
  sorry

/-
## Evaluation as a relation
-/

inductive AEvalR : AExp → Nat → Prop :=
  | e_a_num (n : Nat) : AEvalR (a_num n) n
  | e_a_plus (a₁ a₂ : AExp) (n₁ n₂ : Nat) :
      AEvalR a₁ n₁ → AEvalR a₂ n₂ → AEvalR (a_plus a₁ a₂) (n₁ + n₂)
  | e_a_minus (a₁ a₂ : AExp) (n₁ n₂ : Nat) :
      AEvalR a₁ n₁ → AEvalR a₂ n₂ → AEvalR (a_minus a₁ a₂) (n₁ - n₂)
  | e_a_mult (a₁ a₂ : AExp) (n₁ n₂ : Nat) :
      AEvalR a₁ n₁ → AEvalR a₂ n₂ → AEvalR (a_mult a₁ a₂) (n₁ * n₂)

infix:90 " ==> " => AEvalR

/-
It is straightforward to prove that the relational and functional definitions of evaluation agree.
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

theorem aeval_iff_AEvalR (a : AExp) (n : Nat)
    : a ==> n ↔ aeval a = n := by
  constructor
  . intro h
    induction h <;> simp [aeval, *]
  . intro h
    induction a generalizing n with repeat simp [aeval, *] at *
    | a_num n' => constructor
    | _ => rw [← h]; constructor <;> assumption

/-
exercise (3-star)
Write a relation `BEvalR` in the same style as `AEvalR`, and prove that it is equivalent to `beval`.
-/

inductive BEvalR : BExp → Bool → Prop :=
  /- **fill in here** -/

infix:90 " ==>b " => BEvalR

theorem beval_iff_BEvalR b bv
    : b ==>b bv ↔ beval v = bv := by
  sorry

end Hidden.AExp

/-
### Computational vs relational definitions
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

/-
## Expressions with variables
-/

inductive AExp where
  | a_num : Nat → AExp
  | a_id : String → AExp  -- new
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

declare_syntax_cat expr

syntax num : expr
syntax str : expr
syntax:60 expr:60 "+" expr:61 : expr
syntax:60 expr:60 "-" expr:61 : expr
syntax:70 expr:70 "*" expr:71 : expr
syntax:50 expr:50 "=" expr:50 : expr
syntax:50 expr:50 "!=" expr:50 : expr
syntax:50 expr:50 "<=" expr:50 : expr
syntax:40 "!" expr:40 : expr
syntax:30 expr:30 "&&" expr:31 : expr
syntax:30 expr:30 "||" expr:31 : expr
syntax "True" : expr
syntax "False" : expr
syntax "(" expr ")" : expr

syntax "<{" expr "}>" : term
macro_rules
  | `(<{$n:num}>) => `(a_num $n)
  | `(<{$s:str}>) => `(a_id $s)
  | `(<{$x + $y}>) => `(a_plus <{$x}> <{$y}>)
  | `(<{$x - $y}>) => `(a_minus <{$x}> <{$y}>)
  | `(<{$x * $y}>) => `(a_mult <{$x}> <{$y}>)
  | `(<{True}>) => `(b_true)
  | `(<{False}>) => `(b_false)
  | `(<{$x = $y}>) => `(b_eq <{$x}> <{$y}>)
  | `(<{$x != $y}>) => `(b_neq <{$x}> <{$y}>)
  | `(<{$x <= $y}>) => `(b_le <{$x}> <{$y}>)
  | `(<{!$x}>) => `(b_not <{$x}>)
  | `(<{$x && $y}>) => `(b_and <{$x}> <{$y}>)
  | `(<{$x || $y}>) => `(b_or <{$x}> <{$y}>)

open Lean
open Lean.HashMap

abbrev State := HashMap String Nat

def aeval (st : State) (a : AExp) : Nat :=
  match a with
  | a_num n => n
  | a_id x => find! st x
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

theorem map_lookup_insert (x : String) (v : Nat)
    : find! (insert empty x v) x = v := by
  sorry

example : aeval (insert empty x 5)
    (a_plus (a_num 3) (a_mult (a_id x) (a_num 2)))
    = 13 := by
  simp [aeval, map_lookup_insert]

/-
## Behavioral equivalence
-/

def aequiv (a₁ a₂ : AExp) : Prop :=
  ∀ (st : State), aeval st a₁ = aeval st a₂

def bequiv (b₁ b₂ : BExp) : Prop :=
  ∀ (st : State), beval st b₁ = beval st b₂

theorem aequiv_example
    : aequiv <{"x" - "x"}> <{0}> := by
  intro st
  simp [aeval]

theorem bequiv_example
    : bequiv <{"x" - "x" = 0}> <{True}> := by
  intro st
  simp [beval, aeval]

/-
## Commands
-/

inductive Com :=
  | c_skip : Com
  | c_asgn : String → AExp → Com
  | c_seq : Com → Com → Com
  | c_if : BExp → Com → Com → Com
  | c_while : BExp → Com → Com

/-
## references
* [](https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html)
* [](https://raw.githubusercontent.com/blanchette/logical_verification_2023/main/hitchhikers_guide.pdf)
-/
