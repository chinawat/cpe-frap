-- imperative language exercises

import Frap.Imp

/-
Here, we will work with the original version of arithmetic and boolean expressions (before adding identifiers).
-/

namespace Hidden.AExp

open AExp
open BExp

/-
exercise (1-star)
Prove that the combination of the two optimizations involving zero still preserves the meaning of arithmetic expressions.
You may use results from the lecture without proofs.
-/

def optimize_plus_with_0 (a : AExp) : AExp :=
  optimize_plus0 (optimize_0plus a)

theorem optimize_plus_with_0_sound (a : AExp)
    : aeval (optimize_plus_with_0 a) = aeval a := by
  sorry

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
exercise (3-star)
Write a relation `BEvalR` in the same style as `AEvalR`, and prove that it is equivalent to `beval`.
-/

inductive BEvalR : BExp → Bool → Prop :=
  /- **fill in here** -/

infix:90 " ==>b " => BEvalR

open BEvalR

theorem beval_iff_BEvalR b v
    : b ==>b v ↔ beval b = v := by
  sorry

end Hidden.AExp
