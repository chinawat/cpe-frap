-- linear logic exercises

import Frap.LinearLogic

open LinearTerm
open Permutation
open ValidLinearJudgment

theorem tensor_dist_plus_r' a b c : [] ⊩ (a ⊕ b) ⊗ c ≣ (a ⊗ c) ⊕ (b ⊗ c) := by
  sorry

theorem linear_curry' a b c : [(a ⊗ b) ⊸ c] ⊩ a ⊸ b ⊸ c := by
  sorry

theorem unit_lolli_ident_l' a : [] ⊩ l_unit ⊸ a ≣ a := by
  sorry

/-
Prove that tensor, with, and plus are commutative.
-/

theorem tensor_comm a b : [] ⊩ a ⊗ b ≣ b ⊗ a := by
  have h a b : [] ⊩ a ⊗ b ⊸ b ⊗ a := by
    sorry
  apply vl_with_i
  . apply h a b
  . apply h b a

theorem with_comm a b : [] ⊩ a & b ≣ b & a := by
  sorry

theorem plus_comm a b : [] ⊩ a ⊕ b ≣ b ⊕ a := by
  sorry
