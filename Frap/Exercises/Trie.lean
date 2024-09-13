-- trie exercises

import Frap.Trie

open Trie

/-
exercise (1-star)
-/
theorem look_leaf' α (d : α) j : look d j leaf = d := by
  sorry

/-
exercise (2-star)
This is a rather simple induction.
-/
theorem look_ins_same' {α} d k (v : α) : ∀ t, look d k (ins d k v t) = v := by
  sorry

/-
exercise (2-star)
Use `pos2nat2pos` and `nat2pos2nat` lemmas to prove the following injection properties.
-/

theorem pos2nat_injective' p q : pos2nat p = pos2nat q → p = q := by
  sorry

theorem nat2pos_injective' i j : nat2pos i = nat2pos j → i = j := by
  sorry
