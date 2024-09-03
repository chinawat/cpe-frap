-- insertion sort exercises

import Frap.Sort

open Permutation
open Sorted

/-
exercise (2-star)
Prove the following fact by using only constructors in the `Permutation` relation.
-/
example : Permutation [1, 2, 3] [2, 3, 1] := by
  sorry

/-
exercise (3-star)
Prove that insertion maintains sortedness.
-/

theorem insert_sorted' a l : Sorted l → Sorted (insert a l) := by
  intro S
  induction S with simp at *
  | _ => sorry

/-
exercise (2-star)
Using `insert_sorted`, prove the insertion sort makes a list sorted.
-/

theorem sort_sorted' l : Sorted (sort l) := by
  sorry

/-
exercise (3-star)
Prove that `sort` is a permutation, using `insert_perm`.
-/

theorem sort_perm' l : Permutation l (sort l) := by
  sorry

/-
exercise (1-star)
Finish the proof of correctness!
-/

theorem insertion_sort_correct' : is_a_sorting_algorithm sort := by
  sorry
