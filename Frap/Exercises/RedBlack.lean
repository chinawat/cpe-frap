-- red-black trees exercises

import Frap.RedBlack

namespace Tree

/-
exercise (2-star)
Prove that `insert` preserves `BST.
You do not need induction.
You might need to use `unfold` to unfold the definition of a function.
-/
theorem insert_BST {α : Type u} (t : Tree α) k vk
    : BST t → BST (insert k vk t) := by
  sorry

/-
exercise (2-star)
Verify the second and third equations for `insert`.
You may use unproven theorems in the imported file, though you are encouraged to do so.
You might need to prove a lemma.
-/

theorem lookup_insert_eq {α : Type u} (d : α) t k vk
    : BST t → lookup d k (insert k vk t) = vk := by
  sorry

theorem lookup_insert_neq {α : Type u} (d : α) t k vk
    : BST t → k ≠ k' → lookup d k' (insert k vk t) = lookup d k' t := by
  sorry

end Tree
