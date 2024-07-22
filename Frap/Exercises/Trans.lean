-- program transformations exercises

import Frap.Trans

namespace Hidden.AExp
open AExp

/-
Recall the definition of `optimize_0plus` from the `Imp` lecture.
Note that this function is defined over the old version of `AExp`s, without states.
-/

-- def optimize_0plus (a : AExp) : AExp :=
--   match a with
--   | a_num _ => a
--   | a_plus (a_num 0) a₂ => optimize_0plus a₂
--   | a_plus a₁ a₂ => a_plus (optimize_0plus a₁) (optimize_0plus a₂)
--   | a_minus a₁ a₂ => a_minus (optimize_0plus a₁) (optimize_0plus a₂)
--   | a_mult a₁ a₂ => a_mult (optimize_0plus a₁) (optimize_0plus a₂)

end Hidden.AExp

namespace Imp
open AExp
open BExp
open Com
open CEval
attribute [local simp]
  aeval beval aequiv bequiv cequiv

local macro "split'" : tactic =>
  `(tactic| split <;> (try rename_i heq; simp at heq; obtain ⟨⟩ := heq))

/-
Write a new version of this function that deals with variables (by leaving them along), plus analogous ones for `BExp`s and commands.
-/

def optimize_0plus_aexp (a : AExp) : AExp :=
  sorry

def optimize_0plus_bexp (b : BExp) : BExp :=
  sorry

def optimize_0plus_com (c : Com) : Com :=
  sorry

/-
First, make sure that your optimization works with this example.
-/

example :
    optimize_0plus_com <{ while x != 0 do x := 0 + x - 1 end }>
    = <{ while x != 0 do x := x - 1 end }> := by
  sorry

/-
Prove that these three functions are sound, as we did or `fold_constants_×`.
Make sure you use the congruence lemmas in the proof of `optimize_0plus_com`; otherwise, it will be _long_!
-/

theorem optimize_0plus_aexp_sound : atrans_sound optimize_0plus_aexp := by
  sorry

theorem optimize_0plus_bexp_sound : btrans_sound optimize_0plus_bexp := by
  sorry

theorem optimize_0plus_com_sound : ctrans_sound optimize_0plus_com := by
  sorry

/-
Finally, let's define a compound optimizer on commands that first folds constatns (using `fold_constants_com`) and then eliminates `0 + n` terms (using `optimize_0plus_com`).
-/

def optimizer (c : Com) := optimize_0plus_com (fold_constants_com c)

/-
Prove that this optimizer is sound.
Hint: Use `trans_cequiv`.
-/

theorem optimizer_sound: ctrans_sound optimizer := by
  sorry
