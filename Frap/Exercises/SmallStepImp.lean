-- small-step operational semantics for Imp exercises

import Frap.SmallStepImp

namespace CImp
open Imp
open AStep
open BStep
open CStep
open Multi

/-
exercise (3-star)
-/

theorem par_body_n__Sn' n st
    : st x = n ∧ st y = 0
      → Multi CStep (par_loop, st) (par_loop, x !-> n + 1; st) := by
  sorry

/-
exercise (3-star)
-/

theorem par_body_n' n st
    : st x = 0 ∧ st y = 0
      → ∃ st', Multi CStep (par_loop, st) (par_loop, st')
          ∧ st' x = n ∧ st' y = 0 := by
  sorry
