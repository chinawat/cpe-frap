import Frap.Equiv

namespace Imp
open Com

/-
exercise (2-star)
Prove that adding a `skip` after a command results in an equivalent program.
-/

theorem skip_right c : cequiv <{ <[c]>; skip }> c := by
  sorry

/-
exercise (3-star)
Consider the following predicate.
This predicate yields `true` just on programs that have no while loops.
-/

def no_whiles (c : Com) : Bool :=
  match c with
  | c_skip => true
  | c_asgn _ _ => true
  | c_seq c₁ c₂ => and (no_whiles c₁) (no_whiles c₂)
  | c_if _ c₁ c₂ => and (no_whiles c₁) (no_whiles c₂)
  | c_while _ _ => false

/-
Using `inductive`, write a property `No_whilesR` such that `No_whilesR c` is provable exactly when `c` is a program with no while loops.
-/

inductive No_whilesR : Com → Prop :=
  /- **fill in here** -/

/-
Then, prove its equivalence with `no_whiles`.
-/

theorem no_whiles_eqv c : no_whiles c = true ↔ No_whilesR c := by
  sorry
