-- loop invariant exercises

import Frap.LoopInv

namespace Imp
namespace Hoare
open AExp
open BExp
open Com
open CEval
open DCom
open Decorated
attribute [local simp]
  aeval beval aequiv bequiv cequiv update x y z

/-
exercise (3-star): minimum

Fill in decorations for the following program and prove them correct.
```
  { True } ->>
  { **FILL IN HERE** }
    x := a;
                                { **FILL IN HERE** }
    y := b;
                                { **FILL IN HERE** }
    z := 0;
                                { **FILL IN HERE** }
    while x != 0 && y != 0 do
                                { **FILL IN HERE** } ->>
                                { **FILL IN HERE** }
      x := x - 1
                                { **FILL IN HERE** }
      y := y - 1
                                { **FILL IN HERE** }
      z := z + 1
                                { **FILL IN HERE** }
    end
  { **FILL IN HERE** } ->>
  { z = min a b }
```
-/

def minimum_dec (a b : Nat) : Decorated := decorated
  (fun _ => True) $
    dc_pre (fun st => /-**FILL IN HERE**-/ True) $
    dc_seq (dc_asgn x (a_num a)
      (fun st => /-**FILL IN HERE**-/ True)) $
    dc_seq (dc_asgn y (a_num b)
      (fun st => /-**FILL IN HERE**-/ True)) $
    dc_seq (dc_asgn z <{0}>
      (fun st => /-**FILL IN HERE**-/ True)) $
    dc_post (dc_while <{x != 0 && y != 0}>
        (fun st => /-**FILL IN HERE**-/ True)
        (dc_pre (fun st => /-**FILL IN HERE**-/ True) $
      dc_seq (dc_asgn x <{x - 1}> (fun st => /-**FILL IN HERE**-/ True)) $
      dc_seq (dc_asgn y <{y - 1}> (fun st => /-**FILL IN HERE**-/ True)) $
      dc_asgn z <{z + 1}> (fun st => /-**FILL IN HERE**-/ True)
      ) (fun st => /-**FILL IN HERE**-/ True))
  (fun st => st z = min a b)

theorem minimum_correct a b : outer_triple_valid (minimum_dec a b) := by
  sorry

/-
exercise (2-star)
Show that the precondition in the rule `hoare_asgn` is in fact the weakest precondition.
-/

theorem hoare_asgn_weakest Q x a
    : is_wp (fun st => Q (st[x ↦ aeval st a])) <{x := <[a]>}> Q := by
  sorry
