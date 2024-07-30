-- Hoare logic 2 exercises

import Frap.Hoare2

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
exercise (2-star)
Prove the theorem below using `hoare_if`.
-/

theorem if_minus_plus :
    -- { True }
    {* fun _ => True *}
      <{if x <= y then z := y - x else y := x + z end}>
    -- { y = x + z }
    {* fun st => st y = st x + st z *} := by
  sorry

/-
exercise (2-star)
Fill in valid decorations for the following program:

```
  { True }
    if x <= y then
                    { **FILL IN HERE** } ->>
                    { **FILL IN HERE** }
      z := y - x
                    { **FILL IN HERE** }
    else
                    { **FILL IN HERE** } ->>
                    { **FILL IN HERE** }
      y := x + z
                    { **FILL IN HERE** }
    end
  { y = x + z }
```

Briefly justify each use of `->>`.

**FILL IN HERE**
-/

/-
exercise (2-star)
Here is a skeleton of the formal decorated version of the `if_minus_plus` program above.
Replace all occurrences of `FILL IN HERE` with appropriate assertions and fill in the proof (which should be just as straightforward as in the examples from lecture).
-/
def if_minus_plus_dec : Decorated := decorated
  (fun _ => True) $
    dc_if <{x <= y}>
      (fun st => /-**FILL IN HERE**-/ True)
      (dc_pre (fun st => /-**FILL IN HERE**-/ True) $
    dc_asgn z <{y - x}>
      (fun st => /-**FILL IN HERE**-/ True))

      (fun st => /-**FILL IN HERE**-/ True)
      (dc_pre (fun st => /-**FILL IN HERE**-/ True) $
    dc_asgn y <{x + z}>
      (fun st => /-**FILL IN HERE**-/ True))
  (fun st => st y = st x + st z)

theorem if_minus_plus_correct : outer_triple_valid if_minus_plus_dec := by
  sorry
