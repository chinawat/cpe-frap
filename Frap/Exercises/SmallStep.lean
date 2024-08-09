-- small-step semantics exercises

import Frap.SmallStep

namespace Toy
open Tm

/-
`Value` is a syntactic concept (it is defined by looking at the way a term is written), while `normal_form` is a semantic one (it is defined by looking at how the term steps).

It is not obvious that these concepts should characterize the same set of terms!

Indeed, we could easily have written the definitions (incorrectly) so that they would _not_ coincide.
-/

/-
exercise (3-star)
We might, for example, define `Value` so that it includes some terms that are not finished reducing.
-/

namespace Temp1

inductive Value : Tm → Prop :=
  | v_const n : Value (c n)
  | v_funny t₁ n : Value (p t₁ (c n))  /- ←!!! -/

inductive Step : Tm → Tm → Prop :=
  | st_plusConstConst n₁ n₂ : Step (p (c n₁) (c n₂)) (c (n₁ + n₂))
  | st_plus1 t₁ t₁' t₂ : Step t₁ t₁' → Step (p t₁ t₂) (p t₁' t₂)
  | st_plus2 v₁ t₂ t₂' : Value v₁ → Step t₂ t₂' → Step (p v₁ t₂) (p v₁ t₂')

open Value
open Step

example : ∃v, Value v ∧ ¬ normal_form Step v := by
  sorry

end Temp1

/-
exercise (2-star)
Or we might (again, wrongly) define `Step` so that it permits something designated as a value to reduce further.
-/

namespace Temp2

inductive Value : Tm → Prop :=
  | v_const n : Value (c n)

inductive Step : Tm → Tm → Prop :=
  | st_funny n : Step (c n) (p (c n) (c 0))  /- ←!!! -/
  | st_plusConstConst n₁ n₂ : Step (p (c n₁) (c n₂)) (c (n₁ + n₂))
  | st_plus1 t₁ t₁' t₂ : Step t₁ t₁' → Step (p t₁ t₂) (p t₁' t₂)
  | st_plus2 v₁ t₂ t₂' : Value v₁ → Step t₂ t₂' → Step (p v₁ t₂) (p v₁ t₂')

open Value
open Step

example : ∃v, Value v ∧ ¬ normal_form Step v := by
  sorry

end Temp2

/-
exercise (3-star)
Finally, we might define `Value` and `Step` so that there is some term that is not a value but that cannot take a step in the `Step` relation.
Such terms are said to be _stuck_.
In this case, this is caused by a mistake in the semantics, but we will also see situations where, even in a correct language definition, it makes sense to allow some terms to be stuck.
-/

namespace Temp3

inductive Value : Tm → Prop :=
  | v_const n : Value (c n)

inductive Step : Tm → Tm → Prop :=
  | st_plusConstConst n₁ n₂ : Step (p (c n₁) (c n₂)) (c (n₁ + n₂))
  | st_plus1 t₁ t₁' t₂ : Step t₁ t₁' → Step (p t₁ t₂) (p t₁' t₂)
  /- note that `st_plus2` is missing -/

open Value
open Step

example : ∃v, ¬ Value v ∧ normal_form Step v := by
  sorry

end Temp3
