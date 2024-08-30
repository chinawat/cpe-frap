-- type systems exercises

import Frap.Types

namespace TM
open Tm
-- open BValue
-- open NValue
open Step
open Ty
open HasType

/-
exercise (3-star)
Complete the formal proof of the `progress` property.
-/
theorem progress'' t T
    : HasType t T → value t ∨ ∃ t', Step t t' := by
  intro ht
  induction ht with
  | t_if t₁ t₂ t₃ T =>
    rename_i ih₁ ih₂ ih₃
    right; cases ih₁
    . -- t₁ is a value
      have h : BValue t₁ := by
        apply bool_canonical <;> assumption
      cases h
      . exists t₂; apply st_ifTrue
      . exists t₃; apply st_ifFalse
    . -- t₁ can take a step
      rename_i h
      obtain ⟨t₁', h₁⟩ := h
      exists (ite t₁' t₂ t₃)
      apply st_if; exact h₁
  | _ => sorry

/-
exercise (2-star)
Complete the formal proof of the `preservation` property.
-/
theorem preservation'' t t' T
    : HasType t T → Step t t' → HasType t' T := by
  intro hT hE
  induction hT generalizing t' with
  | t_if =>
    rename_i ih₁ _ _
    cases hE
    . -- st_ifTrue
      assumption
    . -- st_ifFalse
      assumption
    . -- st_if
      apply t_if <;> try assumption
      apply ih₁; assumption
  | _ => sorry

/-
exercise (3-star)
Having seen the subject reduction property, one might wonder whether the opposite property—subject _expansion_—also holds.
That is, is it always the case that, if `t ~~> t'` and `⊢ t' ∈ T`, then `⊢ t ∈ T`?
If so, prove it.
If not, give a counterexample.
-/
theorem subject_expansion
    : (∀ t t' T, Step t t' ∧ HasType t' T → HasType t T)
      ∨ ¬ (∀ t t' T, Step t t' ∧ HasType t' T → HasType t T) := by
  sorry
