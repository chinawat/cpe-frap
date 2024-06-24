-- first-order logic exercises

/-
Consider the "barber paradox," that is, the claim that in a certain town there is a (male) barber that shaves all and only the men who do not shave themselves
Prove that this universal statement is a contradiction:
-/
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

theorem barber_paradox : ¬(∀ x : men, shaves barber x ↔ ¬ shaves x x) := by
  sorry

/-
The barber is one who shaves everyone that does not shave oneself.
Please use your proof above to guide your answer to this question: does the barber shave himself?

**TYPE YOUR ANSWER HERE**
-/

variable (α : Type) (p : α → Prop)

/-
Prove that a negation of an existential statement is equivalient to a universal statement of the negation.
-/
theorem existential_negation : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  sorry

/-
Prove that if there is an element falsifying a predicate, then not all elements satisfy the predicate.
Note: the converse doesn't hold in constructive logic.
-/
theorem exists_not_not_forall : (∃ x, ¬ p x) → (¬ ∀ x, p x) := by
  sorry
