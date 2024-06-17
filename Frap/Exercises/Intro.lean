-- introduction exercises

-- write a proof for each fo the following proposition

theorem curry (p q r : Prop) : (p ∧ q → r) → (p → q → r) := by
  sorry

theorem uncurry (p q r : Prop) : (p → q → r) → (p ∧ q → r) := by
  sorry
