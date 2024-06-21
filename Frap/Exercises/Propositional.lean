-- propositional logic exercises

-- write a proof for each fo the following proposition

theorem and_distributes_over_or (p q r : Prop) :
    p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  sorry

theorem or_distributes_over_and_l (p q r : Prop) :
    p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  sorry

theorem or_distributes_over_and_r (p q r : Prop) :
    (p ∧ q) ∨ r ↔ (p ∨ r) ∧ (q ∨ r) := by
  sorry
