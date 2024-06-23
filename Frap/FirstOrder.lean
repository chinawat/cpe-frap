/-
## Sectioning

Sometimes, it is helpful to limit names to a local scope.
Use `section` ... `end` to indicate a scope.

Optionally, we can give a name to section, in which case the name must follow both `section` and `end`.
-/
section

/-
## Variables

In each proposition we have proven, we often introduce propositional variables like `p` and `q`.
Although we could write them down in each individual proposition, we can declare "global" variables for the entire file, using the `variable` command.
-/

variable (p q r : Prop)

/-
## Anonymous constructors

In a proof having a conjunction in the hypothesis, we had to use the `cases` command to break it down into conjuncts.
This can be tedious.
-/
example : p ∧ q → q ∧ p := by
  intro hand
  cases hand with
  | intro hp hq =>
      apply And.intro
      . exact hq
      . exact hp
/-
For elements that can be constructed in one way, e.g., conjunctions, we can instead use the _anonymous constructor_ notation `⟨arg1, arg2, ...⟩` to break down the elements into its constituents.
These angle brackets can be typed using `\<` and `\>` shortcuts.

Now, we can deconstruct a conjunction at the time of the introduction.
-/
example : p ∧ q → q ∧ p := by
  intro ⟨hp, hq⟩
  apply And.intro
  . exact hq
  . exact hp
/-
In certain scenarios, we might not be able to deconstruct a conjunction at the time of its introduction.
We can use the `obtain` tactic to break down a conjunction appearing in a hypothesis later on.
-/
example : p ∧ q → q ∧ p := by
  intro h
  obtain ⟨hp, hq⟩ := h
  apply And.intro
  . exact hq
  . exact hp

end

section quantifiers

/-
## Predicates

So far, all of our propositions are not parameterized: each proposition can be immediately interpreted as true or false.
To make them more versatile, we can parameterize propositions into _predicates_, whose truth values depends on the value of their parameters.
A predicate expecting one parameter is called a _unary predicate_.
A predicate expecting two parameters is callled a _binary predicate_.

For a unary predicate named `p`, if the type of its parameter is `α`, then `p` is a function of type `α → Prop`, so that if `x : α`, then `p x : Prop`.
Note that we are more familiar with the notation `p(x)`, but Lean doesn't require us to write down parentheses in this context.

The notation `x : α` might be more familiar if seen as `x ∈ α`.
This also applies to when we write `p : Prop`.

Likewise, for a binary predicate named `p`, if the type of its first parameter is `α` and the type of its second parameter is `β`, then `p` is a function of type `α → β → Prop`, so that if `x : α` and `y : β`, then `p x y : Prop`.
Note that we are more familiar with the notation `p(x, y)`, but Lean doesn't require us to write down parentheses or commas in this context.

We can use binary predicates to represent a relation between `α` and `β`.
If `α = β`, then we have a _relation on `α`_.

## Universal quantifier

The universal quantifier (∀) can be typed using `\forall` shortcut.

A universally quantified statement `∀ x : α, p x` is true when, for every `x : α`, `p x` holds.

To prove that a universally quantified statement holds, we use the ∀-introduction rule, which states that, given a proof of `p x` in a context where `x : α` is arbitrary, we obtain a proof of `∀ x : α, p x`.
This can be seen as a _generalization_ of predicate `p`.
We can use the `intro` tactic to introduce the universally quantified variable into the hypothesis.

To use a universally quantified statement in the hypothesis, we use the ∀-elimination rule, which states that, given a proof of `∀ x : α, p x` and any term `t : α`, we obtain a proof of `p t`.
This can be seen as a _specialization_ of predicate `p` on a given term of type `α`.
We can use the `apply` tactic for a specialization, or the `specialize` tactic, along with the name of the assumption and the variable name to specialize on.
-/

example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y := by
  intro h
  intro y
  apply And.left
  apply h

example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y := by
  intro h
  intro y
  specialize h y
  apply And.left
  exact h

section relations
/-
In this subsection, we demonstrate the use of universal quantifiers in the hypothesis.
-/

variable (α : Type) (r : α → α → Prop)

/-
Here, we assume that the relation `r` is reflexive, symmetric, and transitive.
-/
variable (refl_r : ∀ x, r x x)
variable (symm_r : ∀ {x y}, r x y → r y x)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

example (a b c d : α) : r a b → r c b → r c d → r a d  := by
  intro hab hcb hcd
  apply trans_r
  . exact hab
  . apply trans_r
    . apply symm_r
      exact hcb
    . exact hcd
end relations

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  constructor  -- can be used in place of `apply Iff.intro`
  . intro h
    constructor  -- can be used in place of `apply And.intro`
    . intro x
      apply And.left
      apply h
    . intro x
      apply And.right
      apply h
  . intro ⟨hp, hq⟩
    intro x
    constructor
    . apply hp
    . apply hq

/-
exercise (1-star)
-/
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  sorry

/-
exercise (1-star)
-/
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  sorry

end quantifiers

/-
## references
- [Theorem Proving in Lean 4: Quantifiers and Equality](https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html)
-/
