/-
## Backward and forward tactic applications

Recall the conjunction elimination examples from last time:
-/
example (p q : Prop) : p ∧ q → p := by
  intro hand
  apply And.left
  exact hand

example (p q : Prop) : p ∧ q → p := by
  intro hand
  apply And.left hand
/-
Above, we use the`apply` tactic on the `And.left` _function_, whose job is to take a conjunction and return the left operand, and similarly for `And.right`.
-/
#check And.left
#check And.right
/-
In the first example, we attempt to apply `And.left` in the _backward_ mode to the proof goal: given the result of the function, what _could_ be the initial conjunction?
This is the reason why a placeholder variable `?b` occurs on the right-hand side of the "resulting" conjunction: because we don't know what might be the operand on the right just yet.
But when we apply the `exact` tactic with the assumption, the proof engine _unifies_ the placeholder variable with the appropriate proof term, i.e., `q`.

In the second example, we apply `And.left` in the usual _forward_ mode to the `hand` assumption, and the result is simply the left-hand side of the conjunction.
Then, we apply this result to the proof goal, matching it exactly and completing the proof.
In fact, we can use `exact And.left hand` instead of `apply And.left hand` here.
-/

/-
## Equivalence

Equivalence (if and only if) is a two-way implication.
Its symbol (↔) can be typed using `\iff` shortcut.
`p ↔ q` is a shorthand for `(p → q) ∧ (q → p)`.

## Proving equivalence

Since an equivalence is a shorthand of a conjunction, we can prove it in the same way as for a conjunction, by using the `Iff.intro` tactic to split the iff into two implication subgoals.
-/
#check Iff.intro

theorem and_commutative (p q : Prop) : p ∧ q ↔ q ∧ p := by
  apply Iff.intro
  . intro hpq
    apply And.intro
    . apply And.right
      exact hpq
    . apply And.left
      exact hpq
  . intro hqp
    apply And.intro
    . apply And.right
      exact hqp
    . apply And.left
      exact hqp

/-
Using an equivalence in the assumptions can be done in the same way as for a conjunction, by using the `cases` tactic to split the iff into two implications in the assumptions.
-/

example (p q : Prop) : (p ↔ q) → (p → q) := by
  intro iff
  cases iff with
  | intro hpq hqp => exact hpq

/-
exercise (2-star)
Prove that the conjunction operator is associative.
-/
theorem and_associative (p q r : Prop) : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  sorry

/-
## Rewriting proof terms using previously proven results

Often in our proof, we'll need to use the same tactic sequence as in a prior proof.
Like in software development, duplicating the sequence results in duplicate code and can lead to maintenance problems.
We can refer to an earlier propeosition by simply writing the name of the theorem or lemma of interest.
This is similar to breaking down a large program into functions.

First, if we have a previously proven result, we can apply that result directly in the `apply` tactic.
-/
example (p q : Prop) : p ∧ q ↔ q ∧ p := by
  apply and_commutative

/-
We can even refer to asserted but unproven propositions.
-/
example (p q r : Prop) : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  apply and_associative

/-
For nested proof terms, we can use the `rewrite` tactic, along with a list of identities (equivalences) to apply to the proof goal or a hypothesis.

The syntax here is a bit complicated.
We need to pass a configuration stating which occurrence(s) of the proof term we want to rewrite.
An occurrence is a preorder position within the AST of the proof term, with 1 as the root (the entire proof term).
You might need to do some trial-and-error to get the desired occurrence.
Refer to the pop-up contextual guide for more information.
-/
example (p q r : Prop) : (p ∧ q) ∧ r ↔ (q ∧ p) ∧ r := by
  apply Iff.intro
  . intro h
    rewrite (config := {occs := .pos [2]}) [and_commutative] at h
    assumption
  . intro h
    rewrite (config := {occs := .pos [2]}) [and_commutative] at h
    assumption

/-
## Disjunctions

Disjunction symbol (∨) can be typed using `\or` shortcut.

## Proving disjunctions

When the proof goal is a disjunction, it suffices to proof one of the disjuncts.
Here, we can apply the `Or.inl` or `Or.inr` tactic to choose the side we want to prove.
-/

#check Or.inl
#check Or.inr

theorem or_intro_l (p q : Prop) : p → p ∨ q := by
  intro hp
  apply Or.inl
  exact hp

/-
exercise (1-star)
-/
theorem or_intro_r (p q : Prop) : q → p ∨ q := by
  sorry

/-
If a proof is short, we can write multiple tactics on the same line, separated by semicolons.
-/
example (p q : Prop) : p → p ∨ q := by
  intro hp; apply Or.inl; exact hp

/-
So far, whenever we use `intro` and `exact` tactics, we always supply them with the name of the hypothesis.
When proofs become longer, however, there may be lots of names that picking out the desired one may be difficult.
It is possible to use the `intro` tactic without specifying a name, and Lean will automatically generate one.
But how do we use the `exact` tactic on such assumptions?
Instead of specifying an assumption to be used to resolve a goal, we can use the `assumption` tactic to let Lean look for whatever assumption that can resolve a goal and use it.
-/
example (p q : Prop) : p → p ∨ q := by
  intro
  apply Or.inl
  assumption
/-
Initially, when you are still learning how to write a proof, it is advised that you explicitly specify the assumption that will be used in each step, so you can see exactly how the tactic state changes during the course of the proof.
That way, you can understand the proof better.
-/

/-
If we have a disjunction in assumptions and want to use it, we don't know exactly which disjunct is true.
Here, we have to use _proof by cases_ to ensure that, for each disjunct, ourgoal can be satisfied if the disjunct is true.
Use the `cases` tactic like we did with conjunctions, but now there are two cases, one per disjunct.
We introduce the assumption of the left disjunct with `inl`, followed by the name of the hypothesis; similarly, we can use `inr` for the right disjunct.
-/

theorem or_elim (p q r : Prop) : p ∨ q → (p → r) → (q → r) → r := by
  intro hor; intro hpr; intro hqr
  cases hor with
  | inl hp => apply hpr; exact hp
  | inr hq => apply hqr; exact hq

/-
When a proposition to be proved is more complex, there might be a lot of assumptions that need to be introduced.
In the theorem above, we have three assumptions, each one being introduced individually with the `intro` tactic.
We can combine these `intro`s into a single `intros` tactic.
We can use the `intro` tactic with multiple names, too, to the same effect.
-/

example (p q r : Prop) : p ∨ q → (p → r) → (q → r) → r := by
  intros hor hpr hqr
  cases hor with
  | inl hp => apply hpr; exact hp
  | inr hq => apply hqr; exact hq

/-
exercise (1-star)
Prove that the disjunction operator is commutative.
-/
theorem or_commutative (p q : Prop) : p ∨ q ↔ q ∨ p := by
  sorry

/-
exercise (2-star)
Prove that the disjunction operator is associative.
-/
theorem or_associative (p q r : Prop) : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  sorry

/-
## Negation

The negation symbol (¬) can be typed using `\not` shortcut.

The negation of a proposition `p` has the same meaning as `p → False`.

## Proving negation

Since `¬p` means `p → False`, to prove `¬p` means to assume `p` and derive a contradiction.

If we have a negation in the hypothesis, we can derive a contradiction in the hypothesis, and conclude anything.

The canonical example is the _ex falso quodlibet_ rule, which means, "from falsehood, anything follows."
We can use the `exfalso` tactic to convert the current proof goal into a contradiction.
-/

theorem ex_falso_quodlibet (p : Prop) : False → p := by
  intro hf
  exfalso
  exact hf

example (p : Prop) : False → p := by
  intro; exfalso; assumption

example (p q : Prop) : p ∧ ¬p → q := by
  intro h
  cases h with
  | intro hp hnp =>
      exfalso
      apply hnp
      exact hp

/-
Sometimes, we can derive falsity without needing to invoke `exfalso`.
-/
theorem dbl_negation_intro (p : Prop) : p → ¬¬p := by
  intro hp
  intro hnp
  apply hnp
  exact hp

/-
Note that the `¬¬p → p` doesn't hold in constructive logic!
-/

/-
exercise (2-star)
Prove that we can eliminate double negations as long as there are negations left.
-/
theorem dbl_negation_elim (p : Prop) : ¬p ↔ ¬¬¬p := by
  sorry
