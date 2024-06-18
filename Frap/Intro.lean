/-
## Propositions

Propositions in Lean have type `Prop`.
We can define a proposition using `def` keyword.
-/

def p : Prop := True
def q : Prop := False

/-
We can inspect a type of something by using the `#check` command.
-/
#check p
#check q

/-
## Implications

Implication symbol (→) can be typed using `\imp`, `\to`, or `\r` shortcut.

The symbol `->` can also be used.
-/
#check p → q
#check p -> q

/-
## Stating a proposition to be proved

To declare a proposition to be provend, start with the keyword `theorem`, `lemma`, or `example`.  The first two require a name (of the theorem or lemma), while `example` doesn't.

Next, declare any propositional variables that will be used in the proposition itself, followed by a `:`, and then the proposition in question.

Finally, begin the proof by writing `:= by`, followed by the proof.

The keyword `sorry` can be used to leave the proof unfinished.
-/
example (p q : Prop) : p → q := by
  sorry

/-
## Proving implications

The left-hand side of an implication is an assumption that may be used in the proof.
To introduce the assumption given by an implication, use the `intro` tactic, followed by the name of the assumption being introduced.

To use an assumption, use the `exact` tactic, followed by the name of the assumption to be used.
If the provided assumption cannot be used in the current context, an error occurs.
-/

theorem identity (p : Prop) : p → p := by
  intro hp
  exact hp

/-
If we have an implication in assumptions and want to use it, we can use the `apply` tactic with the name of the assumption.

In fact, `exact` is a more efficient variant of `apply`.
-/

theorem modus_ponens (p q : Prop) : p -> (p -> q) -> q := by
  intro hp
  intro h
  apply h
  exact hp

/-
## Conjunctions

Conjunction symbol (∧) can be typed using `\and` shortcut.

## Proving conjunctions

When the proof goal is a conjunction, we need to show that each side of the conjunction holds.
Here, we can apply the `And.intro` tactic to break the conjunction down into two cases.
We give the proof of each case in turn.
-/

theorem and_intro (p q : Prop) : p -> q -> p ∧ q := by
  intro hp
  intro hq
  apply And.intro
  exact hp
  exact hq

/-
When we have multiple subgoals to work with, it might be nice to focus on one goal at a time.  Use the `.` tactic to select the first subgoal (and ignore the rest for now).
-/
example (p q : Prop) : p -> q -> p ∧ q := by
  intro hp
  intro hq
  apply And.intro
  . exact hp
  . exact hq

/-
If we have a conjunction in assumptions and want to use it, we can break it down into individual assumptions using the `cases` tactic on such assumption.
In this situation, there is only one case to work with (namely, the conjunction itself), but within it, there are two smaller assumptions.
We can use the `intro` tactic to introduce each one.
-/
theorem and_elim_l (p q : Prop) : p ∧ q → p := by
  intro hand
  cases hand with
  | intro hp hq => exact hp

/-
exercise (1-star)
-/
theorem and_elim_r (p q : Prop) : p ∧ q → q := by
  sorry

/-
Alternatively, if we only need to use one side of the conjunction, we can apply the `And.left` or `And.right` tactic as appropriate.

In this example, after applying `And.left`, two subgoals result, with a placeholder variable `?b` being introduced.
Applying the assumption _unifies_ the placeholder with the right-hand side of the conjunction.
-/
theorem and_elim_l' (p q : Prop) : p ∧ q → p := by
  intro hand
  apply And.left
  exact hand
/-
In the example above, we already know which assumption we want to use `And.left` on, so we can provide the assumption for the `apply` tactic to work with immediately.
-/
example (p q : Prop) : p ∧ q → p := by
  intro hand
  apply And.left hand
