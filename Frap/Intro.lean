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
To introduce the assumption given by an implication, use the `intro` tactic.

-/

theorem identity (p : Prop) : p → p := by
  intro hp
  exact hp
