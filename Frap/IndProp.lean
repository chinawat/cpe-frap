/-
## Forward reasoning

So far, when we write a proof, we proceed by _backward reasoning_: working backwards from the goal, generating subgoals as necessary, and proving each subgoal.
While this method usually works, sometimes we need to use _forward reasoning_, deducing facts from the hypothesis, so that deduced facts can be used at a later point in the proof.

Recall this earlier example, when we worked backwards from `r` to generate "easier" goals.
-/

example (p q r : Prop) : (p → q) → (q → r) → p → r := by
  intro hpq hqr hp
  apply hqr
  apply hpq
  exact hp

/-
It is possible to turn the proof above into a _forward proof_.
At each point, we assert a fact that we can deduce from the hypothesis using the `have` construct, which introduces an auxiliary subgoal in a proof.
This subgoal can be proven in the same way as the main theorem (`:= by ...`).

In other words, the `have` construct digresses from the main proof.
You can deduce facts from the hypothesis, prove something that may be helpful towards the current goal, or even prove something entirely irrelevant (which, of course, is eventually useless).
-/

example (p q r : Prop) : (p → q) → (q → r) → p → r := by
  intro hpq hqr hp
  have hq : q := by apply hpq; apply hp
  have hr : r := by apply hqr; apply hq
  exact hr

/-
## Inductively defined propositions

So far, we use an `inductive` declaration to declare a type of objects, such as the natural numbers and lists.
These objects may be built from external data other than from the inductive type itself.
For example, when using `cons` to build a longer list, we provide the head element, which is not a list.
The result of `cons` is a list, whose elements are of type `α`.
Here, the `List` _type constructor_ takes a _type argument_ `α` and produces a fully instantiated type.
-/

namespace Hidden
inductive List (α : Type u) where
  | nil  : List α
  | cons : α → List α → List α
end Hidden

/-
We can do the same with predicates: a _predicate_ takes an argument and produces a proposition, and we can inductively build propositions whose truth value depends on other, "smaller" propositions.

For example, we can define predicate `Even` on the natural numbers as follows:
* `0` is even
* if `n` is even, then `n + 2` is also even

We can capture this intuition in the following inductively defined propositions.
`ev_zero` says that `0` is even.
`ev_add_two` says that, for any natural number `n`, if `n` is even, then `n + 2` is also even.
As usual, `ev_zero` is the base case of the definition, while `ev_add_two` is the inductive case.
-/

open Nat  -- Lean's provided natural number

inductive Even : Nat → Prop where
  | ev_zero : Even 0
  | ev_add_two (n : Nat): Even n → Even (n + 2)

/-
We can apply these constructors in simple proofs, e.g., that `4` is even, and that the result of doubling any natural number is even.
-/

open Even

example : Even 4 := by
  apply ev_add_two
  apply ev_add_two
  exact ev_zero

def double (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | succ n' => succ (succ (double n'))

theorem ev_double (n : Nat) : Even (double n) := by
  induction n with
  | zero =>
      apply ev_zero
  | succ n' ih =>
      apply ev_add_two
      apply ih

/-
In fact, all the logical connectives are defined inductively (except for implications and universal quantification, which are embedded into the proof engine directly).
-/

namespace Hidden

inductive And : Prop → Prop → Prop where
  | intro : a → b → And a b

inductive Or : Prop → Prop → Prop where
  | inl : a → Or a b
  | inr : b → Or a b

inductive Iff : Prop → Prop → Prop where
  | intro : (a → b) → (b → a) → Iff a b

inductive Exists {α : Type} : (α → Prop) → Prop where
  | intro : ∀a : α, P a → Exists P

inductive True : Prop where
  | intro : True

inductive False : Prop where

inductive Eq {α : Type} : α → α → Prop where
  | refl : ∀a : α, Eq a a

end Hidden

/-
## Using evidence in proofs

Since evidence for inductive propositions must be built with one of the specified constructors, we can use proof by cases on the constructors that could have generated the evidence.

For example, we can prove that a natural number `n` is even if and only if it is zero or it is the successor of the successor of some other natural number `n'` which is also even.

When deconstructing an inductive proposition, we get all its constituents, which usually include the arguments supplied to the constructor and the evidence for such arguments.
For instance, when deconstructing using `ev_add_two` below, the constituents are (1) the natural number `n'` before taking the successor twice and (2) the evidence that `n'` is even (`hE'`).
-/

theorem ev_inversion (n : Nat)
    : Even n ↔ n = 0 ∨ ∃n' : Nat, n = succ (succ n') ∧ Even n' := by
  constructor
  . intro hE
    cases hE with
    | ev_zero => left; rfl
    | ev_add_two n' hE' => right; exists n'
  . intro hor
    cases hor with
    | inl h0 => rw [h0]; apply ev_zero
    | inr hE =>
        obtain ⟨n', ⟨heq, hE'⟩⟩ := hE
        rw [heq]
        apply ev_add_two
        assumption

/-
When using `cases` on evidence, Lean attempts to deduce the premise for the evidence.
Any inapplicable constructors are automatically resolved.

In the following proof for the fact that, "if the successor of the successor of any natural number `n` is even, then `n` itself is even," the evidence for `Even (succ (succ n))` cannot be built with `ev_zero`.
Therefore, we only need to work on the other case, `ev_add_two`
-/

theorem evSS_ev (n : Nat) : Even (succ (succ n)) → Even n := by
  intro h
  cases h with
  | ev_add_two n' hn' => assumption

/-
We can prove that `1` is not even by using the `ev_inversion` fact from above, along with some more facts from the `Nat` namespace.
-/

theorem one_not_even : ¬ Even 1 := by
  intro h
  have h' := Iff.mp (ev_inversion _) h
  cases h' with
  | inl h1 => apply succ_ne_zero; assumption
  | inr hs =>
      obtain ⟨n', ⟨hss, hen'⟩⟩ := hs
      rw [succ_inj'] at hss
      apply succ_ne_zero
      rw [hss]

/-
Alternatively, we can apply the `cases` tactic on the contradictory `Even 1` evidence, for which Lean concludes that it is impossible.
Here, there are no cases to prove, and we can simply use the `cases` tactic without the `with` keyword.
-/

example : ¬ Even 1 := by
  intro h
  cases h

/-
exercise (1-star)
-/
example : ¬ Even 3 := by
  sorry

/-
exercise (1-star)
-/
theorem evSSSS_ev (n : Nat) : Even (succ (succ (succ (succ n)))) → Even n := by
  sorry

/-
exercise (1-star)
-/
theorem ev5_nonsense : Even 5 → 2 + 2 = 9 := by
  sorry

/-
## Induction on evidence

Like with inductive types, we can use induction on inductive propositions.
In the inductive step, in addition to the constituents of the constructor, we also have the induction hypothesis, as usual.

When we defined the `Even` predicate above, we gradually build up a collection of evidence that larger natural numbers are even.
But this method of checking evenness quickly becomes inefficient when we want to use it in a program.
Instead, we might want to define a more efficient version using the modulo operator.
Here, we can verify that the inductive version implies the efficient variant.
(The converse also needs to be proven to claim that both versions are equivalent.)
-/

theorem mod_two_Eq_zero_of_Even (n : Nat) : Even n → n % 2 = 0 := by
  intro h
  induction h with
  | ev_zero => rfl
  | ev_add_two _ _ ih =>
      rw [add_mod_right]
      exact ih

/-
To avoid looking up facts from the `Nat` namespace, we can try the `simp` tactic, which uses lemmas and hypotheses to simplify the main goal or hypotheses.
-/

example (n : Nat) : Even n → n % 2 = 0 := by
  intro h
  induction h with
  | ev_zero => rfl
  | ev_add_two _ _ ih => simp; exact ih

/-
We can supply our own hypotheses to the `simp` tactic so as to finish the proof right away, when combined with existing lemmas and hypotheses elsewhere.
-/

example : Even n → n % 2 = 0 := by
  intro h
  induction h with
  | ev_zero => rfl
  | ev_add_two _ _ ih => simp [ih]

/-
We can define an alternative notion of evenness (based on `double`), and prove that it is equivalent to the original definition.
-/

def is_even (x : Nat) := ∃n : Nat, x = double n

example : is_even 2 := by
  unfold is_even  -- optional, can be helpful
  exists 1

theorem is_even_Even (n : Nat) : is_even n → Even n := by
  intro ⟨n', hn'⟩
  rw [hn']
  apply ev_double

theorem Even_is_even (n : Nat) : Even n → is_even n := by
  intro h
  induction h with
  | ev_zero => exists 0
  | ev_add_two n' _ ih =>
      obtain ⟨n'', hn''⟩ := ih
      exists (succ n'')
      rw [double, succ_inj', succ_inj']
      assumption

/-
exercise (2-star)
Prove that the sum of even numbers remains even.
-/
theorem ev_sum (n m : Nat) : Even n → Even m → Even (n + m) := by
  sorry

/-
## Inductive relations

Since relations are just a specific form of predicates, we can also define them inductively.

For instance, we can define the "less than or equal to" relation on the natural numbers as follows:
* any natural number is less than or equal to itself
* if `n` is less than or equal to `m`, then `n` is less than or equal to the successor of `m`
-/

inductive LEq : Nat → Nat → Prop where
  | le_n (n : Nat) : LEq n n
  | le_S (n m : Nat) : LEq n m → LEq n (succ m)

open LEq

example : LEq 3 5 := by
  apply le_S
  apply le_S
  apply le_n

/-
We can define the "less than" relation from `LEq`: `n` is less than `m` if the successor of `n` is less than or equal to `m`.
-/

def lt (n m : Nat) := LEq (succ n) m

/-
A total relation is one in which every element in the domain relates to itself.
-/

inductive TotalRel : Nat → Nat → Prop where
  | tot_rel : ∀ n m, TotalRel n m

theorem total_relation_is_total : ∀ n m : Nat, TotalRel n m := by
  apply TotalRel.tot_rel

/-
An empty relation is one in which no elements relate to itself.
-/

inductive EmptyRel : Nat → Nat → Prop where

theorem empty_relation_is_empty : ∀ n m : Nat, ¬ EmptyRel n m := by
  intro n m hcontra
  cases hcontra

/-
exercise (1-star)
Prove that `LEq` is reflexive.
-/
theorem LEq_reflexive : ∀n : Nat, LEq n n := by
  sorry

/-
exercise (4-star)
Prove that `LEq` is transitive.
Hint: We can do induction on a lot of things here.  Which one works?
-/
theorem LEq_transitive : ∀n m k : Nat, LEq n m → LEq m k → LEq n k := by
  sorry

/-
## references
* [Software Foundations, Volume 1: Logical Foundations: Inductively Defined Propositions](https://softwarefoundations.cis.upenn.edu/lf-current/IndProp.html)
* Anne Baanen, Alexander Bentkamp, Janmin Blanchette, Johannes Hölzl, Jannis Limperg. [The Hitchhiker's Guide to Logical Verification](https://raw.githubusercontent.com/blanchette/logical_verification_2023/main/hitchhikers_guide.pdf), version November 21, 2023.  Chapter 6.
-/
