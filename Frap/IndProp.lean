/-
## Forward reasoning

-/

example (p q r : Prop) : (p → q) → (q → r) → p → r := by
  intro hpq hqr hp
  apply hqr
  apply hpq
  apply hp

example (p q r : Prop) : (p → q) → (q → r) → p → r := by
  intro hpq hqr hp
  have hq : q := by apply hpq; apply hp
  have hr : r := by apply hqr; apply hq
  assumption

/-
## Inductively defined propositions

-/

open Nat

inductive Even : Nat → Prop where
  | ev_zero : Even 0
  | ev_add_two (n : Nat): Even n → Even (n + 2)

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

theorem evSS_ev (n : Nat) : Even (succ (succ n)) → Even n := by
  intro h
  have h' := Iff.mp (ev_inversion _) h
  cases h' with
  | inl h0 =>
      exfalso
      apply succ_ne_zero
      assumption
  | inr hs =>
      obtain ⟨n', ⟨hss, hen'⟩⟩ := hs
      have heq : n = n' := by
        rw [succ_inj', succ_inj'] at hss
        assumption
      rw [heq]
      assumption

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

-/

theorem mod_two_Eq_zero_of_Even (n : Nat) : Even n → n % 2 = 0 := by
  intro h
  induction h with
  | ev_zero => rfl
  | ev_add_two _ _ ih =>
      rw [add_mod_right]
      exact ih

/-
-/

example : Even n → n % 2 = 0 := by
  intro h
  induction h with
  | ev_zero => rfl
  | ev_add_two _ _ ih => simp [ih]

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
-/

inductive LEq : Nat → Nat → Prop where
  | le_n (n : Nat) : LEq n n
  | le_S (n m : Nat) : LEq n m → LEq n (succ m)

open LEq

example : LEq 3 5 := by
  apply le_S
  apply le_S
  apply le_n

def lt (n m : Nat) := LEq (succ n) m

inductive TotalRel : Nat → Nat → Prop where
  | tot_rel : ∀ n m, TotalRel n m

theorem total_relation_is_total : ∀ n m : Nat, TotalRel n m := by
  apply TotalRel.tot_rel

inductive EmptyRel : Nat → Nat → Prop where

theorem empty_relation_is_empty : ∀ n m : Nat, ¬ EmptyRel n m := by
  intro n m hcontra
  cases hcontra

/-
## references
* [Software Foundations, Volume 1: Logical Foundations: Inductively Defined Propositions](https://softwarefoundations.cis.upenn.edu/lf-current/IndProp.html)
* Anne Baanen, Alexander Bentkamp, Janmin Blanchette, Johannes Hölzl, Jannis Limperg. [The Hitchhiker's Guide to Logical Verification](https://raw.githubusercontent.com/blanchette/logical_verification_2023/main/hitchhikers_guide.pdf), version November 21, 2023.  Chapter 6.
-/
