section rewriting

variable (α : Type) (a b c d : α)  -- a, b, c, d are elements of some type

/-
## Rewriting

Recall our equality proof from last time.
-/

example : a = b → c = b → c = d → a = d := by
  intro hab hcb hcd
  apply Eq.trans
  . exact hab
  . apply Eq.trans
    . apply Eq.symm
      exact hcb
    . exact hcd

/-
Notice that in each subgoal, we are attempting to use a hypothesis by way of an equality property.
For example, we invoke the transitive property on `a = d` so that we can use the assumption `a = b` and be left with `b = d` to prove.
In effect, we are substituting `b` for `a` in the goal.

This substitution operation can be seen as rewriting some term in the goal with another, via an equality in the hypothesis.
This rewriting operation is so common that Lean provides a `rw` tactic to do so.
It replaces equals for equals, which could be an equality (`=`) or equivalence (`↔`).

Be default, it rewrites the left-hand side with the right-hand side.
For right-to-left rewriting, a left arrow needs to be indicated before the hypothesis (`←`, typed with `\<-` shortcut) .
-/

example : a = b → c = b → c = d → a = d := by
  intro hab hcb hcd
  rw [hab]
  rw [← hcd]
  rw [hcb]

/-
You can use `rw` tactic not only to the entire term of a goal, but also a subterm within a goal.
You can also rewrite a hypothesis by suffixing the tactic with `at _h_`, where _h_ is a hypothesis.
It is best to try this yourself.
-/

end rewriting

/-
## reflexivity tactic

One of the most powerful tactics is the _reflexivity_ tactic, written `rfl` in Lean.
It will attempt to conclude that both sides of an equality goal is indeed equal, up to some trivial computation, such as expansion of definitions and function applications.
-/

example : 2 + 5 = 7 := by
  rfl

/-
## Inductive types

Most objects in computer science are built from smaller objects of the same type.
Trees are built from smaller trees.
Expressions are built from smaller expressions.
Smallest expressions, such as literals, are defined explicitly.
This concept can be captured as _inductive types_.
-/

namespace Hidden

/-
For example, we can define natural numbers as follows.
-/

inductive Nat where
  | zero : Nat
  | succ : Nat → Nat

/-
This says that a natural number can be _constructed_ in two ways.
The `zero` constructor is for 0 (base case).
The `succ` constructor is for building a slightly larger natural number from an existing one (inductive case).
-/

/-
Operations on inductive types are usually defined with recursion.

For example, to define addition, we can use recursion on the second argument as follows.
If the second argument is zero, the result is the first argument.
Otherwise, the second argument is a successor of some other natural number (say `n`), so the result is the successor of the result of adding the first argument with `n`.
-/

namespace Nat

def add (m n : Nat) : Nat :=
  match n with
  | zero    => m
  | succ n' => succ (add m n')

/-
Multiplication is defined similarly.
-/

def mul (m n : Nat) : Nat :=
  match n with
  | zero    => zero
  | succ n' => add (mul m n') m

/-
The following declarations let us use `+` and `*` (almost, for now) interchangeably with `add` and `mul`.
-/
instance : Add Nat where
  add := add
instance : Mul Nat where
  mul := mul

end Nat
end Hidden

/-
Lean already defines `Nat`.
Arabic numbers are compact representations of larger numbers.
The `+` and `*` operators can be used in place of `add` and `mul`.
-/

#print Nat
#check 0
#eval Nat.zero = 0
#eval Nat.succ 0 = 1

#check Nat.add
#print Nat.add
#check Nat.mul
#print Nat.mul

#eval Nat.add 2 5 = 2 + 5
#eval Nat.mul 2 5 = 2 * 5

section opendemo

/-
For convenience, we can avoid prefixing everything with `Nat` by creating _aliases_ to definitions and theorems that begins with `Nat` using the `open` command.
-/

open Nat

end opendemo

/-
But for now, to avoid mixing up what we want to prove and what Leans' `Nat` has already given us, we will work exclusively with our own `Nat`.
-/

namespace Hidden
namespace Nat

/-
As usual, we can prove trivial properties on inductively defined types with `rfl`.
-/

theorem add_zero (m : Nat) : m + zero = m := by
  rfl

theorem add_succ (m n : Nat) : m + succ n = succ (m + n) := by
  rfl

end Nat
end Hidden

/-
Again, Lean has already proven these facts for us.
-/

#check Nat.add_zero
#print Nat.add_zero
#check Nat.add_succ
#print Nat.add_succ

/-
## Structural induction

To prove general properties, however, we need to use _structural induction_.
Use the `induction` tactic to prove the base case and the inductive step, as in how the type is inductively defined.
In the inductive step, you can introduce the smaller object(s) being inducted on, and the induction hypothesis.
-/

namespace Hidden
namespace Nat

theorem zero_add (n : Nat) : zero + n = n := by
  induction n with
  | zero      => rfl
  | succ n' ih =>
      rw [add_succ]
      rw [ih]

example (n : Nat) : zero + n = n := by
  induction n with
  | zero      => rfl
  | succ n' ih => rw [add_succ, ih]

/-
Addition is associative.
-/

theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) := by
  induction k with
  | zero => rfl
  | succ k' ih =>
      rw [add_succ, add_succ, add_succ, ih]

/-
Now, suppose we want to prove that addition is commutative.
-/

example (m n : Nat) : m + n = n + m := by
  induction n with
  | zero =>
      rw [zero_add, add_zero]
  | succ n' ih =>
      rw [add_succ, ih]
      sorry

/-
We're stuck, since we have a goal `(n' + m).succ = n'.succ + m` for which we can't prove.
Here, we need a supporting fact that `succ (m + n) = succ m + n`.
We prove this by structural induction on n.
-/

theorem succ_add (m n : Nat) : succ (m + n) = succ m + n := by
  induction n with
  | zero => rfl
  | succ n' ih =>
      rw [add_succ, add_succ, ih]

theorem add_comm (m n : Nat) : m + n = n + m := by
  induction n with
  | zero =>
      rw [add_zero]
      rw [zero_add]
  | succ n' ih =>
      rw [add_succ]
      rw [ih]
      rw [succ_add]

/-
Alternatively, if the supporting fact is only useful within a single theorem, we can embed the proof within, using the
-/

example (m n : Nat) : m + n = n + m := by
  induction n with
  | zero =>
      rw [add_zero]
      rw [zero_add]
  | succ n' ih =>
      rw [add_succ]
      rw [ih]
      have h (m n : Nat) : succ (m + n) = succ m + n := by
        induction n with
        | zero =>
            rw [add_zero]
            rw [add_zero]
        | succ n' ih =>
            rw [add_succ]
            rw [add_succ]
            rw [ih]
      rw [h]

/-
Let's try proving facts for multiplication.
-/

theorem mul_zero (m : Nat) : m * zero = zero := by
  rfl

theorem mul_succ (m n : Nat) : m * succ n = add (m * n) m := by
  rfl

theorem add_infix (m n : Nat) : m.add n = m + n := by
  rfl

theorem mul_assoc (m n k : Nat) : m * n * k = m * (n * k) := by
  induction k with
  | zero => rfl
  | succ k' ih =>
      rw [mul_succ, mul_succ, ih, add_infix, add_infix]
      have nat_distrib (m n k : Nat)
            : m * n + m * k = m * (n + k) := by
        -- distributive property from left
        induction k with
        | zero => rfl
        | succ k' ih =>
            rw [mul_succ, add_succ, mul_succ, add_infix, add_infix, ← add_assoc, ih]
      rw [nat_distrib]

/-
exercise (3-star)
Prove that multiplication is commutative.
Add auxiliary theorems as necessary.
-/
theorem mul_comm (m n : Nat) : m * n = n * m := by
  sorry

end Nat
end Hidden

/-
## references
* [Theorem Proving in Lean 4: Inductive Types](https://lean-lang.org/theorem_proving_in_lean4/inductive_types.html#tactics-for-inductive-types)
* Anne Baanen, Alexander Bentkamp, Janmin Blanchette, Johannes Hölzl, Jannis Limperg. [The Hitchhiker's Guide to Logical Verification](https://raw.githubusercontent.com/blanchette/logical_verification_2023/main/hitchhikers_guide.pdf), version November 21, 2023.  Chapter 3.
-/
