-- algebraic data types exercises

/-
Define queue operations on lists.

Then, prove algebraic properties of queue operations.
If your proof gets stuck, your implementation of some operation might be incorrect.
-/

open List  -- use Lean 4's `List`

def empty {α : Type u} : List α :=
  sorry

def is_empty (q : List α) : Bool :=
  sorry

def enqueue (q : List α) (x : α) : List α :=
  sorry

def peek (default : α) (q : List α) : α :=
  sorry

def dequeue (q : List α) : List α :=
  sorry

theorem is_empty_empty : is_empty (@empty α) := by
  sorry

theorem is_empty_nonempty (q : List α) (x : α)
    : is_empty (enqueue q x) = false := by
  sorry

theorem peek_empty (d : α) : peek d empty = d := by
  sorry

theorem peek_nonempty (d x : α) (q : List α)
    : peek d (enqueue q x) = peek x q := by
  sorry

theorem dequeue_empty : dequeue (@empty α) = empty := by
  sorry

theorem dequeue_nonempty (x : α) (q : List α)
    : dequeue (enqueue q x) = if is_empty q then q else enqueue (dequeue q) x := by
  sorry
