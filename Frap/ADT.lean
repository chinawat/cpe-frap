/-
## Algebraic data types
-/

/-
## Binary search trees
-/

inductive Tree (α : Type u) where
  | empty  : Tree α
  | tree (l : Tree α) (k : Nat) (v : α) (r : Tree α) : Tree α

namespace Tree

/-
## Binary search tree implementation
-/

def ex_tree : Tree String :=
  tree (tree empty 2 "two" empty) 4 "four" (tree empty 5 "five" empty)

def empty_tree {α : Type u} : Tree α := empty

def contains {α : Type u} (x : Nat) (t : Tree α) : Bool :=
  match t with
  | empty => false
  | tree l k _ r =>
      if x < k then contains x l
      else if x > k then contains x r
      else true

def lookup {α : Type u} (d : α) (x : Nat) (t : Tree α) : α :=
  match t with
  | empty => d
  | tree l k v r =>
      if x < k then lookup d x l
      else if x > k then lookup d x r
      else v

def insert {α : Type u} (x : Nat) (v : α) (t : Tree α) : Tree α :=
  match t with
  | empty => tree empty x v empty
  | tree l k v' r =>
      if x < k then tree (insert x v l) k v' r
      else if x > k then tree l k v' (insert x v r)
      else tree l x v r  -- update value

/-
## Binary search tree invariant
-/

inductive ForallTree {α : Type u} (p : Nat → α → Prop) : Tree α → Prop where
  | empty : ForallTree p empty
  | tree : ∀ l k v r,
      p k v → ForallTree p l → ForallTree p r → ForallTree p (tree l k v r)

inductive BST {α : Type u} : Tree α → Prop where
  | empty : BST empty
  | tree : ∀ l k v r,
      ForallTree (fun x _ => x < k) l
      → ForallTree (fun x _ => x > k) r
      → BST l
      → BST r
      → BST (tree l k v r)

example : BST ex_tree := by
  constructor
  . constructor
    . simp
    . constructor
    . constructor
  . constructor
    . simp
    . constructor
    . constructor
  . constructor
    . constructor
    . constructor
    . constructor
    . constructor
  . constructor
    . constructor
    . constructor
    . constructor
    . constructor

/-
Tactic `t1 <;> t2` applies tactic `t1` to the current goal, and for each subgoal generated, applies tactic `t2`.
-/

example : BST ex_tree := by
  constructor <;> constructor <;> constructor <;> constructor

-- example : BST ex_tree := by
--   repeat' (repeat constructor)

/-
exercise (1-star)
Prove that the empty tree is a BST.
-/
theorem empty_tree_BST (α : Type u) : BST (@empty_tree α) := by
  sorry

/-
exercise (4-star)
Prove that `insert` produces a BST, assuming it is given one.

Start by proving this helper lemma `forallT_insert`, which says that `insert` preserves any node predicate.
Proceed by induction on `t`.

Now prove the main theorem.
Proceed by induction on the evidence that `t` is a BST.
-/

theorem forall_insert_of_forall {α : Type u} (P : Nat → α → Prop) (t : Tree α)
    : ForallTree P t → ∀ k v, P k v → ForallTree P (insert k v t) := by
  sorry

theorem bst_insert_of_bst {α : Type u} (k : Nat) (v : α) (t : Tree α)
    : BST t → BST (insert k v t) := by
  sorry

/-
## Correctness of BST operations
-/

theorem lookup_empty {α : Type u} (d : α) (k : Nat)
    : lookup d k empty_tree = d := by
  rfl

theorem lookup_insert_eq {α : Type u} (d : α) (k : Nat) (v : α) (t : Tree α)
    : lookup d k (insert k v t) = v := by
  induction t with
  | empty => rw [insert, lookup]; simp
  | tree l k' v' r ihl ihr =>
      unfold insert
      by_cases hlt : k < k'
      . simp [*]
        unfold lookup
        simp [*]
      . by_cases hgt : k' < k
        simp [*]
        unfold lookup
        simp [*]
        . have heq : k = k' := by
            simp at *; apply Nat.le_antisymm
            . assumption
            . assumption
          simp [*]
          unfold lookup
          simp [*]

example {α : Type u} (d : α) (k : Nat) (v : α) (t : Tree α)
    : lookup d k (insert k v t) = v := by
  induction t with
  | empty => rw [insert, lookup]; simp
  | tree l k' v' r ihl ihr =>
      unfold insert
      by_cases hlt : k < k'
      . simp [*]
        unfold lookup
        simp [*]
      . by_cases hgt : k' < k
        simp [*]
        unfold lookup
        simp [*]
        . have heq : k = k' := by omega  -- shorter!
          simp [*]
          unfold lookup
          simp [*]

/-- `by_cases' h : e` is a shorthand form `by_cases h : e <;> simp[*]` -/
local macro "by_cases' " e:term : tactic =>
  `(tactic| by_cases $e <;> simp [*])

example {α : Type u} (d : α) (k : Nat) (v : α) (t : Tree α)
    : lookup d k (insert k v t) = v := by
  induction t with
  | empty => rw [insert, lookup]; simp
  | tree l k' v' r ihl ihr =>
      unfold insert
      by_cases' k < k'
      . unfold lookup
        simp [*]
      . by_cases' k' < k
        unfold lookup
        simp [*]
        . have heq : k = k' := by omega
          simp [*]
          unfold lookup
          simp [*]

attribute [local simp]
  contains lookup insert

example {α : Type u} (d : α) (k : Nat) (v : α) (t : Tree α)
    : lookup d k (insert k v t) = v := by
  induction t with simp
  | tree l k' v' r ihl ihr =>
      by_cases' k < k'
      by_cases' k' < k

theorem lookup_insert_neq {α : Type u} (d : α) (k k' : Nat) (v : α) (t : Tree α)
    : k ≠ k' → lookup d k' (insert k v t) = lookup d k' t := by
  intro hneq
  induction t with simp
  | empty => omega
  | tree l x v' r ihl ihr =>
      by_cases' k < x
      by_cases' x < k
      have _ : k = x := by omega
      by_cases' k' < x
      by_cases' x < k'
      have _ : k' = x := by omega
      omega

end Tree

/-
## references
* [Software Foundations, Volume 3 Verified Functional Algorithms: Binary Search Trees](https://softwarefoundations.cis.upenn.edu/vfa-current/SearchTree.html)
* [Lean Manual: Binary Search Trees](https://lean-lang.org/lean4/doc/examples/bintree.lean.html)
-/
