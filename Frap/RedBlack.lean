inductive Color where
  | red
  | black

inductive Tree (α : Type u) where
  | empty  : Tree α
  | tree (c: Color) (l : Tree α) (k : Nat) (v : α) (r : Tree α) : Tree α

namespace Tree
open Color

def ex_tree : Tree String :=
  tree black (tree red empty 2 "two" empty) 4 "four" (tree red empty 5 "five" empty)

def empty_tree {α : Type u} : Tree α := empty

def contains {α : Type u} (x : Nat) (t : Tree α) : Bool :=
  match t with
  | empty => false
  | tree _ l k _ r =>
      if x < k then contains x l
      else if x > k then contains x r
      else true

def lookup {α : Type u} (d : α) (x : Nat) (t : Tree α) : α :=
  match t with
  | empty => d
  | tree _ l k v r =>
      if x < k then lookup d x l
      else if x > k then lookup d x r
      else v

def balance {α : Type u} (c : Color) (l : Tree α) (k : Nat) (vk : α) (r : Tree α) : Tree α :=
  match c with
  | red => tree red l k vk r
  | black =>
    match (l, k, vk, r) with
    | (tree red (tree red a x vx b) y vy c, z, vz, d)
    | (tree red a x vx (tree red b y vy c), z, vz, d)
    | (a, x, vx, tree red (tree red b y vy c) z vz d)
    | (a, x, vx, tree red b y vy (tree red c z vz d))
        => tree red (tree black a x vx b) y vy (tree black c z vz d)
    | _ => tree black l k vk r

def ins {α : Type u} (x : Nat) (vx : α) (t : Tree α) : Tree α :=
  match t with
  | empty => tree red empty x vx empty
  | tree c l k vk r =>
      if x < k then balance c (ins x vx l) k vk r
      else if x > k then balance c l k vk (ins x vx r)
      else tree c l x vx r  -- update value

def make_black {α : Type u} (t : Tree α) : Tree α :=
  match t with
  | empty => empty
  | tree _ l k vk r => tree black l k vk r

def insert {α : Type u} (x : Nat) (vx : α) (t : Tree α) : Tree α :=
  make_black (ins x vx t)

/-
-/

attribute [local simp]
  contains lookup balance ins make_black insert

theorem ins_not_empty {α : Type u} (k : Nat) (vk : α) (t : Tree α)
    : ins k vk t ≠ empty := by
  cases t with simp
  | tree c l k' _ r =>
    split  -- k < k'
    . split  -- c
      . simp
      . split  -- (ins k vk l, k', v✝, r)
        . simp
        . simp
        . simp
        . simp
        . simp
    . split  -- k > k'
      . split  -- c
        . simp
        . split  -- (l, k', v✝, ins k vk r)
          . simp
          . simp
          . simp
          . simp
          . simp
      . simp

example {α : Type u} (k : Nat) (vk : α) (t : Tree α)
    : ins k vk t ≠ empty := by
  cases t with simp
  | tree c l k' _ r =>
    (repeat' split) <;> simp

/-
Once again, we define an inductive predicate stating that a given predicate holds for a tree when the predicate holds for every node of the tree.
-/

inductive ForallTree {α : Type u} (p : Nat → α → Prop) : Tree α → Prop where
  | empty : ForallTree p empty
  | tree : ∀ c l k v r,
      p k v → ForallTree p l → ForallTree p r
      → ForallTree p (tree c l k v r)

/-
Now, we define the _binary search tree_ property.
-/

inductive BST {α : Type u} : Tree α → Prop where
  | empty : BST empty
  | tree : ∀ c l k v r,
      ForallTree (fun x _ => x < k) l
      → ForallTree (fun x _ => x > k) r
      → BST l
      → BST r
      → BST (tree c l k v r)

example : BST ex_tree := by
  constructor <;> constructor <;> constructor <;> constructor

example : BST ex_tree := by
  repeat' constructor

theorem empty_tree_BST {α : Type u} : BST (@empty α) := by
  constructor

/-
-/

theorem forallTree_imp {α : Type u} (P Q : Nat → α → Prop) t
    : ForallTree P t → (∀ k v, P k v → Q k v) → ForallTree Q t := by
  intro hp ha
  induction t with
  | empty => constructor
  | tree =>
    cases hp
    constructor <;> simp [*]

theorem forallTree_lt {α : Type u} (t : Tree α) k k'
    : ForallTree (fun x _ => x < k) t → k < k'
      → ForallTree (fun x _ => x < k') t := by
  intro h hlt
  apply forallTree_imp <;> try assumption
  omega

theorem forallTree_gt {α : Type u} (t : Tree α) k k'
    : ForallTree (fun x _ => x > k) t → k > k'
      → ForallTree (fun x _ => x > k') t := by
  intro h hgt
  apply forallTree_imp <;> try assumption
  omega

theorem balance_BST {α : Type u} c (l : Tree α) k vk (r : Tree α)
    : ForallTree (fun x _ => x < k) l
      -> ForallTree (fun x _ => x > k) r
      -> BST l
      -> BST r
      -> BST (balance c l k vk r) := by
  intro hlk hkr hbl hbr; simp
  split
  . constructor <;> assumption
  . split
    . -- we are in the case where `x` is left child of `y`
      cases l <;> repeat simp [*] at *
      rcases hbl with ⟨⟩ | ⟨_, _, _, _, _, hxy, hyc, hbx, hbc⟩
      rcases hlk with ⟨⟩ | ⟨_, _, _, _, _, hyz, hxz, hzc⟩
      rcases hbx with ⟨⟩ | ⟨_, _, _, _, _, hax, hxb, hba, hbb⟩
      rcases hxy with ⟨⟩ | ⟨_, _, _, _, _, hxy, hay, hby⟩
      rcases hxz with ⟨⟩ | ⟨_, _, _, _, _, haz, hxz, hbz⟩
      repeat' constructor <;> try assumption
      apply forallTree_gt <;> assumption
    . -- we are in the case where `y` is right child of `x`
      cases l <;> repeat simp [*] at *
      rcases hbl with ⟨⟩ | ⟨_, _, _, _, _, hax, hxy, hba, hby⟩
      rcases hlk with ⟨⟩ | ⟨_, _, _, _, _, hxz, haz, hyz⟩
      rcases hby with ⟨⟩ | ⟨_, _, _, _, _, hby, hyc, hbb, hbc⟩
      rcases hxy with ⟨⟩ | ⟨_, _, _, _, _, hxy, hxb, hxc⟩
      rcases hyz with ⟨⟩ | ⟨_, _, _, _, _, hyz, hbz, hcz⟩
      (repeat' constructor) <;> try assumption
      . apply forallTree_lt
        . exact hax
        . assumption
      . apply forallTree_gt <;> assumption
    . -- we are in the case where `y` is left child of `z`
      cases r <;> repeat simp [*] at *
      rcases hbr with ⟨⟩ | ⟨_, _, _, _, _, hyz, hzd, hby, hbd⟩
      rcases hkr with ⟨⟩ | ⟨_, _, _, _, _, hxz, hxy, hxd⟩
      rcases hby with ⟨⟩ | ⟨_, _, _, _, _, hby, hyc, hbb, hbc⟩
      rcases hxy with ⟨⟩ | ⟨_, _, _, _, _, hxy, hxb, hxc⟩
      rcases hyz with ⟨⟩ | ⟨_, _, _, _, _, hyz, hbz, hcz⟩
      (repeat' constructor) <;> try assumption
      . apply forallTree_lt <;> assumption
      . apply forallTree_gt
        . exact hzd
        . assumption
    . -- we are in the case where `z` is right child of `y`
      cases r <;> repeat simp [*] at *
      rcases hbr with ⟨⟩ | ⟨_, _, _, _, _, hby, hyz, hbb, hbz⟩
      rcases hkr with ⟨⟩ | ⟨_, _, _, _, _, hxy, hxb, hxz⟩
      rcases hbz with ⟨⟩ | ⟨_, _, _, _, _, hcz, hzd, hbc, hbd⟩
      rcases hxz with ⟨⟩ | ⟨_, _, _, _, _, hxz, hxc, hxd⟩
      rcases hyz with ⟨⟩ | ⟨_, _, _, _, _, hyz, hyc, hyd⟩
      repeat' constructor <;> try assumption
      apply forallTree_lt <;> assumption
    . constructor <;> assumption

/-
exercise (2-star)
Prove that `balance` preserves `ForallTree P`.
-/
theorem balanceP {α : Type u} (P : Nat → α → Prop) c (l : Tree α) k vk (r : Tree α)
    : ForallTree P l → ForallTree P r → P k vk
      → ForallTree P (balance c l k vk r) := by
  sorry

/-
exercise (2-star)
Prove that `ins` preserves `ForallTree P`.
Hint: proceed by induction on `t`.
Use `balanceP`.
-/
theorem insP {α : Type u} (P : Nat → α → Prop) (t : Tree α) k vk
    : ForallTree P t → P k vk
      → ForallTree P (ins k vk t) := by
  sorry

/-
exercise (3-star)
Prove that `ins` maintains `BST`.
Proceed by induction on `t`.
-/
theorem ins_BST {α : Type u} (t : Tree α) k vk : BST t → BST (ins k vk t) := by
  sorry

/-
exercise (2-star)
Prove that `insert` preserves `BST.
You do not need induction.
-/
theorem insert_BST {α : Type u} (t : Tree α) k vk
    : BST t → BST (insert k vk t) := by
  intro ht
  unfold insert
  unfold make_black
  split
  . constructor
  . have h : BST (ins k vk t) := by apply ins_BST; assumption
    simp [*] at h
    cases h
    constructor <;> assumption
  -- sorry

/-
## Verification

1. `lookup d k empty_tree = d`
2. `lookup d k (insert k vk t) = vk`
3. `lookup d k' (insert k vk t) = lookup d k' t       if k ≠ k'`
-/

theorem lookup_empty {α : Type u} (d : α) (k : Nat)
    : lookup d k empty_tree = d := by
  rfl

/-
exercise (4-star)
Prove that `balance` preserves the result of lookup on nonempty trees.
Use the same proof technique as in `balance_BST`.
-/
theorem balance_lookup {α : Type u} (d : α) c k k' (vk : α) l r
    : BST l → BST r
      → ForallTree (fun x _ => x < k) l → ForallTree (fun x _ => k < x) r
      → lookup d k' (balance c l k vk r) =
          if k' < k then lookup d k' l
          else if k' > k then lookup d k' r
          else vk := by
  sorry

/-
exercise (3-star)
Verify the second equation, though for `ins` rather than `insert`.
Proceed by induction on the evidence that `t` is a `BST`.
Note that precondition `BST t` will be essential in your proof, unlike the ordinary BST's we saw last time.
-/
theorem lookup_ins_eq {α : Type u} (d : α) t k vk
    : BST t → lookup d k (ins k vk t) = vk := by
  sorry

/-
exercise (3-star)
Verify the third equation, once again for `ins` instead of `insert`.
The same hints as for the second equation hold.
-/
theorem lookup_ins_neq {α : Type u} (d : α) t k vk
    : BST t → k ≠ k' → lookup d k' (ins k vk t) = lookup d k' t := by
  sorry

/-
## references
* [Software Foundations, Volume 3 Verified Functional Algorithms: Red-Black Trees](https://softwarefoundations.cis.upenn.edu/vfa-current/Redblack.html)
* [Theorem Proving in Lean 4: Tactics](https://leanprover.github.io/theorem_proving_in_lean4/tactics.html)
-/
