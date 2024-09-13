import Frap.Sort

/-
# Insertion sort verified with multisets

Our specification of `sorted` in [Sort] was based in part on permutations, which enabled us to express the idea that sorting rearranges list elements but does not add or remove any.

Another way to express that idea is to use _multisets_, a.k.a bags.
A _set_ is like a list in which element order is irrelevant, and in which no duplicate elements are permitted.
That is, an element can either be _in_ the set or not in the set, but it can't be in the set multiple times.
A _multiset_ relaxes that restriction: an element can be in the multiset multiple times.
The number of times the element occurs in the multiset is the element's _multiplicity_.

For example:
* {1, 2} is a set, and is the same as set {2, 1}.
* [1, 1, 2] is a list, and is different from list [2, 1, 1].
* {1, 1, 2} is a multiset and is the same as multiset {2, 1, 1}.

In this lecture, we'll explore using multisets to specify sortedness.

## Multisets

We will represent multisets as functions: if `m` is a multiset, then `m n` will be the multiplicity of `n` in `m`.
Since we are sorting lists of natural numbers, the type of multisets would be `Nat → Nat`.
The input is the value, the output is its multiplicity.
To help avoid confusion between those two uses of `Nat`, we'll introduce a synonym, `Value`.
-/

open Nat

abbrev Value := Nat
abbrev Multiset := Value → Nat

/-
The `empty` multiset has multiplicity `0` for every value.
-/

@[simp] def empty : Multiset :=
  fun _ => 0

/-
Multiset `singleton v` contains only `v`, and exactly once.
-/

@[simp] def singleton (v : Value) : Multiset :=
  fun x => if x == v then 1 else 0

/-
The union of two multisets is their _pointwise_ sum.
-/

@[simp] def union (a b : Multiset) : Multiset :=
  fun x => a x + b x

/-
exercise (1-star)
Prove that multiset union is associative.

To prove that one multiset equals another, we use the axiom of functional extensionality, which was introduced in [Hoare].
We begin the proof below by using Lean's tactic `funext`, which applies that axiom.
-/

theorem union_assoc a b c : union a (union b c) = union (union a b) c := by
  funext x
  sorry

/-
exercise (1-star)
Prove that multiset union is commutative.
-/

theorem union_comm a b : union a b = union b a := by
  sorry

/-
exercise (2-star)
Prove that the multisets in a nested union can be swapped.
You do not need `funext` if you use the previous two lemmas.
-/

theorem union_swap a b c : union a (union b c) = union b (union a c) := by
  sorry

/-
Note that this is not an efficient implementation of multisets.
We wouldn't want to use it for programs with high performance requirements.
But we are using multisets for specifications, not for programs.
We don't intend to build large multisets, only to use them in verify in algorithms such as insertion sort.
So this inefficiency is not a problem.

## Specification of sorting

A sorting algorithm must rearrange the elements into a list that is totally ordered.
Using multisets, we can restate that as: the algorithm must product a list _with the same multiset of values_, and this list must be totally ordered.
Let's formalize that idea.

The _contents_ of a list are the elements it contains, without any notion of order.
Function `contents` extracts the contents of a list as a multiset.
-/

open List

@[simp] def contents (al : List Value) : Multiset :=
  match al with
  | [] => empty
  | a :: bl => union (singleton a) (contents bl)

/-
The insertion-sort program `sort` from [Sort] preserves the contents of a list.
Here's an example of that:
-/

example : contents (sort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5])
    = contents [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] := by
  funext x
  simp
  repeat' split
  all_goals rfl
  -- why does this work?
  -- try it step by step, without `repeat'`

/-
A sorting algorithm must preserve contents and totally order the list.
-/

def is_a_sorting_algorithm' (f : List Nat → List Nat) :=
  ∀ al, contents al = contents (f al) ∧ Sorted (f al)

/-
That definition is similar to `is_a_sorting_algorithm` for [Sort], except that we're not using `contents` instead of `Permutation`.

## Verification of insertion sort

The following series of exercises will take you through a verification of insertion sort using multisets.
-/

/-
exercise (3-star)
Prove that insertion sort's `insert` function produces the same contents as merely prepending the inserted elements to the front of the list.

Proceed by induction.
You do not need `funext` if you make use of the above lemmas about `union`.
-/

theorem insert_contents x l : contents (insert x l) = contents (x :: l) := by
  sorry

/-
exercise (2-star)
Prove that insertion sort preserves contents.
Proceed by induction.
Make use of `insert_contents`.
-/

theorem sort_contents l : contents l = contents (sort l) := by
  sorry

/-
exercise (1-star)
Finish the proof of correctness!
-/

theorem insertion_sort_correct' : is_a_sorting_algorithm' sort := by
  sorry

/-
## Equivalence of permutation and multiset specifications

WE have developed two specifications of sorting, one based on permutations (`is_a_sorting_algorithm`) and one based on multisets (`is_a_sorting_algorithm'`).
These two specifications are actually equivalent, which will be the final theorem in this part.

One reason for that equivalence is that permutations and multisets are closely related.
We'll begin by proving:
  `Permutation al bl ↔ contents al = contents bl`
The forward direction is relatively easy, but the backward direction is surprisingly difficult.

### The forward direction
-/

open Permutation

/-
exercise (3-star)
The forward direction is the easier one.
Proceed by induction on the evidence for `Permutation al bl`.
-/

theorem perm_contents al bl
    : Permutation al bl → contents al = contents bl := by
  sorry

/-
### The backward direction (advanced)

The backward direction is surprisingly difficult.
This proof approach is due to Zhong Sheng Hu.
The first three lemmas are used to prove the fourth one.
-- Don't forget that `union`, `singleton`, and `empty` must be explicitly unfolded to access their definitions.
-/

/-
exercise (2-star)
-/

theorem contents_nil_inv l : (∀ x, 0 = contents l x) → l = [] := by
  sorry

/-
exercise (3-star)
-/

theorem contents_cons_inv l x n
    : succ n = contents l x
      → ∃ l₁ l₂, l = l₁ ++ x :: l₂ ∧ contents (l₁ ++ l₂) x = n := by
  sorry

/-
exercise (2-star)
-/

theorem contents_insert_other l₁ l₂ x y
    : y ≠ x → contents (l₁ ++ x :: l₂) y = contents (l₁ ++ l₂) y := by
  sorry

/-
exercise (3-star)
-/

theorem contents_perm al bl
    : contents al = contents bl → Permutation al bl := by
  intro h₀
  have h : ∀ x, contents al x = contents bl x := by
    rw [h₀]; simp
  clear h₀
  induction al generalizing bl with simp at *
  | _ => sorry

/-
### The main theorem

With both directions proved, we can establish the correspondence between multisets and permutations.
-/

/-
exercise (1-star)
Use `contents_perm` (even if you haven't proved it) and `perm_contents` to quickly prove the next theorem.
-/

theorem same_contents_iff_perm al bl
    : contents al = contents bl ↔ Permutation al bl := by
  sorry

/-
Therefore, the two specifications are equivalent.
-/

theorem sort_specifications_equivalent sort
    : is_a_sorting_algorithm sort ↔ is_a_sorting_algorithm' sort := by
  sorry

/-
# Selection sort

The specification for sorting algorithms we developed in [Sort] can also be used to verify selection sort.
The selection sort program itself is interesting, because writing it in Lean will cause us to explore a new technique for convincing Lean that a function terminates.

Note on efficiency: selection sort, like insertion sort, runs in quadratic time.
But selection sort typically makes many more comparisons than insertion sort, so insertion sort is usually preferable for sorting small inputs.
Selection sort can beat insertion sort if the cost of swapping elements is vastly higher than the cost of comparing them, but that doesn't apply to functional lists.

## The selection-sort program

Selection sort on lists is more challenging to code in Lean than insertion sort was.
First, we write a helper function to select the smallest element.
-/

-- `select x l` is `(y, l')`, where `y` is the smallest element of `x :: l`,
-- and `l'` is all the remaining elements of `x :: l`.

@[simp] def select (x : Nat) (l : List Nat) : Nat × List Nat :=
  match l with
  | [] => (x, [])
  | hd :: tl =>
    if x <= hd
    then let (j, l') := select x tl; (j, hd :: l')
    else let (j, l') := select hd tl; (j, x :: l')

/-
Selection sort should repeatedly extract the smallest element and make a list of the results.
But the following attempted definition fails:
-/

-- def selsort (l : List Nat) : List Nat :=
--   match l with
--   | [] => []
--   | x :: tl => let (y, tl') := select x tl; y :: selsort tl'

/-
The error message is
```
  fail to show termination for
    selsort
  with errors
  argument #1 was not used for structural recursion
    failed to eliminate recursive application
      selsort tl'

  structural recursion cannot be used
```

Lean rejects `selsort` because it doesn't satisfy Lean's requirements for termination.
The problem is that the recursive call in `selsort` is not _structurally decreasing_: the argument `tl'` at the call site is not know to be a smaller part of the original input `l`.
Indeed, `select` might not return such a list.
For example, `select 1 [0, 2]` is `(0, [1, 2])`, but `[1, 2]` is not a part of `[0, 2]`.

There are several ways to fix this problem.
One programming pattern is to provide _fuel_: an extra argument that has no use in the algorithm except to bound the amount of recursion.
The `n` argument, below, is the fuel.
When it reaches `0`, the recursion terminates.
-/

def selsort (l : List Nat) (n : Nat) : List Nat :=
  match l, n with
  | _, 0 => []  -- ran out of fuel
  | [], _ => []
  | x :: tl, succ n' => let (y, tl') := select x tl; y :: selsort tl' n'

/-
If fuel runs out, we get the wrong output.
-/

#eval selsort [3, 1, 4, 1, 5] 3

example : selsort [3, 1, 4, 1, 5] 3 ≠ [1, 1, 3, 4, 5] := by
  intro contra; cases contra

/-
Extra fuel isn't a problem though.
-/

example : selsort [3, 1, 4, 1, 5] 10 = [1, 1, 3, 4, 5] := by
  rfl

/-
The exact amount of fuel needed is the length of the input list.
So that's how we define `selection_sort`:
-/

def selection_sort (l : List Nat) : List Nat := selsort l (length l)

example : selection_sort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]
    = [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9] := by
  rfl

/-
## Proof of correctness

In the following exercises, you will prove that selection sort is a correct sorting algorithm.
You might wish to keep track of the lemmas you have proved, so that you can spot places to use them later.
-/

/-
exercise (2-star); worked in class
Prove that `select` returns a permutation of its input.
Proceed by induction on `l`, generalizing `x`, `y`, and `r`.
-/

theorem select_perm x l y r
    : select x l = (y, r) → Permutation (x :: l) (y :: r) := by
  intro h
  induction l generalizing x y r with simp at *
  | nil =>
    obtain ⟨⟩ := h
    subst y r
    apply permutation_refl
  | cons a as ih =>
    split at h
    . obtain ⟨⟩ := h
      have ih' : Permutation (x :: as)
          (Prod.fst (select x as) :: Prod.snd (select x as)) := by
        apply ih; simp
      -- x :: a :: as
      -- a :: x :: as
      -- a :: y :: r
      -- y :: a :: r
      apply perm_trans
      . apply perm_swap
      . apply perm_trans
        . apply perm_skip; exact ih'
        . apply perm_swap
    . obtain ⟨⟩ := h
      have ih' : Permutation (a :: as)
          (Prod.fst (select a as) :: Prod.snd (select a as)) := by
        apply ih; simp
      -- x :: a :: as
      -- x :: y :: r
      -- y :: x :: r
      -- a :: x :: as
      apply perm_trans
      . apply perm_skip; exact ih'
      . apply perm_swap

/-
exercise (1-star)
Prove that `select` returns a list that has the correct length.
You can do this without induction if you make use of `select_perm`.
-/

theorem select_rest_length x l y r
    : select x l = (y, r) → length l = length r := by
  sorry

/-
exercise (3-star)
Prove that if you provide sufficient fuel, `selsort` produces a permutation.
Proceed by induction on `n`.
-/

theorem selsort_perm n l : length l = n → Permutation l (selsort l n) := by
  sorry

/-
exercise (1-star)
Prove that `selection_sort` produces a permutation.
-/

theorem selection_sort_perm l : Permutation l (selection_sort l) := by
  sorry

/-
exercise (2-star)
Prove that the first component of `select x _` is no bigger than `x`.
Proceed by induction on `al`.
-/

theorem select_fst_leq al bl x y : select x al = (y, bl) → y ≤ x := by
  sorry

/-
To represent the concept of comparing a number to a list, we introduce a new notation.
-/

def le_all (x : Nat) (xs : List Nat) := List.all xs (fun y => x ≤ y)

/-
exercise (1-star)
Prove that if `y` is no more than any of the elements of `lst` and if `n` is in `lst`, then `y` is no more than `n`.
-/

theorem le_all__le_one lst y n : le_all y lst → elem n lst → y ≤ n := by
  sorry

/-
exercise (2-star)
Prove that the first component of `select _ _` is no bigger than any of the elements in the second component.
Prove by induction on `al`.
-/

theorem select_smallest al bl x y : select x al = (y, bl) → le_all y bl := by
  sorry

/-
exercise (2-star)
Prove that the element returned by `select` must be one of the elements in its output.
Proceed by induction on `al`.
-/

theorem select_in al bl x y : select x al = (y, bl) → elem y (x :: al) := by
  sorry

/-
exercise (3-star)
Prove that adding an element to the beginning o a selection-sorted list maintains sortedness, as long as the element is small enough and enough fuel is provided.
No induction is needed.
-/

theorem cons_of_small_maintains_sort bl y n
    : n = length bl → le_all y bl → Sorted (selsort bl n)
      → Sorted (y :: selsort bl n) := by
  sorry

/-
exercise (2-star)
Prove that `selsort` produces a sorrted list when given sufficient fuel.
Proceed by induction on `n`.
This proof will make use of a few previous lemmas.
-/

theorem selsort_sorted n al : length al = n → Sorted (selsort al n) := by
  sorry

/-
exercise (1-star)
Prove that `selection_sort` produces as sorted list.
-/

theorem selection_sort_sorted al : Sorted (selection_sort al) := by
  sorry

/-
exercise (1-star)
Finish the proof of correctness.
-/

theorem selection_sort_is_correct : is_a_sorting_algorithm selection_sort := by
  sorry

/-
## Selection sort with multisets (optional)

Let's prove the correctness of `selection_sort` using multisets instead of premutations.
-/

/-
exercise (3-star)
-/

theorem select_contents al bl x y
    : select x al = (y, bl)
      → union (singleton x) (contents al) = union (singleton y) (contents bl) := by
  sorry

/-
exercise (3-star)
-/

theorem selection_sort_contents n l
    : length l = n → contents l = contents (selection_sort l) := by
  sorry

/-
exercise (1-star)
-/

theorem selection_sort_correct' : is_a_sorting_algorithm' selection_sort := by
  sorry

/-
## references
* [Software Foundations, Volume 3 Verified Functional Algorithms: Insertion Sort Verified with Multisets](https://softwarefoundations.cis.upenn.edu/vfa-current/Multiset.html)
* [Software Foundations, Volume 3 Verified Functional Algorithms: Selection Sort](https://softwarefoundations.cis.upenn.edu/vfa-current/Selection.html)
-/
