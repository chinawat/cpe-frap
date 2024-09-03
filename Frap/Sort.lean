/-
# Basic techniques for comparisons and permutations

Consider these algorithms and data structures:
* sort a sequence of numbers
* finite maps from numbers to (arbitrary-type) data
* finite maps from any ordered type to (arbitary-type) data
* priority queues: finding/deleting the highest number in a set

To prove the correctness of such programs, we need to reason about comparisons, and about whether two collections have the same contents.
In this lecture, we introduce some techniques for reasoning about
* less-than comparisons on natural numbers, and
* permutations (rearrangements of lists)

Later on, we'll apply these proof techniques to reasoning about algorithms and data structures.

## The less-than order on the natural numbers

In our proofs about searching and sorting algorithms, we often have to reason about the less-than order on natural numbers.
Recall that we write `x < y` for the proposition that `x` is less than `y`:
-/

#check 25 < 47

/-
Reasoning about inequalities by hand can be a little painful.
-/

example i j k : i < j → ¬(k - 3 ≤ j) → k > i := by
  simp
  intro h1 h2
  apply Nat.lt_trans
  . apply h1
  . apply Nat.lt_trans
    . apply h2
    . -- is `k-3` less than `k`?
      -- on the integers, sure
      -- but we're working with natural numbers, which trancate
      -- subtraction at zero
      sorry

example : ¬(∀ k, k - 3 < k) := by
  simp; exists 0

/-
Since subtraction is truncated, does the proposition above actually hold?
It does.
Let's try again, the hard way, to find the proof.
-/

example i j k : i < j → ¬(k - 3 ≤ j) → k > i := by
  simp
  intro h1 h2
  apply Nat.lt_trans
  . apply h1
  . apply Nat.lt_of_lt_of_le
    . apply h2
    . rw [← Nat.sub_zero k]
      apply Nat.sub_le_sub_left
      simp

/-
That was quite tedious.
Luckily, Lean provides a tactic called `omega` that is quite helpful.
Here's a much easier way.
-/

example i j k : i < j → ¬(k - 3 ≤ j) → k > i := by
  omega

/-
## Swapping

Consider trying to sort a list of natural numbers.
As a small piece of a sorting algorithm, we might need to swap the first two elements of a list if they are out of order.
-/

#print List

@[simp] def maybe_swap (al : List Nat) : List Nat :=
  match al with
  | a :: b :: ar => if a > b then b :: a :: ar else al
  | _ => al

example : maybe_swap [1, 2, 3] = [1, 2, 3] := by
  rfl

example : maybe_swap [3, 2, 1] = [2, 3, 1] := by
  rfl

/-
Applying `maybe_swap` twice should give the same result as applying it once.
That is, `maybe_swap` is _idempotent_.
-/

theorem maybe_swap_idempotent al
    : maybe_swap (maybe_swap al) = maybe_swap al := by
  cases al <;> try rfl
  rename_i a ar
  cases ar <;> try rfl
  rename_i b ar
  simp
  let h := Decidable.or_not_self (b < a)
  cases h
  . simp [*]; intro h'; omega
  . simp [*]

local macro "bcases" e:term : tactic =>
  `(tactic| let hcases := Decidable.or_not_self $e <;> cases hcases)

/-
## Permutations

Another useful fact about `maybe_swap` is that it doesn't add or remove elements from the list: it only reorders them.
That is, the output list is a permutation of the input.
List `al` is a _permutation_ of list `bl` if the elements of `al` can be reordered to get the list `bl`.
Note that reordering does not permit adding or removing duplicate elements.

We can define permutations inductively as follows.
-/

inductive Permutation {α : Type} : List α → List α → Prop :=
  | perm_nil : Permutation [] []
  | perm_skip x l l'
      : Permutation l l' → Permutation (x::l) (x::l')
  | perm_swap x y l : Permutation (y::x::l) (x::y::l)
  | perm_trans l l' l''
      : Permutation l l' → Permutation l' l''
        → Permutation l l''

open Permutation

/-
You might wonder, "is that really the right definition?"
And indeed, it's important that we get a right definition, because `Permutation` is going to be used in our specifications of searching and sorting algorithms.
If we have the wrong specification, then all our proofs of "correctness" will be useless.

It's not obvious that this is indeed the right specification of permutations.
(It happens to be, but that's not obvious.)
To gain confidence that we have the right specification, let's use it to prove some properties that permutations ought to have.
-/

theorem permutation_nil (l : List α) : Permutation [] l → l = [] := by
  generalize heq : [] = l₀
  intro h
  induction h <;> simp [*] at *

theorem permutation_nil_cons (l : List α) (x : α)
    : ¬ Permutation [] (x::l) := by
  generalize heq₁ : [] = l₀
  generalize heq₂ : x::l = l₁
  intro contra
  induction contra with simp [*] at *
  | perm_trans l' l'' l''' hp₁ hp₂ ih₁ ih₂ =>
    subst l' l'''
    apply ih₂
    apply Eq.symm
    apply permutation_nil
    exact hp₁

/-
Permutation over lists is an equivalence relation.
-/

theorem permutation_refl (l : List α) : Permutation l l := by
  induction l with
  | nil => exact perm_nil
  | cons a al ih => apply perm_skip; exact ih

theorem permutation_symm (l l' : List α)
    : Permutation l l' → Permutation l' l := by
  intro h
  induction h with
  | perm_nil => exact perm_nil
  | perm_skip => apply perm_skip; assumption
  | perm_swap => apply perm_swap
  | perm_trans => apply perm_trans <;> assumption

theorem permutation_trans (l l' l'' : List α)
    : Permutation l l' → Permutation l' l''
      → Permutation l l'' := by
  apply perm_trans

/-
Compatibility with other operations on lists
-/

theorem permutation_app_tail (l l' tl : List α)
    : Permutation l l' → Permutation (l++tl) (l'++tl) := by
  intro h
  induction h with try simp
  | perm_nil => apply permutation_refl
  | perm_skip => apply perm_skip; assumption
  | perm_swap => apply perm_swap
  | perm_trans => apply perm_trans <;> assumption

theorem permutation_app_head (l tl tl' : List α)
    : Permutation tl tl' → Permutation (l++tl) (l++tl') := by
  intro h
  induction l with simp
  | nil => exact h
  | cons a al ih => apply perm_skip; exact ih

theorem permutation_app (l m l' m' : List α)
    : Permutation l l' → Permutation m m'
      → Permutation (l++m) (l'++m') := by
  intro h₁ h₂
  apply perm_trans
  . apply permutation_app_tail; assumption
  . apply permutation_app_head; assumption

theorem permutation_add_inside a (l l' tl tl' : List α)
    : Permutation l l' → Permutation tl tl'
      → Permutation (l ++ a :: tl) (l' ++ a :: tl') := by
  intro h₁ h₂
  apply permutation_app
  . assumption
  . apply perm_skip; assumption

theorem permutation_cons_append (l : List α) x
    : Permutation (x :: l) (l ++ [x]) := by
  induction l with simp
  | nil => apply permutation_refl
  | cons =>
    apply perm_trans
    . apply perm_swap
    . apply perm_skip; assumption

theorem permutation_app_comm (l l' : List α)
    : Permutation (l ++ l') (l' ++ l) := by
  induction l with simp
  | nil => apply permutation_refl
  | cons a al ih =>
    -- a :: (al ++ l')
    -- al ++ l' ++ [a]
    -- l' ++ al ++ [a]
    -- l' ++ (al ++ [a])
    -- l' ++ a :: al
    apply perm_trans
    . apply permutation_cons_append
    . apply perm_trans
      . apply permutation_app_tail; exact ih
      . rw [List.append_assoc]
        apply permutation_app_head
        apply permutation_symm
        apply permutation_cons_append

theorem permutation_app_rot (l₁ l₂ l₃ : List α)
    : Permutation (l₁ ++ l₂ ++ l₃) (l₂ ++ l₃ ++ l₁) := by
  rw [List.append_assoc]
  apply permutation_app_comm

theorem permutation_app_swap_app (l₁ l₂ l₃ : List α)
    : Permutation (l₁ ++ l₂ ++ l₃) (l₂ ++ l₁ ++ l₃) := by
  apply permutation_app_tail
  apply permutation_app_comm

theorem permutation_app_middle (l l₁ l₂ l₃ l₄ : List α)
    : Permutation (l₁ ++ l₂) (l₃ ++ l₄)
      → Permutation (l₁ ++ l ++ l₂) (l₃ ++ l ++ l₄) := by
  intro h
  -- l₁ ++ l ++ l₂
  -- l ++ l₁ ++ l₂
  -- l ++ (l₁ ++ l₂)
  -- l ++ (l₃ ++ l₄)
  -- l ++ l₃ ++ l₄
  -- l₃ ++ l ++ l₄
  apply perm_trans
  . apply permutation_app_tail
    apply permutation_app_comm
  . rw [List.append_assoc]
    apply perm_trans
    . apply permutation_app_head; exact h
    . rw [← List.append_assoc]
      apply permutation_app_tail
      apply permutation_app_comm

theorem permutation_cons_app (l l₁ l₂ : List α)
    : Permutation l (l₁ ++ l₂)
      → Permutation (a :: l) (l₁ ++ a :: l₂) := by
  intro h
  -- a :: l
  -- a :: (l₁ ++ l₂)
  -- l₁ ++ l₂ ++ [a]
  -- l₁ ++ (l₂ ++ [a])
  -- l₁ ++ a :: l₂
  apply perm_trans
  . apply perm_skip; exact h
  . apply perm_trans
    . apply permutation_cons_append
    . rw [List.append_assoc]
      apply permutation_app_head
      apply permutation_symm
      apply permutation_cons_append

theorem permutation_middle (l₁ l₂ : List α) a
    : Permutation (a :: l₁ ++ l₂) (l₁ ++ a :: l₂) := by
  apply permutation_cons_app
  apply permutation_refl

theorem permutation_middle2 (l₁ l₂ l₃ : List α) a b
    : Permutation (a :: b :: l₁ ++ l₂ ++ l₃) (l₁ ++ a :: l₂ ++ b :: l₃) := by
  simp
  apply permutation_cons_app
  -- b ++ (l₁ ++ (l₂ ++ l₃))
  -- l₁ ++ b :: (l₂ ++ l₃)
  -- l₁ ++ (l₂ ++ b :: l₃)
  apply perm_trans
  . apply permutation_cons_app
    apply permutation_refl
  . apply permutation_app_head
    apply permutation_cons_app
    apply permutation_refl

theorem permutation_elt (l₁ l₂ l₁' l₂' : List α) a
    : Permutation (l₁ ++ l₂) (l₁' ++ l₂')
      → Permutation (l₁ ++ a :: l₂) (l₁' ++ a :: l₂') := by
  -- l₁ ++ a :: l₂
  -- a :: l₁ ++ l₂
  -- a :: l₁' ++ l₂'
  -- l₁' ++ a :: l₂'
  intro h
  apply perm_trans
  . apply permutation_symm
    apply permutation_cons_app
    apply permutation_symm
    exact h
  . apply permutation_cons_app
    apply permutation_refl

theorem permutation_length (l l' : List α)
    : Permutation l l' → List.length l = List.length l' := by
  intro h
  induction h with try simp
  | perm_skip => assumption
  | perm_trans => apply Eq.trans <;> assumption

theorem permutation_nil_app_cons (l l' : List α) x
  : ¬ Permutation [] (l++x::l') := by
  intro contra
  have contra' : @List.length α [] = List.length (l ++ x :: l') := by
    apply permutation_length; exact contra
  simp [*] at *
  omega

theorem permutation_cons_inv (l l' : List α) a
    : Permutation (a::l) (a::l') → Permutation l l' := by
  -- the proof of this theorem requires another fact
  -- which is currently out of the scope of this course
  sorry

theorem permutation_length_1_inv a (l : List α)
    : Permutation [a] l → l = [a] := by
  generalize heq₁ : [a] = l₁
  intro h
  induction h with (simp [*] at *)
  | perm_skip x l₁ l₂ h₁ =>
    obtain ⟨_, h'⟩ := heq₁
    rw [← h']; rw [← h'] at h₁
    apply permutation_nil; assumption

/-
exercise (2-star)
Prove that [1, 1] is not a permutation of [1, 2].
Hint: use `permutation_cons_inv` and `permutation_length_1_inv` given above.
-/

example : ¬ Permutation [1, 1] [1, 2] := by
  sorry

/-
### Correctness of `maybe_swap`

Now we can prove that `maybe_swap` is a permutation: it reorders elements but does not add or remove any.
-/

theorem maybe_swap_perm al : Permutation al (maybe_swap al) := by
  unfold maybe_swap
  cases al with simp
  | nil => exact perm_nil
  | cons a ar =>
    split
    . rename_i a' b' _ _
      cases ar <;> simp at *
      bcases b' < a' <;> simp [*] at *
      . apply perm_swap
      . apply permutation_refl
    . apply permutation_refl

/-
And we can prove that `maybe_swap` permutes elements such that the first is less than or equal to the second.
-/

@[simp] def first_le_second (al : List Nat) : Prop :=
  match al with
  | a :: b :: _ => a ≤ b
  | _ => True

theorem maybe_swap_correct al
    : Permutation al (maybe_swap al)
      ∧ first_le_second (maybe_swap al) := by
  constructor
  . apply maybe_swap_perm
  . unfold maybe_swap
    split <;> simp
    split <;> try simp
    rename_i h
    split at h <;> simp at * <;> omega

#check List.all
open List

/-
exercise (3-star)
Prove this lemma by induction.
You will need to decide what to induct on: `al`, `bl`, `Permutation al bl`, and `all f al` are possibilities.
-/

theorem all_perm {α} (f : α → Bool) al bl
    : Permutation al bl → all al f → all bl f := by
  sorry

/-
## Summary: comparisons and permutations

To prove correctness of algorithms for sorting and searching, we'll reasong about comparisons and permutations using tools developed here.
The `maybe_swap` program is a tiny little example of a sorting program.
The proof style in `maybe_swap_correct` will be applied (at a larger scale) in what's to come.

# Insertion sort

Sorting can be done in expected O(n lg n) time by various algorithms (quicksort, merge sort, heap sort, etc.).
But for smallish inputs, a simple quadratic-time algorithm such as insertion sort can actually be faster.
It's certainly easier to implement and to verify.

## The insertion-sort program

Insertion sort is usually presented as an imperative program operating on arrays.
But it works just as well as a functional program operating on linked lists.
-/

-- `insert i l` inserts `i` into its sorted place in list `l`.
-- precondition: `l` is sorted

@[simp] def insert (i : Nat) (l : List Nat) :=
  match l with
  | [] => [i]
  | a :: as => if i ≤ a then i :: a :: as else a :: insert i as

@[simp] def sort (l : List Nat) : List Nat :=
  match l with
  | [] => []
  | a :: as => insert a (sort as)

example : sort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]
    = [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9] := by
  rfl

/-
The arrays-and-swaps model of sorting that we usually see in imperative programs is not the only one possible.
In the definitions above, we are writing _functional programs_, where our sequences are (typically) represented as linked lists, and where we do _not_ destructively splice elements into those lists.

As usual with functional lists, the output of `sort` may share memory with the input.
For example:
-/

#eval insert 7 [1, 3, 4, 8, 12, 14, 18]

/-
The tail of this list, `[12, 14, 18]`, is not disturbed or rebuilt by the `insert` algorithm.
The head `1 :: 3 :: 4 :: 7 :: ...` contains new neodes constructed by `insert`.
THe first three nodes of the old list, `1 :: 3 :: 4 ...`, will likely be garbage-collected if no other data structure is still pointing at them.
Thus, in this typical case,
* time cose = 4X
* space cose = (4-3)Y = Y
where X and Y are constants, independent of the length of the tail.
The value Y is the number of bytes in one list node: 2 to 4 words, depending on how the implementation handles constructor-tags.
We write (4-3) to indicate that four list nodes are constructed, while three list nodes become eligible for garbage collection.

We will not prove such things about the time and spece cose, but they are true anyway, and we should keep them in consideration.

## Specification of correctness

A sorting algorithm must rearrange the elements into a list that is totally ordered.
There are many ways we might express that idea formally in Lean.
One is with an inductively-defined relation that says:
* The empty list is sorted.
* Any single-element list is sorted.
* For any two adjacent elements, they must be in proper order.
-/

inductive Sorted : List Nat → Prop :=
  | sorted_nil : Sorted []
  | sorted_1 x : Sorted [x]
  | sorted_cons x y l :
      x ≤ y → Sorted (y :: l) → Sorted (x :: y :: l)

open Sorted

/-
This definition might not be the most obvious.
Another definition, perhaps more familiar, might be: for any two elements of the list (regardless of whether they are adjacent), they should be in the proper order.
Let's try formalizing that.

We can think in terms of indices into a list `lst`, and say: for any valid indices `i` and `j`, if `i < j` then `index lst i ≤ index lst j`, where `index lst n` means the element of `lst` at index `n`.
Unfortunately, formalizing this idea becomes messy, because any Lean function implementing `index` must be total: it must return some result even if the index is out of range of the list.
The Lean standard library contains many such functions, two of which are as follows:
-/

#check getD
#check get?
#print Option

/-
These two functions ensure totally in different ways:
* `getD` takes an additional argument of type A—a _default_ value—to be returned if the index is out of range, whereas
* `get?` returns `some v` if the index is in range and `none` (an error) otherwise.

if we use `nth`, we must ensure that indices are in range:
-/

def sorted'' (al : List Nat) := ∀ i j,
  i < j → j < length al → getD al i 0 ≤ getD al j 0

/-
The choice of default value, here 0, is unimportant, because it will never be returned for the `i` and `j` we pass.

If we use `get?`, we must add additional antecedents:
-/

def sorted' (al : List Nat) := ∀ i j iv jv,
  i < j → get? al i = some iv → get? al j = some jv → iv ≤ jv

/-
Here, the validity of `i` and `j` are implicit in the fact that we get `some` results back from each call to `get?`.

All three definitions of sortedness are reasonable.
In practice, `sorted'` is easier to work with than `sorted''` because it doesn't need to mention the `length` function.
And `Sorted` is easiest, because it doesn't need to mention indices.

Using `Sorted`, we specify what it means to be a correct sorted algorithm:
-/

def is_a_sorting_algorithm (f : List Nat → List Nat) :=
  ∀ al, Permutation al (f al) ∧ Sorted (f al)

/-
Function `f` is a correct sorting algorithm if `f al` is `Sorted` and is a permutation of its input.

## Proof of correctness

In the following exercises, you will prove the correctness of insertion sort.
-/

/-
exercise (3-star)
Prove that insertion maintains sortedness.
-/

theorem insert_sorted a l : Sorted l → Sorted (insert a l) := by
  intro S
  induction S with simp at *
  | _ => sorry

/-
exercise (2-star)
Using `insert_sorted`, prove the insertion sort makes a list sorted.
-/

theorem sort_sorted l : Sorted (sort l) := by
  sorry

/-
exercise (3-star)
The following lema will be useful soon as a helper.
-/

theorem insert_perm x l : Permutation (x :: l) (insert x l) := by
  sorry

/-
exercise (3-star)
Prove that `sort` is a permutation, using `insert_perm`.
-/

theorem sort_perm l : Permutation l (sort l) := by
  sorry

/-
exercise (1-star)
Finish the proof of correctness!
-/

theorem insertion_sort_correct : is_a_sorting_algorithm sort := by
  sorry

/-
## Validating the specification (advanced)

You can prove that a program satisfies a specification, but how can you prove that you have the right specification?
Actually, you cannot.
The specification is an informal requirement in your mind.
As Alan Perlis quipped, "One can't proceed from the informal to the formal by formal means."

But one way to build confidence in a specification is to state it in two different ways, then prove they are equivalent.
-/

/-
exercise (4-star)
Hint: Instead of doing induction on the list `al`, do induction on the sortedness of `al`.
This proof is a bit tricky, so you may have to think about how to approach it, and try out one or two different ideas.
-/

theorem sorted_sorted' al : Sorted al → sorted' al := by
  sorry

/-
exercise (3-star)
Here, you can't do induction on the sortedness of the list, because `sorted'` is not an inductive predicate.
But the proof is less tricky than the previous.
-/

theorem sorted'_sorted al : sorted' al → Sorted al := by
  sorry

/-
## references
* [Software Foundations, Volume 3 Verified Functional Algorithms: Basic Techniques for Comparisons and Permutations](https://softwarefoundations.cis.upenn.edu/vfa-current/Perm.html)
* [The Coq Proof Assistant, Standard Library: List permutations as a composition of adjacent transpositions](https://coq.inria.fr/doc/V8.19.2/stdlib//Coq.Sorting.Permutation.html#Permutation)
* [GitHub: coq/theories/Sorting/Permutation.v](https://github.com/coq/coq/blob/master/theories/Sorting/Permutation.v)
* [Software Foundations, Volume 3 Verified Functional Algorithms: Insertion Sort](https://softwarefoundations.cis.upenn.edu/vfa-current/Sort.html)
-/
