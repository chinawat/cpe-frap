/-
# Number representations and efficient lookup tables

One advantage of imperative programs is that they can do _indexed array update_ in constant time, while functional programs cannot.
As a result, purely functional algorithms sometimes suffer from an asymptotic slowdown of order log N compared to imperative algorithms.

Let's take an example.
Devise an algorithm for detecting duplicate values in a sequence of N integers, each in the range 0..2N.
As an imperative program, there's a very simple linear-time algorithm.
```
  collisions = 0;
  for (i = 0; i < 2N; i++)
    a[i] = 0;
  for (j = 0; j < N; j++) {
    i = input[j];
    if (a[i] != 0)
      collisions++;
    a[i] = 1;
  }
  return collisions;
```

In a functional program, we must replace `a[i]=1` with the update of a finite map.
If we use an inefficient implementation of maps, each lookup and update will take (worst-case) linear time, and the whole algorithm is quadratic time.
If we use balanced binary search tree (e.g., red-black tree), each lookup and update will take (worst-case) log N time, and the whole algorithm takes N log N.
Comparing O(N log N) to O(N), we see that there is a log N asymptotic penalty for using a functional implementation of finite maps.
This penalty arises not only in this "duplicates" algorithm, but in any algorithm that relies on random access in arrays.

Let's examine an approach that uses a construction in Lean of arbitrary-precision binary numbers, with (log N)-time addition, subtraction, and comparison.

## A simple program that's way too slow
-/

abbrev total_map α := Nat → α

def update (t : total_map α) (k : Nat) (v : α) : total_map α :=
  fun x => if x == k then v else t x

namespace VerySlow

def loop (input : List Nat) (c : Nat) (table : Nat → Bool) : Nat :=
  match input with
  | [] => c
  | a::al => if table a then loop al (c+1) table
                        else loop al c (update table a True)

def collisions (input : List Nat) : Nat :=
  loop input 0 (fun _ => False)

example : collisions [3, 1, 4, 1, 5, 9, 2, 6] = 1 := by
  rfl

/-
This program takes quadratic time, O(N²).
Let's assume that there are few duplicates, or none at all.
There are N iterations of `loop`, each iteration does a `table` lookup, most iterations do an `update` as well, and those operations each do up to `N` comparisons.
The average length of the `table` (the number of elements) averages only N/2, and (if there are few duplicates) the lookup will have to traverse the entire list, so really in each iteration there will be only `N/2` comparisons instead of `N`, but in asymptotic analysis we ignore the constant factors.
-/

#print Nat

/-
Remember, `Nat` is a unary representation, with a number of `succ` constructors proportional to the number being represented!
-/

end VerySlow

/-
## Efficient positive numbers

We can do better; we _must_ do better.
We use a binary representation (not unary), so that operations such as `plus` and `leq` take time linear in the number of bits, i.e., logarithmic in the value of the numbers.

We start with positive numbers.
-/

section Integers

inductive Positive : Type :=
  | xI : Positive → Positive
  | xO : Positive → Positive
  | xH : Positive

open Positive

/-
A positive number is either
* 1, that is, `xH`
* 0+2n, that is, `xO n`
* 1+2n, that is, `xI n`

For example, ten is 0+2(1+2(0+2(1)))
-/

def ten := xO (xI (xO xH))

/-
To interpret a `Positive` number as a `Nat`,
-/

def positive2nat (p : Positive) : Nat :=
  match p with
  | xI q => 1 + 2 * positive2nat q
  | xO q => 0 + 2 * positive2nat q
  | xH => 1

#eval positive2nat ten

/-
We can read the binary representation of a positive number as the _backwards_ sequence of `xO` (meaning 0), and `xI`/`xH` (meaning 1).
Thus, ten is 1010 in binary.
-/

def print_in_binary (p : Positive) : List Nat :=
  match p with
  | xI q => print_in_binary q ++ [1]
  | xO q => print_in_binary q ++ [0]
  | xH => [1]

#eval print_in_binary ten

/-
Why are we using positive numbers anyway?
The answer is that it's highly inconvenient to have number systems with several different representation of the same number.
For one thing, we don't want to worry about 00110=110.
Then, when we extend this to the integers, with a "minus sign", we don't have to worry about -0 = +0.

To find the successor of a binary number, i.e., to increment, we work from low-order to high-order, until we hit a zero bit.
-/

def succ x :=
  match x with
  | xI p => xO (succ p)
  | xO p => xI p
  | xH => xO xH

/-
To add binary numbers, we work from low-order to high-order, keeping track of the carry.
-/

/-
Integer type can then be constructed from positive numbers:
-/

inductive Z : Type :=
  | Z₀ : Z
  | Zpos : Positive → Z
  | Zneg : Positive → Z

/-
We can construct efficient (log N time) algorithms for operations on Z: `add`, `subtract`, `compare`, and so on.
These algorithms call upon the efficient algorithms for `Positive`s.
-/

end Integers

/-
## Tries: efficient lookup tables on positive binary numbers

Binary search trees are nice because they can implement lookup tables from _any_ totally ordered type to any other type.
But when the type of keys is known specifically to be (small-to-medium size) integers, then we can use a more specialized representation.

By analogy, in imperative programming languages (C, Java), when the index of a table is the integers in a certain range, you can use arrays.
When the keys are not integers, you have to use something like hash tables or binary search trees.

A _trie_ is a tree in which the edges are labeled with leters from an alphabet, and you look up a word by following edges labeled by successive letters of the word.
In fact, a trie is a special case of a deterministic finite automaton (DFA) that happens to be a tree rather than a more general graph.

A _binary trie_ is a trie in which the alphabet is just {0, 1}.
A "word" is a sequence of bits, i.e., a binary number.
To look up the "word" 10001, use 0 as a signal to "go left", and 1 as a signal to "go right".

The binary numbers we use will be type `Positive`.
Given a `Positive` number such as ten, we will go left to right in the `xO`/`xI` constructors (which is from the low-order bit to the high-order bit), using `xO` as a signal to go left, `xI` as a signal to go right, and `xH` as a signal to stop.
-/

open Positive

inductive Trie (α : Type) :=
  | leaf : Trie α
  | node : Trie α → α → Trie α → Trie α

open Trie

def trie_table (α : Type) : Type := α × Trie α

def empty {α : Type} (default : α) : trie_table α := (default, leaf)

def look {α : Type} (default : α) (i : Positive) (m : Trie α) : α :=
  match m with
  | leaf => default
  | node l x r =>
    match i with
    | xH => x
    | xO i' => look default i' l
    | xI i' => look default i' r

def lookup {α : Type} (i : Positive) (t : trie_table α) : α :=
  look (Prod.fst t) i (Prod.snd t)

def ins {α : Type} (default : α) (i : Positive) (a : α) (m : Trie α) : Trie α :=
  match m with
  | leaf =>
    match i with
    | xH => node leaf a leaf
    | xO i' => node (ins default i' a leaf) default leaf
    | xI i' => node leaf default (ins default i' a leaf)
  | node l o r =>
    match i with
    | xH => node l a r
    | xO i' => node (ins default i' a l) o r
    | xI i' => node l o (ins default i' a r)

def insert {α : Type}
    (i : Positive) (a : α) (t : trie_table α) : trie_table α :=
  (Prod.fst t, ins (Prod.fst t) i a (Prod.snd t))

def three := xI xH
def three_ten : trie_table Bool :=
  insert three True (insert ten True (empty False))

/-
### From quadratic to N x logN
-/

namespace FastEnough

def loop (input : List Positive) (c : Nat) (table : trie_table Bool) : Nat :=
  match input with
  | [] => c
  | a::al => if lookup a table
                then loop al (c+1) table
                else loop al c (insert a True table)

def collisions (input : List Positive) := loop input 0 (empty False)

end FastEnough

/-
This program takes O(N log N) time: the loop executes `N` iterations, the `lookup` takes `log N` time, the insert takes `log N` time.
One might worry about `c+1` computed in the natural numbers (unary representation), but this evaluates in one step to `S c`, which takes constant time, no matter how long `c` is.

## Proving the correctness of trie tables

Trie tables are just another implementation of the `Map` abstract data type.
What we have to prove is the same as usual for ADT: define a representation invariant, define an abstraction relation, prove that the operations respect the invariant and the abstraction relation.

We will indeed do that.
But this time we'll take a different approach.
Instead of defining a "natural" abstraction relation based on what we see in the data structure, we'll define an abstraction relation that says, "what you get is what you get."
This will work, but it means we've moved the work into directly proving some things about the relation between the `lookup` and the `insert` operators.

### Lemmas about the relation between `lookup` and `insert`
-/

/-
exercise (1-star)
-/
theorem look_leaf α (d : α) j : look d j leaf = d := by
  sorry

/-
exercise (2-star)
This is a rather simple induction.
-/
theorem look_ins_same {α} d k (v : α) t : look d k (ins d k v t) = v := by
  sorry

/-
exercise (3-star)
Induction on `j`?
Induction on `t`?
Do you feel lucky?
-/
theorem look_ins_other {α} d j k (v : α) t
    : j ≠ k → look d j (ins d k v t) = look d j t := by
  sorry

/-
### Bijection between `Positive` and `Nat`

In order to relate `lookup` on positives to total map on natural numbers, it's helpful to have a bijection between `Positive` and `Nat`.
We'll relate `xH` to `0`, `xO xH` to `1`, and so on.
-/

def nat2pos' (n : Nat) (f : Nat) : Positive :=
  match n, f with
  | _, 0 => xH  -- out of fuel
  | 0, _ => xH
  | _, Nat.succ f =>
    let q := Nat.div n 2;
    let r := Nat.mod n 2;
    if r == 0 then xO (nat2pos' q f) else xI (nat2pos' q f)

def nat2pos (n : Nat) : Positive := nat2pos' n n
def pos2nat (n : Positive) : Nat := Nat.pred (positive2nat n)

theorem pos2nat2pos p : nat2pos (pos2nat p) = p := by
  sorry

theorem nat2pos2nat i : pos2nat (nat2pos i) = i := by
  sorry

/-
Now, use those two lemmas to prove that it's really a bijection!
-/

/-
exercise (2-star)
-/

theorem pos2nat_injective p q : pos2nat p = pos2nat q → p = q := by
  sorry

theorem nat2pos_injective i j : nat2pos i = nat2pos j → i = j := by
  sorry

/-
### Proving that tries are a "table" ADT

Representation invariant.
Under what condition is a trie well-formed?
Fill in the simplest thing you can, to start; then correct it later as necessary.
-/

def is_trie {α : Type} (t : trie_table α) : Prop :=
  /- **FILL IN HERE** -/
  sorry

/-
Abstraction relation.
This is what we mean by, "what you get is what you get."
That is, the abstraction of a `trie_table` is the total function, from naturals to `α` values, that you get by running the `lookup` function.
Based on this abstraction relation, it will be trivial to prove `lookup_relate`, but `insert_relate` will NOT be trivial.
-/

def abstract {α : Type} {t : trie_table α} (n : Nat) : α :=
  lookup (nat2pos n) t

def Abs {α : Type} (t : trie_table α) (m : total_map α) :=
  @abstract α t = m

/-
exercise (2-star)
If you picked a _really simple_ representation invariant, these should be easy.
Later, if you need to change the representation invariant in order to get the `_relate` proofs to work, then you'll need to fix these proofs.
-/

theorem empty_is_trie {α} (default : α) : is_trie (empty default) := by
  sorry

theorem insert_is_trie {α} i x (t : trie_table α)
    : is_trie t → is_trie (insert i x t) := by
  sorry

/-
exercise (2-star)
Just unfold a bunch of definitions, use `funext`, and use one of the lemmas you proved above, in section "Lemmas about the relation between `lookup` and `insert`."
-/

theorem empty_relate {α} (default : α)
    : Abs (empty default) (fun _ => default) := by
  sorry

/-
exercise (2-star)
Given the abstraction relation we've chosen, this one should be really simple.
-/

theorem lookup_relate {α} i (t : trie_table α) m
    : is_trie t → Abs t m → lookup i t = m (pos2nat i) := by
  sorry

/-
exercise (3-star)
Given the abstraction relation we've chosen, this one should NOT be simple.
However, you've already done the heavy lifting, with the lemmas `look_ins_same` and `look_ins_other`.
You will not need induction here.
Instead, unfold a bunch of things, use extensionality, and get to a case analysis on whether `pos2nat k =? pos2nat j`.
To handle that case analysis, use `split`.
You may also need `pos2nat_injective`.
-/

theorem insert_relate {α} k (v : α) t cts
    : is_trie t → Abs t cts
      → Abs (insert k v t) (update cts (pos2nat k) v) := by
  sorry

/-
## Conclusion

Efficient functional maps with (positive) integer keys are one of the most important data structures in functional programming.
They are used for symbol tables in compilers and static analyzers; to represent directed graphs (the mapping from node-ID to edge-list); and (in general) anywhere that an imperative algorithm uses an array or _requires_ a mutable pointer.
-/

/-
## references
* [Software Foundations, Volume 3 Verified Functional Algorithms: Number Representations and Efficient Lookup Tables](https://softwarefoundations.cis.upenn.edu/vfa-current/Trie.html)
-/
