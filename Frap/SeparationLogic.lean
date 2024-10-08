/-
# Separation logic

Separation logic is a novel system for reasoning about imperative programs.
Developed by O'Hearn, Reynolds, and Yang in 2001, it extends Hoare logic with enriched assertions that can describe the separation of storage and other resources concisely.
The original goal of the logic was to facilitate reasoning about shared mutable data structures, i.e., structures where updatable fields can be referenced from more than one point (aliasing).
More recently, the logic has been extended to deal with shared-variable concurrency and information hiding, and the notion of separation has proven applicable to a wiider conceptual range, where access to memory is replaced by permission to exercise capabilities, or by knowledge of structure.
In a few years, the logic has become a significant research area, wiith a growing literature produced by a variety of researchers.

## The programming language

The programming language we will use is a low-level imperative language; specifically, the simple imperative language originally axiomatized by Hoare, extended with new commands for the manipulation of mutable shared data structures:
```
  comm ::= ...  // imperative constructs from before
    | var := cons(exp, ..., exp)  // allocation (malloc)
    | var := [exp]  // lookup (pointer dereference)
    | [exp] := exp  // mutation (memory assignment)
    | dispose(exp)  // deallocation (free)
```
Memory management is explicit; there is no garbage collection.
As we will see, any dereferencing of dangling addresses will cause a fault.

Semantically, we extend computational states to contain two components: a store (sometimes called a stack), mapping variables into values (as in the semantics of the unextended simple imperative language), and a heap, mapping addresses into values (and representing the mutable structures).

The semantics of the new commands is simple enough to be conveyed by example.
If we begin with a state where the store maps the variable x and y into 3 and 4, and the heap is empty, then the typical effect of each kind of heap-manipulating command is:
```
                                  Store: x:3, y:4
                                  Heap: empty
  Allocation    x := cons(1, 2);
                                  Store: x:37, y:4
                                  Heap: 37:1, 38:2
  Lookup        y := [x];
                                  Store: x:37: y:1
                                  Heap: 37:1, 38:2
  Mutation      [x+1] := 3;
                                  Store: x:37: y:1
                                  Heap: 37:1, 38:3
  Deallocation  dispose(x+1);
                                  Store: x:37: y:1
                                  Heap: 37:1
```
The allocation operation `cons(e₁, ..., eₙ)` activates an initializes `n` cells in the heap.
It is important to notice that, aside from the requirement that the addresses of these cells be consecutive and previously inactive, the choice of addresses is indeterminate.

The remaining operations, for mutation, lookup, and deallocation, all cause memory faults (denoted by the terminal configuration `abort`) if an inactive address is dereferenced or deallocated.
For example:
```
                                Store: x:3, y:4
                                Heap: empty
  Allocation  x := cons(1, 2);
                                Store: x:37, y:4
                                Heap: 37:1, 38:2
  Lookup      y := [x];
                                Store: x:37, y:1
                                Heap: 37:1, 38:2
  Mutation    [x+2] := 3;
                                abort
```

## Motivating example

The use of shared mutable data structures is widespread in areas as diverse as systems programming and artificial intelligence.
Approaches to reasoning about this technique have been studied for three decades, but the result has been methods that suffer from either limited applicability or extreme complexity, and scale poorly to programs of even moderate size.

For conventional logics, the problem with sharing is that it is the default in the logic, while nonsharing is the default in programming, so that declaring all of the instances where sharing does not occur---or at least those instances necessary for correctness---can be extremely tedious.

For example, consider the following program, which performs an in-place reversal of a singly-linked list, where each node contains two parts, the content of the node and the pointer to the next node:
```
LREV(i):
  j := nil;      // output list
  while i != nil do  // input list remains
    k := [i+1];  // get address of next node
    [i+1] := j;  // next node points to head of output list instead
    j := i;      // head of output list becomes current node instead
    i := k;      // move to next node
```
The invariant of this program must state that `i` and `j` are lists representing two sequences α and β such that the reverse of the initial value α₀ can be obtained by concatenating the reverse of α onto β:
  `∃α,β: list α i ∧ list β j ∧ rev(α₀) = rev(α)++β`,
where the predicate `list α i` is defined inductively on the length of α:
  `list [] i ≝ i = nil`  `list (a::α) i ≝ ∃j: i ↪ a,j ∧ list α j`
(and ↪ can be read as "points to").

Unfortunately, however, this is not enough, since the program will malfunction if there is any sharing between the lists `i` and `j`.
To prohibit this, we must extend the invariant to assert that only nil is reachable from both `i` and `j` (1):
  `(∃α,β: list α i ∧ list β j ∧ rev(α₀) = rev(α)++β)`
  ` ∧ (∀k: reachable(i,k) ∧ reachable(j,k) → k = nil)`,
where
  `reachable(i,j) ≝ ∃n≥0: reachableₙ(i,j)`
  `reachable₀(i,j) ≝ i = j`
  `reachableₙ₊₁(i,j) ≝ ∃a,k: i ↪ a,k ∧ reachableₙ(k,j)`.

Even worse, suppose there is some other list `x`, representing a sequence γ, that is not supposed to be affected by the execution of our program.
Then it must not share with either `i` or `j`, so that the invariant becomes (2)
```
  (∃α,β: list α i ∧ list β j ∧ rev(α₀) = rev(α)++β)
  ∧ (∀k: reachable(i,k) ∧ reachable(j,k) → k = nil)
  ∧ list γ x
  ∧ (∀k: reachable(x,k) ∧ (reachable(i,k) ∨ reachable(j,k)) → k = nil).
```
Even in this trivial situation, where all sharing is prohibited, it is evident that this form of reasoning scales poorly.

In separation logic, however, this kind of difficulty can be avoided by using a novel logical operation `P * Q`, called the _separating conjunction_ or _star_, that asserts that `P` and `Q` hold for _disjoint_ portions of the addressable storage.
Since the prohibition of sharing is built into this operation, invariant (1) can be written more succinctly as (3)
  `(∃α,β: list α i * list β j) ∧ rev(α₀) = rev(α)++β`,
and invariant (2) as (4)
  `(∃α,β: list α i * list β j * list γ x) ∧ rev(α₀) = rev(α)++β`.

A more general advantage is the support that separation logic gives to _local reasoning_, which underlies the scalability of the logic.
For example, one can use (3) to prove a _local_ specification
  `{list α i} LREV {list rev(α) j}`.
In separation logic, this specification implies not only that the program expects to find a list at `i` representing `α`, but also that this list is the _only_ addressable storage touched by the execution of `LREV` (often called the _footprint_ of `LREV`).
If `LREV` is a part of a larger program that also manipulates some separate storage, say containing the list `k`, then one can use an inference rule due to O'Hearn, called the _frame rule_, to infer directly that the additional storage is unaffected by `LREV`:
  `{list α i * list γ k} LREV {list rev(α) j * list γ k}`,
thereby avoiding the extra complexity of invariant (4).

In a realistic situation, of course, `LREV` might be a substantial subprogram, and the description of the separate storage might also be voluminous.
Nevertheless, one can still reason _locally_ about `LREV`, i.e., while ignoring the separate storage, and then scale up to the combined storage by using the frame rule.

There is little need for local reasoning in proving toy examples.
But it provides scalability that is critical for more complex programs.

## Assertions

As in Hoare logic, assertions describes states, but now states contain heaps as well as stores.
Thus, in addition to the usual operations and quantifiers of predicate logic, we have four new forms of assertion that describe the heap:
* `emp`  (empty heap)
  The heap is empty.
* `e ↦ e'`  (singleton heap)
  The heap contains one cell, at address `e` with contents `e'`.
* `p₁ * p₂`  (separating conjunction, "star")
  The heap can be split into two disjoint parts such that `p₁` holds for one part and `p₂` holds for the other.
* `p₁ -* p₂`  (separating implication, "magic wand")
  If the heap is extended with a disjoint part in which `p₁` holds, then `p₂` holds for the extended heap.
  In other words, if given `h'` disjoint from heap `h`, then that `p₁` holds for `h'` implies that `p₂` holds for the combined heap `h ⊎ h'`.
It is also useful to introduce abbreviations for asserting that an address `e` is active:
  `e ↦ - ≝ ∃x': e ↦ x'`  where `x'` not free in `e`,
that `e` points to `e'` somewhere in the heap:
  `e ↪ e' ≝ e ↦ e' * true`,
and that `e` points to a record with several fields:
  `e ↦ e₁, ..., eₙ ≝ e ↦ e₁ * ... * e+n-1 ↦ eₙ`
  `e ↪ e₁, ..., eₙ ≝ e ↪ e₁ * ... * e+n-1 ↪ eₙ` iff `e ↦ e₁, ..., eₙ * true`.
Notice that assertions of the form `e ↦ e'`, `e ↦ -`, and `e ↦ e₁, ..., eₙ` determine the extent (i.e., domain) of the heap they describe, while those of the form `e ↪ e'` and `e ↪ e₁, ..., eₙ` do not.
(Technically, the former are said to be _precise_ assertions.)

By using `↦`, `↪`, and both separating and ordinary conjunction, it is easy to describe simple sharing patterns concisely.
For instance:
1. `x ↦ 3,y` asserts that `x` points to an adjacent pair of cells containing `3` and `y` (i.e., the store maps `x` and `y` into some values `α` and `β`, `α` is an address, and the heap maps `α` into `3` and `α+1` into `β`).
2. `y ↦ 3,x` asserts that `y` points to an adjacent pair of cells containing `3` and `x`.
3. `x ↦ 3,y * y ↦ 3,x` asserts that situations (1) and (2) holds for separate parts of the heap.
4. `x ↦ 3,y ∧ y ↦ 3,x` asserts that situations (1) and (2) holds for the same heap, which can only happen if the values of `x` and `y` are the same.
5. `x ↪ 3,y ∧ y ↪ 3,x` asserts that either (3) or (4) may hold, and that the heap may contain additional cells.

Separating implication is somewhat more subtle, but is illustrated by the following example.
Suppose the assertion `p` asserts various conditions about the store and heap, including that the store maps `x` into the address of a record containing `3` and `4`:
  Store: x:α, ...
  Heap: α:3, α+1:4, rest of heap
Then `(x ↦ 3,4) -* p` asserts that, if one were to add to the current heap a disjoint heap consisting of a record at address `x` containing `3` and `4`, t hen the resulting heap would satisfy `p`.
In other words, the current heap is like that described by `p`, except that the record is missing:
  Store: x:α, ...
  Heap: rest of heap, as above
Moreover, `x ↦ 1,2 * ((x ↦ 3,4) -* p)` asserts that the heap consists of a record at `x` containing `1` and `2`, plus a separate part as above:
  Store: x:α, ...
  Heap: α:1, α+1:2, rest of heap, as above

This example suggests that `x ↦ 1,2 * ((x ↦ 3,4) -* p)` describes a state that would be changed by the mutation operations `[x] := 3` and `[x+1] := 4` into a state satisfying `p`.
In fact, we will find that
  `{x ↦ 1,2 * ((x ↦ 3,4) -* p)}  [x] := 3; [x+1] := 4  {p}`
is a valid specification (i.e., Hoare triple) in separation logic---as is the more general specification
  `{x ↦ -,- * ((x ↦ 3,4) -* p)}  [x] := 3; [x+1] := 4  {p}`.

The inference rules for predicate calculus (not involving the new operators we have introduced) remain sound in this enriched setting.
Additional axiom schemata for separating conjunction include commutative and associative laws, the fact taht `emp` is an identity element, and various distributive and semidistributive laws:
  `p₁ * p₂ ↔ p₂ * p₁`
  `(p₁ * p₂) * p₃ ↔ p₁ * (p₂ * p₃)`
  `p * emp ↔ p`
  `(p₁ ∨ p₂) * q ↔ (p₁ * q) ∨ (p₂ * q)`
  `(p₁ ∧ p₂) * q ↔ (p₁ * q) ∧ (p₂ * q)`
  `(∃x: p₁) * p₂ ↔ ∃x: (p₁ * p₂)` when `x` not free in `p₂`
  `(∀x: p₁) * p₂ ↔ ∀x: (p₁ * p₂)` when `x` not free in `p₂`
There is also an inference rule showing that separating conjunction is monotone with respect to implication:
```
  p₁ → p₂     q₁ → q₂
  ------------------- (monotonicity)
   p₁ * q₁ → p₂ * q₂
```
and two further rules capturing the adjunctive relationship between separating conjunction and separating implication:
```
   p₁ * p₂ → p₃
  --------------- (currying)
  p₁ → (p₂ -* p₃)

  p₁ → (p₂ -* p₃)
  --------------- (decurrying)
   p₁ * p₂ → p₃
```

On the other hand, there are two rules that one might expect to hold for an operation called "conjunction" that in fact fail:
  `p → p * p`  (contraction -- unsound)
  `p * q → p`  (weakening -- unsound)
A counterexample to both of these axiom schemata is provided by taking `p` to be `x ↦ 1` and `q` to be `y ↦ 2`; then `p` holds for a certain single-field heap while `p * p` holds for no heap, and `p * q` holds for a certain two-field heap while `p` holds for no two-field heap.
(Thus separation logic is a substructural logic, meaning certain rules in our familiar logic don't hold.)

## Specifications and their inference rules

While assertions describe states, specifications describe commands.
In specification logic, specifications are Hoare triples:
  `{assertion}  command  {assertion}`  (partial correctness)
The initial assertion is called the _precondition_, and the final assertion is called to _postcondition_.

The _partial correctness specification_ `{p} c {q}` is true iiff, starting in any state in which `p` holds,
* No execution of `c` aborts, and
* When some execution of `c` terminates in a final state, then `q` holds in the final state.

This form if specification is so similar to that of Hoare logic that it is important to note the differences.
Our specification is implicitly quantified over both stores and heaps, and also (since allocation is indeterminate) over all possible executions.
Moreover, any execution (starting in a state satisfying `p`) that gives a memory fault falsifies partial specifications.
-/

/-
## references
* [John C. Reynolds, 2008.  An Introduction to Separation Logic](https://www.cs.cmu.edu/~jcr/copenhagen08.pdf)
* [John C. Reynolds, 2011.  An Introduction to Separation Logic, An Overview](https://www.cs.cmu.edu/afs/cs.cmu.edu/project/fox-19/member/jcr/www15818As2011/ch1.pdf)
* [John C. Reynolds, 2002.  Separation Logic: A Logic for Shared Mutable Data Structures](https://www.cs.cmu.edu/~jcr/seplogic.pdf)
* [Peter O'Hearn, John Reynolds, and Hongseok Yang, 2001.  Local Reasoning about Programs that Alter Data Structures](http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/localreasoning.pdf)
* [Daniel Patterson, 2023.  Logic & Computation, Lecture 33: Separation Logic](https://course.ccs.neu.edu/cs2800sp23/l33.html)
-/
