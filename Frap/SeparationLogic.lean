/-
# Separation logic

Separation logic is a novel system for reasoning about imperative programs.
Developed by O'Hearn, Reynolds, and Yang in 2001, it extends Hoare logic with enriched assertions that can describe the separation of storage and other resources concisely.
The original goal of the logic was to facilitate reasoning about shared mutable data structures, i.e., structures where updatable fields can be referenced from more than one point (aliasing).
More recently, the logic has been extended to deal with shared-variable concurrency and information hiding, and the notion of separation has proven applicable to a wider conceptual range, where access to memory is replaced by permission to exercise capabilities, or by knowledge of structure.
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
  `list [] i ≝ i = nil`  `list (a:α) i ≝ ∃j: i ↪ a,j ∧ list α j`
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

The last point goes to the heart of separation logic: well-specified programs don't go wrong.
As a consequence, during the execution of a program that has been proved to meet some specification (assuming that the program is only executed in initial states satisfying the precondition of the specification), it is unnecessary to check for memory faults, or even to equip heap cells with activity bits.

In fact, it is not the implementor's responsibility to detect memory faults.
It is the programmer's responsibility to avoid them---and separation logic is a tool for this purpose.
Indeed, according to the logic, the implementor is free to implement memory faults however he wishes, since nothing can be proved that might gainsay him.

Roughly speaking, the fact that specifications precludes memory faults acts in concert with the indeterminacy of allocation to prohibit violations of record boundaries.
For example, during an execution of
  `c₀; x := cons(1, 2); c₁; [x+2] := 7`,
no allocation performed by the subcommand `c₀` or `c₁` can be guaranteed to allocate the location `x+2`; thus as long as `c₀` and `c₁` terminate and `c₁` does not modify `x`, there is a possibility that the execution will abort.
It follows that there is no postcondition that makes the following specification valid:
  `{true}  c₀; x := cons(1, 2); c₁; [x+2] := 7  {?}`.

Sometimes, however, the notion of record boundaries dissolves, as in the following valid (and provable) specification of a program that tries to form a two-field record by gluing together two one-field records:
```
    {x ↦ - * y ↦ -}
  if y = x+1 then skip  // already consecutive
  else if x = y+1 then x := y  // consecutive but order switched
  else (dispose x; dispose y; x := cons(1, 2))  // build from scratch
    {x ↦ -,-}
```
It is evident that such a program goes well beyond the discipline imposed by type systems for mutable data structures.

In our new setting, the command-specific inference rules of Hoare logic remain sound, as do such structural rules as
* Consequence
  ```
    p → p'     {p'} c {q'}     q' → q
    ---------------------------------
                {p} c {q}
  ```
* Existential quantification (ghost variable elimination)
  ```
        {p} c {q}
    -----------------
    {∃v: p} c {∃v: q}
  ```
  where `v` is not free in `c`.
* Conjunction
  ```
    {p} c {q₁}     {p} c {q₂}
    -------------------------
         {p} c {q₁ ∧ q₂}
  ```

An exception is what is sometimes called the "rule of constancy":
```
      {p} c {q}
  ----------------- (unsound)
  {p ∧ r} c {q ∧ r}
```
where no variable occurring free in `r` is modified by `c`.
It has long been understood that this rule is vital for scalability, since it permits one to extend a "local" specification of `c`, involving only the variables actually used by that command, by adding arbitrary predicates about variables that are not modified by `c` and will therefore be preserved by its execution.

Surprisingly, however, the rule of constancy becomes unsound when one moves from traditional Hoare logic to separatin logic.
For example, the conclusion of the instance
```
          {x ↦ -}  [x] := 4  {x ↦ 4}
  ------------------------------------------
  {x ↦ - ∧ y ↦ 3}  [x] := 4  {x ↦ 4 ∧ y ↦ 3}
```
is not valid, since its precondition does not preclude the case `x = y`, where aliasing will falsify `y ↦ 3` when the mutation command is executed.
(Indeed, this precondition implies `x = y`.)

O'Hearned realized, however, that the ability to extend local specifications can be regained at a deeper level by using separating conjunction.
In place of the rule of constancy, he proposed the _frame rule_:
* Frame rule
  ```
        {p} c {q}
    -----------------
    {p * r} c {q * r}
  ```
  where no variable occurring free in `r` is modified by `c`.
By using the frame rule, one can extend a local specification, involving only the variables _and heap cells_ that may actually be used by `c` (which O'Hearn calls the _footprint_ of `c`), by adding arbitrary predicates about variables and heap cells that are not modified or mutated by `c`.
Thus, the frame rule is the key to "local reasoning" about the heap:
  To understand how a program works, it should be possible for reasoning and specification to be confined to the cells that the program actually accesses.
  The value of any other cell will automatically remain unchanged.

In any valid specification `{p} c {q}`, `p` must assert that the heap contains every cell in the footprint of `c` (except for cells that are freshly allocated by `c`); "locality" is the converse implication that every cell asserted to be contained in the heap belongs to the footprint.
The role of the frame rule is to infer from a local specification of a command the more global specification appropriate to the possible larger footprint of an enclosing command.

Beyond the rules of Hoare logic and the frame rule, there are inferene rules for each of the new heap-manipulating commands.
Indeed, for each of these commands, we can give three kinds of rules: local, global, and backward-reasoning.

For mutation, for example, the simplest rule is the local rule:
* Mutation (local)
```
    ---------------------------
    {e ↦ -} [e] := e' {e ↦ e'}
```
  which specifies the effect of mutation on the single cell being mutated.
  From this, one can use the frame rule to derive a global rule:
* Mutation (global)
```
    --------------------------
    {e ↦ - * r} [e] := e' {e ↦ e' * r}
```
  which also specifies that anything in the heap beyond the cell being mutated is left unchanged by the mutation.
  (One can rederive the local rule from the global one by taking `r` to be `emp`.)
Beyond these forms, there is also:
* Mutation (backwards reasoning)
```
    -----------------------------------------
    {(e ↦ -) * ((e ↦ e') -* p)} [e] := e' {p}
```
  which is called a _backward reasoning_ rule since, by substituting for `p`, one can find a precondition for any postcondition.

A similar development works for deallocation, except that the global form is itself suitable for backward reasoning:
* Deallocation (local)
```
    -----------------------
    {e ↦ -} dispose e {emp}
```
* Deallocation (global, backwards reasoning)
```
    ---------------------------
    {(e ↦ -) * r} dispose e {r}
```

In the same way, one can give equivalent local and global rules for allocation commands in the _nonoverwriting_ case where the old value of the variable being modified plays no role.
* Allocation (nonoverwriting, local)
```
    -------------------------------------------
    {emp} v := cons(e₁, ..., eₙ) {v ↦ e₁,...,eₙ}
```
  where `v` is not free in `e₁,...,eₙ`.
* Allocation (nonoverwriting, global)
```
    -------------------------------------------
    {r} v := cons(e₁, ..., eₙ) {(v ↦ e₁,...,eₙ) * r}
```
  where `v` is not free in `e₁,...,eₙ` or `r`.


Of course, we also need more general rules for allocation commands `v := cons(e₁,...eₙ)`, where `v` occurs in `e₁,...eₙ` or the precondition, as well as a backward-reasoning rule for allocation, and rules for lookup (later).

### Examples of decorated programs

As a simple illustration of separation logic, the following is an annotated specification of the command that tries to glue together adjacent records from earlier:
```
      {x ↦ - * y ↦ -}
  if y = x+1 then
      {(x ↦ - * y ↦ -) ∧ y = x+1} -->
      {x ↦ -,-}
    skip
      {x ↦ -,-}
  else if x = y+1 then
      {(x ↦ - * y ↦ -) ∧ x = y+1} -->
      {y ↦ -,-}
    x := y
      {x ↦ -,-}
  else
      {x ↦ - * y ↦ -}
    dispose x;
      {y ↦ -}
    dispose y;
      {emp}
    x:= cons(1, 2)
      {x ↦ -,-}
```

A second example describes a command that uses allocation and mutation to construct a two-element cyclic structure containing relative addresses:
```
    {emp}
  x := cons(a, a);
    {x ↦ a,a}
  y := cons(b, b);
    {(x ↦ a,a) * (y ↦ b,b)} -->
    {(x ↦ a,_) * (y ↦ b,_)}
  [x+1] := y-x;
    {(x ↦ a,y-x) * (y ↦ b,_)}
  [y+1] := x-y;
    {(x ↦ a,y-x) * (y ↦ b,x-y)} -->
    {∃o: (x ↦ a,o) * (x+o ↦ b,-o)}
```

## Lists

To specify a program adequately, it is usually necessary to describe more than the form of its structures or the sharing patterns between them; one must relate the states of the program to the abstract values that they denote.
For instance, to specify the list-reversal program from earlier, it would hardly be enough to say that, "If `i` is a list before execution, then `j` will be a list afterwards."
One needs to say that, "If `i` is a list representing the sequence `α` before execution, then afterwards `j` will be a list representing the sequence that is the reflection of `α`."

To do so in general, it is necessary to define the set of abstract values (sequencees, in this case), along with their primitive operations, and then to define predicates on the abstract values inductively.
Since these kinds of definitions are standard, we will treat them less formally than the novel aspects of our logic.

Sequences and their primitive operations are an easy first example since they are a standard and well-understood mathematical concept, so that we can omit their definition.
To denote the primitive operations, we write `[]` for the empty sequence, `a:β` for the composition of `a` followed by `β`, `rev(α)` for the reflection of `α`, and `αᵢ` for the i-th component of `α`.

The simplest list structure for representing sequences is the _singly-linked_ list.
To describe this representation, we write `list α i` when `i` is a list representing the sequence `α`.

It is straightforward to define this predicate by induction on the structure of `α`:
  `list [] i ≝ emp ∧ i = nil`
  `list (a:α) i ≝ ∃j: i ↦ a,j * list α j`
and to derive a test whether the list represents an empty sequence:
  `list α i → (i = nil ↔ α = [])`

Then the following is a decorated program for reversing a list, where Greek letters appearing in the assertions are used as variables denoting sequences.
```
      {list α₀ i} -->
      {list α₀ i * (emp ∧ nil = nil)}
  j := nil;
      {list α₀ i * (emp ∧ j = nil)} -->
      {list α₀ i * list [] j} -->
      {∃α,β: (list α i * list β j) ∧ rev(α₀) = rev(α)++β}
  while i != nil do
        {(∃α,β: (list α i * list β j) ∧ rev(α₀) = rev(α)++β) ∧ i ≠ nil} -->
        {∃a,α',β: (list (a:α') i * list β j) ∧ rev(α₀) = rev(a:α')++β} -->
        {∃a,α',β,k: (i ↦ a,k * list α' k * list β j) ∧ rev(α₀) = rev(a:α')++β}
    k := [i+1];
        {∃a,α',β: (i ↦ a,k * list α' k * list β j) ∧ rev(α₀) = rev(a:α')++β}
    [i+1] := j
        {∃a,α',β: (i ↦ a,j * list α' k * list β j) ∧ rev(α₀) = rev(a:α')++β} -->
        {∃a,α',β: (list α' k * list (a:β) i) ∧ rev(α₀) = rev(α')++(a:β)} -->
        {∃α',β': (list α' k * list β' i) ∧ rev(α₀) = rev(α')++β'}
    j := i;
        {∃α',β': (list α' k * list β' j) ∧ rev(α₀) = rev(α')++β'}
    i := k;
        {∃α',β': (list α' i * list β' j) ∧ rev(α₀) = rev(α')++β'}
      {(∃α,β: (list α i * list β j) ∧ rev(α₀) = rev(α)++β) ∧ i = nil} -->
      {∃α,β: list β j ∧ rev(α₀) = rev(α)++β ∧ α = []} -->
      {list rev(α₀) j}
```
-/

/-
## references
* [John C. Reynolds, 2008.  An Introduction to Separation Logic](https://www.cs.cmu.edu/~jcr/copenhagen08.pdf)
* [John C. Reynolds, 2011.  An Introduction to Separation Logic, An Overview](https://www.cs.cmu.edu/afs/cs.cmu.edu/project/fox-19/member/jcr/www15818As2011/ch1.pdf)
* [John C. Reynolds, 2002.  Separation Logic: A Logic for Shared Mutable Data Structures](https://www.cs.cmu.edu/~jcr/seplogic.pdf)
* [Peter O'Hearn, John Reynolds, and Hongseok Yang, 2001.  Local Reasoning about Programs that Alter Data Structures](http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/localreasoning.pdf)
* [Daniel Patterson, 2023.  Logic & Computation, Lecture 33: Separation Logic](https://course.ccs.neu.edu/cs2800sp23/l33.html)
-/
