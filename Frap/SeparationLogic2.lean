/-
## Trees and DAGs

When we move from list to tree data structures, the possible patterns of sharing within the structures become richer.

At the outset, we face a problem of nomenclature: words such as "tree" and "graph" are often used to describe a variety of abstract structures, as well as particular ways of representing such structures.
Here we will focus on a particular kind of abstract value called an "S-expression" in the LISP community.
The set S-exps of these values is the least set such that
  τ ∈ S-exps iff τ ∈ Atoms
                 or τ = (τ₁, τ₂) where τ₁, τ₂ ∈ S-exps
Think of S-expressions as binary abstract syntax trees.

For clarity, it is vital to maintain the distinction between abstract values and their representations.
Thus, we will call abstract values "S-expressions", while calling representations without sharing "trees", and representations with sharing but no cycles "DAGs" (for "directed acyclic graphs").

We write `tree τ (i)` (or `dag τ (i)`) to indicate that `i` is the root of a tree (or DAG) representing the S-expression τ.
Both predicates are defined inductively on the structure of τ:
         `tree a (i)` iff `emp` ∧ `i` = `a`
  `tree (τ₁, τ₂) (i)` iff `∃i₁,i₂: i ↦ i₁,i₂ * tree τ₁ (i₁) * tree τ₂ (i₂)`
          `dag a (i)` iff `i` = `a`
   `dag (τ₁, τ₂) (i)` iff `∃i₁,i₂: i ↦ i₁,i₂ * (dag τ₁ (i₁) ∧ dag τ₂ (i₂))`.

## Shared-variable concurrency

O'Hearn has extended separation logic to reason about shared-variable concurrency, drawing upon early ideas of Hoare, and Owicki and Gries.

For the simplest case, where concurency is unconstrained by any kind of synchronization mechanism, Hoare had given the straightforward rule:
```
  {p₁} c₁ {q₁}     {p₂} c₂ {q₂}
  -----------------------------
   {p₁ ∧ p₂} c₁ ‖ c₂ {q₁ ∧ q₂}
```
when free variables of p₁, c₁, and q₁ are not modified by c₂, and vice versa.

Unfortunately, this rule fails in separaction logic, since, even though the side condition prohibits the processes from interfering via assignments to variables, they permit interference via mutations in the heap.
O'Hearn realized that the rule could be saved by replacing the ordinary conjunctions by separating conjunctions, which separated the heap into parts that can only be mutated by a single process:
```
  {p₁} c₁ {q₁}     {p₂} c₂ {q₂}
  -----------------------------
   {p₁ * p₂} c₁ ‖ c₂ {q₁ * q₂}
```
(with the same side condition as above).

Things become far less straightforward, however, when synchronization was introduced.
Hoare had investigated conditional critical regions, keyed to "resources", which were disjoint collections of variables.
His crucial idea was that there should be an invariant associated with each resource, such that when one entered a critical region keyed to a resource, one could assume that the invariant was true, but when one left the region, the invariant must be restored.

O'Hearn was able to generalize these ideas so that both processes and resources could "own" portions of the heap, and this ownership could move among processes and resources dynamically as the processes entered and left critical regions.

As a simple example, consider two processes that share a buffer consisting of a single `cons`-cell.
At the level of the process, there are simply two procedures: `put(x)`, which accepts a `cons`-cell and makes it disappear, and `get(y)`, which makes a `cons`-cell appear.
The first process allocates a `cons`-cell and gives it to `put(x)`; the second process obtains a `cons`-cell from `get(y)`, uses it, and deallocates it:
```
                          {emp}
                       {emp * emp}
    {emp}                             {emp}
  x := cons(..., ...);              get(y);
    {x ↦ -,-}               ||        {y ↦ -,-}
  put(x);                           "use y";
    {emp}                             {y ↦ -,-}
                                    dispose(y);
                                      {emp}
                       {emp * emp}
                          {emp}
```

Behind the scenes, however, there is a resource `buf` that implements a small buffer that can hold a single `cons`-cell.
Associated with this resource are a boolean variable `full`, which indicates whether the buffer current holds a cell, and an integer variable `c` that points to the cell when `full` is true.
Then `put(x)` is implemented by a critical region that checks the buffer is empty and then fills it with `x`, and `get(y)` is implemented by a conditional critical region that checks the buffer is full and then empties it into y:
  `put(x) = with buf when ¬full do (c := x; full := true)`
  `get(y) = with buf when full do (y := c; full := false)`

Associated with the resource `buf` is an invariant
  R ≝ `(full ∧ c ↦ -,-) ∨ (¬full ∧ emp)`.
The effect of O'Hearn's inference rule for critical regions is that the resource invariant is used explicitly to reason about the body of a critical region, but is hidden outside of the critical region:
```
                     {x ↦ -,-}
  put(x) = with buf when ¬full do
                       {(R * x ↦ -,-) ∧ ¬full} -->
                       {emp * x ↦ -,-} -->
                       {x ↦ -,-}
             c := x;
                       {c ↦ -,-}
             full := true;
                       {full ∧ c ↦ -,-} -->
                       {R} -->
                       {R * emp}
                     {emp}
```
```
                     {emp}
  get(y) = with buf when full do
                       {(R * emp) ∧ full} -->
                       {c ↦ -,- * emp} -->
                       {c ↦ -,-}
             y := c;
                       {y ↦ -,-}
             full := false;
                       {¬full ∧ y ↦ -,-} -->
                       {(¬full * emp) ∧ y ↦ -,-)} -->
                       {R ∧ y ↦ -,-)} -->
                     {y ↦ -,-}
```
On the other hand, the resource invariant reappears outside the declaration of the resource, indicating that it must be initialized beforehand, and will remain true afterwards:
```
    {R * emp}

  resource buf in
          {emp}
        {emp * emp}
        ⋮   ‖   ⋮
        {emp * emp}
          {emp}

    {R * emp}
```

## Rules for allocation

Recall the inference rules for nonoverwriting allocation:
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

The price for the simplicity of the above rules is the prohibition of overwriting, which is expressed by the side conditions.
Turning to the more complex and general rules that permit overwriting, we have three forms for allocation:
* Allocation (local)
```
    ------------------------------------------------------
    {v = v' ∧ emp} v := cons(e₁, ..., eₙ) {v ↦ e₁',...,eₙ'}
```
  where `v'` is distinct from `v`, and `eᵢ'` denotes `eᵢ[v↦v']`.
* Allocation (global)
```
    -----------------------------------------------------
    {r} v := cons(e₁, ..., eₙ) {∃v': v ↦ e₁',...,eₙ' * r'}
```
  where `v'` is distinct from `v`, `v'` is not free in `e₁,...,eₙ` or `r`, and `r'` denotes `r[v↦v']`.
* Allocation (backward-reasoning)
```
    ----------------------------------------------------------
    {∀v'': (v'' ↦ e₁,...,eₙ) -* p''} v := cons(e₁, ..., eₙ) {p}
```
  where `v''` is distinct from `v`, `v''` is not free in `e₁,...,eₙ` or `p`, and `p'` denotes `p[v↦v'']`.
To explain these rules, we begin with the global rule.
Here, the existentially quantified variable `v'` denotes the old value of `v`, which has been overwritten by the allocation command (and may possibly no longer be determined by the store), much as in the assignment rule.
A typical instance is
  `{list α i} i := cons(3,i) {∃j: i ↦ 3,j * list α j}`.

One might expect the local rule to be
```
    ---------------------------------------------------
    {emp} v := cons(e₁, ..., eₙ) {∃v': v ↦ e₁',...,eₙ'}
```
(where `v'` is distinct from `v` and `v'` is not free in `e₁,...,eₙ`), which can be derived from the global rule by taking `r` to be `emp`.
But this rule, though sound, is too weak.
For example, the postcondition of the instance
  `{emp} i := cons(3,i) {∃j: i ↦ 3,j}`
gives no information about the second component of the new record.

In the stronger local rule above, the existential quantifier is dropped and `v'` becomes a variable that is not modified by `v := cons(e₁,...eₙ)`, so that its occurrences in the postcondition denote the same value as in the precondition.

For example,
  `{i = j ∧ emp} i := cons(3,i) {i ↦ 3,j}`
shows that the value of `j` in the postcondition is the value of `i` before the assignment.

## Rules for lookup

Finally, we come to the lookup command, which---for no obvious reason---has the richest variety of inference rules.
We begin with the nonoverwriting rules:
* Lookup (nonoverwriting, local)
```
    ------------------------------------
    {e ↦ v''} v := [e] {v = v'' ∧ e ↦ v}
```
  where `v` is not free in `e`.
* Lookup (nonoverwriting, global)
```
    -------------------------------------------
    {∃v'': (e ↦ v'') * p''} v := [e] {(e ↦ v) * p}
```
  where `v` is not free in `e`, `v''` is not free in `e` or (`p`, but may be `v`), and `p''` denotes `p[v↦v'']`.
In the global rule, there is no restriction preventing `v''` from being the same as variable `v`.
Thus, as a special case,
```
    ----------------------------------------
    {∃v: (e ↦ v) * p} v := [e] {(e ↦ v) * p}
```
where `v` is not free in `e`.
For example, if we take `v` to be `j`, `e` to be `i+1`, and `p` to be `i ↦ 3 * list α j`, then we obtain the instance
```
    {∃j: i ↦ 3,j * list α j}
  j := [i+1]
    {i ↦ 3,j * list α j}
```
In effect, the action of the lookup command is to erase an existential quantifier.
In practice, if one chooses the names of quantified variables with foresight, most lookup commands can be described by this simple special case.

Turning to the rules for the general case of lookup, we have
* Lookup (local)
```
    ----------------------------------------------
    {v = v' ∧ e ↦ v''} v := [e] {v = v'' ∧ e' ↦ v}
```
  where `v`, `v'`, and `v''` are distinct, and `e'` denotes `e[v↦v']`.
* Lookup (global)
```
    ---------------------------------------------------------------
    {∃v'': (e ↦ v'') * r[v'↦v]} v := [e] {∃v': (e' ↦ v) * r[v''↦v]}
```
  where `v`, `v'`, and `v''` are distinct, `v'`,`v''` not free in `e`, `v` not free in `r`, and `e'` denotes `e[v↦v']`.
In each of these rules, one can think of `v'` as denoting the value of `v` before execution of the lookup command, and `v''` as denoting the value of `v` after execution.
-/

/-
## references
* [John C. Reynolds, 2008.  An Introduction to Separation Logic](https://www.cs.cmu.edu/~jcr/copenhagen08.pdf)
* [John C. Reynolds, 2011.  An Introduction to Separation Logic, An Overview](https://www.cs.cmu.edu/afs/cs.cmu.edu/project/fox-19/member/jcr/www15818As2011/ch1.pdf)
* [John C. Reynolds, 2011.  An Introduction to Separation Logic, Specifications](https://www.cs.cmu.edu/afs/cs.cmu.edu/project/fox-19/member/jcr/www15818As2011/ch3.pdf)
-/
