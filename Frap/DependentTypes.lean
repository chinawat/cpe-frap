/-
# Dependent types

Dependent types are the defining feature of the _dependent type theory_ family of logics.
Although you may not be familiar with the terminology, you are likely to be familiar with the concept in some form or another.

Consider a function `pick` that takes a natural number `n` (i.e., the value from ℕ={0, 1, 2, ...}) and returns a natural numbr between 0 and `n`.
Intuitively, `pick n` should have the type {0, 1, ..., n} (i.e., the type consistint of all natural numbers i ≤ n).
In Lean this is written `{i : ℕ // i ≤ n}`.
This would be the type of `pick n`.
-/

#check fun n => {i : Nat // i ≤ n}
/-
`Subtype p`, usually written as `{x : α // p x}`, is a type which represents all the elements `x : α` for which `p x` is true.
It is structurally a pair-like type, so if you have `x : α` and `h : p x` then `⟨x, h⟩ : {x // p x}`.
-/

/-
Mathematically inclined readers might want to think of `pick` as an ℕ-indexed family of terms
  `(pick n : {i : ℕ // i ≤ n})` for n ∈ ℕ
in which the type of each term depends on the index, e.g.,
  `pick 5 : {i : ℕ // i ≤ 5}`.
But what would be the type of `pick` itself?
We would like to express that `pick` is a function that takes an argument `n : ℕ` and returns a value of type `{i : ℕ // i ≤ n}`.
To capture this, we will write
  `pick : (n : ℕ) → {i : ℕ // i ≤ n}`
This is a dependent type: the type of the result depends on the value of the argument `n`.
(The variable name `n` itself is immaterial; we could also write `m` or `x`.)

Unless otherwise specified, a _dependent type_ means a type depending on a (non-type) term, as above, with `n : ℕ` as the term and `{i : ℕ // i ≤ n }` as the type that depends on it.
But:
* A type may also depend on another type, such as the type constructor `List` or the polymorphic type `fun α : Type ↦ α → α` of functions with the same domain and codomain.
* A term may depend on a type, such as the polymorphic identity function
    `fun α : Type ↦ fun x : α ↦ x`.
* And, of course, a term maty also depend on a term, such as `fun n : ℕ ↦ n + 2`.

In summary, there are four cases for `fun x ↦ t`:
* term `t` depending on term `x`: this is simply a function
* type `t` depending on type `x`: this is a type construction (e.g., `List`)
* type `t` depending on term `x`: this is a dependent type (in the narrow sense, e.g., `pick` above)
* term `t` depending on type `x`: this is a polymorphic term (e.g., the polymorphic identity function above)

## Dependent inductive types

The inductive types `List α` we have seen before falls within the simply typed fragment of Lean.
Inductive types may also depend on (non-type) terms.
A typical example is the type of lists of length n, or _vectors_:
-/

inductive Vec (α : Type) : Nat → Type :=
  | nil : Vec α 0
  | cons (a : α) {n : Nat} (v : Vec α n) : Vec α (n+1)

/-
The difference between parentheses and curly braces in the definition above is the implicitness of arguments.
When an argument is enclosed in curly braces, it is _implicit_, meaning Lean will attempt to infer this argument without us explicitly writing it down.
For example, we can write `cons 25 nil`, for which Lean infers that `n = 0`.

Thus, the term `Vec.cons 3 (Vec.cons 1 Vec.nil)` has type `Vec Nat 2`.
By encoding the vector length in the type, we can provide more precise information above the result of functions.
A function such as `Vec.reverse`, which reverses a vector, would map a value `Vec α n` to another value of the same type, with the same `n`.
And `Vec.zip`, which pairs up elements from two lists into a list of pairs, could require its two arguments to have the same length.
Fixed-length vectors and matrics are also useful in mathematics.

Unfornately, this more precise information comes at a cost.
Dependent inductive types cause difficulties when the terms they depend on are provably equal but not syntactically equal up to computation (e.g., `m + n` vs `n + m`).

The definitions below introduces conversions between lists and vectors:
-/

def listOfVec {α : Type} : ∀{n : Nat}, Vec α n → List α
  | _, Vec.nil => []
  | _, Vec.cons a v => a :: listOfVec v

def vecOfList {α : Type} : ∀xs : List α, Vec α (List.length xs)
  | [] => Vec.nil
  | x :: xs => Vec.cons x (vecOfList xs)

/-
The `listOfVec` conversion takes a type `α`, a length `n`, and a vector of length `n` over `α` as arguments and returns a list over `α`.
Although we do not care about the length `n`, it still needs to be an argument because it appears in the type of the third argument (vector).
We make the first two arguments, `α` and `n`, implicit since they can be inferred from the type of the third argument.

The `vecOfList` conversion takesatype `α` and a list over `α` as arguments and returns a vector of the same length as the list.
Lean's type checker is strong enough to determine that the two right-hand sides have the desired type.

Let's verify that converting a vector to a list preserves its length.
-/

theorem length_listOfVec {α : Type} (n : Nat) (v : Vec α n)
    : List.length (listOfVec v) = n := by
  induction v with
  | nil => rfl
  | cons a v' ih => simp [listOfVec]; exact ih

/-
In expositions of list types, we usually see the length function defined first, but here that would not be a very productive function to code.
Instead, let us try to implement vector concatenation.
-/

-- def app {α} n₁ (v₁ : Vec α n₁) n₂ (v₂ : Vec α n₂) : Vec α (n₁+n₂) :=
--   match n₁, v₁ with
--   | 0, Vec.nil => v₂
--   | m+1, Vec.cons a u => sorry

/-
Lean complains:
```
  type mismatch
    v₂
  has type
    Vec α n₂ : Type
  but is expected to have type
    Vec α (0 + n₂) : Type
```

Here, lean fails to prove that `n₂ = 0 + n₂`.
We need to do "type casting" here.
We will use Lean's macro to do so.
`h ▸ e` is a macro built on top of `Eq.rec` and `Eq.symm` definitions.
Given `h : a = b` and `e : p a`, the term `h ▸ e` has type `p b`.
You can also view `h ▸ e` as a "type casting" operation where you change the type of `e` by using `h`.

We could prove this fact directly, or try to find it in the Lean's library.
-/

#check fun n => Eq.symm (Nat.zero_add n)

example {α} n₁ (v₁ : Vec α n₁) n₂ (v₂ : Vec α n₂) : Vec α (n₁+n₂) :=
  match n₁, v₁ with
  | 0, Vec.nil => Eq.symm (Nat.zero_add n₂) ▸ v₂
  | m+1, Vec.cons a u => sorry

/-
Let's now try to implement the other case.
-/

-- def app {α} n₁ (v₁ : Vec α n₁) n₂ (v₂ : Vec α n₂) : Vec α (n₁+n₂) :=
--   match n₁, v₁ with
--   | 0, Vec.nil => Eq.symm (Nat.zero_add n₂) ▸ v₂
--   | m+1, Vec.cons a u => Vec.cons a (app m u n₂ v₂)

/-
Again, this fails with error
```
  type mismatch
    Vec.cons a (app m u n₂ v₂)
  has type
    Vec α (m + n₂ + 1) : Type
  but is expected to have type
    Vec α (m + 1 + n₂) : Type
```
-/

#check Nat.succ_add

def app {α} n₁ (v₁ : Vec α n₁) n₂ (v₂ : Vec α n₂) : Vec α (n₁+n₂) :=
  match n₁, v₁ with
  | 0, Vec.nil => Eq.symm (Nat.zero_add n₂) ▸ v₂
  | m+1, Vec.cons a u => Nat.succ_add m n₂ ▸ Vec.cons a (app m u n₂ v₂)

/-
Here, we see that our definition is more complicated, so that it is safer to use.

Let's try proving other properties between lists and vectors.
-/

theorem listOfVec_reverse α l
    : @listOfVec α (List.length l) (vecOfList l) = l := by
  sorry

/-
## references
* Anne Baanen, Alexander Bentkamp, Janmin Blanchette, Johannes Hölzl, Jannis Limperg. [The Hitchhiker's Guide to Logical Verification](https://raw.githubusercontent.com/blanchette/logical_verification_2023/main/hitchhikers_guide.pdf), version November 21, 2023.  Chapters 4.6, 5.10.
* Adam Chlipala. [Certified Programming with Dependent Types](http://adam.chlipala.net/cpdt/cpdt.pdf), version April 21, 2019
* [How do I convince the Lean 4 type checker that addition is commutative?](https://proofassistants.stackexchange.com/a/1386)
-/
