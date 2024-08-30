import Frap.SmallStep

/-
# Type systems

Our next major topic is _type systems_, static program analyses that classify expressions according to the "shapes" of their results.
We'll begin with a typed version of the simplest imaginable language, to introduce the basic idea of types and typing rules and the fundamental theorems about type systems: _type preservation_ and _progress_.

## Typed arithmetic expressions

To motivate the discussion of type systems, let's begin as usual with a tiny toy language.
We want it to have the potential for programs to go wrong because of run-time type errors, so we need something a tiny bit more complex than the language of constants and addition that we used earlier: a single kind of data (e.g., numbers) is too simple, but just two kinds (numbers and booleans) gives us enough material to tell an interesting story.

The language definition is completely routine.

### Syntax

Here is the syntax, informally:
```
  t ::= true
      | false
      | if t then t else t
      | 0
      | succ t
      | pred t
      | iszero t
```
And here it is formally:
-/

namespace TM

inductive Tm : Type :=
  | tru : Tm
  | fls : Tm
  | ite : Tm → Tm → Tm → Tm
  | zro : Tm
  | scc : Tm → Tm
  | prd : Tm → Tm
  | iszero : Tm → Tm

open Tm

/-
_Values_ are `true`, `false`, and numeric values...
-/

inductive BValue : Tm → Prop :=
  | bv_true : BValue tru
  | bv_false : BValue fls

inductive NValue : Tm → Prop :=
  | nv_0 : NValue zro
  | nv_succ t : NValue t → NValue (scc t)

open BValue
open NValue

abbrev value (t : Tm) := BValue t ∨ NValue t

/-
### Small-step operational semantics
-/

inductive Step : Tm → Tm → Prop :=
  | st_ifTrue t₁ t₂ : Step (ite tru t₁ t₂) t₁
  | st_ifFalse t₁ t₂ : Step (ite fls t₁ t₂) t₂
  | st_if c c' t₁ t₂ :
      Step c c' → Step (ite c t₁ t₂) (ite c' t₁ t₂)
  | st_succ t₁ t₁' : Step t₁ t₁' → Step (scc t₁) (scc t₁')
  | st_pred0 : Step (prd zro) zro
  | st_predSucc v : NValue v → Step (prd (scc v)) v
  | st_pred t₁ t₁' : Step t₁ t₁' → Step (prd t₁) (prd t₁')
  | st_iszero0 : Step (iszero zro) tru
  | st_iszeroSucc v : NValue v → Step (iszero (scc v)) fls
  | st_iszero t₁ t₁' :
      Step t₁ t₁' → Step (iszero t₁) (iszero t₁')

open Step

/-
Notice that the `Step` relation doesn't care about whether the expressioin being stepped makes global sense: it just checks that the operaton in the _next_ reduction step is being applied to the right kinds of operands.
For example, the term `succ true` cannot take a step, but the almost as obviously nonsensical term
  `succ (if true then true else true)`
can take a step (once, before becoming stuck)

### Normal forms and values

The first interesting thing to notice about this `Step` relation is that the strong progress theorem from the [SmallStep] chapter fails here.
That is, there are terms that are normal forms (they can't take a step) but not values (they are not included in our definition of possible "results of reduction").

Such terms are _stuck_.
-/

abbrev step_normal_form := normal_form Step

def stuck (t: Tm) : Prop :=
  step_normal_form t ∧ ¬ value t

/-
exercise (2-star)
-/
example : ∃ t, stuck t := by
  sorry

/-
However, although values and normal forms are _not_ the same in this language, the set of values is a subset of the set of normal forms.

This is important because it shows we did not accidentally define things so that some value could still take a step.
-/

/-
exercise (3-star)
Hint: You will reach a point in this proof where you need to use an induction to reason about a term that is known to be a numeric value.
This induction can be performed either over the term itself or over the evidence that it is a numeric value.
The proof goes through in either case, but you will find that one way is quite a bit shorter than the other.
For the sake of the exercise, try to complete the proof both ways.
-/
theorem value_is_nf t : value t → step_normal_form t := by
  sorry

/-
### Typing

The next critical observation is that, although this language has stuck terms, they are always nonsensical, mixing booleans and numbers in a way that we don't even _want_ to have a meaning.
We can easily exclude such ill-typed terms by defining a _typing relation_ that relates terms to the types (either numeric or boolean) of their final results.
-/

inductive Ty : Type :=
  | bool : Ty
  | nat : Ty

open Ty

/-
In informal notation, the typing relation is often written `⊢ t ∈ T` and pronounced "`t` has type `T`."
The `⊢` symbol is called a "turnstile."
Below, we're going to see richer typing relations where one or more additional "context" arguments are written to the left of the turnstile.
For the moment, the context is always empty.
-/

inductive HasType : Tm → Ty → Prop :=
  | t_true : HasType tru bool
  | t_false : HasType fls bool
  | t_if t₁ t₂ t₃ T :
      HasType t₁ bool → HasType t₂ T → HasType t₃ T
      → HasType (ite t₁ t₂ t₃) T
  | t_0 : HasType zro nat
  | t_succ t₁ : HasType t₁ nat → HasType (scc t₁) nat
  | t_pred t₁ : HasType t₁ nat → HasType (prd t₁) nat
  | t_iszero t₁ : HasType t₁ nat → HasType (iszero t₁) bool

open HasType

example  -- `⊢ if false then 0 else (succ 0) ∈ nat`
    : HasType (ite fls zro (scc zro)) nat := by
  apply t_if
  . apply t_false
  . apply t_0
  . apply t_succ
    apply t_0

/-
It's important to realize that the typing relation is a _conservative_ (or _static_) approximation: it does not consider what happens when the term is reduced.
In particular, it does not calculate the type of its normal form.
-/

example  -- `⊢ if false then zero else true ∉ bool`
    : ¬ HasType (ite fls zro tru) bool := by
  intro contra
  cases contra
  rename_i contra _
  cases contra

/-
exercise (1-star)
-/
example t : HasType (scc t) nat → HasType t nat := by
  sorry

/-
#### Canonical forms

The following two lemmas capture the fundamental fact that the definitions of boolean and numeric values agree with the typing relation.
-/

theorem bool_canonical t : HasType t bool → value t → BValue t := by
  intro ht hv
  cases hv
  . assumption
  . rename_i hn
    cases hn <;> cases ht

theorem nat_canonical t : HasType t nat → value t → NValue t := by
  intro ht hv
  cases hv
  . rename_i hb
    cases hb <;> cases ht
  . assumption

/-
### Progress

The typing relation enjoys two critical properties.

The first is that well-typed normal forms are not stuck.
Or, conversely, if a term is well typed, then either it is a value or it can take at least one step.
We call this _progress_.
-/

/-
exercise (3-star)
Complete the following informal proof:

_Theorem_: If `⊢ t ∈ T`, then either `t` is a value or else `t ~~> t'` for some `t'`.
_Proof_: By induction on a derivation of `⊢ t ∈ T`.

* If the last rule in the derivation is `t_if`, then `t = if t₁ then t₂ else t₃`, with `⊢ t₁ ∈ bool`, `⊢ t₂ ∈ T`, and `⊢ t₃ ∈ T`.
  By the IH, either `t₁` is a value or else `t₁` can step to some `t₁'`.
 * If `t₁` is a value, then by the canonical forms lemmas and the fact that `⊢ t₁ ∈ bool`, we have that `t₁` is a `BValue`, i.e., it is either `true` or `false`.
   If `t₁ = true`, then `t` steps to `t₂` by `st_ifTrue`, while if `t₁ = false`, then `t` steps to `t₃` by `st_ifFalse`.
   Either way, `t` can step, which is what we wanted to show.
 * If `t₁` itself can take a step, then by `st_if`, so can `t`.
/- **FILL IN HERE** -/
-/

/-
exercise (3-star)
Complete the formal proof of the `progress` property.
-/
theorem progress t T
    : HasType t T → value t ∨ ∃ t', Step t t' := by
  intro ht
  induction ht with
  | t_if t₁ t₂ t₃ T =>
    rename_i ih₁ ih₂ ih₃
    right; cases ih₁
    . -- t₁ is a value
      have h : BValue t₁ := by
        apply bool_canonical <;> assumption
      cases h
      . exists t₂; apply st_ifTrue
      . exists t₃; apply st_ifFalse
    . -- t₁ can take a step
      rename_i h
      obtain ⟨t₁', h₁⟩ := h
      exists ite t₁' t₂ t₃
      apply st_if; exact h₁
  | _ => sorry

/-
### Type preservation

The second critical property of typing is that, when a well-typed term takes a step, the result is a well-typed term (of the same type).
-/

/-
exercise (3-star)
Complete the following informal proof:

_Theorem_: If `⊢ t ∈ T` and `t ~~> t'`, then `⊢ t' ∈ T`.
_Proof_: By induction on a derivation of `⊢ t ∈ T`.

* If the last rule in the derivation is `t_if`, then `t = if t₁ then t₂ else t₃`, with `⊢ t₁ ∈ bool`, `⊢ t₂ ∈ T`, and `⊢ t₃ ∈ T`.
  Inspecting the rules for the small-step reduction relation and remembering that `t` is the form `if ...`, we see that the only ones that could have been used to prove `t ~~> t'` are `st_ifTrue`, `st_ifFalse`, or `st_if`.
 * If the last rule was `st_ifTrue`, then `t' = t₂`.
   But we know that `⊢ t₂ ∈ T`, so we are done.
 * If the last rule was `st_ifFalse`, then `t' = t₃`.
   But we know that `⊢ t₃ ∈ T`, so we are done.
 * If the last rule was `st_if`, then `t' = if t₁' then t₂ else t₃`, where `t₁ ~~> t₁'`.
   We know `⊢ t₁ ∈ bool`, so by the IH, `⊢ t₁' ∈ bool`.
   The `t_if` rule then gives us `⊢ if if t₁' then t₂ else t₃ ∈ T`, as required.
/- **FILL IN HERE** -/
-/

/-
exercise (2-star)
Complete the formal proof of the `preservation` property.
-/
theorem preservation t t' T
    : HasType t T → Step t t' → HasType t' T := by
  intro hT hE
  induction hT generalizing t' with
  | t_if =>
    rename_i ih₁ _ _
    cases hE
    . -- st_ifTrue
      assumption
    . -- st_ifFalse
      assumption
    . -- st_if
      apply t_if <;> try assumption
      apply ih₁; assumption
  | _ => sorry

/-
exercise (3-star)
Now prove the same property again by induction on the _evaluation_ derivation instead of on the typing derivation.
Begin by carefully reading and thinking about the first few lines of the above proofs to make sure you understand what each one is doing.
The setup for this proof is similar, but not exactly the same.
-/

theorem preservation' t t' T
    : HasType t T → Step t t' → HasType t' T := by
  sorry

/-
The preservation theorem is often called _subject reduction_, because it tells us what happens when the "subject" of the typing relation is reduced.
This terminology comes from thinking of typing statements as sentences, where the term is the subject and the type is the predicate.

### Type soundness

Putting progress and preservation together, we see that a well-typed term can never reach a stuck state.
-/

abbrev multistep := Multi Step

theorem soundness t t' T
    : HasType t T → multistep t t' → ¬ stuck t' := by
  intro hT P
  induction P with (intro contra; obtain ⟨R, S⟩ := contra)
  | multi_refl =>
    cases (progress _ _ hT)
    . -- value
      simp [*] at *
    . -- step
      simp [step_normal_form, normal_form, *] at *
  | multi_step =>
    rename_i ih; apply ih
    . apply preservation
      . apply hT
      . assumption
    . unfold stuck; constructor <;> assumption

/-
## references
* [Software Foundations, Volume 2 Programming Language Foundations: Type Systems](https://softwarefoundations.cis.upenn.edu/plf-current/Types.html)
-/
