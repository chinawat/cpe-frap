import Frap.Equiv
import Frap.SmallStep

open Imp
open AExp
open BExp
open Com

open Multi

/-
## Small-step Imp

Here's a small-step version of the Imp operational semantics.

The small-step reduction relations for arithmetic and boolean expressions are straightforward extensions of the tiny language we've been working up previously.
-- To make them easier to read, we introduce the symbolic notations `~~>a` and `~~>b` for the arithmetic and boolean step relations.
-/

inductive AVal : AExp → Prop :=
  | av_num : ∀ n, AVal (a_num n)

/-
We are not actually going to bother to define boolean values, since they aren't needed in the definition of `BStep` below (why?), though they might be if our language were a bit more complicated (why?).
-/

inductive AStep (st : State) : AExp → AExp → Prop :=
  | as_id : ∀ v, AStep st (a_id v) (a_num (st v))
  | as_plus1 : ∀ a₁ a₁' a₂,
      AStep st a₁ a₁'
      → AStep st (a_plus a₁ a₂) (a_plus a₁' a₂)
  | as_plus2 : ∀ v₁ a₂ a₂',
      AVal v₁ → AStep st a₂ a₂'
      → AStep st (a_plus v₁ a₂) (a_plus v₁ a₂')
  | as_plus : ∀ (v₁ v₂ : Nat),
      AStep st (a_plus (a_num v₁) (a_num v₂)) (a_num (v₁ + v₂))
  | as_minus1 : ∀ a₁ a₁' a₂,
      AStep st a₁ a₁'
      → AStep st (a_minus a₁ a₂) (a_minus a₁' a₂)
  | as_minus2 : ∀ v₁ a₂ a₂',
      AVal v₁ → AStep st a₂ a₂'
      → AStep st (a_minus v₁ a₂) (a_minus v₁ a₂')
  | as_minus : ∀ (v₁ v₂ : Nat),
      AStep st (a_minus (a_num v₁) (a_num v₂)) (a_num (v₁ - v₂))
  | as_mult1 : ∀ a₁ a₁' a₂,
      AStep st a₁ a₁'
      → AStep st (a_mult a₁ a₂) (a_mult a₁' a₂)
  | as_mult2 : ∀ v₁ a₂ a₂',
      AVal v₁ → AStep st a₂ a₂'
      → AStep st (a_mult v₁ a₂) (a_mult v₁ a₂')
  | as_mult : ∀ (v₁ v₂ : Nat),
      AStep st (a_mult (a_num v₁) (a_num v₂)) (a_num (v₁ * v₂))

open AStep

inductive BStep (st : State) : BExp → BExp → Prop :=
  | bs_eq1 : ∀ a₁ a₁' a₂,
      AStep st a₁ a₁'
      → BStep st (b_eq a₁ a₂) (b_eq a₁' a₂)
  | bs_eq2 : ∀ v₁ a₂ a₂',
      AVal v₁ → AStep st a₂ a₂'
      → BStep st (b_eq v₁ a₂) (b_eq v₁ a₂')
  | bs_eq : ∀ (v₁ v₂ : Nat),
      BStep st (b_eq (a_num v₁) (a_num v₂))
          (if v₁ == v₂ then b_true else b_false)
  | bs_neq1 : ∀ a₁ a₁' a₂,
      AStep st a₁ a₁'
      → BStep st (b_neq a₁ a₂) (b_neq a₁' a₂)
  | bs_neq2 : ∀ v₁ a₂ a₂',
      AVal v₁ → AStep st a₂ a₂'
      → BStep st (b_neq v₁ a₂) (b_neq v₁ a₂')
  | bs_neq : ∀ (v₁ v₂ : Nat),
      BStep st (b_neq (a_num v₁) (a_num v₂))
          (if v₁ != v₂ then b_true else b_false)
  | bs_le1 : ∀ a₁ a₁' a₂,
      AStep st a₁ a₁'
      → BStep st (b_le a₁ a₂) (b_le a₁' a₂)
  | bs_le2 : ∀ v₁ a₂ a₂',
      AVal v₁ → AStep st a₂ a₂'
      → BStep st (b_le v₁ a₂) (b_le v₁ a₂')
  | bs_le : ∀ (v₁ v₂ : Nat),
      BStep st (b_le (a_num v₁) (a_num v₂))
          (if v₁ <= v₂ then b_true else b_false)
  | bs_notStep : ∀ b₁ b₁',
      BStep st b₁ b₁'
      → BStep st (b_not b₁) (b_not b₁')
  | bs_notTrue : BStep st (b_not b_true) b_false
  | bs_notFalse : BStep st (b_not b_false) b_true
  | bs_andStep : ∀ b₁ b₁' b₂,
      BStep st b₁ b₁'
      → BStep st (b_and b₁ b₂) (b_and b₁' b₂)
  | bs_andFalse : ∀ b₂,
      BStep st (b_and b_false b₂) b_false
  | bs_andTrueStep : ∀ b₂ b₂',
      BStep st b₂ b₂'
      → BStep st (b_and b_true b₂) (b_and b_true b₂')
  | bs_andTrueTrue :
      BStep st (b_and b_true b_true) b_true
  | bs_andTrueFalse :
      BStep st (b_and b_true b_false) b_false
  | bs_orStep : ∀ b₁ b₁' b₂,
      BStep st b₁ b₁'
      → BStep st (b_or b₁ b₂) (b_or b₁' b₂)
  | bs_orTrue : ∀ b₂,
      BStep st (b_or b_true b₂) b_true
  | bs_orFalseStep : ∀ b₂ b₂',
      BStep st b₂ b₂'
      → BStep st (b_or b_false b₂) (b_or b_false b₂')
  | bs_orFalseTrue :
      BStep st (b_or b_false b_true) b_true
  | bs_orFalseFalse :
      BStep st (b_or b_false b_false) b_false

open BStep

/-
The semantics of commands is the interesting part.
We need two small tricks to make it work:
* We use `skip` as a "command value," i.e., a command that has reached a normal form.
 * An assignment command reduces to `skip` (and an updated state)
 * The sequencing command waits until its left-hand subcommand has reduced to `skip`, then throws it away so that reduction can continue with the right-hand subcommand.
* We reduce a `while` command a single step by transforming it into a conditional followed by the same `while`.

(There are other ways of achieving the effect of the latter trick, but they all share the feature that the original `while` command is stashed away somewhere while a single copy of the loop body is being reduced.)
-/

inductive CStep : (Com × State) → (Com × State) → Prop :=
  | cs_asgnStep : ∀ st v a₁ a₁',
      AStep st a₁ a₁'
      → CStep (c_asgn v a₁, st) (c_asgn v a₁', st)
  | cs_asgn : ∀ st v (n : Nat),
      CStep (c_asgn v (a_num n), st) (c_skip, x !-> n; st)
  | cs_seqStep : ∀ st c₁ c₁' st' c₂,
      CStep (c₁, st) (c₁', st')
      → CStep (c_seq c₁ c₂, st) (c_seq c₁' c₂, st')
  | cs_seqFinish : ∀ st c₂,
      CStep (c_seq c_skip c₂, st) (c₂, st)
  | cs_ifStep : ∀ st b₁ b₁' c₁ c₂,
      BStep st b₁ b₁'
      → CStep (c_if b₁ c₁ c₂, st) (c_if b₁' c₁ c₂, st)
  | cs_ifTrue : ∀ st c₁ c₂,
      CStep (c_if b_true c₁ c₂, st) (c₁, st)
  | cs_ifFalse : ∀ st c₁ c₂,
      CStep (c_if b_false c₁ c₂, st) (c₂, st)
  | cs_while : ∀ st b₁ c₁,
      CStep (c_while b₁ c₁, st)
        (c_if b₁ (c_seq c₁ (c_while b₁ c₁)) c_skip, st)

/-
## Concurrent Imp

To show the power of this definitional style, let's enrich Imp with a new form of command that runs two subcommands in parallel and terminates when both have terminated.
To reflect the unpredictability of scheduling, the actions of the subcommands may be interleaved in any order, but they share the same memory and can communicate by reading and writing the same variables.

For example:
* This program sets `x` to `0` in one thread and `1` in another, leaving it set to either `0` or `1` at the end:
    `x := 0 <|> x := 1`
* This one leaves `x` set to one of `0`, `1`, `2`, or `3` at the end:
    `x := 0; (x := x + 2 <|> x := x + 1 <|> x := 0)`
-/

namespace CImp

inductive Com : Type :=
  | c_skip : Com
  | c_asgn : String → AExp → Com
  | c_seq : Com → Com → Com
  | c_if : BExp → Com → Com → Com
  | c_while : BExp → Com → Com
  | c_par : Com → Com → Com  /- ← NEW: c₁ <|> c₂ -/

open Com

inductive CStep : (Com × State) → (Com × State) → Prop :=
  /- old part -/
  | cs_asgnStep : ∀ st v a₁ a₁',
      AStep st a₁ a₁'
      → CStep (c_asgn v a₁, st) (c_asgn v a₁', st)
  | cs_asgn : ∀ st v (n : Nat),
      CStep (c_asgn v (a_num n), st) (c_skip, v !-> n; st)
  | cs_seqStep : ∀ st c₁ c₁' st' c₂,
      CStep (c₁, st) (c₁', st')
      → CStep (c_seq c₁ c₂, st) (c_seq c₁' c₂, st')
  | cs_seqFinish : ∀ st c₂,
      CStep (c_seq c_skip c₂, st) (c₂, st)
  | cs_ifStep : ∀ st b₁ b₁' c₁ c₂,
      BStep st b₁ b₁'
      → CStep (c_if b₁ c₁ c₂, st) (c_if b₁' c₁ c₂, st)
  | cs_ifTrue : ∀ st c₁ c₂,
      CStep (c_if b_true c₁ c₂, st) (c₁, st)
  | cs_ifFalse : ∀ st c₁ c₂,
      CStep (c_if b_false c₁ c₂, st) (c₂, st)
  | cs_while : ∀ st b₁ c₁,
      CStep (c_while b₁ c₁, st)
        (c_if b₁ (c_seq c₁ (c_while b₁ c₁)) c_skip, st)
  /- new part -/
  | cs_par1 : ∀ st c₁ c₁' c₂ st',
      CStep (c₁, st) (c₁', st')
      → CStep (c_par c₁ c₂, st) (c_par c₁' c₂, st')
  | cs_par2 : ∀ st c₁ c₂ c₂' st',
      CStep (c₂, st) (c₂', st')
      → CStep (c_par c₁ c₂, st) (c_par c₁ c₂', st')
  | cs_parDone : ∀ st,
      CStep (c_par c_skip c_skip, st) (c_skip, st)

open CStep

#check Multi CStep

/-
Among the many interesting properties of this language is the fact that the following program can terminate with the variable `x` set to any value.

```
    y := 1
  <|>
    while (y == 0) do x := x + 1 end
```
-/

def par_loop : Com :=
  c_par
    (c_asgn y (a_num 1))
    (c_while (b_eq (a_id y) (a_num 0))
      (c_asgn x (a_plus (a_id x) (a_num 1))))

/-
In particular, it can terminate with `x` set to `0`.
-/

example : ∃ st',
    Multi CStep (par_loop, empty) (c_skip, st')
    ∧ st' x = 0 := by
  constructor  -- exists y !-> 1; empty
  constructor
  . apply multi_step
    . apply cs_par1; apply cs_asgn
    . apply multi_step
      . apply cs_par2; apply cs_while
      . apply multi_step
        . apply cs_par2; apply cs_ifStep
          apply bs_eq1; apply as_id
        . apply multi_step
          . apply cs_par2; apply cs_ifStep
            apply bs_eq
          . simp [update]; apply multi_step
            . apply cs_par2; apply cs_ifFalse
            . apply multi_R
              apply cs_parDone
  . rfl

/-
It can also terminate with `x` set to `2`:

The following proofs are particular "deep": they require following the small-step semantics in a particular strategy to exhibit the desired behavior.
For that reason, they are a bit awkward to write with "forced bullets."
Nevertheless, we keep them because they emphasize that the witness for an evaluation by small-step semantics has a size that is proportional to the number of steps taken.
It would be an interesting exercise to write Lean tactics that can help automate the construction of such proofs, but such a tactic would need to "search" among the many possibilities.
-/

example : ∃ st',
    Multi CStep (par_loop, empty) (c_skip, st')
    ∧ st' x = 2 := by
  constructor
  constructor
  . apply multi_step
    . apply cs_par2; apply cs_while
    . apply multi_step
      . apply cs_par2; apply cs_ifStep
        apply bs_eq1; apply as_id
      . apply multi_step
        . apply cs_par2; apply cs_ifStep
          apply bs_eq
        . simp [empty]; apply multi_step
          . apply cs_par2; apply cs_ifTrue
          . apply multi_step
            . apply cs_par2; apply cs_seqStep
              apply cs_asgnStep
              apply as_plus1; apply as_id
            . apply multi_step
              . apply cs_par2; apply cs_seqStep
                apply cs_asgnStep; apply as_plus
              . apply multi_step
                . apply cs_par2; apply cs_seqStep
                  apply cs_asgn
                . simp [empty]; apply multi_step
                  . apply cs_par2; apply cs_seqFinish
                  . apply multi_step
                    . apply cs_par2; apply cs_while
                    . apply multi_step
                      . apply cs_par2; apply cs_ifStep
                        apply bs_eq1; apply as_id
                      . apply multi_step
                        . apply cs_par2; apply cs_ifStep
                          apply bs_eq
                        . simp [empty]; apply multi_step
                          . apply cs_par2; apply cs_ifTrue
                          . apply multi_step
                            . apply cs_par2; apply cs_seqStep
                              apply cs_asgnStep
                              apply as_plus1; apply as_id
                            . apply multi_step
                              . apply cs_par2; apply cs_seqStep
                                apply cs_asgnStep; apply as_plus
                              . apply multi_step
                                . apply cs_par2; apply cs_seqStep
                                  apply cs_asgn
                                . simp [update]; apply multi_step
                                  . apply cs_par2; apply cs_seqFinish
                                  . apply multi_step
                                    . apply cs_par1; apply cs_asgn
                                    . apply multi_step
                                      . apply cs_par2; apply cs_while
                                      . apply multi_step
                                        . apply cs_par2; apply cs_ifStep
                                          apply bs_eq1; apply as_id
                                        . apply multi_step
                                          . apply cs_par2; apply cs_ifStep
                                            apply bs_eq
                                          . simp [update]; apply multi_step
                                            . apply cs_par2; apply cs_ifFalse
                                            . apply multi_R
                                              apply cs_parDone
  . rfl

/-
More generally...
-/

/-
exercise (3-star)
-/

theorem par_body_n__Sn n st
    : st x = n ∧ st y = 0
      → Multi CStep (par_loop, st) (par_loop, x !-> n + 1; st) := by
  sorry

/-
exercise (3-star)
-/

theorem par_body_n n st
    : st x = 0 ∧ st y = 0
      → ∃ st', Multi CStep (par_loop, st) (par_loop, st')
          ∧ st' x = n ∧ st' y = 0 := by
  sorry

/-
... the above loop can exit with `x` having any value whatsoever.
-/

theorem par_loop_any_x n
    : ∃ st', Multi CStep (par_loop, empty) (c_skip, st')
        ∧ st' x = n := by
  let h := par_body_n n empty
  simp [empty] at h
  obtain ⟨st', ⟨h', ⟨hx, _⟩⟩⟩ := h
  exists y !-> 1; st'
  constructor
  . apply multi_trans
    . apply h'
    . apply multi_step
      . apply cs_par1; apply cs_asgn
      . apply multi_step
        . apply cs_par2; apply cs_while
        . apply multi_step
          . apply cs_par2; apply cs_ifStep
            apply bs_eq1; apply as_id
          . apply multi_step
            . apply cs_par2; apply cs_ifStep
              apply bs_eq
            . simp [update]; apply multi_step
              . apply cs_par2; apply cs_ifFalse
              . apply multi_R
                apply cs_parDone
  . simp [update]; assumption

end CImp

/-
## references
* [Software Foundations, Volume 2 Programming Language Foundations: Small-Step Operational Semantics](https://softwarefoundations.cis.upenn.edu/plf-current/Smallstep.html)
-/
