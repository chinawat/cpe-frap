import Frap.Sort

/-
# Linear logic

We have seen Hoare logic, a logic that can help us reason with imperative programs.
There are many more logics for reasoning in a variety of domains.
We can use _linear logic_, proposed by French logician Jean-Yves Girard in 1987, to reason about state and one-time-use resources.

As a motivating example for linear logic, we consider the so-called _blocks world_, which is often used to illustrate planning problems in artificial intelligence.
It consists of various blocks stacked on a table and a robot arm that is capable of picking up and putting down one block at a time.
We are usually given an initial configuration and some goal to achieve.
```
      ______
    _|_
   |   |

  b
  a     c
______________ table
```
We would like to describe this situation, the legal moves, and the problem of achieving a particular goal in a logical form.

We start by defining predicates as follows:
* on(x, y): block x is on block y
* tb(x): block x is on the table
* holds(x): robot arm holds block x
* empty: robot arm is empty
* clear(x): the top of block x is clear

A state is described by a collection of propositions that are true.
For example, the state pictured above would be described as
  Δ₀ = {empty, tb(a), on(b, a), clear(b), tb(c), clear(c)}

A goal to be achieved can also be described as a logical proposition such as "on(a,b)".
We would like to develop a logical system so that we can prove a goal G from some assumptions Δ if and only if the goal G can be achieved from the initial state Δ.
In this kind of representation, plans correspond to proofs.
The immediate problem is how to describe legal moves.
Consider the following description:
  If the robot hand is empty, a block x is clear, and x is on y,  then we can pick up the block, that is, achieve a state where the robot hand holds x and y is clear.

One may be tempted to formulate this as a logical implication
  ∀ x y, empty ∧ clear(x) ∧ on(x, y) → holds(x) ∧ clear(y)
However, this encoding is incorrect.
With this axiom, we can derive contradictory propositions such as empty ∧ holds(b).
The problem is clear: logical assumptions remain true.
In other words, ordinary predicate logic has no notion of state.

One can try to solve this problem in a number of ways.
One way is to introduce a notion of time.
If we write ∘A to denote the truth of A at the next time step, then we might say
  ∀ x y, empty ∧ clear(x) ∧ on(x, y) → ∘(holds(x) ∧ clear(y))
Now the problem above has been solved, since propositions such as empty ∧ ∘holds(b) are not contradictory.
However, we now have the opposite problem: we have not expressesd that "everything else" stays the same when we pick up a block.
In fact, we don't really need a logic of time, but a logic of state.

Miraculously, this is quite easy to achieve by changing our rules on how assumptions may be used.
We write
  A₁, …, Aₙ ⊩ C
to denote that we can prove C from assumptions A₁, …, Aₙ, using every assumption _exactly once_.
Another reading of this judgment is:
  If we had resources A₁, …, Aₙ, we could achieve goal C.
We refer to the judgment above as a _linear hypothetical judgment_.
The order in which assumptions are presented is irrelevant, so we freely allow them to be exchanged.
We use the letter Δ to range over a collection of linear assumptions.

From our point of view, the reinterpretation of logical assumptions as consumable resources is the central insight in linear logic from which all else follows in a systematic fashion.
Such a seemingly small change has major consequences in properties of the logic and its logical connectives.
-/

inductive LinearTerm : Type :=
  -- atoms
  | l_atom : Prop → LinearTerm
  -- multiplicatives
  | l_lolli : LinearTerm → LinearTerm → LinearTerm
  | l_tensor : LinearTerm → LinearTerm → LinearTerm
  | l_unit : LinearTerm
  -- additives
  | l_with : LinearTerm → LinearTerm → LinearTerm
  | l_top : LinearTerm
  | l_plus : LinearTerm → LinearTerm → LinearTerm
  | l_zero : LinearTerm

open LinearTerm

infixr:20 " ⊸ " => l_lolli
infixl:40 " ⊗ " => l_tensor
infixl:30 " & " => l_with
infixl:30 " ⊕ " => l_plus

/-
First, we consider the laws that are derived from the nature of the linear hypothetical judgment itself, without regard to any logical connectives.

The first expresses that if we have a resource A, we can achieve goal A.
```
  ----- hyp
  A ⊩ A
```
Note that there may not be any leftover resources, since all resources must be used exactly once.

The second law in some sense defines the meaning of linear hypothetical judgments.
  If Δ ⊩ A and Δ', A ⊩ C, then Δ,Δ' ⊩ C
Informally: if we know how to achieve goal A from Δ, and if we know how to achieve C from A and Δ', then we can achieve C if we have both collections of resources, Δ and Δ'.
We write Δ,Δ' as concatenation of the resources.
This law is called a _substitution principle_, since it allows us to substitute a proof of A for uses of the assumption A in another deduction.
The substitution principle does not need to be assumed as a primitive rule of inference.
Instead, we want to assure that whenever we can derive the first two judgments, we can already derive the third directly.
This expresses that our logical laws have not violated the basic interpretation of the linear hypothetical judgment: we can never obtain more from a resource A than is allowable by our understanding of the linear hypothetical judgment.

Next, we introduce a few connectives, considering each in turn.

### Simultaneous conjunction

We write `A ⊗ B` (pronounced "A and B" or "A tensor B") if `A` and `B` are true in the same state.
For example, we should be able to prove A,B ⊩ A ⊗ B.
The rule for infering a simultaneous conjunction reads
```
  Δ ⊩ A     Δ' ⊩ B
  ----------------- ⊗I
    Δ,Δ' ⊩ A ⊗ B
```
Read from the conclusion to the premises:
  In order to achieve goal A ⊗ B, we divide our resources into Δ and Δ', and show how to achieve A using Δ and B using Δ'.
Note that the splitting of resources, viewed bottom-up, is a nondeterministic operation.

This is called an _introduction rule_, since it introduces a logical connective in the conclusion.
An introduction rule explains the meaning of a connective by explaining how to achieve it as a goal.

Conversely, we should also specify how to use our knowledge that we can achieve A ⊗ B.
This is specified in the _elimination rule_:
```
  Δ ⊩ A ⊗ B     Δ',A,B ⊩ C
  --------------------------⊗E
            Δ,Δ' ⊩ C
```
We read an elimination rule downward, from the premise to the conclusion:
  If we know that we can achieve A ⊗ B from Δ, we can proceed as if we had both A and B together with some resource Δ'.
  Whatever goal C we can achieve from these resources, we can achieve with the joint resources Δ and Δ'.

### Alternative conjunction

We write `A & B` (pronounced "A with B") if we can achieve goals `A` and `B` with the current resources, but only _alternatively_.
For example, if we have one dollar, we can buy a cup of tea or we can buy a cup of coffee, but we cannot buy them both at the same time.
For this reason, this is also called _internal choice_.
Do not confuse this with disjunction or "exclusive or", the way we often do in natural language!
A logical disjunction (also called _external choice_) would correspond to a vending machine that promises to give you tea or coffee, but you cannot choose between them.

The introduction rule for alternative conjunction appears to duplicate the resources
```
  Δ ⊩ A     Δ ⊩ B
  ----------------&I
      Δ ⊩ A & B
```
However, this is an illusion: since we will actually have to make a choice between A and B, we will only need one copy of the resources.

That we are making an internal choice is also apparent in the elimination rules.
If we know how to achieve A & B, we have to choose between two rules to obtain either A or B.
We can recover either A or B, but not both simultaneously.
Therefore, we have two elimination rules.
```
  Δ ⊩ A & B
  ---------&E_L
    Δ ⊩ A

  Δ ⊩ A & B
  ---------&E_R
    Δ ⊩ B
```

### Linear implication

The _linear implication_ or _resource implication_ internalizes the linear hypothetical judgment at the level of propositions: if we had resource A, we could achieve B.
This is written as `A ⊸ B` (pronounced "A linearly implies B" or "A lolli B") for the goal of achieving B with resource A.
```
    Δ,A ⊩ B
  ----------⊸I
  Δ ⊩ A ⊸ B
```

The elimination rule for A ⊸ B allows us to conclude that B can be achieved if we can achieve A.
```
  Δ ⊩ A ⊸ B     Δ' ⊩ A
  ----------------------⊸E
         Δ,Δ' ⊩ B
```
As in the case of simultaneous conjunction, we have to split the resources, devoting Δ to achieving A ⊸ B and Δ' to achieving A.

### Unit

The trivial goal which requires no resources is written as `1` (also called multiplicative truth).
```
  ---1I
  ⊩ 1
```

In this case, knowing 1 actually does give us some information, namely, that the resources we have can be consumed.
This is reflected in the elimination rule.
```
  Δ ⊩ 1     Δ' ⊩ C
  -----------------1E
       Δ,Δ' ⊩ C
```

Multiplicative truth is the unit of ⊗ in the sense that A ⊗ 1 is equivalent to A.

### Top

In many scenarios, the goal we want to achieve might not describe the complete final state, but only some aspect of the final state.
For example, in the robot-vs-block problem, we might want the final state to be only "on(a, b)" without worrying about anything else.
We can encode the remaining aspects of the goal that we do not care about with `⊤` (pronounced "top").

The goal ⊤ can _always_ be achieved, regardless of which resources we currently have.
We can also think of it as consuming all available resources.
```
  ------⊤I
  Δ ⊩ ⊤
```

Consequently, we have no information when we know ⊤, and there is no elimination rule for ⊤.

⊤ is the unit of alternative conjunction in the sense that A & ⊤ is equivalent to A, and follows the laws of constructive truth.

We can use ⊤ to specify incomplete goals.
For example, if we want to show that we can achieve a state where block a is on b, but we do not care about any other aspect of the state, we can ask if we can prove
  Δ₀ ⊩ on(a, b) ⊗ ⊤
where Δ₀ is the representation of the initial state.

### Disjunction

The _disjunction_ `A ⊕ B` (pronounced "A plus B"; also called _external choice_) is characterized by two introduction rules.
```
    Δ ⊩ A
  ----------⊕I_L
  Δ ⊩ A ⊕ B

    Δ ⊩ B
  ----------⊕I_R
  Δ ⊩ A ⊕ B
```

As in the case for constructive disjunction, we therefore have to distinguish two cases when we know that we can achieve A ⊕ B.
```
  Δ ⊩ A ⊕ B     Δ',A ⊩ C     Δ',B ⊩ C
  -------------------------------------⊕E
                 Δ,Δ' ⊩ C
```
Note that resources Δ' appear in both branches, since only one of those two derivations will actually be used to achieve C, depending on the derivation of A ⊕ B.

### Impossibility

The _impossibility_ `0` is the case of a disjunction between zero alternatives and, and is the unit of ⊕.
There is no introduction rule.
In the elimination rule, we have to consider no branches.
```
    Δ ⊩ 0
  ---------0E
  Δ,Δ' ⊩ C
```
-/


/-
We now formalize the rules of constructive linear logic as an inductive type.
-/

open Permutation

inductive ValidLinearJudgment : List LinearTerm → LinearTerm → Prop :=
  | vl_hyp A : ValidLinearJudgment [A] A
  | vl_exchange Δ Δ' A :
      Permutation Δ Δ' → ValidLinearJudgment Δ A
      → ValidLinearJudgment Δ' A
  | vl_subst Δ Δ' A C :
      ValidLinearJudgment Δ A → ValidLinearJudgment (Δ' ++ [A]) C
      → ValidLinearJudgment (Δ ++ Δ') C
  | vl_tensor_i Δ Δ' A B :
      ValidLinearJudgment Δ A → ValidLinearJudgment Δ' B
      → ValidLinearJudgment (Δ ++ Δ') (A ⊗ B)
  | vl_tensor_e Δ Δ' A B C :
      ValidLinearJudgment Δ (A ⊗ B) → ValidLinearJudgment (Δ'++[A,B]) C
      → ValidLinearJudgment (Δ ++ Δ') C
  | vl_with_i Δ A B :
      ValidLinearJudgment Δ A → ValidLinearJudgment Δ B
      → ValidLinearJudgment Δ (A & B)
  | vl_with_el Δ A B :
      ValidLinearJudgment Δ (A & B)
      → ValidLinearJudgment Δ A
  | vl_with_er Δ A B :
      ValidLinearJudgment Δ (A & B)
      → ValidLinearJudgment Δ B
  | vl_lolli_i Δ A B :
      ValidLinearJudgment (Δ++[A]) B
      → ValidLinearJudgment Δ (A ⊸ B)
  | vl_lolli_e Δ Δ' A B :
      ValidLinearJudgment Δ (A ⊸ B) → ValidLinearJudgment Δ' A
      → ValidLinearJudgment (Δ ++ Δ') B
  | vl_unit_i : ValidLinearJudgment [] l_unit
  | vl_unit_e Δ Δ' C :
      ValidLinearJudgment Δ l_unit → ValidLinearJudgment Δ' C
      → ValidLinearJudgment (Δ ++ Δ') C
  | vl_top_i Δ : ValidLinearJudgment Δ l_top
  | vl_plus_il Δ A B :
      ValidLinearJudgment Δ A
      → ValidLinearJudgment Δ (A ⊕ B)
  | vl_plus_ir Δ A B :
      ValidLinearJudgment Δ B
      → ValidLinearJudgment Δ (A ⊕ B)
  | vl_plus_e Δ Δ' A B C :
      ValidLinearJudgment Δ (A ⊕ B)
      → ValidLinearJudgment (Δ'++[A]) C → ValidLinearJudgment (Δ'++[B]) C
      → ValidLinearJudgment (Δ ++ Δ') C
  | vl_zero_e Δ Δ' C:
      ValidLinearJudgment Δ l_zero
      → ValidLinearJudgment (Δ ++ Δ') C

open ValidLinearJudgment

infix:10 " ⊩ " => ValidLinearJudgment

theorem valid_subst Δ Δ' a c :
    (Δ ⊩ a) → (Δ' ++ [a] ⊩ c)
    → (Δ ++ Δ' ⊩ c) := by
  intro ha hac
  sorry

/-
Using our intuitive understanding of the connectives, we can decide various judgments.
And, of course, we can back this up with proofs, given the rules above.
-/

theorem linear_uncurry a b c : [a ⊸ b ⊸ c] ⊩ (a ⊗ b) ⊸ c := by
  apply vl_lolli_i
  apply vl_exchange ([a ⊗ b] ++ [a ⊸ b ⊸ c])
  . apply perm_swap
  . apply vl_tensor_e
    . apply vl_hyp
    . -- [a ⊸ b ⊸ c] ++ [a, b] ⊩ c
      -- [a ⊸ b ⊸ c] ++ [a] ++ [b] ⊩ c
      apply vl_exchange ([a ⊸ b ⊸ c] ++ [a] ++ [b])
      . apply permutation_refl
      . apply vl_lolli_e
        . apply vl_lolli_e
          . apply vl_hyp
          . apply vl_hyp
        . apply vl_hyp

/-
Equivalence in linear logic is encoded with an internal choice, rather than a tensor.
This is because when we use the equivalence, we will start with one side and end up with the other, so we are choosing which side to use, requiring only one copy of the resources to be consumed.
-/

def linear_iff A B := (A ⊸ B) & (B ⊸ A)

infix:15 " ≣ " => linear_iff

/-
Now, we can prove various properties of linear logic.
-/

theorem tensor_dist_plus_l a b c : [] ⊩ a ⊗ (b ⊕ c) ≣ (a ⊗ b) ⊕ (a ⊗ c) := by
  apply vl_with_i
  . sorry
  . sorry

theorem tensor_dist_plus_r a b c : [] ⊩ (a ⊕ b) ⊗ c ≣ (a ⊗ c) ⊕ (b ⊗ c) := by
  sorry

theorem lolli_dist_with_l a b c : [] ⊩ a ⊸ (b & c) ≣ (a ⊸ b) & (a ⊸ c) := by
  sorry

theorem lolli_dist_plus_r a b c : [] ⊩ (a ⊕ b) ⊸ c ≣ (a ⊸ c) & (b ⊸ c) := by
  sorry

theorem linear_curry a b c : [(a ⊗ b) ⊸ c] ⊩ a ⊸ b ⊸ c := by
  sorry

theorem tensor_dist_into_with_r a b c : [] ⊩ (a & b) ⊗ c ⊸ (a ⊗ c) & (b ⊗ c) := by
  sorry

theorem plus_dist_into_with_r a b c : [] ⊩ (a & b) ⊕ c ⊸ (a ⊕ c) & (b ⊕ c) := by
  sorry

theorem unit_lolli_ident_l a : [] ⊩ l_unit ⊸ a ≣ a := by
  sorry

theorem lolli_top_top a : [] ⊩ a ⊸ l_top ≣ l_top := by
  sorry

/-
## references
* [Frank Pfenning, 2002.  Linear Logic.](https://www.cs.cmu.edu/~fp/courses/15816-f01/handouts/linear.pdf)
* [Wikipedia: Linear logic](https://en.wikipedia.org/wiki/Linear_logic)
-/
