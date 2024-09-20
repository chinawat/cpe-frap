import Frap.Sort

/-
# Process algebra and refinement

In concurrent programming, the threads-and-locks shared-memory style is the most popular way.
Fundamentally imperative style, with side effects coordinating synchronization across threads, can be hard to reason about.
Another well-established (and increasingly popular) style is _message passing_, which is closer in spirit to functional programming.
In that world, there is, in fact, no memory at all, let alone shared memory.
Instead, state is incorporated into the text of thread code, and information passes from thread to thread by sending _messages_ over _channels_.

There are two main kinds of message passing.
In the _asynchronous_ or _mailbox_ style, a thread can deposit a message in a channel, even when no one is ready to receive the message immediately.
Later, a thread can come along and effectively dequeue the message from the channel.
In the _synchronous_ or _rendezvous_ style, a message send only executes when a matching receive, on the same channel, is available immediately.
The threds of the two complementary operations _rendezvous_ and pass the message in one atomic step.

Packages of semantics and proof techniques for such languages are often called _process algebras_, as they support an algebraic style of reasoning about the source code of message-passing programs.
That is, we prove laws very similar to the familiar equations of algebra and use those laws to "rewrite" inside larger processes, by replacing their subprocesses with others we have shown suitably equivalent.
It's a powerful technique for highly modular proofs, which we will develop here for one concrete synchronous language.
Well-known process algebra includes the π-calculus and the Calculus of Communicating Systems.

## An object language with synchronous message passing

We let `c` denote channels, and define possible processes as follows.
* `!c(v); p` (sends): send message `v` along channel `c` (we use an exclamation point to suggest "telling something"), then continues on with process `p`
* `?c(x). p` (receives): receive a message from channel `c` and binds it into parameter `x`, to be used in a subsequent process `p` that should have `x` as a free variable
* `νx. p` (fresh channel generation): crates a new _private_ channel to be used by the body process `p`, where we replace `x` therein with the channel that is chosen.  Following tradition, we use the Greek letter ν (nu) for this purpose.
* `block(c); p` (abstraction boundaries): prevents "the outside world" from sending `p` any messages on channel `c` or receiving any messages from `p` via `c`, i.e., `c` is treated as a local channel for `p`.
* `p₁ ‖ p₂` (parallel compositions): runs both processes in parallel
* `dup(p)` (duplications): acts just like infinitely many copies of `p` composed in parallel.  We use them to implement nonterminating "server" processes that are prepared to respond to many requests over particular channels.  In traditional process algebra, duplication fills the role that loops and recursion fill in conventional programming.
* `done` (the inert process): incapable of doing anything at all; it stands for a finished program.

### Small-step operational semantics

We give an operational semantics in the form of a _labeled transition system_.
That is, we not only express how a step takes us from one state to another, but we also associate each step with a _label_ that summarizes what happened.
Our labels include the _silent_ label `ε`, read labels `?c(v)`, and write labels `!c(v)`.
The latter two indicate that a thread has read a value from or written a value to channel `c`, respectively, and the parameter `v` indicates which values was read or written.
We write `p₁ / l → p₂` to say that process `p₁` steps to `p₂` by performing label `l`.
We use `p₁ → p₂` as an abbreviation for `p₁ / ε → p₂`.

#### Sends and receives

We start with the rules for sends and receives
```
  --------------------[!]
  !c(v); p / !c(v) → p

  -------------------------[?]
  ?c(x). p / ?c(v) → p[x↦v]
```
They record the action in the obvious way, but there is already an interesting wrinkle: the rule for receives _picks a value `v` nondeterministically_.
This nondeterminism is resolved by the next two rules, the rendezvous rules, which force a read label to match a write label precisely.
```
  p₁ / !c(v) → p₁'     p₂ / ?c(v) → p₂'
  -------------------------------------[R!?]
           p₁ ‖ p₂ → p₁' ‖ p₂'

  p₁ / ?c(v) → p₁'     p₂ / !c(v) → p₂'
  -------------------------------------[R?!]
           p₁ ‖ p₂ → p₁' ‖ p₂'
```

#### Fresh channel generations

A fresh channel generation can step according to any valid choice of command.
```
           c fresh
  ------------------------[fresh]
  νx. p → block(c); p[x↦c]
```

#### Abstraction boundaries

An abstraction boundary prevents steps with labels that mention the protected channel.
(We overload notation `c ∉ l` to indicat that channel `c` not appear in the send/receive position of label `l`.)
```
        p / l → p'     c ∉ l
  ------------------------------[block]
  block(c); p / l → block(c); p'
```

#### Parallel compositions

Any step can be lifted up out of a parallel composition.
```
        p₁ / l → p₁'
  ----------------------[par-L]
  p₁ ‖ p₂ / l → p₁' ‖ p₂

        p₂ / l → p₂'
  ----------------------[par-L]
  p₁ ‖ p₂ / l → p₁ ‖ p₂'
```

#### Duplications

Finally, a duplication can spawn a new copy ("thread") at any time.
```
  -------------------[dup]
  dup(p) → dup(p) ‖ p
```

### Example

Below is a tiny example of a process which consists of three parallel components. The channel name `x` is only known by the first two components.
  `νx. (!x(z); done ‖ ?x(y). !y(x); ?x(y). done ‖ ?z(v). !v(v); done)`
The first two components are able to communicate on the channel `x`, and the name `y` becomes bound to `z`.
The next step in the process is therefore
  `νx. (done ‖ !z(x); ?x(y). done ‖ ?z(v). !v(v); done)`
Note that the remaining `y` is not affected because it is defined in an inner scope.
The second and third parallel components can now communicate on the channel name `z`, and the name `v` becomes bound to `x`.
The next step in the process is now
  `νx. (done ‖ ?x(y). done ‖ !x(x); done)`
Note that since the local name `x` has been output, the scope of `x` is extended to cover the third component as well.
Finally, the channel `x` can be used for sending the name `x`.
After that all concurrently executing processes have stopped.
  `νx. (done ‖ done ‖ done)`

## Refinement between processes

The labeled-transition-system approach may seem a bit unwieldy for just explaining the behavior of programs.
Where it really pays off is in supporting a modular, algebraic reasoning style about processes, which we turn to next.

What sort of correctness theorems should we prove about processes?
The classic choice is to show that a more complex _implementation_ process is a _safe substitute_ for a simpler _specification_ process.
We will say that the implementation `p` _refines_ the specification `p'`.
Intuitively, such a claim means that any trace of labels that `p` could generate may also be generated by `p'`, so that `p` has _no more behaviors_ than `p'` has, though it may have fewer behaviors.
Crucially, in building traces of process executions, we ignore silent labels, only collecting the send and receive labels.

This condition is called _trace inclusion_, and though it is intuitive, it is not strong enough to support all of the composition properties that we will want.
Instead, we formalize refinement via _simulation_.

_Definition_: A binary relation `R` between processes is a _simulation_ when these two conditions hold:
* __silent steps match up__: when `p₁ R p₂` and `p₁ → p₁'`, there always exists `p₂'` such that `p₂ →* p₂'` and `p₁' R p₂'`
* __communication steps match up__: when when `p₁ R p₂` and `p₁ / l → p₁'` for l ≠ ε, there always exists `p₂''` and `p₂'` such that `p₂ →* p₂''`, `p₂'' / l → p₂'`, and `p₁' R p₂'`

Intuitively, `R` is a simulation when, starting with a pair of related processes, any step on the left can be match by a step on the right, taking us back into `R`.
The conditions are naturally illustrated with commuting diagrams.

          R
  p₁  --------> p₂
   |            |
   | ∀ →        | ∃ →*
   |            |
   v            v
  p₁' <-------- p₂'
         R⁻¹

          R
  p₁  --------> p₂
   |            |
   | ∀ /l→      | ∃ →* /l→
   |            |
   v            v
  p₁' <-------- p₂'
         R⁻¹

Simulations have quite a lot in common with the concept of invariants of transition systems.
Simulation can be seen as a kind of natural generalization of invariants, which are predicates over single states, into relations that apply to states of two different transition systems that need to evolve in (approximate) lock-step.

We define _refinement_ `p₁ ≤ p₂` to indicate that there exists a simulation `R` such taht `p₁ R p₂`.
Luckily, this somewhat involved definition is easily related back to our intuitions.

_Theorem_: If `p₁ ≤ p₂`, then every trace generated by `p₁` is also generated by `p₂`.
_Proof_: By induction on executions of `p₁`.

Refinement is also a preorder.

_Theorem_ (Reflexivity): `∀p, p ≤ p`
_Proof_: Choose equality as the simulation relation.

_Theorem_ (Transitivity): If `p₁ ≤ p₂` and `p₂ ≤ p₃`, then `p₁ ≤ p₃`.
_Proof_: The two premises respectively imply the existence of simulations R₁ and R₂.  Set the new simulation relation as R₂ ∘ R₁, defined to contain a pair (p, q) iff there exists `r` with `p R₁ r` and `r R₂ q`.

## The algebra of refinement

We now take a tour through some algebraic properties of refinement.

Perhaps the greatest pay-off from the refinement approach is that _refinement is a congruence for parallel composition_.

_Theorem_: If `p₁ ≤ p₁'` and `p₂ ≤ p₂'`, then `p₁ ‖ p₂ ≤ p₁' ‖ p₂'`.

This deceptively simple theorem statement packs a strong modularity punch!
We can verify a component in isolation and then connect to an arbitrary additional component, immediately concluding that the composition behaves properly.
The secret sauce, implicit in our formulation of the object language and refinement, is the labeled-transition-system style, where processes may generate receive labels nondeterministically.
In this way, we can reason about a process implicitly in terms of _every value that some other process might send to it when they are composed_, without needing to quantify explicitly over all other eligible processes.

A similar congruence property holds for duplication.

_Theorem_: If `p ≤ p'`, then `dup(p) ≤ dup(p')`.
_Proof_: The premise implies the existence of a simulation `R`.
We define a derived relation `Rᴰ` with these inference rules.
```
  p R p'
  -------
  p Rᴰ p'

       p R p'
  -----------------
  dup(p) Rᴰ dup(p')

  p₁ Rᴰ p₁'     p₂ Rᴰ p₂'
  -----------------------
    p₁ ‖ p₂ Rᴰ p₁' ‖ p₂'
```
`Rᴰ` is precisely the relation we need to finish the proof.
Intuitively, the challenge is that `dup(p)` includes infinitely many copies of `p`, each of which may evolve in a different way.
It is even possible for different copies to interact with each other through shared channels.
However, comparing intermediate states of `dup(p)` and `dup(p')`, we expect to see a shared backbone, where corresponding threads are related by the original simulation `R`.
The definition of `Rᴰ` formalizes that intuition of a shared backbone with `R` connecting corresponding leaves.

Here are a few more algebraic properties.
We sometimes rely on a predicate `neverUses(c, p)`, to express that, no matter how other threads interact with it, process `p` will never perform a send or receive operation on channel `c`.

_Theorem_: If `p ≤ p'`, then `block(c); p ≤ block(c); p'`.

_Theorem_: `block(c₁); block(c₂); p ≤ block(c₂); block(c₁); p`.

_Theorem_: If `neverUses(c, p₂)`, then `block(c); (p₁ ‖ p₂) ≤ (block(c); p₁) ‖ p₂`.

_Theorem_ (Handoff): If `neverUses(c, p[x↦v])`, then
    `block(c); ((!c(v); done) ‖ dup(?c(x). p)) ≤ p[x↦v]`.

The last theorem is notable for how it prunes down the space of possibilities given an infinitely duplicated server, where each thread is trying to receive from a channel.
If server threads never touch that channel after their initial receives, then most server threads will remain inert.
The one send `!c(v); done` is the only possible source of interaction with server threads, thanks to the abstraction barrier on `c`, and that one send can only awaken one server thread.
Thus, the whole composition behaves just like a single server thread, instantiated with the right input value.

A concrete example of the Handoff theorem in action is a refinement like this one, applying to a kind of forwarding chain between channels:
```
  p = block(c₁); block(c₂);
      (!c₁(v); done)
      ‖ dup(
        ?c₁(x). !c₂(x); done
      )
      ‖ dup(
        ?c₂(y). !c₃(y); done
      )
```
  `p ≤ !c₃(v); done`

Note that, without the abstraction boundaries at the start, this fact would not be derivable.
We would need to worry about meddlesome threads in our environment interacting directly with `c₁` or `c₂`, spoiling the protocol and forcing us to add extra cases to the right-hand side of the refinement.

### Structural congruence

Central to both the reduction semantics and the labelled transition semantics is the notion of _structural congruence_.
Two processes are structurally congruent if they are identical up to structure.
In particular, parallel composition is commutative and associative.

More precisely, structural congruence is defined as the least equivalence relation preserved by the process constructs and satisfying the following axioms.

* alpha conversion:
 * `P` ≡ `Q` if `Q` can be obtained from `P` by renaming one of more bound variables in P.

* axioms for parallel composition
 * `P ‖ Q` ≡ `Q ‖ P`
 * `(P ‖ Q) ‖ R` ≡ `P ‖ (Q ‖ R)`
 * `P ‖ done` ≡ `P`

* axioms for restriction
 * `νx. νy. P` ≡ `νy. νx. P`
 * `νx. done` ≡ `done`

* axiom for replication
 * `!P` ≡ `P ‖ !P`

* axiom relating restriction and parallel
 * `νx. (P ‖ Q)` ≡ ` (νx. P) ‖ Q` if `x` is not a free variable of `Q`

This last axiom is known as the "scope extension" axiom.
This axiom is central, since it describes how a bound name `x` may be extruded by an output action, causing the scope of `x` to be extended.
In cases where `x` is a free variable of `Q`, alpha-conversion may be used to allow extension to proceed.

## Linear logic, revisited

### "Of course" modality

There is another modality to linear logic that we did not talk about last time.
What if there are an infinite amount of a certain kind of resources?
We use the _of course_ modal operator `!A`, pronounced "of course `A`" or "bang `A`" to indicate that there is an infinite supply of `A`.

### Connection between process algebra and linear logic

To distinguish between processes and resources, we write `proc(P)` to refer to the resources associated with process `P`.

#### Process composition

This just corresponds to a `fork` operation that generates two concurrently operating processes `P` and `Q`.
  `fork: proc(P ‖ Q) ⊸ proc(P) ⊗ proc(Q)`

#### Termination

This just corresponds to an `exit` operation, eliminating the process.
  `exit: proc(done) ⊸ 1`

#### Fresh channel generation

The `νx. P` operation simply creates a fresh name `c` for use in `P`.
The freshness condition on `c` can be enforced easily by the corresponding condition when introducing the existential quantifier.
  `gen: proc(νx. P) ⊸ ∃c, proc(P[x↦c])`

#### Replication

This just treats the process as unrestricted resources so that as many copies of `P` can be generated as needed.
  `promote: proc(!P) ⊸ !proc(P)`

Coincidentally, this is achieved in linear logic with the "of course" modality that is also written as "!".

#### Reaction

Basic reaction is synchronous communication along a channel `x`.
  `input: proc(!c(v)) ⊗ proc(?c(x). p) ⊸ proc(p[x↦v])`
-/

/-
## references
* [Adam Chlipala.  Formal Reasoning about Programs, Chapter 21: Process Algebra and Refinement](http://adam.chlipala.net/frap/frap_book.pdf)
* [Frank Pfenning, 2002.  Linear Logic.](https://www.cs.cmu.edu/~fp/courses/15816-f01/handouts/linear.pdf)
* [Wikipedia: Process calculus](https://en.wikipedia.org/wiki/Process_calculus)
* [Wikipedia: π-calculus](https://en.wikipedia.org/wiki/%CE%A0-calculus)
* [Adam Chlipala.  Formal Reasoning about Programs, Messages and Refinement](https://github.com/achlipala/frap/blob/master/MessagesAndRefinement.v)
-/
