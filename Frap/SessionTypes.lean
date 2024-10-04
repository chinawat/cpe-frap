/-
# Session types

Process algebra, as we met last time, can be helpful for modeling network protocols.
Here, multiple _parties_ step through a script of exchanging messages and making decisions based on message contents.
A buggy party might introduce a _deadlock_, where, say, party A is blocked waiting for a message from party B, while B is also waiting for A.
_Session types_ are a style of static type system that rule out deadlock while allowing convenient separate checking of each party, given a shared protocol type.

There is an almost unlimited variation of different versions of session types.
We still step through a progression of three variants here, and even by the end, there will be obvious protocols that don't fit the framework.
Still, we aim to convey the core ideas of the approach.

## Basic two-party session types

Each of our type systems will apply to the object language from `ProcessAlgebra` lecture.
Assume for now that a protocol involves exactly two parties.
Here is a simple type system, explaining a protocol's "script" from the perspective of one party.
```
  base types:  σ
  session types:  τ ::= !c(σ); τ | ?c(σ). τ | done
```

We model simple parties with no internal duplication or parallelism.
A session type looks like an abstracted version of a process, remembering only the _types_ of messages exchanged on channels, rather than their _values_.
A simple set of typing rules makes the connection
```
    v : σ     p : τ
  -------------------
  !c(v); p : !c(σ); τ


  ∀v : σ . p[x↦v] : τ
  -------------------
  ?c(x). p : ?c(σ). τ

  -----------
  done : done
```

The only wrinkle in these rules is the use of universal quantification for the receive rule, to force the body to type-check under any well-typed value read from the channel.
Actually, such proof obligations may be nontrivial when we encode this object language in a mixed-embedding style where the body `p` in the rule could include arbitrary computation, to choose a body based on the value `v` read from the channel.

### Example communication: online store
```
  def customer (product payment_info : string) :=
    !request_product(product);
    ?in_stock_or_not(worked : bool).
      if worked then
        !send_payment_info(payment_info);
        ?payment_success(worked_again : bool).
          if worked_again then
            !add_review((product, "awesome"));
            Done
          else
            Done
      else
        Done

  def merchant (in_stock payment_checker : string -> bool) :=
    ?request_product(product : string).
      if in_stock product then
        !in_stock_or_not(true);
        ?send_payment_info(payment_info : string).
          if payment_checker payment_info then
            !payment_success(true);
            ?add_review(_ : (string, string)).
              Done
          else
            !payment_success(false);
            Done
      else
        !in_stock_or_not(false);
        Done
```

For the rest of this lecture, we will interpret the object language from `ProcessAlgebra` as a transition system with one small change: we only allow silent steps.
That is, we only model whole programs, with no communication with "the environment."
As a result, we consider self-contained protocols.

A satisfying soundness theorem applies to our type system.
To state it, we first need the crucial operation of _complementing_ a session type.
```
  complement of !c(σ); τ = ?c(σ). (complement of τ)
  complement of ?c(σ). τ = !c(σ). (complement of τ)
  complement of done = done
```

It is apparent that complementation just swaps the sends and receives.
When the original session type tells one party what to do, the complement type tells the other party what to do.
The power of this approach is that we can write one global protocol description (the session type) and then check two parties' code against it separately.
A new version of one party can be dropped in without rechecking the other party's code.

Using complementation, we can give succinct conditions for deadlock freedom of a pair of parties.

_Theorem_: If `p₁ : τ` and `p₂ : complement of τ`, then it is an invariant of `p₁ ‖ p₂` that an intermediate process is either `done ‖ done` or can take a step.
_Proof_: By invariant induction, after strengthening the invariant to say that any intermediate process takes the from `p₁' ‖ p₂'`, where, for some type τ', we have `p₁' : τ'` and `p₂' : complement of τ'`.
The inductive case of the proof proceeds by simple inversion on the derivation of `p₁' : τ'`, where, by the definition of complement, it is apparent that any communication p₁' performs has a matching action at the start of p₂'.
The choice of τ' changes during such a step, to the "tail" of the old τ'.

## Dependent two-party session types

It is a boring protocol that follows such a regular communication pattern as our first type system accepts.
Rather, it tends to be crucial to change up the expected protocol steps, based on _values_ sent over channels.
It is natural to switch to a _dependent_ type system to strengthen our expressiveness.
That is, a communication type will allow its body type to depend on the value sent or received.
```
  session types τ ::= !c(x:σ); τ(x) | ?c(x:σ). τ(x) | done
```

Each nontrivial construct does more than give the base type that should be sent or received on or from a channel.
We also bind a variable `x`, to stand for the value sent or received.
It may be unintuitive that we must introduce a binder even for sends, when the sender is in control of which value will be sent.
The reason is that we must allow the sender to then continue with different subprotocols for different values that might be sent.
We should not force the sender's hand by fixing a value in advance, when that value might depend on arbitrary program logic.

Very little change is needed in the typing rules.
```
     v : σ     p : τ(v)
  ------------------------
  !c(v); p : !c(x:σ); τ(x)


   ∀v : σ . p[x↦v] : τ(v)
  ------------------------
  ?c(x). p : ?c(x:σ). τ(x)

  -----------
  done : done
```

Our deadlock-freedom property is easy to reestablish.

_Theorem_: If `p₁ : τ` and `p₂ : complement of τ`, then it is an invariant of `p₁ ‖ p₂` that an intermediate process is either `done ‖ done` or can take a step.
_Proof_: Literally the same proof as the last theorem.

## Multiparty session types

New complications arise when more than two parties are communicating in a protocol.
In a case of an online merchant, for instance, a customer can send orders to the merchant, and a warehouse may be asked by the merchant to be sure a product is in stock.
Many other such examples appear in the real world.

### Example communication: online store with warehouse
```
  def customer' (product payment_info : string) :=
    !request_product(product);
    ?in_stock_or_not(worked : bool).
      if worked then
        !send_payment_info(payment_info);
        ?payment_success(worked_again : bool).
          if worked_again then
            !add_review((product, "awesome"));
            Done
          else
            Done
      else
        Done

  def merchant' (payment_checker : string -> bool) :=
    ?request_product(product : string).
      !merchant_to_warehouse(product);
      ?warehouse_to_merchant(in_stock : bool).
        if in_stock then
          !in_stock_or_not(true);
          ?send_payment_info(payment_info : string).
            if payment_checker payment_info then
              !payment_success(true);
              ?add_review(_ : (string, string)).
                Done
            else
              !payment_success(false);
              Done
        else
          !in_stock_or_not(false);
          Done

  def warehouse (in_stock : string -> bool) :=
    ?merchant_to_warehouse(product : string).
      if in_stock product then
        !warehouse_to_merchant(true);
        Done
      else
        !warehouse_to_merchant(false);
        Done
```

Now it is no longer possible to start from one party's view of a protocol and compute any other party's view.
The reason is that each message only involves two parties.
Any other party will not see that message in its own session type, making it impossible to preserve that message in a complement-like operation.

Instead, we define one global session type that includes only "send" operations.
However, we name the parties and parameterize on a mapping `ℂ` from channels to unique parties that own their send and receive ends.
That is, for any given channel and operation on it (send and receive), precisely one party is given permission to perform the operation, and, indeed, when the time comes, that party is _obligated_ to perform the operation, to avoid deadlock.

With that view in mind, our type language gets even simpler.
```
  session types τ ::= !c(x:σ); τ(x) | done
```

For the online store example, we have the following type (where each channel has a clearly specified sender and receiver):
```
     !request_product(_ : string);
     !merchant_to_warehouse(_ : string);
     !warehouse_to_merchant(_ : bool);
     !in_stock_or_not(worked : bool);
     if worked then
       !send_payment_info(_ : string);
       !payment_success(worked_again : bool);
       if worked_again then
         !add_review(_ : (string, string));
         Done
       else
         Done
     else
       Done.
```

We redefine the typing judgment as `p :[α,b] τ`.
Here, `α` is the identifier of the party running `p`, and be is a boolean that, when set, enforces that `p`'s next action (if any) is a receive.
```
  v : σ     ℂ(c) = (α, β)     β ≠ α     p :[α,⊥] τ(v)
  ---------------------------------------------------
             !c(v); p :[α,⊥] !c(x:σ); τ(x)

  ℂ(c) = (β, α)     β ≠ α     ∀ v : σ . p[x↦v] :[α,⊥] τ(v)
  --------------------------------------------------------
                ?c(x). p :[α,b] !c(x:σ); τ(x)

  ℂ(c) = (β, γ)     β ≠ α     γ ≠ α     ∀ v : σ . p :[α,⊤] τ(v)
  -------------------------------------------------------------
                       p :[α,b] !c(x:σ); τ(x)

  ----------------
  done :[α,b] done
```

The first two rules encode the simple cases where the current party `α` is one of the two designated to step next in the protocol, as we verify by looking up the channel in `ℂ`.
It is important that the send and receive ends of the channel are owned by different parties, or we would clearly have a deadlock, as that party would either wait forever for a message from itself or try to futilely send itself a message!
The `≠` premises enforce that condition.
Also, the boolean flag enforces that we cannot be running a send operation if we have been instructed to run a receive next.
That flag is reset to false in recursive premises, since we only use the flag to express an obligation for the very next command.

The third rule is crucial: it applies to a process that is not participating in the next step of the protocol.
That is, we look up the owners of the channel that comes next, and we verify that neither owner is `α`.
In this case, we merely proceed to the next protocol step, leaving the process unchanged.
Crucially, we must be prep  ared for any value that might be exchanged in this skipped step, even though we do not see it ourselves.

Why does the last premise of the third rule set the boolean flag, forcing the next action to be a receive?
Otherwise, at some point in the protocol, we could have multiple parties trying to send messages.
In such a scenario, there might not be a unique step that the composed parties can take.
The proofs are easier if we can assume deterministic execution within a protocol, which is why we introduced this static restriction.

To amend our theorem statement, we need to characterize when a process implements a set of parties correctly.
We use the judgment `p :ℓ τ` to that end, where `p` is the process, `ℓ` is a list of all involved parties, and `τ` is the type they must follow collectively.
```
  ----------
  done :[] τ

  p₁ :[α,⊥] τ     p₂ :ℓ τ
  -----------------------
     p₁ ‖ p₂ :(α::ℓ) τ
```

The heart of the proof is demonstrating the existence of a unique sequence of steps to a point where all parties are done.
Here is a sketch of the key lemmas.

_Lemma_: If `p :ℓ done`, then `p` can't take any silent step.
_Proof_: By induction on any derivation of a silent step, followed by inversion on `p :ℓ done`.

_Lemma_: If `p :ℓ !c(x:σ); τ(x)` and at least one of sender or receiver of channel `c` is missing from `ℓ`, then `p` can't take any silent step.
_Proof_: By induction on any derivation of a silent step, followed by inversion on `p :ℓ !c(x:σ); τ(x)`.

_Lemma_: Assume that `ℓ` is a duplicate-free list of parties excluding both sender and receiver of channel `c`.
If `p :ℓ !c(x:σ); τ(x)`, then for any `v:σ`, we have `p :ℓ τ(v)`.
In other words, when we have well-typed code for a set of parties that do not participate in the first step of a protocol, that code remains well-typed when we advanced to the next protocol step.
_Proof_: By induction on the derivation of `p :ℓ !c(x:σ); τ(x)`.

_Lemma_: Assume that `ℓ` is a duplicate-free list of parties, at least comprehensive enough to include the sender of channel `c`.
However, `ℓ` should exclude the receiver of `c`.
If `p :ℓ !c(x:σ); τ(x)` and `p / !c(v) → p'`, then `p' :ℓ τ(v)`.
_Proof_: By inducion on steps followed by inversion on multiparty typing.
As we step through elements of `ℓ`, we expect to "pass" parties that do not participate in the current protocol step.
The last lemma lets us justify those passings.

_Theorem_: Assume that `ℓ` is a duplicate-free list of _all_ parties for a protocol.
If `p :ℓ τ`, then it is an invariant of `p` that an intermediate process is either inert (made up only of `done`s and parallel compositions) or can take a step.
_Proof_: By invariant induction, after strengthening the invariant to say that any intermediate process `p'` satisfies `p' :ℓ τ'` for some `τ'`.
The inductive case uses the first lemma to rule out steps by finished protocols, and it uses the second lemma to rule out cases that are impossible because parties that are scheduled to go next are not present in `ℓ`.
Interesting cases are where we find that one of the active parties is at the head of `ℓ`.
That party either sends or receives.
In the first case, we appeal to the last lemma to find a receiver among the remaining parties.
In the second case, we appeal to an analogous lemma (not stated here) to find a sender.
.
The other crucial case of the proof is showing that existence of a multiparty typing implies that, if a process is not inert, it can take a step.
The reasoning is quite similar to in the inductive case, but where instead of  showing that any possible step preserves typing, we demonstrate that a particular step exists.
The head of the session type telegraphs what step it is: for the communication at the head of the type, the assigned sending party sends to the assigned receiving party.
-/

/-
## references
* [Adam Chlipala.  Formal Reasoning about Programs, Chapter 22: Session Types](http://adam.chlipala.net/frap/frap_book.pdf)
* [Adam Chlipala.  Formal Reasoning about Programs, Session Types](https://github.com/achlipala/frap/blob/master/SessionTypes.v)
-/
