/-
M0.2 sanity check — verify the shared-network parallel composition
shape compiles.

This file does NOT depend on `ProbActionSpec` (which is M1 W1 work).
It declares the *type-level shape* of the M0.2 decision: the state of
a composed system is `σ₁ × σ_net × σ₂` and actions are
`ι₁ ⊕ ι_net ⊕ ι₂`. The stub demonstrates that:

  1. `Sum`-coproducts for action labels work ergonomically in Lean 4.
  2. The `AsyncNet` mailbox model is expressible as plain data.
  3. A "two parties exchange one message" sanity example fits in
     ~30 lines.

After M1 W1 lands `ProbActionSpec`, the `parallelWithNet`
construction promoted from this stub should fit in ~50 lines in
`Leslie/Prob/Action.lean`.

See `docs/randomized-leslie-spike/03-parallel-state.md` for the
decision rationale and signatures this file mirrors.
-/

namespace Leslie.Prob.Spike

/-! ## Asynchronous network shape

`AsyncNet n Msg` is the canonical asynchronous mailbox: per (sender,
receiver) ordered pair, a multiset of in-flight messages. We use
`List` rather than Mathlib `Multiset` here to keep this file
Mathlib-independent (M0.2 is pure data; the Mathlib dep is for
M0.1/M0.3 trace-measure work). -/

/-- Per-pair list of in-flight messages. -/
structure AsyncNet (n : Nat) (Msg : Type) where
  inflight : Fin n → Fin n → List Msg

/-- Network actions: only delivery for the basic eventually-fair
model. Drop / reorder / duplicate would be additional constructors. -/
inductive AsyncNetAction (n : Nat) (Msg : Type) : Type
  | deliver (sender receiver : Fin n) (m : Msg) : AsyncNetAction n Msg

/-- Step semantics for delivery: returns `none` if the message is
not in flight; otherwise removes one copy. -/
def AsyncNet.step {n : Nat} {Msg : Type} [DecidableEq Msg]
    (net : AsyncNet n Msg) :
    AsyncNetAction n Msg → Option (AsyncNet n Msg)
  | .deliver s r m =>
    if m ∈ net.inflight s r then
      some { inflight := fun i j =>
        if i = s ∧ j = r then (net.inflight i j).erase m
        else net.inflight i j }
    else none

/-! ## Shared-state composition shape

Two parties + a network. State is the cross product. Actions are the
disjoint union — `Sum.inl` for party 1, `Sum.inr ∘ Sum.inl` for
network, `Sum.inr ∘ Sum.inr` for party 2.

The full version with `ProbActionSpec` action effects lifts these to
PMF transitions; this stub just shows the type-level skeleton. -/

/-- Composed state. -/
structure DistState (σ₁ σ_net σ₂ : Type) where
  s₁ : σ₁
  net : σ_net
  s₂ : σ₂

/-- Composed action labels. -/
abbrev DistAction (ι₁ ι_net ι₂ : Type) := ι₁ ⊕ ι_net ⊕ ι₂

/-- Lifters: each party's per-action footprint specifies how the
party reads + writes its own slice of state plus the network. -/
structure ActionLifter (σ_local σ_net ι : Type) where
  step : ι → σ_local → σ_net → Option (σ_local × σ_net)

/-- Network step lifter (no party state). -/
structure NetLifter (σ_net ι_net : Type) where
  step : ι_net → σ_net → Option σ_net

/-- The composed step relation, as a partial function over the
disjoint union of action sets. -/
def composedStep
    {σ₁ σ_net σ₂ ι₁ ι_net ι₂ : Type}
    (lift₁ : ActionLifter σ₁ σ_net ι₁)
    (liftN : NetLifter σ_net ι_net)
    (lift₂ : ActionLifter σ₂ σ_net ι₂)
    (a : DistAction ι₁ ι_net ι₂) (st : DistState σ₁ σ_net σ₂) :
    Option (DistState σ₁ σ_net σ₂) :=
  match a with
  | .inl i₁ =>
    match lift₁.step i₁ st.s₁ st.net with
    | some (s₁', net') => some { st with s₁ := s₁', net := net' }
    | none => none
  | .inr (.inl iN) =>
    match liftN.step iN st.net with
    | some net' => some { st with net := net' }
    | none => none
  | .inr (.inr i₂) =>
    match lift₂.step i₂ st.s₂ st.net with
    | some (s₂', net') => some { st with s₂ := s₂', net := net' }
    | none => none

/-! ## Sanity example: two parties exchange one message

Each party sends a single boolean to the other. Once both messages
are in transit, the network delivers them. We verify the
*signature-level* round-trip: starting from clean state with `s₁ = 0`,
`s₂ = 0`, both parties send, then deliver.

The example is purely structural — no probabilistic choice. It
demonstrates that the composition shape is functional / ergonomic.
-/

namespace Demo

abbrev N : Nat := 2

/-- Each party's local state: an outbox bit (Some = pending), an
inbox bit (Some = received). -/
structure Local where
  outbox : Option Bool
  inbox : Option Bool

/-- Party action labels: `send` or `recv`. The recv-side is
modeled as the party harvesting from the inbox; actual delivery is
a network action. -/
inductive PartyAction
  | send : PartyAction
  | harvest : PartyAction
  deriving DecidableEq

abbrev Net := AsyncNet N Bool
abbrev NetAction := AsyncNetAction N Bool

/-- Party-1 lifter: send moves outbox to network; harvest reads
inbox. -/
def party₁Lifter : ActionLifter Local Net PartyAction where
  step a loc net :=
    match a with
    | .send =>
      match loc.outbox with
      | some b =>
        some ({ loc with outbox := none },
              { inflight := fun i j =>
                  if i = (0 : Fin N) ∧ j = (1 : Fin N) then b :: net.inflight i j
                  else net.inflight i j })
      | none => none
    | .harvest => some (loc, net)  -- inbox is delivered by net step

def party₂Lifter : ActionLifter Local Net PartyAction where
  step a loc net :=
    match a with
    | .send =>
      match loc.outbox with
      | some b =>
        some ({ loc with outbox := none },
              { inflight := fun i j =>
                  if i = (1 : Fin N) ∧ j = (0 : Fin N) then b :: net.inflight i j
                  else net.inflight i j })
      | none => none
    | .harvest => some (loc, net)

/-- Network lifter via `AsyncNet.step`. The lifter expects action
first, state second; `AsyncNet.step` is in the opposite order, so
flip. -/
def netLifter : NetLifter Net NetAction where
  step := fun a net => net.step a

/-- Initial state: both parties have outboxes ready, empty network. -/
def init : DistState Local Net Local where
  s₁ := { outbox := some true, inbox := none }
  net := { inflight := fun _ _ => [] }
  s₂ := { outbox := some false, inbox := none }

/-- Sanity: `init` typechecks and `composedStep` accepts the
disjoint-union action labels. -/
example : DistState Local Net Local := init

example : Option (DistState Local Net Local) :=
  composedStep party₁Lifter netLifter party₂Lifter
    (.inl .send) init

end Demo

end Leslie.Prob.Spike
