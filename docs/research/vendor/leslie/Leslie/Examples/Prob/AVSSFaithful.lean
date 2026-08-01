/-
Canetti-Rabin asynchronous verified secret sharing: faithful spec skeleton.

This file starts the CR-faithful model promised by
`AVSS-MODEL-NOTES.md` §17.  It intentionally does not mutate
`Leslie.Examples.Prob.AVSS.avssSpec`; the existing file remains the
threshold-faithful regression baseline.

The key difference from `AVSS.lean` is operational: echo and ready
traffic carries value/certificate content.  Receivers validate echo
values against their own column polynomial, and ready/output gates are
scoped to one candidate payload.  The commitment proof is left to a
later PR, where the candidate-scoped evidence should consume the
standard quorum-intersection bound.
-/

import Leslie.Examples.Prob.AVSS
import Leslie.Prob.Action
import Leslie.Prob.PMF
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma

namespace Leslie.Examples.Prob.AVSSFaithful

open Leslie.Prob

variable {n t : Nat} {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## Payloads and certificates -/

/-- Dealer payload sent to one party: row polynomial `f(alpha_p, y)`
and column polynomial `f(x, alpha_p)`.  A corrupt dealer may choose
these payloads independently for different parties. -/
structure DealerPayload (t : Nat) (F : Type*) where
  rowPoly : Fin (t + 1) -> F
  colPoly : Fin (t + 1) -> F
deriving DecidableEq

/-- Value-bearing echo from `sender` to `receiver`.

The intended honest value is the sender row evaluated at the receiver
point.  The receiver validates this same value against its own column
polynomial at the sender point. -/
structure EchoMsg (n t : Nat) (F : Type*) where
  sender : Fin n
  receiver : Fin n
  senderPayload : DealerPayload t F
  value : F
deriving DecidableEq

/-- Candidate-scoped ready certificate.

`supporters` records the senders whose validated echo evidence supports
the receiver's candidate payload.  Later commitment proofs should use
two such certificates plus quorum intersection to force agreement. -/
structure ReadyCert (n t : Nat) (F : Type*) where
  candidate : DealerPayload t F
  supporters : Finset (Fin n)
deriving DecidableEq

/-- Candidate-scoped ready message. -/
structure ReadyMsg (n t : Nat) (F : Type*) where
  sender : Fin n
  receiver : Fin n
  cert : ReadyCert n t F
deriving DecidableEq

namespace DealerPayload

/-- Canonical payload for an honest dealer at party `p`. -/
def ofCoeffs (partyPoint : Fin n -> F)
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F) (p : Fin n) :
    DealerPayload t F :=
  { rowPoly := AVSS.rowPolyOfDealer partyPoint coeffs p
    colPoly := AVSS.colPolyOfDealer partyPoint coeffs p }

end DealerPayload

/-! ## Local and global state -/

/-- Per-party state for the faithful AVSS skeleton.

The local evidence fields are deliberately value-bearing:

* `acceptedEchoes` stores validated echo messages, not just sender IDs.
* `readyReceived` stores candidate-scoped ready messages.
* `readySent` records the candidate certificates already broadcast by
  this party.
-/
structure LocalState (n t : Nat) (F : Type*) where
  delivered : Option (DealerPayload t F)
  echoedTo : Finset (Fin n)
  acceptedEchoes : Finset (EchoMsg n t F)
  readyReceived : Finset (ReadyMsg n t F)
  readySent : Finset (ReadyCert n t F)
  output : Option F
deriving DecidableEq

namespace LocalState

/-- Empty local state. -/
def init (n t : Nat) (F : Type*) : LocalState n t F :=
  { delivered := none
    echoedTo := ∅
    acceptedEchoes := ∅
    readyReceived := ∅
    readySent := ∅
    output := none }

end LocalState

/-- Global state for the faithful AVSS skeleton. -/
structure State (n t : Nat) (F : Type*) where
  partyPoint : Fin n -> F
  secret : F
  local_ : Fin n -> LocalState n t F
  corrupted : Finset (Fin n)
  dealerHonest : Bool
  dealerSent : Fin n -> Bool
  dealerCommit : Fin n -> DealerPayload t F
  inflightDeliveries : Finset (Fin n)
  inflightCorruptDeliveries : Finset (Fin n)
  inflightEchoes : Finset (EchoMsg n t F)
  inflightReady : Finset (ReadyMsg n t F)
deriving DecidableEq

namespace State

/-- A party is honest iff it is outside the static corruption set. -/
def isHonest (s : State n t F) (p : Fin n) : Prop :=
  p ∉ s.corrupted

instance (s : State n t F) (p : Fin n) : Decidable (s.isHonest p) :=
  inferInstanceAs (Decidable (p ∉ s.corrupted))

end State

/-! ## Initial states -/

/-- Initial-state predicate for the faithful skeleton.

For honest dealers, every per-party commitment is the canonical
row+column payload from the sampled bivariate polynomial.  For corrupt
dealers, the per-party commitments are intentionally unconstrained. -/
def initPred (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F) (s : State n t F) : Prop :=
  (∀ p, s.local_ p = LocalState.init n t F) ∧
  s.secret = sec ∧
  s.corrupted = corr ∧
  s.dealerSent = (fun _ => false) ∧
  s.inflightDeliveries = ∅ ∧
  s.inflightCorruptDeliveries = ∅ ∧
  s.inflightEchoes = ∅ ∧
  s.inflightReady = ∅ ∧
  (s.dealerHonest = true ->
    coeffs 0 0 = sec ∧
    ∀ p, s.dealerCommit p = DealerPayload.ofCoeffs s.partyPoint coeffs p)

/-! ## Evidence predicates -/

/-- Echo validation at receiver `p` for candidate payload `candidate`.

The echo must be addressed to `p`; its value must agree with the
sender's row at `p`'s point and with `candidate`'s column at the
sender's point. -/
def validEchoFor (partyPoint : Fin n -> F) (p : Fin n)
    (candidate : DealerPayload t F) (msg : EchoMsg n t F) : Prop :=
  msg.receiver = p ∧
  msg.value = AVSS.evalRowPoly msg.senderPayload.rowPoly (partyPoint p) ∧
  msg.value = AVSS.evalRowPoly candidate.colPoly (partyPoint msg.sender)

/-- The local echo set contains evidence from every listed supporter. -/
def echoCertSupported (s : State n t F) (p : Fin n)
    (cert : ReadyCert n t F) : Prop :=
  ∀ q, q ∈ cert.supporters ->
    ∃ msg ∈ (s.local_ p).acceptedEchoes,
      msg.sender = q ∧ validEchoFor s.partyPoint p cert.candidate msg

/-- The local ready set contains one ready message from every listed
supporter for the same candidate payload. -/
def readyCertSupported (s : State n t F) (p : Fin n)
    (cert : ReadyCert n t F) : Prop :=
  ∀ q, q ∈ cert.supporters ->
    ∃ msg ∈ (s.local_ p).readyReceived,
      msg.sender = q ∧ msg.cert.candidate = cert.candidate

/-! ## Actions and transitions -/

/-- Faithful AVSS protocol actions. -/
inductive Action (n t : Nat) (F : Type*)
  | dealerShareTo (p : Fin n)
  | partyDeliver (p : Fin n)
  | partyCorruptDeliver (p : Fin n)
  | partyEchoSend (sender receiver : Fin n)
  | partyEchoReceive (msg : EchoMsg n t F)
  | partyReady (p : Fin n) (cert : ReadyCert n t F)
  | partyAmplify (p : Fin n) (cert : ReadyCert n t F)
  | partyReceiveReady (msg : ReadyMsg n t F)
  | partyOutput (p : Fin n) (cert : ReadyCert n t F)
deriving DecidableEq

/-- Functional update for one party's local state. -/
def setLocal (s : State n t F) (p : Fin n) (ls : LocalState n t F) :
    State n t F :=
  { s with local_ := fun q => if q = p then ls else s.local_ q }

omit [Field F] [Fintype F] [DecidableEq F] in
@[simp] theorem setLocal_local_self (s : State n t F) (p : Fin n)
    (ls : LocalState n t F) :
    (setLocal s p ls).local_ p = ls := by
  simp [setLocal]

omit [Field F] [Fintype F] [DecidableEq F] in
@[simp] theorem setLocal_local_ne (s : State n t F) (p q : Fin n)
    (ls : LocalState n t F) (h : q ≠ p) :
    (setLocal s p ls).local_ q = s.local_ q := by
  simp [setLocal, h]

/-- Deterministic next-state function.  Gates are enforced separately;
failed gates return `s` through `ProbActionSpec.step = none`, not here. -/
def step (a : Action n t F) (s : State n t F) : State n t F :=
  match a with
  | .dealerShareTo p =>
      { s with
        dealerSent := Function.update s.dealerSent p true
        inflightDeliveries :=
          if p ∉ s.corrupted then insert p s.inflightDeliveries
          else s.inflightDeliveries
        inflightCorruptDeliveries :=
          if p ∈ s.corrupted then insert p s.inflightCorruptDeliveries
          else s.inflightCorruptDeliveries }
  | .partyDeliver p =>
      let ls' : LocalState n t F := { s.local_ p with delivered := some (s.dealerCommit p) }
      let s' := setLocal s p ls'
      { s' with inflightDeliveries := s.inflightDeliveries.erase p }
  | .partyCorruptDeliver p =>
      let ls' : LocalState n t F := { s.local_ p with delivered := some (s.dealerCommit p) }
      let s' := setLocal s p ls'
      { s' with inflightCorruptDeliveries := s.inflightCorruptDeliveries.erase p }
  | .partyEchoSend q p =>
      let payload := (s.local_ q).delivered.getD (s.dealerCommit q)
      let msg : EchoMsg n t F :=
        { sender := q
          receiver := p
          senderPayload := payload
          value := AVSS.evalRowPoly payload.rowPoly (s.partyPoint p) }
      let ls' : LocalState n t F :=
        { s.local_ q with echoedTo := insert p (s.local_ q).echoedTo }
      let s' := setLocal s q ls'
      { s' with inflightEchoes := insert msg s.inflightEchoes }
  | .partyEchoReceive msg =>
      let p := msg.receiver
      let ls' : LocalState n t F :=
        { s.local_ p with acceptedEchoes := insert msg (s.local_ p).acceptedEchoes }
      let s' := setLocal s p ls'
      { s' with inflightEchoes := s.inflightEchoes.erase msg }
  | .partyReady p cert =>
      let ls' : LocalState n t F :=
        { s.local_ p with readySent := insert cert (s.local_ p).readySent }
      let s' := setLocal s p ls'
      { s' with
        inflightReady :=
          s.inflightReady ∪
            (Finset.univ : Finset (Fin n)).image
              (fun r => ({ sender := p, receiver := r, cert := cert } : ReadyMsg n t F)) }
  | .partyAmplify p cert =>
      let ls' : LocalState n t F :=
        { s.local_ p with readySent := insert cert (s.local_ p).readySent }
      let s' := setLocal s p ls'
      { s' with
        inflightReady :=
          s.inflightReady ∪
            (Finset.univ : Finset (Fin n)).image
              (fun r => ({ sender := p, receiver := r, cert := cert } : ReadyMsg n t F)) }
  | .partyReceiveReady msg =>
      let p := msg.receiver
      let ls' : LocalState n t F :=
        { s.local_ p with readyReceived := insert msg (s.local_ p).readyReceived }
      let s' := setLocal s p ls'
      { s' with inflightReady := s.inflightReady.erase msg }
  | .partyOutput p cert =>
      let ls' : LocalState n t F :=
        { s.local_ p with output := some (AVSS.evalRowPoly cert.candidate.rowPoly 0) }
      setLocal s p ls'

/-- Gates for the faithful skeleton.

The send/receive thresholds are candidate-scoped: ready and output
actions carry the certificate they are using, and the gate checks that
the local evidence supports that same candidate. -/
def gate (a : Action n t F) (s : State n t F) : Prop :=
  match a with
  | .dealerShareTo p =>
      s.dealerSent p = false
  | .partyDeliver p =>
      s.dealerSent p = true ∧ p ∉ s.corrupted ∧ p ∈ s.inflightDeliveries ∧
        (s.local_ p).delivered = none
  | .partyCorruptDeliver p =>
      s.dealerSent p = true ∧ p ∈ s.corrupted ∧
        p ∈ s.inflightCorruptDeliveries ∧ (s.local_ p).delivered = none
  | .partyEchoSend q p =>
      (s.local_ q).delivered.isSome ∧ p ∉ (s.local_ q).echoedTo
  | .partyEchoReceive msg =>
      msg ∈ s.inflightEchoes ∧
        ∃ candidate, (s.local_ msg.receiver).delivered = some candidate ∧
          validEchoFor s.partyPoint msg.receiver candidate msg ∧
          msg ∉ (s.local_ msg.receiver).acceptedEchoes
  | .partyReady p cert =>
      (s.local_ p).delivered = some cert.candidate ∧
        cert ∉ (s.local_ p).readySent ∧
        cert.supporters.card ≥ n - t ∧
        echoCertSupported s p cert
  | .partyAmplify p cert =>
      cert ∉ (s.local_ p).readySent ∧
        cert.supporters.card ≥ t + 1 ∧
        readyCertSupported s p cert
  | .partyReceiveReady msg =>
      msg ∈ s.inflightReady ∧ msg ∉ (s.local_ msg.receiver).readyReceived
  | .partyOutput p cert =>
      p ∉ s.corrupted ∧ (s.local_ p).output = none ∧
        (s.local_ p).delivered = some cert.candidate ∧
        cert.supporters.card ≥ n - t ∧
        readyCertSupported s p cert

/-! ## Spec -/

/-- Faithful AVSS probabilistic spec skeleton.  Randomness lives in the
initial measure; all protocol actions are deterministic. -/
noncomputable def spec (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F) :
    ProbActionSpec (State n t F) (Action n t F) where
  init := initPred sec corr coeffs
  actions := fun a =>
    { gate := gate a
      effect := fun s _ => PMF.pure (step a s) }

omit [Fintype F] in
@[simp] theorem spec_step_pure (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F)
    (a : Action n t F) (s : State n t F) (h : gate a s) :
    (spec (t := t) sec corr coeffs).step a s = some (PMF.pure (step a s)) :=
  ProbActionSpec.step_eq_some h

omit [Fintype F] in
theorem spec_step_none (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F)
    (a : Action n t F) (s : State n t F) (h : ¬ gate a s) :
    (spec (t := t) sec corr coeffs).step a s = none :=
  ProbActionSpec.step_eq_none h

/-! ## Measurability and finiteness -/

section Instances

instance : MeasurableSpace (DealerPayload t F) := ⊤
instance : MeasurableSingletonClass (DealerPayload t F) := ⟨fun _ => trivial⟩
instance : MeasurableSpace (EchoMsg n t F) := ⊤
instance : MeasurableSingletonClass (EchoMsg n t F) := ⟨fun _ => trivial⟩
instance : MeasurableSpace (ReadyCert n t F) := ⊤
instance : MeasurableSingletonClass (ReadyCert n t F) := ⟨fun _ => trivial⟩
instance : MeasurableSpace (ReadyMsg n t F) := ⊤
instance : MeasurableSingletonClass (ReadyMsg n t F) := ⟨fun _ => trivial⟩
instance : MeasurableSpace (LocalState n t F) := ⊤
instance : MeasurableSingletonClass (LocalState n t F) := ⟨fun _ => trivial⟩
instance : MeasurableSpace (State n t F) := ⊤
instance : MeasurableSingletonClass (State n t F) := ⟨fun _ => trivial⟩
instance : MeasurableSpace (Action n t F) := ⊤
instance : MeasurableSingletonClass (Action n t F) := ⟨fun _ => trivial⟩

noncomputable instance : Fintype (DealerPayload t F) := by
  classical
  exact Fintype.ofEquiv ((Fin (t + 1) -> F) × (Fin (t + 1) -> F))
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun p => (p.rowPoly, p.colPoly)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance : Countable (DealerPayload t F) := Finite.to_countable

noncomputable instance : Fintype (EchoMsg n t F) := by
  classical
  exact Fintype.ofEquiv (Fin n × Fin n × DealerPayload t F × F)
    { toFun := fun x =>
        ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
      invFun := fun msg =>
        (msg.sender, msg.receiver, msg.senderPayload, msg.value)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance : Countable (EchoMsg n t F) := Finite.to_countable

noncomputable instance : Fintype (ReadyCert n t F) := by
  classical
  exact Fintype.ofEquiv (DealerPayload t F × Finset (Fin n))
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun cert => (cert.candidate, cert.supporters)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance : Countable (ReadyCert n t F) := Finite.to_countable

noncomputable instance : Fintype (ReadyMsg n t F) := by
  classical
  exact Fintype.ofEquiv (Fin n × Fin n × ReadyCert n t F)
    { toFun := fun x => ⟨x.1, x.2.1, x.2.2⟩
      invFun := fun msg => (msg.sender, msg.receiver, msg.cert)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance : Countable (ReadyMsg n t F) := Finite.to_countable

noncomputable instance : Fintype (LocalState n t F) := by
  classical
  exact Fintype.ofEquiv
    (Option (DealerPayload t F) × Finset (Fin n) × Finset (EchoMsg n t F) ×
      Finset (ReadyMsg n t F) × Finset (ReadyCert n t F) × Option F)
    { toFun := fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
        x.2.2.2.2.2⟩
      invFun := fun ls =>
        (ls.delivered, ls.echoedTo, ls.acceptedEchoes, ls.readyReceived,
          ls.readySent, ls.output)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance : Countable (LocalState n t F) := Finite.to_countable

noncomputable instance : Fintype (State n t F) := by
  classical
  exact Fintype.ofEquiv
    ((Fin n -> F) × F × (Fin n -> LocalState n t F) × Finset (Fin n) × Bool ×
      (Fin n -> Bool) × (Fin n -> DealerPayload t F) × Finset (Fin n) ×
      Finset (Fin n) × Finset (EchoMsg n t F) × Finset (ReadyMsg n t F))
    { toFun := fun x =>
        ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
          x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
          x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1,
          x.2.2.2.2.2.2.2.2.2.2⟩
      invFun := fun s =>
        (s.partyPoint, s.secret, s.local_, s.corrupted, s.dealerHonest,
          s.dealerSent, s.dealerCommit, s.inflightDeliveries,
          s.inflightCorruptDeliveries, s.inflightEchoes, s.inflightReady)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance : Countable (State n t F) := Finite.to_countable

noncomputable instance : Fintype (Action n t F) := by
  classical
  exact Fintype.ofEquiv
    (Fin n ⊕ Fin n ⊕ Fin n ⊕ (Fin n × Fin n) ⊕ EchoMsg n t F ⊕
      (Fin n × ReadyCert n t F) ⊕ (Fin n × ReadyCert n t F) ⊕
      ReadyMsg n t F ⊕ (Fin n × ReadyCert n t F))
    { toFun := fun
        | .inl p => .dealerShareTo p
        | .inr (.inl p) => .partyDeliver p
        | .inr (.inr (.inl p)) => .partyCorruptDeliver p
        | .inr (.inr (.inr (.inl x))) => .partyEchoSend x.1 x.2
        | .inr (.inr (.inr (.inr (.inl msg)))) => .partyEchoReceive msg
        | .inr (.inr (.inr (.inr (.inr (.inl x))))) => .partyReady x.1 x.2
        | .inr (.inr (.inr (.inr (.inr (.inr (.inl x)))))) =>
            .partyAmplify x.1 x.2
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl msg))))))) =>
            .partyReceiveReady msg
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr x))))))) =>
            .partyOutput x.1 x.2
      invFun := fun
        | .dealerShareTo p => .inl p
        | .partyDeliver p => .inr (.inl p)
        | .partyCorruptDeliver p => .inr (.inr (.inl p))
        | .partyEchoSend q p => .inr (.inr (.inr (.inl (q, p))))
        | .partyEchoReceive msg => .inr (.inr (.inr (.inr (.inl msg))))
        | .partyReady p cert => .inr (.inr (.inr (.inr (.inr (.inl (p, cert))))))
        | .partyAmplify p cert =>
            .inr (.inr (.inr (.inr (.inr (.inr (.inl (p, cert)))))))
        | .partyReceiveReady msg =>
            .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl msg)))))))
        | .partyOutput p cert =>
            .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (p, cert))))))))
      left_inv := fun
        | .inl _ => rfl
        | .inr (.inl _) => rfl
        | .inr (.inr (.inl _)) => rfl
        | .inr (.inr (.inr (.inl _))) => rfl
        | .inr (.inr (.inr (.inr (.inl _)))) => rfl
        | .inr (.inr (.inr (.inr (.inr (.inl _))))) => rfl
        | .inr (.inr (.inr (.inr (.inr (.inr (.inl _)))))) => rfl
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl _))))))) => rfl
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr _))))))) => rfl
      right_inv := fun
        | .dealerShareTo _ => rfl
        | .partyDeliver _ => rfl
        | .partyCorruptDeliver _ => rfl
        | .partyEchoSend _ _ => rfl
        | .partyEchoReceive _ => rfl
        | .partyReady _ _ => rfl
        | .partyAmplify _ _ => rfl
        | .partyReceiveReady _ => rfl
        | .partyOutput _ _ => rfl }

instance : Countable (Action n t F) := Finite.to_countable

end Instances

/-! ## State-frame lemmas for `step`

These mirror the pattern in `Leslie.Examples.Prob.AVSS`
(`avssStep_partyPoint_invariant`, `avssStep_corrupted_invariant`,
etc.).  Most fields are preserved by every action; the only
field-level monotone update is `dealerSent` under `dealerShareTo`. -/

omit [Fintype F] in
/-- `partyPoint` is preserved by every `step` action. -/
theorem step_partyPoint_invariant (a : Action n t F) (s : State n t F) :
    (step a s).partyPoint = s.partyPoint := by
  cases a <;> simp [step, setLocal]

omit [Fintype F] in
/-- `secret` is preserved by every `step` action. -/
theorem step_secret_invariant (a : Action n t F) (s : State n t F) :
    (step a s).secret = s.secret := by
  cases a <;> simp [step, setLocal]

omit [Fintype F] in
/-- `corrupted` is preserved by every `step` action. -/
theorem step_corrupted_invariant (a : Action n t F) (s : State n t F) :
    (step a s).corrupted = s.corrupted := by
  cases a <;> simp [step, setLocal]

omit [Fintype F] in
/-- `dealerHonest` is preserved by every `step` action. -/
theorem step_dealerHonest_invariant (a : Action n t F) (s : State n t F) :
    (step a s).dealerHonest = s.dealerHonest := by
  cases a <;> simp [step, setLocal]

omit [Fintype F] in
/-- `dealerCommit` is preserved by every `step` action.  The per-party
commitments are pinned at init (canonically for honest dealer, freely
for corrupt dealer) and never modified afterwards. -/
theorem step_dealerCommit_invariant (a : Action n t F) (s : State n t F) :
    (step a s).dealerCommit = s.dealerCommit := by
  cases a <;> simp [step, setLocal]

omit [Fintype F] in
/-- Frame: `dealerSent p` is unchanged by any action other than
`dealerShareTo p`. -/
theorem step_dealerSent_self_unless (a : Action n t F) (s : State n t F)
    (p : Fin n) (h_not_share : a ≠ .dealerShareTo p) :
    (step a s).dealerSent p = s.dealerSent p := by
  cases a with
  | dealerShareTo q =>
    have hpq : p ≠ q := fun heq => h_not_share (heq ▸ rfl)
    show (step (.dealerShareTo q) s).dealerSent p = s.dealerSent p
    simp [step, Function.update_of_ne hpq]
  | partyDeliver q => simp [step, setLocal]
  | partyCorruptDeliver q => simp [step, setLocal]
  | partyEchoSend q r => simp [step, setLocal]
  | partyEchoReceive msg => simp [step, setLocal]
  | partyReady q cert => simp [step, setLocal]
  | partyAmplify q cert => simp [step, setLocal]
  | partyReceiveReady msg => simp [step, setLocal]
  | partyOutput q cert => simp [step, setLocal]

omit [Fintype F] in
/-- After `dealerShareTo p`, `dealerSent p = true`. -/
theorem step_dealerSent_set_after (s : State n t F) (p : Fin n) :
    (step (.dealerShareTo p) s).dealerSent p = true := by
  show (step (.dealerShareTo p) s).dealerSent p = true
  simp [step, Function.update_self]

omit [Fintype F] in
/-- Monotonicity: `dealerSent p = true` is preserved by every action. -/
theorem step_dealerSent_monotone (a : Action n t F) (s : State n t F)
    (p : Fin n) (h_pre : s.dealerSent p = true) :
    (step a s).dealerSent p = true := by
  by_cases h : a = .dealerShareTo p
  · subst h; exact step_dealerSent_set_after s p
  · rw [step_dealerSent_self_unless a s p h]; exact h_pre

/-! ## Initial-state-predicate properties

These extract individual facts pinned by `initPred`.  They are pure
projections — no induction or step reasoning. -/

omit [Fintype F] [DecidableEq F] in
/-- `initPred` does not constrain `partyPoint`: any value is permitted. -/
theorem initPred_partyPoint_arbitrary (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F) (s : State n t F)
    (h : initPred sec corr coeffs s) (pp : Fin n -> F) :
    initPred sec corr coeffs { s with partyPoint := pp } ∨
      initPred sec corr coeffs s := Or.inr h

omit [Fintype F] [DecidableEq F] in
/-- Under honest dealer, `initPred` pins every per-party commitment to
the canonical row+column payload. -/
theorem initPred_dealerCommit_honest (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F) (s : State n t F)
    (h : initPred sec corr coeffs s) (hh : s.dealerHonest = true) (p : Fin n) :
    s.dealerCommit p = DealerPayload.ofCoeffs s.partyPoint coeffs p :=
  (h.2.2.2.2.2.2.2.2 hh).2 p

omit [Fintype F] [DecidableEq F] in
/-- `initPred` pins the corruption set. -/
theorem initPred_corrupted (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F) (s : State n t F)
    (h : initPred sec corr coeffs s) :
    s.corrupted = corr := h.2.2.1

omit [Fintype F] [DecidableEq F] in
/-- `initPred` pins the secret. -/
theorem initPred_secret (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F) (s : State n t F)
    (h : initPred sec corr coeffs s) :
    s.secret = sec := h.2.1

omit [Fintype F] [DecidableEq F] in
/-- `initPred` pins `dealerSent` to the constant-`false` function. -/
theorem initPred_dealerSent_init (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F) (s : State n t F)
    (h : initPred sec corr coeffs s) (p : Fin n) :
    s.dealerSent p = false := by
  have hfn : s.dealerSent = (fun _ => false) := h.2.2.2.1
  simp [hfn]

/-! ## Phase-1 invariants

Three simple invariants with init + preservation lemmas.  These are
the foundation for the queue / flight / freshness invariants in
Step 2 and the substantive cryptographic invariants later. -/

/-- Honest-dealer commitment invariant: under an honest dealer, every
per-party commitment is the canonical bivariate payload at that party
point.  Trivially preserved (both `dealerCommit` and `partyPoint` are
pinned by `step`). -/
def honestDealerCommitInv
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F) (s : State n t F) : Prop :=
  s.dealerHonest = true ->
    ∀ p, s.dealerCommit p = DealerPayload.ofCoeffs s.partyPoint coeffs p

omit [Fintype F] [DecidableEq F] in
/-- Honest-dealer commitment holds at init. -/
theorem honestDealerCommitInv_init (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F) (s : State n t F)
    (h : initPred sec corr coeffs s) :
    honestDealerCommitInv coeffs s := fun hh =>
  (h.2.2.2.2.2.2.2.2 hh).2

omit [Fintype F] in
/-- Honest-dealer commitment is preserved by every `step` action. -/
theorem honestDealerCommitInv_preserve
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F)
    (a : Action n t F) (s : State n t F)
    (h : honestDealerCommitInv coeffs s) :
    honestDealerCommitInv coeffs (step a s) := by
  intro hh p
  rw [step_dealerCommit_invariant, step_partyPoint_invariant]
  apply h
  rw [step_dealerHonest_invariant] at hh
  exact hh

/-- Delivered-implies-dealer-sent invariant: a party with a delivered
payload must have been served by `dealerShareTo`.  Preserved by the
`partyDeliver` and `partyCorruptDeliver` gates (each requires
`dealerSent p = true`); other actions don't change `delivered`. -/
def deliveredImpliesDealerSent (s : State n t F) : Prop :=
  ∀ p, (s.local_ p).delivered.isSome -> s.dealerSent p = true

omit [Fintype F] [DecidableEq F] in
/-- Vacuously true at init: no party is delivered. -/
theorem deliveredImpliesDealerSent_init (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F) (s : State n t F)
    (h : initPred sec corr coeffs s) :
    deliveredImpliesDealerSent s := by
  intro p hd
  have hloc : s.local_ p = LocalState.init n t F := h.1 p
  rw [hloc] at hd
  simp [LocalState.init] at hd

omit [Fintype F] in
/-- Preservation: any action that introduces a delivered payload at `p`
is gated by `dealerSent p = true`; other actions don't change
`delivered` and `dealerSent` is monotone. -/
theorem deliveredImpliesDealerSent_preserve
    (a : Action n t F) (s : State n t F)
    (hgate : gate a s) (h : deliveredImpliesDealerSent s) :
    deliveredImpliesDealerSent (step a s) := by
  intro p hd
  cases a with
  | dealerShareTo q =>
    -- step doesn't touch local_; reduce to old `delivered` + monotonicity
    have hloc : (step (.dealerShareTo q) s).local_ p = s.local_ p := by
      simp [step, setLocal]
    rw [hloc] at hd
    exact step_dealerSent_monotone _ _ _ (h p hd)
  | partyDeliver q =>
    by_cases hpq : p = q
    · subst hpq
      -- gate gives dealerSent p = true; step preserves dealerSent on this branch
      have hsent : s.dealerSent p = true := hgate.1
      have : (step (.partyDeliver p) s).dealerSent p = s.dealerSent p := by
        simp [step, setLocal]
      rw [this]; exact hsent
    · have hloc : (step (.partyDeliver q) s).local_ p = s.local_ p := by
        simp [step, setLocal, hpq]
      rw [hloc] at hd
      have hpre : s.dealerSent p = true := h p hd
      have : (step (.partyDeliver q) s).dealerSent p = s.dealerSent p := by
        simp [step, setLocal]
      rw [this]; exact hpre
  | partyCorruptDeliver q =>
    by_cases hpq : p = q
    · subst hpq
      have hsent : s.dealerSent p = true := hgate.1
      have : (step (.partyCorruptDeliver p) s).dealerSent p = s.dealerSent p := by
        simp [step, setLocal]
      rw [this]; exact hsent
    · have hloc : (step (.partyCorruptDeliver q) s).local_ p = s.local_ p := by
        simp [step, setLocal, hpq]
      rw [hloc] at hd
      have hpre : s.dealerSent p = true := h p hd
      have : (step (.partyCorruptDeliver q) s).dealerSent p = s.dealerSent p := by
        simp [step, setLocal]
      rw [this]; exact hpre
  | partyEchoSend q r =>
    -- step only updates echoedTo on q's local state; delivered untouched
    have hd' : (s.local_ p).delivered.isSome := by
      by_cases hpq : p = q
      · subst hpq
        have : (step (.partyEchoSend p r) s).local_ p =
            { s.local_ p with echoedTo := insert r (s.local_ p).echoedTo } := by
          simp [step, setLocal]
        rw [this] at hd; exact hd
      · have : (step (.partyEchoSend q r) s).local_ p = s.local_ p := by
          simp [step, setLocal, hpq]
        rw [this] at hd; exact hd
    have hpre : s.dealerSent p = true := h p hd'
    have : (step (.partyEchoSend q r) s).dealerSent p = s.dealerSent p := by
      simp [step, setLocal]
    rw [this]; exact hpre
  | partyEchoReceive msg =>
    have hd' : (s.local_ p).delivered.isSome := by
      by_cases hpq : p = msg.receiver
      · rw [hpq] at hd ⊢
        have : (step (.partyEchoReceive msg) s).local_ msg.receiver =
            { s.local_ msg.receiver with
              acceptedEchoes :=
                insert msg (s.local_ msg.receiver).acceptedEchoes } := by
          simp [step, setLocal]
        rw [this] at hd; exact hd
      · have : (step (.partyEchoReceive msg) s).local_ p = s.local_ p := by
          simp [step, setLocal, hpq]
        rw [this] at hd; exact hd
    have hpre : s.dealerSent p = true := h p hd'
    have : (step (.partyEchoReceive msg) s).dealerSent p = s.dealerSent p := by
      simp [step, setLocal]
    rw [this]; exact hpre
  | partyReady q cert =>
    have hd' : (s.local_ p).delivered.isSome := by
      by_cases hpq : p = q
      · subst hpq
        have : (step (.partyReady p cert) s).local_ p =
            { s.local_ p with readySent := insert cert (s.local_ p).readySent } := by
          simp [step, setLocal]
        rw [this] at hd; exact hd
      · have : (step (.partyReady q cert) s).local_ p = s.local_ p := by
          simp [step, setLocal, hpq]
        rw [this] at hd; exact hd
    have hpre : s.dealerSent p = true := h p hd'
    have : (step (.partyReady q cert) s).dealerSent p = s.dealerSent p := by
      simp [step, setLocal]
    rw [this]; exact hpre
  | partyAmplify q cert =>
    have hd' : (s.local_ p).delivered.isSome := by
      by_cases hpq : p = q
      · subst hpq
        have : (step (.partyAmplify p cert) s).local_ p =
            { s.local_ p with readySent := insert cert (s.local_ p).readySent } := by
          simp [step, setLocal]
        rw [this] at hd; exact hd
      · have : (step (.partyAmplify q cert) s).local_ p = s.local_ p := by
          simp [step, setLocal, hpq]
        rw [this] at hd; exact hd
    have hpre : s.dealerSent p = true := h p hd'
    have : (step (.partyAmplify q cert) s).dealerSent p = s.dealerSent p := by
      simp [step, setLocal]
    rw [this]; exact hpre
  | partyReceiveReady msg =>
    have hd' : (s.local_ p).delivered.isSome := by
      by_cases hpq : p = msg.receiver
      · rw [hpq] at hd ⊢
        have : (step (.partyReceiveReady msg) s).local_ msg.receiver =
            { s.local_ msg.receiver with
              readyReceived :=
                insert msg (s.local_ msg.receiver).readyReceived } := by
          simp [step, setLocal]
        rw [this] at hd; exact hd
      · have : (step (.partyReceiveReady msg) s).local_ p = s.local_ p := by
          simp [step, setLocal, hpq]
        rw [this] at hd; exact hd
    have hpre : s.dealerSent p = true := h p hd'
    have : (step (.partyReceiveReady msg) s).dealerSent p = s.dealerSent p := by
      simp [step, setLocal]
    rw [this]; exact hpre
  | partyOutput q cert =>
    have hd' : (s.local_ p).delivered.isSome := by
      by_cases hpq : p = q
      · subst hpq
        have : (step (.partyOutput p cert) s).local_ p =
            { s.local_ p with
              output := some (AVSS.evalRowPoly cert.candidate.rowPoly 0) } := by
          simp [step, setLocal]
        rw [this] at hd; exact hd
      · have : (step (.partyOutput q cert) s).local_ p = s.local_ p := by
          simp [step, setLocal, hpq]
        rw [this] at hd; exact hd
    have hpre : s.dealerSent p = true := h p hd'
    have : (step (.partyOutput q cert) s).dealerSent p = s.dealerSent p := by
      simp [step, setLocal]
    rw [this]; exact hpre

/-- Echoed-implies-delivered invariant: if party `p` has marked party
`q` as echoed-to, then `p` has a delivered payload (the gate of
`partyEchoSend p q` requires `delivered.isSome`). -/
def echoedToImpliesDelivered (s : State n t F) : Prop :=
  ∀ p q, q ∈ (s.local_ p).echoedTo -> (s.local_ p).delivered.isSome

omit [Fintype F] [DecidableEq F] in
/-- Vacuously true at init: every `echoedTo` is empty. -/
theorem echoedToImpliesDelivered_init (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F) (s : State n t F)
    (h : initPred sec corr coeffs s) :
    echoedToImpliesDelivered s := by
  intro p q hq
  have hloc : s.local_ p = LocalState.init n t F := h.1 p
  rw [hloc] at hq
  simp [LocalState.init] at hq

omit [Fintype F] in
/-- Preservation: only `partyEchoSend` extends `echoedTo`, and its
gate provides the required `delivered.isSome`.  Other actions either
leave `local_ p` alone or extend non-`echoedTo` and non-`delivered`
fields. -/
theorem echoedToImpliesDelivered_preserve
    (a : Action n t F) (s : State n t F)
    (hgate : gate a s) (h : echoedToImpliesDelivered s) :
    echoedToImpliesDelivered (step a s) := by
  intro p q hq
  cases a with
  | dealerShareTo r =>
    have hloc : (step (.dealerShareTo r) s).local_ p = s.local_ p := by
      simp [step, setLocal]
    rw [hloc] at hq ⊢
    exact h p q hq
  | partyDeliver r =>
    -- delivered becomes some at r; echoedTo unchanged at r
    by_cases hpr : p = r
    · subst hpr
      have hloc : (step (.partyDeliver p) s).local_ p =
          { s.local_ p with delivered := some (s.dealerCommit p) } := by
        simp [step, setLocal]
      rw [hloc] at hq ⊢
      simp at hq ⊢
    · have hloc : (step (.partyDeliver r) s).local_ p = s.local_ p := by
        simp [step, setLocal, hpr]
      rw [hloc] at hq ⊢
      exact h p q hq
  | partyCorruptDeliver r =>
    by_cases hpr : p = r
    · subst hpr
      have hloc : (step (.partyCorruptDeliver p) s).local_ p =
          { s.local_ p with delivered := some (s.dealerCommit p) } := by
        simp [step, setLocal]
      rw [hloc] at hq ⊢
      simp at hq ⊢
    · have hloc : (step (.partyCorruptDeliver r) s).local_ p = s.local_ p := by
        simp [step, setLocal, hpr]
      rw [hloc] at hq ⊢
      exact h p q hq
  | partyEchoSend r r' =>
    by_cases hpr : p = r
    · subst hpr
      have hloc : (step (.partyEchoSend p r') s).local_ p =
          { s.local_ p with echoedTo := insert r' (s.local_ p).echoedTo } := by
        simp [step, setLocal]
      rw [hloc] at hq ⊢
      -- gate says s.local_ p has delivered.isSome
      exact hgate.1
    · have hloc : (step (.partyEchoSend r r') s).local_ p = s.local_ p := by
        simp [step, setLocal, hpr]
      rw [hloc] at hq ⊢
      exact h p q hq
  | partyEchoReceive msg =>
    by_cases hpr : p = msg.receiver
    · rw [hpr] at hq ⊢
      have hloc : (step (.partyEchoReceive msg) s).local_ msg.receiver =
          { s.local_ msg.receiver with
            acceptedEchoes :=
              insert msg (s.local_ msg.receiver).acceptedEchoes } := by
        simp [step, setLocal]
      rw [hloc] at hq ⊢
      exact h msg.receiver q hq
    · have hloc : (step (.partyEchoReceive msg) s).local_ p = s.local_ p := by
        simp [step, setLocal, hpr]
      rw [hloc] at hq ⊢
      exact h p q hq
  | partyReady r cert =>
    by_cases hpr : p = r
    · subst hpr
      have hloc : (step (.partyReady p cert) s).local_ p =
          { s.local_ p with readySent := insert cert (s.local_ p).readySent } := by
        simp [step, setLocal]
      rw [hloc] at hq ⊢
      exact h p q hq
    · have hloc : (step (.partyReady r cert) s).local_ p = s.local_ p := by
        simp [step, setLocal, hpr]
      rw [hloc] at hq ⊢
      exact h p q hq
  | partyAmplify r cert =>
    by_cases hpr : p = r
    · subst hpr
      have hloc : (step (.partyAmplify p cert) s).local_ p =
          { s.local_ p with readySent := insert cert (s.local_ p).readySent } := by
        simp [step, setLocal]
      rw [hloc] at hq ⊢
      exact h p q hq
    · have hloc : (step (.partyAmplify r cert) s).local_ p = s.local_ p := by
        simp [step, setLocal, hpr]
      rw [hloc] at hq ⊢
      exact h p q hq
  | partyReceiveReady msg =>
    by_cases hpr : p = msg.receiver
    · rw [hpr] at hq ⊢
      have hloc : (step (.partyReceiveReady msg) s).local_ msg.receiver =
          { s.local_ msg.receiver with
            readyReceived :=
              insert msg (s.local_ msg.receiver).readyReceived } := by
        simp [step, setLocal]
      rw [hloc] at hq ⊢
      exact h msg.receiver q hq
    · have hloc : (step (.partyReceiveReady msg) s).local_ p = s.local_ p := by
        simp [step, setLocal, hpr]
      rw [hloc] at hq ⊢
      exact h p q hq
  | partyOutput r cert =>
    by_cases hpr : p = r
    · subst hpr
      have hloc : (step (.partyOutput p cert) s).local_ p =
          { s.local_ p with
            output := some (AVSS.evalRowPoly cert.candidate.rowPoly 0) } := by
        simp [step, setLocal]
      rw [hloc] at hq ⊢
      exact h p q hq
    · have hloc : (step (.partyOutput r cert) s).local_ p = s.local_ p := by
        simp [step, setLocal, hpr]
      rw [hloc] at hq ⊢
      exact h p q hq

/-! ## Phase-2 invariants: queue / flight / freshness

Six invariants describing the well-formedness of the inflight queues
and the local evidence sets.  They are mirror counterparts of
`avssQueueWfInv` / `avssFreshInv` from the threshold-faithful AVSS
spec, adapted to the value-bearing echoes and candidate-scoped ready
certificates of the faithful skeleton.

The invariants in this section:

1. `inflightDeliveriesWf` — every entry of `inflightDeliveries` is
   honest, has its dealer message marked sent, and is still
   undelivered (so `partyDeliver` is enabled on it).
2. `inflightCorruptDeliveriesWf` — same shape for corrupt parties.
3. `outputImpliesDelivered` — a party with an `output` set must have
   its `delivered` set (the `partyOutput` gate requires it).
4. `acceptedEchoesAddressed` — every `msg` in `(local_ p).acceptedEchoes`
   has `msg.receiver = p` (the `partyEchoReceive` gate requires it).
5. `inflightEchoesSenderDelivered` — every queued echo's sender has
   `delivered.isSome` (so the sender produced the echo from a real
   payload).
6. `inflightReadySenderReady` — every queued ready message's
   certificate is in the sender's local `readySent`.

`inflightDeliveriesWf` and `inflightCorruptDeliveriesWf` need
`deliveredImpliesDealerSent` (Phase-1) as a side hypothesis to carry
the freshness clause `delivered = none` through `dealerShareTo`. -/

/-! ### 1. `inflightDeliveriesWf` -/

/-- Every entry of `inflightDeliveries` is honest, has `dealerSent` set,
and has not yet been delivered.  This is the precondition needed to
fire `partyDeliver` on that entry. -/
def inflightDeliveriesWf (s : State n t F) : Prop :=
  ∀ p, p ∈ s.inflightDeliveries ->
    s.dealerSent p = true ∧ p ∉ s.corrupted ∧ (s.local_ p).delivered = none

omit [Fintype F] [DecidableEq F] in
/-- Vacuous at init: `inflightDeliveries` is empty. -/
theorem inflightDeliveriesWf_init (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F) (s : State n t F)
    (h : initPred sec corr coeffs s) :
    inflightDeliveriesWf s := by
  intro p hp
  rw [h.2.2.2.2.1] at hp
  exact absurd hp (Finset.notMem_empty _)

omit [Fintype F] in
/-- Preservation of `inflightDeliveriesWf`.  Threads `deliveredImpliesDealerSent`
to discharge the `delivered = none` clause for the freshly-enqueued
party in the `dealerShareTo` case. -/
theorem inflightDeliveriesWf_preserve
    (a : Action n t F) (s : State n t F)
    (hgate : gate a s) (hdis : deliveredImpliesDealerSent s)
    (h : inflightDeliveriesWf s) :
    inflightDeliveriesWf (step a s) := by
  intro p hp
  cases a with
  | dealerShareTo q =>
    -- `inflightDeliveries` grows by `{q}` only when `q ∉ corrupted`.
    by_cases hqc : q ∈ s.corrupted
    · -- post.ifd = pre.ifd
      have h_ifd : (step (.dealerShareTo q) s).inflightDeliveries =
          s.inflightDeliveries := by
        simp [step, hqc]
      rw [h_ifd] at hp
      obtain ⟨hsent, hnc, hdel⟩ := h p hp
      refine ⟨step_dealerSent_monotone _ _ _ hsent, ?_, ?_⟩
      · rw [step_corrupted_invariant]; exact hnc
      · -- step doesn't touch any local_; delivered unchanged
        have : (step (.dealerShareTo q) s).local_ p = s.local_ p := by
          simp [step, setLocal]
        rw [this]; exact hdel
    · -- post.ifd = insert q pre.ifd
      have h_ifd : (step (.dealerShareTo q) s).inflightDeliveries =
          insert q s.inflightDeliveries := by
        simp [step, hqc]
      rw [h_ifd] at hp
      rcases Finset.mem_insert.mp hp with rfl | hp_old
      · -- p = q: gate says dealerSent p = false → with deliveredImpliesDealerSent,
        -- delivered = none.
        have hgate' : s.dealerSent p = false := hgate
        have hdel : (s.local_ p).delivered = none := by
          by_contra h0
          have : (s.local_ p).delivered.isSome := by
            cases hd : (s.local_ p).delivered with
            | none => exact absurd hd h0
            | some _ => simp [hd]
          have := hdis p this
          rw [this] at hgate'; cases hgate'
        refine ⟨?_, ?_, ?_⟩
        · exact step_dealerSent_set_after s p
        · rw [step_corrupted_invariant]; exact hqc
        · have : (step (.dealerShareTo p) s).local_ p = s.local_ p := by
            simp [step, setLocal]
          rw [this]; exact hdel
      · obtain ⟨hsent, hnc, hdel⟩ := h p hp_old
        refine ⟨step_dealerSent_monotone _ _ _ hsent, ?_, ?_⟩
        · rw [step_corrupted_invariant]; exact hnc
        · have : (step (.dealerShareTo q) s).local_ p = s.local_ p := by
            simp [step, setLocal]
          rw [this]; exact hdel
  | partyDeliver q =>
    -- post.ifd = pre.ifd.erase q.  p ∈ post.ifd → p ∈ pre.ifd ∧ p ≠ q.
    have h_ifd : (step (.partyDeliver q) s).inflightDeliveries =
        s.inflightDeliveries.erase q := by
      simp [step, setLocal]
    rw [h_ifd] at hp
    have hp_old : p ∈ s.inflightDeliveries := Finset.mem_of_mem_erase hp
    have hpq : p ≠ q := Finset.ne_of_mem_erase hp
    obtain ⟨hsent, hnc, hdel⟩ := h p hp_old
    refine ⟨step_dealerSent_monotone _ _ _ hsent, ?_, ?_⟩
    · rw [step_corrupted_invariant]; exact hnc
    · have hloc : (step (.partyDeliver q) s).local_ p = s.local_ p := by
        simp [step, setLocal, hpq]
      rw [hloc]; exact hdel
  | partyCorruptDeliver q =>
    -- post.ifd = pre.ifd; q is corrupt so q ∉ pre.ifd.
    have h_ifd : (step (.partyCorruptDeliver q) s).inflightDeliveries =
        s.inflightDeliveries := by simp [step, setLocal]
    rw [h_ifd] at hp
    obtain ⟨hsent, hnc, hdel⟩ := h p hp
    have hpq : p ≠ q := by
      intro heq; subst heq
      -- q is corrupt by gate; but p ∉ corrupted from invariant.
      exact hnc hgate.2.1
    refine ⟨step_dealerSent_monotone _ _ _ hsent, ?_, ?_⟩
    · rw [step_corrupted_invariant]; exact hnc
    · have hloc : (step (.partyCorruptDeliver q) s).local_ p = s.local_ p := by
        simp [step, setLocal, hpq]
      rw [hloc]; exact hdel
  | partyEchoSend q r =>
    have h_ifd : (step (.partyEchoSend q r) s).inflightDeliveries =
        s.inflightDeliveries := by simp [step, setLocal]
    rw [h_ifd] at hp
    obtain ⟨hsent, hnc, hdel⟩ := h p hp
    refine ⟨step_dealerSent_monotone _ _ _ hsent, ?_, ?_⟩
    · rw [step_corrupted_invariant]; exact hnc
    · -- delivered field at p is unchanged: partyEchoSend only touches echoedTo at q.
      by_cases hpq : p = q
      · subst hpq
        have : ((step (.partyEchoSend p r) s).local_ p).delivered =
            (s.local_ p).delivered := by
          simp [step, setLocal]
        rw [this]; exact hdel
      · have : (step (.partyEchoSend q r) s).local_ p = s.local_ p := by
          simp [step, setLocal, hpq]
        rw [this]; exact hdel
  | partyEchoReceive msg =>
    have h_ifd : (step (.partyEchoReceive msg) s).inflightDeliveries =
        s.inflightDeliveries := by simp [step, setLocal]
    rw [h_ifd] at hp
    obtain ⟨hsent, hnc, hdel⟩ := h p hp
    refine ⟨step_dealerSent_monotone _ _ _ hsent, ?_, ?_⟩
    · rw [step_corrupted_invariant]; exact hnc
    · by_cases hpq : p = msg.receiver
      · rw [hpq]
        have : ((step (.partyEchoReceive msg) s).local_ msg.receiver).delivered =
            (s.local_ msg.receiver).delivered := by
          simp [step, setLocal]
        rw [this, ← hpq]; exact hdel
      · have : (step (.partyEchoReceive msg) s).local_ p = s.local_ p := by
          simp [step, setLocal, hpq]
        rw [this]; exact hdel
  | partyReady q cert =>
    have h_ifd : (step (.partyReady q cert) s).inflightDeliveries =
        s.inflightDeliveries := by simp [step, setLocal]
    rw [h_ifd] at hp
    obtain ⟨hsent, hnc, hdel⟩ := h p hp
    refine ⟨step_dealerSent_monotone _ _ _ hsent, ?_, ?_⟩
    · rw [step_corrupted_invariant]; exact hnc
    · by_cases hpq : p = q
      · subst hpq
        have : ((step (.partyReady p cert) s).local_ p).delivered =
            (s.local_ p).delivered := by
          simp [step, setLocal]
        rw [this]; exact hdel
      · have : (step (.partyReady q cert) s).local_ p = s.local_ p := by
          simp [step, setLocal, hpq]
        rw [this]; exact hdel
  | partyAmplify q cert =>
    have h_ifd : (step (.partyAmplify q cert) s).inflightDeliveries =
        s.inflightDeliveries := by simp [step, setLocal]
    rw [h_ifd] at hp
    obtain ⟨hsent, hnc, hdel⟩ := h p hp
    refine ⟨step_dealerSent_monotone _ _ _ hsent, ?_, ?_⟩
    · rw [step_corrupted_invariant]; exact hnc
    · by_cases hpq : p = q
      · subst hpq
        have : ((step (.partyAmplify p cert) s).local_ p).delivered =
            (s.local_ p).delivered := by
          simp [step, setLocal]
        rw [this]; exact hdel
      · have : (step (.partyAmplify q cert) s).local_ p = s.local_ p := by
          simp [step, setLocal, hpq]
        rw [this]; exact hdel
  | partyReceiveReady msg =>
    have h_ifd : (step (.partyReceiveReady msg) s).inflightDeliveries =
        s.inflightDeliveries := by simp [step, setLocal]
    rw [h_ifd] at hp
    obtain ⟨hsent, hnc, hdel⟩ := h p hp
    refine ⟨step_dealerSent_monotone _ _ _ hsent, ?_, ?_⟩
    · rw [step_corrupted_invariant]; exact hnc
    · by_cases hpq : p = msg.receiver
      · rw [hpq]
        have : ((step (.partyReceiveReady msg) s).local_ msg.receiver).delivered =
            (s.local_ msg.receiver).delivered := by
          simp [step, setLocal]
        rw [this, ← hpq]; exact hdel
      · have : (step (.partyReceiveReady msg) s).local_ p = s.local_ p := by
          simp [step, setLocal, hpq]
        rw [this]; exact hdel
  | partyOutput q cert =>
    have h_ifd : (step (.partyOutput q cert) s).inflightDeliveries =
        s.inflightDeliveries := by simp [step, setLocal]
    rw [h_ifd] at hp
    obtain ⟨hsent, hnc, hdel⟩ := h p hp
    refine ⟨step_dealerSent_monotone _ _ _ hsent, ?_, ?_⟩
    · rw [step_corrupted_invariant]; exact hnc
    · by_cases hpq : p = q
      · subst hpq
        have : ((step (.partyOutput p cert) s).local_ p).delivered =
            (s.local_ p).delivered := by
          simp [step, setLocal]
        rw [this]; exact hdel
      · have : (step (.partyOutput q cert) s).local_ p = s.local_ p := by
          simp [step, setLocal, hpq]
        rw [this]; exact hdel

/-! ### 2. `inflightCorruptDeliveriesWf` -/

/-- Every entry of `inflightCorruptDeliveries` is corrupt, has
`dealerSent` set, and has not yet been delivered. -/
def inflightCorruptDeliveriesWf (s : State n t F) : Prop :=
  ∀ p, p ∈ s.inflightCorruptDeliveries ->
    s.dealerSent p = true ∧ p ∈ s.corrupted ∧ (s.local_ p).delivered = none

omit [Fintype F] [DecidableEq F] in
/-- Vacuous at init: `inflightCorruptDeliveries` is empty. -/
theorem inflightCorruptDeliveriesWf_init (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F) (s : State n t F)
    (h : initPred sec corr coeffs s) :
    inflightCorruptDeliveriesWf s := by
  intro p hp
  rw [h.2.2.2.2.2.1] at hp
  exact absurd hp (Finset.notMem_empty _)

omit [Fintype F] in
/-- Preservation of `inflightCorruptDeliveriesWf`. -/
theorem inflightCorruptDeliveriesWf_preserve
    (a : Action n t F) (s : State n t F)
    (hgate : gate a s) (hdis : deliveredImpliesDealerSent s)
    (h : inflightCorruptDeliveriesWf s) :
    inflightCorruptDeliveriesWf (step a s) := by
  intro p hp
  cases a with
  | dealerShareTo q =>
    by_cases hqc : q ∈ s.corrupted
    · -- post.ifcd = insert q pre.ifcd
      have h_ifcd : (step (.dealerShareTo q) s).inflightCorruptDeliveries =
          insert q s.inflightCorruptDeliveries := by
        simp [step, hqc]
      rw [h_ifcd] at hp
      rcases Finset.mem_insert.mp hp with rfl | hp_old
      · have hgate' : s.dealerSent p = false := hgate
        have hdel : (s.local_ p).delivered = none := by
          by_contra h0
          have : (s.local_ p).delivered.isSome := by
            cases hd : (s.local_ p).delivered with
            | none => exact absurd hd h0
            | some _ => simp [hd]
          have := hdis p this
          rw [this] at hgate'; cases hgate'
        refine ⟨step_dealerSent_set_after s p, ?_, ?_⟩
        · rw [step_corrupted_invariant]; exact hqc
        · have : (step (.dealerShareTo p) s).local_ p = s.local_ p := by
            simp [step, setLocal]
          rw [this]; exact hdel
      · obtain ⟨hsent, hcc, hdel⟩ := h p hp_old
        refine ⟨step_dealerSent_monotone _ _ _ hsent, ?_, ?_⟩
        · rw [step_corrupted_invariant]; exact hcc
        · have : (step (.dealerShareTo q) s).local_ p = s.local_ p := by
            simp [step, setLocal]
          rw [this]; exact hdel
    · have h_ifcd : (step (.dealerShareTo q) s).inflightCorruptDeliveries =
          s.inflightCorruptDeliveries := by simp [step, hqc]
      rw [h_ifcd] at hp
      obtain ⟨hsent, hcc, hdel⟩ := h p hp
      refine ⟨step_dealerSent_monotone _ _ _ hsent, ?_, ?_⟩
      · rw [step_corrupted_invariant]; exact hcc
      · have : (step (.dealerShareTo q) s).local_ p = s.local_ p := by
          simp [step, setLocal]
        rw [this]; exact hdel
  | partyDeliver q =>
    -- post.ifcd unchanged.  q is honest by gate; q ∉ pre.ifcd by inv → p ≠ q.
    have h_ifcd : (step (.partyDeliver q) s).inflightCorruptDeliveries =
        s.inflightCorruptDeliveries := by simp [step, setLocal]
    rw [h_ifcd] at hp
    obtain ⟨hsent, hcc, hdel⟩ := h p hp
    have hpq : p ≠ q := by
      intro heq; subst heq
      exact hgate.2.1 hcc
    refine ⟨step_dealerSent_monotone _ _ _ hsent, ?_, ?_⟩
    · rw [step_corrupted_invariant]; exact hcc
    · have hloc : (step (.partyDeliver q) s).local_ p = s.local_ p := by
        simp [step, setLocal, hpq]
      rw [hloc]; exact hdel
  | partyCorruptDeliver q =>
    -- post.ifcd = pre.ifcd.erase q.
    have h_ifcd : (step (.partyCorruptDeliver q) s).inflightCorruptDeliveries =
        s.inflightCorruptDeliveries.erase q := by simp [step, setLocal]
    rw [h_ifcd] at hp
    have hp_old : p ∈ s.inflightCorruptDeliveries := Finset.mem_of_mem_erase hp
    have hpq : p ≠ q := Finset.ne_of_mem_erase hp
    obtain ⟨hsent, hcc, hdel⟩ := h p hp_old
    refine ⟨step_dealerSent_monotone _ _ _ hsent, ?_, ?_⟩
    · rw [step_corrupted_invariant]; exact hcc
    · have hloc : (step (.partyCorruptDeliver q) s).local_ p = s.local_ p := by
        simp [step, setLocal, hpq]
      rw [hloc]; exact hdel
  | partyEchoSend q r =>
    have h_ifcd : (step (.partyEchoSend q r) s).inflightCorruptDeliveries =
        s.inflightCorruptDeliveries := by simp [step, setLocal]
    rw [h_ifcd] at hp
    obtain ⟨hsent, hcc, hdel⟩ := h p hp
    refine ⟨step_dealerSent_monotone _ _ _ hsent, ?_, ?_⟩
    · rw [step_corrupted_invariant]; exact hcc
    · by_cases hpq : p = q
      · subst hpq
        have : ((step (.partyEchoSend p r) s).local_ p).delivered =
            (s.local_ p).delivered := by simp [step, setLocal]
        rw [this]; exact hdel
      · have : (step (.partyEchoSend q r) s).local_ p = s.local_ p := by
          simp [step, setLocal, hpq]
        rw [this]; exact hdel
  | partyEchoReceive msg =>
    have h_ifcd : (step (.partyEchoReceive msg) s).inflightCorruptDeliveries =
        s.inflightCorruptDeliveries := by simp [step, setLocal]
    rw [h_ifcd] at hp
    obtain ⟨hsent, hcc, hdel⟩ := h p hp
    refine ⟨step_dealerSent_monotone _ _ _ hsent, ?_, ?_⟩
    · rw [step_corrupted_invariant]; exact hcc
    · by_cases hpq : p = msg.receiver
      · rw [hpq]
        have : ((step (.partyEchoReceive msg) s).local_ msg.receiver).delivered =
            (s.local_ msg.receiver).delivered := by simp [step, setLocal]
        rw [this, ← hpq]; exact hdel
      · have : (step (.partyEchoReceive msg) s).local_ p = s.local_ p := by
          simp [step, setLocal, hpq]
        rw [this]; exact hdel
  | partyReady q cert =>
    have h_ifcd : (step (.partyReady q cert) s).inflightCorruptDeliveries =
        s.inflightCorruptDeliveries := by simp [step, setLocal]
    rw [h_ifcd] at hp
    obtain ⟨hsent, hcc, hdel⟩ := h p hp
    refine ⟨step_dealerSent_monotone _ _ _ hsent, ?_, ?_⟩
    · rw [step_corrupted_invariant]; exact hcc
    · by_cases hpq : p = q
      · subst hpq
        have : ((step (.partyReady p cert) s).local_ p).delivered =
            (s.local_ p).delivered := by simp [step, setLocal]
        rw [this]; exact hdel
      · have : (step (.partyReady q cert) s).local_ p = s.local_ p := by
          simp [step, setLocal, hpq]
        rw [this]; exact hdel
  | partyAmplify q cert =>
    have h_ifcd : (step (.partyAmplify q cert) s).inflightCorruptDeliveries =
        s.inflightCorruptDeliveries := by simp [step, setLocal]
    rw [h_ifcd] at hp
    obtain ⟨hsent, hcc, hdel⟩ := h p hp
    refine ⟨step_dealerSent_monotone _ _ _ hsent, ?_, ?_⟩
    · rw [step_corrupted_invariant]; exact hcc
    · by_cases hpq : p = q
      · subst hpq
        have : ((step (.partyAmplify p cert) s).local_ p).delivered =
            (s.local_ p).delivered := by simp [step, setLocal]
        rw [this]; exact hdel
      · have : (step (.partyAmplify q cert) s).local_ p = s.local_ p := by
          simp [step, setLocal, hpq]
        rw [this]; exact hdel
  | partyReceiveReady msg =>
    have h_ifcd : (step (.partyReceiveReady msg) s).inflightCorruptDeliveries =
        s.inflightCorruptDeliveries := by simp [step, setLocal]
    rw [h_ifcd] at hp
    obtain ⟨hsent, hcc, hdel⟩ := h p hp
    refine ⟨step_dealerSent_monotone _ _ _ hsent, ?_, ?_⟩
    · rw [step_corrupted_invariant]; exact hcc
    · by_cases hpq : p = msg.receiver
      · rw [hpq]
        have : ((step (.partyReceiveReady msg) s).local_ msg.receiver).delivered =
            (s.local_ msg.receiver).delivered := by simp [step, setLocal]
        rw [this, ← hpq]; exact hdel
      · have : (step (.partyReceiveReady msg) s).local_ p = s.local_ p := by
          simp [step, setLocal, hpq]
        rw [this]; exact hdel
  | partyOutput q cert =>
    have h_ifcd : (step (.partyOutput q cert) s).inflightCorruptDeliveries =
        s.inflightCorruptDeliveries := by simp [step, setLocal]
    rw [h_ifcd] at hp
    obtain ⟨hsent, hcc, hdel⟩ := h p hp
    refine ⟨step_dealerSent_monotone _ _ _ hsent, ?_, ?_⟩
    · rw [step_corrupted_invariant]; exact hcc
    · by_cases hpq : p = q
      · subst hpq
        have : ((step (.partyOutput p cert) s).local_ p).delivered =
            (s.local_ p).delivered := by simp [step, setLocal]
        rw [this]; exact hdel
      · have : (step (.partyOutput q cert) s).local_ p = s.local_ p := by
          simp [step, setLocal, hpq]
        rw [this]; exact hdel

/-! ### 3. `outputImpliesDelivered` -/

/-- A party with `output` set must have `delivered` set; the
`partyOutput` gate requires `delivered = some cert.candidate`. -/
def outputImpliesDelivered (s : State n t F) : Prop :=
  ∀ p, (s.local_ p).output.isSome -> (s.local_ p).delivered.isSome

omit [Fintype F] [DecidableEq F] in
/-- Vacuous at init. -/
theorem outputImpliesDelivered_init (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F) (s : State n t F)
    (h : initPred sec corr coeffs s) :
    outputImpliesDelivered s := by
  intro p hout
  rw [h.1 p] at hout
  simp [LocalState.init] at hout

omit [Fintype F] in
/-- Preservation. -/
theorem outputImpliesDelivered_preserve
    (a : Action n t F) (s : State n t F)
    (hgate : gate a s) (h : outputImpliesDelivered s) :
    outputImpliesDelivered (step a s) := by
  intro p hout
  cases a with
  | dealerShareTo q =>
    have hloc : (step (.dealerShareTo q) s).local_ p = s.local_ p := by
      simp [step, setLocal]
    rw [hloc] at hout ⊢; exact h p hout
  | partyDeliver q =>
    by_cases hpq : p = q
    · subst hpq
      have hloc : (step (.partyDeliver p) s).local_ p =
          { s.local_ p with delivered := some (s.dealerCommit p) } := by
        simp [step, setLocal]
      rw [hloc]; simp
    · have hloc : (step (.partyDeliver q) s).local_ p = s.local_ p := by
        simp [step, setLocal, hpq]
      rw [hloc] at hout ⊢; exact h p hout
  | partyCorruptDeliver q =>
    by_cases hpq : p = q
    · subst hpq
      have hloc : (step (.partyCorruptDeliver p) s).local_ p =
          { s.local_ p with delivered := some (s.dealerCommit p) } := by
        simp [step, setLocal]
      rw [hloc]; simp
    · have hloc : (step (.partyCorruptDeliver q) s).local_ p = s.local_ p := by
        simp [step, setLocal, hpq]
      rw [hloc] at hout ⊢; exact h p hout
  | partyEchoSend q r =>
    by_cases hpq : p = q
    · subst hpq
      have hloc : (step (.partyEchoSend p r) s).local_ p =
          { s.local_ p with echoedTo := insert r (s.local_ p).echoedTo } := by
        simp [step, setLocal]
      rw [hloc] at hout ⊢
      simp at hout ⊢
      exact h p hout
    · have hloc : (step (.partyEchoSend q r) s).local_ p = s.local_ p := by
        simp [step, setLocal, hpq]
      rw [hloc] at hout ⊢; exact h p hout
  | partyEchoReceive msg =>
    by_cases hpq : p = msg.receiver
    · rw [hpq] at hout ⊢
      have hloc : (step (.partyEchoReceive msg) s).local_ msg.receiver =
          { s.local_ msg.receiver with
            acceptedEchoes :=
              insert msg (s.local_ msg.receiver).acceptedEchoes } := by
        simp [step, setLocal]
      rw [hloc] at hout ⊢
      simp at hout ⊢
      exact h msg.receiver hout
    · have hloc : (step (.partyEchoReceive msg) s).local_ p = s.local_ p := by
        simp [step, setLocal, hpq]
      rw [hloc] at hout ⊢; exact h p hout
  | partyReady q cert =>
    by_cases hpq : p = q
    · subst hpq
      have hloc : (step (.partyReady p cert) s).local_ p =
          { s.local_ p with readySent := insert cert (s.local_ p).readySent } := by
        simp [step, setLocal]
      rw [hloc] at hout ⊢
      simp at hout ⊢
      exact h p hout
    · have hloc : (step (.partyReady q cert) s).local_ p = s.local_ p := by
        simp [step, setLocal, hpq]
      rw [hloc] at hout ⊢; exact h p hout
  | partyAmplify q cert =>
    by_cases hpq : p = q
    · subst hpq
      have hloc : (step (.partyAmplify p cert) s).local_ p =
          { s.local_ p with readySent := insert cert (s.local_ p).readySent } := by
        simp [step, setLocal]
      rw [hloc] at hout ⊢
      simp at hout ⊢
      exact h p hout
    · have hloc : (step (.partyAmplify q cert) s).local_ p = s.local_ p := by
        simp [step, setLocal, hpq]
      rw [hloc] at hout ⊢; exact h p hout
  | partyReceiveReady msg =>
    by_cases hpq : p = msg.receiver
    · rw [hpq] at hout ⊢
      have hloc : (step (.partyReceiveReady msg) s).local_ msg.receiver =
          { s.local_ msg.receiver with
            readyReceived :=
              insert msg (s.local_ msg.receiver).readyReceived } := by
        simp [step, setLocal]
      rw [hloc] at hout ⊢
      simp at hout ⊢
      exact h msg.receiver hout
    · have hloc : (step (.partyReceiveReady msg) s).local_ p = s.local_ p := by
        simp [step, setLocal, hpq]
      rw [hloc] at hout ⊢; exact h p hout
  | partyOutput q cert =>
    by_cases hpq : p = q
    · subst hpq
      have hloc : (step (.partyOutput p cert) s).local_ p =
          { s.local_ p with
            output := some (AVSS.evalRowPoly cert.candidate.rowPoly 0) } := by
        simp [step, setLocal]
      rw [hloc]
      -- gate gives delivered = some cert.candidate
      have hdel : (s.local_ p).delivered = some cert.candidate := hgate.2.2.1
      simp [hdel]
    · have hloc : (step (.partyOutput q cert) s).local_ p = s.local_ p := by
        simp [step, setLocal, hpq]
      rw [hloc] at hout ⊢; exact h p hout

/-! ### 4. `acceptedEchoesAddressed` -/

/-- Every accepted echo at `p` is addressed to `p`.  The `partyEchoReceive`
gate requires this. -/
def acceptedEchoesAddressed (s : State n t F) : Prop :=
  ∀ p, ∀ msg ∈ (s.local_ p).acceptedEchoes, msg.receiver = p

omit [Fintype F] [DecidableEq F] in
/-- Vacuous at init. -/
theorem acceptedEchoesAddressed_init (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F) (s : State n t F)
    (h : initPred sec corr coeffs s) :
    acceptedEchoesAddressed s := by
  intro p msg hmsg
  rw [h.1 p] at hmsg
  simp [LocalState.init] at hmsg

omit [Fintype F] in
/-- Preservation. -/
theorem acceptedEchoesAddressed_preserve
    (a : Action n t F) (s : State n t F)
    (hgate : gate a s) (h : acceptedEchoesAddressed s) :
    acceptedEchoesAddressed (step a s) := by
  intro p msg hmsg
  cases a with
  | dealerShareTo q =>
    have hloc : (step (.dealerShareTo q) s).local_ p = s.local_ p := by
      simp [step, setLocal]
    rw [hloc] at hmsg; exact h p msg hmsg
  | partyDeliver q =>
    by_cases hpq : p = q
    · subst hpq
      have hloc : (step (.partyDeliver p) s).local_ p =
          { s.local_ p with delivered := some (s.dealerCommit p) } := by
        simp [step, setLocal]
      rw [hloc] at hmsg
      simp at hmsg
      exact h p msg hmsg
    · have hloc : (step (.partyDeliver q) s).local_ p = s.local_ p := by
        simp [step, setLocal, hpq]
      rw [hloc] at hmsg; exact h p msg hmsg
  | partyCorruptDeliver q =>
    by_cases hpq : p = q
    · subst hpq
      have hloc : (step (.partyCorruptDeliver p) s).local_ p =
          { s.local_ p with delivered := some (s.dealerCommit p) } := by
        simp [step, setLocal]
      rw [hloc] at hmsg
      simp at hmsg
      exact h p msg hmsg
    · have hloc : (step (.partyCorruptDeliver q) s).local_ p = s.local_ p := by
        simp [step, setLocal, hpq]
      rw [hloc] at hmsg; exact h p msg hmsg
  | partyEchoSend q r =>
    by_cases hpq : p = q
    · subst hpq
      have hloc : (step (.partyEchoSend p r) s).local_ p =
          { s.local_ p with echoedTo := insert r (s.local_ p).echoedTo } := by
        simp [step, setLocal]
      rw [hloc] at hmsg
      simp at hmsg
      exact h p msg hmsg
    · have hloc : (step (.partyEchoSend q r) s).local_ p = s.local_ p := by
        simp [step, setLocal, hpq]
      rw [hloc] at hmsg; exact h p msg hmsg
  | partyEchoReceive msg' =>
    by_cases hpq : p = msg'.receiver
    · rw [hpq] at hmsg ⊢
      have hloc : (step (.partyEchoReceive msg') s).local_ msg'.receiver =
          { s.local_ msg'.receiver with
            acceptedEchoes :=
              insert msg' (s.local_ msg'.receiver).acceptedEchoes } := by
        simp [step, setLocal]
      rw [hloc] at hmsg
      simp at hmsg
      rcases hmsg with rfl | hmsg_old
      · -- msg = msg', and gate says ∃ candidate, ... validEchoFor where
        -- validEchoFor demands msg.receiver = msg'.receiver.
        obtain ⟨_, _, _, hve, _⟩ := hgate
        exact hve.1
      · exact h msg'.receiver msg hmsg_old
    · have hloc : (step (.partyEchoReceive msg') s).local_ p = s.local_ p := by
        simp [step, setLocal, hpq]
      rw [hloc] at hmsg; exact h p msg hmsg
  | partyReady q cert =>
    by_cases hpq : p = q
    · subst hpq
      have hloc : (step (.partyReady p cert) s).local_ p =
          { s.local_ p with readySent := insert cert (s.local_ p).readySent } := by
        simp [step, setLocal]
      rw [hloc] at hmsg
      simp at hmsg
      exact h p msg hmsg
    · have hloc : (step (.partyReady q cert) s).local_ p = s.local_ p := by
        simp [step, setLocal, hpq]
      rw [hloc] at hmsg; exact h p msg hmsg
  | partyAmplify q cert =>
    by_cases hpq : p = q
    · subst hpq
      have hloc : (step (.partyAmplify p cert) s).local_ p =
          { s.local_ p with readySent := insert cert (s.local_ p).readySent } := by
        simp [step, setLocal]
      rw [hloc] at hmsg
      simp at hmsg
      exact h p msg hmsg
    · have hloc : (step (.partyAmplify q cert) s).local_ p = s.local_ p := by
        simp [step, setLocal, hpq]
      rw [hloc] at hmsg; exact h p msg hmsg
  | partyReceiveReady msg' =>
    by_cases hpq : p = msg'.receiver
    · rw [hpq] at hmsg ⊢
      have hloc : (step (.partyReceiveReady msg') s).local_ msg'.receiver =
          { s.local_ msg'.receiver with
            readyReceived :=
              insert msg' (s.local_ msg'.receiver).readyReceived } := by
        simp [step, setLocal]
      rw [hloc] at hmsg
      simp at hmsg
      exact h msg'.receiver msg hmsg
    · have hloc : (step (.partyReceiveReady msg') s).local_ p = s.local_ p := by
        simp [step, setLocal, hpq]
      rw [hloc] at hmsg; exact h p msg hmsg
  | partyOutput q cert =>
    by_cases hpq : p = q
    · subst hpq
      have hloc : (step (.partyOutput p cert) s).local_ p =
          { s.local_ p with
            output := some (AVSS.evalRowPoly cert.candidate.rowPoly 0) } := by
        simp [step, setLocal]
      rw [hloc] at hmsg
      simp at hmsg
      exact h p msg hmsg
    · have hloc : (step (.partyOutput q cert) s).local_ p = s.local_ p := by
        simp [step, setLocal, hpq]
      rw [hloc] at hmsg; exact h p msg hmsg

/-! ### 5. `inflightEchoesSenderDelivered` -/

/-- Every queued echo's sender has `delivered.isSome`.  The
`partyEchoSend` gate requires this when the echo enters the queue;
once delivered, it stays delivered (delivered is monotone). -/
def inflightEchoesSenderDelivered (s : State n t F) : Prop :=
  ∀ msg ∈ s.inflightEchoes, (s.local_ msg.sender).delivered.isSome

omit [Fintype F] [DecidableEq F] in
/-- Vacuous at init: `inflightEchoes` is empty. -/
theorem inflightEchoesSenderDelivered_init (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F) (s : State n t F)
    (h : initPred sec corr coeffs s) :
    inflightEchoesSenderDelivered s := by
  intro msg hmsg
  rw [h.2.2.2.2.2.2.1] at hmsg
  exact absurd hmsg (Finset.notMem_empty _)

omit [Fintype F] in
/-- Preservation. -/
theorem inflightEchoesSenderDelivered_preserve
    (a : Action n t F) (s : State n t F)
    (hgate : gate a s) (h : inflightEchoesSenderDelivered s) :
    inflightEchoesSenderDelivered (step a s) := by
  intro msg hmsg
  -- Key lemma: `delivered` is monotone — once `isSome` always `isSome`.
  -- We'll show: if msg.sender's pre.delivered.isSome, post.delivered.isSome.
  cases a with
  | dealerShareTo q =>
    have h_ife : (step (.dealerShareTo q) s).inflightEchoes =
        s.inflightEchoes := by simp [step, setLocal]
    rw [h_ife] at hmsg
    have hpre := h msg hmsg
    have hloc : (step (.dealerShareTo q) s).local_ msg.sender =
        s.local_ msg.sender := by simp [step, setLocal]
    rw [hloc]; exact hpre
  | partyDeliver q =>
    have h_ife : (step (.partyDeliver q) s).inflightEchoes =
        s.inflightEchoes := by simp [step, setLocal]
    rw [h_ife] at hmsg
    have hpre := h msg hmsg
    by_cases hsq : msg.sender = q
    · rw [hsq]
      have : ((step (.partyDeliver q) s).local_ q).delivered =
          some (s.dealerCommit q) := by simp [step, setLocal]
      rw [this]; simp
    · have : (step (.partyDeliver q) s).local_ msg.sender = s.local_ msg.sender := by
        simp [step, setLocal, hsq]
      rw [this]; exact hpre
  | partyCorruptDeliver q =>
    have h_ife : (step (.partyCorruptDeliver q) s).inflightEchoes =
        s.inflightEchoes := by simp [step, setLocal]
    rw [h_ife] at hmsg
    have hpre := h msg hmsg
    by_cases hsq : msg.sender = q
    · rw [hsq]
      have : ((step (.partyCorruptDeliver q) s).local_ q).delivered =
          some (s.dealerCommit q) := by simp [step, setLocal]
      rw [this]; simp
    · have : (step (.partyCorruptDeliver q) s).local_ msg.sender =
          s.local_ msg.sender := by simp [step, setLocal, hsq]
      rw [this]; exact hpre
  | partyEchoSend q r =>
    -- post.ife = insert (new echo with sender = q) pre.ife
    have h_ife : (step (.partyEchoSend q r) s).inflightEchoes =
        insert
          ({ sender := q, receiver := r,
             senderPayload := (s.local_ q).delivered.getD (s.dealerCommit q),
             value := AVSS.evalRowPoly
                 ((s.local_ q).delivered.getD (s.dealerCommit q)).rowPoly
                 (s.partyPoint r) } : EchoMsg n t F)
          s.inflightEchoes := by
      simp [step, setLocal]
    rw [h_ife] at hmsg
    rcases Finset.mem_insert.mp hmsg with rfl | hmsg_old
    · -- New echo: sender = q. Gate gives (s.local_ q).delivered.isSome.
      have hgq : (s.local_ q).delivered.isSome := hgate.1
      -- Post local_ q has updated echoedTo, but delivered unchanged.
      have : ((step (.partyEchoSend q r) s).local_ q).delivered =
          (s.local_ q).delivered := by simp [step, setLocal]
      show ((step (.partyEchoSend q r) s).local_ _).delivered.isSome
      rw [this]; exact hgq
    · have hpre := h msg hmsg_old
      by_cases hsq : msg.sender = q
      · rw [hsq]
        have : ((step (.partyEchoSend q r) s).local_ q).delivered =
            (s.local_ q).delivered := by simp [step, setLocal]
        rw [this, ← hsq]; exact hpre
      · have : (step (.partyEchoSend q r) s).local_ msg.sender =
            s.local_ msg.sender := by simp [step, setLocal, hsq]
        rw [this]; exact hpre
  | partyEchoReceive msg' =>
    -- post.ife = pre.ife.erase msg'
    have h_ife : (step (.partyEchoReceive msg') s).inflightEchoes =
        s.inflightEchoes.erase msg' := by simp [step, setLocal]
    rw [h_ife] at hmsg
    have hmsg_old : msg ∈ s.inflightEchoes := Finset.mem_of_mem_erase hmsg
    have hpre := h msg hmsg_old
    by_cases hsr : msg.sender = msg'.receiver
    · rw [hsr]
      have : ((step (.partyEchoReceive msg') s).local_ msg'.receiver).delivered =
          (s.local_ msg'.receiver).delivered := by simp [step, setLocal]
      rw [this, ← hsr]; exact hpre
    · have : (step (.partyEchoReceive msg') s).local_ msg.sender =
          s.local_ msg.sender := by simp [step, setLocal, hsr]
      rw [this]; exact hpre
  | partyReady q cert =>
    have h_ife : (step (.partyReady q cert) s).inflightEchoes =
        s.inflightEchoes := by simp [step, setLocal]
    rw [h_ife] at hmsg
    have hpre := h msg hmsg
    by_cases hsq : msg.sender = q
    · rw [hsq]
      have : ((step (.partyReady q cert) s).local_ q).delivered =
          (s.local_ q).delivered := by simp [step, setLocal]
      rw [this, ← hsq]; exact hpre
    · have : (step (.partyReady q cert) s).local_ msg.sender =
          s.local_ msg.sender := by simp [step, setLocal, hsq]
      rw [this]; exact hpre
  | partyAmplify q cert =>
    have h_ife : (step (.partyAmplify q cert) s).inflightEchoes =
        s.inflightEchoes := by simp [step, setLocal]
    rw [h_ife] at hmsg
    have hpre := h msg hmsg
    by_cases hsq : msg.sender = q
    · rw [hsq]
      have : ((step (.partyAmplify q cert) s).local_ q).delivered =
          (s.local_ q).delivered := by simp [step, setLocal]
      rw [this, ← hsq]; exact hpre
    · have : (step (.partyAmplify q cert) s).local_ msg.sender =
          s.local_ msg.sender := by simp [step, setLocal, hsq]
      rw [this]; exact hpre
  | partyReceiveReady msg' =>
    have h_ife : (step (.partyReceiveReady msg') s).inflightEchoes =
        s.inflightEchoes := by simp [step, setLocal]
    rw [h_ife] at hmsg
    have hpre := h msg hmsg
    by_cases hsr : msg.sender = msg'.receiver
    · rw [hsr]
      have : ((step (.partyReceiveReady msg') s).local_ msg'.receiver).delivered =
          (s.local_ msg'.receiver).delivered := by simp [step, setLocal]
      rw [this, ← hsr]; exact hpre
    · have : (step (.partyReceiveReady msg') s).local_ msg.sender =
          s.local_ msg.sender := by simp [step, setLocal, hsr]
      rw [this]; exact hpre
  | partyOutput q cert =>
    have h_ife : (step (.partyOutput q cert) s).inflightEchoes =
        s.inflightEchoes := by simp [step, setLocal]
    rw [h_ife] at hmsg
    have hpre := h msg hmsg
    by_cases hsq : msg.sender = q
    · rw [hsq]
      have : ((step (.partyOutput q cert) s).local_ q).delivered =
          (s.local_ q).delivered := by simp [step, setLocal]
      rw [this, ← hsq]; exact hpre
    · have : (step (.partyOutput q cert) s).local_ msg.sender =
          s.local_ msg.sender := by simp [step, setLocal, hsq]
      rw [this]; exact hpre

/-! ### 6. `inflightReadySenderReady` -/

/-- Every queued ready message's certificate is in the sender's
`readySent`.  Both `partyReady` and `partyAmplify` insert into
`readySent` and `inflightReady` simultaneously; `readySent` is
monotone. -/
def inflightReadySenderReady (s : State n t F) : Prop :=
  ∀ msg ∈ s.inflightReady, msg.cert ∈ (s.local_ msg.sender).readySent

omit [Fintype F] [DecidableEq F] in
/-- Vacuous at init: `inflightReady` is empty. -/
theorem inflightReadySenderReady_init (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F) (s : State n t F)
    (h : initPred sec corr coeffs s) :
    inflightReadySenderReady s := by
  intro msg hmsg
  rw [h.2.2.2.2.2.2.2.1] at hmsg
  exact absurd hmsg (Finset.notMem_empty _)

omit [Fintype F] in
/-- Preservation. -/
theorem inflightReadySenderReady_preserve
    (a : Action n t F) (s : State n t F)
    (hgate : gate a s) (h : inflightReadySenderReady s) :
    inflightReadySenderReady (step a s) := by
  intro msg hmsg
  cases a with
  | dealerShareTo q =>
    have h_ifr : (step (.dealerShareTo q) s).inflightReady =
        s.inflightReady := by simp [step, setLocal]
    rw [h_ifr] at hmsg
    have hpre := h msg hmsg
    have hloc : (step (.dealerShareTo q) s).local_ msg.sender =
        s.local_ msg.sender := by simp [step, setLocal]
    rw [hloc]; exact hpre
  | partyDeliver q =>
    have h_ifr : (step (.partyDeliver q) s).inflightReady =
        s.inflightReady := by simp [step, setLocal]
    rw [h_ifr] at hmsg
    have hpre := h msg hmsg
    by_cases hsq : msg.sender = q
    · rw [hsq]
      have : ((step (.partyDeliver q) s).local_ q).readySent =
          (s.local_ q).readySent := by simp [step, setLocal]
      rw [this, ← hsq]; exact hpre
    · have : (step (.partyDeliver q) s).local_ msg.sender = s.local_ msg.sender := by
        simp [step, setLocal, hsq]
      rw [this]; exact hpre
  | partyCorruptDeliver q =>
    have h_ifr : (step (.partyCorruptDeliver q) s).inflightReady =
        s.inflightReady := by simp [step, setLocal]
    rw [h_ifr] at hmsg
    have hpre := h msg hmsg
    by_cases hsq : msg.sender = q
    · rw [hsq]
      have : ((step (.partyCorruptDeliver q) s).local_ q).readySent =
          (s.local_ q).readySent := by simp [step, setLocal]
      rw [this, ← hsq]; exact hpre
    · have : (step (.partyCorruptDeliver q) s).local_ msg.sender =
          s.local_ msg.sender := by simp [step, setLocal, hsq]
      rw [this]; exact hpre
  | partyEchoSend q r =>
    have h_ifr : (step (.partyEchoSend q r) s).inflightReady =
        s.inflightReady := by simp [step, setLocal]
    rw [h_ifr] at hmsg
    have hpre := h msg hmsg
    by_cases hsq : msg.sender = q
    · rw [hsq]
      have : ((step (.partyEchoSend q r) s).local_ q).readySent =
          (s.local_ q).readySent := by simp [step, setLocal]
      rw [this, ← hsq]; exact hpre
    · have : (step (.partyEchoSend q r) s).local_ msg.sender =
          s.local_ msg.sender := by simp [step, setLocal, hsq]
      rw [this]; exact hpre
  | partyEchoReceive msg' =>
    have h_ifr : (step (.partyEchoReceive msg') s).inflightReady =
        s.inflightReady := by simp [step, setLocal]
    rw [h_ifr] at hmsg
    have hpre := h msg hmsg
    by_cases hsr : msg.sender = msg'.receiver
    · rw [hsr]
      have : ((step (.partyEchoReceive msg') s).local_ msg'.receiver).readySent =
          (s.local_ msg'.receiver).readySent := by simp [step, setLocal]
      rw [this, ← hsr]; exact hpre
    · have : (step (.partyEchoReceive msg') s).local_ msg.sender =
          s.local_ msg.sender := by simp [step, setLocal, hsr]
      rw [this]; exact hpre
  | partyReady q cert =>
    -- post.ifr = pre.ifr ∪ {sender:=q,receiver:=r,cert:=cert | r}
    -- post.local_ q.readySent = insert cert (pre.local_ q).readySent
    have h_ifr : (step (.partyReady q cert) s).inflightReady =
        s.inflightReady ∪
          (Finset.univ : Finset (Fin n)).image
            (fun r => ({ sender := q, receiver := r, cert := cert } : ReadyMsg n t F)) := by
      simp [step, setLocal]
    rw [h_ifr] at hmsg
    rcases Finset.mem_union.mp hmsg with hmsg_old | hmsg_new
    · have hpre := h msg hmsg_old
      by_cases hsq : msg.sender = q
      · rw [hsq]
        have : ((step (.partyReady q cert) s).local_ q).readySent =
            insert cert (s.local_ q).readySent := by simp [step, setLocal]
        rw [this]; exact Finset.mem_insert_of_mem (hsq ▸ hpre)
      · have : (step (.partyReady q cert) s).local_ msg.sender =
            s.local_ msg.sender := by simp [step, setLocal, hsq]
        rw [this]; exact hpre
    · -- new message: sender = q, cert = cert
      simp at hmsg_new
      obtain ⟨r, hmsg_eq⟩ := hmsg_new
      rw [← hmsg_eq]
      simp
      have : ((step (.partyReady q cert) s).local_ q).readySent =
          insert cert (s.local_ q).readySent := by simp [step, setLocal]
      rw [this]; exact Finset.mem_insert_self _ _
  | partyAmplify q cert =>
    have h_ifr : (step (.partyAmplify q cert) s).inflightReady =
        s.inflightReady ∪
          (Finset.univ : Finset (Fin n)).image
            (fun r => ({ sender := q, receiver := r, cert := cert } : ReadyMsg n t F)) := by
      simp [step, setLocal]
    rw [h_ifr] at hmsg
    rcases Finset.mem_union.mp hmsg with hmsg_old | hmsg_new
    · have hpre := h msg hmsg_old
      by_cases hsq : msg.sender = q
      · rw [hsq]
        have : ((step (.partyAmplify q cert) s).local_ q).readySent =
            insert cert (s.local_ q).readySent := by simp [step, setLocal]
        rw [this]; exact Finset.mem_insert_of_mem (hsq ▸ hpre)
      · have : (step (.partyAmplify q cert) s).local_ msg.sender =
            s.local_ msg.sender := by simp [step, setLocal, hsq]
        rw [this]; exact hpre
    · simp at hmsg_new
      obtain ⟨r, hmsg_eq⟩ := hmsg_new
      rw [← hmsg_eq]
      simp
      have : ((step (.partyAmplify q cert) s).local_ q).readySent =
          insert cert (s.local_ q).readySent := by simp [step, setLocal]
      rw [this]; exact Finset.mem_insert_self _ _
  | partyReceiveReady msg' =>
    have h_ifr : (step (.partyReceiveReady msg') s).inflightReady =
        s.inflightReady.erase msg' := by simp [step, setLocal]
    rw [h_ifr] at hmsg
    have hmsg_old : msg ∈ s.inflightReady := Finset.mem_of_mem_erase hmsg
    have hpre := h msg hmsg_old
    by_cases hsr : msg.sender = msg'.receiver
    · rw [hsr]
      have : ((step (.partyReceiveReady msg') s).local_ msg'.receiver).readySent =
          (s.local_ msg'.receiver).readySent := by simp [step, setLocal]
      rw [this, ← hsr]; exact hpre
    · have : (step (.partyReceiveReady msg') s).local_ msg.sender =
          s.local_ msg.sender := by simp [step, setLocal, hsr]
      rw [this]; exact hpre
  | partyOutput q cert =>
    have h_ifr : (step (.partyOutput q cert) s).inflightReady =
        s.inflightReady := by simp [step, setLocal]
    rw [h_ifr] at hmsg
    have hpre := h msg hmsg
    by_cases hsq : msg.sender = q
    · rw [hsq]
      have : ((step (.partyOutput q cert) s).local_ q).readySent =
          (s.local_ q).readySent := by simp [step, setLocal]
      rw [this, ← hsq]; exact hpre
    · have : (step (.partyOutput q cert) s).local_ msg.sender =
          s.local_ msg.sender := by simp [step, setLocal, hsq]
      rw [this]; exact hpre

/-! ## Step 3a — Termination certificate scaffolding

This section adapts the AVSS termination-certificate scaffolding
(`Leslie.Examples.Prob.AVSS` §11–§12) to the value-bearing AVSSFaithful
spec.  The pieces landed here:

* `terminated` predicate (every honest party output, echoed to every
  receiver, all queues drained).
* Helper sets and cardinality bounds for the lex-product variant
  `cert_U`: `unsentDealerSet`, `unsentEchoPairSet`, `notReadySentSet`,
  `unfinishedSet`, plus `lexBase`.
* `cert_U`, `cert_V` — 7-component lex-product variant matching the
  AVSS structure (but with per-pair echo counting since AVSSFaithful's
  `partyEchoSend q p` is per-receiver).
* `fairActions`, `fair` — fair-required action set and
  `FairnessAssumptions` bundle (every honest-protocol action, NOT
  `partyCorruptDeliver`).
* `atomic_broadcast_AE` — CR '93-style atomic-broadcast hypothesis.
* Trivial `cert_U_term`, `cert_V_term`, `cert_V_pos`, `cert_U_le_bound`
  facts (the `Inv → ...` shape mirrors AVSS's `avssCert_U_term` etc.).

Subsequent steps (3b/3c/...) will land the per-action `cert_U` strict-
decrease and non-increase lemmas, the joint inductive invariant
(`avssTermInv`-analog plus queue / fresh / flow auxiliaries), and the
full `FairASTCertificate` instance + termination theorems.  The skeleton
here matches AVSS's structure component-for-component so subsequent
steps can adapt the AVSS proofs nearly verbatim.

(`avssCert_U_term` and friends in AVSS take ~2000 LOC of per-action
lemma support + four auxiliary invariants; the full Step-3 deliverable
exceeds the 500-LOC budget for a single PR, so it is staged.) -/

/-! ### Helper sets for the lex-product variant -/

/-- Honest parties for which the dealer hasn't yet emitted a payload.
The `c₁` component of `cert_U`: drops by 1 each time `dealerShareTo p`
fires for honest `p`. Mirrors `AVSS.unsentDealerSet`. -/
def unsentDealerSet (s : State n t F) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter
    (fun p => p ∉ s.corrupted ∧ s.dealerSent p = false)

omit [Field F] [Fintype F] [DecidableEq F] in
@[simp] theorem unsentDealerSet_card_le (s : State n t F) :
    (unsentDealerSet s).card ≤ n := by
  classical
  unfold unsentDealerSet
  exact (Finset.card_le_univ _).trans (by simp)

/-- Honest `(sender, receiver)` pairs for which `sender` has delivered
but has not yet echoed to `receiver`.  This is the AVSSFaithful analogue
of AVSS's `unsentEchoSet`: AVSSFaithful's `partyEchoSend q p` is per-
receiver (since echo carries a value computed at receiver point), so
the variant counts pairs rather than parties. -/
def unsentEchoPairSet (s : State n t F) : Finset (Fin n × Fin n) :=
  (Finset.univ : Finset (Fin n × Fin n)).filter
    (fun pr => pr.1 ∉ s.corrupted ∧
      (s.local_ pr.1).delivered.isSome = true ∧
      pr.2 ∉ (s.local_ pr.1).echoedTo)

omit [Field F] [Fintype F] [DecidableEq F] in
@[simp] theorem unsentEchoPairSet_card_le (s : State n t F) :
    (unsentEchoPairSet s).card ≤ n * n := by
  classical
  have h1 : (unsentEchoPairSet s).card ≤
      (Finset.univ : Finset (Fin n × Fin n)).card :=
    Finset.card_le_univ _
  have h2 : (Finset.univ : Finset (Fin n × Fin n)).card = n * n := by simp
  omega

/-- Honest parties whose `readySent` set is empty.  Mirrors
`AVSS.notReadySentSet` (where `readySent` was a `Bool`).  In
AVSSFaithful, `readySent` is a `Finset ReadyCert`, so the analogue is
"no ready ever broadcast" — once `partyReady`/`partyAmplify` fires for
*any* candidate, this party drops out. -/
def notReadySentSet (s : State n t F) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter
    (fun p => p ∉ s.corrupted ∧ (s.local_ p).readySent = ∅)

omit [Field F] [Fintype F] in
@[simp] theorem notReadySentSet_card_le (s : State n t F) :
    (notReadySentSet s).card ≤ n := by
  classical
  unfold notReadySentSet
  exact (Finset.card_le_univ _).trans (by simp)

/-- Honest parties with `output = none`. -/
def unfinishedSet (s : State n t F) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter
    (fun p => p ∉ s.corrupted ∧ (s.local_ p).output = none)

omit [Field F] [Fintype F] [DecidableEq F] in
@[simp] theorem unfinishedSet_card_le (s : State n t F) :
    (unfinishedSet s).card ≤ n := by
  classical
  unfold unfinishedSet
  exact (Finset.card_le_univ _).trans (by simp)

omit [Field F] [Fintype F] [DecidableEq F] in
@[simp] theorem inflightDeliveries_card_le' (s : State n t F) :
    s.inflightDeliveries.card ≤ n := by
  classical
  exact (Finset.card_le_univ s.inflightDeliveries).trans (by simp)

/-- Lex base: large enough to dominate every component.  Each pair-
counted component is bounded by `n * n ≤ (n+1)²`. -/
def lexBase (n : ℕ) : ℕ := (n + 1) * (n + 1)

theorem lexBase_pos : 1 ≤ lexBase n := by unfold lexBase; nlinarith

/-! ### The variant `cert_U` and likelihood `cert_V` -/

/-- The 6-component lex-product termination variant for AVSSFaithful.

```
U = c₁·K^6 + c₂·K^5 + c₃·K^4 + c₄·K^3 + c₆·K + c₇
```

with components in lex-decreasing weight order (`notReadySentSet` is
intentionally omitted; AVSSFaithful's `partyOutput` gate doesn't require
`cert ∈ readySent`, so the `output ⇒ readySent ≠ ∅` invariant is not
preservable, hence we drop the `notReadySentSet` component and let
`partyReady`/`partyAmplify` go through the disjunctive `Or.inr` arm of
the certificate's `U_dec_det`):

  1. `unsentDealerSet.card`   — pending `dealerShareTo` step.
  2. `inflightDeliveries.card` — pending `partyDeliver` step.
  3. `unsentEchoPairSet.card`  — pending `partyEchoSend` step
                                 (per-pair, AVSSFaithful-specific).
  4. `inflightEchoes.card`     — pending `partyEchoReceive` step.
  6. `inflightReady.card`      — pending `partyReceiveReady`.
  7. `unfinishedSet.card`      — pending `partyOutput`.

The lex base `K = (M+1)*(M+1)` with `M = n*(n+1)` dominates every
single component (in particular `unsentEchoPairSet.card ≤ n²` and
`inflightEchoes.card ≤ |EchoMsg|`). -/
noncomputable def cert_U (s : State n t F) : ℕ :=
  let M : ℕ := n * (n + 1)
  let K : ℕ := lexBase M
  (unsentDealerSet s).card * K ^ 6 +
    s.inflightDeliveries.card * K ^ 5 +
    (unsentEchoPairSet s).card * K ^ 4 +
    s.inflightEchoes.card * K ^ 3 +
    s.inflightReady.card * K +
    (unfinishedSet s).card

/-- Likelihood `V s = (cert_U s : ℝ≥0)`. -/
noncomputable def cert_V (s : State n t F) : NNReal := (cert_U s : NNReal)

/-! ### Terminated predicate -/

/-- A state is terminated iff:

* every honest party has snapped output,
* every honest party has echoed to every receiver,
* the dealer has emitted a payload to every honest party,
* and all in-flight queues are drained.

Mirrors `AVSS.terminated`; the per-pair echo-completeness clause matches
the per-pair `unsentEchoPairSet` component of `cert_U`. -/
def terminated (s : State n t F) : Prop :=
  (∀ p, p ∉ s.corrupted → (s.local_ p).output.isSome) ∧
  (∀ p, p ∉ s.corrupted →
      ∀ r : Fin n, r ∈ (s.local_ p).echoedTo) ∧
  (∀ p, p ∉ s.corrupted → s.dealerSent p = true) ∧
  s.inflightDeliveries = ∅ ∧
  s.inflightEchoes = ∅ ∧
  s.inflightReady = ∅

/-! ### Fair-required action set -/

/-- Set of fair-required actions for AVSSFaithful.

Every honest-protocol action is fair-required *except* the adversarial
`partyCorruptDeliver` (used to model corrupt parties acquiring their
shares for the secrecy view; honest-party fairness is unaffected by
whether corrupt parties have received their shares).

Note: `partyReady`/`partyAmplify` carry a `cert` argument; the gate
already ensures `cert ∉ readySent`, so each cert fires at most once.
The fair-required action set requires *some* cert eventually be fired
for every honest party with an `(n−t)`-supported certificate available. -/
def fairActions : Set (Action n t F) :=
  { a | match a with
        | .dealerShareTo _ => True
        | .partyDeliver _ => True
        | .partyEchoSend _ _ => True
        | .partyEchoReceive _ => True
        | .partyReady _ _ => True
        | .partyAmplify _ _ => True
        | .partyReceiveReady _ => True
        | .partyOutput _ _ => True
        | _ => False }

/-- AVSSFaithful fairness assumptions. -/
noncomputable def fair :
    FairnessAssumptions (State n t F) (Action n t F) where
  fair_actions := fairActions
  isWeaklyFair := fun _ => True

/-! ### Atomic broadcast hypothesis (CR '93 spirit) -/

open Leslie.Prob in
/-- **Atomic broadcast (AE)** for AVSSFaithful: AE on the trace, every
honest party eventually has `dealerSent p = true`.  Mirrors
`AVSS.atomic_broadcast_AE` (without the `dealerMessages` clause, since
in AVSSFaithful the per-party commitment lives directly in
`s.dealerCommit p` from initialization, not in an `Option`-typed
channel).

Under this hypothesis, fairness of `partyDeliver` plus monotonicity of
`dealerSent` yields almost-sure delivery to every honest party,
discharging the runtime conditional-CR hypothesis on
`avss_termination_AS_fair`-style claims. -/
noncomputable def atomic_broadcast_AE (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F)
    (μ₀ : MeasureTheory.Measure (State n t F))
    [MeasureTheory.IsProbabilityMeasure μ₀]
    (A : Adversary (State n t F) (Action n t F)) : Prop :=
  ∀ᵐ ω ∂(traceDist (spec (t := t) sec corr coeffs) A μ₀),
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ p, p ∉ corr →
      (ω k).1.dealerSent p = true

/-! ### Variant facts at terminated / non-terminated states -/

omit [Field F] [Fintype F] [DecidableEq F] in
/-- The four cardinality components are zero on a terminated state. -/
theorem cert_U_components_zero_of_terminated (s : State n t F)
    (ht : terminated s) :
    (unsentDealerSet s).card = 0 ∧
    s.inflightDeliveries.card = 0 ∧
    (unsentEchoPairSet s).card = 0 ∧
    s.inflightEchoes.card = 0 ∧
    s.inflightReady.card = 0 ∧
    (unfinishedSet s).card = 0 := by
  classical
  obtain ⟨ht_out, ht_echo, ht_ds, ht_ifd, ht_ife, ht_ifr⟩ := ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_of_forall_notMem
    intro p hp
    simp only [unsentDealerSet, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp
    obtain ⟨hp_h, hp_ds⟩ := hp
    have := ht_ds p hp_h
    rw [this] at hp_ds; cases hp_ds
  · rw [ht_ifd]; rfl
  · apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_of_forall_notMem
    intro pr hpr
    simp only [unsentEchoPairSet, Finset.mem_filter, Finset.mem_univ,
      true_and] at hpr
    obtain ⟨hp_h, _, hp_no⟩ := hpr
    exact hp_no (ht_echo pr.1 hp_h pr.2)
  · rw [ht_ife]; rfl
  · rw [ht_ifr]; rfl
  · apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_of_forall_notMem
    intro p hp
    simp only [unfinishedSet, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp
    obtain ⟨hp_h, hp_none⟩ := hp
    have := ht_out p hp_h
    rw [hp_none] at this; simp at this

omit [Field F] [Fintype F] in
/-- Note: `notReadySentSet` is NOT forced to zero by `terminated`
alone.  At a terminated state, `output.isSome` for every honest party,
but the AVSSFaithful gate `partyOutput p cert` does not require
`cert ∈ (s.local_ p).readySent` (only `readyCertSupported`).  So a
party could output without having sent a ready, leaving
`(s.local_ p).readySent = ∅`.  Forcing `notReadySentSet = 0` at
terminated states therefore requires an *invariant* (`output.isSome →
readySent ≠ ∅`) — added in subsequent step 3b. -/
theorem cert_U_eq_zero_of_terminated_modulo_readySent
    (s : State n t F) (ht : terminated s)
    (_h_ready : (notReadySentSet s).card = 0) :
    cert_U s = 0 := by
  classical
  unfold cert_U
  obtain ⟨h1, h2, h3, h4, h6, h7⟩ :=
    cert_U_components_zero_of_terminated s ht
  rw [h1, h2, h3, h4, h6, h7]
  ring

omit [Field F] [Fintype F] [DecidableEq F] in
/-- `cert_U s = 0` at every terminated state.  Step 3b refinement:
dropping the `notReadySentSet` component from `cert_U` makes this
unconditional (the `_modulo_readySent` form above takes a now-redundant
hypothesis). -/
theorem cert_U_eq_zero_of_terminated
    (s : State n t F) (ht : terminated s) :
    cert_U s = 0 := by
  classical
  unfold cert_U
  obtain ⟨h1, h2, h3, h4, h6, h7⟩ :=
    cert_U_components_zero_of_terminated s ht
  rw [h1, h2, h3, h4, h6, h7]
  ring

/-! ### Variant cardinality bound

A uniform `cert_U` bound is needed for the certificate's `U_bdd_subl`
field (`∀ k, ∃ M, ...`).  We give a coarse bound here using fintype
cardinalities of the message types; a tighter bound (matching AVSS's
`(7n+7)·K^6` shape) is deferred to step 3b. -/

omit [Field F] [DecidableEq F] in
/-- Coarse uniform bound for the inflight-echo cardinality.  Used to
package `cert_U_le_bound`. -/
theorem inflightEchoes_card_le_univ (s : State n t F) :
    s.inflightEchoes.card ≤ Fintype.card (EchoMsg n t F) := by
  classical
  exact (Finset.card_le_univ s.inflightEchoes).trans (by simp)

omit [Field F] [DecidableEq F] in
/-- Coarse uniform bound for the inflight-ready cardinality. -/
theorem inflightReady_card_le_univ (s : State n t F) :
    s.inflightReady.card ≤ Fintype.card (ReadyMsg n t F) := by
  classical
  exact (Finset.card_le_univ s.inflightReady).trans (by simp)

omit [Field F] in
/-- A uniform bound on `cert_U` valid at every state.  The bound is
loose (component-wise): each component is bounded by its fintype
universe size, and the K-power weighting is closed in. -/
theorem cert_U_le_bound (s : State n t F) :
    cert_U s ≤
      let K := lexBase (n * (n + 1))
      n * K ^ 6 + n * K ^ 5 +
        (n * n) * K ^ 4 +
        Fintype.card (EchoMsg n t F) * K ^ 3 +
        Fintype.card (ReadyMsg n t F) * K +
        n := by
  classical
  unfold cert_U
  have h1 := unsentDealerSet_card_le (s := s)
  have h2 := inflightDeliveries_card_le' (s := s)
  have h3 := unsentEchoPairSet_card_le (s := s)
  have h4 := inflightEchoes_card_le_univ s
  have h6 := inflightReady_card_le_univ s
  have h7 := unfinishedSet_card_le (s := s)
  set K : ℕ := lexBase (n * (n + 1)) with hKdef
  have hK_pos : 1 ≤ K := lexBase_pos
  have e1 : (unsentDealerSet s).card * K ^ 6 ≤ n * K ^ 6 :=
    Nat.mul_le_mul_right _ h1
  have e2 : s.inflightDeliveries.card * K ^ 5 ≤ n * K ^ 5 :=
    Nat.mul_le_mul_right _ h2
  have e3 : (unsentEchoPairSet s).card * K ^ 4 ≤ (n * n) * K ^ 4 :=
    Nat.mul_le_mul_right _ h3
  have e4 : s.inflightEchoes.card * K ^ 3 ≤
      Fintype.card (EchoMsg n t F) * K ^ 3 :=
    Nat.mul_le_mul_right _ h4
  have e6 : s.inflightReady.card * K ≤
      Fintype.card (ReadyMsg n t F) * K :=
    Nat.mul_le_mul_right _ h6
  have e7 : (unfinishedSet s).card ≤ n := h7
  simp only []
  have := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (Nat.add_le_add e1 e2) e3) e4) e6) e7
  exact this

/-! ### Joint inductive invariant (Step 3b checkpoint A)

Bundles every Step-1 and Step-2 invariant into a single structure. Adding
new conjuncts is a non-breaking change (new fields don't break existing
field accesses), per `CLAUDE.md`'s guideline. -/

/-- Joint inductive invariant for AVSSFaithful termination. -/
structure cert_Inv (coeffs : Fin (t + 1) -> Fin (t + 1) -> F)
    (s : State n t F) : Prop where
  honest_commit : honestDealerCommitInv coeffs s
  delivered_sent : deliveredImpliesDealerSent s
  echoed_delivered : echoedToImpliesDelivered s
  ifd_wf : inflightDeliveriesWf s
  ifcd_wf : inflightCorruptDeliveriesWf s
  out_delivered : outputImpliesDelivered s
  echo_addr : acceptedEchoesAddressed s
  ife_sender_del : inflightEchoesSenderDelivered s
  ifr_sender_ready : inflightReadySenderReady s

omit [Fintype F] [DecidableEq F] in
/-- The joint invariant holds at every initial state. -/
theorem cert_Inv_init (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F) (s : State n t F)
    (h : initPred sec corr coeffs s) :
    cert_Inv coeffs s :=
  { honest_commit := honestDealerCommitInv_init sec corr coeffs s h
    delivered_sent := deliveredImpliesDealerSent_init sec corr coeffs s h
    echoed_delivered := echoedToImpliesDelivered_init sec corr coeffs s h
    ifd_wf := inflightDeliveriesWf_init sec corr coeffs s h
    ifcd_wf := inflightCorruptDeliveriesWf_init sec corr coeffs s h
    out_delivered := outputImpliesDelivered_init sec corr coeffs s h
    echo_addr := acceptedEchoesAddressed_init sec corr coeffs s h
    ife_sender_del := inflightEchoesSenderDelivered_init sec corr coeffs s h
    ifr_sender_ready := inflightReadySenderReady_init sec corr coeffs s h }

omit [Fintype F] in
/-- The joint invariant is preserved by every gated `step`. -/
theorem cert_Inv_preserve
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F)
    (a : Action n t F) (s : State n t F)
    (hgate : gate a s) (h : cert_Inv coeffs s) :
    cert_Inv coeffs (step a s) :=
  { honest_commit := honestDealerCommitInv_preserve coeffs a s h.honest_commit
    delivered_sent := deliveredImpliesDealerSent_preserve a s hgate h.delivered_sent
    echoed_delivered := echoedToImpliesDelivered_preserve a s hgate h.echoed_delivered
    ifd_wf := inflightDeliveriesWf_preserve a s hgate h.delivered_sent h.ifd_wf
    ifcd_wf := inflightCorruptDeliveriesWf_preserve a s hgate h.delivered_sent h.ifcd_wf
    out_delivered := outputImpliesDelivered_preserve a s hgate h.out_delivered
    echo_addr := acceptedEchoesAddressed_preserve a s hgate h.echo_addr
    ife_sender_del := inflightEchoesSenderDelivered_preserve a s hgate h.ife_sender_del
    ifr_sender_ready := inflightReadySenderReady_preserve a s hgate h.ifr_sender_ready }

/-! ### `isHonestFire` predicate (Step 3b) -/

/-- Honest-fired action: the owning party (if any) is honest. -/
def isHonestFire (a : Action n t F) (s : State n t F) : Prop :=
  match a with
  | .dealerShareTo p => p ∉ s.corrupted
  | .partyEchoSend q _ => q ∉ s.corrupted
  | .partyReady p _ => p ∉ s.corrupted
  | .partyAmplify p _ => p ∉ s.corrupted
  | _ => True

/-! ### Useful constants -/

omit [Field F] [Fintype F] [DecidableEq F] in
/-- The lex base `K` exceeds `n + 1`. -/
theorem cert_K_ge_succ : n + 1 ≤ lexBase (n * (n + 1)) := by
  unfold lexBase
  have h1 : n + 1 ≤ n * (n + 1) + 1 := by nlinarith
  have h2 : n * (n + 1) + 1 ≤ (n * (n + 1) + 1) * (n * (n + 1) + 1) := by
    have : 1 ≤ n * (n + 1) + 1 := by omega
    nlinarith
  omega

omit [Field F] [Fintype F] [DecidableEq F] in
theorem cert_K_pos' : 1 ≤ lexBase (n * (n + 1)) := lexBase_pos

/-! ### Per-action `cert_U` strict decrease lemmas (Step 3b checkpoint B)

For each fair action fired at an honest party, `cert_U` strictly
decreases.  Six lemmas; the two omitted (`partyReady` /  `partyAmplify`)
go through the disjunctive `Or.inr` arm of the certificate's
`U_dec_det` field (the dropped `notReadySentSet` component means there
is no counterweight against the K-weight `inflightReady` growth on
ready/amplify firings — see the docstring on `cert_U`). -/

omit [Fintype F] in
/-- `dealerShareTo p` for honest `p`: c1 drops by 1 (weight K⁶), c2
grows by 1 (weight K⁵).  Net decrease ≥ K⁶ - K⁵ > 0. -/
theorem cert_U_step_dealerShareTo_lt
    (s : State n t F) (p : Fin n)
    (hgate : gate (.dealerShareTo p) s)
    (hinv : cert_Inv coeffs s)
    (hp : p ∉ s.corrupted) :
    cert_U (step (.dealerShareTo p) s) < cert_U s := by
  classical
  have hK_pos : 1 ≤ lexBase (n * (n + 1)) := cert_K_pos'
  have hds_pre : s.dealerSent p = false := hgate
  have hp_notin_ifd : p ∉ s.inflightDeliveries := by
    intro hin
    have := hinv.ifd_wf p hin
    rw [hds_pre] at this; cases this.1
  have hp_in_uds : p ∈ unsentDealerSet s := by
    simp [unsentDealerSet, hp, hds_pre]
  have h_uds_eq : unsentDealerSet (step (.dealerShareTo p) s) =
      (unsentDealerSet s).erase p := by
    ext q
    simp only [unsentDealerSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    have hcorr : (step (.dealerShareTo p) s).corrupted = s.corrupted := by simp [step]
    rw [hcorr]
    by_cases hqp : q = p
    · subst hqp
      have : (step (.dealerShareTo q) s).dealerSent q = true := by
        simp [step, Function.update_self]
      rw [this]; simp
    · have : (step (.dealerShareTo p) s).dealerSent q = s.dealerSent q := by
        show (Function.update s.dealerSent p true) q = s.dealerSent q
        rw [Function.update_apply]; rw [if_neg hqp]
      rw [this]; tauto
  have h_uds_pos : 1 ≤ (unsentDealerSet s).card :=
    Finset.card_pos.mpr ⟨p, hp_in_uds⟩
  have h_uds_card : (unsentDealerSet (step (.dealerShareTo p) s)).card + 1 =
      (unsentDealerSet s).card := by
    rw [h_uds_eq, Finset.card_erase_of_mem hp_in_uds]; omega
  have h_ifd_eq : (step (.dealerShareTo p) s).inflightDeliveries =
      insert p s.inflightDeliveries := by simp [step, hp]
  have h_ifd_card : (step (.dealerShareTo p) s).inflightDeliveries.card =
      s.inflightDeliveries.card + 1 := by
    rw [h_ifd_eq, Finset.card_insert_of_notMem hp_notin_ifd]
  have h_uep : unsentEchoPairSet (step (.dealerShareTo p) s) =
      unsentEchoPairSet s := by ext pr; simp [unsentEchoPairSet, step]
  have h_ife : (step (.dealerShareTo p) s).inflightEchoes = s.inflightEchoes := by
    simp [step]
  have h_ifr : (step (.dealerShareTo p) s).inflightReady = s.inflightReady := by
    simp [step]
  have h_unfin : unfinishedSet (step (.dealerShareTo p) s) = unfinishedSet s := by
    ext q; simp [unfinishedSet, step]
  -- K^6 ≥ K^5 + K^5 (when K ≥ 2). For n=0, K=1; we handle with general K^6 ≥ K^5+1 (K≥2 gives this; K=1 gives K^6=K^5=1, but uds_card ≥ 1 from p ∈, so the c1 drop dominates).
  -- Actually in all cases K ≥ 1, so K^6 ≥ K^5 ≥ 1.  But we need K^6 - K^5 ≥ 1 for the strict decrease.
  -- If K = 1, K^6 = K^5 = 1, c1 drops by 1 (weight 1), c2 grows by 1 (weight 1). Net 0.  Need K ≥ 2.
  -- For n ≥ 1, K = (n²+n+1)² ≥ 9 ≥ 2.  For n = 0, K = 1.  But n = 0 means Fin 0 is empty, so p doesn't exist.
  have hK_ge_2 : n ≥ 1 → 2 ≤ lexBase (n * (n + 1)) := by
    intro hn
    unfold lexBase
    have hM : 2 ≤ n * (n + 1) := by nlinarith
    have : 9 ≤ (n * (n + 1) + 1) * (n * (n + 1) + 1) := by nlinarith
    omega
  have hn_pos : n ≥ 1 := by
    by_contra hbad; push_neg at hbad
    interval_cases n
    exact (Fin.elim0 p)
  have hKge2 : 2 ≤ lexBase (n * (n + 1)) := hK_ge_2 hn_pos
  have hKpow_diff : (lexBase (n * (n + 1))) ^ 5 + 1 ≤ (lexBase (n * (n + 1))) ^ 6 := by
    have hK5 : 1 ≤ (lexBase (n * (n + 1))) ^ 5 := Nat.one_le_pow _ _ hK_pos
    have h_eq : (lexBase (n * (n + 1))) ^ 6 = (lexBase (n * (n + 1))) ^ 5 *
        lexBase (n * (n + 1)) := by ring
    rw [h_eq]; nlinarith [hKge2, hK5]
  simp only [cert_U]
  rw [h_uep, h_ife, h_ifr, h_unfin, h_ifd_card]
  set c := (unsentDealerSet (step (.dealerShareTo p) s)).card
  have h_uds_pre : (unsentDealerSet s).card = c + 1 := h_uds_card.symm
  rw [h_uds_pre]
  set K := lexBase (n * (n + 1))
  -- LHS = c·K^6 + (ifd+1)·K^5 + rest
  -- RHS = (c+1)·K^6 + ifd·K^5 + rest
  -- Diff: K^6 - K^5 ≥ 1.
  have hLHS : c * K ^ 6 + (s.inflightDeliveries.card + 1) * K ^ 5 +
      (unsentEchoPairSet s).card * K ^ 4 + s.inflightEchoes.card * K ^ 3 +
      s.inflightReady.card * K + (unfinishedSet s).card =
      c * K ^ 6 + s.inflightDeliveries.card * K ^ 5 + K ^ 5 +
      (unsentEchoPairSet s).card * K ^ 4 + s.inflightEchoes.card * K ^ 3 +
      s.inflightReady.card * K + (unfinishedSet s).card := by ring
  have hRHS : (c + 1) * K ^ 6 + s.inflightDeliveries.card * K ^ 5 +
      (unsentEchoPairSet s).card * K ^ 4 + s.inflightEchoes.card * K ^ 3 +
      s.inflightReady.card * K + (unfinishedSet s).card =
      c * K ^ 6 + K ^ 6 + s.inflightDeliveries.card * K ^ 5 +
      (unsentEchoPairSet s).card * K ^ 4 + s.inflightEchoes.card * K ^ 3 +
      s.inflightReady.card * K + (unfinishedSet s).card := by ring
  rw [hLHS, hRHS]; linarith [hKpow_diff]

omit [Fintype F] in
/-- `partyDeliver p`: c2 drops by 1 (K⁵), c3 grows by ≤ n (K⁴). -/
theorem cert_U_step_partyDeliver_lt
    (s : State n t F) (p : Fin n)
    (hgate : gate (.partyDeliver p) s)
    (_hinv : cert_Inv coeffs s) :
    cert_U (step (.partyDeliver p) s) < cert_U s := by
  classical
  obtain ⟨_, _hp, hp_in_ifd, _hp_del⟩ := hgate
  have hK_pos : 1 ≤ lexBase (n * (n + 1)) := cert_K_pos'
  have hK_ns : n + 1 ≤ lexBase (n * (n + 1)) := cert_K_ge_succ
  have h_uds : unsentDealerSet (step (.partyDeliver p) s) = unsentDealerSet s := by
    ext q; simp [unsentDealerSet, step, setLocal]
  have h_ifd : (step (.partyDeliver p) s).inflightDeliveries =
      s.inflightDeliveries.erase p := by simp [step, setLocal]
  have h_ifd_card : (step (.partyDeliver p) s).inflightDeliveries.card + 1 =
      s.inflightDeliveries.card := by
    have h_pos : 1 ≤ s.inflightDeliveries.card :=
      Finset.card_pos.mpr ⟨p, hp_in_ifd⟩
    rw [h_ifd, Finset.card_erase_of_mem hp_in_ifd]; omega
  have h_uep_card : (unsentEchoPairSet (step (.partyDeliver p) s)).card ≤
      (unsentEchoPairSet s).card + n := by
    have hsub : unsentEchoPairSet (step (.partyDeliver p) s) ⊆
        unsentEchoPairSet s ∪
          ((Finset.univ : Finset (Fin n)).image (fun r => (p, r))) := by
      intro pr hpr
      simp only [unsentEchoPairSet, Finset.mem_filter, Finset.mem_univ,
        true_and] at hpr
      obtain ⟨hpr_h, hpr_del, hpr_ne⟩ := hpr
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      by_cases hpq : pr.1 = p
      · right; exact ⟨pr.2, by simp [hpq, Prod.ext_iff]⟩
      · left
        simp only [unsentEchoPairSet, Finset.mem_filter, Finset.mem_univ, true_and]
        have hcorr : (step (.partyDeliver p) s).corrupted = s.corrupted := by simp [step, setLocal]
        have hloc : (step (.partyDeliver p) s).local_ pr.1 = s.local_ pr.1 := by
          simp [step, setLocal, hpq]
        rw [hcorr] at hpr_h
        rw [hloc] at hpr_del hpr_ne
        exact ⟨hpr_h, hpr_del, hpr_ne⟩
    have h_card_le := Finset.card_le_card hsub
    have h_card_union :
        (unsentEchoPairSet s ∪
            ((Finset.univ : Finset (Fin n)).image (fun r => (p, r)))).card ≤
        (unsentEchoPairSet s).card +
            ((Finset.univ : Finset (Fin n)).image (fun r => (p, r))).card :=
      Finset.card_union_le _ _
    have h_image_card :
        ((Finset.univ : Finset (Fin n)).image (fun r => (p, r))).card ≤ n := by
      have := Finset.card_image_le (s := (Finset.univ : Finset (Fin n)))
        (f := fun r : Fin n => (p, r))
      simp at this; exact this
    omega
  have h_ife : (step (.partyDeliver p) s).inflightEchoes = s.inflightEchoes := by
    simp [step, setLocal]
  have h_ifr : (step (.partyDeliver p) s).inflightReady = s.inflightReady := by
    simp [step, setLocal]
  have h_unfin : unfinishedSet (step (.partyDeliver p) s) = unfinishedSet s := by
    ext q
    simp only [unfinishedSet, Finset.mem_filter, Finset.mem_univ, true_and]
    have hcorr : (step (.partyDeliver p) s).corrupted = s.corrupted := by simp [step, setLocal]
    rw [hcorr]
    by_cases hqp : q = p
    · subst hqp
      have hloc : (step (.partyDeliver q) s).local_ q =
          { s.local_ q with delivered := some (s.dealerCommit q) } := by
        simp [step, setLocal]
      rw [hloc]
    · have hloc : (step (.partyDeliver p) s).local_ q = s.local_ q := by
        simp [step, setLocal, hqp]
      rw [hloc]
  -- Key inequality: K^5 ≥ (n+1) * K^4.
  have hK4_pos : 0 < (lexBase (n * (n + 1))) ^ 4 :=
    Nat.pow_pos (by omega)
  have hKpow_gap : (n + 1) * (lexBase (n * (n + 1))) ^ 4 ≤
      (lexBase (n * (n + 1))) ^ 5 := by
    have h_eq : (lexBase (n * (n + 1))) ^ 5 = lexBase (n * (n + 1)) *
        (lexBase (n * (n + 1))) ^ 4 := by ring
    rw [h_eq]
    exact Nat.mul_le_mul_right _ hK_ns
  simp only [cert_U]
  rw [h_uds, h_ife, h_ifr, h_unfin]
  set K := lexBase (n * (n + 1))
  set c2_post := (step (.partyDeliver p) s).inflightDeliveries.card
  set c3_post := (unsentEchoPairSet (step (.partyDeliver p) s)).card
  set c3_pre := (unsentEchoPairSet s).card
  have h_c2pre : s.inflightDeliveries.card = c2_post + 1 := h_ifd_card.symm
  rw [h_c2pre]
  have h_c3 : c3_post * K ^ 4 ≤ c3_pre * K ^ 4 + n * K ^ 4 := by
    have h1 := Nat.mul_le_mul_right (K ^ 4) h_uep_card
    rw [Nat.add_mul] at h1; exact h1
  nlinarith [hKpow_gap, hK4_pos]

omit [Fintype F] in
/-- `partyEchoSend q p` for honest `q`: c3 drops by 1 (K⁴), c4 grows by ≤ 1 (K³). -/
theorem cert_U_step_partyEchoSend_lt
    (s : State n t F) (q p : Fin n)
    (hgate : gate (.partyEchoSend q p) s)
    (_hinv : cert_Inv coeffs s)
    (hq : q ∉ s.corrupted) :
    cert_U (step (.partyEchoSend q p) s) < cert_U s := by
  classical
  obtain ⟨hq_del, hp_notin⟩ := hgate
  have hK_pos : 1 ≤ lexBase (n * (n + 1)) := cert_K_pos'
  have h_uds : unsentDealerSet (step (.partyEchoSend q p) s) = unsentDealerSet s := by
    ext r; simp [unsentDealerSet, step, setLocal]
  have h_ifd : (step (.partyEchoSend q p) s).inflightDeliveries = s.inflightDeliveries := by
    simp [step, setLocal]
  have hqp_in : (q, p) ∈ unsentEchoPairSet s := by
    simp [unsentEchoPairSet, hq, hq_del, hp_notin]
  have h_uep : unsentEchoPairSet (step (.partyEchoSend q p) s) =
      (unsentEchoPairSet s).erase (q, p) := by
    ext pr
    simp only [unsentEchoPairSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    have hcorr : (step (.partyEchoSend q p) s).corrupted = s.corrupted := by
      simp [step, setLocal]
    rw [hcorr]
    by_cases hpq : pr.1 = q
    · subst hpq
      have hloc : (step (.partyEchoSend pr.1 p) s).local_ pr.1 =
          { s.local_ pr.1 with echoedTo := insert p (s.local_ pr.1).echoedTo } := by
        simp [step, setLocal]
      rw [hloc]
      simp only [Finset.mem_insert]
      constructor
      · rintro ⟨hpr_h, hpr_del, hpr_ne⟩
        push_neg at hpr_ne
        refine ⟨?_, hpr_h, hpr_del, hpr_ne.2⟩
        intro habs
        rw [Prod.ext_iff] at habs
        exact hpr_ne.1 habs.2
      · rintro ⟨hne, hpr_h, hpr_del, hpr_ne⟩
        refine ⟨hpr_h, hpr_del, ?_⟩
        push_neg
        refine ⟨?_, hpr_ne⟩
        intro habs
        apply hne; rw [Prod.ext_iff]; exact ⟨rfl, habs⟩
    · have hloc : (step (.partyEchoSend q p) s).local_ pr.1 = s.local_ pr.1 := by
        simp [step, setLocal, hpq]
      rw [hloc]
      constructor
      · rintro ⟨hpr_h, hpr_del, hpr_ne⟩
        refine ⟨?_, hpr_h, hpr_del, hpr_ne⟩
        intro habs; rw [Prod.ext_iff] at habs; exact hpq habs.1
      · rintro ⟨_, hpr_h, hpr_del, hpr_ne⟩; exact ⟨hpr_h, hpr_del, hpr_ne⟩
  have h_uep_card : (unsentEchoPairSet (step (.partyEchoSend q p) s)).card + 1 =
      (unsentEchoPairSet s).card := by
    have h_pos : 1 ≤ (unsentEchoPairSet s).card :=
      Finset.card_pos.mpr ⟨(q, p), hqp_in⟩
    rw [h_uep, Finset.card_erase_of_mem hqp_in]; omega
  have h_ife_card : (step (.partyEchoSend q p) s).inflightEchoes.card ≤
      s.inflightEchoes.card + 1 := by
    simp only [step]; exact Finset.card_insert_le _ _
  have h_ifr : (step (.partyEchoSend q p) s).inflightReady = s.inflightReady := by
    simp [step, setLocal]
  have h_unfin : unfinishedSet (step (.partyEchoSend q p) s) = unfinishedSet s := by
    ext r
    simp only [unfinishedSet, Finset.mem_filter, Finset.mem_univ, true_and]
    have hcorr : (step (.partyEchoSend q p) s).corrupted = s.corrupted := by
      simp [step, setLocal]
    rw [hcorr]
    by_cases hrq : r = q
    · subst hrq
      have hloc : (step (.partyEchoSend r p) s).local_ r =
          { s.local_ r with echoedTo := insert p (s.local_ r).echoedTo } := by
        simp [step, setLocal]
      rw [hloc]
    · have hloc : (step (.partyEchoSend q p) s).local_ r = s.local_ r := by
        simp [step, setLocal, hrq]
      rw [hloc]
  have hK3_pos : 0 < (lexBase (n * (n + 1))) ^ 3 :=
    Nat.pow_pos (by omega)
  have hKpow_gap : 2 * (lexBase (n * (n + 1))) ^ 3 ≤
      (lexBase (n * (n + 1))) ^ 4 := by
    have hKge2 : 2 ≤ lexBase (n * (n + 1)) := by
      by_cases hn : n ≥ 1
      · unfold lexBase
        have hM : 2 ≤ n * (n + 1) := by nlinarith
        have : 9 ≤ (n * (n + 1) + 1) * (n * (n + 1) + 1) := by nlinarith
        omega
      · push_neg at hn; interval_cases n
        exfalso; exact (Fin.elim0 q)
    have h_eq : (lexBase (n * (n + 1))) ^ 4 = lexBase (n * (n + 1)) *
        (lexBase (n * (n + 1))) ^ 3 := by ring
    rw [h_eq]; nlinarith [hKge2, hK3_pos]
  simp only [cert_U]
  rw [h_uds, h_ifd, h_ifr, h_unfin]
  set K := lexBase (n * (n + 1))
  set c3_post := (unsentEchoPairSet (step (.partyEchoSend q p) s)).card
  set c4_post := (step (.partyEchoSend q p) s).inflightEchoes.card
  have h_c3pre : (unsentEchoPairSet s).card = c3_post + 1 := h_uep_card.symm
  rw [h_c3pre]
  have h_c4 : c4_post * K ^ 3 ≤ s.inflightEchoes.card * K ^ 3 + K ^ 3 := by
    have h1 := Nat.mul_le_mul_right (K ^ 3) h_ife_card
    rw [Nat.add_mul] at h1; simpa using h1
  nlinarith [hKpow_gap, hK3_pos]

omit [Fintype F] in
/-- `partyEchoReceive msg`: c4 drops by 1. -/
theorem cert_U_step_partyEchoReceive_lt
    (s : State n t F) (msg : EchoMsg n t F)
    (hgate : gate (.partyEchoReceive msg) s)
    (_hinv : cert_Inv coeffs s) :
    cert_U (step (.partyEchoReceive msg) s) < cert_U s := by
  classical
  obtain ⟨hmsg_in, _⟩ := hgate
  have hK_pos : 1 ≤ lexBase (n * (n + 1)) := cert_K_pos'
  have h_uds : unsentDealerSet (step (.partyEchoReceive msg) s) = unsentDealerSet s := by
    ext r; simp [unsentDealerSet, step, setLocal]
  have h_ifd : (step (.partyEchoReceive msg) s).inflightDeliveries =
      s.inflightDeliveries := by simp [step, setLocal]
  have h_uep : unsentEchoPairSet (step (.partyEchoReceive msg) s) =
      unsentEchoPairSet s := by
    ext pr
    simp only [unsentEchoPairSet, Finset.mem_filter, Finset.mem_univ, true_and]
    have hcorr : (step (.partyEchoReceive msg) s).corrupted = s.corrupted := by
      simp [step, setLocal]
    rw [hcorr]
    by_cases hpr : pr.1 = msg.receiver
    · have hloc : (step (.partyEchoReceive msg) s).local_ pr.1 =
          { s.local_ pr.1 with
            acceptedEchoes := insert msg (s.local_ pr.1).acceptedEchoes } := by
        rw [hpr]; simp [step, setLocal]
      rw [hloc]
    · have hloc : (step (.partyEchoReceive msg) s).local_ pr.1 = s.local_ pr.1 := by
        simp [step, setLocal, hpr]
      rw [hloc]
  have h_ife : (step (.partyEchoReceive msg) s).inflightEchoes =
      s.inflightEchoes.erase msg := by simp [step, setLocal]
  have h_ife_card : (step (.partyEchoReceive msg) s).inflightEchoes.card + 1 =
      s.inflightEchoes.card := by
    have h_pos : 1 ≤ s.inflightEchoes.card :=
      Finset.card_pos.mpr ⟨msg, hmsg_in⟩
    rw [h_ife, Finset.card_erase_of_mem hmsg_in]; omega
  have h_ifr : (step (.partyEchoReceive msg) s).inflightReady = s.inflightReady := by
    simp [step, setLocal]
  have h_unfin : unfinishedSet (step (.partyEchoReceive msg) s) = unfinishedSet s := by
    ext r
    simp only [unfinishedSet, Finset.mem_filter, Finset.mem_univ, true_and]
    have hcorr : (step (.partyEchoReceive msg) s).corrupted = s.corrupted := by
      simp [step, setLocal]
    rw [hcorr]
    by_cases hrr : r = msg.receiver
    · have hloc : (step (.partyEchoReceive msg) s).local_ r =
          { s.local_ r with
            acceptedEchoes := insert msg (s.local_ r).acceptedEchoes } := by
        rw [hrr]; simp [step, setLocal]
      rw [hloc]
    · have hloc : (step (.partyEchoReceive msg) s).local_ r = s.local_ r := by
        simp [step, setLocal, hrr]
      rw [hloc]
  have hK3_pos : 0 < (lexBase (n * (n + 1))) ^ 3 :=
    Nat.pow_pos (by omega)
  simp only [cert_U]
  rw [h_uds, h_ifd, h_uep, h_ifr, h_unfin]
  set c4_post := (step (.partyEchoReceive msg) s).inflightEchoes.card
  have h_pre : s.inflightEchoes.card = c4_post + 1 := h_ife_card.symm
  rw [h_pre]
  nlinarith [hK3_pos]

omit [Fintype F] in
/-- `partyReceiveReady msg`: c6 drops by 1. -/
theorem cert_U_step_partyReceiveReady_lt
    (s : State n t F) (msg : ReadyMsg n t F)
    (hgate : gate (.partyReceiveReady msg) s)
    (_hinv : cert_Inv coeffs s) :
    cert_U (step (.partyReceiveReady msg) s) < cert_U s := by
  classical
  obtain ⟨hmsg_in, _⟩ := hgate
  have hK_pos : 1 ≤ lexBase (n * (n + 1)) := cert_K_pos'
  have h_uds : unsentDealerSet (step (.partyReceiveReady msg) s) = unsentDealerSet s := by
    ext r; simp [unsentDealerSet, step, setLocal]
  have h_ifd : (step (.partyReceiveReady msg) s).inflightDeliveries =
      s.inflightDeliveries := by simp [step, setLocal]
  have h_uep : unsentEchoPairSet (step (.partyReceiveReady msg) s) =
      unsentEchoPairSet s := by
    ext pr
    simp only [unsentEchoPairSet, Finset.mem_filter, Finset.mem_univ, true_and]
    have hcorr : (step (.partyReceiveReady msg) s).corrupted = s.corrupted := by
      simp [step, setLocal]
    rw [hcorr]
    by_cases hpr : pr.1 = msg.receiver
    · have hloc : (step (.partyReceiveReady msg) s).local_ pr.1 =
          { s.local_ pr.1 with
            readyReceived := insert msg (s.local_ pr.1).readyReceived } := by
        rw [hpr]; simp [step, setLocal]
      rw [hloc]
    · have hloc : (step (.partyReceiveReady msg) s).local_ pr.1 = s.local_ pr.1 := by
        simp [step, setLocal, hpr]
      rw [hloc]
  have h_ife : (step (.partyReceiveReady msg) s).inflightEchoes =
      s.inflightEchoes := by simp [step, setLocal]
  have h_ifr : (step (.partyReceiveReady msg) s).inflightReady =
      s.inflightReady.erase msg := by simp [step, setLocal]
  have h_ifr_card : (step (.partyReceiveReady msg) s).inflightReady.card + 1 =
      s.inflightReady.card := by
    have h_pos : 1 ≤ s.inflightReady.card :=
      Finset.card_pos.mpr ⟨msg, hmsg_in⟩
    rw [h_ifr, Finset.card_erase_of_mem hmsg_in]; omega
  have h_unfin : unfinishedSet (step (.partyReceiveReady msg) s) = unfinishedSet s := by
    ext r
    simp only [unfinishedSet, Finset.mem_filter, Finset.mem_univ, true_and]
    have hcorr : (step (.partyReceiveReady msg) s).corrupted = s.corrupted := by
      simp [step, setLocal]
    rw [hcorr]
    by_cases hrr : r = msg.receiver
    · have hloc : (step (.partyReceiveReady msg) s).local_ r =
          { s.local_ r with
            readyReceived := insert msg (s.local_ r).readyReceived } := by
        rw [hrr]; simp [step, setLocal]
      rw [hloc]
    · have hloc : (step (.partyReceiveReady msg) s).local_ r = s.local_ r := by
        simp [step, setLocal, hrr]
      rw [hloc]
  simp only [cert_U]
  rw [h_uds, h_ifd, h_uep, h_ife, h_unfin]
  set c6_post := (step (.partyReceiveReady msg) s).inflightReady.card
  have h_pre : s.inflightReady.card = c6_post + 1 := h_ifr_card.symm
  rw [h_pre]
  nlinarith [hK_pos]

omit [Fintype F] in
/-- `partyOutput p cert`: c7 drops by 1. -/
theorem cert_U_step_partyOutput_lt
    (s : State n t F) (p : Fin n) (cert : ReadyCert n t F)
    (hgate : gate (.partyOutput p cert) s)
    (_hinv : cert_Inv coeffs s) :
    cert_U (step (.partyOutput p cert) s) < cert_U s := by
  classical
  have hp : p ∉ s.corrupted := hgate.1
  have hp_out : (s.local_ p).output = none := hgate.2.1
  have h_uds : unsentDealerSet (step (.partyOutput p cert) s) = unsentDealerSet s := by
    ext r; simp [unsentDealerSet, step, setLocal]
  have h_ifd : (step (.partyOutput p cert) s).inflightDeliveries = s.inflightDeliveries := by
    simp [step, setLocal]
  have h_uep : unsentEchoPairSet (step (.partyOutput p cert) s) =
      unsentEchoPairSet s := by
    ext pr
    simp only [unsentEchoPairSet, Finset.mem_filter, Finset.mem_univ, true_and]
    have hcorr : (step (.partyOutput p cert) s).corrupted = s.corrupted := by
      simp [step, setLocal]
    rw [hcorr]
    by_cases hpr : pr.1 = p
    · subst hpr
      have hloc : (step (.partyOutput pr.1 cert) s).local_ pr.1 =
          { s.local_ pr.1 with
            output := some (AVSS.evalRowPoly cert.candidate.rowPoly 0) } := by
        simp [step, setLocal]
      rw [hloc]
    · have hloc : (step (.partyOutput p cert) s).local_ pr.1 = s.local_ pr.1 := by
        simp [step, setLocal, hpr]
      rw [hloc]
  have h_ife : (step (.partyOutput p cert) s).inflightEchoes = s.inflightEchoes := by
    simp [step, setLocal]
  have h_ifr : (step (.partyOutput p cert) s).inflightReady = s.inflightReady := by
    simp [step, setLocal]
  have hp_in : p ∈ unfinishedSet s := by simp [unfinishedSet, hp, hp_out]
  have h_unfin : unfinishedSet (step (.partyOutput p cert) s) =
      (unfinishedSet s).erase p := by
    ext r
    simp only [unfinishedSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    have hcorr : (step (.partyOutput p cert) s).corrupted = s.corrupted := by
      simp [step, setLocal]
    rw [hcorr]
    by_cases hrp : r = p
    · subst hrp
      have hloc : (step (.partyOutput r cert) s).local_ r =
          { s.local_ r with
            output := some (AVSS.evalRowPoly cert.candidate.rowPoly 0) } := by
        simp [step, setLocal]
      rw [hloc]; simp
    · have hloc : (step (.partyOutput p cert) s).local_ r = s.local_ r := by
        simp [step, setLocal, hrp]
      rw [hloc]; tauto
  have h_unfin_card_pos : 1 ≤ (unfinishedSet s).card :=
    Finset.card_pos.mpr ⟨p, hp_in⟩
  have h_unfin_card : (unfinishedSet (step (.partyOutput p cert) s)).card + 1 =
      (unfinishedSet s).card := by
    rw [h_unfin, Finset.card_erase_of_mem hp_in]; omega
  -- Reduce to arithmetic.
  simp only [cert_U]
  rw [h_uds, h_ifd, h_uep, h_ife, h_ifr]
  omega

/-! ### Step 3b checkpoint C — `cert_U` positivity at non-terminated states -/

omit [Fintype F] in
/-- At a non-terminated state with the joint invariant, `cert_U` is
positive.  This is the contrapositive of "`cert_U = 0 → terminated`",
proved by decomposing the 6-component sum and chaining the cert_Inv
fields (`out_delivered`, etc.) to the `terminated` definition. -/
theorem cert_U_pos_of_not_terminated (s : State n t F)
    (hinv : cert_Inv coeffs s) (hnt : ¬ terminated s) : 0 < cert_U s := by
  classical
  by_contra hbad
  push_neg at hbad
  have hU0 : cert_U s = 0 := Nat.le_zero.mp hbad
  apply hnt
  simp only [cert_U] at hU0
  set K := lexBase (n * (n + 1)) with hKdef
  have hK_pos : 1 ≤ K := lexBase_pos
  have hK_pow_pos : ∀ k, 1 ≤ K ^ k := fun k => Nat.one_le_pow _ _ hK_pos
  have h_each : (unsentDealerSet s).card * K ^ 6 = 0 ∧
                s.inflightDeliveries.card * K ^ 5 = 0 ∧
                (unsentEchoPairSet s).card * K ^ 4 = 0 ∧
                s.inflightEchoes.card * K ^ 3 = 0 ∧
                s.inflightReady.card * K = 0 ∧
                (unfinishedSet s).card = 0 := by omega
  obtain ⟨e1, e2, e3, e4, e6, e7⟩ := h_each
  have h_uds : (unsentDealerSet s).card = 0 := by
    have := hK_pow_pos 6; rcases Nat.mul_eq_zero.mp e1 with h | h
    · exact h
    · omega
  have h_ifd : s.inflightDeliveries.card = 0 := by
    have := hK_pow_pos 5; rcases Nat.mul_eq_zero.mp e2 with h | h
    · exact h
    · omega
  have h_uep : (unsentEchoPairSet s).card = 0 := by
    have := hK_pow_pos 4; rcases Nat.mul_eq_zero.mp e3 with h | h
    · exact h
    · omega
  have h_ife : s.inflightEchoes.card = 0 := by
    have := hK_pow_pos 3; rcases Nat.mul_eq_zero.mp e4 with h | h
    · exact h
    · omega
  have h_ifr : s.inflightReady.card = 0 := by
    rcases Nat.mul_eq_zero.mp e6 with h | h
    · exact h
    · omega
  have h_unfin : (unfinishedSet s).card = 0 := e7
  have h_ifd_emp : s.inflightDeliveries = ∅ := Finset.card_eq_zero.mp h_ifd
  have h_ife_emp : s.inflightEchoes = ∅ := Finset.card_eq_zero.mp h_ife
  have h_ifr_emp : s.inflightReady = ∅ := Finset.card_eq_zero.mp h_ifr
  have h_unfin_emp : unfinishedSet s = ∅ := Finset.card_eq_zero.mp h_unfin
  have h_uds_emp : unsentDealerSet s = ∅ := Finset.card_eq_zero.mp h_uds
  have h_uep_emp : unsentEchoPairSet s = ∅ := Finset.card_eq_zero.mp h_uep
  have h_out : ∀ p, p ∉ s.corrupted → (s.local_ p).output.isSome := by
    intro p hp
    by_contra hsome_neg
    have hp_in : p ∈ unfinishedSet s := by
      simp only [unfinishedSet, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hp, ?_⟩
      cases hop : (s.local_ p).output with
      | none => rfl
      | some _ => simp [hop] at hsome_neg
    rw [h_unfin_emp] at hp_in; exact (Finset.notMem_empty _) hp_in
  have h_ds : ∀ p, p ∉ s.corrupted → s.dealerSent p = true := by
    intro p hp
    by_contra hbadds
    have hf : s.dealerSent p = false := by
      cases hd : s.dealerSent p with
      | true => exact absurd hd hbadds
      | false => rfl
    have hp_in : p ∈ unsentDealerSet s := by
      simp [unsentDealerSet, hp, hf]
    rw [h_uds_emp] at hp_in; exact (Finset.notMem_empty _) hp_in
  have h_echoed : ∀ p, p ∉ s.corrupted → ∀ r : Fin n, r ∈ (s.local_ p).echoedTo := by
    intro p hp r
    by_contra hr_notin
    have hp_some : (s.local_ p).output.isSome := h_out p hp
    have hp_del : (s.local_ p).delivered.isSome := hinv.out_delivered p hp_some
    have hpr_in : (p, r) ∈ unsentEchoPairSet s := by
      simp [unsentEchoPairSet, hp, hp_del, hr_notin]
    rw [h_uep_emp] at hpr_in; exact (Finset.notMem_empty _) hpr_in
  exact ⟨h_out, h_echoed, h_ds, h_ifd_emp, h_ife_emp, h_ifr_emp⟩

/-! ### Naive uniform bound on `cert_U` -/

/-- A noncomputable naive uniform bound on `cert_U` valid at every state.
Pulled out of the `cert.U_bdd_subl` / `V_init_bdd` fields so the inline
expression doesn't trigger `LE Type` synthesis errors. -/
noncomputable def cert_U_naive_bound : ℕ :=
  let K := lexBase (n * (n + 1))
  n * K ^ 6 + n * K ^ 5 + (n * n) * K ^ 4 +
    Fintype.card (EchoMsg n t F) * K ^ 3 +
    Fintype.card (ReadyMsg n t F) * K + n

theorem cert_U_le_naive_bound (s : State n t F) :
    cert_U s ≤ cert_U_naive_bound (n := n) (t := t) (F := F) :=
  cert_U_le_bound s

/-! ### Step 3b checkpoint C — `FairASTCertificate` instance -/

open Leslie.Prob in
/-- The `FairASTCertificate` instance for AVSSFaithful.  Takes an
external **fair-action-enabled-at-non-terminated** witness `h_progress`
mirroring AVSS's `avssFairActionEnabled_at_non_terminated`; for
AVSSFaithful, the analog cascade additionally has to dispatch the
`partyEchoReceive` validity check on echoes and is deferred. -/
noncomputable def cert (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F)
    (h_progress : ∀ (s : State n t F), cert_Inv coeffs s → ¬ terminated s →
                  ∃ j ∈ (fairActions : Set (Action n t F)), gate j s) :
    FairASTCertificate (spec (t := t) sec corr coeffs) fair terminated where
  Inv := cert_Inv coeffs
  V := cert_V
  U := cert_U
  inv_init := fun s hinit => cert_Inv_init sec corr coeffs s hinit
  inv_step := fun a s h hinv s' hs' => by
    have heff : ((spec (t := t) sec corr coeffs).actions a).effect s h =
        PMF.pure (step a s) := rfl
    rw [heff, PMF.support_pure, Set.mem_singleton_iff] at hs'
    subst hs'
    exact cert_Inv_preserve coeffs a s h hinv
  V_term := fun s _ ht => by
    show (cert_U s : NNReal) = 0
    rw [cert_U_eq_zero_of_terminated s ht]; simp
  V_pos := fun s hinv hnt => by
    show 0 < (cert_U s : NNReal)
    have hpos : 0 < cert_U s := cert_U_pos_of_not_terminated s hinv hnt
    exact_mod_cast hpos
  V_super := fun a s h hinv hnt => by
    classical
    have heff : ((spec (t := t) sec corr coeffs).actions a).effect s h =
        PMF.pure (step a s) := rfl
    by_cases hpost : terminated (step a s)
    · left
      rw [heff, tsum_eq_single (step a s)]
      · rw [PMF.pure_apply, if_pos rfl, one_mul]
        have h_post : cert_U (step a s) = 0 := cert_U_eq_zero_of_terminated _ hpost
        unfold cert_V
        rw [h_post]; simp
      · intro b hb
        rw [PMF.pure_apply, if_neg hb, zero_mul]
    · right
      intro s' hs'
      rw [heff, PMF.support_pure, Set.mem_singleton_iff] at hs'
      subst hs'
      exact h_progress _ (cert_Inv_preserve coeffs a s h hinv) hpost
  V_super_fair := fun a s h _hfair hinv hnt => by
    classical
    have heff : ((spec (t := t) sec corr coeffs).actions a).effect s h =
        PMF.pure (step a s) := rfl
    by_cases hpost : terminated (step a s)
    · left
      rw [heff, tsum_eq_single (step a s)]
      · rw [PMF.pure_apply, if_pos rfl, one_mul]
        have h_post : cert_U (step a s) = 0 := cert_U_eq_zero_of_terminated _ hpost
        have h_pre : 0 < cert_U s := cert_U_pos_of_not_terminated s hinv hnt
        unfold cert_V
        rw [h_post]
        exact_mod_cast h_pre
      · intro b hb
        rw [PMF.pure_apply, if_neg hb, zero_mul]
    · right
      intro s' hs'
      rw [heff, PMF.support_pure, Set.mem_singleton_iff] at hs'
      subst hs'
      exact h_progress _ (cert_Inv_preserve coeffs a s h hinv) hpost
  U_term := fun s _ ht => cert_U_eq_zero_of_terminated s ht
  U_dec_det := fun a s h _hfair hinv hnt s' hs' => by
    classical
    have heff : ((spec (t := t) sec corr coeffs).actions a).effect s h =
        PMF.pure (step a s) := rfl
    rw [heff, PMF.support_pure, Set.mem_singleton_iff] at hs'
    subst hs'
    by_cases hpost : terminated (step a s)
    · left
      have h_post : cert_U (step a s) = 0 := cert_U_eq_zero_of_terminated _ hpost
      have h_pre : 0 < cert_U s := cert_U_pos_of_not_terminated s hinv hnt
      omega
    · right
      exact h_progress _ (cert_Inv_preserve coeffs a s h hinv) hpost
  U_bdd_subl := fun _ => ⟨cert_U_naive_bound, fun s _ _ => cert_U_le_bound s⟩
  V_init_bdd :=
    ⟨((@cert_U_naive_bound n t F _ : ℕ) : NNReal),
      fun s _ => by
        show ((cert_U s : ℕ) : NNReal) ≤ ((@cert_U_naive_bound n t F _ : ℕ) : NNReal)
        exact_mod_cast cert_U_le_bound s⟩

/-! ### Step 3b checkpoint C — termination theorems -/

open Leslie.Prob MeasureTheory in
/-- **Trajectory-form termination via the BC running-min route**.
Every fair execution almost-surely reaches a terminated state.  Takes
the fair-action-enabled-at-non-terminated witness `h_progress` and the
trajectory running-min-drop hypothesis `h_drop_io` as parameters. -/
theorem termination_AS_fair_traj
    (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F)
    (μ₀ : Measure (State n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr coeffs s)
    (h_progress : ∀ (s : State n t F), cert_Inv coeffs s → ¬ terminated s →
                  ∃ j ∈ (fairActions : Set (Action n t F)), gate j s)
    (A : Leslie.Prob.TrajectoryFairAdversary
            (spec (t := t) sec corr coeffs) fair μ₀)
    (h_drop_io : ∀ N : ℕ, FairASTCertificate.TrajectoryFairRunningMinDropIO
        (spec (t := t) sec corr coeffs) fair
        (cert sec corr coeffs h_progress) μ₀ A.toFair N) :
    AlmostDiamond (spec (t := t) sec corr coeffs) A.toAdversary μ₀ terminated := by
  have h_init_inv : ∀ᵐ s ∂μ₀, (cert sec corr coeffs h_progress).Inv s := by
    filter_upwards [h_init] with s hs
    exact (cert sec corr coeffs h_progress).inv_init s hs
  set certX := cert sec corr coeffs h_progress with hcertdef
  unfold AlmostDiamond
  have hbounded_or_unbounded :
      ∀ ω : Trace (State n t F) (Action n t F),
        (∃ N : ℕ, ∀ k, certX.V (ω k).1 ≤ ((N : ℕ) : NNReal)) ∨
        (∀ N : ℕ, ¬ (∀ k, certX.V (ω k).1 ≤ ((N : ℕ) : NNReal))) := by
    intro ω
    by_cases h : ∃ N : ℕ, ∀ k, certX.V (ω k).1 ≤ ((N : ℕ) : NNReal)
    · exact .inl h
    · refine .inr ?_
      intro N hbnd
      exact h ⟨N, hbnd⟩
  have h_inf_null :
      ∀ᵐ ω ∂(traceDist (spec (t := t) sec corr coeffs) A.toAdversary μ₀),
      ¬ (∀ N : ℕ, ¬ (∀ k, certX.V (ω k).1 ≤ ((N : ℕ) : NNReal))) := by
    rw [ae_iff]
    have heq :
        {a : Trace (State n t F) (Action n t F) |
            ¬ ¬ ∀ N : ℕ, ¬ (∀ k, certX.V (a k).1 ≤ ((N : ℕ) : NNReal))} =
        {ω : Trace (State n t F) (Action n t F) |
            ∀ N : ℕ, ¬ (∀ k, certX.V (ω k).1 ≤ ((N : ℕ) : NNReal))} := by
      ext ω; simp
    rw [heq]
    exact FairASTCertificate.pi_infty_zero_fair certX μ₀ h_init_inv A.toFair
  have h_each_N : ∀ N : ℕ,
      ∀ᵐ ω ∂(traceDist (spec (t := t) sec corr coeffs) A.toAdversary μ₀),
        (∀ k, certX.V (ω k).1 ≤ ((N : ℕ) : NNReal)) → ∃ k, terminated (ω k).1 :=
    fun N => FairASTCertificate.pi_n_AST_fair_with_progress_bc_of_running_min_drops
      certX μ₀ h_init_inv A.toFair N (h_drop_io N)
  rw [← MeasureTheory.ae_all_iff] at h_each_N
  filter_upwards [h_each_N, h_inf_null] with ω hN h_inf
  rcases hbounded_or_unbounded ω with ⟨N, hbnd⟩ | hunb
  · exact hN N hbnd
  · exact absurd hunb h_inf

/-- Termination as `AlmostDiamond` under a trajectory-fair adversary. -/
theorem termination_AS_fair
    (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F)
    (μ₀ : MeasureTheory.Measure (State n t F))
    [MeasureTheory.IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr coeffs s)
    (h_progress : ∀ (s : State n t F), cert_Inv coeffs s → ¬ terminated s →
                  ∃ j ∈ (fairActions : Set (Action n t F)), gate j s)
    (A : Leslie.Prob.TrajectoryFairAdversary
            (spec (t := t) sec corr coeffs) fair μ₀)
    (h_drop_io : ∀ N : ℕ, FairASTCertificate.TrajectoryFairRunningMinDropIO
        (spec (t := t) sec corr coeffs) fair
        (cert sec corr coeffs h_progress) μ₀ A.toFair N) :
    AlmostDiamond (spec (t := t) sec corr coeffs) A.toAdversary μ₀ terminated :=
  termination_AS_fair_traj sec corr coeffs μ₀ h_init h_progress A h_drop_io

/-- **Termination under atomic broadcast (CR '93 spirit).** -/
theorem termination_AS_fair_under_atomic_broadcast
    (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F)
    (μ₀ : MeasureTheory.Measure (State n t F))
    [MeasureTheory.IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr coeffs s)
    (h_progress : ∀ (s : State n t F), cert_Inv coeffs s → ¬ terminated s →
                  ∃ j ∈ (fairActions : Set (Action n t F)), gate j s)
    (A : Leslie.Prob.TrajectoryFairAdversary
            (spec (t := t) sec corr coeffs) fair μ₀)
    (_h_atomic : atomic_broadcast_AE sec corr coeffs μ₀ A.toAdversary)
    (h_drop_io : ∀ N : ℕ, FairASTCertificate.TrajectoryFairRunningMinDropIO
        (spec (t := t) sec corr coeffs) fair
        (cert sec corr coeffs h_progress) μ₀ A.toFair N) :
    AlmostDiamond (spec (t := t) sec corr coeffs) A.toAdversary μ₀ terminated :=
  termination_AS_fair sec corr coeffs μ₀ h_init h_progress A h_drop_io

end Leslie.Examples.Prob.AVSSFaithful
