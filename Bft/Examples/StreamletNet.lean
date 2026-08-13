/-
Copyright (c) 2026 lean-tla contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Case study: Streamlet over a partially synchronous network

This file adds the *network layer* that `Bft.Examples.Streamlet` deliberately
omitted (its header declares: "Liveness needs a partial-synchrony model
(epochs of 2Δ and message delivery bounds), which this global-clock model
does not attempt").

The transport model is the standard Global Stabilization Time (GST) regime
(Dwork–Lynch–Stockmeyer; Streamlet §2.2, §3.6):

* **Rounds** are a global clock `now : ℕ`. Before `GST` message delays are
  arbitrary; after `GST` an honest sender's message is delivered within `Δ`
  rounds.
* **In-flight messages**: a message is *sent* (enters `inflight`) and only
  later *delivered* (moves to `seen`). Delivery to the honest broadcast group
  is modeled as one `Deliver` step — a conservative over-approximation of the
  paper's implicit echoing + Δ-bounded per-pair delivery: every honest node
  observes the message *by* the deadline, never later. (Per-recipient
  delivery with `Packet`/`NetState` from `Bft/Refine.lean` is a refinement,
  not modeled here.)
* **The Δ-bound is split into its two halves**, following the library's
  doctrine that fairness assumptions stay explicit (`docs/bft-design.md`
  §4.3):
  1. *safety* — a message cannot be delivered *late*: `Deliver m` is guarded
     by `now ≤ max GST (m.round + Δ)` when the sender is honest, and `Tick`
     is blocked from crossing an honest in-flight message's deadline. This is
     the inductive invariant `NoOverdue`, and gives **Fact 1 (no late
     delivery)** as a theorem.
  2. *liveness* — a message is actually delivered: under weak fairness
     `WF(Deliver m)`, `m ∈ inflight ↝ m ∈ seen` (proved by `wf1`). Combined
     with the safety half, an honest message sent at round `r` is observed by
     round `max GST (r + Δ)`.

The Streamlet *protocol* layer (proposals, votes, notarization, the
leader schedule, and the paper's Fact 2 / Fact 3 / Lemma 5) is built on top
of this transport layer in a follow-up file; here we only prove the delivery
guarantee the protocol facts rest on.
-/
import Bft.Examples.Streamlet
import Bft.Tactic

namespace Bft.Examples.StreamletNet

open Bft
open Bft.Examples.Streamlet (Blk)

variable (n : ℕ) (Byz : Finset (Fin n)) (Δ GST : ℕ)

/-! ## Messages and state -/

/-- A message body: a block proposal for some epoch, or a vote for a block.
The sender of a `.prop` is the epoch leader; the sender of a `.vote` is the
voter. -/
inductive Body where
  | prop (e : ℕ) (b : Blk)
  | vote (b : Blk)
deriving DecidableEq, Repr

/-- A message: source node, send round, and body. -/
structure Msg (n : ℕ) where
  src : Fin n
  round : ℕ
  body : Body
deriving DecidableEq, Repr

/-- Network state: the current round, the messages in flight (sent, not yet
delivered), the messages delivered to the honest broadcast group, and — as
auxiliary *history variables* (Lamport) — the votes and proposals cast so far.
`castVotes`/`castProps` are monotone accumulators of what was sent; they are
what the safety invariant is stated over. -/
structure St (n : ℕ) where
  now : ℕ
  inflight : Finset (Msg n)
  seen : Finset (Msg n)
  castVotes : Finset (Fin n × Blk)
  castProps : Finset (ℕ × Blk)
deriving DecidableEq

/-- The delivery deadline of `m`: round `max GST (m.round + Δ)`. -/
def deadline (m : Msg n) : ℕ := max GST (m.round + Δ)

/-! ## Actions -/

/-- Time passes — but never past the delivery deadline of an honest-sent
message still in flight. -/
def Tick : Action (St n) := fun s s' =>
  s'.now = s.now + 1 ∧ s'.inflight = s.inflight ∧ s'.seen = s.seen ∧
  s'.castVotes = s.castVotes ∧ s'.castProps = s.castProps ∧
  (∀ m, m ∈ s.inflight → m.src ∉ Byz → s'.now ≤ deadline n Δ GST m)

/-- A node broadcasts a message: it enters the network, stamped with the
current round. A message is sent at most once. -/
def Send (m : Msg n) : Action (St n) := fun s s' =>
  m.round = s.now ∧ m ∉ s.inflight ∧ m ∉ s.seen ∧
  s'.now = s.now ∧ s'.inflight = insert m s.inflight ∧ s'.seen = s.seen ∧
  s'.castVotes = (match m.body with | Body.vote b => insert (m.src, b) s.castVotes | _ => s.castVotes) ∧
  s'.castProps = (match m.body with | Body.prop e b => insert (e, b) s.castProps | _ => s.castProps)

/-- Delivery: an in-flight message becomes visible to all honest nodes.
After GST, an honest-sent message is delivered within `Δ` of being sent —
the guard forbids late delivery. -/
def Deliver (m : Msg n) : Action (St n) := fun s s' =>
  m ∈ s.inflight ∧ (m.src ∉ Byz → s.now ≤ deadline n Δ GST m) ∧
  s'.now = s.now ∧ s'.inflight = s.inflight.erase m ∧ s'.seen = insert m s.seen ∧
  s'.castVotes = s.castVotes ∧ s'.castProps = s.castProps

/-- The step relation. -/
def Next : Action (St n) := fun s s' =>
  Tick n Byz Δ GST s s' ∨ (∃ m, Send n m s s') ∨
    (∃ m, Deliver n Byz Δ GST m s s')

/-- Frame: the whole state. -/
def vars (n : ℕ) : St n → St n := id

/-- Initially: round 0, nothing in flight, nothing seen. -/
def Init : StatePred (St n) := { s | s.now = 0 ∧ s.inflight = ∅ ∧ s.seen = ∅ ∧ s.castVotes = ∅ ∧ s.castProps = ∅ }

/-- The specification. -/
def Hspec : Pred (St n) := tlaAnd (statePred (Init n)) (stutAlways (Next n Byz Δ GST) (vars n))

/-! ## Fact 1, safety half: no late delivery

The inductive invariant `NoOverdue` — no honest-sent message is still in
flight past its deadline — is the safety content of the paper's Δ-bounded
delivery assumption. -/

/-- No honest-sent in-flight message has missed its deadline. -/
def NoOverdue : StatePred (St n) := { s |
  ∀ m, m ∈ s.inflight → m.src ∉ Byz → s.now ≤ deadline n Δ GST m }

attribute [grind unfold] NoOverdue deadline

theorem init_inv : ∀ s, s ∈ Init n → s ∈ NoOverdue n Byz Δ GST := by
  intro s hs
  obtain ⟨_hnow, hinf, _hseen, _, _⟩ := hs
  intro m hm _hsrc
  simp [hinf] at hm

theorem step_inv : ∀ s s', StutAction (Next n Byz Δ GST) (vars n) s s' →
    s ∈ NoOverdue n Byz Δ GST → s' ∈ NoOverdue n Byz Δ GST := by
  intro s s' hstep hinv
  rcases hstep with hnext | hstut
  swap
  · have hss' : s' = s := hstut
    rwa [hss']
  rcases hnext with htick | ⟨m, hs⟩ | ⟨m, hd⟩
  · obtain ⟨hnow, hinf, _hseen, _, _, hguard⟩ := htick
    grind
  · obtain ⟨hr, _hninf, _hnseen, hnow, hinf, _hseen, _, _⟩ := hs
    grind
  · obtain ⟨_hmem, _hguard, hnow, hinf, _hseen, _, _⟩ := hd
    grind

/-- The safety half of the delivery guarantee is an invariant of the spec. -/
theorem delivery_safety :
    Entails (Hspec n Byz Δ GST) (always (statePred (NoOverdue n Byz Δ GST))) :=
  init_invariant_stut (Init n) (Next n Byz Δ GST) (vars n) (NoOverdue n Byz Δ GST)
    (init_inv n Byz Δ GST) (step_inv n Byz Δ GST)

/-- Once past a message's deadline, an honest-sent message is no longer in
flight (state-level form of "no late delivery"). -/
theorem not_inflight_after_deadline {s : St n} (hs : s ∈ NoOverdue n Byz Δ GST)
    {m : Msg n} (hsrc : m.src ∉ Byz) (hlate : deadline n Δ GST m < s.now) :
    m ∉ s.inflight := by
  intro hm
  exact (not_lt_of_ge (hs m hm hsrc)) hlate

/-- A message that has been sent and is no longer in flight has been seen. -/
theorem sent_not_inflight_imp_seen {s : St n} {m : Msg n}
    (hsent : m ∈ s.inflight ∨ m ∈ s.seen) (hni : m ∉ s.inflight) : m ∈ s.seen := by
  rcases hsent with h | h
  · exact absurd h hni
  · exact h

/-- **Fact 1 (safety)**: an honest-sent message is delivered by its deadline. -/
theorem delivered_by_deadline {s : St n} (hs : s ∈ NoOverdue n Byz Δ GST)
    {m : Msg n} (hsrc : m.src ∉ Byz) (hsent : m ∈ s.inflight ∨ m ∈ s.seen)
    (hlate : deadline n Δ GST m < s.now) : m ∈ s.seen :=
  sent_not_inflight_imp_seen n hsent (not_inflight_after_deadline n Byz Δ GST hs hsrc hlate)

/-! ## Fact 1, liveness half: delivery actually happens

Under weak fairness of `Deliver m`, an in-flight message is eventually
delivered. The `wf1` rank is the one-bit "still in flight" flag; the
pending predicate folds in the deadline condition so `Deliver m` stays
enabled exactly while the message is in flight. -/

/-- `m` is in flight. -/
def inflightOf (m : Msg n) : StatePred (St n) := { s | m ∈ s.inflight }

/-- `m` has been seen. -/
def seenOf (m : Msg n) : StatePred (St n) := { s | m ∈ s.seen }

/-- The `wf1` pending predicate: `m` in flight, and not past its deadline
(so `Deliver m` is enabled). -/
def pending (m : Msg n) : StatePred (St n) := { s |
  m ∈ s.inflight ∧ (m.src ∉ Byz → s.now ≤ deadline n Δ GST m) }

attribute [grind unfold] pending seenOf

theorem pending_step (m : Msg n) : ∀ s s',
    s ∈ pending n Byz Δ GST m → StutAction (Next n Byz Δ GST) (vars n) s s' →
    s' ∈ pending n Byz Δ GST m ∨ s' ∈ seenOf n m := by
  intro s s' hsp hstep
  rcases hstep with hnext | hstut
  swap
  · left
    have hss' : s' = s := hstut
    rwa [hss']
  rcases hnext with htick | ⟨m', hs⟩ | ⟨m', hd⟩
  · left
    obtain ⟨hnow, hinf, _hseen, _, _, hguard⟩ := htick
    grind
  · left
    obtain ⟨_hr, _hninf, _hnseen, hnow, hinf, _hseen, _, _⟩ := hs
    grind
  · obtain ⟨_hmem, _hguard, hnow, hinf, hseen, _, _⟩ := hd
    grind

theorem pending_aq (m : Msg n) : ∀ s s',
    s ∈ pending n Byz Δ GST m → AngleAction (Deliver n Byz Δ GST m) (vars n) s s' →
    s' ∈ seenOf n m := by
  intro s s' _hsp hang
  obtain ⟨hdel, _⟩ := hang
  obtain ⟨_hmem, _hguard, _hnow, _hinf, hseen, _, _⟩ := hdel
  change m ∈ s'.seen
  rw [hseen]
  exact Finset.mem_insert_self m s.seen

theorem pending_enable (m : Msg n) : ∀ s,
    s ∈ pending n Byz Δ GST m →
      s ∈ Enabled (AngleAction (Deliver n Byz Δ GST m) (vars n)) ∨ s ∈ seenOf n m := by
  intro s hsp
  left
  let s' : St n := { now := s.now, inflight := s.inflight.erase m, seen := insert m s.seen, castVotes := s.castVotes, castProps := s.castProps }
  refine ⟨s', ?_⟩
  constructor
  · exact ⟨hsp.1, hsp.2, rfl, rfl, rfl, rfl, rfl⟩
  · change s' ≠ s
    intro hss
    have hinfle : s.inflight.erase m = s.inflight := by
      simpa [s'] using (congrArg St.inflight hss)
    have hm' : m ∈ s.inflight.erase m := by
      rw [hinfle]
      exact hsp.1
    exact (Finset.mem_erase.mp hm').1 rfl

/-- **Fact 1 (liveness)**: under weak fairness of `Deliver m`, an in-flight
message is eventually delivered. -/
theorem fact1_liveness (m : Msg n) :
    Entails (tlaAnd (Hspec n Byz Δ GST) (WF_v (Deliver n Byz Δ GST m) (vars n)))
      (leadsTo (statePred (inflightOf n m)) (statePred (seenOf n m))) := by
  intro e hE k hk
  have hspec : Hspec n Byz Δ GST e := hE.1
  have hwf : WF_v (Deliver n Byz Δ GST m) (vars n) e := hE.2
  have hnext : stutAlways (Next n Byz Δ GST) (vars n) e := hspec.2
  have hnoover : always (statePred (NoOverdue n Byz Δ GST)) e :=
    delivery_safety n Byz Δ GST e hspec
  have hk' : m ∈ (e k).inflight := by simpa [inflightOf] using hk
  have hpk : e k ∈ pending n Byz Δ GST m := by
    refine ⟨hk', ?_⟩
    intro hsrc
    exact (always_statePred_at hnoover) m hk' hsrc
  have hleads : leadsTo (statePred (pending n Byz Δ GST m)) (statePred (seenOf n m)) e :=
    wf1 (pending n Byz Δ GST m) (seenOf n m) (Next n Byz Δ GST) (Deliver n Byz Δ GST m)
      (vars n) (pending_step n Byz Δ GST m) (pending_aq n Byz Δ GST m)
      (pending_enable n Byz Δ GST m) e ⟨hnext, hwf⟩
  exact hleads k (by simpa using hpk)

end Bft.Examples.StreamletNet
