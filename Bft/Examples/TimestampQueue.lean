/-
Copyright (c) 2026 lean-tla contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Example: McMillan's timestamped queue (CAV 2024)

The running example of "Toward Liveness Proofs at Scale" (McMillan,
CAV 2024): a sender enters messages with increasing natural-number
timestamps (gaps allowed); a receiver polls the queue and removes the
message with the *minimum* timestamp.

  property: if the receiver polls infinitely often, every timestamp
  sent is eventually received — `send(t) ⇒ ♦recv(t)`, proved here as
  `t ∈ pend ↝ t ∈ rcvd`.

McMillan's point is that the proof needs *no well-founded ranking*: the
liveness of the queue does not depend on the well-foundedness of the
timestamp order. Our certificate follows his relational ranking exactly:

  δ(τ) ≜ pend(τ) ∧ τ ≤ t   (pending timestamps not above t)
  φ    ≜ pend(t)

Each poll removes the minimum pending timestamp, which is ≤ t while
`t` is pending — so `δ` strictly shrinks; sends add timestamps above
`last ≥ t`, so `δ` is conserved. In Lean the finiteness side condition
(his Rule 5) is just `Set.Finite {τ | τ ≤ t}` — no out-of-logic trick.

The per-step obligations `c1`–`c3` are pure one-step first-order facts —
the grind targets corresponding to McMillan's EPR verification
conditions.
-/
import Bft.RelRank
import Bft.Tactic

namespace Bft.Examples

open Bft

/-- Queue state: pending timestamps, last timestamp entered, and the
sequence of received timestamps (history variable, so the property can
be stated as `recv`). -/
structure TQSt where
  pend : Finset ℕ
  last : ℕ
  rcvd : List ℕ
deriving DecidableEq

/-- Sender enters timestamp `t`, strictly above the last one entered. -/
def Send (t : ℕ) : Action TQSt := fun s s' =>
  s.last < t ∧ s'.pend = s.pend ∪ {t} ∧ s'.last = t ∧ s'.rcvd = s.rcvd

/-- Receiver polls: the minimum pending timestamp is removed and
received. -/
def Poll : Action TQSt := fun s s' =>
  ∃ h : s.pend.Nonempty,
    s'.pend = s.pend.erase (s.pend.min' h) ∧ s'.last = s.last ∧
    s'.rcvd = s.pend.min' h :: s.rcvd

/-- The step relation. -/
def Next : Action TQSt := fun s s' => (∃ t, Send t s s') ∨ Poll s s'

/-- Frame: the whole state. -/
def vars : TQSt → TQSt := id

/-- Initially the queue is empty. -/
def Init : StatePred TQSt := { s | s.pend = ∅ ∧ s.last = 0 ∧ s.rcvd = [] }

/-- The specification: interleaving stuttering machine. -/
def Hspec : Pred TQSt := tlaAnd (statePred Init) (stutAlways Next vars)

/-! ## Safety invariant (re-used from the safety proof, as in the paper) -/

/-- Every pending timestamp is at most `last`. -/
def Inv : StatePred TQSt := { s | ∀ τ ∈ s.pend, τ ≤ s.last }

theorem init_inv : ∀ s, s ∈ Init → s ∈ Inv := by
  intro s hs
  simp [Inv, hs.1]

theorem step_inv : ∀ s s', StutAction Next vars s s' → s ∈ Inv → s' ∈ Inv := by
  intro s s' hstep hinv
  rcases hstep with hnext | hstut
  · rcases hnext with ⟨t, hlt, hpend, hlast, _⟩ | ⟨h, hpend, hlast, _⟩
    · intro τ hτ
      grind [Inv]
    · intro τ hτ
      grind [Inv, Finset.mem_of_mem_erase]
  · change s' = s at hstut
    rwa [hstut]

theorem safety : Entails Hspec (always (statePred Inv)) :=
  init_invariant_stut Init Next vars Inv init_inv step_inv

/-! ## Liveness: the relational ranking certificate -/

/-- McMillan's certificate for "timestamp `t` is eventually received". -/
noncomputable def cert (t : ℕ) :
    RelRankCert TQSt { s | t ∈ s.pend } { s | t ∈ s.rcvd } where
  α := ℕ
  r := Poll
  φ := { s | t ∈ s.pend }
  δ := fun s τ => τ ∈ s.pend ∧ τ ≤ t
  R := fun _s τ => τ ≤ t
  H := Hspec
  finiteness := by
    intro e n
    exact Set.finite_le_nat t
  c1 := by
    intro e _hE k hp
    exact Or.inr ⟨hp, fun _x h => h.2⟩
  c2 := by
    intro e hE k hφ
    have hN : StutAction Next vars (e k) (e (k + 1)) := stutAlways_step hE.2
    have hinv : (e k) ∈ Inv := always_statePred_at (safety e hE)
    rcases hN with hnext | hstut
    · rcases hnext with ⟨t', hlt, hpend, _, hrcvd⟩ | ⟨hne, hpend, _, hrcvd⟩
      · -- Send: φ preserved; δ conserved (the new timestamp is > last ≥ t)
        right
        refine ⟨by grind [Finset.mem_union_left], fun x hx => by grind [Inv]⟩
      · -- Poll: either t is the minimum (q reached) or φ ∧ δ conserved
        by_cases hm : (e k).pend.min' hne = t
        · left
          grind
        · right
          refine ⟨by grind, fun x hx => by grind [Finset.mem_of_mem_erase]⟩
    · -- Stutter
      right
      change e (k + 1) = e k at hstut
      grind [Conserves]
  c3 := by
    intro e _hE k hφ hr
    obtain ⟨hne, hpend, _, _⟩ := hr
    right
    -- the removed minimum is ≤ t (since t is pending), hence in δ, and
    -- is gone afterwards
    refine ⟨(e k).pend.min' hne,
      ⟨Finset.min'_mem _ _, Finset.min'_le _ t hφ⟩, ?_⟩
    grind

/-- McMillan's property (4): if the receiver polls infinitely often, every
timestamp sent is eventually received. -/
theorem recv_liveness (t : ℕ) :
    Entails (tlaAnd Hspec (globalJustice Poll))
      (leadsTo (statePred { s | t ∈ s.pend }) (statePred { s | t ∈ s.rcvd })) :=
  (cert t).toLeadsTo

end Bft.Examples
