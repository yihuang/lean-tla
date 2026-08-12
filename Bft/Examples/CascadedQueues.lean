/-
Copyright (c) 2026 lean-tla contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Example: McMillan's cascaded queues (CAV 2024, §3.2)

Two timestamped queues in cascade: when queue 1 is polled, the received
timestamp is entered into queue 2 *in the same transition*. The property
is end-to-end response:

  `t ∈ pend₁ ↝ t ∈ rcvd₂`   assuming `□◇poll₁` and `□◇poll₂`.

McMillan proves this with his Rule D (chaining with tableau axioms fed
to Z3). Here chaining is `RelRankCert.trans` (Rule 7): two certificates,
each a relational-ranking certificate of the single-queue shape, compose
at the descent layer — no temporal tableau reasoning at all. The
mid-condition `t ∈ rcvd₁` is related to `t ∈ pend₂` by a safety
invariant (an element received by queue 1 is either pending in queue 2
or already received by queue 2), exactly the "safety invariants are
reused for liveness" pattern of the paper.

The second certificate's environment bundles the *other* queue's justice
into its `H`, so `trans`'s environment implication `hH` is pure
conjunction shuffling.
-/
import Bft.Examples.TimestampQueue

namespace Bft.Examples

open Bft

/-- Two timestamped queues in cascade. -/
structure CQSt where
  q1 : TQSt
  q2 : TQSt
deriving DecidableEq

/-- Sender enters timestamp `t` into queue 1 (increasing, gaps allowed). -/
def Send1 (t : ℕ) : Action CQSt := fun s s' =>
  Send t s.q1 s'.q1 ∧ s'.q2 = s.q2

/-- Poll queue 1: the minimum pending timestamp is received and entered
into queue 2 in the same transition. -/
def Poll1 : Action CQSt := fun s s' =>
  ∃ h : s.q1.pend.Nonempty,
    s'.q1.pend = s.q1.pend.erase (s.q1.pend.min' h) ∧ s'.q1.last = s.q1.last ∧
    s'.q1.rcvd = s.q1.pend.min' h :: s.q1.rcvd ∧
    s'.q2.pend = s.q2.pend ∪ {s.q1.pend.min' h} ∧ s'.q2.last = s.q1.pend.min' h ∧
    s'.q2.rcvd = s.q2.rcvd

/-- Poll queue 2. -/
def Poll2 : Action CQSt := fun s s' =>
  Poll s.q2 s'.q2 ∧ s'.q1 = s.q1

/-- The step relation. -/
def CNext : Action CQSt := fun s s' =>
  (∃ t, Send1 t s s') ∨ Poll1 s s' ∨ Poll2 s s'

/-- Frame: the whole state. -/
def cvars : CQSt → CQSt := id

/-- Initially both queues are empty. -/
def CInit : StatePred CQSt := { s | s.q1.pend = ∅ ∧ s.q1.last = 0 ∧ s.q1.rcvd = [] ∧
    s.q2.pend = ∅ ∧ s.q2.last = 0 ∧ s.q2.rcvd = [] }

/-- The specification. -/
def CHspec : Pred CQSt := tlaAnd (statePred CInit) (stutAlways CNext cvars)

/-! ## Safety invariants -/

/-- The cascade invariant bundle:
1. each queue's pending timestamps are bounded by its `last`;
2. `last₂ ≤ last₁`;
3. pending timestamps in queue 1 are strictly above `last₂`;
4. an element received by queue 1 is in flight in queue 2 or received. -/
def CInv : StatePred CQSt := { s |
  (∀ τ ∈ s.q1.pend, τ ≤ s.q1.last) ∧
  (∀ τ ∈ s.q2.pend, τ ≤ s.q2.last) ∧
  s.q2.last ≤ s.q1.last ∧
  (∀ τ ∈ s.q1.pend, s.q2.last < τ) ∧
  (∀ x, x ∈ s.q1.rcvd → x ∈ s.q2.pend ∨ x ∈ s.q2.rcvd) }

theorem cinit_inv : ∀ s, s ∈ CInit → s ∈ CInv := by
  intro s hs
  obtain ⟨p1, l1, r1, p2, l2, r2⟩ := hs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [p1, l1, r1, p2, l2, r2]

theorem cstep_inv : ∀ s s', StutAction CNext cvars s s' → s ∈ CInv → s' ∈ CInv := by
  intro s s' hstep hinv
  rcases hstep with hnext | hstut
  swap
  · change s' = s at hstut
    rwa [hstut]
  obtain ⟨h1, h2, hle, hgt, hflight⟩ := hinv
  rcases hnext with ⟨t, hsend, hq2⟩ | hpoll1 | ⟨hpoll2, hq1⟩
  · -- Send1: only queue 1 changes
    obtain ⟨hlt, hpend, hlast, hrcvd⟩ := hsend
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro τ hτ
      rw [hpend] at hτ
      grind
    · intro τ hτ
      rw [hq2] at hτ ⊢
      exact le_trans (h2 τ hτ) (by grind)
    · grind
    · intro τ hτ
      rw [hpend] at hτ
      grind
    · intro x hx
      rw [hrcvd] at hx
      rw [hq2]
      exact hflight x hx
  · -- Poll1: m leaves queue 1 and enters queue 2
    obtain ⟨hne, hp1, hl1, hr1, hp2, hl2, hr2⟩ := hpoll1
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro τ hτ
      rw [hp1] at hτ
      grind [Finset.mem_of_mem_erase]
    · intro τ hτ
      rw [hp2] at hτ
      rcases Finset.mem_union.mp hτ with h | h
      · have hm := hgt _ (Finset.min'_mem _ hne)
        grind
      · rw [Finset.mem_singleton] at h
        grind
    · grind [Finset.min'_mem, Finset.min'_le]
    · intro τ hτ
      rw [hp1] at hτ
      have hm : s.q1.pend.min' hne < τ := by
        have h1 := Finset.min'_le _ _ (Finset.mem_of_mem_erase hτ)
        have h2 := Finset.mem_erase.mp hτ
        grind
      grind
    · intro x hx
      rw [hr1] at hx
      rcases List.mem_cons.mp hx with h | h
      · rw [hp2]
        grind
      · rw [hp2, hr2]
        rcases hflight x h with hl | hr
        · exact Or.inl (Finset.mem_union_left _ hl)
        · exact Or.inr hr
  · -- Poll2: only queue 2 changes
    obtain ⟨hne, hp2, hl2, hr2⟩ := hpoll2
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro τ hτ
      rw [hq1] at hτ
      grind
    · intro τ hτ
      rw [hp2] at hτ
      grind [Finset.mem_of_mem_erase]
    · grind
    · intro τ hτ
      rw [hq1] at hτ
      grind
    · intro x hx
      rw [hp2, hr2]
      rcases hflight x (hq1 ▸ hx) with hl | hr
      · by_cases hm : s.q2.pend.min' hne = x
        · exact Or.inr (by grind)
        · exact Or.inl (Finset.mem_erase.mpr ⟨Ne.symm hm, hl⟩)
      · exact Or.inr (List.mem_cons_of_mem _ hr)

theorem csafety : Entails CHspec (always (statePred CInv)) :=
  init_invariant_stut CInit CNext cvars CInv cinit_inv cstep_inv

/-! ## The two certificates -/

/-- Queue 1's certificate: `t` pending in queue 1 is eventually received
by queue 1 (justice `poll₁`). The other queue's justice is bundled into
`H` so the certificates compose under `RelRankCert.trans`. -/
noncomputable def cert₁ (t : ℕ) :
    RelRankCert CQSt { s | t ∈ s.q1.pend } { s | t ∈ s.q1.rcvd } where
  α := ℕ
  r := Poll1
  φ := { s | t ∈ s.q1.pend }
  δ := fun s τ => τ ∈ s.q1.pend ∧ τ ≤ t
  R := fun _s τ => τ ≤ t
  H := tlaAnd CHspec (globalJustice Poll2)
  finiteness := by
    intro e n
    exact Set.finite_le_nat t
  c1 := by
    intro e _hE k hp
    exact Or.inr ⟨hp, fun _x h => h.2⟩
  c2 := by
    intro e hE k hφ
    have hN : StutAction CNext cvars (e k) (e (k + 1)) := by
      have h := hE.1.2 k
      simpa [stutAlways, always] using h
    have hinv : (e k) ∈ CInv := by
      have h := csafety e hE.1 k
      rwa [statePred_drop] at h
    rcases hN with hnext | hstut
    swap
    · right
      change e (k + 1) = e k at hstut
      grind [Conserves]
    rcases hnext with ⟨t', hsend, hq2⟩ | hpoll1 | ⟨hpoll2, hq1⟩
    · -- Send1: φ preserved; δ conserved (new timestamp > last₁ ≥ t)
      obtain ⟨hlt, hpend, _, _⟩ := hsend
      right
      have ht : t < t' := by
        have := hinv.1 t hφ; omega
      refine ⟨by show t ∈ (e (k + 1)).q1.pend; rw [hpend]
                 grind [Finset.mem_union_left], fun x hx => ?_⟩
      change x ∈ (e (k + 1)).q1.pend ∧ x ≤ t at hx
      rw [hpend] at hx
      grind
    · -- Poll1: either t is the minimum (received) or φ ∧ δ conserved
      obtain ⟨hne, hp1, _, hr1, _, _, _⟩ := hpoll1
      by_cases hm : (e k).q1.pend.min' hne = t
      · left
        show t ∈ (e (k + 1)).q1.rcvd
        rw [hr1, hm]
        exact List.mem_cons_self
      · right
        refine ⟨by show t ∈ (e (k + 1)).q1.pend; rw [hp1]; grind,
          fun x hx => by
            change x ∈ (e (k + 1)).q1.pend ∧ x ≤ t at hx
            rw [hp1] at hx
            grind [Finset.mem_of_mem_erase]⟩
    · -- Poll2: queue 1 untouched
      obtain ⟨hne, hp2, _, _⟩ := hpoll2
      right
      refine ⟨by show t ∈ (e (k + 1)).q1.pend; rw [hq1]; exact hφ,
        fun x hx => by
          change x ∈ (e (k + 1)).q1.pend ∧ x ≤ t at hx
          rw [hq1] at hx
          exact hx⟩
  c3 := by
    intro e _hE k hφ hr
    obtain ⟨hne, hp1, _, _, _, _, _⟩ := hr
    right
    refine ⟨(e k).q1.pend.min' hne,
      ⟨Finset.min'_mem _ _, Finset.min'_le _ t hφ⟩, ?_⟩
    show ¬ ((e k).q1.pend.min' hne ∈ (e (k + 1)).q1.pend ∧ (e k).q1.pend.min' hne ≤ t)
    rw [hp1]
    grind

/-- Queue 2's certificate, with mid-condition `t ∈ rcvd₁`: an element
received by queue 1 is in flight in queue 2 (safety invariant 5), from
where queue 2's certificate takes over (justice `poll₂`). -/
noncomputable def cert₂ (t : ℕ) :
    RelRankCert CQSt { s | t ∈ s.q1.rcvd } { s | t ∈ s.q2.rcvd } where
  α := ℕ
  r := Poll2
  φ := { s | t ∈ s.q2.pend }
  δ := fun s τ => τ ∈ s.q2.pend ∧ τ ≤ t
  R := fun _s τ => τ ≤ t
  H := tlaAnd CHspec (globalJustice Poll1)
  finiteness := by
    intro e n
    exact Set.finite_le_nat t
  c1 := by
    intro e hE k hp
    have hinv : (e k) ∈ CInv := by
      have h := csafety e hE.1 k
      rwa [statePred_drop] at h
    rcases hinv.2.2.2.2 t hp with hl | hr
    · exact Or.inr ⟨hl, fun _x h => h.2⟩
    · exact Or.inl hr
  c2 := by
    intro e hE k hφ
    have hN : StutAction CNext cvars (e k) (e (k + 1)) := by
      have h := hE.1.2 k
      simpa [stutAlways, always] using h
    have hinv : (e k) ∈ CInv := by
      have h := csafety e hE.1 k
      rwa [statePred_drop] at h
    rcases hN with hnext | hstut
    swap
    · right
      change e (k + 1) = e k at hstut
      grind [Conserves]
    rcases hnext with ⟨t', hsend, hq2⟩ | hpoll1 | ⟨hpoll2, hq1⟩
    · -- Send1: queue 2 untouched
      right
      refine ⟨by show t ∈ (e (k + 1)).q2.pend; rw [hq2]; exact hφ,
        fun x hx => by
          change x ∈ (e (k + 1)).q2.pend ∧ x ≤ t at hx
          rw [hq2] at hx
          exact hx⟩
    · -- Poll1: m enters queue 2, above last₂ ≥ t — φ preserved, δ conserved
      obtain ⟨hne, hp1, _, _, hp2, hl2, _⟩ := hpoll1
      right
      have hmt : t < (e k).q1.pend.min' hne := by
        have h2 : t ≤ (e k).q2.last := hinv.2.1 t hφ
        have h3 := hinv.2.2.2.1 _ (Finset.min'_mem _ hne)
        grind
      refine ⟨by show t ∈ (e (k + 1)).q2.pend; rw [hp2]
                 grind [Finset.mem_union_left], fun x hx => ?_⟩
      change x ∈ (e (k + 1)).q2.pend ∧ x ≤ t at hx
      rw [hp2] at hx
      grind
    · -- Poll2: either t is received, or φ ∧ δ conserved
      obtain ⟨hne, hp2, _, hr2⟩ := hpoll2
      by_cases hm : (e k).q2.pend.min' hne = t
      · left
        show t ∈ (e (k + 1)).q2.rcvd
        rw [hr2, hm]
        exact List.mem_cons_self
      · right
        refine ⟨by show t ∈ (e (k + 1)).q2.pend; rw [hp2]; grind,
          fun x hx => by
            change x ∈ (e (k + 1)).q2.pend ∧ x ≤ t at hx
            rw [hp2] at hx
            grind [Finset.mem_of_mem_erase]⟩
  c3 := by
    intro e _hE k hφ hr
    obtain ⟨hne, hp2, _, _⟩ := hr.1
    right
    refine ⟨(e k).q2.pend.min' hne,
      ⟨Finset.min'_mem _ _, Finset.min'_le _ t hφ⟩, ?_⟩
    show ¬ ((e k).q2.pend.min' hne ∈ (e (k + 1)).q2.pend ∧ (e k).q2.pend.min' hne ≤ t)
    rw [hp2]
    grind

/-- McMillan's end-to-end response property for the cascade. -/
theorem cascade_liveness (t : ℕ) :
    Entails (tlaAnd CHspec (tlaAnd (globalJustice Poll1) (globalJustice Poll2)))
      (leadsTo (statePred { s | t ∈ s.q1.pend }) (statePred { s | t ∈ s.q2.rcvd })) := by
  have hH : ∀ e, tlaAnd (cert₁ t).H (globalJustice (cert₁ t).r) e →
      tlaAnd (cert₂ t).H (globalJustice (cert₂ t).r) e := by
    intro e hE
    obtain ⟨h1, h2⟩ := hE
    obtain ⟨hH, hJ2⟩ := h1
    exact ⟨⟨hH, h2⟩, hJ2⟩
  have h := RelRankCert.trans (cert₁ t) (cert₂ t) hH
  intro e hE
  obtain ⟨hHc, hJ1, hJ2⟩ := hE
  apply h e
  show (cert₁ t).H e ∧ (globalJustice (cert₁ t).r) e
  refine ⟨?_, hJ1⟩
  show CHspec e ∧ (globalJustice Poll2) e
  exact ⟨hHc, hJ2⟩

end Bft.Examples
