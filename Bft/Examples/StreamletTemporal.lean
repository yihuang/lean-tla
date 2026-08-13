/-
Copyright (c) 2026 lean-tla contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Case study: Streamlet liveness — the temporal wrapper (Theorem 13)

The final layer: compose the state-level liveness core (`StreamletLiveness`)
with per-epoch honest-timing assumptions into the paper's liveness theorem
(Theorem 13, abstracted to epoch granularity). This mirrors
`TlaDsl/Examples/StreamletLiveness.lean`'s temporal section, translated to
the `Bft` temporal API (`leadsTo`/`statePred`/`always_statePred_at`).

The honest-timing assumptions — the clock advances, the honest leader of
each epoch proposes, and honest nodes vote + delivery chain-notarizes the
proposal before the epoch passes — are stated explicitly as per-epoch
leads-to predicates, bundled into the spec `H`. In the real system these
follow from the transport's Δ-bounded delivery (Fact 1) plus weak fairness
of `Propose`/`VoteH`/`Tick`; here they are the declared trust base, matching
the library's "fairness is explicit" doctrine.
-/
import Bft.Examples.StreamletLiveness

namespace Bft.Examples.StreamletTemporal

open Bft
open Bft.Examples.StreamletNet (Body Msg St vars)
open Bft.Examples.Streamlet (Blk ValidChain bep quorum)
open Bft.Examples.StreamletProto
open Bft.Examples.StreamletLiveness

variable (n : ℕ) (Byz : Finset (Fin n)) (Δ GST f : ℕ) (L : ℕ → Fin n)

/-! ## Monotonicity under protocol steps -/

/-- The sent set of `s'` contains that of `s`. -/
def sentGrows (s s' : St n) : Prop :=
  ∀ m, (m ∈ s.inflight ∨ m ∈ s.seen) → (m ∈ s'.inflight ∨ m ∈ s'.seen)

/-- Every protocol step preserves (grows) the sent set. -/
theorem pnext_sentGrows {s s' : St n} (hstep : PNext n Byz Δ GST f L s s') : sentGrows n s s' := by
  intro m hm
  rcases hstep with htick | ⟨e, b, hpr⟩ | ⟨i, b, hv⟩ | ⟨m0, hd⟩
  · obtain ⟨_hnow, hinf, hseen, _⟩ := htick
    rw [hinf, hseen]; exact hm
  · obtain ⟨_hprior, _hL, _hval, _hbep, _hcur, _hparseen, _hparcast, _hlong, hsend⟩ := hpr
    obtain ⟨_hr, _hninf, _hnseen, _hnow, hinf, hseen⟩ := hsend
    rw [hinf, hseen]
    rcases hm with hm | hm
    · left; exact Finset.mem_insert_of_mem hm
    · right; exact hm
  · obtain ⟨_hi, _hval, _hbpos, _hbcur, _hfirst, _hprop, _hparseen, _hparcast, _hlong, hsend⟩ := hv
    obtain ⟨_hr, _hninf, _hnseen, _hnow, hinf, hseen⟩ := hsend
    rw [hinf, hseen]
    rcases hm with hm | hm
    · left; exact Finset.mem_insert_of_mem hm
    · right; exact hm
  · obtain ⟨hmem, _hguard, _hnow, hinf, hseen⟩ := hd
    have hsent := sent_eq_deliver n hmem hinf hseen
    exact (hsent m).2 hm

/-- `propCast` is monotone in the sent set. -/
theorem propCast_mono {s s' : St n} (h : sentGrows n s s') {e : ℕ} {b : Blk} :
    propCast n L s e b → propCast n L s' e b := by
  rintro ⟨m, hm, hsrc, hb⟩
  exact ⟨m, h m hm, hsrc, hb⟩

/-- `votersCast` is monotone in the sent set. -/
theorem votersCast_mono {s s' : St n} (h : sentGrows n s s') (b : Blk) :
    votersCast n s b ⊆ votersCast n s' b := by
  intro i hi
  rw [mem_votersCast n] at hi ⊢
  rcases hi with ⟨m, hm, hsrc, hb⟩
  exact ⟨m, h m hm, hsrc, hb⟩

/-- `NotarizedCast` is monotone in the sent set. -/
theorem notarizedCast_mono {s s' : St n} (h : sentGrows n s s') {b : Blk} :
    NotarizedCast n f s b → NotarizedCast n f s' b := by
  intro hN
  exact le_trans hN (Finset.card_le_card (votersCast_mono n h b))

/-- `NotarizedBy` is monotone in the sent set. -/
theorem notarizedBy_mono_send {s s' : St n} (h : sentGrows n s s') {b : Blk} {e : ℕ} :
    NotarizedBy n f s b e → NotarizedBy n f s' b e := by
  rintro ⟨hN, hbep⟩
  exact ⟨notarizedCast_mono n f h hN, hbep⟩

/-- `ChainNotarizedBy` is monotone in the sent set. -/
theorem chainNotarizedBy_mono_send {s s' : St n} (h : sentGrows n s s') {b : Blk} {e : ℕ} :
    ChainNotarizedBy n f s b e → ChainNotarizedBy n f s' b e := by
  intro hc d hd hs
  exact notarizedBy_mono_send n f h (hc d hd hs)

/-! ## Persistence along behaviors -/

/-- `Inv` holds at every point of a `PSpec` behavior. -/
theorem inv_all_of_pspec {e : Behavior (St n)} (h : PSpec n Byz Δ GST f L e) :
    ∀ k, Inv n Byz Δ f L (e k) := by
  intro k
  have h' := spec_entails_inv n Byz Δ GST f L e h k
  simpa [InvState] using h'

/-- `propCast` persists along a behavior. -/
theorem propCast_persist_along {e : Behavior (St n)}
    (hS : ∀ m, StutAction (PNext n Byz Δ GST f L) (vars n) (e m) (e (m + 1)))
    {e' : ℕ} {b : Blk} {k j : ℕ} (hp : propCast n L (e k) e' b) :
    propCast n L (e (k + j)) e' b := by
  induction j with
  | zero => simpa using hp
  | succ j ih =>
      have hmono : propCast n L (e (k + j + 1)) e' b := by
        have hstep : PNext n Byz Δ GST f L (e (k + j)) (e (k + j + 1)) ∨
            (e (k + j + 1)) = e (k + j) := hS (k + j)
        rcases hstep with hnext | hstut
        · exact propCast_mono n L (pnext_sentGrows n Byz Δ GST f L hnext) ih
        · have hstut' : e (k + j + 1) = e (k + j) := hstut
          rw [hstut']; exact ih
      simpa [Nat.add_assoc] using hmono

/-- `ChainNotarizedBy` persists along a behavior. -/
theorem chainNotarizedBy_persist_along {e : Behavior (St n)}
    (hS : ∀ m, StutAction (PNext n Byz Δ GST f L) (vars n) (e m) (e (m + 1)))
    {b : Blk} {e' : ℕ} {k j : ℕ} (hc : ChainNotarizedBy n f (e k) b e') :
    ChainNotarizedBy n f (e (k + j)) b e' := by
  induction j with
  | zero => simpa using hc
  | succ j ih =>
      have hmono : ChainNotarizedBy n f (e (k + j + 1)) b e' := by
        have hstep := hS (k + j)
        rcases hstep with hnext | hstut
        · exact chainNotarizedBy_mono_send n f (pnext_sentGrows n Byz Δ GST f L hnext) ih
        · have hstut' : e (k + j + 1) = e (k + j) := hstut
          rw [hstut']; exact ih
      simpa [Nat.add_assoc] using hmono

/-! ## The completed-window predicate and the final step -/

/-- Every completed epoch `e'` of the window has a chain-notarized proposal. -/
def WindowDone (e0 : ℕ) (s : St n) : Prop :=
  ∀ e' : ℕ, e0 ≤ e' → e' < curEpoch Δ s.now →
    ∃ b : Blk, propCast n L s e' b ∧ ChainNotarizedBy n f s b e'

/-- **The window delivers**: five completed honest-leader epochs finalize. -/
theorem window_finality (hB : Byz.card ≤ f) {s : St n} (hinv : Inv n Byz Δ f L s)
    {e0 : ℕ} (_he0 : 0 < e0) (hW : WindowDone n Δ f L e0 s)
    (hcur : curEpoch Δ s.now = e0 + 5)
    (hL : ∀ e', e0 ≤ e' → e' < e0 + 5 → L e' ∉ Byz) :
    FinalSome n f s := by
  have hlt0 : e0 < curEpoch Δ s.now := by rw [hcur]; omega
  have hlt1 : e0 + 1 < curEpoch Δ s.now := by rw [hcur]; omega
  have hlt2 : e0 + 2 < curEpoch Δ s.now := by rw [hcur]; omega
  have hlt3 : e0 + 3 < curEpoch Δ s.now := by rw [hcur]; omega
  have hlt4 : e0 + 4 < curEpoch Δ s.now := by rw [hcur]; omega
  rcases hW e0 le_rfl hlt0 with ⟨b0, hp0, hc0⟩
  rcases hW (e0 + 1) (by omega) hlt1 with ⟨b1, hp1, hc1⟩
  rcases hW (e0 + 2) (by omega) hlt2 with ⟨b2, hp2, hc2⟩
  rcases hW (e0 + 3) (by omega) hlt3 with ⟨b3, hp3, hc3⟩
  rcases hW (e0 + 4) (by omega) hlt4 with ⟨b4, hp4, hc4⟩
  have hL0 : L e0 ∉ Byz := hL e0 le_rfl (by omega)
  have hL1 : L (e0 + 1) ∉ Byz := hL (e0 + 1) (by omega) (by omega)
  have hL2 : L (e0 + 2) ∉ Byz := hL (e0 + 2) (by omega) (by omega)
  have hL3 : L (e0 + 3) ∉ Byz := hL (e0 + 3) (by omega) (by omega)
  have hL4 : L (e0 + 4) ∉ Byz := hL (e0 + 4) (by omega) (by omega)
  have hb0ne : b0 ≠ [] := ne_nil_of_valid (hinv.propValid e0 b0 hp0 hL0)
  have hb1ne : b1 ≠ [] := ne_nil_of_valid (hinv.propValid (e0 + 1) b1 hp1 hL1)
  have hb2ne : b2 ≠ [] := ne_nil_of_valid (hinv.propValid (e0 + 2) b2 hp2 hL2)
  have hb3ne : b3 ≠ [] := ne_nil_of_valid (hinv.propValid (e0 + 3) b3 hp3 hL3)
  have hb4ne : b4 ≠ [] := ne_nil_of_valid (hinv.propValid (e0 + 4) b4 hp4 hL4)
  have hG01 : b0.length < b1.length :=
    proposal_growth n Byz Δ f L hinv hp0 hp1 hL0 hL1
      ⟨b0, chain_notarized_block n f hc0 hb0ne, le_rfl⟩
  have hG12 : b1.length < b2.length :=
    proposal_growth n Byz Δ f L hinv hp1 hp2 hL1 hL2
      ⟨b1, chain_notarized_block n f hc1 hb1ne, le_rfl⟩
  have hG23 : b2.length < b3.length :=
    proposal_growth n Byz Δ f L hinv hp2 hp3 hL2 hL3
      ⟨b2, chain_notarized_block n f hc2 hb2ne, le_rfl⟩
  have hG34 : b3.length < b4.length :=
    proposal_growth n Byz Δ f L hinv hp3 hp4 hL3 hL4
      ⟨b3, chain_notarized_block n f hc3 hb3ne, le_rfl⟩
  exact ⟨e0 + 2, b2, b3, b4,
    liveness_finality n Byz Δ f L hB hinv hp0 hp1 hp2 hp3 hp4 hL0 hL1 hL2 hL3 hL4
      hG01 hG12 hG23 hG34 hc2 hc3 hc4⟩

/-! ## The honest-timing assumptions -/

/-- The epoch clock eventually advances past epoch `e`. -/
def ClockAssumption (e : ℕ) : Pred (St n) :=
  leadsTo (statePred {s | curEpoch Δ s.now = e})
    (statePred {s | curEpoch Δ s.now = e + 1})

/-- The honest leader of epoch `e` proposes before the epoch passes. -/
def ProposeAssumption (e : ℕ) : Pred (St n) :=
  leadsTo (statePred {s | curEpoch Δ s.now = e ∧ ∀ b : Blk, ¬ propCast n L s e b})
    (statePred {s | curEpoch Δ s.now = e ∧ ∃ b : Blk, propCast n L s e b})

/-- Honest nodes vote and delivery chain-notarizes the proposal within the epoch. -/
def VoteAssumption (e : ℕ) : Pred (St n) :=
  leadsTo (statePred {s | curEpoch Δ s.now = e ∧ ∃ b : Blk, propCast n L s e b})
    (statePred {s | curEpoch Δ s.now = e ∧
      ∃ b : Blk, propCast n L s e b ∧ ChainNotarizedBy n f s b e})

/-- The honest-timing spec: the protocol plus per-epoch clock/propose/vote
assumptions. -/
def H : Pred (St n) :=
  tlaAnd (PSpec n Byz Δ GST f L)
    (tlaAnd (fun e => ∀ e' : ℕ, ClockAssumption n Δ e' e)
      (tlaAnd (fun e => ∀ e' : ℕ, ProposeAssumption n Δ L e' e)
        (fun e => ∀ e' : ℕ, VoteAssumption n Δ f L e' e)))

/-! ## The per-epoch step -/

/-- **One epoch completes**: from `curEpoch = e'` (with `Inv`), the
propose/vote/clock assumptions deliver `curEpoch = e'+1` with the epoch's
proposal chain-notarized. -/
theorem epoch_step {e' : ℕ} {e : Behavior (St n)} (hH : H n Byz Δ GST f L e) :
    leadsTo (statePred {s | Inv n Byz Δ f L s ∧ curEpoch Δ s.now = e'})
      (statePred {s | Inv n Byz Δ f L s ∧ curEpoch Δ s.now = e' + 1 ∧
        ∃ b : Blk, propCast n L s e' b ∧ ChainNotarizedBy n f s b e'}) e := by
  have hspec : PSpec n Byz Δ GST f L e := hH.1
  have hClock : ∀ e'', ClockAssumption n Δ e'' e := hH.2.1
  have hPropose : ∀ e'', ProposeAssumption n Δ L e'' e := hH.2.2.1
  have hVote : ∀ e'', VoteAssumption n Δ f L e'' e := hH.2.2.2
  have hS : ∀ m, StutAction (PNext n Byz Δ GST f L) (vars n) (e m) (e (m + 1)) :=
    fun m => stutAlways_step hspec.2
  have hInvAll : ∀ m, Inv n Byz Δ f L (e m) := inv_all_of_pspec n Byz Δ GST f L hspec
  intro k hp
  rcases hp with ⟨_hInv0, hcur⟩
  have hcur' : curEpoch Δ (e k).now = e' := by simpa using hcur
  by_cases hnone : ∀ b : Blk, ¬ propCast n L (e k) e' b
  · -- absent: the propose assumption fires
    have hP : curEpoch Δ (e k).now = e' ∧ ∀ b : Blk, ¬ propCast n L (e k) e' b :=
      ⟨hcur', hnone⟩
    rcases (hPropose e' k (by simpa using hP)) with ⟨j1, hj1⟩
    have hj1' : curEpoch Δ (e (k + j1)).now = e' ∧
        ∃ b : Blk, propCast n L (e (k + j1)) e' b := by simpa using hj1
    rcases hj1' with ⟨hj1cur, hj1prop⟩
    rcases hj1prop with ⟨b, hpb⟩
    have hVoteP : curEpoch Δ (e (k + j1)).now = e' ∧
        ∃ b : Blk, propCast n L (e (k + j1)) e' b := ⟨hj1cur, ⟨b, hpb⟩⟩
    rcases (hVote e' (k + j1) (by simpa using hVoteP)) with ⟨j2, hj2⟩
    have hj2' : curEpoch Δ (e (k + j1 + j2)).now = e' ∧
        ∃ b : Blk, propCast n L (e (k + j1 + j2)) e' b ∧
          ChainNotarizedBy n f (e (k + j1 + j2)) b e' := by simpa using hj2
    rcases hj2' with ⟨hj2cur, hj2fact⟩
    rcases hj2fact with ⟨b', hpb', hcb'⟩
    rcases (hClock e' (k + j1 + j2) (by simpa using hj2cur)) with ⟨j3, hj3⟩
    have hj3cur : curEpoch Δ (e (k + j1 + j2 + j3)).now = e' + 1 := by simpa using hj3
    refine ⟨j1 + j2 + j3, ?_⟩
    have hpbpers : propCast n L (e (k + j1 + j2 + j3)) e' b' :=
      propCast_persist_along n Byz Δ GST f L hS (k := k + j1 + j2) (j := j3) (by simpa using hpb')
    have hcbpers : ChainNotarizedBy n f (e (k + j1 + j2 + j3)) b' e' :=
      chainNotarizedBy_persist_along n Byz Δ GST f L hS (k := k + j1 + j2) (j := j3) (by simpa using hcb')
    refine ⟨?_, ?_, ?_⟩
    · simpa [Nat.add_assoc] using (hInvAll (k + (j1 + j2 + j3)))
    · simpa [Nat.add_assoc] using hj3cur
    · refine ⟨b', ?_, ?_⟩
      · have hidx : k + (j1 + j2 + j3) = k + j1 + j2 + j3 := by omega
        simpa [hidx] using hpbpers
      · have hidx : k + (j1 + j2 + j3) = k + j1 + j2 + j3 := by omega
        simpa [hidx] using hcbpers
  · -- already present
    have hnone' : ∃ b : Blk, propCast n L (e k) e' b := by
      simpa [not_forall, not_not] using hnone
    rcases hnone' with ⟨b, hpb⟩
    have hVoteP : curEpoch Δ (e k).now = e' ∧ ∃ b : Blk, propCast n L (e k) e' b :=
      ⟨hcur', ⟨b, hpb⟩⟩
    rcases (hVote e' k (by simpa using hVoteP)) with ⟨j2, hj2⟩
    have hj2' : curEpoch Δ (e (k + j2)).now = e' ∧
        ∃ b : Blk, propCast n L (e (k + j2)) e' b ∧
          ChainNotarizedBy n f (e (k + j2)) b e' := by simpa using hj2
    rcases hj2' with ⟨hj2cur, hj2fact⟩
    rcases hj2fact with ⟨b', hpb', hcb'⟩
    rcases (hClock e' (k + j2) (by simpa using hj2cur)) with ⟨j3, hj3⟩
    have hj3cur : curEpoch Δ (e (k + j2 + j3)).now = e' + 1 := by simpa using hj3
    refine ⟨j2 + j3, ?_⟩
    have hpbpers : propCast n L (e (k + j2 + j3)) e' b' :=
      propCast_persist_along n Byz Δ GST f L hS (k := k + j2) (j := j3) (by simpa using hpb')
    have hcbpers : ChainNotarizedBy n f (e (k + j2 + j3)) b' e' :=
      chainNotarizedBy_persist_along n Byz Δ GST f L hS (k := k + j2) (j := j3) (by simpa using hcb')
    refine ⟨?_, ?_, ?_⟩
    · simpa [Nat.add_assoc] using (hInvAll (k + (j2 + j3)))
    · simpa [Nat.add_assoc] using hj3cur
    · refine ⟨b', ?_, ?_⟩
      · have hidx : k + (j2 + j3) = k + j2 + j3 := by omega
        simpa [hidx] using hpbpers
      · have hidx : k + (j2 + j3) = k + j2 + j3 := by omega
        simpa [hidx] using hcbpers

/-! ## The window countdown -/

/-- The remaining-window rank arithmetic. -/
theorem window_rank_sub (e0 k : ℕ) (hk : k ≤ 5) (hkpos : 0 < k) :
    (e0 + 5 - k) + 1 = e0 + 5 - (k - 1) := by
  omega

/-- From `k` epochs remaining in the window, the window completes. -/
theorem window_progress (e0 : ℕ) (k : ℕ) (hk : k ≤ 5) {e : Behavior (St n)}
    (hH : H n Byz Δ GST f L e) :
    leadsTo (statePred {s | WindowDone n Δ f L e0 s ∧ curEpoch Δ s.now = e0 + 5 - k})
      (statePred {s | WindowDone n Δ f L e0 s ∧ curEpoch Δ s.now = e0 + 5}) e := by
  have hspec : PSpec n Byz Δ GST f L e := hH.1
  have hS : ∀ m, StutAction (PNext n Byz Δ GST f L) (vars n) (e m) (e (m + 1)) :=
    fun m => stutAlways_step hspec.2
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro n' hp
      rcases hp with ⟨hW, hcur⟩
      by_cases hk0 : k = 0
      · subst k
        refine ⟨0, ?_⟩
        have hW' : WindowDone n Δ f L e0 (e n') := by simpa using hW
        have hcur' : curEpoch Δ (e n').now = e0 + 5 := by simpa using hcur
        simpa using ⟨hW', hcur'⟩
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        let e' := e0 + 5 - k
        have hcur' : curEpoch Δ (e n').now = e' := by simpa [e'] using hcur
        have hInv' : Inv n Byz Δ f L (e n') := inv_all_of_pspec n Byz Δ GST f L hspec n'
        have hstep := epoch_step n Byz Δ GST f L (e' := e') hH
        rcases (hstep n' (by simpa using ⟨hInv', hcur'⟩)) with ⟨j, hj⟩
        rcases hj with ⟨_hInvj, hcurj, hfact⟩
        have hcurj' : curEpoch Δ (e (n' + j)).now = e' + 1 := by simpa using hcurj
        have hfact' : ∃ b : Blk, propCast n L (e (n' + j)) e' b ∧
            ChainNotarizedBy n f (e (n' + j)) b e' := by simpa using hfact
        have hW' : WindowDone n Δ f L e0 (e (n' + j)) := by
          intro e'' he0'' hlt''
          have hltj : e'' < e' + 1 := by
            rw [hcurj'] at hlt''
            exact hlt''
          by_cases hlt : e'' < e'
          · have hlt0 : e'' < curEpoch Δ (e n').now := by simpa [hcur'] using hlt
            rcases hW e'' he0'' (by simpa using hlt0) with ⟨b, hpb, hcb⟩
            refine ⟨b, ?_, ?_⟩
            · exact propCast_persist_along n Byz Δ GST f L hS (k := n') (j := j) (by simpa using hpb)
            · exact chainNotarizedBy_persist_along n Byz Δ GST f L hS (k := n') (j := j) (by simpa using hcb)
          · have heq : e'' = e' := by
              have hge : e' ≤ e'' := le_of_not_gt hlt
              exact le_antisymm (Nat.le_of_lt_succ hltj) hge
            subst e''
            exact hfact'
        have hrank : curEpoch Δ (e (n' + j)).now = e0 + 5 - (k - 1) := by
          have hsub : e' + 1 = e0 + 5 - (k - 1) := by
            simpa [e'] using window_rank_sub e0 k hk hkpos
          rw [hsub] at hcurj'
          exact hcurj'
        have hkm : k - 1 < k := by omega
        have hkm5 : k - 1 ≤ 5 := by omega
        rcases (ih (k - 1) hkm hkm5 (n' + j) (by simpa using ⟨hW', hrank⟩)) with ⟨j', hj'⟩
        refine ⟨j + j', ?_⟩
        have hidx : n' + (j + j') = n' + j + j' := by omega
        simpa [hidx] using hj'

/-! ## The liveness theorem -/

/-- **Streamlet liveness (Theorem 13, abstracted)**: under the honest-timing
spec, from the start of a 5-epoch honest-leader window some block is
eventually final. -/
theorem liveness_spec (hB : Byz.card ≤ f) (e0 : ℕ) (he0 : 0 < e0)
    (hL : ∀ e', e0 ≤ e' → e' < e0 + 5 → L e' ∉ Byz) :
    Entails (H n Byz Δ GST f L)
      (leadsTo (statePred {s | curEpoch Δ s.now = e0})
        (statePred {s | FinalSome n f s})) := by
  intro e hH n' hp
  have hspec : PSpec n Byz Δ GST f L e := hH.1
  have hInvAll : ∀ m, Inv n Byz Δ f L (e m) := inv_all_of_pspec n Byz Δ GST f L hspec
  have hcur0 : curEpoch Δ (e n').now = e0 := by simpa using hp
  have hW : WindowDone n Δ f L e0 (e n') := by
    intro e'' he0'' hlt''
    have hlt0 : e'' < e0 := by rw [hcur0] at hlt''; exact hlt''
    exact (not_lt_of_ge he0'' hlt0).elim
  have hrank : curEpoch Δ (e n').now = e0 + 5 - 5 := by
    rw [hcur0]
    exact (Nat.add_sub_cancel e0 5).symm
  have h5 := window_progress n Byz Δ GST f L e0 5 (by omega) hH
  rcases (h5 n' (by simpa using ⟨hW, hrank⟩)) with ⟨j, hj⟩
  rcases hj with ⟨hW', hcur'⟩
  have hW'' : WindowDone n Δ f L e0 (e (n' + j)) := by simpa using hW'
  have hcur'' : curEpoch Δ (e (n' + j)).now = e0 + 5 := by simpa using hcur'
  refine ⟨j, ?_⟩
  have hfin : FinalSome n f (e (n' + j)) :=
    window_finality n Byz Δ f L hB (hInvAll (n' + j)) he0 hW'' hcur'' hL
  simpa using hfin
end Bft.Examples.StreamletTemporal
