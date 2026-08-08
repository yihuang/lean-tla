import TlaDsl.Basic
import TlaDsl.Notation
import TlaDsl.RelRank
import TlaDsl.Tactic
import Mathlib.Tactic.FinCases

set_option maxHeartbeats 4000000

open scoped Tla

/-! # Parameterized justice: per-process poll actions (Rule 11)

The paper's §4.2 parameterized-systems slice: an unbounded set of processes
`p : Nat`, each with its own poll action `Poll p` that delivers the earliest
pending message *owned by `p`* (ownership is a fixed function carried in the
state and preserved by every action). Fairness is per process —
`∀p, □◇ Poll p` — which is exactly the infinite conjunction Rule 11 is
designed for.

The tracked message `t` is owned by `s.owner t`, and only `Poll (s.owner t)`
can deliver it, so the scheduler is `ψ(p) = owner t = p ∧ t ∈ pend`: exactly
one parameter instance is scheduled while `t` waits, and the ranking
`δ = {τ | τ ∈ pend ∧ τ ≤ t}` decreases when `Poll (owner t)` fires (the
earliest owned message has timestamp `≤ t` because `t` itself is owned by
`owner t`). The conclusion is `sent t ↝ recv t` under the parameterized
fairness premise.
-/

namespace TlaDsl.Examples.ParamQueue

/-- A queue of messages with per-process ownership; `Poll p` delivers the
earliest pending message owned by `p`. -/
structure St where
  owner : Nat → Nat
  pend : Finset Nat
  last : Nat
  sent : Finset Nat
  recv : Finset Nat

/-- The pending messages owned by `p`. -/
def owned (p : Nat) (s : St) : Finset Nat :=
  s.pend.filter (fun τ => s.owner τ = p)

/-- Send a message (timestamps strictly increase); its owner is fixed by
the state's ownership function. -/
def Send (u : Nat) : Tla.Action St :=
  fun s s' =>
    u > s.last ∧ s'.pend = insert u s.pend ∧ s'.last = u ∧
      s'.sent = insert u s.sent ∧ s'.recv = s.recv ∧ s'.owner = s.owner

/-- Process `p` delivers the earliest pending message it owns. -/
def Poll (p : Nat) : Tla.Action St :=
  fun s s' =>
    ∃ h : (owned p s).Nonempty,
      s'.pend = s.pend.erase (Finset.min' (owned p s) h) ∧
        s'.recv = insert (Finset.min' (owned p s) h) s.recv ∧
        s'.last = s.last ∧ s'.sent = s.sent ∧ s'.owner = s.owner

/-- A step: send, or some process polls. -/
def Next : Tla.Action St :=
  fun s s' => (∃ u : Nat, Send u s s') ∨ ∃ p : Nat, Poll p s s'

/-- Everything starts empty (ownership is unconstrained). -/
def Init : Tla.StatePred St :=
  fun s => s.pend = ∅ ∧ s.last = 0 ∧ s.sent = ∅ ∧ s.recv = ∅

/-! ## The ranking and scheduler -/

/-- `δ`: pending messages with timestamp `≤ t` (one component, `n = 1`). -/
def deltas (t : Nat) (_i : Fin 1) (s : St) : Finset Nat :=
  s.pend.filter (fun τ => τ ≤ t)

/-- The parameterized scheduler: `ψ(p) = owner t = p ∧ t ∈ pend`. -/
def psis (t : Nat) (_i : Fin 1) (p : Nat) (s : St) : Prop :=
  s.owner t = p ∧ t ∈ s.pend

/-- The parameterized justice actions: `r(p) = Poll p`. -/
def rjs (_i : Fin 1) (p : Nat) : Tla.Action St :=
  Poll p

/-! ## The inductive invariant -/

/-- Sent timestamps are bounded by the shared counter, and the pipeline
holds for `t`. -/
def Inv (t : Nat) (s : St) : Prop :=
  (∀ τ : Nat, τ ∈ s.sent → τ ≤ s.last) ∧
  (t ∈ s.sent → t ∈ s.recv ∨ t ∈ s.pend)

/-- `Inv t` is preserved by every step of `Next`. -/
theorem inv_step (t : Nat) (s s' : St) (h : Inv t s) (hstep : Next s s') : Inv t s' := by
  rcases h with ⟨h1, h2⟩
  rcases hstep with hsend | hpoll
  · -- a send
    rcases hsend with ⟨u, hsend'⟩
    rcases hsend' with ⟨hu, hp', hl', hs', hr', ho'⟩
    refine ⟨?_, ?_⟩
    · intro τ hτ
      rw [hs'] at hτ
      rcases Finset.mem_insert.mp hτ with hτu | hτ1
      · rw [hτu, hl']
      · rw [hl']
        exact le_trans (h1 τ hτ1) (Nat.le_of_lt hu)
    · intro ht
      rw [hs'] at ht
      rcases Finset.mem_insert.mp ht with htt | hts
      · right
        rw [hp', htt]
        exact Finset.mem_insert_self u s.pend
      · rcases h2 hts with hr | hp
        · left
          rw [hr']
          exact hr
        · right
          rw [hp']
          exact Finset.mem_insert.mpr (Or.inr hp)
  · -- some process polls
    rcases hpoll with ⟨p, hp'⟩
    rcases hp' with ⟨h, hpoll', hr', hl', hs', ho'⟩
    let m := Finset.min' (owned p s) h
    refine ⟨?_, ?_⟩
    · intro τ hτ
      rw [hs'] at hτ
      rw [hl']
      exact h1 τ hτ
    · intro ht
      rw [hs'] at ht
      rcases h2 ht with hr | hp
      · left
        rw [hr']
        exact Finset.mem_insert.mpr (Or.inr hr)
      · by_cases htm : t = m
        · left
          rw [hr', htm]
          exact Finset.mem_insert_self m s.recv
        · right
          rw [hpoll']
          exact Finset.mem_erase.mpr ⟨htm, hp⟩

/-- `Inv t` holds at every reachable state. -/
theorem inv_inductive (t : Nat) (e : Tla.Behavior St)
    (hInit : Init (e 0)) (hNext : ∀ m, Next (e m) (e (m + 1))) :
    ∀ k, Inv t (e k) := by
  intro k
  induction k with
  | zero =>
      rcases hInit with ⟨hp0, hl0, hs0, hr0⟩
      refine ⟨?_, ?_⟩
      · intro τ hτ
        rw [hs0] at hτ
        exact False.elim ((Finset.notMem_empty τ) hτ)
      · intro ht
        rw [hs0] at ht
        exact False.elim ((Finset.notMem_empty t) ht)
  | succ k ih =>
      exact inv_step t (e k) (e (k + 1)) ih (hNext k)

/-! ## The liveness theorem (Rule 11 instance) -/

/-- The parameterized-queue spec: init, next, and per-owner poll fairness. -/
def Spec : Tla.Pred St :=
  Tla.tlaAnd (Tla.statePred Init)
    (Tla.tlaAnd (Tla.always (Tla.actionPred Next))
      (fun e => ∀ p : Nat, (Tla.always (Tla.eventually (Tla.actionPred (Poll p)))) e))

/-- `(∀p, □◇ Poll p) ⊢ sent(t) ↝ recv(t)` for a message `t`, via the
single ranking `δ = pend ∩ {τ ≤ t}` with the parameterized scheduler
`ψ(p) = owner t = p ∧ t ∈ pend`. -/
theorem param_queue_liveness (t : Nat) :
    Tla.Entails Spec
      (Tla.leadsTo (Tla.statePred (fun s => t ∈ s.sent))
        (Tla.statePred (fun s => t ∈ s.recv))) := by
  tla_rel_rank_param
    (fun s => t ∈ s.sent), (fun s => t ∈ s.recv),
    (fun s => t ∈ s.sent ∧ t ∈ s.pend),
    (deltas t), (psis t), rjs, Spec
  · -- S1: a sent message is received or still pending
    tla_spec_split
    intro k hp
    have hIk := inv_inductive t e hInit0 hNextAll k
    rcases hIk.2 hp with hr | hp'
    · left
      exact Tla.eventually_imp (Tla.statePred (fun s => t ∈ s.recv)) e k
        (by simpa [Tla.statePred, Cslib.ωSequence.drop] using hr)
    · right
      exact ⟨hp, hp'⟩
  · -- P2: the parameterized L2 step
    tla_spec_split
    intro k hφ
    have hIk := inv_inductive t e hInit0 hNextAll k
    rcases hIk with ⟨h1, h2⟩
    rcases hNextAll k with hsend | hpoll
    · -- a send
      rcases hsend with ⟨u, hsend'⟩
      rcases hsend' with ⟨hu, hp', hl', hs', hr', ho'⟩
      right
      constructor
      · change t ∈ (e (k + 1)).sent ∧ t ∈ (e (k + 1)).pend
        constructor
        · rw [hs']
          exact Finset.mem_insert.mpr (Or.inr hφ.1)
        · rw [hp']
          exact Finset.mem_insert.mpr (Or.inr hφ.2)
      · constructor
        · intro p i hnp
          fin_cases i
          have htl : t ≤ (e k).last := h1 t hφ.1
          have hut : u > t := lt_of_le_of_lt htl hu
          intro x hx
          simp [deltas] at hx ⊢
          constructor
          · rw [hp'] at hx
            rcases Finset.mem_insert.mp hx.1 with hxu | hx1
            · exact False.elim ((ne_of_lt (lt_of_le_of_lt hx.2 hut)) hxu)
            · exact hx1
          · exact hx.2
        · constructor
          · intro p i
            fin_cases i
            intro hreq hR
            rcases hR with ⟨h, hpoll', _hr'', _hl'', _hs'', _ho''⟩
            let m := Finset.min' (owned p (e k)) h
            have htowned : t ∈ owned p (e k) :=
              Finset.mem_filter.mpr ⟨hreq.1.2, hreq.1.1⟩
            have hmle : m ≤ t := (Finset.isLeast_min' (owned p (e k)) h).2 htowned
            refine ⟨m, ?_, ?_⟩
            · simp [deltas]
              exact ⟨(Finset.filter_subset (fun τ => (e k).owner τ = p) (e k).pend)
                (Finset.min'_mem (owned p (e k)) h), hmle⟩
            · intro hδ
              simp [deltas] at hδ
              rw [hpoll'] at hδ
              exact (Finset.mem_erase.mp hδ.1).1 rfl
          · intro p i
            fin_cases i
            intro hreq hnr
            constructor
            · rw [ho']
              exact hreq.1.1
            · rw [hp']
              exact Finset.mem_insert.mpr (Or.inr hreq.1.2)
    · -- some process polls
      rcases hpoll with ⟨p', hp'⟩
      rcases hp' with ⟨h, hpoll', hr', hl', hs', ho'⟩
      let m := Finset.min' (owned p' (e k)) h
      by_cases htm : t = m
      · left
        have hrec : t ∈ (e (k + 1)).recv := by
          rw [hr', htm]
          exact Finset.mem_insert_self m (e k).recv
        have hqev : Tla.eventually (Tla.statePred (fun s => t ∈ s.recv))
            ((e.drop k).drop 1) := by
          simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (Tla.eventually_imp (Tla.statePred (fun s => t ∈ s.recv)) e (k + 1)
              (by simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_comm] using hrec))
        rcases hqev with ⟨t0, ht0⟩
        refine ⟨1 + t0, ?_⟩
        simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using ht0
      · right
        constructor
        · change t ∈ (e (k + 1)).sent ∧ t ∈ (e (k + 1)).pend
          constructor
          · rw [hs']
            exact hφ.1
          · rw [hpoll']
            exact Finset.mem_erase.mpr ⟨htm, hφ.2⟩
        · constructor
          · intro p i hnp
            fin_cases i
            intro x hx
            simp [deltas] at hx ⊢
            constructor
            · rw [hpoll'] at hx
              exact (Finset.erase_subset m (e k).pend) hx.1
            · exact hx.2
          · constructor
            · intro p i
              fin_cases i
              intro hreq hR
              rcases hR with ⟨h0, hpoll'', _hr'', _hl'', _hs'', _ho''⟩
              let m0 := Finset.min' (owned p (e k)) h0
              have htowned : t ∈ owned p (e k) :=
                Finset.mem_filter.mpr ⟨hreq.1.2, hreq.1.1⟩
              have hmle : m0 ≤ t := (Finset.isLeast_min' (owned p (e k)) h0).2 htowned
              refine ⟨m0, ?_, ?_⟩
              · simp [deltas]
                exact ⟨(Finset.filter_subset (fun τ => (e k).owner τ = p) (e k).pend)
                  (Finset.min'_mem (owned p (e k)) h0), hmle⟩
              · intro hδ
                simp [deltas] at hδ
                rw [hpoll''] at hδ
                exact (Finset.mem_erase.mp hδ.1).1 rfl
            · intro p i
              fin_cases i
              intro hreq hnr
              constructor
              · rw [ho']
                exact hreq.1.1
              · rw [hpoll']
                exact Finset.mem_erase.mpr ⟨htm, hreq.1.2⟩
  · -- P3: a scheduled justice action eventually fires
    tla_spec_split
    intro k _hφ p i hψ
    fin_cases i
    right
    exact hJ1 p k
  · -- P4: the tracked message's owner is always scheduled while pending
    intro e _hH k hφ
    right
    exact ⟨(e k).owner t, ⟨(0 : Fin 1), ⟨rfl, hφ.2⟩⟩⟩

end TlaDsl.Examples.ParamQueue
