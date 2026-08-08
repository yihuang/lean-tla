import TlaDsl.Basic
import TlaDsl.Notation
import TlaDsl.RelRank
import TlaDsl.Tactic
import Mathlib.Tactic.FinCases

set_option maxHeartbeats 4000000

open scoped Tla

/-! # Bounded cascade: stable schedulers (Rule 8/10)

The paper's §3.3 bounded-cascade variant (Fig. 3 plus the bounded
paragraph): two queues in cascade, and queue 2 holds at most one timestamp,
so `poll₁` *blocks* while queue 2 is non-empty. The scheduler prioritizes
the action that unblocks the other:

* `ψ₀ = ¬∃τ ∈ queue₂, τ ≤ t` — queue 2 has no message before `t`, so
  `poll₁` may proceed;
* `ψ₁ = ∃τ ∈ queue₂, τ ≤ t` — queue 2 holds a message before `t`, so
  `poll₂` must fire.

The schedulers are complementary (`ψ₀ = ¬ψ₁`), and the ranking is the
paper's Fig. 3 pair:

* `δ₀ = {τ | τ ∈ pend₁ ∧ τ ≤ t}` — messages before `t` in queue 1;
* `δ₁ = {τ | (τ ∈ pend₁ ∨ τ ∈ queue₂) ∧ τ ≤ t}` — messages before `t` in
  *either* queue, so moving a timestamp from queue 1 to queue 2 does not
  increase it.

While queue 2 holds an early message, `δ₁` is required — `poll₂` removes
it; otherwise `δ₀` is required — `poll₁` moves `t` (or an earlier message)
into queue 2. The conclusion is
`(□◇ poll₁) ∧ (□◇ poll₂) ⊢ sent₁(t) ↝ recv₂(t)`.
-/

namespace TlaDsl.Examples.BoundedCascade

/-- Two queues in cascade; queue 2 holds at most one timestamp (capacity
one, so `poll₁` blocks while it is non-empty). -/
structure St where
  pend1 : Finset Nat
  last : Nat
  sent1 : Finset Nat
  queue2 : Finset Nat
  recv2 : Finset Nat

/-- Send a message (timestamps strictly increase). -/
def Send (u : Nat) : Tla.Action St :=
  fun s s' =>
    u > s.last ∧ s'.pend1 = insert u s.pend1 ∧ s'.last = u ∧
      s'.sent1 = insert u s.sent1 ∧ s'.queue2 = s.queue2 ∧ s'.recv2 = s.recv2

/-- Poll the earliest message of queue 1 into queue 2 (blocked while queue 2
is non-empty — the bounded capacity). -/
def Poll1 : Tla.Action St :=
  fun s s' =>
    ∃ h : s.pend1.Nonempty,
      s.queue2 = ∅ ∧ s'.pend1 = s.pend1.erase (Finset.min' s.pend1 h) ∧
        s'.queue2 = insert (Finset.min' s.pend1 h) ∅ ∧ s'.last = s.last ∧
        s'.sent1 = s.sent1 ∧ s'.recv2 = s.recv2

/-- Queue 2 delivers its (single) message. -/
def Poll2 : Tla.Action St :=
  fun s s' =>
    ∃ h : s.queue2.Nonempty,
      s'.queue2 = ∅ ∧ s'.recv2 = insert (Finset.min' s.queue2 h) s.recv2 ∧
        s'.pend1 = s.pend1 ∧ s'.last = s.last ∧ s'.sent1 = s.sent1

/-- A step: send, poll queue 1, or deliver queue 2. -/
def Next : Tla.Action St :=
  fun s s' => (∃ u : Nat, Send u s s') ∨ Poll1 s s' ∨ Poll2 s s'

/-- Everything starts empty. -/
def Init : Tla.StatePred St :=
  fun s => s.pend1 = ∅ ∧ s.last = 0 ∧ s.sent1 = ∅ ∧ s.queue2 = ∅ ∧ s.recv2 = ∅

/-! ## The rankings and schedulers -/

/-- `δ₀`: pending messages in queue 1 with timestamp `≤ t`. -/
def Delta0 (t : Nat) (s : St) : Finset Nat :=
  s.pend1.filter (fun τ => τ ≤ t)

/-- `δ₁`: messages with timestamp `≤ t` in either queue. -/
def Delta1 (t : Nat) (s : St) : Finset Nat :=
  (s.pend1 ∪ s.queue2).filter (fun τ => τ ≤ t)

/-- The two ranking components. -/
def deltas (t : Nat) (i : Fin 2) (s : St) : Finset Nat :=
  if i.val = 0 then Delta0 t s else Delta1 t s

/-- The schedulers: `ψ₀ = no message `≤ t` in queue 2` (poll₁ may
proceed), `ψ₁ = some message `≤ t` in queue 2` (poll₂ must fire). -/
def psis (t : Nat) (i : Fin 2) (s : St) : Prop :=
  if i.val = 0 then ¬ ∃ τ : Nat, τ ∈ s.queue2 ∧ τ ≤ t
  else ∃ τ : Nat, τ ∈ s.queue2 ∧ τ ≤ t

/-- The justice actions: `r₀ = poll₁`, `r₁ = poll₂`. -/
def rjs : Fin 2 → Tla.Action St :=
  fun i => if i.val = 0 then Poll1 else Poll2

/-! ## The inductive invariant -/

/-- Sent timestamps are bounded by the shared counter, the pipeline holds
for `t`, queue 2 holds at most one message, a message is never in both
queues (the paper's safety invariant), and both queues are timestamp-bounded. -/
def Inv (t : Nat) (s : St) : Prop :=
  (∀ τ : Nat, τ ∈ s.sent1 → τ ≤ s.last) ∧
  (t ∈ s.sent1 → t ∈ s.recv2 ∨ t ∈ s.pend1 ∨ t ∈ s.queue2) ∧
  (s.queue2.card ≤ 1) ∧
  (∀ τ : Nat, τ ∈ s.pend1 → τ ∉ s.queue2) ∧
  (∀ τ : Nat, τ ∈ s.queue2 → τ ≤ s.last) ∧
  (∀ τ : Nat, τ ∈ s.pend1 → τ ≤ s.last)

/-- `Inv t` is preserved by every step of `Next`. -/
theorem inv_step (t : Nat) (s s' : St) (h : Inv t s) (hstep : Next s s') : Inv t s' := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
  rcases hstep with hsend | hrest
  · -- a send
    rcases hsend with ⟨u, hsend'⟩
    rcases hsend' with ⟨hu, hp1', hl', hs1', hq2', hr2'⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro τ hτ
      rw [hs1'] at hτ
      rcases Finset.mem_insert.mp hτ with hτu | hτ1
      · rw [hτu, hl']
      · rw [hl']
        exact le_trans (h1 τ hτ1) (Nat.le_of_lt hu)
    · intro ht
      rw [hs1'] at ht
      rcases Finset.mem_insert.mp ht with htt | hts
      · right
        left
        rw [hp1']
        exact Finset.mem_insert.mpr (Or.inl htt)
      · rcases h2 hts with hr | hp | hq
        · left
          rw [hr2']
          exact hr
        · right
          left
          rw [hp1']
          exact Finset.mem_insert.mpr (Or.inr hp)
        · right
          right
          rw [hq2']
          exact hq
    · rw [hq2']
      exact h3
    · intro τ hτ
      rw [hp1'] at hτ
      rcases Finset.mem_insert.mp hτ with hτu | hτ1
      · rw [hτu]
        intro hq
        rw [hq2'] at hq
        have hle : u ≤ s.last := h5 u hq
        omega
      · intro hq
        rw [hq2'] at hq
        exact h4 τ hτ1 hq
    · intro τ hτ
      rw [hq2'] at hτ
      rw [hl']
      exact le_trans (h5 τ hτ) (Nat.le_of_lt hu)
    · intro τ hτ
      rw [hp1'] at hτ
      rcases Finset.mem_insert.mp hτ with hτu | hτ1
      · rw [hτu, hl']
      · rw [hl']
        exact le_trans (h6 τ hτ1) (Nat.le_of_lt hu)
  · rcases hrest with hp1 | hp2
    · -- poll₁
      rcases hp1 with ⟨h, hq2, hp1', hq2', hl', hs1', hr2'⟩
      let m := Finset.min' s.pend1 h
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro τ hτ
        rw [hs1'] at hτ
        rw [hl']
        exact h1 τ hτ
      · intro ht
        rw [hs1'] at ht
        rcases h2 ht with hr | hp | hq
        · left
          rw [hr2']
          exact hr
        · right
          by_cases htm : t = m
          · right
            rw [hq2', htm]
            exact Finset.mem_insert_self m ∅
          · left
            rw [hp1']
            exact Finset.mem_erase.mpr ⟨htm, hp⟩
        · rw [hq2] at hq
          exact False.elim (Finset.notMem_empty t hq)
      · rw [hq2']
        simp
      · intro τ hτ
        rw [hp1'] at hτ
        have hτ1 : τ ∈ s.pend1 := (Finset.mem_erase.mp hτ).2
        have hτne : τ ≠ m := (Finset.mem_erase.mp hτ).1
        intro hq
        rw [hq2'] at hq
        exact hτne (by simpa using hq)
      · intro τ hτ
        rw [hq2'] at hτ
        have hτm : τ = m := by simpa using hτ
        rw [hτm, hl']
        exact h6 m (Finset.min'_mem s.pend1 h)
      · intro τ hτ
        rw [hp1'] at hτ
        rw [hl']
        exact h6 τ (Finset.mem_erase.mp hτ).2
    · -- poll₂
      rcases hp2 with ⟨h, hq2', hr2', hp1', hl', hs1'⟩
      let m := Finset.min' s.queue2 h
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro τ hτ
        rw [hs1'] at hτ
        rw [hl']
        exact h1 τ hτ
      · intro ht
        rw [hs1'] at ht
        rcases h2 ht with hr | hp | hq
        · left
          rw [hr2']
          exact Finset.mem_insert.mpr (Or.inr hr)
        · right
          left
          rw [hp1']
          exact hp
        · left
          have htmem : t ∈ s.queue2 := hq
          have hmmem : m ∈ s.queue2 := Finset.min'_mem s.queue2 h
          have htm : t = m := (Finset.card_le_one.1 h3) t htmem m hmmem
          rw [hr2', htm]
          exact Finset.mem_insert_self m s.recv2
      · rw [hq2']
        simp
      · intro τ hτ hq
        rw [hq2'] at hq
        exact Finset.notMem_empty τ hq
      · intro τ hτ
        rw [hq2'] at hτ
        exact False.elim (Finset.notMem_empty τ hτ)
      · intro τ hτ
        rw [hp1'] at hτ
        rw [hl']
        exact h6 τ hτ

/-- `Inv t` holds at every reachable state. -/
theorem inv_inductive (t : Nat) (e : Tla.Behavior St)
    (hInit : Init (e 0)) (hNext : ∀ m, Next (e m) (e (m + 1))) :
    ∀ k, Inv t (e k) := by
  intro k
  induction k with
  | zero =>
      rcases hInit with ⟨hp10, hl0, hs10, hq20, hr20⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro τ hτ
        rw [hs10] at hτ
        exact False.elim ((Finset.notMem_empty τ) hτ)
      · intro ht
        rw [hs10] at ht
        exact False.elim ((Finset.notMem_empty t) ht)
      · rw [hq20]
        simp
      · intro τ hτ hq
        rw [hp10] at hτ
        exact False.elim ((Finset.notMem_empty τ) hτ)
      · intro τ hτ
        rw [hq20] at hτ
        exact False.elim ((Finset.notMem_empty τ) hτ)
      · intro τ hτ
        rw [hp10] at hτ
        exact False.elim ((Finset.notMem_empty τ) hτ)
  | succ k ih =>
      exact inv_step t (e k) (e (k + 1)) ih (hNext k)

/-! ## The liveness theorem (Rule 10 instance with stable schedulers) -/

/-- The bounded-cascade spec: init, next, and the two fairness
assumptions. -/
def Spec : Tla.Pred St :=
  Tla.tlaAnd (Tla.statePred Init)
    (Tla.tlaAnd (Tla.always (Tla.actionPred Next))
      (Tla.tlaAnd (Tla.always (Tla.eventually (Tla.actionPred Poll1)))
        (Tla.always (Tla.eventually (Tla.actionPred Poll2)))))

/-- `(□◇ poll₁) ∧ (□◇ poll₂) ⊢ sent₁(t) ↝ recv₂(t)` for a message `t`,
via the two-component lexicographic ranking `(δ₀, δ₁)` with the
complementary schedulers `ψ₀ = ¬ψ₁` that prioritize the action unblocking
the other. -/
theorem cascade_liveness (t : Nat) :
    Tla.Entails Spec
      (Tla.leadsTo (Tla.statePred (fun s => t ∈ s.sent1))
        (Tla.statePred (fun s => t ∈ s.recv2))) := by
  tla_rel_rank_lex
    (fun s => t ∈ s.sent1), (fun s => t ∈ s.recv2),
    (fun s => t ∈ s.sent1 ∧ (t ∈ s.pend1 ∨ t ∈ s.queue2)),
    (deltas t), (psis t), rjs, Spec
  · -- S1: a sent message is received, in queue 1, or in queue 2
    tla_spec_split
    intro k hp
    have hIk := inv_inductive t e hInit0 hNextAll k
    rcases hIk.2.1 hp with hr | hp1 | hq
    · left
      exact Tla.eventually_imp (Tla.statePred (fun s => t ∈ s.recv2)) e k
        (by simpa [Tla.statePred, Cslib.ωSequence.drop] using hr)
    · right
      exact ⟨hp, Or.inl hp1⟩
    · right
      exact ⟨hp, Or.inr hq⟩
  · -- L2
    tla_spec_split
    intro k hφ
    have hIk := inv_inductive t e hInit0 hNextAll k
    rcases hIk with ⟨h1, h2, h3, h4, h5, h6⟩
    rcases hNextAll k with hsend | hrest
    · -- a send
      rcases hsend with ⟨u, hsend'⟩
      rcases hsend' with ⟨hu, hp1', hl', hs1', hq2s, hr2'⟩
      right
      constructor
      · change t ∈ (e (k + 1)).sent1 ∧ (t ∈ (e (k + 1)).pend1 ∨ t ∈ (e (k + 1)).queue2)
        constructor
        · rw [hs1']
          exact Finset.mem_insert.mpr (Or.inr hφ.1)
        · rcases hφ.2 with hpa | hq
          · left
            rw [hp1']
            exact Finset.mem_insert.mpr (Or.inr hpa)
          · right
            rw [hq2s]
            exact hq
      · constructor
        · intro i _hnp
          fin_cases i
          · have htl : t ≤ (e k).last := h1 t hφ.1
            have hut : u > t := lt_of_le_of_lt htl hu
            intro x hx
            simp [deltas, Delta0] at hx ⊢
            constructor
            · have hxne : x ≠ u := ne_of_lt (lt_of_le_of_lt hx.2 hut)
              rw [hp1'] at hx
              exact (Finset.mem_insert.mp hx.1).resolve_left hxne
            · exact hx.2
          · have htl : t ≤ (e k).last := h1 t hφ.1
            have hut : u > t := lt_of_le_of_lt htl hu
            intro x hx
            simp [deltas, Delta1] at hx ⊢
            constructor
            · rcases hx.1 with hx1 | hx2
              · rw [hp1'] at hx1
                rcases Finset.mem_insert.mp hx1 with hxu | hx1'
                · exact False.elim ((ne_of_lt (lt_of_le_of_lt hx.2 hut)) hxu)
                · exact Or.inl hx1'
              · rw [hq2s] at hx2
                exact Or.inr hx2
            · exact hx.2
        · constructor
          · intro i
            fin_cases i
            · intro _hreq hR
              exfalso
              rcases hR with ⟨h, hq2, _hp1'', hq2p, _hl'', _hs1'', _hr2''⟩
              have hc : insert (Finset.min' (e k).pend1 h) (∅ : Finset Nat) = (∅ : Finset Nat) := by
                rw [← hq2p, hq2s, hq2]
              have hm : Finset.min' (e k).pend1 h ∈ (∅ : Finset Nat) := by
                rw [← hc]
                simp
              exact (Finset.notMem_empty (Finset.min' (e k).pend1 h)) hm
            · intro _hreq hR
              exfalso
              rcases hR with ⟨h, hq2p', _hr2'', _hp1'', _hl'', _hs1''⟩
              have hq2old : (e k).queue2 = ∅ := by
                rw [← hq2s, hq2p']
              rw [hq2old] at h
              simp at h
          · intro i
            fin_cases i
            · intro hreq _hnr hex
              rcases hex with ⟨τ, hτ, hτle⟩
              rw [hq2s] at hτ
              exact hreq.1 ⟨τ, hτ, hτle⟩
            · intro hreq _hnr
              rcases hreq.1 with ⟨τ, hτ, hτle⟩
              refine ⟨τ, ?_, hτle⟩
              rw [hq2s]
              exact hτ
    · rcases hrest with hp1step | hp2step
      · -- poll₁
        rcases hp1step with ⟨h, hq2, hp1', hq2p, hl', hs1', hr2'⟩
        let m := Finset.min' (e k).pend1 h
        right
        constructor
        · change t ∈ (e (k + 1)).sent1 ∧ (t ∈ (e (k + 1)).pend1 ∨ t ∈ (e (k + 1)).queue2)
          constructor
          · rw [hs1']
            exact hφ.1
          · rcases hφ.2 with hpa | hq
            · by_cases htm : t = m
              · right
                rw [hq2p, htm]
                exact Finset.mem_insert_self m ∅
              · left
                rw [hp1']
                exact Finset.mem_erase.mpr ⟨htm, hpa⟩
            · rw [hq2] at hq
              exact False.elim (Finset.notMem_empty t hq)
        · constructor
          · intro i hnp
            fin_cases i
            · intro x hx
              simp [deltas, Delta0] at hx ⊢
              constructor
              · rw [hp1'] at hx
                exact (Finset.erase_subset m (e k).pend1) hx.1
              · exact hx.2
            · -- δ₁ is conserved under ψ₁; poll₁ cannot fire under ψ₁
              have hψ0 : psis t 0 (e k) := by
                simp [psis, hq2]
              exact False.elim (hnp ⟨(0 : Fin 2), ⟨by decide, hψ0⟩⟩)
          · constructor
            · intro i
              fin_cases i
              · intro _hreq hR
                rcases hR with ⟨_h, _hq2', _hp1'', _hq2p', _hl'', _hs1'', _hr2''⟩
                have ht1 : t ∈ (e k).pend1 := by
                  rcases hφ.2 with hpa | hq
                  · exact hpa
                  · rw [hq2] at hq
                    exact False.elim (Finset.notMem_empty t hq)
                have hmle : m ≤ t := (Finset.isLeast_min' (e k).pend1 h).2 ht1
                refine ⟨m, ?_, ?_⟩
                · simp [deltas, Delta0]
                  exact ⟨Finset.min'_mem (e k).pend1 h, hmle⟩
                · intro hδ
                  simp [deltas, Delta0] at hδ
                  rw [hp1'] at hδ
                  exact (Finset.mem_erase.mp hδ.1).1 rfl
              · intro _hreq hR
                exfalso
                rcases hR with ⟨h2', hq2p', _hr2'', _hp1'', _hl'', _hs1''⟩
                have hc : insert m (∅ : Finset Nat) = (∅ : Finset Nat) := by
                  rw [← hq2p, hq2p']
                have hm : m ∈ (∅ : Finset Nat) := by
                  rw [← hc]
                  simp
                exact (Finset.notMem_empty m) hm
            · intro i
              fin_cases i
              · intro _hreq hnr
                exact False.elim (hnr ⟨h, hq2, hp1', hq2p, hl', hs1', hr2'⟩)
              · intro _hreq _hnr
                have ht1 : t ∈ (e k).pend1 := by
                  rcases hφ.2 with hpa | hq
                  · exact hpa
                  · rw [hq2] at hq
                    exact False.elim (Finset.notMem_empty t hq)
                have hmle : m ≤ t := (Finset.isLeast_min' (e k).pend1 h).2 ht1
                refine ⟨m, ?_, hmle⟩
                rw [hq2p]
                exact Finset.mem_insert_self m ∅
      · -- poll₂
        rcases hp2step with ⟨h, hq2p', hr2', hp1', hl', hs1'⟩
        let m := Finset.min' (e k).queue2 h
        by_cases htm : t = m
        · left
          have hrec : t ∈ (e (k + 1)).recv2 := by
            rw [hr2', htm]
            exact Finset.mem_insert_self m (e k).recv2
          have hqev : Tla.eventually (Tla.statePred (fun s => t ∈ s.recv2))
              ((e.drop k).drop 1) := by
            simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              (Tla.eventually_imp (Tla.statePred (fun s => t ∈ s.recv2)) e (k + 1)
                (by simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_comm] using hrec))
          rcases hqev with ⟨t0, ht0⟩
          refine ⟨1 + t0, ?_⟩
          simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using ht0
        · right
          constructor
          · change t ∈ (e (k + 1)).sent1 ∧ (t ∈ (e (k + 1)).pend1 ∨ t ∈ (e (k + 1)).queue2)
            constructor
            · rw [hs1']
              exact hφ.1
            · rcases hφ.2 with hpa | hq
              · left
                rw [hp1']
                exact hpa
              · have htmem : t ∈ (e k).queue2 := hq
                have hmmem : m ∈ (e k).queue2 := Finset.min'_mem (e k).queue2 h
                have hteq : t = m := (Finset.card_le_one.1 h3) t htmem m hmmem
                exact False.elim (htm hteq)
          · constructor
            · intro i _hnp
              fin_cases i
              · intro x hx
                simp [deltas, Delta0] at hx ⊢
                rw [hp1'] at hx
                exact hx
              · intro x hx
                simp [deltas, Delta1] at hx ⊢
                constructor
                · rcases hx.1 with hx1 | hx2
                  · rw [hp1'] at hx1
                    exact Or.inl hx1
                  · rw [hq2p'] at hx2
                    exact False.elim (Finset.notMem_empty x hx2)
                · exact hx.2
            · constructor
              · intro i
                fin_cases i
                · intro _hreq hR
                  exfalso
                  rcases hR with ⟨h1', _hq2, _hp1'', hq2'', _hl'', _hs1'', _hr2''⟩
                  have hc : insert (Finset.min' (e k).pend1 h1') (∅ : Finset Nat) = (∅ : Finset Nat) := by
                    rw [← hq2'', hq2p']
                  have hm : Finset.min' (e k).pend1 h1' ∈ (∅ : Finset Nat) := by
                    rw [← hc]
                    simp
                  exact (Finset.notMem_empty (Finset.min' (e k).pend1 h1')) hm
                · intro hreq _hR
                  rcases hreq.1 with ⟨τ, hτ, hτle⟩
                  have hmle : m ≤ t := le_trans ((Finset.isLeast_min' (e k).queue2 h).2 hτ) hτle
                  refine ⟨m, ?_, ?_⟩
                  · simp [deltas, Delta1]
                    exact ⟨Or.inr (Finset.min'_mem (e k).queue2 h), hmle⟩
                  · intro hδ
                    simp [deltas, Delta1] at hδ
                    rw [hp1', hq2p'] at hδ
                    have hmp : ¬ m ∈ (e k).pend1 := fun hp => h4 m hp
                      (Finset.min'_mem (e k).queue2 h)
                    rcases hδ.1 with hmp' | hem
                    · exact hmp hmp'
                    · exact Finset.notMem_empty m hem
              · intro i
                fin_cases i
                · intro _hreq _hnr hex
                  rcases hex with ⟨τ, hτ, _hτle⟩
                  rw [hq2p'] at hτ
                  exact Finset.notMem_empty τ hτ
                · intro _hreq hnr
                  exact False.elim (hnr ⟨h, hq2p', hr2', hp1', hl', hs1'⟩)
  · -- S3: scheduled justice fires (from the two fairness assumptions)
    tla_spec_split
    intro k _hφ i hψ
    fin_cases i
    · right
      exact hJ1 k
    · right
      exact hJ2 k
  · -- S4: at least one scheduler is on
    intro e _hH k hφ
    right
    by_cases h : ∃ τ : Nat, τ ∈ (e k).queue2 ∧ τ ≤ t
    · exact ⟨(1 : Fin 2), by simpa [psis] using h⟩
    · exact ⟨(0 : Fin 2), by simpa [psis] using h⟩

end TlaDsl.Examples.BoundedCascade
