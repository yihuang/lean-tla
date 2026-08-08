import TlaDsl.Basic
import TlaDsl.Notation
import TlaDsl.Coercion
import TlaDsl.RelRank
import TlaDsl.Tactic
import Mathlib.Tactic.FinCases

set_option maxHeartbeats 4000000

open scoped Tla

/-! # Memory pipeline with a reorder buffer (Rule 11, global preemption)

The CPU-memory-subsystem-shaped case study (paper §4): unbounded memory
controllers `c : Nat`, each with a queue of pending operations; operations
are *completed* out-of-order by their controllers and *retired* in-order at
the reorder buffer (by timestamp). Fairness is per controller —
`∀c, □◇ Complete c` — plus the retire action `□◇ Retire`.

The tracked operation `t` is retired once every operation `≤ t` has been
completed (the reorder buffer retires in timestamp order). The two-component
ranking:

* `δ₀ = {op ≤ t | op pending at some controller}` — high priority: reduced
  when the controller holding a pending `op ≤ t` completes it;
* `δ₁ = {op ≤ t | op completed but not retired}` — low priority: reduced by
  `Retire`.

The schedulers are `ψ₀(c) = ∃ op ≤ t pending at c` and `ψ₁(c) = t ∈ done`.
Retire (`δ₁`) is preempted whenever *any* controller still has a pending
`op ≤ t` — the *global* preemption of `rel_rank_param_global`: while any
controller can still add a completion, `δ₁` may grow, so it must not be
required until all of them have completed.

The conclusion is `t ∈ issued ↝ t ∈ retired`.
-/

namespace TlaDsl.Examples.MemoryPipeline

/-- The state: a fixed destination function, a shared timestamp counter, the
issued set, the per-controller pending pairs `(controller, op)`, the
completed (reorder-buffer) set, and the retired set. -/
structure St where
  dest : Nat → Nat
  last : Nat
  issued : Finset Nat
  pending : Finset (Nat × Nat)
  done : Finset Nat
  retired : Finset Nat

/-- The operations pending at controller `c`. -/
def cops (c : Nat) (s : St) : Finset Nat :=
  (s.pending.filter (fun p => p.1 = c)).image Prod.snd

/-- The pair `(c, m)` is in `pending` whenever `m` is an operation of
controller `c`. -/
lemma cops_mem_pending (c : Nat) (s : St) {m : Nat} (h : m ∈ cops c s) :
    (c, m) ∈ s.pending := by
  rcases Finset.mem_image.mp h with ⟨p, hp, hpsnd⟩
  have hp' : p ∈ s.pending ∧ p.1 = c := Finset.mem_filter.mp hp
  rcases hp' with ⟨hp1, hp2⟩
  have hpm : p = (c, m) := Prod.ext hp2 hpsnd
  rw [hpm] at hp1
  exact hp1

/-- Issue an operation (timestamps strictly increase). -/
def Issue (u : Nat) : Tla.Action St :=
  fun s s' =>
    u > s.last ∧ s'.issued = insert u s.issued ∧ s'.last = u ∧
      s'.pending = insert (s.dest u, u) s.pending ∧
      s'.done = s.done ∧ s'.retired = s.retired ∧ s'.dest = s.dest

/-- Controller `c` completes its earliest pending operation. -/
def Complete (c : Nat) : Tla.Action St :=
  fun s s' =>
    ∃ h : (cops c s).Nonempty,
      s'.pending = s.pending.erase (c, Finset.min' (cops c s) h) ∧
        s'.done = insert (Finset.min' (cops c s) h) s.done ∧
        s'.issued = s.issued ∧ s'.last = s.last ∧
        s'.retired = s.retired ∧ s'.dest = s.dest

/-- The reorder buffer retires the earliest completed operation. -/
def Retire : Tla.Action St :=
  fun s s' =>
    ∃ h : s.done.Nonempty,
      s'.done = s.done.erase (Finset.min' s.done h) ∧
        s'.retired = insert (Finset.min' s.done h) s.retired ∧
        s'.pending = s.pending ∧ s'.issued = s.issued ∧
        s'.last = s.last ∧ s'.dest = s.dest

/-- A step: issue, complete, or retire. -/
def Next : Tla.Action St :=
  fun s s' => (∃ u : Nat, Issue u s s') ∨ (∃ c : Nat, Complete c s s') ∨ Retire s s'

/-- Everything starts empty (destinations are unconstrained). -/
def Init : Tla.StatePred St :=
  fun s => s.pending = ∅ ∧ s.last = 0 ∧ s.issued = ∅ ∧ s.done = ∅ ∧ s.retired = ∅

/-! ## The rankings and schedulers -/

/-- `δ₀`: pending operations with timestamp `≤ t`. -/
def Delta0 (t : Nat) (s : St) : Finset Nat :=
  (s.pending.filter (fun p => p.2 ≤ t)).image Prod.snd

/-- `δ₁`: completed-but-not-retired operations with timestamp `≤ t`. -/
def Delta1 (t : Nat) (s : St) : Finset Nat :=
  s.done.filter (fun op => op ≤ t)

/-- The two ranking components. -/
def deltas (t : Nat) (i : Fin 2) (s : St) : Finset Nat :=
  if i.val = 0 then Delta0 t s else Delta1 t s

/-- The parameterized schedulers: `ψ₀(c) = ∃ op ≤ t pending at c`,
`ψ₁(c) = t ∈ done`. -/
def psis (t : Nat) (i : Fin 2) (c : Nat) (s : St) : Prop :=
  if i.val = 0 then ∃ op : Nat, op ≤ t ∧ (c, op) ∈ s.pending
  else t ∈ s.done

/-- The parameterized justice actions: `r₀(c) = Complete c`, `r₁(c) = Retire`. -/
def rjs (i : Fin 2) (c : Nat) : Tla.Action St :=
  if i.val = 0 then Complete c else Retire

/-! ## The inductive invariant -/

/-- Issued timestamps are bounded by the counter, the pipeline holds for
`t`, pending timestamps are globally distinct, and pending timestamps are
bounded by the counter. -/
def Inv (t : Nat) (s : St) : Prop :=
  (∀ op : Nat, op ∈ s.issued → op ≤ s.last) ∧
  (t ∈ s.issued → t ∈ s.retired ∨ (∃ c : Nat, (c, t) ∈ s.pending) ∨ t ∈ s.done) ∧
  (∀ p : Nat × Nat, p ∈ s.pending → ∀ q : Nat × Nat, q ∈ s.pending →
    p.2 = q.2 → p = q) ∧
  (∀ p : Nat × Nat, p ∈ s.pending → p.2 ≤ s.last)

/-- `Inv t` is preserved by every step of `Next`. -/
theorem inv_step (t : Nat) (s s' : St) (h : Inv t s) (hstep : Next s s') : Inv t s' := by
  rcases h with ⟨h1, h2, h3, h4⟩
  rcases hstep with hissue | hrest
  · -- an issue
    rcases hissue with ⟨u, hissue'⟩
    rcases hissue' with ⟨hu, hissued', hl', hpending', hdone', hretired', hdest'⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro op hop
      rw [hissued'] at hop
      rcases Finset.mem_insert.mp hop with hopu | hop1
      · rw [hopu, hl']
      · rw [hl']
        exact le_trans (h1 op hop1) (Nat.le_of_lt hu)
    · intro ht
      rw [hissued'] at ht
      rcases Finset.mem_insert.mp ht with htt | hts
      · right
        left
        refine ⟨s.dest t, ?_⟩
        rw [hpending', htt]
        exact Finset.mem_insert.mpr (Or.inl rfl)
      · rcases h2 hts with hr | hp | hd
        · left
          rw [hretired']
          exact hr
        · right
          left
          rcases hp with ⟨c, hpair⟩
          refine ⟨c, ?_⟩
          rw [hpending']
          exact Finset.mem_insert.mpr (Or.inr hpair)
        · right
          right
          rw [hdone']
          exact hd
    · intro p hp q hq hpq
      rw [hpending'] at hp
      rcases Finset.mem_insert.mp hp with hpu | hp1
      · rw [hpending'] at hq
        rcases Finset.mem_insert.mp hq with hqu | hq1
        · exact hpu.trans hqu.symm
        · have hqle : q.2 ≤ s.last := h4 q hq1
          rw [hpu] at hpq
          rw [← hpq] at hqle
          omega
      · rw [hpending'] at hq
        rcases Finset.mem_insert.mp hq with hqu | hq1
        · have hple : p.2 ≤ s.last := h4 p hp1
          rw [hqu] at hpq
          rw [hpq] at hple
          omega
        · exact h3 p hp1 q hq1 hpq
    · intro p hp
      rw [hpending'] at hp
      rcases Finset.mem_insert.mp hp with hpu | hp1
      · rw [hpu, hl']
      · rw [hl']
        exact le_trans (h4 p hp1) (Nat.le_of_lt hu)
  · rcases hrest with hcomplete | hretire
    · -- a completion
      rcases hcomplete with ⟨c, hcomplete'⟩
      rcases hcomplete' with ⟨h, hpending', hdone', hissued', hl', hretired', hdest'⟩
      let m := Finset.min' (cops c s) h
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro op hop
        rw [hissued'] at hop
        rw [hl']
        exact h1 op hop
      · intro ht
        rw [hissued'] at ht
        rcases h2 ht with hr | hp | hd
        · left
          rw [hretired']
          exact hr
        · right
          by_cases htm : t = m
          · right
            rw [hdone', htm]
            exact Finset.mem_insert_self m s.done
          · left
            rcases hp with ⟨c0, hpair⟩
            refine ⟨c0, ?_⟩
            rw [hpending']
            exact Finset.mem_erase.mpr ⟨by
              intro heq
              exact htm (congrArg Prod.snd heq), hpair⟩
        · right
          right
          rw [hdone']
          exact Finset.mem_insert.mpr (Or.inr hd)
      · intro p hp q hq hpq
        rw [hpending'] at hp
        have hpold : p ∈ s.pending := (Finset.mem_erase.mp hp).2
        rw [hpending'] at hq
        have hqold : q ∈ s.pending := (Finset.mem_erase.mp hq).2
        exact h3 p hpold q hqold hpq
      · intro p hp
        rw [hpending'] at hp
        rw [hl']
        exact h4 p (Finset.mem_erase.mp hp).2
    · -- a retirement
      rcases hretire with ⟨h, hdone', hretired', hpending', hissued', hl', hdest'⟩
      let m := Finset.min' s.done h
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro op hop
        rw [hissued'] at hop
        rw [hl']
        exact h1 op hop
      · intro ht
        rw [hissued'] at ht
        rcases h2 ht with hr | hp | hd
        · left
          rw [hretired']
          exact Finset.mem_insert.mpr (Or.inr hr)
        · right
          left
          rw [hpending']
          exact hp
        · by_cases htm : t = m
          · left
            rw [hretired', htm]
            exact Finset.mem_insert_self m s.retired
          · right
            right
            rw [hdone']
            exact Finset.mem_erase.mpr ⟨htm, hd⟩
      · intro p hp q hq hpq
        rw [hpending'] at hp
        rw [hpending'] at hq
        exact h3 p hp q hq hpq
      · intro p hp
        rw [hpending'] at hp
        rw [hl']
        exact h4 p hp

/-- `Inv t` holds at every reachable state. -/
theorem inv_inductive (t : Nat) (e : Tla.Behavior St)
    (hInit : Init (e 0)) (hNext : ∀ m, Next (e m) (e (m + 1))) :
    ∀ k, Inv t (e k) := by
  intro k
  induction k with
  | zero =>
      rcases hInit with ⟨hp0, hl0, hi0, hd0, hr0⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro op hop
        rw [hi0] at hop
        exact False.elim ((Finset.notMem_empty op) hop)
      · intro ht
        rw [hi0] at ht
        exact False.elim ((Finset.notMem_empty t) ht)
      · intro p hp q hq hpq
        rw [hp0] at hp
        exact False.elim ((Finset.notMem_empty p) hp)
      · intro p hp
        rw [hp0] at hp
        exact False.elim ((Finset.notMem_empty p) hp)
  | succ k ih =>
      exact inv_step t (e k) (e (k + 1)) ih (hNext k)

/-! ## The liveness theorem (Rule 11 instance, global preemption) -/

/-- The memory-pipeline spec: init, next, per-controller completion
fairness, and retire fairness. -/
def Spec : Tla.Pred St :=
  [t| Init ∧ □ Next ∧ (∀ c : Nat, □◇ Complete c) ∧ □◇ Retire]

/-- `(∀c, □◇ Complete c) ∧ (□◇ Retire) ⊢ issued(t) ↝ retired(t)` via the
two-component ranking with the global preemption of the retire component. -/
theorem memory_pipeline_liveness (t : Nat) :
    Tla.Entails Spec
      (Tla.leadsTo (Tla.statePred (fun s => t ∈ s.issued))
        (Tla.statePred (fun s => t ∈ s.retired))) := by
  tla_rel_rank_param_global
    (fun s => t ∈ s.issued), (fun s => t ∈ s.retired),
    (fun s => t ∈ s.issued ∧ ((∃ c : Nat, (c, t) ∈ s.pending) ∨ t ∈ s.done)),
    (deltas t), (psis t), rjs, Spec
  · -- S1: an issued operation is retired, pending, or done
    tla_spec_split
    intro k hp
    have hIk := inv_inductive t e hInit0 hNextAll k
    rcases hIk.2.1 hp with hr | hp' | hd
    · left
      exact Tla.eventually_imp (Tla.statePred (fun s => t ∈ s.retired)) e k
        (by simpa [Tla.statePred, Cslib.ωSequence.drop] using hr)
    · right
      exact ⟨hp, Or.inl hp'⟩
    · right
      exact ⟨hp, Or.inr hd⟩
  · -- P2: the parameterized L2 step (global preemption)
    tla_spec_split
    intro k hφ
    have hIk := inv_inductive t e hInit0 hNextAll k
    rcases hIk with ⟨h1, h2, h3, h4⟩
    rcases hNextAll k with hissue | hrest
    · -- an issue
      rcases hissue with ⟨u, hissue'⟩
      rcases hissue' with ⟨hu, hissued', hl', hpending', hdone', hretired', _hdest'⟩
      right
      constructor
      · change t ∈ (e (k + 1)).issued ∧
          ((∃ c : Nat, (c, t) ∈ (e (k + 1)).pending) ∨ t ∈ (e (k + 1)).done)
        constructor
        · rw [hissued']
          exact Finset.mem_insert.mpr (Or.inr hφ.1)
        · rcases hφ.2 with hpen | hd
          · left
            rcases hpen with ⟨c, hpair⟩
            refine ⟨c, ?_⟩
            rw [hpending']
            exact Finset.mem_insert.mpr (Or.inr hpair)
          · right
            rw [hdone']
            exact hd
      · constructor
        · intro c i _hnp
          fin_cases i
          · have htl : t ≤ (e k).last := h1 t hφ.1
            have hut : u > t := lt_of_le_of_lt htl hu
            intro x hx
            change x ∈ ((e (k + 1)).pending.filter (fun p => p.2 ≤ t)).image Prod.snd at hx
            rcases Finset.mem_image.mp hx with ⟨p, hp, hpx⟩
            rcases Finset.mem_filter.mp hp with ⟨hp1, hp2⟩
            rw [hpending'] at hp1
            rcases Finset.mem_insert.mp hp1 with hpu | hp1'
            · rw [hpu] at hp2
              exact False.elim ((not_le_of_gt hut) hp2)
            · change x ∈ ((e k).pending.filter (fun p => p.2 ≤ t)).image Prod.snd
              exact Finset.mem_image.mpr ⟨p, ⟨Finset.mem_filter.mpr ⟨hp1', hp2⟩, hpx⟩⟩
          · intro x hx
            simp [deltas, Delta1] at hx ⊢
            rw [hdone'] at hx
            exact hx
        · constructor
          · intro c i
            fin_cases i
            · intro hreq hR
              rcases hR with ⟨h0, hpending'', _hdone'', _hissued'', _hlast'', _hretired''⟩
              let m0 := Finset.min' (cops c (e k)) h0
              rcases hreq.1 with ⟨τ, hτle, hτpair⟩
              have hτcops : τ ∈ cops c (e k) := by
                exact Finset.mem_image.mpr ⟨(c, τ),
                  ⟨Finset.mem_filter.mpr ⟨hτpair, rfl⟩, rfl⟩⟩
              have hmle : m0 ≤ t := le_trans ((Finset.isLeast_min' (cops c (e k)) h0).2 hτcops) hτle
              have hmpair : (c, m0) ∈ (e k).pending :=
                cops_mem_pending c (e k) (Finset.min'_mem (cops c (e k)) h0)
              have hmem : m0 ∈ deltas t 0 (e k) := by
                change m0 ∈ ((e k).pending.filter (fun p => p.2 ≤ t)).image Prod.snd
                exact Finset.mem_image.mpr ⟨(c, m0), ⟨Finset.mem_filter.mpr ⟨hmpair, hmle⟩, rfl⟩⟩
              have hnotmem : m0 ∉ deltas t 0 (e (k + 1)) := by
                intro hδ
                change m0 ∈ ((e (k + 1)).pending.filter (fun p => p.2 ≤ t)).image Prod.snd at hδ
                rcases Finset.mem_image.mp hδ with ⟨p, hp, hpx⟩
                rcases Finset.mem_filter.mp hp with ⟨hp1, _hp2⟩
                rw [hpending''] at hp1
                have hpne : p ≠ (c, m0) := (Finset.mem_erase.mp hp1).1
                have hpold : p ∈ (e k).pending := (Finset.mem_erase.mp hp1).2
                have hpeq : p = (c, m0) := h3 p hpold (c, m0) hmpair hpx
                exact hpne hpeq
              exact ⟨m0, hmem, hnotmem⟩
            · intro _hreq hR
              exfalso
              rcases hR with ⟨h2, hdone'', _hretired'', _hpending'', _hissued'', _hlast''⟩
              have hc : (e k).done.erase (Finset.min' (e k).done h2) = (e k).done := by
                rw [← hdone'', hdone']
              have hm : Finset.min' (e k).done h2 ∈
                  (e k).done.erase (Finset.min' (e k).done h2) := by
                rw [hc]
                exact Finset.min'_mem (e k).done h2
              exact (Finset.mem_erase.mp hm).1 rfl
          · intro c i
            fin_cases i
            · intro hreq _hnr
              rcases hreq.1 with ⟨τ, hτle, hτpair⟩
              refine ⟨τ, hτle, ?_⟩
              rw [hpending']
              exact Finset.mem_insert.mpr (Or.inr hτpair)
            · intro hreq _hnr
              simpa [psis, hdone'] using hreq.1
    · rcases hrest with hcomplete | hretire
      · -- a completion by controller `c'`
        rcases hcomplete with ⟨c', hcomplete'⟩
        rcases hcomplete' with ⟨h, hpending', hdone', hissued', hl', hretired', _hdest'⟩
        let m := Finset.min' (cops c' (e k)) h
        right
        constructor
        · change t ∈ (e (k + 1)).issued ∧
            ((∃ c : Nat, (c, t) ∈ (e (k + 1)).pending) ∨ t ∈ (e (k + 1)).done)
          constructor
          · rw [hissued']
            exact hφ.1
          · rcases hφ.2 with hpen | hd
            · by_cases htm : t = m
              · right
                rw [hdone', htm]
                exact Finset.mem_insert_self m (e k).done
              · left
                rcases hpen with ⟨c0, hpair⟩
                refine ⟨c0, ?_⟩
                rw [hpending']
                exact Finset.mem_erase.mpr ⟨by
                  intro heq
                  exact htm (congrArg Prod.snd heq), hpair⟩
            · right
              rw [hdone']
              exact Finset.mem_insert.mpr (Or.inr hd)
        · constructor
          · intro c i hnp
            fin_cases i
            · intro x hx
              change x ∈ ((e (k + 1)).pending.filter (fun p => p.2 ≤ t)).image Prod.snd at hx
              rcases Finset.mem_image.mp hx with ⟨p, hp, hpx⟩
              rcases Finset.mem_filter.mp hp with ⟨hp1, hp2⟩
              rw [hpending'] at hp1
              change x ∈ ((e k).pending.filter (fun p => p.2 ≤ t)).image Prod.snd
              exact Finset.mem_image.mpr ⟨p, ⟨Finset.mem_filter.mpr
                ⟨(Finset.erase_subset (c', m) (e k).pending) hp1, hp2⟩, hpx⟩⟩
            · intro x hx
              simp [deltas, Delta1] at hx ⊢
              rw [hdone'] at hx
              constructor
              · rcases Finset.mem_insert.mp hx.1 with hxm | hxmem
                · have hmle : m ≤ t := by
                    rw [hxm] at hx
                    exact hx.2
                  have hpair : (c', m) ∈ (e k).pending :=
                    cops_mem_pending c' (e k) (Finset.min'_mem (cops c' (e k)) h)
                  exact False.elim (hnp ⟨(0 : Fin 2), ⟨by decide,
                    ⟨c', ⟨m, ⟨hmle, hpair⟩⟩⟩⟩⟩)
                · exact hxmem
              · exact hx.2
          · constructor
            · intro c i
              fin_cases i
              · intro hreq hR
                rcases hR with ⟨h0, hpending'', _hdone'', _hissued'', _hlast'', _hretired''⟩
                let m0 := Finset.min' (cops c (e k)) h0
                rcases hreq.1 with ⟨τ, hτle, hτpair⟩
                have hτcops : τ ∈ cops c (e k) := by
                  exact Finset.mem_image.mpr ⟨(c, τ),
                    ⟨Finset.mem_filter.mpr ⟨hτpair, rfl⟩, rfl⟩⟩
                have hmle : m0 ≤ t := le_trans ((Finset.isLeast_min' (cops c (e k)) h0).2 hτcops) hτle
                have hmpair : (c, m0) ∈ (e k).pending :=
                  cops_mem_pending c (e k) (Finset.min'_mem (cops c (e k)) h0)
                have hmem : m0 ∈ deltas t 0 (e k) := by
                  change m0 ∈ ((e k).pending.filter (fun p => p.2 ≤ t)).image Prod.snd
                  exact Finset.mem_image.mpr ⟨(c, m0), ⟨Finset.mem_filter.mpr ⟨hmpair, hmle⟩, rfl⟩⟩
                have hnotmem : m0 ∉ deltas t 0 (e (k + 1)) := by
                  intro hδ
                  change m0 ∈ ((e (k + 1)).pending.filter (fun p => p.2 ≤ t)).image Prod.snd at hδ
                  rcases Finset.mem_image.mp hδ with ⟨p, hp, hpx⟩
                  rcases Finset.mem_filter.mp hp with ⟨hp1, _hp2⟩
                  rw [hpending''] at hp1
                  have hpne : p ≠ (c, m0) := (Finset.mem_erase.mp hp1).1
                  have hpold : p ∈ (e k).pending := (Finset.mem_erase.mp hp1).2
                  have hpeq : p = (c, m0) := h3 p hpold (c, m0) hmpair hpx
                  exact hpne hpeq
                exact ⟨m0, hmem, hnotmem⟩
              · intro _hreq hR
                exfalso
                rcases hR with ⟨h2, hdone'', _hretired'', _hpending'', _hissued'', _hlast''⟩
                have hc : (e k).done.erase (Finset.min' (e k).done h2) =
                    insert m (e k).done := by
                  rw [← hdone'', hdone']
                have hm : Finset.min' (e k).done h2 ∈
                    (e k).done.erase (Finset.min' (e k).done h2) := by
                  rw [hc]
                  exact Finset.mem_insert.mpr (Or.inr (Finset.min'_mem (e k).done h2))
                exact (Finset.mem_erase.mp hm).1 rfl
            · intro c i
              fin_cases i
              · intro hreq hnr
                rcases hreq.1 with ⟨τ, hτle, hτpair⟩
                by_cases hc : c = c'
                · exfalso
                  exact hnr (by simpa [hc] using ⟨h, hpending', hdone', hissued', hl', hretired', _hdest'⟩)
                · refine ⟨τ, hτle, ?_⟩
                  rw [hpending']
                  exact Finset.mem_erase.mpr ⟨by
                    intro heq
                    exact hc (congrArg Prod.fst heq), hτpair⟩
              · intro hreq _hnr
                change t ∈ (e (k + 1)).done
                rw [hdone']
                exact Finset.mem_insert.mpr (Or.inr hreq.1)
      · -- a retirement
        rcases hretire with ⟨h, hdone', hretired', hpending', hissued', hl', _hdest'⟩
        let m := Finset.min' (e k).done h
        by_cases htm : t = m
        · left
          have hrec : t ∈ (e (k + 1)).retired := by
            rw [hretired', htm]
            exact Finset.mem_insert_self m (e k).retired
          have hqev : Tla.eventually (Tla.statePred (fun s => t ∈ s.retired))
              ((e.drop k).drop 1) := by
            simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              (Tla.eventually_imp (Tla.statePred (fun s => t ∈ s.retired)) e (k + 1)
                (by simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_comm] using hrec))
          rcases hqev with ⟨t0, ht0⟩
          refine ⟨1 + t0, ?_⟩
          simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using ht0
        · right
          constructor
          · change t ∈ (e (k + 1)).issued ∧
              ((∃ c : Nat, (c, t) ∈ (e (k + 1)).pending) ∨ t ∈ (e (k + 1)).done)
            constructor
            · rw [hissued']
              exact hφ.1
            · rcases hφ.2 with hpen | hd
              · left
                rw [hpending']
                exact hpen
              · right
                rw [hdone']
                exact Finset.mem_erase.mpr ⟨htm, hd⟩
          · constructor
            · intro c i _hnp
              fin_cases i
              · intro x hx
                simp [deltas, Delta0] at hx ⊢
                rw [hpending'] at hx
                exact hx
              · intro x hx
                simp [deltas, Delta1] at hx ⊢
                constructor
                · rw [hdone'] at hx
                  exact (Finset.erase_subset m (e k).done) hx.1
                · exact hx.2
            · constructor
              · intro c i
                fin_cases i
                · intro _hreq hR
                  exfalso
                  rcases hR with ⟨h0, hpending'', _hdone'', _hissued'', _hlast'', _hretired''⟩
                  let m0 := Finset.min' (cops c (e k)) h0
                  have hmpair : (c, m0) ∈ (e k).pending :=
                    cops_mem_pending c (e k) (Finset.min'_mem (cops c (e k)) h0)
                  have hc : (e k).pending.erase (c, m0) = (e k).pending := by
                    rw [← hpending'', hpending']
                  have hmem : (c, m0) ∈ (e k).pending.erase (c, m0) := by
                    rw [hc]
                    exact hmpair
                  exact (Finset.mem_erase.mp hmem).1 rfl
                · intro hreq hR
                  rcases hR with ⟨h2, hdone'', _hretired'', _hpending'', _hissued'', _hlast''⟩
                  let m0 := Finset.min' (e k).done h2
                  have hmle : m0 ≤ t := (Finset.isLeast_min' (e k).done h2).2 hreq.1
                  refine ⟨m0, ?_, ?_⟩
                  · simp [deltas, Delta1]
                    exact ⟨Finset.min'_mem (e k).done h2, hmle⟩
                  · intro hδ
                    simp [deltas, Delta1] at hδ
                    rw [hdone''] at hδ
                    exact (Finset.mem_erase.mp hδ.1).1 rfl
              · intro c i
                fin_cases i
                · intro hreq _hnr
                  rcases hreq.1 with ⟨τ, hτle, hτpair⟩
                  refine ⟨τ, hτle, ?_⟩
                  rw [hpending']
                  exact hτpair
                · intro _hreq hnr
                  exact False.elim (hnr ⟨h, hdone', hretired', hpending', hissued', hl', _hdest'⟩)
  · -- P3: a scheduled justice action eventually fires
    tla_spec_split
    intro k _hφ c i hψ
    fin_cases i
    · right
      exact hJ1 c k
    · right
      exact hJ2 k
  · -- P4: the tracked operation's controller is scheduled while pending, or
    -- the reorder buffer is scheduled once `t` is done
    intro e _hH k hφ
    right
    rcases hφ.2 with hpen | hd
    · rcases hpen with ⟨c, hpair⟩
      exact ⟨c, ⟨(0 : Fin 2), by simpa [psis] using ⟨t, ⟨le_rfl, hpair⟩⟩⟩⟩
    · exact ⟨0, ⟨(1 : Fin 2), by simpa [psis] using hd⟩⟩

end TlaDsl.Examples.MemoryPipeline
