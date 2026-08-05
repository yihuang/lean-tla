import TlaDsl.Basic
import TlaDsl.Notation
import TlaDsl.RelRank
import TlaDsl.Tactic

open scoped Tla

/-! # Cascaded queues: chaining response properties (Rule 7)

The paper's §3.2 example (Fig. 3) run through the chaining variant of the
relational-ranking rule. Two queues in a cascade: polling queue 1 moves its
minimal pending timestamp into queue 2 (the same transition records it as
`recv1` and `sent2`); polling queue 2 removes and records `recv2`. The
end-to-end property

    (□◇ poll₁) ∧ (□◇ poll₂) ⊢ sent₁ t ↝ recv₂ t

is proved *without* a two-component ranking: two single-queue liveness
lemmas (`q1_liveness`, `q2_liveness`, each an instance of Rule 6) are
chained with Rule 7, whose premises carry `◇q` and are manipulated with the
`◇` tableau axioms. The ranking is queue 1's `δ₁(τ) = τ ∈ pend₁ ∧ τ ≤ t`;
when a poll₁ step removes `t` itself, `D2` hands off to `q2_liveness` via
the coupling invariant `recv₁ t → sent₂ t`.
-/

namespace TlaDsl.Examples.CascadedQueues

/-- Two timestamped queues in a cascade, with history flags for each. -/
structure St where
  pend1 : Finset Nat
  last1 : Nat
  sent1 : Finset Nat
  recv1 : Finset Nat
  pend2 : Finset Nat
  last2 : Nat
  sent2 : Finset Nat
  recv2 : Finset Nat

/-- The sender enters a message with timestamp `u` into queue 1. -/
def Send1 (u : Nat) : Tla.Action St :=
  fun s s' =>
    u > s.last1 ∧ s'.pend1 = insert u s.pend1 ∧ s'.last1 = u ∧
      s'.sent1 = insert u s.sent1 ∧ s'.recv1 = s.recv1 ∧
      s'.pend2 = s.pend2 ∧ s'.last2 = s.last2 ∧ s'.sent2 = s.sent2 ∧
      s'.recv2 = s.recv2

/-- Polling queue 1 moves its minimal pending timestamp into queue 2. -/
def Poll1 : Tla.Action St :=
  fun s s' =>
    ∃ h : s.pend1.Nonempty,
      s'.pend1 = s.pend1.erase (Finset.min' s.pend1 h) ∧ s'.last1 = s.last1 ∧
        s'.sent1 = s.sent1 ∧ s'.recv1 = insert (Finset.min' s.pend1 h) s.recv1 ∧
        s'.pend2 = insert (Finset.min' s.pend1 h) s.pend2 ∧
        s'.last2 = max s.last2 (Finset.min' s.pend1 h) ∧
        s'.sent2 = insert (Finset.min' s.pend1 h) s.sent2 ∧ s'.recv2 = s.recv2

/-- Polling queue 2 removes its minimal pending timestamp. -/
def Poll2 : Tla.Action St :=
  fun s s' =>
    ∃ h : s.pend2.Nonempty,
      s'.pend2 = s.pend2.erase (Finset.min' s.pend2 h) ∧
        s'.recv2 = insert (Finset.min' s.pend2 h) s.recv2 ∧ s'.last2 = s.last2 ∧
        s'.pend1 = s.pend1 ∧ s'.last1 = s.last1 ∧ s'.sent1 = s.sent1 ∧
        s'.recv1 = s.recv1 ∧ s'.sent2 = s.sent2

/-- A step: a send to queue 1, a poll of queue 1, or a poll of queue 2. -/
def Next : Tla.Action St :=
  fun s s' => (∃ u : Nat, Send1 u s s') ∨ Poll1 s s' ∨ Poll2 s s'

/-- Both queues start empty. -/
def Init : Tla.StatePred St :=
  fun s => s.pend1 = ∅ ∧ s.last1 = 0 ∧ s.sent1 = ∅ ∧ s.recv1 = ∅ ∧
    s.pend2 = ∅ ∧ s.last2 = 0 ∧ s.sent2 = ∅ ∧ s.recv2 = ∅

/-- The inductive invariant for the cascade (at a fixed message timestamp
`t`): per-queue "sent ⇒ received-or-pending" and "pending ⇒ bounded by
last", the coupling `recv₁ t → sent₂ t`, the paper's cross invariant
(queue-1 timestamps are strictly after queue-2's largest), and the
timestamp order inside each queue. -/
def Inv (t : Nat) (s : St) : Prop :=
  (t ∈ s.sent1 → t ∈ s.recv1 ∨ t ∈ s.pend1) ∧
  (t ∈ s.pend1 → t ≤ s.last1) ∧
  (t ∈ s.sent2 → t ∈ s.recv2 ∨ t ∈ s.pend2) ∧
  (t ∈ s.pend2 → t ≤ s.last2) ∧
  (t ∈ s.recv1 → t ∈ s.sent2) ∧
  (∀ τ, τ ∈ s.pend1 → s.last2 < τ) ∧
  (s.last2 ≤ s.last1) ∧
  (∀ τ, τ ∈ s.pend2 → τ ≤ s.last2) ∧
  (∀ τ, τ ∈ s.pend1 → τ ≤ s.last1)

/-- `Inv t` is preserved by every step of `Next`. -/
theorem inv_step (t : Nat) (s s' : St) (h : Inv t s) (hstep : Next s s') : Inv t s' := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  rcases hstep with hsend | hpoll
  · -- a send into queue 1
    rcases hsend with ⟨u, hsend'⟩
    rcases hsend' with ⟨hu, hp1', hl1', hs1', hr1', hp2', hl2', hs2', hr2'⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro ht
      rw [hs1'] at ht
      rcases Finset.mem_insert.mp ht with htu | hts
      · right
        rw [hp1']
        exact Finset.mem_insert.mpr (Or.inl htu)
      · rcases h1 hts with hq | hpnd
        · left
          rw [hr1']
          exact hq
        · right
          rw [hp1']
          exact Finset.mem_insert.mpr (Or.inr hpnd)
    · intro ht
      rw [hp1'] at ht
      rw [hl1']
      rcases Finset.mem_insert.mp ht with htu | htp
      · exact le_of_eq htu
      · exact le_trans (h2 htp) (le_of_lt hu)
    · intro ht
      have ht' : t ∈ s.sent2 := by simpa [hs2'] using ht
      rcases h3 ht' with hq | hpnd
      · left
        simpa [hr2'] using hq
      · right
        simpa [hp2'] using hpnd
    · intro ht
      have ht' : t ∈ s.pend2 := by simpa [hp2'] using ht
      simpa [hl2'] using (h4 ht')
    · intro ht
      have ht' : t ∈ s.recv1 := by simpa [hr1'] using ht
      simpa [hs2'] using (h5 ht')
    · intro τ hτ
      rw [hl2']
      rw [hp1'] at hτ
      rcases Finset.mem_insert.mp hτ with hτu | hτp
      · rw [hτu]
        exact lt_of_le_of_lt h7 hu
      · exact h6 τ hτp
    · rw [hl2', hl1']
      exact le_trans h7 (le_of_lt hu)
    · intro τ hτ
      have hτ' : τ ∈ s.pend2 := by simpa [hp2'] using hτ
      simpa [hl2'] using (h8 τ hτ')
    · intro τ hτ
      rw [hp1'] at hτ
      rw [hl1']
      rcases Finset.mem_insert.mp hτ with hτu | hτp
      · exact le_of_eq hτu
      · exact le_trans (h9 τ hτp) (le_of_lt hu)
  · rcases hpoll with hpoll1 | hpoll2
    · -- a poll of queue 1: `m` moves from queue 1 to queue 2
      rcases hpoll1 with ⟨h1p, hp⟩
      rcases hp with ⟨hp1', hl1', hs1', hr1', hp2', hl2', hs2', hr2'⟩
      let m := Finset.min' s.pend1 h1p
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro ht
        have ht' : t ∈ s.sent1 := by simpa [hs1'] using ht
        rcases h1 ht' with hq | hpnd
        · left
          rw [hr1']
          exact Finset.mem_insert.mpr (Or.inr hq)
        · by_cases htm : t = m
          · left
            rw [hr1', htm]
            exact Finset.mem_insert_self m s.recv1
          · right
            rw [hp1']
            exact Finset.mem_erase.mpr ⟨htm, hpnd⟩
      · intro ht
        rw [hp1'] at ht
        have htp : t ∈ s.pend1 := (Finset.mem_erase.mp ht).2
        simpa [hl1'] using (h2 htp)
      · intro ht
        rw [hs2'] at ht
        rcases Finset.mem_insert.mp ht with htm | hts
        · right
          rw [hp2']
          exact Finset.mem_insert.mpr (Or.inl htm)
        · rcases h3 hts with hq | hpnd
          · left
            simpa [hr2'] using hq
          · right
            rw [hp2']
            exact Finset.mem_insert.mpr (Or.inr hpnd)
      · intro ht
        rw [hp2'] at ht
        rw [hl2']
        rcases Finset.mem_insert.mp ht with htm | htp
        · rw [htm]
          exact le_max_right s.last2 m
        · exact le_trans (h4 htp) (le_max_left s.last2 m)
      · intro ht
        rw [hr1'] at ht
        rcases Finset.mem_insert.mp ht with htm | htr
        · rw [htm, hs2']
          exact Finset.mem_insert_self m s.sent2
        · rw [hs2']
          exact Finset.mem_insert.mpr (Or.inr (h5 htr))
      · intro τ hτ
        rw [hp1'] at hτ
        have hτp : τ ∈ s.pend1 := (Finset.mem_erase.mp hτ).2
        have hτne : τ ≠ m := (Finset.mem_erase.mp hτ).1
        rw [hl2']
        have h1lt : s.last2 < τ := h6 τ hτp
        have hmlt : m < τ := by
          have hmle : m ≤ τ := (Finset.isLeast_min' s.pend1 h1p).2 hτp
          exact lt_of_le_of_ne hmle (Ne.symm hτne)
        exact max_lt h1lt hmlt
      · rw [hl2', hl1']
        exact max_le h7 (h9 m (Finset.min'_mem s.pend1 h1p))
      · intro τ hτ
        rw [hp2'] at hτ
        rw [hl2']
        rcases Finset.mem_insert.mp hτ with hτm | hτp
        · rw [hτm]
          exact le_max_right s.last2 m
        · exact le_trans (h8 τ hτp) (le_max_left s.last2 m)
      · intro τ hτ
        rw [hp1'] at hτ
        have hτp : τ ∈ s.pend1 := (Finset.mem_erase.mp hτ).2
        simpa [hl1'] using (h9 τ hτp)
    · -- a poll of queue 2
      rcases hpoll2 with ⟨h2p, hp⟩
      rcases hp with ⟨hp2', hr2', hl2', hp1', hl1', hs1', hr1', hs2'⟩
      let m := Finset.min' s.pend2 h2p
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro ht
        have ht' : t ∈ s.sent1 := by simpa [hs1'] using ht
        rcases h1 ht' with hq | hpnd
        · left
          simpa [hr1'] using hq
        · right
          simpa [hp1'] using hpnd
      · intro ht
        have ht' : t ∈ s.pend1 := by simpa [hp1'] using ht
        simpa [hl1'] using (h2 ht')
      · intro ht
        have ht' : t ∈ s.sent2 := by simpa [hs2'] using ht
        rcases h3 ht' with hq | hpnd
        · left
          rw [hr2']
          exact Finset.mem_insert.mpr (Or.inr hq)
        · by_cases htm : t = m
          · left
            rw [hr2', htm]
            exact Finset.mem_insert_self m s.recv2
          · right
            rw [hp2']
            exact Finset.mem_erase.mpr ⟨htm, hpnd⟩
      · intro ht
        rw [hp2'] at ht
        have htp : t ∈ s.pend2 := (Finset.mem_erase.mp ht).2
        simpa [hl2'] using (h4 htp)
      · intro ht
        have ht' : t ∈ s.recv1 := by simpa [hr1'] using ht
        simpa [hs2'] using (h5 ht')
      · intro τ hτ
        have hτ' : τ ∈ s.pend1 := by simpa [hp1'] using hτ
        simpa [hl2'] using (h6 τ hτ')
      · rw [hl2', hl1']
        exact h7
      · intro τ hτ
        rw [hp2'] at hτ
        have hτp : τ ∈ s.pend2 := (Finset.mem_erase.mp hτ).2
        simpa [hl2'] using (h8 τ hτp)
      · intro τ hτ
        have hτ' : τ ∈ s.pend1 := by simpa [hp1'] using hτ
        simpa [hl1'] using (h9 τ hτ')

/-- `Inv t` holds at every reachable state of `Init ∧ □ Next`. -/
theorem inv_inductive (t : Nat) (e : Tla.Behavior St)
    (hInit : Init (e 0)) (hNext : ∀ m, Next (e m) (e (m + 1))) :
    ∀ k, Inv t (e k) := by
  intro k
  induction k with
  | zero =>
      rcases hInit with ⟨hp10, hl10, hs10, hr10, hp20, hl20, hs20, hr20⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro ht
        rw [hs10] at ht
        exact False.elim ((Finset.notMem_empty t) ht)
      · intro ht
        rw [hp10] at ht
        exact False.elim ((Finset.notMem_empty t) ht)
      · intro ht
        rw [hs20] at ht
        exact False.elim ((Finset.notMem_empty t) ht)
      · intro ht
        rw [hp20] at ht
        exact False.elim ((Finset.notMem_empty t) ht)
      · intro ht
        rw [hr10] at ht
        exact False.elim ((Finset.notMem_empty t) ht)
      · intro τ hτ
        rw [hp10] at hτ
        exact False.elim ((Finset.notMem_empty τ) hτ)
      · rw [hl20, hl10]
      · intro τ hτ
        rw [hp20] at hτ
        exact False.elim ((Finset.notMem_empty τ) hτ)
      · intro τ hτ
        rw [hp10] at hτ
        exact False.elim ((Finset.notMem_empty τ) hτ)
  | succ k ih =>
      exact inv_step t (e k) (e (k + 1)) ih (hNext k)

/-! ## The two single-queue liveness lemmas (Rule 6 instances) -/

/-- Queue 1 liveness: `(□◇ poll₁) ⊢ sent₁ t ↝ recv₁ t`. -/
theorem q1_liveness (t : Nat) :
    Tla.Entails
      (Tla.tlaAnd (Tla.statePred Init)
        (Tla.tlaAnd (Tla.always (Tla.actionPred Next))
          (Tla.always (Tla.eventually (Tla.actionPred Poll1)))))
      (Tla.leadsTo (Tla.statePred (fun s => t ∈ s.sent1))
        (Tla.statePred (fun s => t ∈ s.recv1))) := by
  intro e h
  rcases h with ⟨hInit, hNextJ⟩
  rcases hNextJ with ⟨hNext, hJ⟩
  refine Tla.relational_ranking_rule
    (p := fun s => t ∈ s.sent1) (q := fun s => t ∈ s.recv1) (r := Poll1)
    (φ := fun s => t ∈ s.pend1)
    (δ := fun s τ => τ ∈ s.pend1 ∧ τ ≤ t)
    (R := fun s τ => τ ∈ s.pend1)
    (H := Tla.tlaAnd (Tla.statePred Init) (Tla.always (Tla.actionPred Next)))
    ?_ ?_ ?_ ?_ e ⟨⟨hInit, hNext⟩, hJ⟩
  · intro e' n
    simp
  · -- C1: `sent₁ t → recv₁ t ∨ (φ ∧ δ₁ ⊆ R₁)`
    intro e' hH k hp
    rcases hH with ⟨hInit', hNext'⟩
    have hInit0 : Init (e' 0) := by
      simpa [Tla.statePred, Cslib.ωSequence.drop] using hInit'
    have hNextAll : ∀ m, Next (e' m) (e' (m + 1)) := by
      intro m
      have hm := hNext' m
      simpa [Tla.actionPred, Cslib.ωSequence.drop, Nat.add_comm] using hm
    have hIk := inv_inductive t e' hInit0 hNextAll k
    rcases hIk.1 hp with hq | hpnd
    · exact Or.inl hq
    · exact Or.inr ⟨hpnd, fun x hx => hx.1⟩
  · -- C2: `φ₁` persists and `δ₁` is conserved
    intro e' hH k hφ
    rcases hH with ⟨hInit', hNext'⟩
    have hInit0 : Init (e' 0) := by
      simpa [Tla.statePred, Cslib.ωSequence.drop] using hInit'
    have hNextAll : ∀ m, Next (e' m) (e' (m + 1)) := by
      intro m
      have hm := hNext' m
      simpa [Tla.actionPred, Cslib.ωSequence.drop, Nat.add_comm] using hm
    have hIk := inv_inductive t e' hInit0 hNextAll k
    rcases hIk with ⟨_h1, h2, _h3, _h4, _h5, _h6, _h7, _h8, _h9⟩
    rcases hNextAll k with hsend | hpoll
    · rcases hsend with ⟨u, hsend'⟩
      rcases hsend' with ⟨hu, hp1', _hl1', _hs1', hr1', _hp2', _hl2', _hs2', _hr2'⟩
      by_cases hq : t ∈ (e' (k + 1)).recv1
      · exact Or.inl hq
      · right
        constructor
        · rw [hp1']
          exact Finset.mem_insert.mpr (Or.inr hφ)
        · have htl : t ≤ (e' k).last1 := h2 hφ
          have hut : u > t := lt_of_le_of_lt htl hu
          intro x hx
          constructor
          · have hxne : x ≠ u := ne_of_lt (lt_of_le_of_lt hx.2 hut)
            rw [hp1'] at hx
            exact (Finset.mem_insert.mp hx.1).resolve_left hxne
          · exact hx.2
    · rcases hpoll with hpoll1 | hpoll2
      · -- a poll₁ step: either `t` is removed (recv₁) or stays
        rcases hpoll1 with ⟨h1p, hp⟩
        rcases hp with ⟨hp1', _hl1', _hs1', hr1', _hp2', _hl2', _hs2', _hr2'⟩
        let m := Finset.min' (e' k).pend1 h1p
        by_cases hq : t ∈ (e' (k + 1)).recv1
        · exact Or.inl hq
        · right
          constructor
          · have htm : t ≠ m := by
              intro htm
              have htR : t ∈ (e' (k + 1)).recv1 := by
                rw [hr1', htm]
                exact Finset.mem_insert_self m (e' k).recv1
              exact hq htR
            rw [hp1']
            exact Finset.mem_erase.mpr ⟨htm, hφ⟩
          · intro x hx
            constructor
            · rw [hp1'] at hx
              exact (Finset.erase_subset m (e' k).pend1) hx.1
            · exact hx.2
      · -- a poll₂ step: queue 1 is untouched
        rcases hpoll2 with ⟨h2p, hp⟩
        rcases hp with ⟨_hp2', _hr2', _hl2', hp1', _hl1', _hs1', _hr1', _hs2'⟩
        right
        constructor
        · simpa [hp1'] using hφ
        · intro x hx
          constructor
          · rw [hp1'] at hx
            exact hx.1
          · exact hx.2
  · -- C3: a poll₁ step reduces `δ₁` (the minimum pending timestamp)
    intro e' _hH k hφ hpoll1
    rcases hpoll1 with ⟨h1p, hp⟩
    rcases hp with ⟨hp1', _hl1', _hs1', _hr1', _hp2', _hl2', _hs2', _hr2'⟩
    right
    let m := Finset.min' (e' k).pend1 h1p
    refine ⟨m, ?_, ?_⟩
    · constructor
      · simpa [m] using Finset.min'_mem (e' k).pend1 h1p
      · have hmin := (Finset.isLeast_min' (e' k).pend1 h1p).2 hφ
        simpa [m] using hmin
    · intro hδ
      have hmnot : m ∉ (e' (k + 1)).pend1 := by
        rw [hp1']
        simp [m]
      exact hmnot hδ.1

/-- Queue 2 liveness: `(□◇ poll₂) ⊢ sent₂ t ↝ recv₂ t`. -/
theorem q2_liveness (t : Nat) :
    Tla.Entails
      (Tla.tlaAnd (Tla.statePred Init)
        (Tla.tlaAnd (Tla.always (Tla.actionPred Next))
          (Tla.always (Tla.eventually (Tla.actionPred Poll2)))))
      (Tla.leadsTo (Tla.statePred (fun s => t ∈ s.sent2))
        (Tla.statePred (fun s => t ∈ s.recv2))) := by
  intro e h
  rcases h with ⟨hInit, hNextJ⟩
  rcases hNextJ with ⟨hNext, hJ⟩
  refine Tla.relational_ranking_rule
    (p := fun s => t ∈ s.sent2) (q := fun s => t ∈ s.recv2) (r := Poll2)
    (φ := fun s => t ∈ s.pend2)
    (δ := fun s τ => τ ∈ s.pend2 ∧ τ ≤ t)
    (R := fun s τ => τ ∈ s.pend2)
    (H := Tla.tlaAnd (Tla.statePred Init) (Tla.always (Tla.actionPred Next)))
    ?_ ?_ ?_ ?_ e ⟨⟨hInit, hNext⟩, hJ⟩
  · intro e' n
    simp
  · -- C1: `sent₂ t → recv₂ t ∨ (φ ∧ δ₂ ⊆ R₂)`
    intro e' hH k hp
    rcases hH with ⟨hInit', hNext'⟩
    have hInit0 : Init (e' 0) := by
      simpa [Tla.statePred, Cslib.ωSequence.drop] using hInit'
    have hNextAll : ∀ m, Next (e' m) (e' (m + 1)) := by
      intro m
      have hm := hNext' m
      simpa [Tla.actionPred, Cslib.ωSequence.drop, Nat.add_comm] using hm
    have hIk := inv_inductive t e' hInit0 hNextAll k
    rcases hIk.2.2.1 hp with hq | hpnd
    · exact Or.inl hq
    · exact Or.inr ⟨hpnd, fun x hx => hx.1⟩
  · -- C2: `φ₂` persists and `δ₂` is conserved
    intro e' hH k hφ
    rcases hH with ⟨hInit', hNext'⟩
    have hInit0 : Init (e' 0) := by
      simpa [Tla.statePred, Cslib.ωSequence.drop] using hInit'
    have hNextAll : ∀ m, Next (e' m) (e' (m + 1)) := by
      intro m
      have hm := hNext' m
      simpa [Tla.actionPred, Cslib.ωSequence.drop, Nat.add_comm] using hm
    have hIk := inv_inductive t e' hInit0 hNextAll k
    rcases hIk with ⟨_h1, _h2, _h3, h4, _h5, h6, _h7, _h8, _h9⟩
    rcases hNextAll k with hsend | hpoll
    · -- a send into queue 1: queue 2 is untouched
      rcases hsend with ⟨u, hsend'⟩
      rcases hsend' with ⟨_hu, _hp1', _hl1', _hs1', _hr1', hp2', hl2', hs2', hr2'⟩
      by_cases hq : t ∈ (e' (k + 1)).recv2
      · exact Or.inl hq
      · right
        constructor
        · simpa [hp2'] using hφ
        · intro x hx
          constructor
          · rw [hp2'] at hx
            exact hx.1
          · exact hx.2
    · rcases hpoll with hpoll1 | hpoll2
      · -- a poll₁ step: the moved timestamp `m` is `> t` (strict cross
        -- invariant), so no element `≤ t` is added to queue 2
        rcases hpoll1 with ⟨h1p, hp⟩
        rcases hp with ⟨_hp1', _hl1', _hs1', _hr1', hp2', _hl2', hs2', _hr2'⟩
        let m := Finset.min' (e' k).pend1 h1p
        by_cases hq : t ∈ (e' (k + 1)).recv2
        · exact Or.inl hq
        · right
          constructor
          · rw [hp2']
            exact Finset.mem_insert.mpr (Or.inr hφ)
          · have htl : t ≤ (e' k).last2 := h4 hφ
            have hcross : (e' k).last2 < m := h6 m (Finset.min'_mem (e' k).pend1 h1p)
            have hmlt : t < m := lt_of_le_of_lt htl hcross
            intro x hx
            constructor
            · have hxne : x ≠ m := ne_of_lt (lt_of_le_of_lt hx.2 hmlt)
              rw [hp2'] at hx
              exact (Finset.mem_insert.mp hx.1).resolve_left hxne
            · exact hx.2
      · -- a poll₂ step: like the single queue
        rcases hpoll2 with ⟨h2p, hp⟩
        rcases hp with ⟨hp2', hr2', _hl2', _hp1', _hl1', _hs1', _hr1', _hs2'⟩
        let m := Finset.min' (e' k).pend2 h2p
        by_cases hq : t ∈ (e' (k + 1)).recv2
        · exact Or.inl hq
        · right
          constructor
          · have htm : t ≠ m := by
              intro htm
              have htR : t ∈ (e' (k + 1)).recv2 := by
                rw [hr2', htm]
                exact Finset.mem_insert_self m (e' k).recv2
              exact hq htR
            rw [hp2']
            exact Finset.mem_erase.mpr ⟨htm, hφ⟩
          · intro x hx
            constructor
            · rw [hp2'] at hx
              exact (Finset.erase_subset m (e' k).pend2) hx.1
            · exact hx.2
  · -- C3: a poll₂ step reduces `δ₂`
    intro e' _hH k hφ hpoll2
    rcases hpoll2 with ⟨h2p, hp⟩
    rcases hp with ⟨hp2', _hr2', _hl2', _hp1', _hl1', _hs1', _hr1', _hs2'⟩
    right
    let m := Finset.min' (e' k).pend2 h2p
    refine ⟨m, ?_, ?_⟩
    · constructor
      · simpa [m] using Finset.min'_mem (e' k).pend2 h2p
      · have hmin := (Finset.isLeast_min' (e' k).pend2 h2p).2 hφ
        simpa [m] using hmin
    · intro hδ
      have hmnot : m ∉ (e' (k + 1)).pend2 := by
        rw [hp2']
        simp [m]
      exact hmnot hδ.1

/-! ## End-to-end liveness by chaining (Rule 7) -/

/-- End-to-end response: `(□◇ poll₁) ∧ (□◇ poll₂) ⊢ sent₁ t ↝ recv₂ t`.
The single-queue lemmas are chained with Rule 7; when a poll₁ removes `t`
itself, `D2` hands off to `q2_liveness` via the coupling invariant. -/
theorem cascade_liveness (t : Nat) :
    Tla.Entails
      (Tla.tlaAnd (Tla.statePred Init)
        (Tla.tlaAnd (Tla.always (Tla.actionPred Next))
          (Tla.tlaAnd (Tla.always (Tla.eventually (Tla.actionPred Poll1)))
            (Tla.always (Tla.eventually (Tla.actionPred Poll2))))))
      (Tla.leadsTo (Tla.statePred (fun s => t ∈ s.sent1))
        (Tla.statePred (fun s => t ∈ s.recv2))) := by
  intro e h
  rcases h with ⟨hInit, hNextJ⟩
  rcases hNextJ with ⟨hNext, hJ⟩
  rcases hJ with ⟨hJ1, hJ2⟩
  refine Tla.relational_ranking_rule_leadsTo
    (p := fun s => t ∈ s.sent1) (q := fun s => t ∈ s.recv2) (r := Poll1)
    (φ := fun s => t ∈ s.pend1)
    (δ := fun s τ => τ ∈ s.pend1 ∧ τ ≤ t)
    (R := fun s τ => τ ∈ s.pend1)
    (H := Tla.tlaAnd (Tla.statePred Init)
      (Tla.tlaAnd (Tla.always (Tla.actionPred Next))
        (Tla.tlaAnd (Tla.always (Tla.eventually (Tla.actionPred Poll1)))
          (Tla.always (Tla.eventually (Tla.actionPred Poll2))))))
    ?_ ?_ ?_ ?_ ?_ e ⟨hInit, ⟨hNext, ⟨hJ1, hJ2⟩⟩⟩
  · intro e' n
    simp
  · -- D1: a sent message is either pending in queue 1, or has reached
    -- queue 2 and `q2_liveness` delivers it
    intro e' hH k hp
    rcases hH with ⟨hInit', hNext'⟩
    rcases hNext' with ⟨hNext'', hJ⟩
    rcases hJ with ⟨hJ1', hJ2'⟩
    have hInit0 : Init (e' 0) := by
      simpa [Tla.statePred, Cslib.ωSequence.drop] using hInit'
    have hNextAll : ∀ m, Next (e' m) (e' (m + 1)) := by
      intro m
      have hm := hNext'' m
      simpa [Tla.actionPred, Cslib.ωSequence.drop, Nat.add_comm] using hm
    have hIk := inv_inductive t e' hInit0 hNextAll k
    rcases hIk with ⟨h1, _h2, _h3, _h4, h5, _h6, _h7, _h8, _h9⟩
    by_cases hq : t ∈ (e' k).recv2
    · left
      exact Tla.eventually_imp (Tla.statePred (fun s => t ∈ s.recv2)) e' k
        (by simpa [Tla.statePred, Cslib.ωSequence.drop] using hq)
    · rcases h1 hp with hrecv1 | hpend1
      · -- `t` was received from queue 1: by the coupling invariant it is
        -- in queue 2, and `q2_liveness` delivers `recv₂ t`
        left
        have hcouple : t ∈ (e' k).sent2 := h5 hrecv1
        have hq2ev : Tla.eventually (Tla.statePred (fun s => t ∈ s.recv2)) (e'.drop k) := by
          have hq2 : Tla.leadsTo (Tla.statePred (fun s => t ∈ s.sent2))
              (Tla.statePred (fun s => t ∈ s.recv2)) e' :=
            q2_liveness t e' ⟨hInit', ⟨hNext'', hJ2'⟩⟩
          have hp2' : Tla.statePred (fun s => t ∈ s.sent2) (e'.drop k) := by
            simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_comm] using hcouple
          exact hq2 k hp2'
        exact hq2ev
      · -- `t` is pending in queue 1: the invariant `φ` holds with `δ₁ ⊆ R₁`
        right
        refine ⟨hpend1, ?_⟩
        intro τ hτ
        exact hτ.1
  · -- D2: while `t` is pending in queue 1, `φ` persists and `δ₁` is
    -- conserved; if a poll₁ removes `t`, it enters queue 2 and
    -- `q2_liveness` delivers `recv₂ t`
    intro e' hH k hφ
    rcases hH with ⟨hInit', hNext'⟩
    rcases hNext' with ⟨hNext'', hJ⟩
    rcases hJ with ⟨hJ1', hJ2'⟩
    have hInit0 : Init (e' 0) := by
      simpa [Tla.statePred, Cslib.ωSequence.drop] using hInit'
    have hNextAll : ∀ m, Next (e' m) (e' (m + 1)) := by
      intro m
      have hm := hNext'' m
      simpa [Tla.actionPred, Cslib.ωSequence.drop, Nat.add_comm] using hm
    have hIk := inv_inductive t e' hInit0 hNextAll k
    rcases hIk with ⟨_h1, h2, _h3, _h4, _h5, _h6, _h7, _h8, _h9⟩
    rcases hNextAll k with hsend | hpoll
    · -- a send into queue 1
      rcases hsend with ⟨u, hsend'⟩
      rcases hsend' with ⟨hu, hp1', _hl1', _hs1', _hr1', _hp2', _hl2', _hs2', _hr2'⟩
      by_cases hq : t ∈ (e' (k + 1)).recv2
      · left
        have hq2ev : Tla.eventually (Tla.statePred (fun s => t ∈ s.recv2))
            ((e'.drop k).drop 1) := by
          simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (Tla.eventually_imp (Tla.statePred (fun s => t ∈ s.recv2)) e' (k + 1)
              (by simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_comm] using hq))
        rcases hq2ev with ⟨t0, ht0⟩
        refine ⟨1 + t0, ?_⟩
        simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using ht0
      · right
        constructor
        · rw [hp1']
          exact Finset.mem_insert.mpr (Or.inr hφ)
        · have htl : t ≤ (e' k).last1 := h2 hφ
          have hut : u > t := lt_of_le_of_lt htl hu
          intro x hx
          constructor
          · have hxne : x ≠ u := ne_of_lt (lt_of_le_of_lt hx.2 hut)
            rw [hp1'] at hx
            exact (Finset.mem_insert.mp hx.1).resolve_left hxne
          · exact hx.2
    · rcases hpoll with hpoll1 | hpoll2
      · -- a poll₁ step
        rcases hpoll1 with ⟨h1p, hp⟩
        rcases hp with ⟨hp1', _hl1', _hs1', hr1', _hp2', _hl2', hs2', _hr2'⟩
        let m := Finset.min' (e' k).pend1 h1p
        by_cases htm : t = m
        · -- `t` was removed from queue 1: it is now in queue 2, and
          -- `q2_liveness` delivers `recv₂ t`
          left
          have hcouple : t ∈ (e' (k + 1)).sent2 := by
            rw [hs2', htm]
            exact Finset.mem_insert_self m (e' k).sent2
          have hq2ev : Tla.eventually (Tla.statePred (fun s => t ∈ s.recv2))
              ((e'.drop k).drop 1) := by
            have hq2 : Tla.leadsTo (Tla.statePred (fun s => t ∈ s.sent2))
                (Tla.statePred (fun s => t ∈ s.recv2)) e' :=
              q2_liveness t e' ⟨hInit', ⟨hNext'', hJ2'⟩⟩
            simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              hq2 (k + 1) (by
                simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
                  Nat.add_left_comm] using hcouple)
          rcases hq2ev with ⟨t0, ht0⟩
          refine ⟨1 + t0, ?_⟩
          simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using ht0
        · -- `t` stays in queue 1 and `δ₁` is conserved
          right
          constructor
          · rw [hp1']
            exact Finset.mem_erase.mpr ⟨htm, hφ⟩
          · intro x hx
            constructor
            · rw [hp1'] at hx
              exact (Finset.erase_subset m (e' k).pend1) hx.1
            · exact hx.2
      · -- a poll₂ step: queue 1 is untouched
        rcases hpoll2 with ⟨h2p, hp⟩
        rcases hp with ⟨_hp2', _hr2', _hl2', hp1', _hl1', _hs1', _hr1', _hs2'⟩
        right
        constructor
        · simpa [hp1'] using hφ
        · intro x hx
          constructor
          · rw [hp1'] at hx
            exact hx.1
          · exact hx.2
  · -- D3: a poll₁ step reduces `δ₁` (the minimum pending timestamp)
    intro e' _hH k hφ hpoll1
    rcases hpoll1 with ⟨h1p, hp⟩
    rcases hp with ⟨hp1', _hl1', _hs1', _hr1', _hp2', _hl2', _hs2', _hr2'⟩
    right
    let m := Finset.min' (e' k).pend1 h1p
    refine ⟨m, ?_, ?_⟩
    · constructor
      · simpa [m] using Finset.min'_mem (e' k).pend1 h1p
      · have hmin := (Finset.isLeast_min' (e' k).pend1 h1p).2 hφ
        simpa [m] using hmin
    · intro hδ
      have hmnot : m ∉ (e' (k + 1)).pend1 := by
        rw [hp1']
        simp [m]
      exact hmnot hδ.1
  · -- D4: while `t` is pending in queue 1, poll₁ fires eventually (justice)
    intro e' hH k _hφ
    rcases hH with ⟨_hInit', hNext'⟩
    rcases hNext' with ⟨_hNext'', hJ⟩
    rcases hJ with ⟨hJ1', _hJ2'⟩
    right
    exact hJ1' k

end TlaDsl.Examples.CascadedQueues
