import TlaDsl.Basic
import TlaDsl.Notation
import TlaDsl.RelRank
import TlaDsl.Tactic
import Mathlib.Tactic.FinCases

set_option maxHeartbeats 4000000

open scoped Tla

/-! # Reordering queues: lexicographic relational ranking (Rule 10)

The paper's §3.4 example (Fig. 4): a queue whose messages have two
classes, `A` and `B`, with a separate polling action per class. `poll₁A`
moves the earliest class-`A` message to the FIFO queue 2, `poll₁B` the
earliest class-`B` message; queue 2 delivers in arrival order. Class-`B`
messages can therefore *bypass* a class-`A` message `t` while it waits in
queue 1, so no single finite ranking can bound how long `t` waits.

The lexicographic ranking of Rule 10 solves it:

* `δ₀(τ) = pend₁(τ) ∧ A(τ) ∧ τ ≤ t` — class-`A` messages before `t` in
  queue 1 (high priority);
* `δ₁ = {a | (a, τ) ∈ queue₂ ∧ a ≤ ta(t)}` — arrivals in queue 2 no later
  than `t`'s own arrival (low priority);
* schedulers `ψ₀ = t ∈ pend₁`, `ψ₁ = t ∈ queue₂`.

While `t` is in queue 1 (`ψ₀`), `δ₁` is *preempted* and may grow — that is
the bypassing. When `t` reaches queue 2 (`ψ₁`), `δ₁` is conserved (no new
arrival can be earlier than `t`'s) and reduced by `poll₂`. The conclusion
is `(□◇ poll₁A) ∧ (□◇ poll₂) ⊢ sent₁(t) ↝ recv₂(t)`.

Model note: both classes share one strictly-increasing timestamp counter
`last`, so timestamps are globally unique — a class-`B` message can never
carry the tracked class-`A` timestamp `t`. This is what keeps `δ₁`
conserved when `poll₁B` adds a new arrival while `t` is already in queue 2.
-/

namespace TlaDsl.Examples.LexReordering

/-- Two-class queue 1 (`pendA`/`pendB`), a shared timestamp counter, a
FIFO queue 2 of (arrival-number, timestamp) pairs, and history flags. -/
structure St where
  pendA : Finset Nat
  last : Nat
  sentA : Finset Nat
  pendB : Finset Nat
  queue2 : Finset (Nat × Nat)
  arrNext : Nat
  recv2 : Finset Nat

/-- Send a class-`A` message (timestamps strictly increase, shared). -/
def SendA (u : Nat) : Tla.Action St :=
  fun s s' =>
    u > s.last ∧ s'.pendA = insert u s.pendA ∧ s'.last = u ∧
      s'.sentA = insert u s.sentA ∧ s'.pendB = s.pendB ∧
      s'.queue2 = s.queue2 ∧ s'.arrNext = s.arrNext ∧ s'.recv2 = s.recv2

/-- Send a class-`B` message (same shared timestamp counter). -/
def SendB (u : Nat) : Tla.Action St :=
  fun s s' =>
    u > s.last ∧ s'.pendB = insert u s.pendB ∧ s'.last = u ∧
      s'.pendA = s.pendA ∧ s'.sentA = s.sentA ∧ s'.queue2 = s.queue2 ∧
      s'.arrNext = s.arrNext ∧ s'.recv2 = s.recv2

/-- Poll the earliest class-`A` message into queue 2. -/
def Poll1A : Tla.Action St :=
  fun s s' =>
    ∃ h : s.pendA.Nonempty,
      s'.pendA = s.pendA.erase (Finset.min' s.pendA h) ∧ s'.last = s.last ∧
        s'.sentA = s.sentA ∧ s'.pendB = s.pendB ∧
        s'.queue2 = insert (s.arrNext, Finset.min' s.pendA h) s.queue2 ∧
        s'.arrNext = s.arrNext + 1 ∧ s'.recv2 = s.recv2

/-- Poll the earliest class-`B` message into queue 2. -/
def Poll1B : Tla.Action St :=
  fun s s' =>
    ∃ h : s.pendB.Nonempty,
      s'.pendB = s.pendB.erase (Finset.min' s.pendB h) ∧ s'.last = s.last ∧
        s'.pendA = s.pendA ∧ s'.sentA = s.sentA ∧
        s'.queue2 = insert (s.arrNext, Finset.min' s.pendB h) s.queue2 ∧
        s'.arrNext = s.arrNext + 1 ∧ s'.recv2 = s.recv2

/-- Queue 2 delivers the earliest arrival. -/
def Poll2 : Tla.Action St :=
  fun s s' =>
    ∃ p : Nat × Nat, p ∈ s.queue2 ∧ (∀ q : Nat × Nat, q ∈ s.queue2 → p.1 ≤ q.1) ∧
      s'.queue2 = s.queue2.erase p ∧ s'.recv2 = insert p.2 s.recv2 ∧
      s'.arrNext = s.arrNext ∧ s'.pendA = s.pendA ∧ s'.last = s.last ∧
      s'.sentA = s.sentA ∧ s'.pendB = s.pendB

/-- A step: send, poll-`A`, poll-`B`, or queue-2 delivery. -/
def Next : Tla.Action St :=
  fun s s' => (∃ u : Nat, SendA u s s') ∨ (∃ u : Nat, SendB u s s') ∨
    Poll1A s s' ∨ Poll1B s s' ∨ Poll2 s s'

/-- Everything starts empty. -/
def Init : Tla.StatePred St :=
  fun s => s.pendA = ∅ ∧ s.last = 0 ∧ s.sentA = ∅ ∧ s.pendB = ∅ ∧
    s.queue2 = ∅ ∧ s.arrNext = 0 ∧ s.recv2 = ∅

/-! ## `minArrival`: the arrival of a timestamp in queue 2 -/

/-- The minimum arrival number of a pair with timestamp `t` in `q` (0 if
none). Deterministic and total; the three lemmas below isolate the
(expensive) image/min machinery so the liveness proofs stay cheap. -/
noncomputable def minArrival (q : Finset (Nat × Nat)) (t : Nat) : Nat := by
  classical
  let I : Finset Nat := (q.filter (fun p => p.2 = t)).image Prod.fst
  exact if h : I.Nonempty then I.min' h else 0

/-- If `t` has an arrival, `minArrival` is one of its pairs. -/
lemma minArrival_mem {q : Finset (Nat × Nat)} {t : Nat} (h : ∃ a, (a, t) ∈ q) :
    (minArrival q t, t) ∈ q := by
  classical
  let I : Finset Nat := (q.filter (fun p => p.2 = t)).image Prod.fst
  have hne : I.Nonempty := by
    rcases h with ⟨a, ha⟩
    exact ⟨a, by simp [I, Finset.mem_image, Finset.mem_filter, ha]⟩
  have hm : I.min' hne ∈ I := Finset.min'_mem I hne
  rcases Finset.mem_image.mp hm with ⟨p, hp, hpfst⟩
  have hp2 : p.2 = t := (Finset.mem_filter.mp hp).2
  have hmin : minArrival q t = p.1 := by
    rw [minArrival]
    simp [I, hne, hpfst]
  rw [hmin]
  rw [← hp2]
  exact (Finset.mem_filter.mp hp).1

/-- Adding a pair with a different timestamp does not change `minArrival`. -/
lemma minArrival_insert_ne {q : Finset (Nat × Nat)} {t a m : Nat} (hne : m ≠ t) :
    minArrival (insert (a, m) q) t = minArrival q t := by
  classical
  have hfilter : (insert (a, m) q).filter (fun p => p.2 = t) =
      q.filter (fun p => p.2 = t) := by
    apply Finset.ext
    intro p
    constructor
    · intro hp
      have hp' := Finset.mem_filter.mp hp
      rcases Finset.mem_insert.mp hp'.1 with hpp | hpq
      · exfalso
        rw [hpp] at hp'
        exact hne hp'.2
      · exact Finset.mem_filter.mpr ⟨hpq, hp'.2⟩
    · intro hp
      have hp' := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_insert.mpr (Or.inr hp'.1), hp'.2⟩
  let I : Finset Nat := (q.filter (fun p => p.2 = t)).image Prod.fst
  let I' : Finset Nat := ((insert (a, m) q).filter (fun p => p.2 = t)).image Prod.fst
  have himg : I' = I := by
    simp [I, I', hfilter]
  by_cases h : I.Nonempty
  · have h' : I'.Nonempty := by
      rw [himg]
      exact h
    rw [minArrival, minArrival]
    rw [dif_pos h', dif_pos h]
    rw [Finset.min'_eq_iff]
    constructor
    · rw [hfilter]
      exact Finset.min'_mem ((q.filter (fun p => p.2 = t)).image Prod.fst) h
    · intro b hb
      rw [hfilter] at hb
      exact (Finset.isLeast_min' ((q.filter (fun p => p.2 = t)).image Prod.fst) h).2 hb
  · have h' : ¬ I'.Nonempty := by
      rw [himg]
      exact h
    rw [minArrival, minArrival]
    rw [dif_neg h', dif_neg h]

/-- Removing a pair with a different timestamp does not change `minArrival`. -/
lemma minArrival_erase_ne {q : Finset (Nat × Nat)} {t : Nat} {p : Nat × Nat}
    (hne : p.2 ≠ t) : minArrival (q.erase p) t = minArrival q t := by
  classical
  have hfilter : (q.erase p).filter (fun q2 => q2.2 = t) =
      q.filter (fun q2 => q2.2 = t) := by
    apply Finset.ext
    intro q2
    constructor
    · intro hq
      have hq' := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hq'.1).2, hq'.2⟩
    · intro hq
      have hq' := Finset.mem_filter.mp hq
      refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨?_, hq'.1⟩, hq'.2⟩
      intro hqp
      have : p.2 = t := by rw [← hqp, hq'.2]
      exact hne this
  let I : Finset Nat := (q.filter (fun q2 => q2.2 = t)).image Prod.fst
  let I' : Finset Nat := ((q.erase p).filter (fun q2 => q2.2 = t)).image Prod.fst
  have himg : I' = I := by
    simp [I, I', hfilter]
  by_cases h : I.Nonempty
  · have h' : I'.Nonempty := by
      rw [himg]
      exact h
    rw [minArrival, minArrival]
    rw [dif_pos h', dif_pos h]
    rw [Finset.min'_eq_iff]
    constructor
    · rw [hfilter]
      exact Finset.min'_mem ((q.filter (fun q2 => q2.2 = t)).image Prod.fst) h
    · intro b hb
      rw [hfilter] at hb
      exact (Finset.isLeast_min' ((q.filter (fun q2 => q2.2 = t)).image Prod.fst) h).2 hb
  · have h' : ¬ I'.Nonempty := by
      rw [himg]
      exact h
    rw [minArrival, minArrival]
    rw [dif_neg h', dif_neg h]

/-- The arrival number of timestamp `t` in queue 2. -/
noncomputable def ArrT (s : St) (t : Nat) : Nat := minArrival s.queue2 t

/-! ## The rankings and schedulers -/

/-- `δ₀`: class-`A` pending messages with timestamp `≤ t`. -/
def Delta0 (t : Nat) (s : St) : Finset Nat :=
  s.pendA.filter (fun τ => τ ≤ t)

/-- `δ₁`: arrivals in queue 2 no later than `t`'s own arrival. -/
noncomputable def Delta1 (s : St) (t : Nat) : Finset Nat :=
  (s.queue2.filter (fun p => p.1 ≤ ArrT s t)).image Prod.fst

/-- The two ranking components. -/
noncomputable def deltas (t : Nat) (i : Fin 2) (s : St) : Finset Nat :=
  if i.val = 0 then Delta0 t s else Delta1 s t

/-- The schedulers: `ψ₀ = t ∈ pend₁`, `ψ₁ = t ∈ queue₂`. -/
def psis (t : Nat) (i : Fin 2) (s : St) : Prop :=
  if i.val = 0 then t ∈ s.pendA else ∃ a : Nat, (a, t) ∈ s.queue2

/-- The justice actions: `r₀ = poll₁A`, `r₁ = poll₂`. -/
def rjs : Fin 2 → Tla.Action St :=
  fun i => if i.val = 0 then Poll1A else Poll2

/-! ## The inductive invariant -/

/-- Sent timestamps are bounded by the shared counter, the pipeline holds
for `t`, arrivals are bounded and distinct, and class-`B` pending messages
are never class-`A` sent and stay bounded (the unique-timestamp invariant:
the shared counter makes all timestamps globally distinct). -/
def Inv (t : Nat) (s : St) : Prop :=
  (∀ τ : Nat, τ ∈ s.sentA → τ ≤ s.last) ∧
  (t ∈ s.sentA → t ∈ s.recv2 ∨ t ∈ s.pendA ∨ (∃ a : Nat, (a, t) ∈ s.queue2)) ∧
  (∀ p : Nat × Nat, p ∈ s.queue2 → p.1 < s.arrNext) ∧
  (∀ p : Nat × Nat, p ∈ s.queue2 → ∀ q : Nat × Nat, q ∈ s.queue2 →
    p.1 = q.1 → p = q) ∧
  (∀ τ : Nat, τ ∈ s.pendB → τ ∉ s.sentA) ∧
  (∀ τ : Nat, τ ∈ s.pendB → τ ≤ s.last)

/-- `Inv t` is preserved by every step of `Next`. -/
theorem inv_step (t : Nat) (s s' : St) (h : Inv t s) (hstep : Next s s') : Inv t s' := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
  rcases hstep with hsendA | hrest
  · -- a class-A send
    rcases hsendA with ⟨u, hsendA'⟩
    rcases hsendA' with ⟨hu, hpa', hla', hsa', hpb', hq2', han', hr2'⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro τ hτ
      rw [hsa'] at hτ
      rcases Finset.mem_insert.mp hτ with hτu | hτs
      · rw [hla']
        exact le_of_eq hτu
      · rw [hla']
        exact le_trans (h1 τ hτs) (le_of_lt hu)
    · intro ht
      rw [hsa'] at ht
      rcases Finset.mem_insert.mp ht with htu | hts
      · right
        left
        rw [hpa', htu]
        exact Finset.mem_insert_self u s.pendA
      · rcases h2 hts with hr | hp | hq
        · left
          rw [hr2']
          exact hr
        · right
          left
          rw [hpa']
          exact Finset.mem_insert.mpr (Or.inr hp)
        · right
          right
          rw [hq2']
          exact hq
    · intro p hp
      have hp' : p ∈ s.queue2 := by
        rw [hq2'] at hp
        exact hp
      rw [han']
      exact h3 p hp'
    · intro p hp q hq hpq
      have hp' : p ∈ s.queue2 := by
        rw [hq2'] at hp
        exact hp
      have hq' : q ∈ s.queue2 := by
        rw [hq2'] at hq
        exact hq
      exact h4 p hp' q hq' hpq
    · intro τ hτ
      have hτ' : τ ∈ s.pendB := by
        rw [hpb'] at hτ
        exact hτ
      intro h
      rw [hsa'] at h
      rcases Finset.mem_insert.mp h with hτu | hτs
      · have hτl : τ ≤ s.last := h6 τ hτ'
        omega
      · exact h5 τ hτ' hτs
    · intro τ hτ
      have hτ' : τ ∈ s.pendB := by
        rw [hpb'] at hτ
        exact hτ
      rw [hla']
      exact le_trans (h6 τ hτ') (le_of_lt hu)
  · rcases hrest with hsendB | hrest
    · -- a class-B send
      rcases hsendB with ⟨u, hsendB'⟩
      rcases hsendB' with ⟨hu, hpb', hla', hpa', hsa', hq2', han', hr2'⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro τ hτ
        have hτ' : τ ∈ s.sentA := by
          rw [hsa'] at hτ
          exact hτ
        rw [hla']
        exact le_trans (h1 τ hτ') (le_of_lt hu)
      · intro ht
        have hts : t ∈ s.sentA := by
          rw [hsa'] at ht
          exact ht
        rcases h2 hts with hr | hp | hq
        · left
          rw [hr2']
          exact hr
        · right
          left
          rw [hpa']
          exact hp
        · right
          right
          rw [hq2']
          exact hq
      · intro p hp
        have hp' : p ∈ s.queue2 := by
          rw [hq2'] at hp
          exact hp
        rw [han']
        exact h3 p hp'
      · intro p hp q hq hpq
        have hp' : p ∈ s.queue2 := by
          rw [hq2'] at hp
          exact hp
        have hq' : q ∈ s.queue2 := by
          rw [hq2'] at hq
          exact hq
        exact h4 p hp' q hq' hpq
      · intro τ hτ
        rw [hpb'] at hτ
        rcases Finset.mem_insert.mp hτ with hτu | hτs
        · intro h
          rw [hsa', hτu] at h
          have hul : u ≤ s.last := h1 u h
          omega
        · intro h
          rw [hsa'] at h
          exact h5 τ hτs h
      · intro τ hτ
        rw [hpb'] at hτ
        rcases Finset.mem_insert.mp hτ with hτu | hτs
        · rw [hla']
          exact le_of_eq hτu
        · rw [hla']
          exact le_trans (h6 τ hτs) (le_of_lt hu)
    · rcases hrest with hp1a | hrest
      · -- a poll of the earliest class-A message
        rcases hp1a with ⟨h, hp⟩
        rcases hp with ⟨hpa', hla', hsa', hpb', hq2', han', hr2'⟩
        let m := Finset.min' s.pendA h
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro τ hτ
          have hτ' : τ ∈ s.sentA := by
            rw [hsa'] at hτ
            exact hτ
          rw [hla']
          exact h1 τ hτ'
        · intro ht
          have hts : t ∈ s.sentA := by
            rw [hsa'] at ht
            exact ht
          rcases h2 hts with hr | hp | hq
          · left
            rw [hr2']
            exact hr
          · by_cases htm : t = m
            · right
              right
              refine ⟨s.arrNext, ?_⟩
              rw [hq2', htm]
              exact Finset.mem_insert_self (s.arrNext, m) s.queue2
            · right
              left
              rw [hpa']
              exact Finset.mem_erase.mpr ⟨htm, hp⟩
          · right
            right
            rcases hq with ⟨a, hq⟩
            refine ⟨a, ?_⟩
            rw [hq2']
            exact Finset.mem_insert.mpr (Or.inr hq)
        · intro p hp
          rw [hq2'] at hp
          rcases Finset.mem_insert.mp hp with hpq | hpq2
          · rw [hpq, han']
            exact Nat.lt_succ_self s.arrNext
          · have hp' : p ∈ s.queue2 := hpq2
            rw [han']
            exact lt_trans (h3 p hp') (Nat.lt_succ_self s.arrNext)
        · intro p hp q hq hpq
          rw [hq2'] at hp
          rcases Finset.mem_insert.mp hp with hpq1 | hpq2
          · rw [hq2'] at hq
            rcases Finset.mem_insert.mp hq with hqq1 | hqq2
            · exact hpq1.trans hqq1.symm
            · have hq1 : q.1 = s.arrNext := by
                rw [hpq1] at hpq
                simpa using hpq.symm
              have hlt : q.1 < s.arrNext := h3 q hqq2
              exfalso
              omega
          · have hp' : p ∈ s.queue2 := hpq2
            rw [hq2'] at hq
            rcases Finset.mem_insert.mp hq with hqq1 | hqq2
            · have hq1 : p.1 = s.arrNext := by
                rw [hqq1] at hpq
                exact hpq
              have hlt : p.1 < s.arrNext := h3 p hp'
              exfalso
              omega
            · exact h4 p hp' q hqq2 hpq
        · intro τ hτ
          have hτ' : τ ∈ s.pendB := by
            rw [hpb'] at hτ
            exact hτ
          intro h
          rw [hsa'] at h
          exact h5 τ hτ' h
        · intro τ hτ
          have hτ' : τ ∈ s.pendB := by
            rw [hpb'] at hτ
            exact hτ
          rw [hla']
          exact h6 τ hτ'
      · rcases hrest with hp1b | hp2
        · -- a poll of the earliest class-B message
          rcases hp1b with ⟨h, hp⟩
          rcases hp with ⟨hpb', hla', hpa', hsa', hq2', han', hr2'⟩
          let m := Finset.min' s.pendB h
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro τ hτ
            have hτ' : τ ∈ s.sentA := by
              rw [hsa'] at hτ
              exact hτ
            rw [hla']
            exact h1 τ hτ'
          · intro ht
            have hts : t ∈ s.sentA := by
              rw [hsa'] at ht
              exact ht
            rcases h2 hts with hr | hp | hq
            · left
              rw [hr2']
              exact hr
            · right
              left
              rw [hpa']
              exact hp
            · right
              right
              rcases hq with ⟨a, hq⟩
              refine ⟨a, ?_⟩
              rw [hq2']
              exact Finset.mem_insert.mpr (Or.inr hq)
          · intro p hp
            rw [hq2'] at hp
            rcases Finset.mem_insert.mp hp with hpq | hpq2
            · rw [hpq, han']
              exact Nat.lt_succ_self s.arrNext
            · have hp' : p ∈ s.queue2 := hpq2
              rw [han']
              exact lt_trans (h3 p hp') (Nat.lt_succ_self s.arrNext)
          · intro p hp q hq hpq
            rw [hq2'] at hp
            rcases Finset.mem_insert.mp hp with hpq1 | hpq2
            · rw [hq2'] at hq
              rcases Finset.mem_insert.mp hq with hqq1 | hqq2
              · exact hpq1.trans hqq1.symm
              · have hq1 : q.1 = s.arrNext := by
                  rw [hpq1] at hpq
                  simpa using hpq.symm
                have hlt : q.1 < s.arrNext := h3 q hqq2
                exfalso
                omega
            · have hp' : p ∈ s.queue2 := hpq2
              rw [hq2'] at hq
              rcases Finset.mem_insert.mp hq with hqq1 | hqq2
              · have hq1 : p.1 = s.arrNext := by
                  rw [hqq1] at hpq
                  exact hpq
                have hlt : p.1 < s.arrNext := h3 p hp'
                exfalso
                omega
              · exact h4 p hp' q hqq2 hpq
          · intro τ hτ
            rw [hpb'] at hτ
            have hτ' : τ ∈ s.pendB := (Finset.mem_erase.mp hτ).2
            intro h
            rw [hsa'] at h
            exact h5 τ hτ' h
          · intro τ hτ
            rw [hpb'] at hτ
            have hτ' : τ ∈ s.pendB := (Finset.mem_erase.mp hτ).2
            rw [hla']
            exact h6 τ hτ'
        · -- queue-2 delivery
          rcases hp2 with ⟨p, hp, hmin, hq2', hr2', han', hpa', hla', hsa', hpb'⟩
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro τ hτ
            have hτ' : τ ∈ s.sentA := by
              rw [hsa'] at hτ
              exact hτ
            rw [hla']
            exact h1 τ hτ'
          · intro ht
            have hts : t ∈ s.sentA := by
              rw [hsa'] at ht
              exact ht
            rcases h2 hts with hr | hp | hq
            · left
              rw [hr2']
              exact Finset.mem_insert.mpr (Or.inr hr)
            · right
              left
              rw [hpa']
              exact hp
            · by_cases hpt : p.2 = t
              · left
                rw [hr2', ← hpt]
                exact Finset.mem_insert_self p.2 s.recv2
              · right
                right
                rcases hq with ⟨a, hq⟩
                refine ⟨a, ?_⟩
                rw [hq2']
                refine Finset.mem_erase.mpr ⟨?_, hq⟩
                intro heq
                exact hpt (congrArg Prod.snd heq).symm
          · intro q hq
            have hq' : q ∈ s.queue2 := by
              rw [hq2'] at hq
              exact (Finset.erase_subset p s.queue2) hq
            rw [han']
            exact h3 q hq'
          · intro p1 hp1 q1 hq1 hpq1
            have hp1' : p1 ∈ s.queue2 := by
              rw [hq2'] at hp1
              exact (Finset.erase_subset p s.queue2) hp1
            have hq1' : q1 ∈ s.queue2 := by
              rw [hq2'] at hq1
              exact (Finset.erase_subset p s.queue2) hq1
            exact h4 p1 hp1' q1 hq1' hpq1
          · intro τ hτ
            have hτ' : τ ∈ s.pendB := by
              rw [hpb'] at hτ
              exact hτ
            intro h
            rw [hsa'] at h
            exact h5 τ hτ' h
          · intro τ hτ
            have hτ' : τ ∈ s.pendB := by
              rw [hpb'] at hτ
              exact hτ
            rw [hla']
            exact h6 τ hτ'

/-- `Inv t` holds at every reachable state. -/
theorem inv_inductive (t : Nat) (e : Tla.Behavior St)
    (hInit : Init (e 0)) (hNext : ∀ m, Next (e m) (e (m + 1))) :
    ∀ k, Inv t (e k) := by
  intro k
  induction k with
  | zero =>
      rcases hInit with ⟨hpa0, hla0, hsa0, hpb0, hq20, han0, hr20⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro τ hτ
        rw [hsa0] at hτ
        exact False.elim ((Finset.notMem_empty τ) hτ)
      · intro ht
        rw [hsa0] at ht
        exact False.elim ((Finset.notMem_empty t) ht)
      · intro p hp
        rw [hq20] at hp
        exact False.elim ((Finset.notMem_empty p) hp)
      · intro p hp q hq hpq
        rw [hq20] at hp
        exact False.elim ((Finset.notMem_empty p) hp)
      · intro τ hτ
        rw [hpb0] at hτ
        exact False.elim ((Finset.notMem_empty τ) hτ)
      · intro τ hτ
        rw [hpb0] at hτ
        exact False.elim ((Finset.notMem_empty τ) hτ)
  | succ k ih =>
      exact inv_step t (e k) (e (k + 1)) ih (hNext k)

/-! ## The liveness theorem (Rule 10 instance) -/

/-- `(□◇ poll₁A) ∧ (□◇ poll₂) ⊢ sent₁(t) ↝ recv₂(t)` for a class-`A`
message `t`, via the lexicographic ranking `(δ₀, δ₁)` with schedulers
`ψ₀ = t ∈ pend₁`, `ψ₁ = t ∈ queue₂`. -/
theorem reorder_liveness (t : Nat) :
    Tla.Entails
      (Tla.tlaAnd (Tla.statePred Init)
        (Tla.tlaAnd (Tla.always (Tla.actionPred Next))
          (Tla.tlaAnd (Tla.always (Tla.eventually (Tla.actionPred Poll1A)))
            (Tla.always (Tla.eventually (Tla.actionPred Poll2))))))
      (Tla.leadsTo (Tla.statePred (fun s => t ∈ s.sentA))
        (Tla.statePred (fun s => t ∈ s.recv2))) := by
  intro e h
  rcases h with ⟨hInit, hNextJ⟩
  rcases hNextJ with ⟨hNext, hJ⟩
  rcases hJ with ⟨hJ1, hJ2⟩
  refine Tla.rel_rank_lex
    (p := fun s => t ∈ s.sentA) (q := fun s => t ∈ s.recv2)
    (φ := fun s => t ∈ s.sentA ∧ (t ∈ s.pendA ∨ (∃ a : Nat, (a, t) ∈ s.queue2)))
    (δs := deltas t) (ψs := psis t) (rs := rjs)
    (H := Tla.tlaAnd (Tla.statePred Init)
      (Tla.tlaAnd (Tla.always (Tla.actionPred Next))
        (Tla.tlaAnd (Tla.always (Tla.eventually (Tla.actionPred Poll1A)))
          (Tla.always (Tla.eventually (Tla.actionPred Poll2))))))
    ?_ ?_ ?_ ?_ e ⟨hInit, ⟨hNext, ⟨hJ1, hJ2⟩⟩⟩
  · -- S1: a sent message is received, in queue 1, or in queue 2
    intro e' hH k hp
    rcases hH with ⟨hInit', hNext'⟩
    rcases hNext' with ⟨hNext'', hJ⟩
    rcases hJ with ⟨_hJ1', _hJ2'⟩
    have hInit0 : Init (e' 0) := by
      simpa [Tla.statePred, Cslib.ωSequence.drop] using hInit'
    have hNextAll : ∀ m, Next (e' m) (e' (m + 1)) := by
      intro m
      have hm := hNext'' m
      simpa [Tla.actionPred, Cslib.ωSequence.drop, Nat.add_comm] using hm
    have hIk := inv_inductive t e' hInit0 hNextAll k
    rcases hIk.2.1 hp with hr | hpa | hq
    · left
      exact Tla.eventually_imp (Tla.statePred (fun s => t ∈ s.recv2)) e' k
        (by simpa [Tla.statePred, Cslib.ωSequence.drop] using hr)
    · right
      exact ⟨hp, Or.inl hpa⟩
    · right
      exact ⟨hp, Or.inr hq⟩
  · -- L2
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
    rcases hIk with ⟨h1, h2, h3, h4, h5, h6⟩
    rcases hNextAll k with hsendA | hrest
    · -- class-A send
      rcases hsendA with ⟨u, hsend'⟩
      rcases hsend' with ⟨hu, hpa', hla', hsa', hpb', hq2', han', hr2'⟩
      right
      constructor
      · change t ∈ (e' (k + 1)).sentA ∧ (t ∈ (e' (k + 1)).pendA ∨ ∃ a, (a, t) ∈ (e' (k + 1)).queue2)
        constructor
        · rw [hsa']
          exact Finset.mem_insert.mpr (Or.inr hφ.1)
        · rcases hφ.2 with hpa | hq
          · left
            rw [hpa']
            exact Finset.mem_insert.mpr (Or.inr hpa)
          · right
            rw [hq2']
            exact hq
      · constructor
        · intro i hnp
          fin_cases i
          · have htl : t ≤ (e' k).last := h1 t hφ.1
            have hut : u > t := lt_of_le_of_lt htl hu
            intro x hx
            simp [deltas, Delta0] at hx ⊢
            constructor
            · have hxne : x ≠ u := ne_of_lt (lt_of_le_of_lt hx.2 hut)
              rw [hpa'] at hx
              exact (Finset.mem_insert.mp hx.1).resolve_left hxne
            · exact hx.2
          · intro x hx
            simp [deltas, Delta1] at hx ⊢
            have hArr : ArrT (e' (k + 1)) t = ArrT (e' k) t := by
              change minArrival (e' (k + 1)).queue2 t = minArrival (e' k).queue2 t
              rw [hq2']
            rw [hq2', hArr] at hx
            exact hx
        · constructor
          · intro i
            fin_cases i
            · intro hreq hR
              rcases hR with ⟨h, hp⟩
              rcases hp with ⟨hpa', _hla', _hsa', _hpb', _hq2', _han', _hr2'⟩
              let m := Finset.min' (e' k).pendA h
              have hmle : m ≤ t := (Finset.isLeast_min' (e' k).pendA h).2 hreq.1
              refine ⟨m, ?_, ?_⟩
              · simp [deltas, Delta0]
                exact ⟨Finset.min'_mem (e' k).pendA h, hmle⟩
              · intro hδ
                simp [deltas, Delta0] at hδ
                rw [hpa'] at hδ
                exact (Finset.mem_erase.mp hδ.1).1 rfl
            · intro hreq hR
              rcases hR with ⟨p, hp, hmin, hq2', _hr2', _han', _hpa', _hla', _hsa', _hpb'⟩
              have hp' : (ArrT (e' k) t, t) ∈ (e' k).queue2 := by
                change (minArrival (e' k).queue2 t, t) ∈ (e' k).queue2
                exact minArrival_mem (by simpa [psis] using hreq.1)
              have hle1 : p.1 ≤ ArrT (e' k) t := hmin (ArrT (e' k) t, t) hp'
              refine ⟨p.1, ?_, ?_⟩
              · have hmem : p.1 ∈ Delta1 (e' k) t := by
                  change p.1 ∈ ((e' k).queue2.filter (fun q => q.1 ≤ ArrT (e' k) t)).image Prod.fst
                  exact Finset.mem_image.mpr ⟨p, ⟨Finset.mem_filter.mpr ⟨hp, hle1⟩, rfl⟩⟩
                simpa [deltas] using hmem
              · intro hδ
                rw [deltas] at hδ
                change p.1 ∈ ((e' (k + 1)).queue2.filter (fun q => q.1 ≤ ArrT (e' (k + 1)) t)).image Prod.fst at hδ
                rcases Finset.mem_image.mp hδ with ⟨q, hqmem, hqf⟩
                have hq1 : q.1 = p.1 := hqf
                have hqmem' : q ∈ (e' k).queue2 := by
                  have hq' : q ∈ (e' (k + 1)).queue2 := (Finset.mem_filter.mp hqmem).1
                  rw [hq2'] at hq'
                  exact (Finset.mem_erase.mp hq').2
                have hqne : q ≠ p := by
                  have hq' : q ∈ (e' (k + 1)).queue2 := (Finset.mem_filter.mp hqmem).1
                  rw [hq2'] at hq'
                  exact (Finset.mem_erase.mp hq').1
                have hsame : q = p := h4 q hqmem' p hp hq1
                exact hqne hsame
          · intro i
            fin_cases i
            · intro hreq hnr
              have hψ' : t ∈ (e' (k + 1)).pendA := by
                rw [hpa']
                exact Finset.mem_insert.mpr (Or.inr hreq.1)
              simpa [psis] using hψ'
            · intro hreq hnr
              have hψ' : ∃ a, (a, t) ∈ (e' (k + 1)).queue2 := by
                rw [hq2']
                simpa [psis] using hreq.1
              simpa [psis] using hψ'
    · rcases hrest with hsendB | hrest
      · -- class-B send
        rcases hsendB with ⟨u, hsend'⟩
        rcases hsend' with ⟨hu, hpb', hla', hpa', hsa', hq2', han', hr2'⟩
        right
        constructor
        · change t ∈ (e' (k + 1)).sentA ∧ (t ∈ (e' (k + 1)).pendA ∨ ∃ a, (a, t) ∈ (e' (k + 1)).queue2)
          constructor
          · rw [hsa']
            exact hφ.1
          · rcases hφ.2 with hpa | hq
            · left
              rw [hpa']
              exact hpa
            · right
              rw [hq2']
              exact hq
        · constructor
          · intro i hnp
            fin_cases i
            · intro x hx
              simp [deltas, Delta0] at hx ⊢
              rw [hpa'] at hx
              exact hx
            · intro x hx
              simp [deltas, Delta1] at hx ⊢
              have hArr : ArrT (e' (k + 1)) t = ArrT (e' k) t := by
                change minArrival (e' (k + 1)).queue2 t = minArrival (e' k).queue2 t
                rw [hq2']
              rw [hq2', hArr] at hx
              exact hx
          · constructor
            · intro i
              fin_cases i
              · intro hreq hR
                rcases hR with ⟨h, hp⟩
                rcases hp with ⟨hpa', _hla', _hsa', _hpb', _hq2', _han', _hr2'⟩
                let m := Finset.min' (e' k).pendA h
                have hmle : m ≤ t := (Finset.isLeast_min' (e' k).pendA h).2 hreq.1
                refine ⟨m, ?_, ?_⟩
                · simp [deltas, Delta0]
                  exact ⟨Finset.min'_mem (e' k).pendA h, hmle⟩
                · intro hδ
                  simp [deltas, Delta0] at hδ
                  rw [hpa'] at hδ
                  exact (Finset.mem_erase.mp hδ.1).1 rfl
              · intro hreq hR
                rcases hR with ⟨p, hp, hmin, hq2', _hr2', _han', _hpa', _hla', _hsa', _hpb'⟩
                have hp' : (ArrT (e' k) t, t) ∈ (e' k).queue2 := by
                  change (minArrival (e' k).queue2 t, t) ∈ (e' k).queue2
                  exact minArrival_mem (by simpa [psis] using hreq.1)
                have hle1 : p.1 ≤ ArrT (e' k) t := hmin (ArrT (e' k) t, t) hp'
                refine ⟨p.1, ?_, ?_⟩
                · have hmem : p.1 ∈ Delta1 (e' k) t := by
                    change p.1 ∈ ((e' k).queue2.filter (fun q => q.1 ≤ ArrT (e' k) t)).image Prod.fst
                    exact Finset.mem_image.mpr ⟨p, ⟨Finset.mem_filter.mpr ⟨hp, hle1⟩, rfl⟩⟩
                  simpa [deltas] using hmem
                · intro hδ
                  rw [deltas] at hδ
                  change p.1 ∈ ((e' (k + 1)).queue2.filter (fun q => q.1 ≤ ArrT (e' (k + 1)) t)).image Prod.fst at hδ
                  rcases Finset.mem_image.mp hδ with ⟨q, hqmem, hqf⟩
                  have hq1 : q.1 = p.1 := hqf
                  have hqmem' : q ∈ (e' k).queue2 := by
                    have hq' : q ∈ (e' (k + 1)).queue2 := (Finset.mem_filter.mp hqmem).1
                    rw [hq2'] at hq'
                    exact (Finset.mem_erase.mp hq').2
                  have hqne : q ≠ p := by
                    have hq' : q ∈ (e' (k + 1)).queue2 := (Finset.mem_filter.mp hqmem).1
                    rw [hq2'] at hq'
                    exact (Finset.mem_erase.mp hq').1
                  have hsame : q = p := h4 q hqmem' p hp hq1
                  exact hqne hsame
            · intro i
              fin_cases i
              · intro hreq hnr
                have hψ' : t ∈ (e' (k + 1)).pendA := by
                  rw [hpa']
                  exact hreq.1
                simpa [psis] using hψ'
              · intro hreq hnr
                have hψ' : ∃ a, (a, t) ∈ (e' (k + 1)).queue2 := by
                  rw [hq2']
                  simpa [psis] using hreq.1
                simpa [psis] using hψ'
      · rcases hrest with hp1a | hrest
        · -- poll₁A
          rcases hp1a with ⟨h, hp⟩
          rcases hp with ⟨hpa', hla', hsa', hpb', hq2', han', hr2'⟩
          let m := Finset.min' (e' k).pendA h
          right
          constructor
          · change t ∈ (e' (k + 1)).sentA ∧ (t ∈ (e' (k + 1)).pendA ∨ ∃ a, (a, t) ∈ (e' (k + 1)).queue2)
            constructor
            · rw [hsa']
              exact hφ.1
            · rcases hφ.2 with hpa | hq
              · by_cases htm : t = m
                · right
                  refine ⟨(e' k).arrNext, ?_⟩
                  rw [hq2', htm]
                  exact Finset.mem_insert_self ((e' k).arrNext, m) (e' k).queue2
                · left
                  rw [hpa']
                  exact Finset.mem_erase.mpr ⟨htm, hpa⟩
              · right
                rcases hq with ⟨a, hq⟩
                refine ⟨a, ?_⟩
                rw [hq2']
                exact Finset.mem_insert.mpr (Or.inr hq)
          · constructor
            · intro i hnp
              fin_cases i
              · intro x hx
                simp [deltas, Delta0] at hx ⊢
                constructor
                · rw [hpa'] at hx
                  exact (Finset.erase_subset m (e' k).pendA) hx.1
                · exact hx.2
              · have htA : t ∉ (e' k).pendA := by
                  intro h
                  exact hnp ⟨(0 : Fin 2), by decide, by simpa [psis] using h⟩
                have htq : ∃ a, (a, t) ∈ (e' k).queue2 := by
                  rcases hφ.2 with hpa | hq
                  · exact False.elim (htA hpa)
                  · exact hq
                have hArr : ArrT (e' k) t < (e' k).arrNext := by
                  have hp' : (ArrT (e' k) t, t) ∈ (e' k).queue2 := by
                    change (minArrival (e' k).queue2 t, t) ∈ (e' k).queue2
                    exact minArrival_mem htq
                  simpa using (h3 (ArrT (e' k) t, t) hp')
                have hne : m ≠ t := by
                  intro hmt
                  exact htA (by
                    rw [← hmt]
                    exact Finset.min'_mem (e' k).pendA h)
                intro x hx
                simp [deltas, Delta1] at hx ⊢
                have hArrE : ArrT (e' (k + 1)) t = ArrT (e' k) t := by
                  change minArrival (e' (k + 1)).queue2 t = minArrival (e' k).queue2 t
                  rw [hq2']
                  exact minArrival_insert_ne hne
                rw [hq2', hArrE] at hx
                constructor
                · rcases hx.1 with ⟨τ, hx1⟩
                  rcases Finset.mem_insert.mp hx1 with hxn | hxq
                  · have hxf : x = (e' k).arrNext := congrArg Prod.fst hxn
                    rw [hxf] at hx
                    exfalso
                    omega
                  · exact ⟨τ, hxq⟩
                · exact hx.2
            · constructor
              · intro i
                fin_cases i
                · intro hreq hR
                  rcases hR with ⟨h, hp⟩
                  rcases hp with ⟨hpa', _hla', _hsa', _hpb', _hq2', _han', _hr2'⟩
                  let m := Finset.min' (e' k).pendA h
                  have hmle : m ≤ t := (Finset.isLeast_min' (e' k).pendA h).2 hreq.1
                  refine ⟨m, ?_, ?_⟩
                  · simp [deltas, Delta0]
                    exact ⟨Finset.min'_mem (e' k).pendA h, hmle⟩
                  · intro hδ
                    simp [deltas, Delta0] at hδ
                    rw [hpa'] at hδ
                    exact (Finset.mem_erase.mp hδ.1).1 rfl
                · intro hreq hR
                  rcases hR with ⟨p, hp, hmin, hq2', _hr2', _han', _hpa', _hla', _hsa', _hpb'⟩
                  have hp' : (ArrT (e' k) t, t) ∈ (e' k).queue2 := by
                    change (minArrival (e' k).queue2 t, t) ∈ (e' k).queue2
                    exact minArrival_mem (by simpa [psis] using hreq.1)
                  have hle1 : p.1 ≤ ArrT (e' k) t := hmin (ArrT (e' k) t, t) hp'
                  refine ⟨p.1, ?_, ?_⟩
                  · have hmem : p.1 ∈ Delta1 (e' k) t := by
                      change p.1 ∈ ((e' k).queue2.filter (fun q => q.1 ≤ ArrT (e' k) t)).image Prod.fst
                      exact Finset.mem_image.mpr ⟨p, ⟨Finset.mem_filter.mpr ⟨hp, hle1⟩, rfl⟩⟩
                    simpa [deltas] using hmem
                  · intro hδ
                    rw [deltas] at hδ
                    change p.1 ∈ ((e' (k + 1)).queue2.filter (fun q => q.1 ≤ ArrT (e' (k + 1)) t)).image Prod.fst at hδ
                    rcases Finset.mem_image.mp hδ with ⟨q, hqmem, hqf⟩
                    have hq1 : q.1 = p.1 := hqf
                    have hqmem' : q ∈ (e' k).queue2 := by
                      have hq' : q ∈ (e' (k + 1)).queue2 := (Finset.mem_filter.mp hqmem).1
                      rw [hq2'] at hq'
                      exact (Finset.mem_erase.mp hq').2
                    have hqne : q ≠ p := by
                      have hq' : q ∈ (e' (k + 1)).queue2 := (Finset.mem_filter.mp hqmem).1
                      rw [hq2'] at hq'
                      exact (Finset.mem_erase.mp hq').1
                    have hsame : q = p := h4 q hqmem' p hp hq1
                    exact hqne hsame
              · intro i
                fin_cases i
                · intro hreq hnr
                  exact False.elim (hnr ⟨h, hpa', hla', hsa', hpb', hq2', han', hr2'⟩)
                · intro hreq hnr
                  have hq : ∃ a, (a, t) ∈ (e' k).queue2 := by
                    simpa [psis] using hreq.1
                  rcases hq with ⟨a, hq⟩
                  refine ⟨a, ?_⟩
                  rw [hq2']
                  exact Finset.mem_insert.mpr (Or.inr hq)
        · rcases hrest with hp1b | hp2
          · -- poll₁B
            rcases hp1b with ⟨h, hp⟩
            rcases hp with ⟨hpb', hla', hpa', hsa', hq2', han', hr2'⟩
            let m := Finset.min' (e' k).pendB h
            right
            constructor
            · change t ∈ (e' (k + 1)).sentA ∧ (t ∈ (e' (k + 1)).pendA ∨ ∃ a, (a, t) ∈ (e' (k + 1)).queue2)
              constructor
              · rw [hsa']
                exact hφ.1
              · rcases hφ.2 with hpa | hq
                · left
                  rw [hpa']
                  exact hpa
                · right
                  rcases hq with ⟨a, hq⟩
                  refine ⟨a, ?_⟩
                  rw [hq2']
                  exact Finset.mem_insert.mpr (Or.inr hq)
            · constructor
              · intro i hnp
                fin_cases i
                · intro x hx
                  simp [deltas, Delta0] at hx ⊢
                  rw [hpa'] at hx
                  exact hx
                · have htA : t ∉ (e' k).pendA := by
                    intro h
                    exact hnp ⟨(0 : Fin 2), by decide, by simpa [psis] using h⟩
                  have htq : ∃ a, (a, t) ∈ (e' k).queue2 := by
                    rcases hφ.2 with hpa | hq
                    · exact False.elim (htA hpa)
                    · exact hq
                  have hArr : ArrT (e' k) t < (e' k).arrNext := by
                    have hp' : (ArrT (e' k) t, t) ∈ (e' k).queue2 := by
                      change (minArrival (e' k).queue2 t, t) ∈ (e' k).queue2
                      exact minArrival_mem htq
                    simpa using (h3 (ArrT (e' k) t, t) hp')
                  have hne : m ≠ t := by
                    intro hmt
                    have hmB : m ∈ (e' k).pendB := Finset.min'_mem (e' k).pendB h
                    have hns : m ∉ (e' k).sentA := h5 m hmB
                    exact hns (by rw [hmt]; exact hφ.1)
                  intro x hx
                  simp [deltas, Delta1] at hx ⊢
                  have hArrE : ArrT (e' (k + 1)) t = ArrT (e' k) t := by
                    change minArrival (e' (k + 1)).queue2 t = minArrival (e' k).queue2 t
                    rw [hq2']
                    exact minArrival_insert_ne hne
                  rw [hq2', hArrE] at hx
                  constructor
                  · rcases hx.1 with ⟨τ, hx1⟩
                    rcases Finset.mem_insert.mp hx1 with hxn | hxq
                    · have hxf : x = (e' k).arrNext := congrArg Prod.fst hxn
                      rw [hxf] at hx
                      exfalso
                      omega
                    · exact ⟨τ, hxq⟩
                  · exact hx.2
              · constructor
                · intro i
                  fin_cases i
                  · intro hreq hR
                    rcases hR with ⟨h, hp⟩
                    rcases hp with ⟨hpa', _hla', _hsa', _hpb', _hq2', _han', _hr2'⟩
                    let m := Finset.min' (e' k).pendA h
                    have hmle : m ≤ t := (Finset.isLeast_min' (e' k).pendA h).2 hreq.1
                    refine ⟨m, ?_, ?_⟩
                    · simp [deltas, Delta0]
                      exact ⟨Finset.min'_mem (e' k).pendA h, hmle⟩
                    · intro hδ
                      simp [deltas, Delta0] at hδ
                      rw [hpa'] at hδ
                      exact (Finset.mem_erase.mp hδ.1).1 rfl
                  · intro hreq hR
                    rcases hR with ⟨p, hp, hmin, hq2', _hr2', _han', _hpa', _hla', _hsa', _hpb'⟩
                    have hp' : (ArrT (e' k) t, t) ∈ (e' k).queue2 := by
                      change (minArrival (e' k).queue2 t, t) ∈ (e' k).queue2
                      exact minArrival_mem (by simpa [psis] using hreq.1)
                    have hle1 : p.1 ≤ ArrT (e' k) t := hmin (ArrT (e' k) t, t) hp'
                    refine ⟨p.1, ?_, ?_⟩
                    · have hmem : p.1 ∈ Delta1 (e' k) t := by
                        change p.1 ∈ ((e' k).queue2.filter (fun q => q.1 ≤ ArrT (e' k) t)).image Prod.fst
                        exact Finset.mem_image.mpr ⟨p, ⟨Finset.mem_filter.mpr ⟨hp, hle1⟩, rfl⟩⟩
                      simpa [deltas] using hmem
                    · intro hδ
                      rw [deltas] at hδ
                      change p.1 ∈ ((e' (k + 1)).queue2.filter (fun q => q.1 ≤ ArrT (e' (k + 1)) t)).image Prod.fst at hδ
                      rcases Finset.mem_image.mp hδ with ⟨q, hqmem, hqf⟩
                      have hq1 : q.1 = p.1 := hqf
                      have hqmem' : q ∈ (e' k).queue2 := by
                        have hq' : q ∈ (e' (k + 1)).queue2 := (Finset.mem_filter.mp hqmem).1
                        rw [hq2'] at hq'
                        exact (Finset.mem_erase.mp hq').2
                      have hqne : q ≠ p := by
                        have hq' : q ∈ (e' (k + 1)).queue2 := (Finset.mem_filter.mp hqmem).1
                        rw [hq2'] at hq'
                        exact (Finset.mem_erase.mp hq').1
                      have hsame : q = p := h4 q hqmem' p hp hq1
                      exact hqne hsame
                · intro i
                  fin_cases i
                  · intro hreq hnr
                    have hψ' : t ∈ (e' (k + 1)).pendA := by
                      rw [hpa']
                      exact hreq.1
                    simpa [psis] using hψ'
                  · intro hreq hnr
                    have hq : ∃ a, (a, t) ∈ (e' k).queue2 := by
                      simpa [psis] using hreq.1
                    rcases hq with ⟨a, hq⟩
                    refine ⟨a, ?_⟩
                    rw [hq2']
                    exact Finset.mem_insert.mpr (Or.inr hq)
          · -- poll₂
            rcases hp2 with ⟨p, hp, hmin, hq2', hr2', han', hpa', hla', hsa', hpb'⟩
            by_cases hq : t ∈ (e' (k + 1)).recv2
            · left
              have hqev : Tla.eventually (Tla.statePred (fun s => t ∈ s.recv2))
                  ((e'.drop k).drop 1) := by
                simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                  (Tla.eventually_imp (Tla.statePred (fun s => t ∈ s.recv2)) e' (k + 1)
                    (by simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_comm] using hq))
              rcases hqev with ⟨t0, ht0⟩
              refine ⟨1 + t0, ?_⟩
              simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using ht0
            · right
              constructor
              · change t ∈ (e' (k + 1)).sentA ∧ (t ∈ (e' (k + 1)).pendA ∨ ∃ a, (a, t) ∈ (e' (k + 1)).queue2)
                constructor
                · rw [hsa']
                  exact hφ.1
                · rcases hφ.2 with hpa | hq'
                  · left
                    rw [hpa']
                    exact hpa
                  · right
                    have htm : t ≠ p.2 := by
                      intro htm
                      have htR : t ∈ (e' (k + 1)).recv2 := by
                        rw [hr2', htm]
                        exact Finset.mem_insert_self p.2 (e' k).recv2
                      exact hq htR
                    rcases hq' with ⟨a, hq'⟩
                    refine ⟨a, ?_⟩
                    rw [hq2']
                    refine Finset.mem_erase.mpr ⟨?_, hq'⟩
                    intro heq
                    exact htm (congrArg Prod.snd heq)
              · constructor
                · intro i hnp
                  fin_cases i
                  · intro x hx
                    simp [deltas, Delta0] at hx ⊢
                    rw [hpa'] at hx
                    exact hx
                  · intro x hx
                    simp [deltas, Delta1] at hx ⊢
                    have htm' : p.2 ≠ t := by
                      intro htm'
                      apply hq
                      rw [hr2', ← htm']
                      exact Finset.mem_insert_self p.2 (e' k).recv2
                    have hArrE : ArrT (e' (k + 1)) t = ArrT (e' k) t := by
                      change minArrival (e' (k + 1)).queue2 t = minArrival (e' k).queue2 t
                      rw [hq2']
                      exact minArrival_erase_ne htm'
                    rw [hq2', hArrE] at hx
                    constructor
                    · rcases hx.1 with ⟨τ, hx1⟩
                      refine ⟨τ, ?_⟩
                      exact (Finset.erase_subset p (e' k).queue2) hx1
                    · exact hx.2
                · constructor
                  · intro i
                    fin_cases i
                    · intro hreq hR
                      rcases hR with ⟨h, hp⟩
                      rcases hp with ⟨hpa', _hla', _hsa', _hpb', _hq2', _han', _hr2'⟩
                      let m := Finset.min' (e' k).pendA h
                      have hmle : m ≤ t := (Finset.isLeast_min' (e' k).pendA h).2 hreq.1
                      refine ⟨m, ?_, ?_⟩
                      · simp [deltas, Delta0]
                        exact ⟨Finset.min'_mem (e' k).pendA h, hmle⟩
                      · intro hδ
                        simp [deltas, Delta0] at hδ
                        rw [hpa'] at hδ
                        exact (Finset.mem_erase.mp hδ.1).1 rfl
                    · intro hreq hR
                      rcases hR with ⟨p, hp, hmin, hq2', _hr2', _han', _hpa', _hla', _hsa', _hpb'⟩
                      have hp' : (ArrT (e' k) t, t) ∈ (e' k).queue2 := by
                        change (minArrival (e' k).queue2 t, t) ∈ (e' k).queue2
                        exact minArrival_mem (by simpa [psis] using hreq.1)
                      have hle1 : p.1 ≤ ArrT (e' k) t := hmin (ArrT (e' k) t, t) hp'
                      refine ⟨p.1, ?_, ?_⟩
                      · have hmem : p.1 ∈ Delta1 (e' k) t := by
                          change p.1 ∈ ((e' k).queue2.filter (fun q => q.1 ≤ ArrT (e' k) t)).image Prod.fst
                          exact Finset.mem_image.mpr ⟨p, ⟨Finset.mem_filter.mpr ⟨hp, hle1⟩, rfl⟩⟩
                        simpa [deltas] using hmem
                      · intro hδ
                        rw [deltas] at hδ
                        change p.1 ∈ ((e' (k + 1)).queue2.filter (fun q => q.1 ≤ ArrT (e' (k + 1)) t)).image Prod.fst at hδ
                        rcases Finset.mem_image.mp hδ with ⟨q, hqmem, hqf⟩
                        have hq1 : q.1 = p.1 := hqf
                        have hqmem' : q ∈ (e' k).queue2 := by
                          have hq' : q ∈ (e' (k + 1)).queue2 := (Finset.mem_filter.mp hqmem).1
                          rw [hq2'] at hq'
                          exact (Finset.mem_erase.mp hq').2
                        have hqne : q ≠ p := by
                          have hq' : q ∈ (e' (k + 1)).queue2 := (Finset.mem_filter.mp hqmem).1
                          rw [hq2'] at hq'
                          exact (Finset.mem_erase.mp hq').1
                        have hsame : q = p := h4 q hqmem' p hp hq1
                        exact hqne hsame
                  · intro i
                    fin_cases i
                    · intro hreq hnr
                      have hψ' : t ∈ (e' (k + 1)).pendA := by
                        rw [hpa']
                        exact hreq.1
                      simpa [psis] using hψ'
                    · intro hreq hnr
                      exact False.elim (hnr ⟨p, hp, hmin, hq2', hr2', han', hpa', hla', hsa', hpb'⟩)
  · -- S3: scheduled justice fires (from the two fairness assumptions)
    intro e' hH k _hφ i hψ
    rcases hH with ⟨_hInit', hNext'⟩
    rcases hNext' with ⟨_hNext'', hJ⟩
    rcases hJ with ⟨hJ1', hJ2'⟩
    fin_cases i
    · right
      exact hJ1' k
    · right
      exact hJ2' k
  · -- S4: at least one scheduler is on
    intro e' _hH k hφ
    rcases hφ.2 with hpa | hq
    · right
      exact ⟨(0 : Fin 2), by simpa [psis] using hpa⟩
    · right
      exact ⟨(1 : Fin 2), by simpa [psis] using hq⟩

end TlaDsl.Examples.LexReordering
