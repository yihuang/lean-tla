import TlaDsl.Basic
import TlaDsl.Notation
import TlaDsl.RelRank
import TlaDsl.Tactic

open scoped Tla

/-! # Timestamped queue: relational ranking liveness (McMillan, CAV 2024)

The paper's motivating example (Fig. 1) run through the relational-ranking
engine: a sender enters messages into a queue with strictly increasing
logical timestamps (gaps allowed); a receiver polls the queue and removes
the message with the *minimal* timestamp. The liveness property is

    (□◇ poll) ⊢ (sent t ↝ recv t)

for a fixed message timestamp `t`: if the queue is polled infinitely often,
every sent message is eventually received.

The relational ranking is the paper's `δ(τ) = pend(τ) ∧ τ ≤ t`, the
invariant is `φ = pend t`, and the finite envelope is `R = pend` (finite at
every time because each step adds at most one element — here `pend` is a
`Finset`, so finiteness is immediate). The step premises are discharged
from the model and its *safety* invariant (timestamps enter in increasing
order, so a send never adds a pending timestamp `≤ t` while `t` is
pending): the liveness proof itself is the relational-ranking finite
descent.
-/

namespace TlaDsl.Examples.TimestampedQueue

/-- The queue state: pending timestamps, the largest timestamp ever sent,
and history flags for sent/received timestamps (the paper's `send(t)` /
`recv(t)` events become persistent state predicates). -/
structure St where
  pend : Finset Nat
  last : Nat
  sent : Finset Nat
  recv : Finset Nat

/-- The sender enters a message with timestamp `u`, strictly after the
largest one so far (timestamps enter in increasing order — the safety
invariant). -/
def Send (u : Nat) : Tla.Action St :=
  fun s s' =>
    u > s.last ∧ s'.pend = insert u s.pend ∧ s'.last = u ∧
      s'.sent = insert u s.sent ∧ s'.recv = s.recv

/-- The receiver polls the queue: the minimal pending timestamp is removed
and recorded as received. -/
def Poll : Tla.Action St :=
  fun s s' =>
    ∃ h : s.pend.Nonempty,
      s'.pend = s.pend.erase (s.pend.min' h) ∧ s'.last = s.last ∧
        s'.sent = s.sent ∧ s'.recv = insert (s.pend.min' h) s.recv

/-- A step: a send or a poll. -/
def Next : Tla.Action St :=
  fun s s' => (∃ u : Nat, Send u s s') ∨ Poll s s'

/-- The queue starts empty. -/
def Init : Tla.StatePred St :=
  fun s => s.pend = ∅ ∧ s.last = 0 ∧ s.sent = ∅ ∧ s.recv = ∅

/-- The safety invariant needed for liveness, at a fixed message timestamp
`t`: sent-but-unreceived messages are pending, and pending timestamps never
exceed the largest one sent. -/
def Inv (t : Nat) (s : St) : Prop :=
  (t ∈ s.sent → t ∈ s.recv ∨ t ∈ s.pend) ∧
  (t ∈ s.pend → t ≤ s.last)

/-- `Inv t` is inductive for `Init ∧ □ Next`. -/
theorem inv_inductive (t : Nat) (e : Tla.Behavior St)
    (hInit : Init (e 0)) (hNext : ∀ m, Next (e m) (e (m + 1))) :
    ∀ k, Inv t (e k) := by
  intro k
  induction k with
  | zero =>
      -- the queue starts empty: both clauses are vacuous
      rcases hInit with ⟨hpend0, _hlast0, hsent0, _hrecv0⟩
      constructor
      · intro ht
        rw [hsent0] at ht
        exact False.elim ((Finset.notMem_empty t) ht)
      · intro ht
        rw [hpend0] at ht
        exact False.elim ((Finset.notMem_empty t) ht)
  | succ k ih =>
      rcases hNext k with hsend | hpoll
      · -- a send step with timestamp `u`: no pending timestamp `≤ t` is
        -- added, because `u > last ≥ t` whenever `t` is pending
        rcases hsend with ⟨u, hsend'⟩
        rcases hsend' with ⟨hu, hp', hl', hs', hr'⟩
        constructor
        · intro ht
          rw [hs'] at ht
          rcases Finset.mem_insert.mp ht with htu | hts
          · right
            rw [hp']
            exact Finset.mem_insert.mpr (Or.inl htu)
          · rcases ih.1 hts with hq | hpnd
            · left
              rw [hr']
              exact hq
            · right
              rw [hp']
              exact Finset.mem_insert.mpr (Or.inr hpnd)
        · intro ht
          rw [hp'] at ht
          rw [hl']
          rcases Finset.mem_insert.mp ht with htu | htp
          · exact le_of_eq htu
          · exact le_trans (ih.2 htp) (le_of_lt hu)
      · -- a poll step: the minimal pending timestamp is removed
        rcases hpoll with ⟨h, hp⟩
        rcases hp with ⟨hp', _hlast', hsent', hrecv'⟩
        constructor
        · intro ht
          rw [hsent'] at ht
          rcases ih.1 ht with hq | hpnd
          · left
            rw [hrecv']
            exact Finset.mem_insert.mpr (Or.inr hq)
          · by_cases htm : t = (e k).pend.min' h
            · left
              rw [hrecv', htm]
              exact Finset.mem_insert_self (Finset.min' (e k).pend h) (e k).recv
            · right
              rw [hp']
              exact Finset.mem_erase.mpr ⟨htm, hpnd⟩
        · intro ht
          rw [hp'] at ht
          have htp : t ∈ (e k).pend := (Finset.mem_erase.mp ht).2
          rw [_hlast']
          exact ih.2 htp

/-- Liveness of the queue (Rule 6 instance): with the safety invariant
supplying the step premises, `(□◇ poll) ⊢ sent t ↝ recv t` via the
relational ranking `δ(τ) = pend τ ∧ τ ≤ t`, invariant `φ = pend t` and
finite envelope `R = pend`. -/
theorem queue_liveness (t : Nat) :
    Tla.Entails
      (Tla.tlaAnd (Tla.statePred Init)
        (Tla.tlaAnd (Tla.always (Tla.actionPred Next))
          (Tla.always (Tla.eventually (Tla.actionPred Poll)))))
      (Tla.leadsTo (Tla.statePred (fun s => t ∈ s.sent))
        (Tla.statePred (fun s => t ∈ s.recv))) := by
  intro e h
  rcases h with ⟨hInit, hNextJ⟩
  rcases hNextJ with ⟨hNext, hJ⟩
  refine Tla.relational_ranking_rule
    (p := fun s => t ∈ s.sent) (q := fun s => t ∈ s.recv) (r := Poll)
    (φ := fun s => t ∈ s.pend)
    (δ := fun s τ => τ ∈ s.pend ∧ τ ≤ t)
    (R := fun s τ => τ ∈ s.pend)
    (H := Tla.tlaAnd (Tla.statePred Init) (Tla.always (Tla.actionPred Next)))
    ?_ ?_ ?_ ?_ e ⟨⟨hInit, hNext⟩, hJ⟩
  · -- `R = pend` is finite at every time (a `Finset`)
    intro e' n
    simp
  · -- C1: sent-but-unreceived messages are pending, and `δ ⊆ R`
    intro e' hH k hp
    rcases hH with ⟨hInit', hNext'⟩
    have hInit0 : Init (e' 0) := by
      simpa [Tla.statePred, Cslib.ωSequence.drop] using hInit'
    have hNextAll : ∀ m, Next (e' m) (e' (m + 1)) := by
      intro m
      have hm := hNext' m
      simpa [Tla.actionPred, Cslib.ωSequence.drop, Nat.add_comm] using hm
    have hIk : Inv t (e' k) := inv_inductive t e' hInit0 hNextAll k
    rcases hIk.1 hp with hq | hpnd
    · exact Or.inl hq
    · exact Or.inr ⟨hpnd, fun x hx => hx.1⟩
  · -- C2: `φ` persists and `δ` is conserved (sends add no element `≤ t`,
    -- polls only remove)
    intro e' hH k hφ
    rcases hH with ⟨hInit', hNext'⟩
    have hInit0 : Init (e' 0) := by
      simpa [Tla.statePred, Cslib.ωSequence.drop] using hInit'
    have hNextAll : ∀ m, Next (e' m) (e' (m + 1)) := by
      intro m
      have hm := hNext' m
      simpa [Tla.actionPred, Cslib.ωSequence.drop, Nat.add_comm] using hm
    have hIk : Inv t (e' k) := inv_inductive t e' hInit0 hNextAll k
    rcases hNextAll k with hsend | hpoll
    · rcases hsend with ⟨u, hsend'⟩
      rcases hsend' with ⟨hu, hp', _hl', _hs', hr'⟩
      by_cases hq : t ∈ (e' (k + 1)).recv
      · exact Or.inl hq
      · right
        constructor
        · -- `t` stays pending after a send
          rw [hp']
          exact Finset.mem_insert.mpr (Or.inr hφ)
        · -- conservation: a send adds no element `≤ t` (`u > last ≥ t`)
          have htl : t ≤ (e' k).last := hIk.2 hφ
          have hut : u > t := lt_of_le_of_lt htl hu
          intro x hx
          constructor
          · have hxne : x ≠ u := ne_of_lt (lt_of_le_of_lt hx.2 hut)
            rw [hp'] at hx
            exact (Finset.mem_insert.mp hx.1).resolve_left hxne
          · exact hx.2
    · rcases hpoll with ⟨h, hp⟩
      rcases hp with ⟨hp', _hlast', _hsent', hrecv'⟩
      by_cases hq : t ∈ (e' (k + 1)).recv
      · exact Or.inl hq
      · right
        constructor
        · -- `t` stays pending after a poll unless it was the removed one
          have htm : t ≠ (e' k).pend.min' h := by
            intro htm
            have htR : t ∈ (e' (k + 1)).recv := by
              rw [hrecv', htm]
              exact Finset.mem_insert_self (Finset.min' (e' k).pend h) (e' k).recv
            exact hq htR
          rw [hp']
          exact Finset.mem_erase.mpr ⟨htm, hφ⟩
        · -- conservation: a poll only removes the minimum
          intro x hx
          constructor
          · rw [hp'] at hx
            exact (Finset.erase_subset (Finset.min' (e' k).pend h) (e' k).pend) hx.1
          · exact hx.2
  · -- C3: a poll step reduces `δ`: the minimum pending timestamp
    -- `m ≤ t` is removed
    intro e' _hH k hφ hpoll
    rcases hpoll with ⟨h, hp⟩
    rcases hp with ⟨hp', _hlast', _hsent', _hrecv'⟩
    right
    let m := Finset.min' (e' k).pend h
    refine ⟨m, ?_, ?_⟩
    · -- `δ (e' k) m`: `m` is pending and `m ≤ t`
      constructor
      · simpa [m] using Finset.min'_mem (e' k).pend h
      · have hmin := (Finset.isLeast_min' (e' k).pend h).2 hφ
        simpa [m] using hmin
    · -- `m ∉ δ (e' (k + 1))`: `m` was removed
      intro hδ
      have hmnot : m ∉ (e' (k + 1)).pend := by
        rw [hp']
        simp [m]
      exact hmnot hδ.1

end TlaDsl.Examples.TimestampedQueue
