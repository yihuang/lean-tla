/-
Copyright (c) 2026 lean-tla contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# FIFO queue template (Rule-6 instance)

A generic liveness template for FIFO-style queues: any element `x` currently
in the queue is eventually removed, provided

* every step that keeps `x` queued does not increase its position (`hc2`), and
* every `serve` step that keeps `x` queued strictly decreases its position
  (`hc3`).

These are exactly the C2/C3 premises of a `RelRankCert` whose rank function is
the queue position `List.idxOf x`; the template packages them once so that
concrete systems only discharge two behavior-level hypotheses.

C1 and finiteness come for free: positions are natural numbers bounded by the
queue length, so `{i | i < (queue s).length}` is always finite.

Typical usage: define a structure projecting a queue and a serve action from
your state, prove `hc2`/`hc3` (usually from a `Nodup` invariant plus the
action definitions), then obtain `x ∈ queue ↝ x ∉ queue` under
`H ∧ □◇⟨serve⟩` via `FifoTemplate.liveness`.
-/
import Bft.RelRank

namespace Bft

/-- Data for the FIFO queue template: a queue projection, a serve action,
the watched element, and the two rank side conditions (C2/C3 shape). -/
structure FifoTemplate (σ : Type u) (α : Type v) [DecidableEq α] where
  /-- Queue projection from the state. -/
  queue : σ → List α
  /-- The action that serves (removes) the head element. -/
  serve : Action σ
  /-- The watched queue element. -/
  x : α
  /-- Ambient truth (e.g. `Init ∧ □[Next]_vars ∧ WF`). -/
  H : Pred σ
  /-- C2: any step that keeps `x` queued does not increase its position. -/
  hc2 : ∀ e : Behavior σ, H e → ∀ k : ℕ, x ∈ queue (e k) → x ∈ queue (e (k + 1)) →
    (queue (e (k + 1))).idxOf x ≤ (queue (e k)).idxOf x
  /-- C3: any `serve` step that keeps `x` queued strictly decreases its position. -/
  hc3 : ∀ e : Behavior σ, H e → ∀ k : ℕ, x ∈ queue (e k) →
    serve (e k) (e (k + 1)) → x ∈ queue (e (k + 1)) →
    (queue (e (k + 1))).idxOf x < (queue (e k)).idxOf x

namespace FifoTemplate

variable {σ : Type u} {α : Type v} [DecidableEq α] (t : FifoTemplate σ α)

/-- The certificate produced by the template: rank = queue position.
`noncomputable` because the case splits use classical logic. -/
noncomputable def toCert : RelRankCert σ {s | t.x ∈ t.queue s}
    {s | t.x ∉ t.queue s} where
  α := ℕ
  r := t.serve
  φ := {s | t.x ∈ t.queue s}
  δ := fun s i => t.x ∈ t.queue s ∧ i < (t.queue s).idxOf t.x
  R := fun s i => i < (t.queue s).length
  H := t.H
  finiteness := fun _e _n => Set.finite_lt_nat _
  c1 := fun e _hH k hp => by
    by_cases hq : t.x ∉ t.queue (e k)
    · exact Or.inl hq
    · exact Or.inr ⟨hp, fun _ hi => Nat.lt_of_lt_of_le hi.2 List.idxOf_le_length⟩
  c2 := fun e hH k hφ => by
    by_cases hq : t.x ∉ t.queue (e (k + 1))
    · exact Or.inl hq
    · push Not at hq
      refine Or.inr ⟨hq, fun i hi => ⟨hφ, ?_⟩⟩
      exact Nat.lt_of_lt_of_le hi.2 (t.hc2 e hH k hφ hq)
  c3 := fun e hH k hφ hr => by
    by_cases hq : t.x ∉ t.queue (e (k + 1))
    · exact Or.inl hq
    · push Not at hq
      have hlt := t.hc3 e hH k hφ hr hq
      have hpos : 1 ≤ (t.queue (e k)).idxOf t.x := by omega
      refine Or.inr ⟨(t.queue (e k)).idxOf t.x - 1, ⟨hφ, by omega⟩, ?_⟩
      simp only [not_and, not_lt]
      intro _; omega

/-- Liveness of the watched element: under `H ∧ □◇⟨serve⟩`,
`x ∈ queue ↝ x ∉ queue`. -/
theorem liveness :
    Entails (tlaAnd t.H (globalJustice t.serve))
      (leadsTo (statePred {s | t.x ∈ t.queue s})
               (statePred {s | t.x ∉ t.queue s})) :=
  t.toCert.toLeadsTo

end FifoTemplate

end Bft
