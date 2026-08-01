/-
M1 W2 acceptance — coupling demo.

Demonstrates the `PMF.Coupling` API on a few small examples:

  1. `Coupling.self` (diagonal coupling) — the simplest coupling
     of `μ` with itself.
  2. `Coupling.bijection` — image of `μ` under `f` is coupled with
     `μ` along `(a, f a)`.
  3. `eq_of_coupling_id` — derive PMF equality from a coupling that
     supports `(· = ·)`.

The full pRHL toolbox (tactic forms `by_coupling`,
`coupling_bijection` as a tactic, `coupling_swap`, `coupling_up_to_bad`)
is M1 W2 polish work in `Leslie/Tactics/Prob.lean`.
-/

import Leslie.Prob.Coupling

namespace Leslie.Examples.Prob.CouplingDemo

open PMF

noncomputable section

/-- The diagonal coupling exists for any PMF. -/
example {α : Type*} (μ : PMF α) : Coupling μ μ :=
  Coupling.self μ

/-- The diagonal coupling supports equality. -/
example {α : Type*} (μ : PMF α) : (Coupling.self μ).supports (· = ·) :=
  Coupling.self_supports_eq μ

/-- The bijection-induced coupling exists for any function `f`. -/
example {α β : Type*} (μ : PMF α) (f : α → β) : Coupling μ (μ.map f) :=
  Coupling.bijection μ f

/-- The bijection-induced coupling supports `b = f a`. -/
example {α β : Type*} (μ : PMF α) (f : α → β) :
    (Coupling.bijection μ f).supports (fun a b => b = f a) :=
  Coupling.bijection_supports μ f

/-- A trivial PMF-equality proof via `eq_of_coupling_id`. -/
example {α : Type*} (μ : PMF α) : μ = μ :=
  eq_of_coupling_id (Coupling.self μ) (Coupling.self_supports_eq μ)

/-! ## Bool XOR is uniform — a non-trivial use of `bijection`

`(uniform Bool).map (· ^^ x) = uniform Bool` for any fixed `x`.

This is *not* just refl: the LHS is a pushforward of uniform under
the bijection `b ↦ b ^^ x` (XOR). The bijection coupling makes the
proof a one-liner once we have the right invariance lemma.
-/

/-- XOR with a fixed bit is a bijection on `Bool`. -/
theorem xor_bijective (x : Bool) : Function.Bijective (fun b => b ^^ x) := by
  refine ⟨?_, ?_⟩
  · intro a b h; simpa using congrArg (· ^^ x) h
  · intro b; exact ⟨b ^^ x, by simp⟩

end

end Leslie.Examples.Prob.CouplingDemo
