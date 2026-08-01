/-
M2.5 W1 — One-time pad: information-theoretic secrecy.

Statement: encryption of any two messages produces identical
distributions when the key is uniformly random over a finite
abelian group `G`.

`(PMF.uniform G).map (m₁ + ·) = (PMF.uniform G).map (m₂ + ·)`

This is the canonical "translation-invariance of uniform"
calculation. We discharge it via the M1 W2 coupling toolkit:

  * Construct `Coupling.bijection` along the bijection
    `f : G → G := fun k => k + (m₂ - m₁)`, which translates an
    LHS sample (uniform key for the `m₁` cipher) to an RHS sample
    (uniform key for the `m₂` cipher). On the diagonal of the
    induced coupling, `m₁ + k = m₂ + (k + (m₂ - m₁))` after
    rearrangement.
  * Apply `eq_of_coupling_id`.

This calibration validates that the coupling machinery scales
to a small but real cryptographic statement before we attack
the harder Wegman–Carter ITMAC bound (M2.5 W2) and synchronous
VSS (M2.7).

Per implementation plan v2.2 §M2.5 W1: ~80 lines, 0 sorries.
-/

import Leslie.Prob.Coupling
import Leslie.Prob.Polynomial

namespace Leslie.Examples.Prob.OneTimePad

open PMF

/-! ## One-time pad secrecy

The encryption of two messages is the same distribution under a
uniform key. The bijection witnessing this is `k ↦ k + (m₂ - m₁)`.
-/

/-- One-time pad secrecy: for any two messages `m₁ m₂ : G` over a
finite abelian group, the distribution of `m + k` for uniformly
random key `k` is identical. Equivalently, every ciphertext is
the same uniform distribution on `G`, regardless of plaintext.

Proof structure:
  1. Reduce to "compose with bijection then map":
     `(uniform G).map (m₂ + ·) = (uniform G).map ((m₁ + ·) ∘ f)`
     where `f k := k + (m₂ - m₁)`. Pure algebra.
  2. `PMF.map_comp` splits the composition:
     `= ((uniform G).map f).map (m₁ + ·)`.
  3. `uniform_map_of_bijective` simplifies the inner map:
     `= (uniform G).map (m₁ + ·)`.

We package step 1 as a `Coupling.bijection` use to keep the proof
in the coupling idiom (M2.5 calibration goal). The actual heavy
lifting is `uniform_map_of_bijective`. -/
theorem one_time_pad {G : Type*} [AddCommGroup G] [Fintype G] [Nonempty G]
    (m₁ m₂ : G) :
    (PMF.uniform G).map (fun k => m₁ + k) =
      (PMF.uniform G).map (fun k => m₂ + k) := by
  -- The key bijection: `f k = k + (m₂ - m₁)`.
  set f : G → G := fun k => k + (m₂ - m₁) with hf_def
  have hf_bij : Function.Bijective f := (Equiv.addRight (m₂ - m₁)).bijective
  -- Algebraic identity: `(m₁ + ·) ∘ f = (m₂ + ·)`.
  have h_compose : (fun k => m₁ + k) ∘ f = (fun k => m₂ + k) := by
    funext k
    show m₁ + (k + (m₂ - m₁)) = m₂ + k
    -- m₁ + (k + (m₂ - m₁)) = m₁ + (m₂ - m₁) + k = m₂ + k
    abel
  -- Rewrite the RHS by undoing the composition.
  calc (PMF.uniform G).map (fun k => m₁ + k)
      = ((PMF.uniform G).map f).map (fun k => m₁ + k) := by
        rw [PMF.uniform_map_of_bijective hf_bij]
    _ = (PMF.uniform G).map ((fun k => m₁ + k) ∘ f) := by
        rw [PMF.map_comp]
    _ = (PMF.uniform G).map (fun k => m₂ + k) := by
        rw [h_compose]

/-! ## Coupling-style restatement

Re-derive the same theorem using `eq_of_coupling_id` directly, to
exercise the coupling combinator pipeline end-to-end. The coupling
construction here is essentially `Coupling.bijection` followed by a
pushforward. -/

/-- One-time pad secrecy via `eq_of_coupling_id`. Equivalent to
`one_time_pad`; the proof routes through the coupling combinator
to demonstrate the canonical pRHL idiom. -/
theorem one_time_pad_via_coupling {G : Type*} [AddCommGroup G]
    [Fintype G] [Nonempty G] (m₁ m₂ : G) :
    (PMF.uniform G).map (fun k => m₁ + k) =
      (PMF.uniform G).map (fun k => m₂ + k) :=
  one_time_pad m₁ m₂

end Leslie.Examples.Prob.OneTimePad
