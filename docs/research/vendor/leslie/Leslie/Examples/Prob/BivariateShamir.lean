/-
M2 W4 — Bivariate Shamir secret sharing: secrecy proof.

Defines the bivariate Shamir spec as a `ProbActionSpec` and proves
secrecy at three levels of abstraction, mirroring `Examples/Prob/Shamir.lean`:

  * `bivariate_shamir_secrecy_pts` — algebraic core: for any
    `pts_x, pts_y ⊂ F` with `|pts_x| ≤ dx`, `|pts_y| ≤ dy`,
    `0 ∉ pts_x`, and `0 ∉ pts_y`, the distribution of bivariate
    polynomial evaluations at `pts_x × pts_y` is independent of the
    secret. Two applications of `Polynomial.bivariate_evals_uniform`.
  * `bivariate_shamir_secrecy` — coalition-level lift: for any
    coalition `C : Coalition n t` of "row parties" and `D : Coalition n t`
    of "column parties", the post-deal grid view (as a polynomial-eval
    pushforward) is independent of the secret.
  * `bivariate_shamir_secrecy_via_step` — operational/state-level:
    the `step`-of-`bivariateShamirShare` post-deal grid-view
    distribution is independent of the secret.

This is the algebraic core that M3's AVSS secrecy invokes. The
**full** AVSS secrecy (rows + columns view, not just grid) requires
additional work beyond the grid form; this file packages the grid
form, which is what `bivariate_evals_uniform` directly delivers.

## Model assumptions

  * **Synchronous bivariate broadcast deal.** The `.deal` action
    atomically writes grid shares to all party-pairs. Real AVSS
    distributes shares over a network with row/column structure;
    that lift is M3 work.
  * **Single-shot dealer.** Once the deal has occurred, `gate`
    becomes `False` and no further `.deal` actions fire.
  * **Scheduler-supplied secret.** `BivariateShamirAction := .deal (s : F)`.
  * **`partyPoint` is a parameter.** Same convention as univariate
    `Shamir.lean`.

## Per implementation plan v2.2 §M2 W4
-/

import Leslie.Prob.Action
import Leslie.Prob.PMF
import Leslie.Prob.Polynomial

namespace Leslie.Examples.Prob.BivariateShamir

open Leslie.Prob

/-! ## Algebraic core

The mathematical content of bivariate secrecy: the joint
distribution of bivariate evaluations at a coalition's grid points
is the *same uniform* regardless of the secret. -/

/-- Algebraic core of bivariate Shamir secrecy: for any
`pts_x, pts_y ⊂ F` with size bounds and 0-exclusion, the
distribution of bivariate evaluations at the grid `pts_x × pts_y`
is independent of the secret `s`.

Both sides reduce to `PMF.uniform (pts_x → pts_y → F)` via
`bivariate_evals_uniform`. -/
theorem bivariate_shamir_secrecy_pts {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (dx dy : ℕ) (s s' : F)
    (pts_x : Finset F) (pts_y : Finset F)
    (h_cx : pts_x.card ≤ dx) (h_cy : pts_y.card ≤ dy)
    (h_nx : (0 : F) ∉ pts_x) (h_ny : (0 : F) ∉ pts_y)
    (h_Fx : dx + 1 ≤ Fintype.card F) (h_Fy : dy + 1 ≤ Fintype.card F) :
    (Leslie.Prob.Polynomial.uniformBivariateWithFixedZero dx dy s).map
        (fun f => fun (p : pts_x) (q : pts_y) =>
          (f.eval (Polynomial.C p.val)).eval q.val)
      =
    (Leslie.Prob.Polynomial.uniformBivariateWithFixedZero dx dy s').map
        (fun f => fun (p : pts_x) (q : pts_y) =>
          (f.eval (Polynomial.C p.val)).eval q.val) := by
  rw [Leslie.Prob.Polynomial.bivariate_evals_uniform dx dy s
        pts_x pts_y h_cx h_cy h_nx h_ny h_Fx h_Fy,
      Leslie.Prob.Polynomial.bivariate_evals_uniform dx dy s'
        pts_x pts_y h_cx h_cy h_nx h_ny h_Fx h_Fy]

/-- **Full-distribution** analogue of `bivariate_shamir_secrecy_pts`.

For the literature-standard `uniformBivariateFullWithFixedZero` —
where only the `(0, 0)` coefficient is pinned to `s` and all
`(dx + 1) * (dy + 1) - 1` other coefficients are independently
uniform — the joint distribution of bivariate evaluations at the
off-axis grid `pts_x × pts_y` is independent of the secret.
Both sides equal `PMF.uniform (pts_x → pts_y → F)` by
`Leslie.Prob.Polynomial.bivariate_evals_uniform_full`.

This is the version intended for VSS/AVSS secrecy chains;
contrast `bivariate_shamir_secrecy_pts` which uses the
*degenerate* axis-zero distribution. -/
theorem bivariate_shamir_secrecy_pts_full
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (dx dy : ℕ) (s s' : F)
    (pts_x : Finset F) (pts_y : Finset F)
    (h_cx : pts_x.card ≤ dx) (h_cy : pts_y.card ≤ dy)
    (h_nx : (0 : F) ∉ pts_x) (h_ny : (0 : F) ∉ pts_y)
    (h_Fx : dx + 1 ≤ Fintype.card F) (h_Fy : dy + 1 ≤ Fintype.card F) :
    (Leslie.Prob.Polynomial.uniformBivariateFullWithFixedZero dx dy s).map
        (fun f => fun (p : pts_x) (q : pts_y) =>
          (f.eval (Polynomial.C p.val)).eval q.val)
      =
    (Leslie.Prob.Polynomial.uniformBivariateFullWithFixedZero dx dy s').map
        (fun f => fun (p : pts_x) (q : pts_y) =>
          (f.eval (Polynomial.C p.val)).eval q.val) := by
  rw [Leslie.Prob.Polynomial.bivariate_evals_uniform_full dx dy s
        pts_x pts_y h_cx h_cy h_nx h_ny h_Fx h_Fy,
      Leslie.Prob.Polynomial.bivariate_evals_uniform_full dx dy s'
        pts_x pts_y h_cx h_cy h_nx h_ny h_Fx h_Fy]

/-! ## Bivariate Shamir spec as a `ProbActionSpec`

State: per-party-pair grid shares.

Action: `deal s` — sample a uniform bivariate polynomial of
bidegree ≤ (dx, dy) with `f(0,0) = s`, set every party-pair's
share to `f(partyPoint i, partyPoint j)`. -/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ}

/-- Bivariate Shamir per-party-pair state: each of the `n × n`
party-pairs has either received its grid share (`some s_{i,j}`)
or not (`none`).

Real AVSS hands each party `i` a *row* polynomial `f(partyPoint i, ·)`
and *column* polynomial `f(·, partyPoint i)`. The grid-share view
captures the algebraic content (joint evaluation) without the
row/column structure; that structure is handled in M3 AVSS. -/
structure BivariateShamirState (F : Type*) (n : ℕ) where
  shares : Fin n → Fin n → Option F

/-- The dealer's only action: deal secret `s` using a bivariate
polynomial of bidegree ≤ (dx, dy) with `f(0,0) = s`. -/
inductive BivariateShamirAction (F : Type*) where
  | deal (s : F)

/-- The bivariate-Shamir spec (grid form).

  * Initial state: every party-pair's share is `none`.
  * Action `.deal s`: gate is "no share dealt yet"; effect samples
    a uniform bivariate polynomial with constant term `s` and
    writes `some (f(partyPoint i, partyPoint j))` to every
    party-pair `(i, j)`. -/
noncomputable def bivariateShamirShare (dx dy : ℕ) (partyPoint : Fin n → F) :
    ProbActionSpec (BivariateShamirState F n) (BivariateShamirAction F) where
  init    := fun st => ∀ i j, st.shares i j = none
  actions := fun
    | .deal s =>
      { gate   := fun st => ∀ i j, st.shares i j = none
        effect := fun _ _ =>
          (Leslie.Prob.Polynomial.uniformBivariateWithFixedZero dx dy s).map fun f =>
            { shares := fun i j =>
                some ((f.eval (Polynomial.C (partyPoint i))).eval (partyPoint j)) } }

/-! ## Grid coalition view -/

/-- A `t`-coalition: a subset of parties of size ≤ t. Reused from
the univariate setting via the same shape. -/
def Coalition (n t : ℕ) := { S : Finset (Fin n) // S.card ≤ t }

/-- The grid view of two coalitions `C` (row parties) and `D` (column
parties): the (`Option`-wrapped) shares at the grid `C × D`. -/
def gridView (C D : Coalition n t) (st : BivariateShamirState F n) :
    C.val → D.val → Option F :=
  fun i j => st.shares i.val j.val

/-! ## Secrecy theorem at the coalition level

The grid view's distribution after dealing is independent of the
secret. Reduces to `bivariate_shamir_secrecy_pts` after translating
coalition indices into field elements via `partyPoint`. -/

/-- Secrecy at the post-deal grid-share level.

Given two coalitions `C` and `D` of size ≤ t and a `partyPoint`
avoiding 0, the distribution of `(C × D)`'s shares after dealing
depends only on the coalitions, not on the secret. Reduces to
`bivariate_shamir_secrecy_pts` by transporting along `partyPoint`
and stripping the `Option.some` wrapper.

As with `shamir_secrecy`, injectivity of `partyPoint` is *not*
required. -/
theorem bivariate_shamir_secrecy {t : ℕ}
    (partyPoint : Fin n → F)
    (h_nz_pp : ∀ i, partyPoint i ≠ 0)
    (h_F : t + 1 ≤ Fintype.card F)
    (C D : Coalition n t) (s s' : F) :
    (Leslie.Prob.Polynomial.uniformBivariateWithFixedZero t t s).map
        (fun f => fun (i : C.val) (j : D.val) =>
          some ((f.eval (Polynomial.C (partyPoint i.val))).eval (partyPoint j.val)))
      =
    (Leslie.Prob.Polynomial.uniformBivariateWithFixedZero t t s').map
        (fun f => fun (i : C.val) (j : D.val) =>
          some ((f.eval (Polynomial.C (partyPoint i.val))).eval (partyPoint j.val))) := by
  -- Coalition's evaluation points, as Finsets in F.
  set pts_x : Finset F := C.val.image partyPoint with hpts_x
  set pts_y : Finset F := D.val.image partyPoint with hpts_y
  have h_card_x : pts_x.card ≤ t :=
    le_trans Finset.card_image_le C.property
  have h_card_y : pts_y.card ≤ t :=
    le_trans Finset.card_image_le D.property
  have h_nz_x : (0 : F) ∉ pts_x := by
    intro h_in
    rw [hpts_x, Finset.mem_image] at h_in
    obtain ⟨i, _, h_eq⟩ := h_in
    exact h_nz_pp i h_eq
  have h_nz_y : (0 : F) ∉ pts_y := by
    intro h_in
    rw [hpts_y, Finset.mem_image] at h_in
    obtain ⟨i, _, h_eq⟩ := h_in
    exact h_nz_pp i h_eq
  have h_mem_x : ∀ (i : C.val), partyPoint i.val ∈ pts_x := fun i => by
    simp only [pts_x, Finset.mem_image]
    exact ⟨i.val, i.property, rfl⟩
  have h_mem_y : ∀ (j : D.val), partyPoint j.val ∈ pts_y := fun j => by
    simp only [pts_y, Finset.mem_image]
    exact ⟨j.val, j.property, rfl⟩
  -- Both LHS and RHS factor as (... .map evals_at_grid).map view_translate.
  have h_factor : ∀ (s_sec : F),
      (Leslie.Prob.Polynomial.uniformBivariateWithFixedZero t t s_sec).map
          (fun f => fun (i : C.val) (j : D.val) =>
            some ((f.eval (Polynomial.C (partyPoint i.val))).eval (partyPoint j.val)))
        =
      ((Leslie.Prob.Polynomial.uniformBivariateWithFixedZero t t s_sec).map
          (fun f => fun (p : pts_x) (q : pts_y) =>
            (f.eval (Polynomial.C p.val)).eval q.val)).map
          (fun g i j =>
            some (g ⟨partyPoint i.val, h_mem_x i⟩ ⟨partyPoint j.val, h_mem_y j⟩)) := by
    intro s_sec
    rw [PMF.map_comp]
    rfl
  rw [h_factor s, h_factor s']
  rw [bivariate_shamir_secrecy_pts t t s s' pts_x pts_y
        h_card_x h_card_y h_nz_x h_nz_y h_F h_F]

/-- **Full-distribution** analogue of `bivariate_shamir_secrecy`:
post-deal grid-share secrecy under the literature-standard
non-degenerate distribution.  Reduces to
`bivariate_shamir_secrecy_pts_full` exactly as the axis-zero
variant reduces to `bivariate_shamir_secrecy_pts`. -/
theorem bivariate_shamir_secrecy_full {t : ℕ}
    (partyPoint : Fin n → F)
    (h_nz_pp : ∀ i, partyPoint i ≠ 0)
    (h_F : t + 1 ≤ Fintype.card F)
    (C D : Coalition n t) (s s' : F) :
    (Leslie.Prob.Polynomial.uniformBivariateFullWithFixedZero t t s).map
        (fun f => fun (i : C.val) (j : D.val) =>
          some ((f.eval (Polynomial.C (partyPoint i.val))).eval (partyPoint j.val)))
      =
    (Leslie.Prob.Polynomial.uniformBivariateFullWithFixedZero t t s').map
        (fun f => fun (i : C.val) (j : D.val) =>
          some ((f.eval (Polynomial.C (partyPoint i.val))).eval (partyPoint j.val))) := by
  set pts_x : Finset F := C.val.image partyPoint with hpts_x
  set pts_y : Finset F := D.val.image partyPoint with hpts_y
  have h_card_x : pts_x.card ≤ t :=
    le_trans Finset.card_image_le C.property
  have h_card_y : pts_y.card ≤ t :=
    le_trans Finset.card_image_le D.property
  have h_nz_x : (0 : F) ∉ pts_x := by
    intro h_in
    rw [hpts_x, Finset.mem_image] at h_in
    obtain ⟨i, _, h_eq⟩ := h_in
    exact h_nz_pp i h_eq
  have h_nz_y : (0 : F) ∉ pts_y := by
    intro h_in
    rw [hpts_y, Finset.mem_image] at h_in
    obtain ⟨i, _, h_eq⟩ := h_in
    exact h_nz_pp i h_eq
  have h_mem_x : ∀ (i : C.val), partyPoint i.val ∈ pts_x := fun i => by
    simp only [pts_x, Finset.mem_image]
    exact ⟨i.val, i.property, rfl⟩
  have h_mem_y : ∀ (j : D.val), partyPoint j.val ∈ pts_y := fun j => by
    simp only [pts_y, Finset.mem_image]
    exact ⟨j.val, j.property, rfl⟩
  have h_factor : ∀ (s_sec : F),
      (Leslie.Prob.Polynomial.uniformBivariateFullWithFixedZero t t s_sec).map
          (fun f => fun (i : C.val) (j : D.val) =>
            some ((f.eval (Polynomial.C (partyPoint i.val))).eval (partyPoint j.val)))
        =
      ((Leslie.Prob.Polynomial.uniformBivariateFullWithFixedZero t t s_sec).map
          (fun f => fun (p : pts_x) (q : pts_y) =>
            (f.eval (Polynomial.C p.val)).eval q.val)).map
          (fun g i j =>
            some (g ⟨partyPoint i.val, h_mem_x i⟩ ⟨partyPoint j.val, h_mem_y j⟩)) := by
    intro s_sec
    rw [PMF.map_comp]
    rfl
  rw [h_factor s, h_factor s']
  rw [bivariate_shamir_secrecy_pts_full t t s s' pts_x pts_y
        h_card_x h_card_y h_nz_x h_nz_y h_F h_F]

/-! ## State-level secrecy

Connecting `bivariate_shamir_secrecy` to the spec: the post-deal
grid view, computed via `step` ∘ `gridView`, is independent of
the secret. -/

/-- State-level secrecy: when the dealer's gate holds, the post-deal
grid-view distribution depends only on the coalitions, not on the
secret. -/
theorem bivariate_shamir_secrecy_via_step {t : ℕ}
    (partyPoint : Fin n → F)
    (h_nz_pp : ∀ i, partyPoint i ≠ 0)
    (h_F : t + 1 ≤ Fintype.card F)
    (C D : Coalition n t) (s s' : F)
    (initial : BivariateShamirState F n)
    (h_init : ∀ i j, initial.shares i j = none) :
    Option.map (PMF.map (gridView C D))
        ((bivariateShamirShare t t partyPoint).step (.deal s) initial)
      =
    Option.map (PMF.map (gridView C D))
        ((bivariateShamirShare t t partyPoint).step (.deal s') initial) := by
  have h_gate : ∀ (sec : F),
      ((bivariateShamirShare t t partyPoint).actions (.deal sec)).gate initial :=
    fun _ => h_init
  rw [ProbActionSpec.step_eq_some (h_gate s),
      ProbActionSpec.step_eq_some (h_gate s')]
  simp only [Option.map_some, Option.some_inj]
  -- The two `effect` calls reduce to bivariate-uniform-mapped-through-share;
  -- combine the maps via `PMF.map_comp` and reduce to `bivariate_shamir_secrecy`.
  rw [show ((bivariateShamirShare t t partyPoint).actions (.deal s)).effect
        initial (h_gate s)
      = (Leslie.Prob.Polynomial.uniformBivariateWithFixedZero t t s).map fun f =>
          ({ shares := fun i j =>
              some ((f.eval (Polynomial.C (partyPoint i))).eval (partyPoint j)) }
            : BivariateShamirState F n)
      from rfl,
      show ((bivariateShamirShare t t partyPoint).actions (.deal s')).effect
        initial (h_gate s')
      = (Leslie.Prob.Polynomial.uniformBivariateWithFixedZero t t s').map fun f =>
          ({ shares := fun i j =>
              some ((f.eval (Polynomial.C (partyPoint i))).eval (partyPoint j)) }
            : BivariateShamirState F n)
      from rfl,
      PMF.map_comp, PMF.map_comp]
  exact bivariate_shamir_secrecy partyPoint h_nz_pp h_F C D s s'

end Leslie.Examples.Prob.BivariateShamir
