import Bft.Core

/-!
# Bft.Rules — rules proved from the semantics

Everything is proved from the semantic definitions in `Core`; no axioms are
introduced. Reduction at the temporal/position boundary relies on the
pointwise simp lemmas registered in `Core` (`statePred_drop`,
`actionPred_drop`, etc., ultimately CSLib's `@[simp] get_drop`) — no
addition-rewrite chains appear in the proofs.
-/

namespace Bft

/-- Inductive invariance (non-stuttering version). -/
theorem init_invariant {σ : Type u} (init : StatePred σ) (next : Action σ)
    (inv : StatePred σ)
    (hinit : ∀ s, s ∈ init → s ∈ inv)
    (hstep : ∀ s s', next s s' → s ∈ inv → s' ∈ inv) :
    Entails (tlaAnd (statePred init) (always (actionPred next)))
      (always (statePred inv)) := by
  intro e he n
  induction n with
  | zero => exact hinit (e 0) he.1
  | succ n ih =>
      have hstepn : next (e n) (e (n + 1)) := by
        have := he.2 n
        simpa [always] using this
      simpa [statePred] using
        hstep (e n) (e (n + 1)) hstepn (by simpa [statePred] using ih)

/-- One-step extraction: a stuttering machine performs a stuttering step at
every position. Absorbs the recurring
`have h := hE.2 k; simpa [stutAlways, always] using h` prologue. -/
theorem stutAlways_step {σ : Type u} {α : Type v} {a : Action σ} {v : σ → α}
    {e : Behavior σ} {k : ℕ} (h : stutAlways a v e) :
    StutAction a v (e k) (e (k + 1)) := by
  have hk := h k
  rwa [actionPred_drop] at hk

/-- Invariant extraction in membership normal form. -/
theorem always_statePred_at {σ : Type u} {inv : StatePred σ} {e : Behavior σ}
    {k : ℕ} (h : always (statePred inv) e) : e k ∈ inv := by
  have hk := h k
  rwa [statePred_drop] at hk

/-- Inductive invariance, stuttering version. -/
theorem init_invariant_stut {σ : Type u} {α : Type v} (init : StatePred σ)
    (next : Action σ) (v : σ → α) (inv : StatePred σ)
    (hinit : ∀ s, s ∈ init → s ∈ inv)
    (hstep : ∀ s s', StutAction next v s s' → s ∈ inv → s' ∈ inv) :
    Entails (tlaAnd (statePred init) (stutAlways next v))
      (always (statePred inv)) := by
  intro e he n
  induction n with
  | zero => exact hinit (e 0) he.1
  | succ n ih =>
      have hstepn : StutAction next v (e n) (e (n + 1)) :=
        stutAlways_step he.2
      simpa [statePred] using
        hstep (e n) (e (n + 1)) hstepn (by simpa [statePred] using ih)

/-- Inductive invariance for a bundled `Spec`. -/
theorem Spec.init_invariant {σ : Type u} (S : Spec σ)
    (inv : StatePred σ)
    (hinit : ∀ s, s ∈ S.Init → s ∈ inv)
    (hstep : ∀ s s', StutAction S.Next id s s' → s ∈ inv → s' ∈ inv) :
    Entails S.pred (always (statePred inv)) :=
  init_invariant_stut S.Init S.Next id inv hinit hstep

/-- Transitivity of leads-to. -/
theorem leadsTo_trans {σ : Type u} (P Q R : Pred σ) :
    Entails (tlaAnd (leadsTo P Q) (leadsTo Q R)) (leadsTo P R) := by
  intro e h n hP
  rcases h.1 n hP with ⟨k, hQ⟩
  rw [Cslib.ωSequence.drop_drop] at hQ
  rcases h.2 (n + k) hQ with ⟨m, hR⟩
  rw [Cslib.ωSequence.drop_drop] at hR
  exact ⟨k + m, by
    simpa [Cslib.ωSequence.drop_drop, Nat.add_assoc] using hR⟩

/-- Left-or distribution of leads-to. -/
theorem leadsTo_or {σ : Type u} (p1 p2 q : Pred σ) :
    Entails (tlaAnd (leadsTo p1 q) (leadsTo p2 q)) (leadsTo (tlaOr p1 p2) q) := by
  intro e h n hpq
  rcases hpq with hp1 | hp2
  · exact h.1 n hp1
  · exact h.2 n hp2

/-- WF1 (Lamport): `p ↝ q` under `□[N]_v ∧ WF_v(A)`. Proved from the semantics. -/
theorem wf1 {σ : Type u} {α : Type v} (p q : StatePred σ) (N A : Action σ)
    (v : σ → α)
    (hstep : ∀ s s', s ∈ p → StutAction N v s s' → s' ∈ p ∨ s' ∈ q)
    (haq : ∀ s s', s ∈ p → AngleAction A v s s' → s' ∈ q)
    (henable : ∀ s, s ∈ p → s ∈ Enabled (AngleAction A v) ∨ s ∈ q) :
    Entails (tlaAnd (stutAlways N v) (WF_v A v))
      (leadsTo (statePred p) (statePred q)) := by
  intro e h k hpk
  apply Classical.byContradiction
  intro hq
  have hqall : ∀ m, e (k + m) ∉ q := by
    intro m hm
    exact hq ⟨m, by simpa using hm⟩
  have hp : ∀ j, e (k + j) ∈ p := by
    intro j
    induction j with
    | zero => simpa [statePred] using hpk
    | succ j ih =>
        have hN : StutAction N v (e (k + j)) (e (k + j + 1)) :=
          stutAlways_step h.1
        rcases hstep _ _ ih hN with hp' | hq'
        · exact hp'
        · exact absurd hq' (hqall (j + 1))
  have hen : ∀ j, e (k + j) ∈ Enabled (AngleAction A v) := by
    intro j
    rcases henable _ (hp j) with hEn | hqj
    · exact hEn
    · exact absurd hqj (hqall j)
  have hWF : eventually (actionPred (AngleAction A v)) (e.drop k) := by
    have h2 := h.2 k
    apply h2
    intro j
    -- goal: statePred (Enabled …) ((e.drop k).drop j), reduced to e (k+j)
    simpa using hen j
  rcases hWF with ⟨j, hA⟩
  have hA' : AngleAction A v (e (k + j)) (e (k + j + 1)) := by
    simpa using hA
  exact hqall (j + 1) (haq _ _ (hp j) hA')

/-- SF1: the SF version (permanently enabled under the contradiction assumption
implies infinitely-often enabled, and SF guarantees firing). -/
theorem sf1 {σ : Type u} {α : Type v} (p q : StatePred σ) (N A : Action σ)
    (v : σ → α)
    (hstep : ∀ s s', s ∈ p → StutAction N v s s' → s' ∈ p ∨ s' ∈ q)
    (haq : ∀ s s', s ∈ p → AngleAction A v s s' → s' ∈ q)
    (henable : ∀ s, s ∈ p → s ∈ Enabled (AngleAction A v) ∨ s ∈ q) :
    Entails (tlaAnd (stutAlways N v) (SF_v A v))
      (leadsTo (statePred p) (statePred q)) := by
  intro e h k hpk
  apply Classical.byContradiction
  intro hq
  have hqall : ∀ m, e (k + m) ∉ q := by
    intro m hm
    exact hq ⟨m, by simpa using hm⟩
  have hp : ∀ j, e (k + j) ∈ p := by
    intro j
    induction j with
    | zero => simpa [statePred] using hpk
    | succ j ih =>
        have hN : StutAction N v (e (k + j)) (e (k + j + 1)) :=
          stutAlways_step h.1
        rcases hstep _ _ ih hN with hp' | hq'
        · exact hp'
        · exact absurd hq' (hqall (j + 1))
  have hen : ∀ j, e (k + j) ∈ Enabled (AngleAction A v) := by
    intro j
    rcases henable _ (hp j) with hEn | hqj
    · exact hEn
    · exact absurd hqj (hqall j)
  have hInfEn :
      always (eventually (statePred (Enabled (AngleAction A v)))) (e.drop k) := by
    intro j
    exact ⟨0, by simpa using hen j⟩
  have hSF : eventually (actionPred (AngleAction A v)) (e.drop k) :=
    h.2 k hInfEn
  rcases hSF with ⟨j, hA⟩
  have hA' : AngleAction A v (e (k + j)) (e (k + j + 1)) := by
    simpa using hA
  exact hqall (j + 1) (haq _ _ (hp j) hA')

end Bft
