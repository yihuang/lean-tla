import TlaDsl.Basic
import TlaDsl.Meta
import Cslib.Foundations.Semantics.LTS.Relation
import Cslib.Foundations.Semantics.LTS.OmegaExecution
import Cslib.Foundations.Semantics.LTS.Simulation
import Cslib.Foundations.Semantics.LTS.HasTau

namespace Tla

/-! # LTS refinement layer

Connects the DSL's stuttering specs to CSLib's LTS machinery. A stuttering
spec `□⟨next⟩_v` is an LTS (`SpecLTS`) whose ω-executions are exactly its
behaviors; the Abadi–Lamport step condition is exactly a forward simulation
between the spec LTSs (and, τ-absorbing the stutter steps, between the
*saturated* LTSs); and safety refinement is trace inclusion of ω-executions.
The `ImageFinite`/`finiteState` classes are the structural finiteness
hypotheses of the deep A-L liveness theorem, and a finite state space makes
`SpecLTS` image-finite automatically.

Stutter steps play the role of CSLib's internal label `τ`: `SpecLTS` uses a
single label type with `HasTau.τ = ()`, so `StutAction next v` is both the
step relation and the τ-transition relation.
-/

/-- The LTS of a stuttering spec: transitions are `StutAction next v`, all
labeled with the single (internal) label `()`. -/
def SpecLTS {σ : Type u} {α : Type v} (next : Action σ) (v : σ → α) :
    Cslib.LTS σ Unit :=
  Cslib.LTS.Relation.toLTS (StutAction next v) ()

/-- The single label `()` is the internal (stutter) label `τ`. -/
instance : Cslib.HasTau Unit := ⟨()⟩

/-- A behavior satisfies `□⟨next⟩_v` iff it is an ω-execution of the spec
LTS with the constantly-`τ` label sequence. -/
theorem specLTS_omegaExec_iff_stutAlways {σ : Type u} {α : Type v}
    (next : Action σ) (v : σ → α) (e : Behavior σ) :
    (SpecLTS next v).OmegaExecution e (Cslib.ωSequence.const ()) ↔ stutAlways next v e := by
  constructor
  · intro h i
    have htr : (SpecLTS next v).Tr (e i) () (e (i + 1)) := h i
    simpa [stutAlways, always, actionPred, SpecLTS, Cslib.LTS.Relation.toLTS, StutAction,
      Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htr
  · intro h i
    have hstep : StutAction next v (e i) (e (i + 1)) := by
      simpa [stutAlways, always, actionPred, StutAction, Cslib.ωSequence.drop,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h i
    simpa [SpecLTS, Cslib.LTS.Relation.toLTS] using hstep

/-- The Abadi–Lamport step condition is exactly a forward simulation
between the spec LTSs (all transitions share the single label `τ`). -/
theorem sim_iff_step {σ τ : Type u} {α β : Type v}
    (nextA : Action σ) (u : σ → α) (nextC : Action τ) (v : τ → β)
    (f : τ → σ) :
    Cslib.LTS.IsSimulation (SpecLTS nextC v) (SpecLTS nextA u) (fun s t => f s = t) ↔
      ∀ s s', StutAction nextC v s s' → StutAction nextA u (f s) (f s') := by
  constructor
  · intro h s s' hs
    rcases h s (f s) rfl () s' (by
      simpa [SpecLTS, Cslib.LTS.Relation.toLTS] using hs) with ⟨t, htr, hrel⟩
    rw [← hrel] at htr
    simpa [SpecLTS, Cslib.LTS.Relation.toLTS] using htr
  · intro h s t hrel μ s' htr
    rcases hrel with rfl
    cases μ
    have hs' : StutAction nextC v s s' := by
      simpa [SpecLTS, Cslib.LTS.Relation.toLTS, StutAction] using htr
    refine ⟨f s', ?_, rfl⟩
    simpa [SpecLTS, Cslib.LTS.Relation.toLTS] using h s s' hs'

/-- A simulation preserves τ-runs: a τ-path from `s` to `s'` with `r s t`
yields a τ-path from `t` to some `t'` with `r s' t'`. -/
theorem tauSTr_map {σ τ : Type u} (lts₁ : Cslib.LTS σ Unit) (lts₂ : Cslib.LTS τ Unit)
    {r : σ → τ → Prop} (h : Cslib.LTS.IsSimulation lts₁ lts₂ r)
    {s s' : σ} {t : τ} (hrel : r s t) (htr : lts₁.τSTr s s') :
    ∃ t' : τ, lts₂.τSTr t t' ∧ r s' t' := by
  induction htr with
  | refl =>
      exact ⟨t, Cslib.LTS.τSTr.refl, hrel⟩
  | tail htr' hstep ih =>
      rcases ih with ⟨t₁, hτ₁, hrel₁⟩
      rcases h _ t₁ hrel₁ Cslib.HasTau.τ _ hstep with ⟨t₂, htr₂, hrel₂⟩
      exact ⟨t₂, Relation.ReflTransGen.tail hτ₁ htr₂, hrel₂⟩

/-- The Abadi–Lamport step condition is a forward simulation between the
*saturated* spec LTSs (τ-stutter runs are absorbed on both sides). -/
theorem sim_saturate_of_step {σ τ : Type u} {α β : Type v}
    (nextA : Action σ) (u : σ → α) (nextC : Action τ) (v : τ → β)
    (f : τ → σ)
    (hstep : ∀ s s', StutAction nextC v s s' → StutAction nextA u (f s) (f s')) :
    Cslib.LTS.IsSimulation (Cslib.LTS.saturate (SpecLTS nextC v))
      (Cslib.LTS.saturate (SpecLTS nextA u)) (fun s t => f s = t) := by
  have hsim : Cslib.LTS.IsSimulation (SpecLTS nextC v) (SpecLTS nextA u)
      (fun s t => f s = t) :=
    (sim_iff_step nextA u nextC v f).2 hstep
  intro s t hrel μ s' htr
  rcases hrel with rfl
  refine ⟨f s', ?_, rfl⟩
  cases htr with
  | refl =>
      exact Cslib.LTS.STr.refl
  | tr h1 htr2 h3 =>
      rcases tauSTr_map (SpecLTS nextC v) (SpecLTS nextA u) hsim rfl h1 with
        ⟨t₂, hτ₂, hrel₂⟩
      rcases hsim _ t₂ hrel₂ μ _ htr2 with
        ⟨t₃, htr₃, hrel₃⟩
      rcases tauSTr_map (SpecLTS nextC v) (SpecLTS nextA u) hsim hrel₃ h3 with
        ⟨t₄, hτ₄, hrel₄⟩
      have hτ₄' : (SpecLTS nextA u).τSTr t₃ (f s') := by
        rw [← hrel₄] at hτ₄
        exact hτ₄
      exact Cslib.LTS.STr.tr hτ₂ htr₃ hτ₄'

/-- Abadi–Lamport safety refinement, re-derived in LTS vocabulary: the step
condition is a forward simulation of the spec LTSs, so every concrete
ω-execution maps to an abstract one (trace inclusion). -/
theorem refinement_mapping_lts {σ τ : Type u} {α β : Type v}
    (initA : StatePred σ) (nextA : Action σ) (u : σ → α)
    (initC : StatePred τ) (nextC : Action τ) (v : τ → β)
    (f : τ → σ)
    (hinit : ∀ s, initC s → initA (f s))
    (hstep : ∀ s s', StutAction nextC v s s' → StutAction nextA u (f s) (f s')) :
    RefinesVia f (tlaAnd (statePred initC) (stutAlways nextC v))
      (tlaAnd (statePred initA) (stutAlways nextA u)) := by
  have hsim : Cslib.LTS.IsSimulation (SpecLTS nextC v) (SpecLTS nextA u)
      (fun s t => f s = t) :=
    (sim_iff_step nextA u nextC v f).2 hstep
  intro e he
  constructor
  · exact hinit (e 0) (by simpa [statePred] using he.1)
  · rw [← specLTS_omegaExec_iff_stutAlways]
    intro i
    have hω : (SpecLTS nextC v).OmegaExecution e (Cslib.ωSequence.const ()) :=
      (specLTS_omegaExec_iff_stutAlways nextC v e).2 he.2
    have htr' : (SpecLTS nextA u).Tr (f (e i)) () (f (e (i + 1))) := by
      rcases hsim (e i) (f (e i)) rfl () (e (i + 1)) (hω i) with ⟨t, htr, hrel⟩
      rw [← hrel] at htr
      exact htr
    simpa [Cslib.ωSequence.map] using htr'

/-- Abadi–Lamport refinement with liveness, in LTS vocabulary: the safety
mapping conditions plus liveness-conjunct preservation give the full
canonical-form refinement. -/
theorem refinement_mapping_liveness_lts {σ τ : Type u} {α β : Type v}
    (initA : StatePred σ) (nextA : Action σ) (u : σ → α)
    (initC : StatePred τ) (nextC : Action τ) (v : τ → β)
    (LC : Pred τ) (LA : Pred σ) (f : τ → σ)
    (hinit : ∀ s, initC s → initA (f s))
    (hstep : ∀ s s', StutAction nextC v s s' → StutAction nextA u (f s) (f s'))
    (hL : ∀ e : Behavior τ, LC e → LA (Cslib.ωSequence.map f e)) :
    RefinesVia f
      (tlaAnd (tlaAnd (statePred initC) (stutAlways nextC v)) LC)
      (tlaAnd (tlaAnd (statePred initA) (stutAlways nextA u)) LA) := by
  intro e he
  exact ⟨refinement_mapping_lts initA nextA u initC nextC v f hinit hstep e ⟨he.1.1, he.1.2⟩,
    hL e he.2⟩

/-- A spec LTS over a finite state space is image-finite — the structural
finiteness hypothesis of the deep A-L liveness theorem (CSLib
`finiteState_imageFinite`). -/
theorem specLTS_imageFinite {σ : Type u} {α : Type v} [Finite σ]
    (next : Action σ) (v : σ → α) : (SpecLTS next v).ImageFinite :=
  inferInstance

end Tla
