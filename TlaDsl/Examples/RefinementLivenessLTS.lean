import TlaDsl.Examples.RefinementLiveness
import TlaDsl.LTSRefine
import Cslib.Foundations.Semantics.FLTS.FLTSToLTS

open scoped Tla

/-! # Deep liveness refinement through the LTS layer

`RefinementLiveness.lean`'s two-phase counter, re-derived through CSLib's
LTS machinery. The DSL step correspondence is exactly a forward simulation
between the spec LTSs (`sim_iff_step`), the concrete LTS is image-finite
even though its state space is infinite (the structural finiteness
hypothesis of the deep A-L liveness theorem: finitely many successors per
state, not a finite state space), and the full canonical-form refinement
with liveness is re-proved via `refinement_mapping_liveness_lts`.

This is the "E3" executable-refinement layer: the stuttering spec `□[N]_v`
is the LTS whose ω-executions are the behaviors, stutter steps play the
role of the internal label `τ`, and the saturated simulation (`τ`-paths
absorbed) is the refinement of the τ-closed semantics.
-/

namespace TlaDsl.Examples.HandshakeRefinement

/-- The step correspondence is a forward simulation between the spec LTSs:
every concrete step (or stutter) maps to an abstract step (or stutter). -/
theorem conc_refines_abs_lts :
    Cslib.LTS.IsSimulation (Tla.SpecLTS Conc.Next Conc.Vars)
      (Tla.SpecLTS Abs.Next Abs.x) (fun s t => f s = t) := by
  exact (Tla.sim_iff_step Abs.Next Abs.x Conc.Next Conc.Vars f).2 step_refines

/-- The saturated simulation: the same correspondence with τ-stutter runs
absorbed on both sides. -/
theorem conc_refines_abs_sat_lts :
    Cslib.LTS.IsSimulation (Cslib.LTS.saturate (Tla.SpecLTS Conc.Next Conc.Vars))
      (Cslib.LTS.saturate (Tla.SpecLTS Abs.Next Abs.x)) (fun s t => f s = t) := by
  exact Tla.sim_saturate_of_step Abs.Next Abs.x Conc.Next Conc.Vars f
    (by
      intro s s' hs
      simpa [Tla.StutAction] using step_refines s s' (by simpa [Tla.StutAction] using hs))

/-- The frame is injective: `(x, flag)` determines the state. -/
lemma vars_injective : Function.Injective Conc.Vars := by
  intro s s' h
  cases s with
  | mk x f =>
      cases s' with
      | mk x' f' =>
          have hx : x = x' := by
            simpa [Conc.Vars] using congrArg Prod.fst h
          have hf : f = f' := by
            simpa [Conc.Vars] using congrArg Prod.snd h
          subst x'
          subst f'
          rfl

/-- The concrete LTS is image-finite: every state has finitely many
successors. The action contributes at most two successors (the prepare and
the increment targets) and the stutter disjunct contributes exactly one
(the state itself, since `Vars` is injective), so the successor set is
finite even though `Conc.St` is infinite. This is the structural
finiteness hypothesis the deep A-L liveness theorem needs. -/
lemma conc_imageFinite : (Tla.SpecLTS Conc.Next Conc.Vars).ImageFinite := by
  apply Tla.specLTS_imageFinite_of_step
  · -- the frame is injective: `(x, flag)` determines the state
    exact vars_injective
  · -- at most two action successors: the prepare and the increment targets
    intro s
    let t1 : Conc.St := { x := s.x, flag := 1 }
    let t2 : Conc.St := { x := s.x + 1, flag := 0 }
    have hsub : {s' : Conc.St | Conc.Next s s'} ⊆ ({t1, t2} : Set Conc.St) := by
      intro s' hs'
      tla_unfold
      rcases hs' with hR | hI
      · left
        cases s' with
        | mk x' f' =>
            cases s with
            | mk x0 f0 =>
                have hx' : x' = x0 := by simpa using hR.2.1
                have hf' : f' = 1 := by simpa using hR.2.2
                simp [t1, hx', hf']
      · right
        cases s' with
        | mk x' f' =>
            cases s with
            | mk x0 f0 =>
                have hx' : x' = x0 + 1 := by simpa using hI.2.1
                have hf' : f' = 0 := by simpa using hI.2.2
                simp [t2, hx', hf']
    exact Set.Finite.subset (by exact (Set.finite_singleton t2).insert t1) hsub

/-! ## The spec is runnable

The DSL action is not just a proof artifact: the counter's `Next` is a
deterministic step function, so the same spec is an executable FLTS
(CSLib's functional LTS). Each state has exactly one successor — the
prepare or the increment target — and the stuttering disjunct never fires
because `Vars` is injective and every action step changes the frame, so
the FLTS's LTS is exactly the spec LTS: every `foldl` run of `step` is a
behavior of `□[Next]_Vars`. This is the E1 "executable step function"
shape from the BFT design notes. -/

/-- The deterministic step function: from `flag = 0` prepare, otherwise
increment. -/
def step (s : Conc.St) : Conc.St :=
  if s.flag = 0 then { x := s.x, flag := 1 } else { x := s.x + 1, flag := 0 }

/-- The action is deterministic: it fires exactly to `step s`. -/
lemma next_iff_step (s s' : Conc.St) : Conc.Next s s' ↔ s' = step s := by
  constructor
  · intro hs'
    tla_unfold
    by_cases hf : s.flag = 0
    · rcases hs' with hR | hI
      · cases s with
        | mk x0 f0 =>
            cases s' with
            | mk x' f' =>
                have hf0 : f0 = 0 := by simpa using hf
                have hx' : x' = x0 := by simpa using hR.2.1
                have hf' : f' = 1 := by simpa using hR.2.2
                simp [step, hf0, hx', hf']
      · exfalso
        simp [hf] at hI
    · rcases hs' with hR | hI
      · exfalso
        simp [hf] at hR
      · cases s with
        | mk x0 f0 =>
            cases s' with
            | mk x' f' =>
                have hf0 : f0 ≠ 0 := by simpa using hf
                have hx' : x' = x0 + 1 := by simpa using hI.2.1
                have hf' : f' = 0 := by simpa using hI.2.2
                simp [step, hf0, hx', hf']
  · intro hs'
    rw [hs']
    by_cases hf : s.flag = 0
    · tla_unfold
      simp [step, hf]
    · tla_unfold
      simp [step, hf]

/-- `[Next]_Vars`-steps are either the deterministic action step or a
stutter — which, since `Vars` is injective, is the state itself. -/
lemma stutAction_iff_step_or_self (s s' : Conc.St) :
    Tla.StutAction Conc.Next Conc.Vars s s' ↔ s' = step s ∨ s' = s := by
  constructor
  · intro hs'
    rcases hs' with hNext | hstut
    · exact Or.inl ((next_iff_step s s').1 hNext)
    · exact Or.inr (vars_injective hstut)
  · intro hs'
    rcases hs' with hstep' | hself
    · left
      exact (next_iff_step s s').2 hstep'
    · right
      rw [hself]

/-- The executable FLTS of the counter: the transition function is
`step`, over the single internal label. -/
def flts : Cslib.FLTS Conc.St Unit where
  tr := fun s _ => step s

/-- The FLTS transitions are exactly the action steps. -/
lemma flts_tr_iff_next (s s' : Conc.St) :
    (Cslib.FLTS.toLTS flts).Tr s () s' ↔ Conc.Next s s' := by
  rw [Cslib.FLTS.toLTS_tr]
  rw [next_iff_step]
  exact eq_comm

/-- The spec LTS is the FLTS LTS plus the stutter self-loops: an
`[Next]_Vars`-step is either a `step` step or a stutter. -/
lemma spec_tr_iff_flts_or_stutter (s s' : Conc.St) :
    (Tla.SpecLTS Conc.Next Conc.Vars).Tr s () s' ↔
      (Cslib.FLTS.toLTS flts).Tr s () s' ∨ s' = s := by
  rw [Cslib.FLTS.toLTS_tr]
  change Tla.StutAction Conc.Next Conc.Vars s s' ↔ step s = s' ∨ s' = s
  rw [stutAction_iff_step_or_self]
  constructor
  · rintro (h1 | h2)
    · exact Or.inl h1.symm
    · exact Or.inr h2
  · rintro (h1 | h2)
    · exact Or.inl h1.symm
    · exact Or.inr h2

/-- Every FLTS run is a `[Next]_Vars` behavior: the FLTS's transitions are
a sub-relation of the spec LTS's. -/
lemma flts_tr_sub_spec (s s' : Conc.St) :
    (Cslib.FLTS.toLTS flts).Tr s () s' → (Tla.SpecLTS Conc.Next Conc.Vars).Tr s () s' := by
  intro h
  exact (spec_tr_iff_flts_or_stutter s s').2 (Or.inl h)

/-- The executable runs refine the abstract spec too: the FLTS's LTS
simulates the abstract spec LTS. -/
theorem flts_refines_abs_lts :
    Cslib.LTS.IsSimulation (Cslib.FLTS.toLTS flts)
      (Tla.SpecLTS Abs.Next Abs.x) (fun s t => f s = t) := by
  intro s t hrel μ s' htr
  rcases hrel with rfl
  have hspec : (Tla.SpecLTS Conc.Next Conc.Vars).Tr s μ s' := flts_tr_sub_spec s s' htr
  rcases conc_refines_abs_lts s (f s) rfl μ s' hspec with ⟨t', htr', hrel'⟩
  exact ⟨t', htr', hrel'⟩

/-- The full canonical-form refinement with liveness, re-proved through
the LTS layer: the safety simulation plus the fairness preservation give
the same `RefinesVia` as the DSL-level proof. -/
theorem conc_refines_abs_wf_lts : Tla.RefinesVia f Conc.SpecWF Abs.SpecWF := by
  intro e hSpec
  exact ⟨Tla.refinement_mapping_lts Abs.Init Abs.Next Abs.x Conc.Init Conc.Next Conc.Vars f
    init_refines
    (by
      intro s s' hs
      simpa [Tla.StutAction] using step_refines s s' (by simpa [Tla.StutAction] using hs))
    e ⟨hSpec.1.1, hSpec.1.2⟩, wf_conc_to_abs e hSpec⟩

end TlaDsl.Examples.HandshakeRefinement
