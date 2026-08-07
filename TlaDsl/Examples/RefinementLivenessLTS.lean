import TlaDsl.Examples.RefinementLiveness
import TlaDsl.LTSRefine

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

/-- The concrete LTS is image-finite: every state has finitely many
successors. The action contributes at most two successors (the prepare and
the increment targets) and the stutter disjunct contributes exactly one
(the state itself, since `Vars` is injective), so the successor set is
finite even though `Conc.St` is infinite. This is the structural
finiteness hypothesis the deep A-L liveness theorem needs. -/
lemma conc_imageFinite : (Tla.SpecLTS Conc.Next Conc.Vars).ImageFinite := by
  apply Tla.specLTS_imageFinite_of_step
  · -- the frame is injective: `(x, flag)` determines the state
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
