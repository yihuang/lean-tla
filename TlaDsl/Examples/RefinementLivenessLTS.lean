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
  intro s μ
  cases μ
  -- the successor set of `s`: `{s' | Next s s' ∨ Vars s' = Vars s}`
  change Finite {s' : Conc.St | Tla.StutAction Conc.Next Conc.Vars s s'}
  -- the stutter-successors are exactly the singleton `{s}`
  have hstut : {s' : Conc.St | Conc.Vars s' = Conc.Vars s} = ({s} : Set Conc.St) := by
    ext s'
    constructor
    · intro h
      have hx : s'.x = s.x := by
        simpa [Conc.Vars] using congrArg (fun p : Nat × Nat => p.1) h
      have hf : s'.flag = s.flag := by
        simpa [Conc.Vars] using congrArg (fun p : Nat × Nat => p.2) h
      cases s' with
      | mk x' f' =>
          cases s with
          | mk x0 f0 =>
              have hx' : x' = x0 := by simpa using hx
              have hf' : f' = f0 := by simpa using hf
              simp [hx', hf']
    · intro h
      subst s'
      simp
  -- the action-successors are contained in a two-element set
  let t1 : Conc.St := { x := s.x, flag := 1 }
  let t2 : Conc.St := { x := s.x + 1, flag := 0 }
  have hact : {s' : Conc.St | Conc.Next s s'} ⊆ ({t1, t2} : Set Conc.St) := by
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
  -- the image is the union of the two finite pieces
  change Finite {s' : Conc.St | Conc.Next s s' ∨ Conc.Vars s' = Conc.Vars s}
  have hunion : {s' : Conc.St | Conc.Next s s' ∨ Conc.Vars s' = Conc.Vars s} =
      {s' : Conc.St | Conc.Next s s'} ∪ {s' : Conc.St | Conc.Vars s' = Conc.Vars s} := by
    ext s'
    simp [Set.mem_union]
  rw [hunion]
  exact Set.Finite.union
    (Set.Finite.subset (by
      have hfin2 : Set.Finite ({t1, t2} : Set Conc.St) := by
        exact (Set.finite_singleton t2).insert t1
      exact hfin2) hact)
    (by
      rw [hstut]
      exact Set.finite_singleton s)

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
