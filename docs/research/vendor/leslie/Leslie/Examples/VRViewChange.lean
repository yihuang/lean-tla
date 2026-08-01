import Leslie.Round

/-! ## Viewstamped Replication: View Change Safety

    A round-based model of VR's view change protocol, proving the key
    safety property: committed operations survive view changes.

    **Model (simplified to 3 replicas, 1 log slot, 2 views):**

    View 0 is the "normal" view with leader = replica 0.
    View 1 is the new view with leader = replica 1.

    **Phase 1 — Normal operation (view 0):**
    The leader proposes a command for the single log slot.
    Replicas accept (store in their log). When a majority (≥ 2) accept,
    the command is committed.

    **Phase 2 — View change (view 0 → view 1):**
    - DoViewChange: each replica sends its state to the new leader.
    - StartView: the new leader picks the log from a replica that accepted
      (if any are in the DVC quorum), and broadcasts it.

    **Safety:** If a command was committed in view 0 (majority accepted),
    then the new leader in view 1 selects a log containing that command.
    The argument is quorum intersection: the commit quorum and the view
    change quorum (both ≥ 2 of 3) must share at least one replica.
-/

open TLA

namespace VRViewChange

abbrev Replica := Fin 3
abbrev Cmd := Nat

/-! ### State -/

structure RState where
  log : Option Cmd
  accepted : Bool
  deriving DecidableEq, Repr

structure VCState where
  phase : Nat
  replicas : Replica → RState
  proposed : Option Cmd
  accepted_set : Replica → Bool
  newLeaderLog : Option Cmd

/-! ### Phase transitions -/

/-- Phase 0 → 1: Leader (replica 0) proposes a command, replicas in HO accept. -/
def stepNormalOp (s s' : VCState) (ho : HOCollection Replica)
    (cmd : Cmd) : Prop :=
  s.phase = 0 ∧ s'.phase = 1 ∧
  s'.proposed = some cmd ∧
  (∀ r : Replica, s'.replicas r =
    if ho (0 : Replica) r
    then { log := some cmd, accepted := true }
    else { log := none, accepted := false }) ∧
  (∀ r, s'.accepted_set r = ho (0 : Replica) r) ∧
  s'.newLeaderLog = none

/-- Phase 1 → 2: View change. New leader (replica 1) collects DVCs from a
    quorum and picks the log from an accepted replica if one exists. -/
def stepViewChange (s s' : VCState) (ho : HOCollection Replica) : Prop :=
  s.phase = 1 ∧ s'.phase = 2 ∧
  let dvc_quorum := (List.finRange 3).filter fun r => ho r (1 : Replica)
  dvc_quorum.length ≥ 2 ∧
  (let heard_accepted := dvc_quorum.filter fun r => (s.replicas r).accepted
   match heard_accepted.head? with
   | some r => s'.newLeaderLog = (s.replicas r).log
   | none   => s'.newLeaderLog = none) ∧
  s'.proposed = s.proposed ∧
  s'.replicas = s.replicas ∧
  s'.accepted_set = s.accepted_set

/-- Phase ≥ 2: Done (stutter). -/
def stepDone (s s' : VCState) : Prop :=
  s.phase ≥ 2 ∧ s' = s

def vrSpec : Spec VCState where
  init := fun s =>
    s.phase = 0 ∧ s.proposed = none ∧ s.newLeaderLog = none ∧
    (∀ r, s.replicas r = { log := none, accepted := false }) ∧
    (∀ r, s.accepted_set r = false)
  next := fun s s' =>
    (∃ ho cmd, stepNormalOp s s' ho cmd) ∨
    (∃ ho, stepViewChange s s' ho) ∨
    stepDone s s'

/-! ### Safety property -/

def vc_safety (s : VCState) : Prop :=
  ∀ cmd,
    s.proposed = some cmd →
    ((List.finRange 3).filter fun r => s.accepted_set r).length ≥ 2 →
    s.newLeaderLog ≠ none →
    s.newLeaderLog = some cmd

/-- Auxiliary invariant: accepted_set and the accepted flag agree, and any
    accepted replica's log matches the proposed command. -/
def replica_inv (s : VCState) : Prop :=
  ∀ r, s.accepted_set r = (s.replicas r).accepted ∧
       ((s.replicas r).accepted = true → (s.replicas r).log = s.proposed)

/-! ### Quorum intersection for 3 replicas -/

theorem majority3_intersect (p₁ p₂ : Replica → Bool)
    (h₁ : ((List.finRange 3).filter fun r => p₁ r).length ≥ 2)
    (h₂ : ((List.finRange 3).filter fun r => p₂ r).length ≥ 2) :
    ∃ r : Replica, p₁ r = true ∧ p₂ r = true := by
  by_contra h
  have h' : ∀ r, ¬(p₁ r = true ∧ p₂ r = true) := by
    intro r hr ; exact h ⟨r, hr⟩
  have h_sum := filter_disjoint_length_le
    (fun r => p₁ r) (fun r => p₂ r) (List.finRange 3) h'
  have h_len : (List.finRange 3).length = 3 := List.length_finRange
  omega

/-! ### Safety proof -/

theorem vc_safety_invariant :
    pred_implies vrSpec.safety [tlafml| □ ⌜vc_safety⌝] := by
  -- We prove the stronger combined invariant vc_safety ∧ replica_inv
  suffices h : pred_implies vrSpec.safety [tlafml| □ ⌜fun s => vc_safety s ∧ replica_inv s⌝] by
    intro e he n
    exact (h e he n).1
  apply init_invariant
  · -- Init
    intro s ⟨_, _, hnl, hrep, hacc⟩
    exact ⟨fun _ _ _ hne => absurd hnl hne,
           fun r => by simp [hrep r, hacc r]⟩
  · -- Inductive step
    intro s s' hnext ⟨hinv_safety, hinv_rep⟩
    rcases hnext with ⟨ho, c, hstep⟩ | ⟨ho, hstep⟩ | hstep
    · -- Normal operation: newLeaderLog stays none
      obtain ⟨_, _, hprop', hrep, hacc, hnl⟩ := hstep
      refine ⟨fun _ _ _ hne => absurd hnl hne, fun r => ?_⟩
      constructor
      · rw [hacc, hrep] ; by_cases hho : ho 0 r = true <;> simp [hho]
      · intro hr ; rw [hrep] at hr ⊢
        by_cases hho : ho 0 r = true <;> simp [hho] at hr ⊢; exact hprop'.symm
    · -- View change: apply quorum intersection
      obtain ⟨_, _, hquorum, hpick, hprop', hreplicas, haccepted'⟩ := hstep
      constructor
      · -- vc_safety for s'
        intro cmd hprop haccepted hnewleader
        rw [hprop'] at hprop
        rw [haccepted'] at haccepted
        -- Rewrite accepted quorum using replica_inv
        have haccepted_rep : ((List.finRange 3).filter
            fun r => (s.replicas r).accepted).length ≥ 2 := by
          rw [show (fun r => (s.replicas r).accepted) = s.accepted_set from
            funext (fun r => ((hinv_rep r).1).symm)]
          exact haccepted
        -- Quorum intersection
        obtain ⟨r, hr_acc, hr_dvc⟩ := majority3_intersect
          (fun r => (s.replicas r).accepted)
          (fun r => ho r (1 : Replica))
          haccepted_rep hquorum
        -- r is in dvc_quorum and heard_accepted
        have hr_in_dvc : r ∈ (List.finRange 3).filter (fun r => ho r (1 : Replica)) :=
          List.mem_filter.mpr ⟨List.mem_finRange r, hr_dvc⟩
        have hr_in_heard : r ∈ ((List.finRange 3).filter (fun r => ho r (1 : Replica))).filter
            (fun r => (s.replicas r).accepted) :=
          List.mem_filter.mpr ⟨hr_in_dvc, hr_acc⟩
        -- heard_accepted is nonempty
        have hne : ((List.finRange 3).filter (fun r => ho r (1 : Replica))).filter
            (fun r => (s.replicas r).accepted) ≠ [] :=
          fun h => absurd (h ▸ hr_in_heard) (List.not_mem_nil)
        -- Case-split on the list to determine head?
        -- The hpick hypothesis has a let/match; we need to work with it
        -- Let's rewrite hpick by examining what heard_accepted.head? equals
        have : ∃ y ys, ((List.finRange 3).filter (fun r => ho r (1 : Replica))).filter
            (fun r => (s.replicas r).accepted) = y :: ys := by
          cases hlist : ((List.finRange 3).filter (fun r => ho r (1 : Replica))).filter
              (fun r => (s.replicas r).accepted)
          · exact absurd hlist hne
          · exact ⟨_, _, rfl⟩
        obtain ⟨y, ys, hlist⟩ := this
        -- y is in heard_accepted, so y.accepted = true
        have hy_mem : y ∈ ((List.finRange 3).filter (fun r => ho r (1 : Replica))).filter
            (fun r => (s.replicas r).accepted) := hlist ▸ List.Mem.head ys
        have hy_acc : (s.replicas y).accepted = true := (List.mem_filter.mp hy_mem).2
        -- y.log = s.proposed = some cmd
        have hy_log : (s.replicas y).log = some cmd := by
          rw [(hinv_rep y).2 hy_acc, hprop]
        -- Now we need to show s'.newLeaderLog = some cmd
        -- hpick says: match heard_accepted.head? with some r => ... | none => ...
        -- with hlist, head? = some y, so hpick gives s'.newLeaderLog = (s.replicas y).log
        -- The tricky part is connecting hpick (which has `let` bindings) to our hlist
        -- Let's try to simplify hpick using hlist
        simp only [hlist, List.head?] at hpick
        rw [hpick, hy_log]
      · -- replica_inv preserved
        intro r
        have ⟨h1, h2⟩ := hinv_rep r
        exact ⟨by rw [haccepted', hreplicas]; exact h1,
               fun hr => by rw [hreplicas] at hr ⊢; rw [hprop']; exact h2 hr⟩
    · -- Done: state unchanged, use IH
      obtain ⟨_, heq⟩ := hstep
      subst heq
      exact ⟨hinv_safety, hinv_rep⟩

end VRViewChange
