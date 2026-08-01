import Leslie.Action

/-! ## Two-Phase Commit as an ActionSpec

    A simplified two-phase commit protocol with 2 resource managers.
    Demonstrates using `GatedAction` and `ActionSpec` to structure
    a multi-action protocol, and proving refinement to an abstract
    transaction commit specification.

    Abstract spec (TCommit):
      State: each RM is in {working, committed, aborted}
      Init:  all RMs working
      Next:  an RM commits (if all prepared) or aborts

    Concrete spec (TwoPhaseCommit):
      State: RM states + TM state + messages
      Init:  all working, TM in init state
      Next:  various protocol actions (prepare, commit, abort, etc.)

    We prove: TwoPhaseCommit refines TCommit (the consistency invariant
    is preserved by refinement).
-/

open TLA

namespace TwoPhaseCommit

/-! ### Types -/

inductive RMState where | working | prepared | committed | aborted
  deriving DecidableEq, Repr

inductive TMState where | init | committed | aborted
  deriving DecidableEq, Repr

/-! ### Abstract Spec: Transaction Commit (2 RMs) -/

structure TCommitState where
  rm1 : RMState
  rm2 : RMState

inductive TCommitAction where
  | rm1_commit | rm2_commit | rm1_abort | rm2_abort

def tcommit : ActionSpec TCommitState TCommitAction where
  init := fun s => s.rm1 = .working ∧ s.rm2 = .working
  actions := fun
    | .rm1_commit => {
        gate := fun s => s.rm1 = .working ∧ s.rm2 = .working
        transition := fun s s' => s' = { s with rm1 := .committed, rm2 := .committed }
      }
    | .rm2_commit => {
        gate := fun s => s.rm1 = .working ∧ s.rm2 = .working
        transition := fun s s' => s' = { s with rm1 := .committed, rm2 := .committed }
      }
    | .rm1_abort => {
        gate := fun s => s.rm1 = .working
        transition := fun s s' => s' = { s with rm1 := .aborted }
      }
    | .rm2_abort => {
        gate := fun s => s.rm2 = .working
        transition := fun s s' => s' = { s with rm2 := .aborted }
      }

/-! ### Consistency invariant at the abstract level -/

def tc_consistent (s : TCommitState) : Prop :=
  ¬ (s.rm1 = .committed ∧ s.rm2 = .aborted) ∧
  ¬ (s.rm1 = .aborted ∧ s.rm2 = .committed)

def tc_inv (s : TCommitState) : Prop :=
  (s.rm1 = .committed → s.rm2 = .committed) ∧
  (s.rm2 = .committed → s.rm1 = .committed)

theorem tc_inv_implies_consistent (s : TCommitState) :
    tc_inv s → tc_consistent s := by
  intro ⟨h1, h2⟩
  constructor
  · rintro ⟨ha, hb⟩ ; exact absurd (h1 ha) (by rw [hb] ; exact RMState.noConfusion)
  · rintro ⟨ha, hb⟩ ; exact absurd (h2 hb) (by rw [ha] ; exact RMState.noConfusion)

theorem tcommit_preserves_inv :
    pred_implies tcommit.safety [tlafml| □ ⌜ tc_inv ⌝] := by
  apply init_invariant
  · intro s ⟨h1, h2⟩ ; simp [tc_inv] ; constructor <;> (intro h ; simp_all)
  · intro s s' ⟨i, hgate, htrans⟩ hinv
    simp [tcommit, tc_inv] at *
    cases i <;> simp at hgate htrans <;> subst htrans <;>
      simp_all

theorem tcommit_preserves_consistency :
    pred_implies tcommit.safety [tlafml| □ ⌜ tc_consistent ⌝] := by
  apply pred_implies_trans (q := [tlafml| □ ⌜ tc_inv ⌝])
  · exact tcommit_preserves_inv
  · apply always_monotone
    intro e h ; exact tc_inv_implies_consistent (e 0) h

/-! ### Concrete Spec: Two-Phase Commit Protocol -/

structure TPCState where
  rm1 : RMState
  rm2 : RMState
  tmState : TMState
  tm1Prepared : Bool
  tm2Prepared : Bool
  msgCommit : Bool
  msgAbort : Bool

inductive TPCAction where
  | rm1_prepare | rm2_prepare
  | tm_recv_prepared_1 | tm_recv_prepared_2
  | tm_commit | tm_abort
  | rm1_recv_commit | rm2_recv_commit
  | rm1_recv_abort | rm2_recv_abort

def tpc : ActionSpec TPCState TPCAction where
  init := fun s =>
    s.rm1 = .working ∧ s.rm2 = .working ∧
    s.tmState = .init ∧
    s.tm1Prepared = false ∧ s.tm2Prepared = false ∧
    s.msgCommit = false ∧ s.msgAbort = false
  actions := fun
    | .rm1_prepare => {
        gate := fun s => s.rm1 = .working
        transition := fun s s' => s' = { s with rm1 := .prepared }
      }
    | .rm2_prepare => {
        gate := fun s => s.rm2 = .working
        transition := fun s s' => s' = { s with rm2 := .prepared }
      }
    | .tm_recv_prepared_1 => {
        gate := fun s => s.tmState = .init ∧ s.rm1 = .prepared
        transition := fun s s' => s' = { s with tm1Prepared := true }
      }
    | .tm_recv_prepared_2 => {
        gate := fun s => s.tmState = .init ∧ s.rm2 = .prepared
        transition := fun s s' => s' = { s with tm2Prepared := true }
      }
    | .tm_commit => {
        gate := fun s => s.tmState = .init ∧ s.tm1Prepared = true ∧ s.tm2Prepared = true
        transition := fun s s' => s' = { s with tmState := .committed, msgCommit := true }
      }
    | .tm_abort => {
        gate := fun s => s.tmState = .init
        transition := fun s s' => s' = { s with tmState := .aborted, msgAbort := true }
      }
    | .rm1_recv_commit => {
        gate := fun s => s.msgCommit = true
        transition := fun s s' => s' = { s with rm1 := .committed }
      }
    | .rm2_recv_commit => {
        gate := fun s => s.msgCommit = true
        transition := fun s s' => s' = { s with rm2 := .committed }
      }
    | .rm1_recv_abort => {
        gate := fun s => s.msgAbort = true
        transition := fun s s' => s' = { s with rm1 := .aborted }
      }
    | .rm2_recv_abort => {
        gate := fun s => s.msgAbort = true
        transition := fun s s' => s' = { s with rm2 := .aborted }
      }

/-! ### Refinement mapping -/

def tpc_ref (s : TPCState) : TCommitState where
  rm1 := if s.rm1 = .committed ∧ s.rm2 = .committed then .committed
         else if s.rm1 = .aborted then .aborted
         else .working
  rm2 := if s.rm1 = .committed ∧ s.rm2 = .committed then .committed
         else if s.rm2 = .aborted then .aborted
         else .working

/-! ### Protocol invariant

    The invariant tracks the relationship between messages and TM state:
    - committed RMs imply commit message was sent
    - aborted RMs imply abort message was sent
    - commit message implies TM decided to commit
    - abort message implies TM decided to abort
    This ensures commit and abort messages are never both active. -/

def tpc_inv (s : TPCState) : Prop :=
  (s.rm1 = .committed → s.msgCommit = true) ∧
  (s.rm2 = .committed → s.msgCommit = true) ∧
  (s.rm1 = .aborted → s.msgAbort = true) ∧
  (s.rm2 = .aborted → s.msgAbort = true) ∧
  (s.msgCommit = true → s.tmState = .committed) ∧
  (s.msgAbort = true → s.tmState = .aborted)

set_option maxHeartbeats 1600000 in
theorem tpc_refines_tcommit :
    refines_via tpc_ref tpc.toSpec.safety tcommit.toSpec.safety_stutter := by
  apply refinement_mapping_stutter_with_invariant tpc.toSpec tcommit.toSpec tpc_ref tpc_inv
  · -- inv_init
    intro s ⟨h1, h2, _, _, _, h6, h7⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> simp_all
  · -- inv_next
    intro s s' ⟨hrc1, hrc2, hra1, hra2, hmc, hma⟩ ⟨i, hfire⟩
    cases i <;> simp [tpc, GatedAction.fires] at hfire <;>
      obtain ⟨hgate, htrans⟩ := hfire <;> subst htrans <;>
      (refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> simp_all)
  · -- init_preserved
    intro s ⟨h1, h2, _⟩
    constructor <;> (simp only [tpc_ref] ; rw [h1, h2] ; decide)
  · -- step_simulation
    intro s s' ⟨hrc1, hrc2, hra1, hra2, hmc, hma⟩ ⟨i, hfire⟩
    cases i <;> simp [tpc, GatedAction.fires] at hfire <;>
      obtain ⟨hgate, htrans⟩ := hfire <;> subst htrans
    -- rm1_prepare: stutter (working → prepared, both map to .working)
    · right
      have : s.rm1 ≠ .committed := by rw [hgate] ; exact nofun
      have : s.rm1 ≠ .aborted := by rw [hgate] ; exact nofun
      simp [tpc_ref, *]
    -- rm2_prepare: stutter
    · right
      have : s.rm2 ≠ .committed := by rw [hgate] ; exact nofun
      have : s.rm2 ≠ .aborted := by rw [hgate] ; exact nofun
      simp [tpc_ref, *]
    -- tm_recv_prepared_1: stutter (tpc_ref doesn't use tm1Prepared)
    · right ; rfl
    -- tm_recv_prepared_2: stutter
    · right ; rfl
    -- tm_commit: stutter (tpc_ref doesn't use tmState or msgCommit)
    · right ; rfl
    -- tm_abort: stutter
    · right ; rfl
    -- rm1_recv_commit
    · have htm : s.tmState = .committed := hmc hgate
      have hna1 : s.rm1 ≠ .aborted :=
        fun h => absurd (hma (hra1 h)) (by rw [htm] ; exact nofun)
      have hna2 : s.rm2 ≠ .aborted :=
        fun h => absurd (hma (hra2 h)) (by rw [htm] ; exact nofun)
      by_cases h2 : s.rm2 = .committed
      · by_cases h1 : s.rm1 = .committed
        · -- Both already committed: stutter
          right ; simp [tpc_ref, h1, h2]
        · -- rm2 committed, rm1 not: abstract commit
          left ; refine ⟨.rm1_commit, ⟨?_, ?_⟩, ?_⟩
          · simp [tpc_ref, h1, h2, hna1]
          · simp [tpc_ref, h1, h2]
          · simp [tpc_ref, tcommit, h2]
      · -- rm2 not committed: stutter
        right ; simp [tpc_ref, h2, hna1, hna2]
    -- rm2_recv_commit
    · have htm : s.tmState = .committed := hmc hgate
      have hna1 : s.rm1 ≠ .aborted :=
        fun h => absurd (hma (hra1 h)) (by rw [htm] ; exact nofun)
      have hna2 : s.rm2 ≠ .aborted :=
        fun h => absurd (hma (hra2 h)) (by rw [htm] ; exact nofun)
      by_cases h1 : s.rm1 = .committed
      · by_cases h2 : s.rm2 = .committed
        · right ; simp [tpc_ref, h1, h2]
        · left ; refine ⟨.rm2_commit, ⟨?_, ?_⟩, ?_⟩
          · simp [tpc_ref, h1, h2]
          · simp [tpc_ref, h1, h2, hna2]
          · simp [tpc_ref, tcommit, h1]
      · right ; simp [tpc_ref, h1, hna1, hna2]
    -- rm1_recv_abort
    · have htm : s.tmState = .aborted := hma hgate
      have hnc1 : s.rm1 ≠ .committed :=
        fun h => absurd (hmc (hrc1 h)) (by rw [htm] ; exact nofun)
      have hnc2 : s.rm2 ≠ .committed :=
        fun h => absurd (hmc (hrc2 h)) (by rw [htm] ; exact nofun)
      by_cases ha1 : s.rm1 = .aborted
      · right ; simp [tpc_ref, ha1, hnc2]
      · left ; refine ⟨.rm1_abort, ?_, ?_⟩
        · simp [tpc_ref, tcommit, hnc1, hnc2, ha1]
        · simp [tpc_ref, tcommit, hnc1, hnc2]
    -- rm2_recv_abort
    · have htm : s.tmState = .aborted := hma hgate
      have hnc1 : s.rm1 ≠ .committed :=
        fun h => absurd (hmc (hrc1 h)) (by rw [htm] ; exact nofun)
      have hnc2 : s.rm2 ≠ .committed :=
        fun h => absurd (hmc (hrc2 h)) (by rw [htm] ; exact nofun)
      by_cases ha2 : s.rm2 = .aborted
      · right ; simp [tpc_ref, ha2, hnc1]
      · left ; refine ⟨.rm2_abort, ?_, ?_⟩
        · simp [tpc_ref, tcommit, hnc1, hnc2, ha2]
        · simp [tpc_ref, tcommit, hnc1, hnc2]

end TwoPhaseCommit
