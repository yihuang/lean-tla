import Leslie.Action

/-! ## Peterson's Algorithm: 2-Process Mutual Exclusion

    Peterson's algorithm achieves mutual exclusion for two processes
    using two boolean flags and a shared turn variable.

    Each process i:
    1. Sets flag[i] = true  (intent to enter)
    2. Sets turn = 1-i      (yield priority to the other)
    3. Waits until flag[1-i] = false ∨ turn = i
    4. Enters critical section
    5. Sets flag[i] = false  (release)

    We model this as an `ActionSpec` with 8 actions (4 per process),
    prove mutual exclusion via an inductive invariant, and establish
    a refinement to an abstract lock specification.
-/

open TLA

namespace Peterson

/-! ### Program counter -/

inductive PC where
  | idle      -- not trying; flag[i] = false
  | flagged   -- flag[i] = true, about to set turn
  | waiting   -- flag[i] = true, turn set, spinning for entry
  | cs        -- in critical section
  deriving DecidableEq, Repr

/-! ### State -/

structure PState where
  flag0 : Bool
  flag1 : Bool
  turn : Bool       -- false = process 0's priority, true = process 1's priority
  pc0 : PC
  pc1 : PC
  deriving DecidableEq

/-! ### Actions -/

inductive PAction where
  | setFlag0 | setFlag1
  | setTurn0 | setTurn1
  | enter0 | enter1
  | exit0 | exit1

/-! ### ActionSpec -/

def peterson : ActionSpec PState PAction where
  init := fun s =>
    s.flag0 = false ∧ s.flag1 = false ∧
    s.turn = false ∧ s.pc0 = .idle ∧ s.pc1 = .idle
  actions := fun
    | .setFlag0 => {
        gate := fun s => s.pc0 = .idle
        transition := fun s s' =>
          s' = { s with flag0 := true, pc0 := .flagged }
      }
    | .setFlag1 => {
        gate := fun s => s.pc1 = .idle
        transition := fun s s' =>
          s' = { s with flag1 := true, pc1 := .flagged }
      }
    | .setTurn0 => {
        gate := fun s => s.pc0 = .flagged
        transition := fun s s' =>
          s' = { s with turn := true, pc0 := .waiting }   -- yield to process 1
      }
    | .setTurn1 => {
        gate := fun s => s.pc1 = .flagged
        transition := fun s s' =>
          s' = { s with turn := false, pc1 := .waiting }  -- yield to process 0
      }
    | .enter0 => {
        gate := fun s => s.pc0 = .waiting ∧ (s.flag1 = false ∨ s.turn = false)
        transition := fun s s' =>
          s' = { s with pc0 := .cs }
      }
    | .enter1 => {
        gate := fun s => s.pc1 = .waiting ∧ (s.flag0 = false ∨ s.turn = true)
        transition := fun s s' =>
          s' = { s with pc1 := .cs }
      }
    | .exit0 => {
        gate := fun s => s.pc0 = .cs
        transition := fun s s' =>
          s' = { s with flag0 := false, pc0 := .idle }
      }
    | .exit1 => {
        gate := fun s => s.pc1 = .cs
        transition := fun s s' =>
          s' = { s with flag1 := false, pc1 := .idle }
      }

/-! ### Mutual exclusion property -/

def mutex (s : PState) : Prop :=
  ¬ (s.pc0 = .cs ∧ s.pc1 = .cs)

/-! ### Inductive invariant

    Mutual exclusion alone is not inductive. We strengthen it with:
    - Flag consistency: flag[i] = true iff process i is past idle
    - Turn arbitration: when one is in CS and the other is waiting,
      turn favors the one in CS -/

def inv (s : PState) : Prop :=
  -- Flag consistency
  (s.flag0 = true ↔ s.pc0 ≠ .idle) ∧
  (s.flag1 = true ↔ s.pc1 ≠ .idle) ∧
  -- Mutual exclusion
  ¬ (s.pc0 = .cs ∧ s.pc1 = .cs) ∧
  -- Turn arbitration
  (s.pc0 = .cs → s.pc1 = .waiting → s.turn = false) ∧
  (s.pc1 = .cs → s.pc0 = .waiting → s.turn = true)

theorem inv_init : ∀ s, peterson.init s → inv s := by
  intro s ⟨hf0, hf1, _, hpc0, hpc1⟩
  simp [inv, hf0, hf1, hpc0, hpc1]

theorem inv_next : ∀ s s', (∃ i, (peterson.actions i).fires s s') → inv s → inv s' := by
  intro s s' ⟨i, hfire⟩ hinv
  cases i <;> simp [peterson, GatedAction.fires] at hfire <;>
    obtain ⟨hgate, htrans⟩ := hfire <;> subst htrans <;>
    simp [inv] at * <;> aesop

theorem mutex_invariant :
    pred_implies peterson.toSpec.safety [tlafml| □ ⌜ mutex ⌝] := by
  apply pred_implies_trans (q := [tlafml| □ ⌜ inv ⌝])
  · apply init_invariant
    · exact inv_init
    · intro s s' hnext hinv ; exact inv_next s s' hnext hinv
  · apply always_monotone
    intro e hinv ; exact hinv.2.2.1

/-! ### Abstract lock specification -/

inductive ProcId where | p0 | p1
  deriving DecidableEq, Repr

structure LockState where
  holder : Option ProcId

inductive LockAction where
  | enter0 | enter1
  | leave0 | leave1

def lock : ActionSpec LockState LockAction where
  init := fun s => s.holder = none
  actions := fun
    | .enter0 => {
        gate := fun s => s.holder = none
        transition := fun _ s' => s' = { holder := some .p0 }
      }
    | .enter1 => {
        gate := fun s => s.holder = none
        transition := fun _ s' => s' = { holder := some .p1 }
      }
    | .leave0 => {
        gate := fun s => s.holder = some .p0
        transition := fun _ s' => s' = { holder := none }
      }
    | .leave1 => {
        gate := fun s => s.holder = some .p1
        transition := fun _ s' => s' = { holder := none }
      }

/-! ### Refinement mapping -/

def abs_map (s : PState) : LockState where
  holder := if s.pc0 = .cs then some .p0
            else if s.pc1 = .cs then some .p1
            else none

theorem peterson_refines_lock :
    refines_via abs_map peterson.toSpec.safety lock.toSpec.safety_stutter := by
  apply refinement_mapping_stutter_with_invariant
    peterson.toSpec lock.toSpec abs_map inv
  · exact inv_init
  · intro s s' hinv ⟨i, hfire⟩ ; exact inv_next s s' ⟨i, hfire⟩ hinv
  · intro s ⟨_, _, _, hpc0, hpc1⟩
    simp [abs_map, lock, ActionSpec.toSpec, hpc0, hpc1]
  · intro s s' hinv ⟨i, hfire⟩
    have ⟨hflag0, hflag1, hmutex, hturn0, hturn1⟩ := hinv
    cases i <;> simp [peterson, GatedAction.fires] at hfire <;>
      obtain ⟨hgate, htrans⟩ := hfire <;> subst htrans
    -- setFlag0: stuttering (pc0 goes idle → flagged, not cs)
    · right ; simp [abs_map, hgate]
    -- setFlag1: stuttering
    · right ; simp [abs_map, hgate]
    -- setTurn0: stuttering (pc0 goes flagged → waiting, not cs)
    · right ; simp [abs_map, hgate]
    -- setTurn1: stuttering
    · right ; simp [abs_map, hgate]
    -- enter0: maps to lock.enter0
    · have hno1 : ¬s.pc1 = .cs := by
        intro hcs1
        have hf1 := hflag1.mpr (by simp [hcs1])
        have ht := hturn1 hcs1 hgate.1
        cases hgate.2 with | inl h => simp_all | inr h => simp_all
      left ; exact ⟨.enter0,
        by simp [lock, abs_map, hgate.1, hno1],
        by simp [lock, abs_map, hgate.1, hno1]⟩
    -- enter1: maps to lock.enter1
    · have hno0 : ¬s.pc0 = .cs := by
        intro hcs0
        have hf0 := hflag0.mpr (by simp [hcs0])
        have ht := hturn0 hcs0 hgate.1
        cases hgate.2 with | inl h => simp_all | inr h => simp_all
      left ; exact ⟨.enter1,
        by simp [lock, abs_map, hgate.1, hno0],
        by simp [lock, abs_map, hgate.1, hno0]⟩
    -- exit0: maps to lock.leave0
    · have hno1 : ¬ s.pc1 = .cs := fun h => hmutex ⟨hgate, h⟩
      left ; exact ⟨.leave0,
        by simp [lock, abs_map, hgate],
        by simp_all [lock, abs_map]⟩
    -- exit1: maps to lock.leave1
    · have hno0 : ¬ s.pc0 = .cs := fun h => hmutex ⟨h, hgate⟩
      left ; exact ⟨.leave1,
        by simp [lock, abs_map, hgate, hno0],
        by simp_all [lock, abs_map]⟩

end Peterson
