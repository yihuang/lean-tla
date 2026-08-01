import Leslie.Action

/-! ## CAS Counter Refinement

    We prove that a concurrent CAS-based counter refines an atomic counter
    via a stuttering refinement mapping.

    ### Concurrent counter (CAS-based, cf. Fig 2, OOPSLA'24)

    Each thread performs a single invocation of `inc` or `dec`:
    ```
    inc()/dec():
      do {
        loc = read(ctr)
        new = loc + delta       -- +1 for inc, -1 for dec
      } while (!CAS(ctr, loc, new))
      return ok
    ```

    The concrete actions per thread are:
    - `call`:     idle       → called      (external)
    - `rd`:       called     → read_done   (internal: loc := ctr)
    - `cas_succ`: read_done  → done        (internal: ctr := loc + delta, when ctr = loc)
    - `cas_fail`: read_done  → called      (internal: retry, when ctr ≠ loc)
    - `ret`:      done       → returned    (external)

    ### Atomic counter

    Same interface, single atomic internal step:
    - `call`: idle    → called    (external)
    - `step`: called  → done      (internal: ctr := ctr + delta)
    - `ret`:  done    → returned  (external)

    ### Refinement mapping

    The linearization point is the successful CAS (`cas_succ`).
    The mapping is the identity on `ctr` and `op`, and maps
    program counters via `abs_pc` which sends `read_done ↦ called`
    (the thread has not yet linearized) and is the identity otherwise.

    Every `call`/`ret` of the concrete maps to a `call`/`ret` of the
    abstract.  The `cas_succ` maps to the abstract `step`.  The `rd`
    and `cas_fail` actions stutter (the abstract state is unchanged).
-/

open TLA

namespace CASCounter

/-! ### Common definitions -/

/-- The operation a thread is performing. -/
inductive Op where | inc | dec
  deriving DecidableEq

/-- The integer offset corresponding to an operation. -/
def Op.delta : Op → Int
  | .inc => 1
  | .dec => -1

/-! ### Program counters -/

/-- Concrete program counter. -/
inductive CPC where
  | idle | called | read_done | done | returned
  deriving DecidableEq

/-- Abstract program counter. -/
inductive APC where
  | idle | called | done | returned
  deriving DecidableEq

/-! ### States -/

/-- Concrete state: shared counter, per-thread PC, operation, and
    local snapshot `loc`. -/
structure CState (Tid : Type) where
  ctr : Int
  pc  : Tid → CPC
  op  : Tid → Op
  loc : Tid → Int

/-- Abstract state: shared counter, per-thread PC and operation. -/
@[ext]
structure AState (Tid : Type) where
  ctr : Int
  pc  : Tid → APC
  op  : Tid → Op

variable {Tid : Type} [DecidableEq Tid]

/-! ### Concrete CAS counter -/

/-- Action labels for the concrete counter. -/
inductive CAction (Tid : Type) where
  | call     (t : Tid)
  | rd       (t : Tid)
  | cas_succ (t : Tid)
  | cas_fail (t : Tid)
  | ret      (t : Tid)

/-- The concurrent CAS-based counter as an `ActionSpec`. -/
def cas_counter : ActionSpec (CState Tid) (CAction Tid) where
  init := fun s =>
    s.ctr = 0 ∧ (∀ t, s.pc t = .idle) ∧ (∀ t, s.loc t = 0)
  actions := fun
    | .call t => {
        gate := fun s => s.pc t = .idle
        transition := fun s s' =>
          s' = { s with pc := fun t' => if t' = t then .called else s.pc t' } }
    | .rd t => {
        gate := fun s => s.pc t = .called
        transition := fun s s' =>
          s' = { s with
            pc  := fun t' => if t' = t then .read_done else s.pc t'
            loc := fun t' => if t' = t then s.ctr else s.loc t' } }
    | .cas_succ t => {
        gate := fun s => s.pc t = .read_done ∧ s.ctr = s.loc t
        transition := fun s s' =>
          s' = { s with
            ctr := s.loc t + (s.op t).delta
            pc  := fun t' => if t' = t then .done else s.pc t' } }
    | .cas_fail t => {
        gate := fun s => s.pc t = .read_done ∧ s.ctr ≠ s.loc t
        transition := fun s s' =>
          s' = { s with
            pc := fun t' => if t' = t then .called else s.pc t' } }
    | .ret t => {
        gate := fun s => s.pc t = .done
        transition := fun s s' =>
          s' = { s with pc := fun t' => if t' = t then .returned else s.pc t' } }

/-! ### Abstract atomic counter -/

/-- Action labels for the atomic counter. -/
inductive AAction (Tid : Type) where
  | call (t : Tid)
  | step (t : Tid)
  | ret  (t : Tid)

/-- The atomic counter as an `ActionSpec`. -/
def atomic_counter : ActionSpec (AState Tid) (AAction Tid) where
  init := fun s =>
    s.ctr = 0 ∧ (∀ t, s.pc t = .idle)
  actions := fun
    | .call t => {
        gate := fun s => s.pc t = .idle
        transition := fun s s' =>
          s' = { s with
            pc := fun t' => if t' = t then .called else s.pc t' } }
    | .step t => {
        gate := fun s => s.pc t = .called
        transition := fun s s' =>
          s' = { s with
            ctr := s.ctr + (s.op t).delta
            pc  := fun t' => if t' = t then .done else s.pc t' } }
    | .ret t => {
        gate := fun s => s.pc t = .done
        transition := fun s s' =>
          s' = { s with
            pc := fun t' => if t' = t then .returned else s.pc t' } }

/-! ### Refinement mapping -/

/-- Map concrete PCs to abstract PCs.
    The key choice: `read_done ↦ called` (pre-linearization). -/
def abs_pc : CPC → APC
  | .idle      => .idle
  | .called    => .called
  | .read_done => .called
  | .done      => .done
  | .returned  => .returned

/-- The refinement mapping from concrete to abstract states. -/
def ref_map (s : CState Tid) : AState Tid where
  ctr := s.ctr
  pc  := fun t => abs_pc (s.pc t)
  op  := s.op

/-! ### Refinement proof -/

/-- The CAS counter refines the atomic counter (with stuttering). -/
theorem cas_counter_refines_atomic :
    refines_via (ref_map (Tid := Tid))
      (cas_counter (Tid := Tid)).toSpec.safety
      (atomic_counter (Tid := Tid)).toSpec.safety_stutter := by
  apply refinement_mapping_stutter cas_counter.toSpec atomic_counter.toSpec ref_map
  · -- Init preservation
    intro s ⟨hctr, hpc, _⟩
    exact ⟨hctr, fun t => by simp [ref_map, abs_pc, hpc t]⟩
  · -- Step simulation
    intro s s' ⟨i, hfire⟩
    cases i with
    | call t =>
      -- call: concrete idle → called, abstract idle → called
      obtain ⟨hg, ht⟩ := hfire
      dsimp only [cas_counter] at hg ht; subst ht
      left; refine ⟨.call t, by dsimp [atomic_counter, ref_map, abs_pc]; rw [hg], ?_⟩
      dsimp only [atomic_counter, ref_map]
      congr 1; funext t'
      by_cases h : t' = t
      · subst h; simp [abs_pc]
      · simp [h]
    | rd t =>
      -- read: stutter (read_done maps to called via abs_pc)
      obtain ⟨hg, ht⟩ := hfire
      dsimp only [cas_counter] at hg ht; subst ht
      right; dsimp only [ref_map]
      congr 1; funext t'
      by_cases h : t' = t
      · subst h; simp [abs_pc, hg]
      · simp [h]
    | cas_succ t =>
      -- CAS success: linearization point → abstract step
      obtain ⟨⟨hpc, hctr⟩, ht⟩ := hfire
      dsimp only [cas_counter] at hpc hctr ht; subst ht
      left; refine ⟨.step t, by dsimp [atomic_counter, ref_map, abs_pc]; rw [hpc], ?_⟩
      dsimp only [atomic_counter, ref_map]
      congr 1
      · -- ctr: loc t + delta = ctr + delta since ctr = loc t
        rw [hctr]
      · funext t'
        by_cases h : t' = t
        · subst h; simp [abs_pc]
        · simp [h]
    | cas_fail t =>
      -- CAS failure: stutter (called maps to called)
      obtain ⟨⟨hpc, _⟩, ht⟩ := hfire
      dsimp only [cas_counter] at hpc ht; subst ht
      right; dsimp only [ref_map]
      congr 1; funext t'
      by_cases h : t' = t
      · subst h; simp [abs_pc, hpc]
      · simp [h]
    | ret t =>
      -- return: concrete done → returned, abstract done → returned
      obtain ⟨hg, ht⟩ := hfire
      dsimp only [cas_counter] at hg ht; subst ht
      left; refine ⟨.ret t, by dsimp [atomic_counter, ref_map, abs_pc]; rw [hg], ?_⟩
      dsimp only [atomic_counter, ref_map]
      congr 1; funext t'
      by_cases h : t' = t
      · subst h; simp [abs_pc]
      · simp [h]

end CASCounter
