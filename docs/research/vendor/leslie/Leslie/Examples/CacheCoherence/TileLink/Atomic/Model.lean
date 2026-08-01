import Leslie.SymShared
import Leslie.Examples.CacheCoherence.TileLink.Common

open TLA SymShared

/-! ## TileLink TL-C Atomic Model

    A first atomic single-line model for TileLink TL-C. The initial acquire
    step schedules a probe/grant wave, `finishGrant` atomically consumes the
    required probe obligations and delivers the grant, and `GrantAck` /
    `ReleaseAck` remain explicit so the model still tracks same-block
    serialization obligations.

    Status of this model:

    - It is a parameterized single-line model over `n` symmetric caches.
    - Shared state tracks home memory, a directory summary, pending grant
      metadata, and pending `GrantAck` / `ReleaseAck` obligations.
    - Local state tracks permission, validity, dirtiness, and data.
    - `AcquirePerm` grants `T` permission without valid data.
    - `AcquireBlock` / `AcquirePerm` schedule a pending coherence wave, and
      `finishGrant` resolves that wave atomically.
    - `Release` and `ReleaseData` are distinct abstract C-channel actions.

    Verified properties are proved in `Invariant.lean`, `StepProof.lean`, and
    `Theorem.lean`. The current invariant establishes:

    - single-writer / single-tip safety
    - pending `GrantAck` / `ReleaseAck` discipline
    - directory agreement with local permissions
    - local cache-line well-formedness
    - clean valid copies agree with home memory
    - the dirty owner determines the model's logical line value

    Important differences from full TL-C:

    - one address / one cache line only
    - no explicit A/B/C/D/E message network
    - no source/sink IDs, multibeat transfers, `denied`, or `corrupt`
    - probe fanout / probe responses are abstracted into metadata plus
      `finishGrant`
    - no forwarded B/C access flows
    - no liveness proof
    - no explicit-message refinement yet

    The current pending-grant invariant distinguishes scheduled and delivered
    grant phases, but only at the phase/shape level. It does not yet encode a
    stronger post-grant state correspondence.
-/

namespace TileLink.Atomic

open TileLink

inductive GrantKind where
  | block
  | perm
  deriving DecidableEq, Repr

structure PendingGrantMeta where
  requester : Nat
  kind : GrantKind
  requesterPerm : TLPerm
  usedDirtySource : Bool
  transferVal : Val
  probesNeeded : Nat → Bool
  probesRemaining : Nat → Bool

@[ext] structure HomeState where
  mem : Val
  dir : Nat → TLPerm
  pendingGrantMeta : Option PendingGrantMeta
  pendingGrantAck : Option Nat
  pendingReleaseAck : Option Nat

inductive Act where
  | acquireBlock
  | acquirePerm
  | finishGrant
  | store (v : Val)
  | grantAck
  | release (param : PruneReportParam)
  | releaseData (param : PruneReportParam)
  | releaseAck
  | uncachedWrite (v : Val)
  deriving DecidableEq

def invalidateLine (line : CacheLine) : CacheLine :=
  { line with perm := .N, valid := false, dirty := false }

def branchLine (v : Val) : CacheLine :=
  { perm := .B, valid := true, dirty := false, data := v }

def tipLine (v : Val) : CacheLine :=
  { perm := .T, valid := true, dirty := false, data := v }

/-- `AcquirePerm` grants write authority without providing valid data. -/
def grantPermLine (line : CacheLine) : CacheLine :=
  { line with perm := .T, valid := false, dirty := false }

def dirtyTipLine (v : Val) : CacheLine :=
  { perm := .T, valid := true, dirty := true, data := v }

def releasedLine (line : CacheLine) (perm : TLPerm) : CacheLine :=
  match perm with
  | .N => invalidateLine line
  | .B => branchLine line.data
  | .T => tipLine line.data

def syncDir {n : Nat} (dir : Nat → TLPerm) (locals : Fin n → CacheLine) : Nat → TLPerm :=
  fun k =>
    if hk : k < n then
      (locals ⟨k, hk⟩).perm
    else
      dir k

@[simp] theorem syncDir_apply_fin {n : Nat} (dir : Nat → TLPerm)
    (locals : Fin n → CacheLine) (i : Fin n) :
    syncDir dir locals i.1 = (locals i).perm := by
  simp [syncDir, i.is_lt]

@[simp] theorem invalidateLine_perm (line : CacheLine) :
    (invalidateLine line).perm = .N := rfl

@[simp] theorem invalidateLine_valid (line : CacheLine) :
    (invalidateLine line).valid = false := rfl

@[simp] theorem invalidateLine_dirty (line : CacheLine) :
    (invalidateLine line).dirty = false := rfl

@[simp] theorem invalidateLine_data (line : CacheLine) :
    (invalidateLine line).data = line.data := rfl

@[simp] theorem branchLine_perm (v : Val) : (branchLine v).perm = .B := rfl
@[simp] theorem branchLine_valid (v : Val) : (branchLine v).valid = true := rfl
@[simp] theorem branchLine_dirty (v : Val) : (branchLine v).dirty = false := rfl
@[simp] theorem branchLine_data (v : Val) : (branchLine v).data = v := rfl

@[simp] theorem tipLine_perm (v : Val) : (tipLine v).perm = .T := rfl
@[simp] theorem tipLine_valid (v : Val) : (tipLine v).valid = true := rfl
@[simp] theorem tipLine_dirty (v : Val) : (tipLine v).dirty = false := rfl
@[simp] theorem tipLine_data (v : Val) : (tipLine v).data = v := rfl

@[simp] theorem grantPermLine_perm (line : CacheLine) : (grantPermLine line).perm = .T := rfl
@[simp] theorem grantPermLine_valid (line : CacheLine) : (grantPermLine line).valid = false := rfl
@[simp] theorem grantPermLine_dirty (line : CacheLine) : (grantPermLine line).dirty = false := rfl
@[simp] theorem grantPermLine_data (line : CacheLine) : (grantPermLine line).data = line.data := rfl

@[simp] theorem dirtyTipLine_perm (v : Val) : (dirtyTipLine v).perm = .T := rfl
@[simp] theorem dirtyTipLine_valid (v : Val) : (dirtyTipLine v).valid = true := rfl
@[simp] theorem dirtyTipLine_dirty (v : Val) : (dirtyTipLine v).dirty = true := rfl
@[simp] theorem dirtyTipLine_data (v : Val) : (dirtyTipLine v).data = v := rfl

@[simp] theorem invalidateLine_wf (line : CacheLine) :
    (invalidateLine line).WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · intro hdirty
    simp at hdirty
  · intro hperm
    simp at hperm
  · intro hperm
    simp

@[simp] theorem branchLine_wf (v : Val) : (branchLine v).WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · intro hdirty
    simp at hdirty
  · intro _
    rfl
  · intro hperm
    simp at hperm

@[simp] theorem tipLine_wf (v : Val) : (tipLine v).WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · intro hdirty
    simp at hdirty
  · intro hperm
    simp at hperm
  · intro hperm
    simp at hperm

@[simp] theorem grantPermLine_wf (line : CacheLine) : (grantPermLine line).WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · intro hdirty
    simp at hdirty
  · intro hperm
    simp at hperm
  · intro hperm
    simp at hperm

@[simp] theorem dirtyTipLine_wf (v : Val) : (dirtyTipLine v).WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · intro _
    simp
  · intro hperm
    simp at hperm
  · intro hperm
    simp at hperm

@[simp] theorem releasedLine_perm (line : CacheLine) (perm : TLPerm) :
    (releasedLine line perm).perm = perm := by
  cases perm <;> rfl

@[simp] theorem releasedLine_dirty (line : CacheLine) (perm : TLPerm) :
    (releasedLine line perm).dirty = false := by
  cases perm <;> rfl

@[simp] theorem releasedLine_data (line : CacheLine) (perm : TLPerm) :
    (releasedLine line perm).data = line.data := by
  cases perm <;> rfl

@[simp] theorem releasedLine_wf (line : CacheLine) (perm : TLPerm) :
    (releasedLine line perm).WellFormed := by
  cases perm <;> simp [releasedLine]

def hasDirtyOther (n : Nat) (i : Fin n) (s : SymState HomeState CacheLine n) : Prop :=
  ∃ j : Fin n, j ≠ i ∧ (s.locals j).dirty = true

def hasCachedOther (n : Nat) (i : Fin n) (s : SymState HomeState CacheLine n) : Prop :=
  ∃ j : Fin n, j ≠ i ∧ (s.locals j).perm ≠ .N

def allOthersInvalid (n : Nat) (i : Fin n) (s : SymState HomeState CacheLine n) : Prop :=
  ∀ j : Fin n, j ≠ i → (s.locals j).perm = .N

def noProbeMask : Nat → Bool :=
  fun _ => false

@[simp] theorem noProbeMask_apply (k : Nat) : noProbeMask k = false := rfl

def singleProbeMask (j : Nat) : Nat → Bool :=
  fun k => decide (k = j)

theorem singleProbeMask_eq_true {j k : Nat} :
    singleProbeMask j k = true ↔ k = j := by
  simp [singleProbeMask]

def writableProbeMask {n : Nat}
    (s : SymState HomeState CacheLine n) (i : Fin n) : Nat → Bool :=
  fun k =>
    if hk : k < n then
      let p : Fin n := ⟨k, hk⟩
      if p = i then false else decide ((s.locals p).perm = .T)
    else
      false

def cachedProbeMask {n : Nat}
    (s : SymState HomeState CacheLine n) (i : Fin n) : Nat → Bool :=
  fun k =>
    if hk : k < n then
      let p : Fin n := ⟨k, hk⟩
      if p = i then false else decide ((s.locals p).perm ≠ .N)
    else
      false

def acquireBlockSharedLocals {n : Nat}
    (s : SymState HomeState CacheLine n) (i : Fin n) : Fin n → CacheLine :=
  fun k =>
    if k = i then
      branchLine s.shared.mem
    else if (s.locals k).perm = .T then
      branchLine s.shared.mem
    else
      s.locals k

def acquireBlockDirtyLocals {n : Nat}
    (s : SymState HomeState CacheLine n) (i j : Fin n) : Fin n → CacheLine :=
  fun k =>
    if k = i then
      branchLine (s.locals j).data
    else if k = j then
      branchLine (s.locals j).data
    else
      s.locals k

def acquirePermLocals {n : Nat}
    (s : SymState HomeState CacheLine n) (i : Fin n) : Fin n → CacheLine :=
  fun k =>
    if k = i then
      grantPermLine (s.locals k)
    else
      invalidateLine (s.locals k)

def deliveredGrantMeta (pg : PendingGrantMeta) : PendingGrantMeta :=
  { pg with probesRemaining := noProbeMask }

-- ── Post-state definitions ──────────────────────────────────────────

/-- `acquireBlock` dirty sub-case: schedule probe of dirty owner `j`. -/
@[reducible] def acquireBlockDirtyState {n : Nat}
    (s : SymState HomeState CacheLine n) (i j : Fin n) : SymState HomeState CacheLine n :=
  { shared := { s.shared with
                  pendingGrantMeta := some {
                    requester := i.1
                    kind := .block
                    requesterPerm := .B
                    usedDirtySource := true
                    transferVal := (s.locals j).data
                    probesNeeded := singleProbeMask j.1
                    probesRemaining := singleProbeMask j.1 }
                , pendingGrantAck := none
                , pendingReleaseAck := none }
  , locals := s.locals }

/-- `acquireBlock` shared sub-case: schedule probe of writable sharers. -/
@[reducible] def acquireBlockSharedState {n : Nat}
    (s : SymState HomeState CacheLine n) (i : Fin n) : SymState HomeState CacheLine n :=
  { shared := { s.shared with
                  pendingGrantMeta := some {
                    requester := i.1
                    kind := .block
                    requesterPerm := .B
                    usedDirtySource := false
                    transferVal := s.shared.mem
                    probesNeeded := writableProbeMask s i
                    probesRemaining := writableProbeMask s i },
                  pendingGrantAck := none,
                  pendingReleaseAck := none }
  , locals := s.locals }

/-- `acquireBlock` invalid sub-case: no probes needed, grant Tip. -/
@[reducible] def acquireBlockInvalidState {n : Nat}
    (s : SymState HomeState CacheLine n) (i : Fin n) : SymState HomeState CacheLine n :=
  { shared := { s.shared with
                  pendingGrantMeta := some {
                    requester := i.1
                    kind := .block
                    requesterPerm := .T
                    usedDirtySource := false
                    transferVal := s.shared.mem
                    probesNeeded := noProbeMask
                    probesRemaining := noProbeMask },
                  pendingGrantAck := none,
                  pendingReleaseAck := none }
  , locals := s.locals }

/-- `acquirePerm` dirty sub-case: schedule probe of all cached. -/
@[reducible] def acquirePermDirtyState {n : Nat}
    (s : SymState HomeState CacheLine n) (i j : Fin n) : SymState HomeState CacheLine n :=
  { shared := { s.shared with
                  pendingGrantMeta := some {
                    requester := i.1
                    kind := .perm
                    requesterPerm := .T
                    usedDirtySource := true
                    transferVal := (s.locals j).data
                    probesNeeded := cachedProbeMask s i
                    probesRemaining := cachedProbeMask s i }
                , pendingGrantAck := none
                , pendingReleaseAck := none }
  , locals := s.locals }

/-- `acquirePerm` clean sub-case. -/
@[reducible] def acquirePermCleanState {n : Nat}
    (s : SymState HomeState CacheLine n) (i : Fin n) : SymState HomeState CacheLine n :=
  { shared := { s.shared with
                  pendingGrantMeta := some {
                    requester := i.1
                    kind := .perm
                    requesterPerm := .T
                    usedDirtySource := false
                    transferVal := s.shared.mem
                    probesNeeded := cachedProbeMask s i
                    probesRemaining := cachedProbeMask s i },
                  pendingGrantAck := none,
                  pendingReleaseAck := none }
  , locals := s.locals }

/-- `finishGrant` block-dirty sub-case. -/
@[reducible] def finishGrantBlockDirtyState {n : Nat}
    (s : SymState HomeState CacheLine n) (i j : Fin n) (pg : PendingGrantMeta) :
    SymState HomeState CacheLine n :=
  { shared := { mem := (s.locals j).data
              , dir := syncDir s.shared.dir (acquireBlockDirtyLocals s i j)
              , pendingGrantMeta := some (deliveredGrantMeta pg)
              , pendingGrantAck := some i.1
              , pendingReleaseAck := none }
  , locals := acquireBlockDirtyLocals s i j }

/-- `finishGrant` block-shared sub-case. -/
@[reducible] def finishGrantBlockSharedState {n : Nat}
    (s : SymState HomeState CacheLine n) (i : Fin n) (pg : PendingGrantMeta) :
    SymState HomeState CacheLine n :=
  { shared := { mem := s.shared.mem
              , dir := syncDir s.shared.dir (acquireBlockSharedLocals s i)
              , pendingGrantMeta := some (deliveredGrantMeta pg)
              , pendingGrantAck := some i.1
              , pendingReleaseAck := none }
  , locals := acquireBlockSharedLocals s i }

/-- `finishGrant` block-tip (all others invalid) sub-case. -/
@[reducible] def finishGrantBlockTipState {n : Nat}
    (s : SymState HomeState CacheLine n) (i : Fin n) (pg : PendingGrantMeta) :
    SymState HomeState CacheLine n :=
  { shared := { mem := s.shared.mem
              , dir := syncDir s.shared.dir (setFn s.locals i (tipLine s.shared.mem))
              , pendingGrantMeta := some (deliveredGrantMeta pg)
              , pendingGrantAck := some i.1
              , pendingReleaseAck := none }
  , locals := setFn s.locals i (tipLine s.shared.mem) }

/-- `finishGrant` perm-dirty sub-case. -/
@[reducible] def finishGrantPermDirtyState {n : Nat}
    (s : SymState HomeState CacheLine n) (i j : Fin n) (pg : PendingGrantMeta) :
    SymState HomeState CacheLine n :=
  { shared := { mem := (s.locals j).data
              , dir := syncDir s.shared.dir (acquirePermLocals s i)
              , pendingGrantMeta := some (deliveredGrantMeta pg)
              , pendingGrantAck := some i.1
              , pendingReleaseAck := none }
  , locals := acquirePermLocals s i }

/-- `finishGrant` perm-clean sub-case. -/
@[reducible] def finishGrantPermCleanState {n : Nat}
    (s : SymState HomeState CacheLine n) (i : Fin n) (pg : PendingGrantMeta) :
    SymState HomeState CacheLine n :=
  { shared := { mem := s.shared.mem
              , dir := syncDir s.shared.dir (acquirePermLocals s i)
              , pendingGrantMeta := some (deliveredGrantMeta pg)
              , pendingGrantAck := some i.1
              , pendingReleaseAck := none }
  , locals := acquirePermLocals s i }

/-- `store` post-state. -/
@[reducible] def storeState {n : Nat}
    (s : SymState HomeState CacheLine n) (i : Fin n) (v : Val) :
    SymState HomeState CacheLine n :=
  { shared := { s.shared with mem := v }
  , locals := setFn s.locals i (dirtyTipLine v) }

/-- `grantAck` post-state. -/
@[reducible] def grantAckState {n : Nat}
    (s : SymState HomeState CacheLine n) : SymState HomeState CacheLine n :=
  { shared := { s.shared with pendingGrantMeta := none, pendingGrantAck := none }
  , locals := s.locals }

/-- `release` post-state. -/
@[reducible] def releaseState {n : Nat}
    (s : SymState HomeState CacheLine n) (i : Fin n) (param : PruneReportParam) :
    SymState HomeState CacheLine n :=
  { shared := { mem := s.shared.mem
              , dir := syncDir s.shared.dir (setFn s.locals i (releasedLine (s.locals i) param.result))
              , pendingGrantMeta := none
              , pendingGrantAck := none
              , pendingReleaseAck := some i.1 }
  , locals := setFn s.locals i (releasedLine (s.locals i) param.result) }

/-- `releaseData` post-state. -/
@[reducible] def releaseDataState {n : Nat}
    (s : SymState HomeState CacheLine n) (i : Fin n) (param : PruneReportParam) :
    SymState HomeState CacheLine n :=
  { shared := { mem := (s.locals i).data
              , dir := syncDir s.shared.dir (setFn s.locals i (releasedLine (s.locals i) param.result))
              , pendingGrantMeta := none
              , pendingGrantAck := none
              , pendingReleaseAck := some i.1 }
  , locals := setFn s.locals i (releasedLine (s.locals i) param.result) }

/-- `releaseAck` post-state. -/
@[reducible] def releaseAckState {n : Nat}
    (s : SymState HomeState CacheLine n) : SymState HomeState CacheLine n :=
  { shared := { s.shared with pendingReleaseAck := none }
  , locals := s.locals }

/-- `uncachedWrite` post-state. -/
@[reducible] def uncachedWriteState {n : Nat}
    (s : SymState HomeState CacheLine n) (v : Val) : SymState HomeState CacheLine n :=
  { shared := { s.shared with mem := v }
  , locals := s.locals }

-- ── End post-state definitions ──────────────────────────────────────

def tlAtomic : SymSharedSpec where
  Shared := HomeState
  Local := CacheLine
  ActType := Act
  init_shared := fun sh =>
    sh.mem = 0 ∧
    (∀ k : Nat, sh.dir k = .N) ∧
    sh.pendingGrantMeta = none ∧
    sh.pendingGrantAck = none ∧
    sh.pendingReleaseAck = none
  init_local := fun line =>
    line.perm = .N ∧
    line.valid = false ∧
    line.dirty = false ∧
    line.data = 0
  step := fun n i a s s' =>
    match a with
    | .acquireBlock =>
        s.shared.pendingGrantMeta = none ∧
        s.shared.pendingGrantAck = none ∧
        s.shared.pendingReleaseAck = none ∧
        (s.locals i).perm = .N ∧
        ((∃ j : Fin n, j ≠ i ∧ (s.locals j).dirty = true ∧
          s' = acquireBlockDirtyState s i j) ∨
         ((¬hasDirtyOther n i s) ∧ hasCachedOther n i s ∧
          s' = acquireBlockSharedState s i) ∨
         (allOthersInvalid n i s ∧
          s' = acquireBlockInvalidState s i))
    | .acquirePerm =>
        s.shared.pendingGrantMeta = none ∧
        s.shared.pendingGrantAck = none ∧
        s.shared.pendingReleaseAck = none ∧
        (s.locals i).perm ≠ .T ∧
        ((∃ j : Fin n, j ≠ i ∧ (s.locals j).dirty = true ∧
          s' = acquirePermDirtyState s i j) ∨
         ((¬hasDirtyOther n i s) ∧
          s' = acquirePermCleanState s i))
    | .finishGrant =>
        (∃ pg, s.shared.pendingGrantMeta = some pg ∧
          s.shared.pendingGrantAck = none ∧
          s.shared.pendingReleaseAck = none ∧
          pg.requester = i.1 ∧
          ((∃ j : Fin n, j ≠ i ∧ (s.locals j).dirty = true ∧
              pg.kind = .block ∧
              pg.requesterPerm = .B ∧
              pg.usedDirtySource = true ∧
              pg.transferVal = (s.locals j).data ∧
              pg.probesNeeded = singleProbeMask j.1 ∧
              pg.probesRemaining = singleProbeMask j.1 ∧
              s' = finishGrantBlockDirtyState s i j pg) ∨
           ((¬hasDirtyOther n i s) ∧ hasCachedOther n i s ∧
            pg.kind = .block ∧
            pg.requesterPerm = .B ∧
            pg.usedDirtySource = false ∧
            pg.transferVal = s.shared.mem ∧
            pg.probesNeeded = writableProbeMask s i ∧
            pg.probesRemaining = writableProbeMask s i ∧
            s' = finishGrantBlockSharedState s i pg) ∨
           (allOthersInvalid n i s ∧
            pg.kind = .block ∧
            pg.requesterPerm = .T ∧
            pg.usedDirtySource = false ∧
            pg.transferVal = s.shared.mem ∧
            pg.probesNeeded = noProbeMask ∧
            pg.probesRemaining = noProbeMask ∧
            s' = finishGrantBlockTipState s i pg) ∨
           (∃ j : Fin n, j ≠ i ∧ (s.locals j).dirty = true ∧
              pg.kind = .perm ∧
              pg.requesterPerm = .T ∧
              pg.usedDirtySource = true ∧
              pg.transferVal = (s.locals j).data ∧
              pg.probesNeeded = cachedProbeMask s i ∧
              pg.probesRemaining = cachedProbeMask s i ∧
              s' = finishGrantPermDirtyState s i j pg) ∨
           ((¬hasDirtyOther n i s) ∧
            pg.kind = .perm ∧
            pg.requesterPerm = .T ∧
            pg.usedDirtySource = false ∧
            pg.transferVal = s.shared.mem ∧
            pg.probesNeeded = cachedProbeMask s i ∧
            pg.probesRemaining = cachedProbeMask s i ∧
            s' = finishGrantPermCleanState s i pg)))
    | .store v =>
        s.shared.pendingGrantMeta = none ∧
        s.shared.pendingGrantAck = none ∧
        s.shared.pendingReleaseAck = none ∧
        (s.locals i).perm = .T ∧
        s' = storeState s i v
    | .grantAck =>
        s.shared.pendingGrantAck = some i.1 ∧
        s' = grantAckState s
    | .release param =>
        s.shared.pendingGrantMeta = none ∧
        s.shared.pendingGrantAck = none ∧
        s.shared.pendingReleaseAck = none ∧
        param.legalFrom (s.locals i).perm ∧
        (s.locals i).dirty = false ∧
        ((s.locals i).valid = true ∨ param.result = .N) ∧
        s' = releaseState s i param
    | .releaseData param =>
        s.shared.pendingGrantMeta = none ∧
        s.shared.pendingGrantAck = none ∧
        s.shared.pendingReleaseAck = none ∧
        param.legalFrom (s.locals i).perm ∧
        (s.locals i).dirty = true ∧
        s' = releaseDataState s i param
    | .releaseAck =>
        s.shared.pendingReleaseAck = some i.1 ∧
        s' = releaseAckState s
    | .uncachedWrite v =>
        s.shared.pendingGrantMeta = none ∧
        s.shared.pendingGrantAck = none ∧
        (∀ j : Fin n, (s.locals j).perm = .N) ∧
        s' = uncachedWriteState s v

end TileLink.Atomic
