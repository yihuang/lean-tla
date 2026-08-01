import Leslie.Refinement
import Leslie.Examples.CacheCoherence.TileLink.Messages.Refinement.Preservation

namespace TileLink.Messages

open TLA TileLink SymShared Classical

/-- Map a message-level request kind to the atomic pending-grant kind. -/
def absGrantKind : ReqKind → TileLink.Atomic.GrantKind
  | .acquireBlock => .block
  | .acquirePerm => .perm

/-- Abstraction of a live message-level manager transaction to the atomic
    pending-grant summary. -/
def absPendingGrantMeta (tx : ManagerTxn) : TileLink.Atomic.PendingGrantMeta :=
  { requester := tx.requester
  , kind := absGrantKind tx.kind
  , requesterPerm := tx.resultPerm
  , usedDirtySource := tx.usedDirtySource
  , transferVal := tx.transferVal
  , probesNeeded := tx.probesNeeded
  , probesRemaining :=
      if tx.phase = .grantPendingAck then
        TileLink.Atomic.noProbeMask
      else
        tx.probesNeeded }

/-- Directory view before an acquire wave takes effect. -/
def preTxnDir (n : Nat) (tx : ManagerTxn) (dir : Nat → TLPerm) : Nat → TLPerm :=
  fun k =>
    if _hk : k < n then
      (tx.preLines k).perm
    else
      dir k

/-- Pick the unique queued release wave, if any. Reachable states in the
    current single-line model never have more than one. -/
noncomputable def queuedReleaseIdx (n : Nat) (s : SymState HomeState NodeState n) : Option Nat :=
  if h : ∃ i : Fin n, (s.locals i).releaseInFlight = true ∧ (s.locals i).chanC ≠ none then
    some (Classical.choose h).1
  else
    none

/-- Extract data from an in-flight dirty release message, if any.
    Used by the refinement map to track logical memory when a dirty release
    has been sent but not yet received by the manager. -/
noncomputable def findDirtyReleaseVal (n : Nat) (s : SymState HomeState NodeState n) : Option Val :=
  if h : ∃ i : Fin n, (s.locals i).releaseInFlight = true ∧
      ∃ msg : CMsg, (s.locals i).chanC = some msg ∧ msg.data ≠ none then
    let i := Classical.choose h
    let spec := (Classical.choose_spec h).2
    (Classical.choose spec).data
  else
    none

/-- Atomic-style directory view during `grantPendingAck`: requester permission
    is visible even if the concrete requester has not yet consumed D. -/
def grantPendingDir (n : Nat) (tx : ManagerTxn) (dir : Nat → TLPerm) : Nat → TLPerm :=
  if hk : tx.requester < n then
    updateDirAt dir ⟨tx.requester, hk⟩ tx.resultPerm
  else
    dir

/-- Message-level shared state mapped to the atomic wave-level summary state. -/
noncomputable def refMapShared (n : Nat) (s : SymState HomeState NodeState n) :
    TileLink.Atomic.HomeState :=
  let dir :=
    match s.shared.currentTxn with
    | none => TileLink.Atomic.syncDir s.shared.dir (fun i => (s.locals i).line)
    | some tx =>
        if tx.phase = .grantPendingAck then
          grantPendingDir n tx s.shared.dir
        else
          preTxnDir n tx s.shared.dir
  let pendingReleaseAck :=
    match s.shared.pendingReleaseAck with
    | some i => some i
    | none =>
        match s.shared.currentTxn with
        | some _ => none
        | none => queuedReleaseIdx n s
  let mem :=
    match s.shared.currentTxn with
    | some tx =>
        if tx.usedDirtySource then tx.transferVal else s.shared.mem
    | none =>
        -- Check for dirty owner (not releasing): its data is the logical value
        if h : ∃ j : Fin n, (s.locals j).line.dirty = true then
          (s.locals (Classical.choose h)).line.data
        else
          match findDirtyReleaseVal n s with
          | some v => v
          | none => s.shared.mem
  { mem := mem
  , dir := dir
  , pendingGrantMeta := s.shared.currentTxn.map absPendingGrantMeta
  , pendingGrantAck := s.shared.pendingGrantAck
  , pendingReleaseAck := pendingReleaseAck }

/-! ### Per-field projection lemmas for refMapShared

    These make simulation proofs modular: instead of reasoning about the
    entire 5-field record, each action only needs to show which fields
    changed and which stayed the same. -/

@[simp] theorem refMapShared_pendingGrantMeta (n : Nat) (s : SymState HomeState NodeState n) :
    (refMapShared n s).pendingGrantMeta = s.shared.currentTxn.map absPendingGrantMeta := rfl

@[simp] theorem refMapShared_pendingGrantAck (n : Nat) (s : SymState HomeState NodeState n) :
    (refMapShared n s).pendingGrantAck = s.shared.pendingGrantAck := rfl

/-- refMapShared.dir under currentTxn = none. -/
@[simp] theorem refMapShared_dir_none {n : Nat} {s : SymState HomeState NodeState n}
    (h : s.shared.currentTxn = none) :
    (refMapShared n s).dir = TileLink.Atomic.syncDir s.shared.dir (fun i => (s.locals i).line) := by
  simp [refMapShared, h]

/-- refMapShared.dir under currentTxn = some tx, phase ≠ grantPendingAck. -/
@[simp] theorem refMapShared_dir_some_not_gpa {n : Nat} {s : SymState HomeState NodeState n}
    {tx : ManagerTxn} (hcur : s.shared.currentTxn = some tx)
    (hphase : tx.phase ≠ .grantPendingAck) :
    (refMapShared n s).dir = preTxnDir n tx s.shared.dir := by
  simp [refMapShared, hcur, hphase]

/-- refMapShared.dir under currentTxn = some tx, phase = grantPendingAck. -/
@[simp] theorem refMapShared_dir_gpa {n : Nat} {s : SymState HomeState NodeState n}
    {tx : ManagerTxn} (hcur : s.shared.currentTxn = some tx)
    (hphase : tx.phase = .grantPendingAck) :
    (refMapShared n s).dir = grantPendingDir n tx s.shared.dir := by
  simp [refMapShared, hcur, hphase]

/-- refMapShared.mem under currentTxn = some tx. -/
@[simp] theorem refMapShared_mem_some {n : Nat} {s : SymState HomeState NodeState n}
    {tx : ManagerTxn} (hcur : s.shared.currentTxn = some tx) :
    (refMapShared n s).mem =
      if tx.usedDirtySource then tx.transferVal else s.shared.mem := by
  simp [refMapShared, hcur]

/-- refMapShared.mem under currentTxn = none. -/
theorem refMapShared_mem_none {n : Nat} {s : SymState HomeState NodeState n}
    (hcur : s.shared.currentTxn = none) :
    (refMapShared n s).mem =
      if h : ∃ j : Fin n, (s.locals j).line.dirty = true then
        (s.locals (Classical.choose h)).line.data
      else
        match findDirtyReleaseVal n s with
        | some v => v
        | none => s.shared.mem := by
  simp [refMapShared, hcur]

/-- refMapShared.pendingReleaseAck under pendingReleaseAck = some. -/
@[simp] theorem refMapShared_pra_some {n : Nat} {s : SymState HomeState NodeState n}
    {i : Nat} (h : s.shared.pendingReleaseAck = some i) :
    (refMapShared n s).pendingReleaseAck = some i := by
  simp [refMapShared, h]

/-- refMapShared.pendingReleaseAck under pendingReleaseAck = none, currentTxn = some. -/
@[simp] theorem refMapShared_pra_none_txn {n : Nat} {s : SymState HomeState NodeState n}
    {tx : ManagerTxn} (hrel : s.shared.pendingReleaseAck = none)
    (hcur : s.shared.currentTxn = some tx) :
    (refMapShared n s).pendingReleaseAck = none := by
  simp [refMapShared, hrel, hcur]

/-- refMapShared.pendingReleaseAck under pendingReleaseAck = none, currentTxn = none. -/
@[simp] theorem refMapShared_pra_none_notxn {n : Nat} {s : SymState HomeState NodeState n}
    (hrel : s.shared.pendingReleaseAck = none) (hcur : s.shared.currentTxn = none) :
    (refMapShared n s).pendingReleaseAck = queuedReleaseIdx n s := by
  simp [refMapShared, hrel, hcur]


theorem findDirtyReleaseVal_none_of_all_chanC_none' {n : Nat}
    (s : SymState HomeState NodeState n)
    (hallC : ∀ j : Fin n, (s.locals j).chanC = none) :
    findDirtyReleaseVal n s = none := by
  unfold findDirtyReleaseVal
  have hnone : ¬∃ i : Fin n, (s.locals i).releaseInFlight = true ∧
      ∃ msg : CMsg, (s.locals i).chanC = some msg ∧ msg.data ≠ none := by
    intro ⟨j, _, msg, hC, _⟩; rw [hallC j] at hC; cases hC
  simp [hnone]

/-! ### Per-action mem lemmas

    The `mem` field of `refMapShared` is the hardest to reason about.
    These lemmas specialize it for each action that changes the refMap. -/

/-- sendGrant preserves refMapShared.mem: same tx (just phase change), same mem. -/
theorem refMapShared_mem_sendGrant {n : Nat}
    {s : SymState HomeState NodeState n} {i : Fin n} {tx : ManagerTxn}
    (hcur : s.shared.currentTxn = some tx) :
    (refMapShared n (sendGrantState s i tx)).mem = (refMapShared n s).mem := by
  simp [refMapShared, sendGrantState, sendGrantShared, hcur]

/-- recvGrant preserves refMapShared.mem: currentTxn unchanged. -/
theorem refMapShared_mem_recvGrant {n : Nat}
    {s : SymState HomeState NodeState n} {i : Fin n} {tx : ManagerTxn}
    (hcur : s.shared.currentTxn = some tx) :
    (refMapShared n (recvGrantState s i tx)).mem = (refMapShared n s).mem := by
  simp [refMapShared, recvGrantState, recvGrantShared, hcur]

/-- recvProbeAck preserves refMapShared.mem when usedDirtySource = true:
    transferVal is unchanged, and mem is unchanged in the shared state. -/
theorem refMapShared_mem_recvProbeAck_dirty {n : Nat}
    {s : SymState HomeState NodeState n} {i : Fin n}
    {tx : ManagerTxn} {msg : CMsg}
    (hused : tx.usedDirtySource = true) :
    (refMapShared n (recvProbeAckState s i tx msg)).mem = tx.transferVal := by
  simp [refMapShared, recvProbeAckState, recvProbeAckShared, hused]

/-- recvProbeAck preserves refMapShared.mem when usedDirtySource = false
    and msg carries no data (non-dirty probeAck). -/
theorem refMapShared_mem_recvProbeAck_clean {n : Nat}
    {s : SymState HomeState NodeState n} {i : Fin n}
    {tx : ManagerTxn} {msg : CMsg}
    (hused : tx.usedDirtySource = false) (hdata : msg.data = none) :
    (refMapShared n (recvProbeAckState s i tx msg)).mem = s.shared.mem := by
  simp [refMapShared, recvProbeAckState, recvProbeAckShared, hused, hdata]

/-- recvProbeAck: when usedDirtySource = false, mem reduces to match on msg.data. -/
theorem refMapShared_mem_recvProbeAck_clean' {n : Nat}
    {s : SymState HomeState NodeState n} {i : Fin n}
    {tx : ManagerTxn} {msg : CMsg}
    (hused : tx.usedDirtySource = false) :
    (refMapShared n (recvProbeAckState s i tx msg)).mem =
      match msg.data with | some v => v | none => s.shared.mem := by
  simp [refMapShared, recvProbeAckState, recvProbeAckShared, hused]; rfl

/-- recvGrantAck general form: mem is determined by dirty owners in post-state. -/
theorem refMapShared_mem_recvGrantAck {n : Nat}
    {s : SymState HomeState NodeState n} {i : Fin n} :
    (refMapShared n (recvGrantAckState s i)).mem =
      if h : ∃ j : Fin n, ((recvGrantAckState s i).locals j).line.dirty = true then
        ((recvGrantAckState s i).locals (Classical.choose h)).line.data
      else
        match findDirtyReleaseVal n (recvGrantAckState s i) with
        | some v => v
        | none => s.shared.mem := by
  simp [refMapShared, recvGrantAckState, recvGrantAckShared]

theorem refMapShared_mem_recvGrantAck_clean {n : Nat}
    {s : SymState HomeState NodeState n} {i : Fin n}
    (hnoDirtyPost : ¬∃ j : Fin n, ((recvGrantAckState s i).locals j).line.dirty = true)
    (hnoRelPost : findDirtyReleaseVal n (recvGrantAckState s i) = none) :
    (refMapShared n (recvGrantAckState s i)).mem = s.shared.mem := by
  rw [refMapShared_mem_recvGrantAck]
  simp only [dif_neg hnoDirtyPost, hnoRelPost]

/-- recvAcquire under noDirtyInv: new mem = old mem = s.shared.mem. -/
theorem refMapShared_mem_recvAcquire_noDirty {n : Nat}
    {s : SymState HomeState NodeState n} {i : Fin n}
    {kind : ReqKind} {grow : GrowParam} {source : SourceId}
    (hnoDirty : noDirtyInv n s)
    (htxn : s.shared.currentTxn = none)
    (hrel : s.shared.pendingReleaseAck = none)
    (hallC : ∀ j : Fin n, (s.locals j).chanC = none) :
    (refMapShared n (recvAcquireState s i kind grow source)).mem =
      (refMapShared n s).mem := by
  -- New state has txn, usedDirtySource = false (since noDirtyInv → no dirty other)
  have hdo : dirtyOwnerOpt s i = none := by
    unfold dirtyOwnerOpt
    simp [show ¬∃ j : Fin n, j ≠ i ∧ (s.locals j).line.dirty = true from
      fun ⟨j, _, hd⟩ => absurd hd (by simp [hnoDirty j])]
  have hud : (plannedTxn s i kind grow source).usedDirtySource = false := by
    simp [plannedTxn, plannedUsedDirtySource, hdo]
  simp [refMapShared, recvAcquireState, recvAcquireShared, hud, htxn, hrel]
  -- Both sides reduce to s.shared.mem (no dirty owner under noDirtyInv)
  have hnd : ¬∃ j : Fin n, (s.locals j).line.dirty = true := by
    intro ⟨j, hd⟩; exact absurd hd (by simp [hnoDirty j])
  simp [hnd, findDirtyReleaseVal_none_of_all_chanC_none' s hallC]

/-- Local-line abstraction during an active acquire wave. Before grant delivery,
    lines are hidden behind the transaction snapshot; after grant delivery, the
    requester is synthesized from the grant metadata even if the concrete D
    message is still pending. -/
def refMapLine (s : SymState HomeState NodeState n) (i : Fin n) : CacheLine :=
  match s.shared.currentTxn with
  | none => (s.locals i).line
  | some tx =>
      if tx.phase = .grantPendingAck then
        if _hreq : tx.requester = i.1 then
          grantLine (tx.preLines i.1) tx
        else
          (s.locals i).line
      else
        tx.preLines i.1

/-- Refinement map from the explicit message model to the atomic model. -/
noncomputable def refMap (n : Nat) (s : SymState HomeState NodeState n) :
    SymState TileLink.Atomic.HomeState CacheLine n :=
  { shared := refMapShared n s
  , locals := refMapLine s }

theorem syncDir_lines_eq {n : Nat} (dir : Nat → TLPerm)
    (ls ls' : Fin n → NodeState)
    (hline : ∀ i : Fin n, (ls' i).line = (ls i).line) :
    TileLink.Atomic.syncDir dir (fun i => (ls' i).line) =
      TileLink.Atomic.syncDir dir (fun i => (ls i).line) := by
  funext k
  by_cases hk : k < n
  · let i : Fin n := ⟨k, hk⟩
    simp [TileLink.Atomic.syncDir, hk]
    exact congrArg CacheLine.perm (hline i)
  · simp [TileLink.Atomic.syncDir, hk]

theorem refMapLine_eq_preLines_of_not_grantPendingAck {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn}
    (hcur : s.shared.currentTxn = some tx) (hphase : tx.phase ≠ .grantPendingAck)
    (i : Fin n) :
    refMapLine s i = tx.preLines i.1 := by
  simp [refMapLine, hcur, hphase]

theorem queuedReleaseIdx_eq_of_chanC_releaseEq {n : Nat}
    {s s' : SymState HomeState NodeState n}
    (hC : ∀ j : Fin n, (s'.locals j).chanC = (s.locals j).chanC)
    (hflight : ∀ j : Fin n, (s'.locals j).releaseInFlight = (s.locals j).releaseInFlight) :
    queuedReleaseIdx n s' = queuedReleaseIdx n s := by
  simp [queuedReleaseIdx, hC, hflight]

theorem queuedReleaseIdx_eq_none_of_all_chanC_none {n : Nat}
    (s : SymState HomeState NodeState n)
    (hallC : ∀ j : Fin n, (s.locals j).chanC = none) :
    queuedReleaseIdx n s = none := by
  unfold queuedReleaseIdx
  have hnone : ¬∃ i : Fin n, (s.locals i).releaseInFlight = true ∧ (s.locals i).chanC ≠ none := by
    intro h
    rcases h with ⟨i, _, hC⟩
    rw [hallC i] at hC
    contradiction
  simp [hnone]

theorem findDirtyReleaseVal_none_of_all_chanC_none {n : Nat}
    (s : SymState HomeState NodeState n)
    (hallC : ∀ j : Fin n, (s.locals j).chanC = none) :
    findDirtyReleaseVal n s = none := by
  unfold findDirtyReleaseVal
  have hnone : ¬∃ i : Fin n, (s.locals i).releaseInFlight = true ∧
      ∃ msg : CMsg, (s.locals i).chanC = some msg ∧ msg.data ≠ none := by
    intro ⟨j, _, msg, hC, _⟩
    rw [hallC j] at hC; cases hC
  simp [hnone]

/-- If `shared` is identical and locals only change in fields invisible to refMap
    (i.e., line, chanC, releaseInFlight are all preserved), then `refMap` is unchanged. -/
theorem refMap_eq_of_invisible_local_change {n : Nat}
    {s : SymState HomeState NodeState n}
    {ls' : Fin n → NodeState}
    (hline : ∀ j : Fin n, (ls' j).line = (s.locals j).line)
    (hC : ∀ j : Fin n, (ls' j).chanC = (s.locals j).chanC)
    (hflight : ∀ j : Fin n, (ls' j).releaseInFlight = (s.locals j).releaseInFlight) :
    refMap n { shared := s.shared, locals := ls' } = refMap n s := by
  let s' : SymState HomeState NodeState n := ⟨s.shared, ls'⟩
  show refMap n s' = refMap n s
  have hloc : (fun j => refMapLine s' j) = (fun j => refMapLine s j) := by
    funext j
    simp only [refMapLine, show s'.shared = s.shared from rfl]
    cases htxn : s.shared.currentTxn with
    | some tx =>
      simp [htxn]
      split
      · split
        · rfl
        · exact hline j
      · rfl
    | none =>
      simp [htxn]
      exact hline j
  have hsh : refMapShared n s' = refMapShared n s := by
    unfold refMapShared
    simp only [show s'.shared = s.shared from rfl, show s'.locals = ls' from rfl]
    simp only [show ∀ j : Fin n, (ls' j).line = (s.locals j).line from hline]
    -- findDirtyReleaseVal and queuedReleaseIdx still have s'.locals references.
    -- Since s' = ⟨s.shared, ls'⟩ and hC/hflight hold, these are equal.
    -- Use simp to rewrite hC and hflight inside the remaining references.
    -- After simp only [hline], the remaining differences should only be in
    -- findDirtyReleaseVal and queuedReleaseIdx which access chanC/releaseInFlight.
    -- Since those access s'.locals which is ls', and hC/hflight equate the relevant fields,
    -- simp should close this.
    have hFDR : findDirtyReleaseVal n s' = findDirtyReleaseVal n s := by
      simp only [findDirtyReleaseVal, show s'.locals = ls' from rfl, hC, hflight]
    have hQRI : queuedReleaseIdx n s' = queuedReleaseIdx n s := by
      simp only [queuedReleaseIdx, show s'.locals = ls' from rfl, hC, hflight]
    rw [hFDR, hQRI]
  simp only [refMap]
  exact SymState.ext hsh hloc

theorem preTxnDir_updateDirAt_eq {n : Nat} (tx : ManagerTxn)
    (dir : Nat → TLPerm) (i : Fin n) (perm : TLPerm) :
    preTxnDir n tx (updateDirAt dir i perm) = preTxnDir n tx dir := by
  funext k
  by_cases hk : k < n
  · simp [preTxnDir, hk]
  · have hne : k ≠ i.1 := by
      intro h
      exact hk (h ▸ i.is_lt)
    simp [preTxnDir, hk, updateDirAt, hne]

theorem preTxnDir_tx_update_eq {n : Nat} (tx : ManagerTxn)
    (dir : Nat → TLPerm) (phase : TxnPhase) (probesRemaining : Nat → Bool) :
    preTxnDir n { tx with phase := phase, probesRemaining := probesRemaining } dir =
      preTxnDir n tx dir := by
  funext k
  by_cases hk : k < n <;> simp [preTxnDir, hk]

theorem preTxnDir_plannedTxn_eq_syncDir {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n) (kind : ReqKind) (grow : GrowParam) (source : SourceId) :
    preTxnDir n (plannedTxn s i kind grow source) s.shared.dir =
      TileLink.Atomic.syncDir s.shared.dir (fun j => (s.locals j).line) := by
  funext k
  by_cases hk : k < n
  · simp [preTxnDir, plannedTxn, TileLink.Atomic.syncDir, hk]
  · simp [preTxnDir, plannedTxn, TileLink.Atomic.syncDir, hk]

theorem grantPendingDir_updateDirAt_eq {n : Nat} (tx : ManagerTxn)
    (dir : Nat → TLPerm) (i : Fin n) (perm : TLPerm)
    (hreq : tx.requester = i.1) :
    grantPendingDir n tx (updateDirAt dir i perm) = grantPendingDir n tx dir := by
  funext k
  by_cases hk : tx.requester < n
  · by_cases hki : k = i.1
    · subst k
      simp [grantPendingDir, hk, updateDirAt, hreq]
    · simp [grantPendingDir, hk, updateDirAt, hreq, hki]
  · exfalso
    exact hk (hreq ▸ i.is_lt)

theorem txnDataInv_currentTxn {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn}
    (htxnData : txnDataInv n s) (hcur : s.shared.currentTxn = some tx) :
    (tx.usedDirtySource = false → tx.transferVal = s.shared.mem) ∧
    (tx.usedDirtySource = true → ∃ k, k < n ∧ (tx.preLines k).dirty = true ∧
      tx.transferVal = (tx.preLines k).data) := by
  simp [txnDataInv, hcur] at htxnData
  exact ⟨htxnData.1, htxnData.2.1⟩

theorem txnCoreInv_grantReady_allFalse {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn}
    (hfull : fullInv n s) (hcur : s.shared.currentTxn = some tx) (hphase : tx.phase = .grantReady) :
    ∀ j : Fin n, tx.probesRemaining j.1 = false := by
  rcases hfull with ⟨⟨_, _, _, htxnCore⟩, _, _⟩
  rcases (by simpa [txnCoreInv, hcur] using htxnCore :
      tx.requester < n ∧
      (tx.phase = .probing ∨ tx.phase = .grantReady ∨ tx.phase = .grantPendingAck) ∧
      tx.resultPerm = tx.grow.result ∧
      (tx.grantHasData = false → tx.resultPerm = .T) ∧
      tx.probesNeeded tx.requester = false ∧
      (∀ k : Nat, tx.probesRemaining k = true → tx.probesNeeded k = true) ∧
      (tx.phase = .grantReady → ∀ j : Fin n, tx.probesRemaining j.1 = false) ∧
      (tx.phase = .grantPendingAck → ∀ j : Fin n, tx.probesRemaining j.1 = false))
    with ⟨_, _, _, _, _, _, hready, _⟩
  exact hready hphase

theorem chanC_none_of_phase_ne_probing {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn}
    (hfull : fullInv n s) (hcur : s.shared.currentTxn = some tx)
    (hphase : tx.phase ≠ .probing) :
    ∀ j : Fin n, (s.locals j).chanC = none := by
  rcases hfull with ⟨_, hchan, _⟩
  rcases hchan with ⟨_, _, hchanC, _, _⟩
  intro j
  specialize hchanC j
  cases hC : (s.locals j).chanC with
  | none => rfl
  | some msg =>
      rw [hC] at hchanC
      rcases hchanC with ⟨tx', hcur', hprobe, _, _, _, _⟩ | ⟨_, htxnNone, _, _, _, _, _⟩
      · rw [hcur] at hcur'
        cases hcur'
        exact False.elim (hphase hprobe)
      · rw [hcur] at htxnNone
        cases htxnNone

theorem txnPlanInv_acquireBlock_branch {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn}
    (hplan : txnPlanInv n s) (hcur : s.shared.currentTxn = some tx)
    (hkind : tx.kind = .acquireBlock) (hperm : tx.resultPerm = .B) :
    snapshotHasCachedOther n tx ∧ tx.probesNeeded = snapshotWritableProbeMask n tx := by
  rcases (by simpa [txnPlanInv, hcur, hkind] using hplan :
      tx.requester < n ∧
      tx.grantHasData = decide (tx.kind = .acquireBlock) ∧
      ((tx.resultPerm = .B →
          snapshotHasCachedOther n tx ∧ tx.probesNeeded = snapshotWritableProbeMask n tx) ∧
        (tx.resultPerm = .T →
          snapshotAllOthersInvalid n tx ∧ tx.probesNeeded = TileLink.Atomic.noProbeMask)))
    with ⟨_, _, hbranch, _⟩
  exact hbranch hperm

theorem txnPlanInv_grantHasData {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn}
    (hplan : txnPlanInv n s) (hcur : s.shared.currentTxn = some tx) :
    tx.grantHasData = decide (tx.kind = .acquireBlock) := by
  rcases (by simpa [txnPlanInv, hcur] using hplan :
      tx.requester < n ∧
      tx.grantHasData = decide (tx.kind = .acquireBlock) ∧
      match tx.kind with
      | .acquireBlock =>
          (tx.resultPerm = .B →
            snapshotHasCachedOther n tx ∧ tx.probesNeeded = snapshotWritableProbeMask n tx) ∧
          (tx.resultPerm = .T →
            snapshotAllOthersInvalid n tx ∧ tx.probesNeeded = TileLink.Atomic.noProbeMask)
      | .acquirePerm =>
          tx.resultPerm = .T ∧
          tx.probesNeeded = snapshotCachedProbeMask n tx ∧
          (tx.preLines tx.requester).perm ≠ .T) with ⟨_, hgrant, _⟩
  exact hgrant

theorem txnPlanInv_acquireBlock_tip {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn}
    (hplan : txnPlanInv n s) (hcur : s.shared.currentTxn = some tx)
    (hkind : tx.kind = .acquireBlock) (hperm : tx.resultPerm = .T) :
    snapshotAllOthersInvalid n tx ∧ tx.probesNeeded = TileLink.Atomic.noProbeMask := by
  rcases (by simpa [txnPlanInv, hcur, hkind] using hplan :
      tx.requester < n ∧
      tx.grantHasData = decide (tx.kind = .acquireBlock) ∧
      ((tx.resultPerm = .B →
          snapshotHasCachedOther n tx ∧ tx.probesNeeded = snapshotWritableProbeMask n tx) ∧
        (tx.resultPerm = .T →
          snapshotAllOthersInvalid n tx ∧ tx.probesNeeded = TileLink.Atomic.noProbeMask)))
    with ⟨_, _, _, htip⟩
  exact htip hperm

theorem txnPlanInv_acquirePerm {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn}
    (hplan : txnPlanInv n s) (hcur : s.shared.currentTxn = some tx)
    (hkind : tx.kind = .acquirePerm) :
    tx.resultPerm = .T ∧
      tx.probesNeeded = snapshotCachedProbeMask n tx ∧
      (tx.preLines tx.requester).perm ≠ .T := by
  rcases (by simpa [txnPlanInv, hcur, hkind] using hplan :
      tx.requester < n ∧
        tx.grantHasData = false ∧
        tx.resultPerm = .T ∧
        tx.probesNeeded = snapshotCachedProbeMask n tx ∧
        (tx.preLines tx.requester).perm ≠ .T)
    with ⟨_, _, hperm, hmask, hnotT⟩
  exact ⟨hperm, hmask, hnotT⟩

end TileLink.Messages
