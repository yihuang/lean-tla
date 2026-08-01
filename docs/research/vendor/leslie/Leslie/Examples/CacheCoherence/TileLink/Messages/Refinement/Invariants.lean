import Leslie.Examples.CacheCoherence.TileLink.Messages.Theorem
import Leslie.Examples.CacheCoherence.TileLink.Atomic.Model

namespace TileLink.Messages

open TLA TileLink SymShared Classical

def noDirtyInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ i : Fin n, (s.locals i).line.dirty = false

def cleanDataInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ i : Fin n, (s.locals i).line.valid = true →
    (s.locals i).line.data = s.shared.mem

/-- At most one dirty line; if one exists, all others have perm = .N. -/
def dirtyExclusiveInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ i j : Fin n, i ≠ j → (s.locals i).line.dirty = true → (s.locals j).line.perm = .N

/-- Clean valid lines agree with home memory when no transaction is active
    and the node doesn't have a release in flight.
    During transactions, data coherence is tracked by txnDataInv + txnLineInv.
    During release-in-flight, the data may differ from mem until writeback. -/
def dataCoherenceInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  s.shared.currentTxn = none →
    ∀ i : Fin n, (s.locals i).releaseInFlight = false →
      (s.locals i).line.perm ≠ .N →
        (s.locals i).line.dirty = false →
          (s.locals i).line.data = s.shared.mem

def txnDataInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  match s.shared.currentTxn with
  | none => True
  | some tx =>
      (tx.usedDirtySource = false → tx.transferVal = s.shared.mem) ∧
      (tx.usedDirtySource = true → ∃ k, k < n ∧ (tx.preLines k).dirty = true ∧
        tx.transferVal = (tx.preLines k).data) ∧
      ((tx.phase = .grantReady ∨ tx.phase = .grantPendingAck) →
        tx.transferVal = s.shared.mem)

def preLinesCleanInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  match s.shared.currentTxn with
  | none => True
  | some tx => ∀ k : Nat, k < n →
      (tx.preLines k).perm ≠ .N →
        (tx.preLines k).dirty = false → (tx.preLines k).data = s.shared.mem

def preLinesNoDirtyInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  match s.shared.currentTxn with
  | none => True
  | some tx => ∀ k1 k2 : Nat, k1 < n → k2 < n → k1 ≠ k2 →
      (tx.preLines k1).dirty = true → (tx.preLines k2).perm = .N

def snapshotHasCachedOther (n : Nat) (tx : ManagerTxn) : Prop :=
  ∃ j : Fin n, j.1 ≠ tx.requester ∧ (tx.preLines j.1).perm ≠ .N

def snapshotAllOthersInvalid (n : Nat) (tx : ManagerTxn) : Prop :=
  ∀ j : Fin n, j.1 ≠ tx.requester → (tx.preLines j.1).perm = .N

def snapshotWritableProbeMask (n : Nat) (tx : ManagerTxn) : Nat → Bool :=
  fun k =>
    if hk : k < n then
      if k = tx.requester then false else decide ((tx.preLines k).perm = .T)
    else
      false

def snapshotCachedProbeMask (n : Nat) (tx : ManagerTxn) : Nat → Bool :=
  fun k =>
    if hk : k < n then
      if k = tx.requester then false else decide ((tx.preLines k).perm ≠ .N)
    else
      false

def txnPlanInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  match s.shared.currentTxn with
  | none => True
  | some tx =>
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
          (tx.preLines tx.requester).perm ≠ .T

/-- When no transaction is active and no release is in flight at node i,
    C-channel messages at node i carry no data. During transactions, probeAcks
    can carry dirty data. During release-in-flight, release msgs can carry data. -/
def cleanChanCInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  s.shared.currentTxn = none →
    ∀ i : Fin n, (s.locals i).releaseInFlight = false →
      ∀ msg : CMsg, (s.locals i).chanC = some msg → msg.data = none

/-- At most one release in flight when no transaction is active, and no release
    in chanC when pendingReleaseAck is set. -/
def releaseUniqueInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  s.shared.currentTxn = none →
    (s.shared.pendingReleaseAck ≠ none → ∀ j : Fin n, (s.locals j).chanC = none) ∧
    (∀ i j : Fin n, i ≠ j → (s.locals i).chanC ≠ none → (s.locals j).chanC = none)

/-- Single-writer / multiple-reader: at most one .T permission; if .T exists, all
    others have .N. This is the message-level analogue of the atomic model's `swmr`. -/
def permSwmrInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ i j : Fin n, i ≠ j → (s.locals i).line.perm = .T → (s.locals j).line.perm = .N

/-- When a dirty release is in flight (a node has releaseInFlight with chanC carrying data)
    and no transaction is active, all OTHER nodes have perm = .N.
    This captures the fact that at sendReleaseData time, the sender was the unique dirty owner
    (.T permission), so all others had .N. Since no transaction occurs between then and now,
    their permissions remain .N. -/
def dirtyReleaseExclusiveInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  s.shared.currentTxn = none →
    ∀ i : Fin n, (s.locals i).releaseInFlight = true →
      (∃ msg : CMsg, (s.locals i).chanC = some msg ∧ msg.data ≠ none) →
        ∀ j : Fin n, j ≠ i → (s.locals j).line.perm = .N

structure RefinementInv (n : Nat) (s : SymState HomeState NodeState n) : Prop where
  full : fullInv n s
  dirtyEx : dirtyExclusiveInv n s
  swmr : permSwmrInv n s
  txnData : txnDataInv n s
  cleanC : cleanChanCInv n s
  relUniq : releaseUniqueInv n s
  dirtyRelEx : dirtyReleaseExclusiveInv n s

abbrev refinementInv := @RefinementInv

/-- When usedDirtySource = false, no non-requester preLines is dirty. -/
def usedDirtySourceInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ tx, s.shared.currentTxn = some tx → tx.usedDirtySource = false →
    ∀ k, k < n → k ≠ tx.requester → (tx.preLines k).dirty = false

theorem init_usedDirtySourceInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s →
      usedDirtySourceInv n s := by
  intro s ⟨⟨_, _, htxn, _, _, _⟩, _⟩
  intro tx hcur; rw [htxn] at hcur; cases hcur

/-- When usedDirtySource = true, there exists a dirty non-requester preLines
    entry, and transferVal holds its data. -/
def dirtyOwnerExistsInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ tx, s.shared.currentTxn = some tx → tx.usedDirtySource = true →
    ∃ k, k < n ∧ k ≠ tx.requester ∧ (tx.preLines k).dirty = true ∧
      tx.transferVal = (tx.preLines k).data

theorem init_dirtyOwnerExistsInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s →
      dirtyOwnerExistsInv n s := by
  intro s ⟨⟨_, _, htxn, _, _, _⟩, _⟩
  intro tx hcur; rw [htxn] at hcur; cases hcur

/-- For acquireBlock, the requester's snapshot permission is .N.
    This is set at acquire time (precondition perm = .N) and preLines are immutable. -/
def preLinesReqPermInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ tx, s.shared.currentTxn = some tx → tx.kind = .acquireBlock →
    (tx.preLines tx.requester).perm = .N

theorem init_preLinesReqPermInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s →
      preLinesReqPermInv n s := by
  intro s ⟨⟨_, _, htxn, _, _, _⟩, _⟩
  intro tx hcur; rw [htxn] at hcur; cases hcur

/-- Snapshot lines satisfy WellFormed. This holds because preLines are set to
    current lines at transaction start (which satisfy lineWFInv) and never change. -/
def preLinesWFInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  match s.shared.currentTxn with
  | none => True
  | some tx => ∀ k : Nat, k < n → (tx.preLines k).WellFormed

theorem init_preLinesWFInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s →
      preLinesWFInv n s := by
  intro s ⟨⟨_, _, htxn, _, _, _⟩, _⟩
  simp [preLinesWFInv, htxn]

/-- When usedDirtySource is true and all dirty preLines have had their
    probeAck processed (probesRemaining = false), then transferVal = mem.
    This captures the fact that when a dirty probeAck is processed, both
    transferVal and mem are updated to the same value. -/
def txnTransferMemInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  match s.shared.currentTxn with
  | none => True
  | some tx =>
      tx.usedDirtySource = true →
        (∀ k : Nat, k < n → (tx.preLines k).dirty = true → tx.probesRemaining k = false) →
          tx.transferVal = s.shared.mem

theorem init_txnTransferMemInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s →
      txnTransferMemInv n s := by
  intro s ⟨⟨_, _, htxn, _, _, _⟩, _⟩
  simp [txnTransferMemInv, htxn]

/-- During a dirty release, the chanC message data matches the node's current line data.
    Set at sendReleaseData (releasedLine preserves data), stable until recvRelease clears chanC. -/
def releaseDataChanCInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ i : Fin n, (s.locals i).releaseInFlight = true →
    ∀ msg : CMsg, (s.locals i).chanC = some msg →
      msg.data ≠ none → msg.data = some (s.locals i).line.data

theorem init_releaseDataChanCInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s →
      releaseDataChanCInv n s := by
  intro s ⟨_, hlocals⟩ i hflight
  have ⟨_, _, _, _, _, _, _, hrel, _⟩ := hlocals i
  simp_all

/-- During a transaction (currentTxn ≠ none), no node has releaseInFlight = true.
    True because recvAcquire requires all releaseInFlight = false and sendRelease
    requires currentTxn = none. -/
def txnNoReleaseInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  s.shared.currentTxn ≠ none → ∀ j : Fin n, (s.locals j).releaseInFlight = false

theorem init_txnNoReleaseInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s →
      txnNoReleaseInv n s := by
  intro s ⟨⟨_, _, htxn, _, _, _⟩, _⟩
  simp [txnNoReleaseInv, htxn]

/-- During a release cycle (releaseInFlight = true), clean non-invalid lines
    match shared memory. This bridges the gap in dataCoherenceInv which guards
    on releaseInFlight = false. -/
def releaseDataInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  s.shared.currentTxn = none →
    ∀ i : Fin n, (s.locals i).releaseInFlight = true →
      (∀ msg : CMsg, (s.locals i).chanC = some msg → msg.data = none) →
        (s.locals i).line.perm ≠ .N →
          (s.locals i).line.dirty = false →
            (s.locals i).line.data = s.shared.mem

theorem init_releaseDataInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s →
      releaseDataInv n s := by
  intro s ⟨⟨_, _, htxn, _, _, _⟩, hlocals⟩
  simp [releaseDataInv, htxn]
  intro i hflight
  have ⟨_, _, _, _, _, _, _, hrel, _⟩ := hlocals i
  simp_all

structure StrongRefinementInv (n : Nat) (s : SymState HomeState NodeState n) : Prop where
  ref : RefinementInv n s
  txnLine : txnLineInv n s
  preClean : preLinesCleanInv n s
  preNoDirty : preLinesNoDirtyInv n s
  plan : txnPlanInv n s
  usedDirty : usedDirtySourceInv n s
  dirtyOwner : dirtyOwnerExistsInv n s

abbrev strongRefinementInv := @StrongRefinementInv

theorem init_noDirtyInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → noDirtyInv n s := by
  intro s hinit i
  rcases hinit with ⟨_, hlocals⟩
  rcases hlocals i with ⟨hline, _, _, _, _, _, _, _, _⟩
  rw [hline]

theorem init_cleanDataInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → cleanDataInv n s := by
  intro s hinit i hvalid
  rcases hinit with ⟨⟨hmem, _, _, _, _, _⟩, hlocals⟩
  rcases hlocals i with ⟨hline, _, _, _, _, _, _, _, _⟩
  simp [hline, hmem]

theorem plannedTxn_clean {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n)
    (hnoDirty : noDirtyInv n s) :
    plannedUsedDirtySource s i = false ∧ plannedTransferVal s i = s.shared.mem := by
  unfold plannedUsedDirtySource plannedTransferVal dirtyOwnerOpt
  have hnone : ¬∃ j : Fin n, j ≠ i ∧ (s.locals j).line.dirty = true := by
    intro h
    rcases h with ⟨j, _, hdirty⟩
    rw [hnoDirty j] at hdirty
    contradiction
  simp [hnone]

/-- The planned transaction satisfies the generalized txnDataInv. -/
theorem plannedTxn_txnDataInv {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n) (kind : ReqKind)
    (grow : GrowParam) (source : SourceId) :
    let tx := plannedTxn s i kind grow source
    (tx.usedDirtySource = false → tx.transferVal = s.shared.mem) ∧
    (tx.usedDirtySource = true → ∃ k, k < n ∧ (tx.preLines k).dirty = true ∧
      tx.transferVal = (tx.preLines k).data) := by
  unfold plannedTxn plannedUsedDirtySource plannedTransferVal dirtyOwnerOpt
  by_cases hex : ∃ j : Fin n, j ≠ i ∧ (s.locals j).line.dirty = true
  · simp only [hex, dite_true]
    constructor
    · intro h; simp at h
    · intro _
      have hj := Classical.choose_spec hex
      exact ⟨(Classical.choose hex).1, (Classical.choose hex).2, by simp [dif_pos (Classical.choose hex).2]; exact hj.2, by simp [dif_pos (Classical.choose hex).2]⟩
  · simp [hex]

/-- When there is no dirty other node, the planned transaction uses no dirty source
    and the transfer value equals memory. Weaker than `plannedTxn_clean` (uses `¬hasDirtyOther`
    instead of `noDirtyInv`). -/
theorem plannedTxn_clean_of_not_hasDirtyOther {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n)
    (hnd : ¬hasDirtyOther s i) :
    plannedUsedDirtySource s i = false ∧ plannedTransferVal s i = s.shared.mem := by
  unfold plannedUsedDirtySource plannedTransferVal dirtyOwnerOpt
  have hnone : ¬∃ j : Fin n, j ≠ i ∧ (s.locals j).line.dirty = true := hnd
  simp [hnone]

/-- `allOthersInvalid` implies `¬hasDirtyOther` since well-formed lines with perm = .N
    cannot be dirty (WellFormed: perm = .N → dirty = false). -/
theorem not_hasDirtyOther_of_allOthersInvalid {n : Nat}
    {s : SymState HomeState NodeState n} {i : Fin n}
    (hwf : lineWFInv n s)
    (hallInvalid : allOthersInvalid s i) :
    ¬hasDirtyOther s i := by
  intro ⟨j, hji, hdirty⟩
  have hpermN := hallInvalid j hji
  have ⟨_, _, hN⟩ := hwf j
  have ⟨_, hdirtyF⟩ := hN hpermN
  rw [hdirtyF] at hdirty
  contradiction

theorem init_txnDataInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → txnDataInv n s := by
  intro s hinit
  rcases hinit with ⟨⟨_, _, htxn, _, _, _⟩, _⟩
  simp [txnDataInv, htxn]

theorem init_preLinesCleanInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → preLinesCleanInv n s := by
  intro s hinit
  rcases hinit with ⟨⟨_, _, htxn, _, _, _⟩, _⟩
  simp [preLinesCleanInv, htxn]

theorem init_preLinesNoDirtyInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → preLinesNoDirtyInv n s := by
  intro s hinit
  rcases hinit with ⟨⟨_, _, htxn, _, _, _⟩, _⟩
  simp [preLinesNoDirtyInv, htxn]

theorem init_txnPlanInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → txnPlanInv n s := by
  intro s hinit
  rcases hinit with ⟨⟨_, _, htxn, _, _, _⟩, _⟩
  simp [txnPlanInv, htxn]

theorem init_cleanChanCInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → cleanChanCInv n s := by
  intro s hinit _ i _ msg hC
  rcases hinit with ⟨_, hlocals⟩
  rcases hlocals i with ⟨_, _, _, hCnone, _, _, _, _, _⟩
  rw [hCnone] at hC; cases hC

theorem init_releaseUniqueInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → releaseUniqueInv n s := by
  intro s hinit _
  rcases hinit with ⟨_, hlocals⟩
  exact ⟨fun _ j => by rcases hlocals j with ⟨_, _, _, hC, _, _, _, _, _⟩; exact hC,
    fun i _ _ hi => by rcases hlocals i with ⟨_, _, _, hC, _, _, _, _, _⟩; exact absurd hC hi⟩

theorem init_dirtyExclusiveInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → dirtyExclusiveInv n s := by
  intro s hinit i j _ hdirty
  rcases hinit with ⟨_, hlocals⟩
  rcases hlocals i with ⟨hline, _, _, _, _, _, _, _, _⟩
  rw [hline] at hdirty; cases hdirty

theorem init_dataCoherenceInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → dataCoherenceInv n s := by
  intro s hinit _ i _ _ hdirty
  rcases hinit with ⟨⟨hmem, _, _, _, _, _⟩, hlocals⟩
  rcases hlocals i with ⟨hline, _, _, _, _, _, _, _, _⟩
  simp [hline, hmem]

theorem init_permSwmrInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → permSwmrInv n s := by
  intro s hinit i j _ hperm
  rcases hinit with ⟨_, hlocals⟩
  rcases hlocals i with ⟨hline, _, _, _, _, _, _, _, _⟩
  rw [hline] at hperm; cases hperm

theorem init_dirtyReleaseExclusiveInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n,
      (tlMessages.toSpec n).init s → dirtyReleaseExclusiveInv n s := by
  intro s hinit _ i hrel _
  rcases hinit with ⟨_, hlocals⟩
  rcases hlocals i with ⟨_, _, _, _, _, _, _, _, hflight⟩
  rw [hflight] at hrel; cases hrel

theorem init_refinementInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → refinementInv n s := by
  intro s hinit
  exact ⟨init_fullInv n s hinit, init_dirtyExclusiveInv n s hinit, init_permSwmrInv n s hinit,
    init_txnDataInv n s hinit, init_cleanChanCInv n s hinit, init_releaseUniqueInv n s hinit,
    init_dirtyReleaseExclusiveInv n s hinit⟩

theorem init_strongRefinementInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → strongRefinementInv n s := by
  intro s hinit
  exact ⟨init_refinementInv n s hinit, init_txnLineInv n s hinit,
    init_preLinesCleanInv n s hinit, init_preLinesNoDirtyInv n s hinit,
    init_txnPlanInv n s hinit, init_usedDirtySourceInv n s hinit,
    init_dirtyOwnerExistsInv n s hinit⟩

theorem usedDirtySourceInv_preserved (n : Nat) (s s' : SymState HomeState NodeState n)
    (hfull : fullInv n s) (hinv : usedDirtySourceInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    usedDirtySourceInv n s' := by
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  match a with
  | .sendAcquireBlock _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      rw [hs']; simpa [usedDirtySourceInv] using hinv
  | .sendAcquirePerm _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      rw [hs']; simpa [usedDirtySourceInv] using hinv
  | .recvAcquireAtManager =>
      rcases hstep with hblk | hperm
      · rcases hblk with ⟨grow, source, _, _, _, _, _, _, _, _, _, _, hs'⟩
        rw [hs']
        intro tx' hcur' hused k hk hne
        simp only [recvAcquireState, recvAcquireShared] at hcur'
        cases hcur'
        simp only [plannedTxn] at hused hne ⊢
        simp only [dif_pos hk]
        unfold plannedUsedDirtySource dirtyOwnerOpt at hused
        by_cases hex : ∃ j : Fin n, j ≠ i ∧ (s.locals j).line.dirty = true
        · simp [hex] at hused
        · have hfin : ⟨k, hk⟩ ≠ i := by intro h; exact hne (congrArg Fin.val h)
          cases hdirty : (s.locals ⟨k, hk⟩).line.dirty
          · rfl
          · exact absurd ⟨⟨k, hk⟩, hfin, hdirty⟩ hex
      · rcases hperm with ⟨grow, source, _, _, _, _, _, _, _, _, _, hs'⟩
        rw [hs']
        intro tx' hcur' hused k hk hne
        simp only [recvAcquireState, recvAcquireShared] at hcur'
        cases hcur'
        simp only [plannedTxn] at hused hne ⊢
        simp only [dif_pos hk]
        unfold plannedUsedDirtySource dirtyOwnerOpt at hused
        by_cases hex : ∃ j : Fin n, j ≠ i ∧ (s.locals j).line.dirty = true
        · simp [hex] at hused
        · have hfin : ⟨k, hk⟩ ≠ i := by intro h; exact hne (congrArg Fin.val h)
          cases hdirty : (s.locals ⟨k, hk⟩).line.dirty
          · rfl
          · exact absurd ⟨⟨k, hk⟩, hfin, hdirty⟩ hex
  | .recvProbeAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']; simpa [usedDirtySourceInv, recvProbeState] using hinv
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [usedDirtySourceInv, hcur, recvProbeAckState, recvProbeAckShared] using hinv
  | .sendGrantToRequester =>
      rcases hstep with ⟨tx, hcur, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [usedDirtySourceInv, hcur, sendGrantState, sendGrantShared] using hinv
  | .recvGrantAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [usedDirtySourceInv, recvGrantState, recvGrantShared] using hinv
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨tx, msg, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [usedDirtySourceInv, recvGrantAckState, recvGrantAckShared]
  | .sendRelease _ =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, htail⟩
      rcases htail with ⟨_, hs'⟩
      rw [hs']; simp [usedDirtySourceInv, hcur, sendReleaseState]
  | .sendReleaseData _ =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']; simp [usedDirtySourceInv, hcur, sendReleaseState]
  | .recvReleaseAtManager =>
      rcases hstep with ⟨msg, param, hcur, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']; simp [usedDirtySourceInv, hcur, recvReleaseState, recvReleaseShared]
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨msg, hcur, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [usedDirtySourceInv, recvReleaseAckState, recvReleaseAckShared] using hinv
  | .store v =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']; simp [usedDirtySourceInv, hcur]
  | .read =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩
      exact hinv
  | .uncachedGet source =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, rfl⟩
      simp [usedDirtySourceInv, hcur]
  | .uncachedPut source v =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, rfl⟩
      simp [usedDirtySourceInv, hcur]
  | .recvUncachedAtManager =>
      rcases hstep with ⟨hcur, _, _, _, _, _, rfl⟩
      simp [usedDirtySourceInv, hcur]
  | .recvAccessAckAtMaster =>
      rcases hstep with ⟨_, _, _, rfl⟩
      exact hinv

theorem dirtyOwnerExistsInv_preserved (n : Nat) (s s' : SymState HomeState NodeState n)
    (hfull : fullInv n s) (hinv : dirtyOwnerExistsInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    dirtyOwnerExistsInv n s' := by
  -- Same structure as usedDirtySourceInv_preserved: preLines/usedDirtySource/transferVal frozen
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  match a with
  | .sendAcquireBlock _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      rw [hs']; simpa [dirtyOwnerExistsInv] using hinv
  | .sendAcquirePerm _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      rw [hs']; simpa [dirtyOwnerExistsInv] using hinv
  | .recvAcquireAtManager =>
      rcases hstep with hblk | hperm
      · rcases hblk with ⟨grow, source, _, _, _, _, _, _, _, _, _, _, hs'⟩
        rw [hs']
        intro tx' hcur' hused
        simp only [recvAcquireState, recvAcquireShared] at hcur'
        cases hcur'
        simp only [plannedTxn] at hused ⊢
        -- usedDirtySource = true means dirtyOwnerOpt returned some j
        unfold plannedUsedDirtySource at hused
        unfold dirtyOwnerOpt at hused
        by_cases hex : ∃ j : Fin n, j ≠ i ∧ (s.locals j).line.dirty = true
        · -- dirtyOwnerOpt = some (choose hex)
          simp [hex] at hused
          let j := Classical.choose hex
          have hj := Classical.choose_spec hex
          refine ⟨j.1, j.isLt, ?_, ?_, ?_⟩
          · intro h; exact hj.1 (Fin.ext h)
          · simp [dif_pos j.isLt]; exact hj.2
          · simp [plannedTransferVal, dirtyOwnerOpt, hex, dif_pos j.isLt]; rfl
        · simp [hex] at hused
      · rcases hperm with ⟨grow, source, _, _, _, _, _, _, _, _, _, hs'⟩
        rw [hs']
        intro tx' hcur' hused
        simp only [recvAcquireState, recvAcquireShared] at hcur'
        cases hcur'
        simp only [plannedTxn] at hused ⊢
        unfold plannedUsedDirtySource at hused
        unfold dirtyOwnerOpt at hused
        by_cases hex : ∃ j : Fin n, j ≠ i ∧ (s.locals j).line.dirty = true
        · simp [hex] at hused
          let j := Classical.choose hex
          have hj := Classical.choose_spec hex
          refine ⟨j.1, j.isLt, ?_, ?_, ?_⟩
          · intro h; exact hj.1 (Fin.ext h)
          · simp [dif_pos j.isLt]; exact hj.2
          · simp [plannedTransferVal, dirtyOwnerOpt, hex, dif_pos j.isLt]; rfl
        · simp [hex] at hused
  | .recvProbeAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']; simpa [dirtyOwnerExistsInv, recvProbeState] using hinv
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [dirtyOwnerExistsInv, hcur, recvProbeAckState, recvProbeAckShared] using hinv
  | .sendGrantToRequester =>
      rcases hstep with ⟨tx, hcur, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [dirtyOwnerExistsInv, hcur, sendGrantState, sendGrantShared] using hinv
  | .recvGrantAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [dirtyOwnerExistsInv, recvGrantState, recvGrantShared] using hinv
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨tx, msg, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [dirtyOwnerExistsInv, recvGrantAckState, recvGrantAckShared]
  | .sendRelease _ =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, htail⟩
      rcases htail with ⟨_, hs'⟩
      rw [hs']; simp [dirtyOwnerExistsInv, hcur, sendReleaseState]
  | .sendReleaseData _ =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']; simp [dirtyOwnerExistsInv, hcur, sendReleaseState]
  | .recvReleaseAtManager =>
      rcases hstep with ⟨msg, param, hcur, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']; simp [dirtyOwnerExistsInv, hcur, recvReleaseState, recvReleaseShared]
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨msg, hcur, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [dirtyOwnerExistsInv, recvReleaseAckState, recvReleaseAckShared] using hinv
  | .store v =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']; simp [dirtyOwnerExistsInv, hcur]
  | .read =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩
      exact hinv
  | .uncachedGet source =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, rfl⟩
      simp [dirtyOwnerExistsInv, hcur]
  | .uncachedPut source v =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, rfl⟩
      simp [dirtyOwnerExistsInv, hcur]
  | .recvUncachedAtManager =>
      rcases hstep with ⟨hcur, _, _, _, _, _, rfl⟩
      simp [dirtyOwnerExistsInv, hcur]
  | .recvAccessAckAtMaster =>
      rcases hstep with ⟨_, _, _, rfl⟩
      exact hinv

end TileLink.Messages
