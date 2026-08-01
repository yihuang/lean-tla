import Leslie.Examples.CacheCoherence.TileLink.Messages.ModelDefs
import Leslie.Gadgets.FrameLemmaGen

open TLA SymShared Classical

/-! ## TileLink TL-C Message-Level Helpers

    Helper functions, line transformers, message constructors, state transformers,
    and their simp/well-formedness lemmas.

    Pure type definitions live in `ModelDefs.lean`.
    Action predicates and the `tlMessages` spec live in `Model.lean`.
-/

namespace TileLink.Messages

open TileLink

def mkAcquireBlockMsg (grow : GrowParam) (source : SourceId) : AMsg :=
  { opcode := .acquireBlock, param := grow, source := source }

def mkAcquirePermMsg (grow : GrowParam) (source : SourceId) : AMsg :=
  { opcode := .acquirePerm, param := grow, source := source }

def probeOpcodeOfKind : ReqKind → BOpcode
  | .acquireBlock => .probeBlock
  | .acquirePerm => .probePerm

def probeCapOfResult : TLPerm → CapParam
  | .N => .toN
  | .B => .toB
  | .T => .toN

def probeAckOpcodeOfLine (line : CacheLine) : COpcode :=
  if line.dirty then .probeAckData else .probeAck

def probeAckDataOfLine (line : CacheLine) : Option Val :=
  if line.dirty then some line.data else none

def invalidatedLine (line : CacheLine) : CacheLine :=
  { line with perm := .N, valid := false, dirty := false }

def branchAfterProbe (line : CacheLine) : CacheLine :=
  { perm := .B, valid := true, dirty := false, data := line.data }

def tipAfterProbe (line : CacheLine) : CacheLine :=
  { perm := .T, valid := true, dirty := false, data := line.data }

@[simp] theorem invalidatedLine_perm (line : CacheLine) :
    (invalidatedLine line).perm = .N := rfl

@[simp] theorem invalidatedLine_wf (line : CacheLine) :
    (invalidatedLine line).WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · intro hdirty
    simp [invalidatedLine] at hdirty
  · intro hperm
    simp [invalidatedLine] at hperm
  · intro hperm
    simp [invalidatedLine] at hperm ⊢

@[simp] theorem branchAfterProbe_wf (line : CacheLine) :
    (branchAfterProbe line).WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · intro hdirty
    simp [branchAfterProbe] at hdirty
  · intro hperm
    simp [branchAfterProbe] at hperm ⊢
  · intro hperm
    simp [branchAfterProbe] at hperm

@[simp] theorem tipAfterProbe_wf (line : CacheLine) :
    (tipAfterProbe line).WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · intro hdirty
    simp [tipAfterProbe] at hdirty
  · intro hperm
    simp [tipAfterProbe] at hperm
  · intro hperm
    simp [tipAfterProbe] at hperm

def probedLine (line : CacheLine) (cap : CapParam) : CacheLine :=
  match cap with
  | .toN => invalidatedLine line
  | .toB => branchAfterProbe line
  | .toT => tipAfterProbe line

@[simp] theorem probedLine_wf (line : CacheLine) (cap : CapParam) :
    (probedLine line cap).WellFormed := by
  cases cap <;> simp [probedLine]

def clearProbeIdx (probeMask : Nat → Bool) (idx : Nat) : Nat → Bool :=
  fun k => if k = idx then false else probeMask k

def updateDirAt {n : Nat} (dir : Nat → TLPerm) (i : Fin n) (perm : TLPerm) : Nat → TLPerm :=
  fun k => if k = i.1 then perm else dir k

@[simp] theorem updateDirAt_self {n : Nat} (dir : Nat → TLPerm) (i : Fin n) (perm : TLPerm) :
    updateDirAt dir i perm i.1 = perm := by
  simp [updateDirAt]

@[simp] theorem updateDirAt_ne {n : Nat} (dir : Nat → TLPerm) (i : Fin n) (perm : TLPerm)
    {k : Nat} (h : k ≠ i.1) :
    updateDirAt dir i perm k = dir k := by
  simp [updateDirAt, h]

def probeAckPhase {n : Nat} (probeMask : Nat → Bool) : TxnPhase :=
  if _ : ∀ j : Fin n, probeMask j.1 = false then .grantReady else .probing

def probeAckMsg (i : Fin n) (line : CacheLine) : CMsg :=
  { opcode := probeAckOpcodeOfLine line
  , source := i.1
  , data := probeAckDataOfLine line }

def grantOpcodeOfTxn (tx : ManagerTxn) : DOpcode :=
  if tx.grantHasData then .grantData else .grant

def grantDataOfTxn (tx : ManagerTxn) : Option Val :=
  if tx.grantHasData then some tx.transferVal else none

def grantMsgOfTxn (tx : ManagerTxn) : DMsg :=
  { opcode := grantOpcodeOfTxn tx
  , sink := tx.sink
  , source := tx.source
  , param := some (probeCapOfResult tx.resultPerm)
  , data := grantDataOfTxn tx }

def grantLine (line : CacheLine) (tx : ManagerTxn) : CacheLine :=
  if tx.grantHasData then
    match tx.resultPerm with
    | .N => invalidatedLine line
    | .B => { perm := .B, valid := true, dirty := false, data := tx.transferVal }
    | .T => { perm := .T, valid := true, dirty := false, data := tx.transferVal }
  else
    { line with perm := .T, valid := false, dirty := false }

def releasedLine (line : CacheLine) (perm : TLPerm) : CacheLine :=
  match perm with
  | .N => invalidatedLine line
  | .B => branchAfterProbe line
  | .T => tipAfterProbe line

def releaseOpcode (withData : Bool) : COpcode :=
  if withData then .releaseData else .release

def releaseDataPayload (withData : Bool) (line : CacheLine) : Option Val :=
  if withData then some line.data else none

def releaseMsg (source : SourceId) (param : PruneReportParam)
    (withData : Bool) (line : CacheLine) : CMsg :=
  { opcode := releaseOpcode withData
  , param := some param
  , source := source
  , data := releaseDataPayload withData line }

def releaseAckMsg (source : SourceId) : DMsg :=
  { opcode := .releaseAck, sink := 0, source := source }

def releaseMsgWellFormed (msg : CMsg) : Prop :=
  (msg.opcode = .release ∧ ∃ param : PruneReportParam, msg.param = some param ∧ msg.data = none) ∨
  (msg.opcode = .releaseData ∧ ∃ param : PruneReportParam, ∃ v : Val,
    msg.param = some param ∧ msg.data = some v)

def probeAckMsgWellFormed (msg : CMsg) : Prop :=
  (msg.opcode = .probeAck ∧ msg.data = none) ∨
  (msg.opcode = .probeAckData ∧ ∃ v : Val, msg.data = some v)

theorem probeAckMsg_wf {n : Nat} (i : Fin n) (line : CacheLine) :
    probeAckMsgWellFormed (probeAckMsg i line) := by
  by_cases hdirty : line.dirty = true
  · right
    refine ⟨?_, ?_⟩
    · simp [probeAckMsg, probeAckOpcodeOfLine, hdirty]
    · exact ⟨line.data, by simp [probeAckMsg, probeAckDataOfLine, hdirty]⟩
  · left
    refine ⟨?_, ?_⟩
    · simp [probeAckMsg, probeAckOpcodeOfLine, hdirty]
    · simp [probeAckMsg, probeAckDataOfLine, hdirty]

@[simp] theorem grantLine_wf (line : CacheLine) (tx : ManagerTxn) :
    (grantLine line tx).WellFormed := by
  by_cases hdata : tx.grantHasData
  · cases hperm : tx.resultPerm
    · simp [grantLine, hdata, hperm, invalidatedLine_wf]
    · refine ⟨?_, ?_, ?_⟩ <;> simp [grantLine, hdata, hperm]
    · refine ⟨?_, ?_, ?_⟩ <;> simp [grantLine, hdata, hperm]
  · refine ⟨?_, ?_, ?_⟩ <;> simp [grantLine, hdata]

theorem grantLine_perm_eq_result (line : CacheLine) (tx : ManagerTxn)
    (hnoData : tx.grantHasData = false → tx.resultPerm = .T) :
    (grantLine line tx).perm = tx.resultPerm := by
  cases hdata : tx.grantHasData
  · simp [grantLine, hdata, hnoData hdata]
  · cases hperm : tx.resultPerm <;> simp [grantLine, hdata, hperm, invalidatedLine_perm]

@[simp] theorem releasedLine_perm (line : CacheLine) (perm : TLPerm) :
    (releasedLine line perm).perm = perm := by
  cases perm <;> rfl

@[simp] theorem releasedLine_wf (line : CacheLine) (perm : TLPerm) :
    (releasedLine line perm).WellFormed := by
  cases perm <;> simp [releasedLine]

theorem releaseMsg_of_clean (source : SourceId) (param : PruneReportParam) (line : CacheLine) :
    releaseMsgWellFormed (releaseMsg source param false line) := by
  left
  refine ⟨by simp [releaseMsg, releaseOpcode], ?_⟩
  exact ⟨param, by simp [releaseMsg, releaseDataPayload]⟩

theorem releaseMsg_of_dirty (source : SourceId) (param : PruneReportParam) (line : CacheLine) :
    releaseMsgWellFormed (releaseMsg source param true line) := by
  right
  refine ⟨by simp [releaseMsg, releaseOpcode], ?_⟩
  exact ⟨param, line.data, by simp [releaseMsg, releaseDataPayload]⟩

/-! ### State predicates and probe masks -/

def hasDirtyOther {n : Nat} (s : SymState HomeState NodeState n) (i : Fin n) : Prop :=
  ∃ j : Fin n, j ≠ i ∧ (s.locals j).line.dirty = true

def hasCachedOther {n : Nat} (s : SymState HomeState NodeState n) (i : Fin n) : Prop :=
  ∃ j : Fin n, j ≠ i ∧ (s.locals j).line.perm ≠ .N

def allOthersInvalid {n : Nat} (s : SymState HomeState NodeState n) (i : Fin n) : Prop :=
  ∀ j : Fin n, j ≠ i → (s.locals j).line.perm = .N

noncomputable def dirtyOwnerOpt {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n) : Option (Fin n) :=
  if h : ∃ j : Fin n, j ≠ i ∧ (s.locals j).line.dirty = true then
    some (Classical.choose h)
  else
    none

def noProbeMask : Nat → Bool :=
  fun _ => false

def writableProbeMask {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n) : Nat → Bool :=
  fun k =>
    if hk : k < n then
      let p : Fin n := ⟨k, hk⟩
      if p = i then false else decide ((s.locals p).line.perm = .T)
    else
      false

def cachedProbeMask {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n) : Nat → Bool :=
  fun k =>
    if hk : k < n then
      let p : Fin n := ⟨k, hk⟩
      if p = i then false else decide ((s.locals p).line.perm ≠ .N)
    else
      false

def probeMaskForResult {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n) (perm : TLPerm) : Nat → Bool :=
  match perm with
  | .N => noProbeMask
  | .B => writableProbeMask s i
  | .T => cachedProbeMask s i

def allTargetBsEmpty {n : Nat}
    (s : SymState HomeState NodeState n) (probeMask : Nat → Bool) : Prop :=
  ∀ j : Fin n, probeMask j.1 = true → (s.locals j).chanB = none

noncomputable def plannedTransferVal {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n) : Val :=
  match dirtyOwnerOpt s i with
  | some j => (s.locals j).line.data
  | none => s.shared.mem

noncomputable def plannedUsedDirtySource {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n) : Bool :=
  match dirtyOwnerOpt s i with
  | some _ => true
  | none => false

noncomputable def plannedTxn {n : Nat}
    (s : SymState HomeState NodeState n)
    (requester : Fin n)
    (kind : ReqKind)
    (grow : GrowParam)
    (source : SourceId) : ManagerTxn :=
  let resultPerm := grow.result
  let probeMask := probeMaskForResult s requester resultPerm
  let preLines : Nat → CacheLine :=
    fun k =>
      if hk : k < n then
        (s.locals ⟨k, hk⟩).line
      else
        ({ perm := .N, valid := false, dirty := false, data := 0 } : CacheLine)
  { requester := requester.1
  , source := source
  , sink := s.shared.nextSink
  , kind := kind
  , grow := grow
  , phase := @probeAckPhase n probeMask
  , grantHasData := decide (kind = .acquireBlock)
  , resultPerm := resultPerm
  , transferVal := plannedTransferVal s requester
  , usedDirtySource := plannedUsedDirtySource s requester
  , probesNeeded := probeMask
  , probesRemaining := probeMask
  , preLines := preLines }

/-! ### Per-action state transformers -/

def recvProbeLocal {n : Nat} (node : NodeState) (i : Fin n) (msg : BMsg) : NodeState :=
  { node with
      line := probedLine node.line msg.param
      chanA := none
      chanB := none
      chanC := some (probeAckMsg i node.line) }

#gen_frame_lemmas recvProbeLocal

def recvProbeLocals {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n)
    (msg : BMsg) : Fin n → NodeState :=
  setFn s.locals i (recvProbeLocal (s.locals i) i msg)

def recvProbeState {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n)
    (msg : BMsg) : SymState HomeState NodeState n :=
  { shared := s.shared
  , locals := recvProbeLocals s i msg }

noncomputable def recvProbeAckShared {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n)
    (tx : ManagerTxn)
    (msg : CMsg) : HomeState :=
  let remaining := clearProbeIdx tx.probesRemaining i.1
  let phase := probeAckPhase (n := n) remaining
  let newMem := match msg.data with | some v => v | none => s.shared.mem
  { s.shared with
      mem := newMem
      dir := updateDirAt s.shared.dir i (s.locals i).line.perm
      currentTxn := some { tx with probesRemaining := remaining, phase := phase } }

def recvProbeAckLocal (node : NodeState) : NodeState :=
  { node with chanC := none }

#gen_frame_lemmas recvProbeAckLocal

def recvProbeAckLocals {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n) : Fin n → NodeState :=
  setFn s.locals i (recvProbeAckLocal (s.locals i))

noncomputable def recvProbeAckState {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n)
    (tx : ManagerTxn)
    (msg : CMsg) : SymState HomeState NodeState n :=
  { shared := recvProbeAckShared s i tx msg
  , locals := recvProbeAckLocals s i }

noncomputable def sendGrantShared {n : Nat}
    (s : SymState HomeState NodeState n)
    (tx : ManagerTxn) : HomeState :=
  { s.shared with
      currentTxn := some { tx with phase := .grantPendingAck }
      pendingGrantAck := some tx.requester }

def sendGrantLocal (node : NodeState) (tx : ManagerTxn) : NodeState :=
  { node with
      chanD := some (grantMsgOfTxn tx)
      pendingSink := some tx.sink }

#gen_frame_lemmas sendGrantLocal

def sendGrantLocals {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n)
    (tx : ManagerTxn) : Fin n → NodeState :=
  setFn s.locals i (sendGrantLocal (s.locals i) tx)

noncomputable def sendGrantState {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n)
    (tx : ManagerTxn) : SymState HomeState NodeState n :=
  { shared := sendGrantShared s tx
  , locals := sendGrantLocals s i tx }

noncomputable def recvGrantShared {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n)
    (tx : ManagerTxn) : HomeState :=
  { s.shared with dir := updateDirAt s.shared.dir i tx.resultPerm }

def recvGrantLocal
    (node : NodeState)
    (tx : ManagerTxn) : NodeState :=
  { node with
      line := grantLine node.line tx
      chanD := none
      chanE := some { sink := tx.sink }
      pendingSource := none }

#gen_frame_lemmas recvGrantLocal

def recvGrantLocals {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n)
    (tx : ManagerTxn) : Fin n → NodeState :=
  setFn s.locals i (recvGrantLocal (s.locals i) tx)

noncomputable def recvGrantState {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n)
    (tx : ManagerTxn) : SymState HomeState NodeState n :=
  { shared := recvGrantShared s i tx
  , locals := recvGrantLocals s i tx }

noncomputable def recvGrantAckShared
    (s : SymState HomeState NodeState n) : HomeState :=
  { s.shared with currentTxn := none, pendingGrantAck := none }

def recvGrantAckLocal (node : NodeState) : NodeState :=
  { node with
      chanE := none
      pendingSink := none }

#gen_frame_lemmas recvGrantAckLocal

def recvGrantAckLocals {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n) : Fin n → NodeState :=
  setFn s.locals i (recvGrantAckLocal (s.locals i))

noncomputable def recvGrantAckState {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n) : SymState HomeState NodeState n :=
  { shared := recvGrantAckShared s
  , locals := recvGrantAckLocals s i }

def sendReleaseLocal (node : NodeState) (source : SourceId)
    (param : PruneReportParam) (withData : Bool) : NodeState :=
  { node with
      line := releasedLine node.line param.result
      chanC := some (releaseMsg source param withData node.line)
      releaseInFlight := true }

#gen_frame_lemmas sendReleaseLocal

def sendReleaseLocals {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n)
    (param : PruneReportParam)
    (withData : Bool) : Fin n → NodeState :=
  setFn s.locals i (sendReleaseLocal (s.locals i) i.1 param withData)

noncomputable def sendReleaseState {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n)
    (param : PruneReportParam)
    (withData : Bool) : SymState HomeState NodeState n :=
  { shared := s.shared
  , locals := sendReleaseLocals s i param withData }

def releaseWriteback (mem : Val) (msg : CMsg) : Val :=
  match msg.data with
  | some v => v
  | none => mem

noncomputable def recvReleaseShared {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n)
    (msg : CMsg)
    (param : PruneReportParam) : HomeState :=
  { s.shared with
      mem := releaseWriteback s.shared.mem msg
      dir := updateDirAt s.shared.dir i param.result
      pendingReleaseAck := some i.1 }

def recvReleaseLocal (node : NodeState) (source : SourceId) : NodeState :=
  { node with
      chanC := none
      chanD := some (releaseAckMsg source) }

#gen_frame_lemmas recvReleaseLocal

def recvReleaseLocals {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n) : Fin n → NodeState :=
  setFn s.locals i (recvReleaseLocal (s.locals i) i.1)

noncomputable def recvReleaseState {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n)
    (msg : CMsg)
    (param : PruneReportParam) : SymState HomeState NodeState n :=
  { shared := recvReleaseShared s i msg param
  , locals := recvReleaseLocals s i }

noncomputable def recvReleaseAckShared {n : Nat}
    (s : SymState HomeState NodeState n) : HomeState :=
  { s.shared with pendingReleaseAck := none }

def recvReleaseAckLocal (node : NodeState) : NodeState :=
  { node with
      chanD := none
      releaseInFlight := false }

#gen_frame_lemmas recvReleaseAckLocal

def recvReleaseAckLocals {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n) : Fin n → NodeState :=
  setFn s.locals i (recvReleaseAckLocal (s.locals i))

noncomputable def recvReleaseAckState {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n) : SymState HomeState NodeState n :=
  { shared := recvReleaseAckShared s
  , locals := recvReleaseAckLocals s i }

def storeLocal (node : NodeState) (v : Val) : NodeState :=
  { node with line := { perm := .T, valid := true, dirty := true, data := v } }

#gen_frame_lemmas storeLocal

def scheduleProbeLocals {n : Nat}
    (s : SymState HomeState NodeState n)
    (requester : Fin n)
    (probeMask : Nat → Bool)
    (kind : ReqKind)
    (resultPerm : TLPerm)
    (source : SourceId) : Fin n → NodeState :=
  fun j =>
    let clearedA :=
      if j = requester then
        { (s.locals j) with chanA := none }
      else
        s.locals j
    if probeMask j.1 = true then
      { clearedA with
          chanB := some
            { opcode := probeOpcodeOfKind kind
            , param := probeCapOfResult resultPerm
            , source := source } }
    else
      clearedA

noncomputable def recvAcquireShared {n : Nat}
    (s : SymState HomeState NodeState n)
    (requester : Fin n)
    (kind : ReqKind)
    (grow : GrowParam)
    (source : SourceId) : HomeState :=
  { mem := s.shared.mem
  , dir := s.shared.dir
  , currentTxn := some (plannedTxn s requester kind grow source)
  , pendingGrantAck := none
  , pendingReleaseAck := none
  , nextSink := s.shared.nextSink + 1 }

noncomputable def recvAcquireLocals {n : Nat}
    (s : SymState HomeState NodeState n)
    (requester : Fin n)
    (kind : ReqKind)
    (grow : GrowParam)
    (source : SourceId) : Fin n → NodeState :=
  scheduleProbeLocals s requester (probeMaskForResult s requester grow.result) kind grow.result source

noncomputable def recvAcquireState {n : Nat}
    (s : SymState HomeState NodeState n)
    (requester : Fin n)
    (kind : ReqKind)
    (grow : GrowParam)
    (source : SourceId) : SymState HomeState NodeState n :=
  { shared := recvAcquireShared s requester kind grow source
  , locals := recvAcquireLocals s requester kind grow source }

end TileLink.Messages
