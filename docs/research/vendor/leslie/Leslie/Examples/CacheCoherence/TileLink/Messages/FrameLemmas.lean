import Leslie.Examples.CacheCoherence.TileLink.Messages.Model

namespace TileLink.Messages

open TileLink SymShared

@[simp] theorem scheduleProbeLocals_line {n : Nat}
    (s : SymState HomeState NodeState n) (requester : Fin n)
    (probeMask : Nat → Bool) (kind : ReqKind) (resultPerm : TLPerm) (source : SourceId)
    (j : Fin n) :
    (scheduleProbeLocals s requester probeMask kind resultPerm source j).line =
      (s.locals j).line := by
  by_cases hji : j = requester
  · cases hji
    by_cases hmask : probeMask requester.1 = true <;> simp [scheduleProbeLocals, hmask]
  · by_cases hmask : probeMask j.1 = true <;> simp [scheduleProbeLocals, hji, hmask]

@[simp] theorem scheduleProbeLocals_chanC {n : Nat}
    (s : SymState HomeState NodeState n) (requester : Fin n)
    (probeMask : Nat → Bool) (kind : ReqKind) (resultPerm : TLPerm) (source : SourceId)
    (j : Fin n) :
    (scheduleProbeLocals s requester probeMask kind resultPerm source j).chanC =
      (s.locals j).chanC := by
  by_cases hji : j = requester
  · cases hji
    by_cases hmask : probeMask requester.1 = true <;> simp [scheduleProbeLocals, hmask]
  · by_cases hmask : probeMask j.1 = true <;> simp [scheduleProbeLocals, hji, hmask]

@[simp] theorem scheduleProbeLocals_chanD {n : Nat}
    (s : SymState HomeState NodeState n) (requester : Fin n)
    (probeMask : Nat → Bool) (kind : ReqKind) (resultPerm : TLPerm) (source : SourceId)
    (j : Fin n) :
    (scheduleProbeLocals s requester probeMask kind resultPerm source j).chanD =
      (s.locals j).chanD := by
  by_cases hji : j = requester
  · cases hji
    by_cases hmask : probeMask requester.1 = true <;> simp [scheduleProbeLocals, hmask]
  · by_cases hmask : probeMask j.1 = true <;> simp [scheduleProbeLocals, hji, hmask]

@[simp] theorem scheduleProbeLocals_chanE {n : Nat}
    (s : SymState HomeState NodeState n) (requester : Fin n)
    (probeMask : Nat → Bool) (kind : ReqKind) (resultPerm : TLPerm) (source : SourceId)
    (j : Fin n) :
    (scheduleProbeLocals s requester probeMask kind resultPerm source j).chanE =
      (s.locals j).chanE := by
  by_cases hji : j = requester
  · cases hji
    by_cases hmask : probeMask requester.1 = true <;> simp [scheduleProbeLocals, hmask]
  · by_cases hmask : probeMask j.1 = true <;> simp [scheduleProbeLocals, hji, hmask]

@[simp] theorem scheduleProbeLocals_pendingSource {n : Nat}
    (s : SymState HomeState NodeState n) (requester : Fin n)
    (probeMask : Nat → Bool) (kind : ReqKind) (resultPerm : TLPerm) (source : SourceId)
    (j : Fin n) :
    (scheduleProbeLocals s requester probeMask kind resultPerm source j).pendingSource =
      (s.locals j).pendingSource := by
  by_cases hji : j = requester
  · cases hji
    by_cases hmask : probeMask requester.1 = true <;> simp [scheduleProbeLocals, hmask]
  · by_cases hmask : probeMask j.1 = true <;> simp [scheduleProbeLocals, hji, hmask]

@[simp] theorem scheduleProbeLocals_pendingSink {n : Nat}
    (s : SymState HomeState NodeState n) (requester : Fin n)
    (probeMask : Nat → Bool) (kind : ReqKind) (resultPerm : TLPerm) (source : SourceId)
    (j : Fin n) :
    (scheduleProbeLocals s requester probeMask kind resultPerm source j).pendingSink =
      (s.locals j).pendingSink := by
  by_cases hji : j = requester
  · cases hji
    by_cases hmask : probeMask requester.1 = true <;> simp [scheduleProbeLocals, hmask]
  · by_cases hmask : probeMask j.1 = true <;> simp [scheduleProbeLocals, hji, hmask]

@[simp] theorem scheduleProbeLocals_releaseInFlight {n : Nat}
    (s : SymState HomeState NodeState n) (requester : Fin n)
    (probeMask : Nat → Bool) (kind : ReqKind) (resultPerm : TLPerm) (source : SourceId)
    (j : Fin n) :
    (scheduleProbeLocals s requester probeMask kind resultPerm source j).releaseInFlight =
      (s.locals j).releaseInFlight := by
  by_cases hji : j = requester
  · cases hji
    by_cases hmask : probeMask requester.1 = true <;> simp [scheduleProbeLocals, hmask]
  · by_cases hmask : probeMask j.1 = true <;> simp [scheduleProbeLocals, hji, hmask]

@[simp] theorem scheduleProbeLocals_chanA_self {n : Nat}
    (s : SymState HomeState NodeState n) (requester : Fin n)
    (probeMask : Nat → Bool) (kind : ReqKind) (resultPerm : TLPerm) (source : SourceId) :
    (scheduleProbeLocals s requester probeMask kind resultPerm source requester).chanA = none := by
  by_cases hmask : probeMask requester.1 = true <;> simp [scheduleProbeLocals, hmask]

@[simp] theorem scheduleProbeLocals_chanA_other {n : Nat}
    (s : SymState HomeState NodeState n) (requester j : Fin n)
    (probeMask : Nat → Bool) (kind : ReqKind) (resultPerm : TLPerm) (source : SourceId)
    (h : j ≠ requester) :
    (scheduleProbeLocals s requester probeMask kind resultPerm source j).chanA =
      (s.locals j).chanA := by
  by_cases hmask : probeMask j.1 = true <;> simp [scheduleProbeLocals, h, hmask]

@[simp] theorem scheduleProbeLocals_chanB_true {n : Nat}
    (s : SymState HomeState NodeState n) (requester j : Fin n)
    (probeMask : Nat → Bool) (kind : ReqKind) (resultPerm : TLPerm) (source : SourceId)
    (hmask : probeMask j.1 = true) :
    (scheduleProbeLocals s requester probeMask kind resultPerm source j).chanB =
      some { opcode := probeOpcodeOfKind kind, param := probeCapOfResult resultPerm, source := source } := by
  by_cases hji : j = requester
  · cases hji
    simp [scheduleProbeLocals, hmask]
  · simp [scheduleProbeLocals, hji, hmask]

@[simp] theorem scheduleProbeLocals_chanB_false {n : Nat}
    (s : SymState HomeState NodeState n) (requester j : Fin n)
    (probeMask : Nat → Bool) (kind : ReqKind) (resultPerm : TLPerm) (source : SourceId)
    (hmask : probeMask j.1 = false) :
    (scheduleProbeLocals s requester probeMask kind resultPerm source j).chanB =
      if j = requester then (s.locals j).chanB else (s.locals j).chanB := by
  by_cases hji : j = requester
  · cases hji
    simp [scheduleProbeLocals, hmask]
  · simp [scheduleProbeLocals, hji, hmask]

@[simp] theorem recvAcquireShared_mem {n : Nat}
    (s : SymState HomeState NodeState n) (requester : Fin n)
    (kind : ReqKind) (grow : GrowParam) (source : SourceId) :
    (recvAcquireShared s requester kind grow source).mem = s.shared.mem := rfl

@[simp] theorem recvAcquireShared_dir {n : Nat}
    (s : SymState HomeState NodeState n) (requester : Fin n)
    (kind : ReqKind) (grow : GrowParam) (source : SourceId) :
    (recvAcquireShared s requester kind grow source).dir = s.shared.dir := rfl

@[simp] theorem recvAcquireLocals_line {n : Nat}
    (s : SymState HomeState NodeState n) (requester : Fin n)
    (kind : ReqKind) (grow : GrowParam) (source : SourceId) (j : Fin n) :
    (recvAcquireLocals s requester kind grow source j).line = (s.locals j).line := by
  simp [recvAcquireLocals]

@[simp] theorem recvAcquireLocals_chanC {n : Nat}
    (s : SymState HomeState NodeState n) (requester : Fin n)
    (kind : ReqKind) (grow : GrowParam) (source : SourceId) (j : Fin n) :
    (recvAcquireLocals s requester kind grow source j).chanC = (s.locals j).chanC := by
  simp [recvAcquireLocals]

@[simp] theorem recvAcquireLocals_chanD {n : Nat}
    (s : SymState HomeState NodeState n) (requester : Fin n)
    (kind : ReqKind) (grow : GrowParam) (source : SourceId) (j : Fin n) :
    (recvAcquireLocals s requester kind grow source j).chanD = (s.locals j).chanD := by
  simp [recvAcquireLocals]

@[simp] theorem recvAcquireLocals_chanE {n : Nat}
    (s : SymState HomeState NodeState n) (requester : Fin n)
    (kind : ReqKind) (grow : GrowParam) (source : SourceId) (j : Fin n) :
    (recvAcquireLocals s requester kind grow source j).chanE = (s.locals j).chanE := by
  simp [recvAcquireLocals]

@[simp] theorem recvAcquireLocals_pendingSource {n : Nat}
    (s : SymState HomeState NodeState n) (requester : Fin n)
    (kind : ReqKind) (grow : GrowParam) (source : SourceId) (j : Fin n) :
    (recvAcquireLocals s requester kind grow source j).pendingSource = (s.locals j).pendingSource := by
  simp [recvAcquireLocals]

@[simp] theorem recvAcquireLocals_pendingSink {n : Nat}
    (s : SymState HomeState NodeState n) (requester : Fin n)
    (kind : ReqKind) (grow : GrowParam) (source : SourceId) (j : Fin n) :
    (recvAcquireLocals s requester kind grow source j).pendingSink = (s.locals j).pendingSink := by
  simp [recvAcquireLocals]

@[simp] theorem recvAcquireLocals_releaseInFlight {n : Nat}
    (s : SymState HomeState NodeState n) (requester : Fin n)
    (kind : ReqKind) (grow : GrowParam) (source : SourceId) (j : Fin n) :
    (recvAcquireLocals s requester kind grow source j).releaseInFlight = (s.locals j).releaseInFlight := by
  simp [recvAcquireLocals]

@[simp] theorem sendAcquireBlock_shared {n : Nat}
    {s s' : SymState HomeState NodeState n} {i : Fin n} {grow : GrowParam} {source : SourceId}
    (h : SendAcquireBlock s s' i grow source) :
    s'.shared = s.shared := by
  rcases h with ⟨_, _, _, _, _, _, _, rfl⟩
  rfl

@[simp] theorem sendAcquirePerm_shared {n : Nat}
    {s s' : SymState HomeState NodeState n} {i : Fin n} {grow : GrowParam} {source : SourceId}
    (h : SendAcquirePerm s s' i grow source) :
    s'.shared = s.shared := by
  rcases h with ⟨_, _, _, _, _, _, _, rfl⟩
  rfl

@[simp] theorem sendAcquireBlock_line {n : Nat}
    {s s' : SymState HomeState NodeState n} {i j : Fin n} {grow : GrowParam} {source : SourceId}
    (h : SendAcquireBlock s s' i grow source) :
    (s'.locals j).line = (s.locals j).line := by
  rcases h with ⟨_, _, _, _, _, _, _, rfl⟩
  by_cases hji : j = i <;> simp [setFn, hji]

@[simp] theorem sendAcquirePerm_line {n : Nat}
    {s s' : SymState HomeState NodeState n} {i j : Fin n} {grow : GrowParam} {source : SourceId}
    (h : SendAcquirePerm s s' i grow source) :
    (s'.locals j).line = (s.locals j).line := by
  rcases h with ⟨_, _, _, _, _, _, _, rfl⟩
  by_cases hji : j = i <;> simp [setFn, hji]

@[simp] theorem sendAcquireBlock_chanB {n : Nat}
    {s s' : SymState HomeState NodeState n} {i j : Fin n} {grow : GrowParam} {source : SourceId}
    (h : SendAcquireBlock s s' i grow source) :
    (s'.locals j).chanB = (s.locals j).chanB := by
  rcases h with ⟨_, _, _, _, _, _, _, rfl⟩
  by_cases hji : j = i <;> simp [setFn, hji]

@[simp] theorem sendAcquirePerm_chanB {n : Nat}
    {s s' : SymState HomeState NodeState n} {i j : Fin n} {grow : GrowParam} {source : SourceId}
    (h : SendAcquirePerm s s' i grow source) :
    (s'.locals j).chanB = (s.locals j).chanB := by
  rcases h with ⟨_, _, _, _, _, _, _, rfl⟩
  by_cases hji : j = i <;> simp [setFn, hji]

@[simp] theorem sendAcquireBlock_chanC {n : Nat}
    {s s' : SymState HomeState NodeState n} {i j : Fin n} {grow : GrowParam} {source : SourceId}
    (h : SendAcquireBlock s s' i grow source) :
    (s'.locals j).chanC = (s.locals j).chanC := by
  rcases h with ⟨_, _, _, _, _, _, _, rfl⟩
  by_cases hji : j = i <;> simp [setFn, hji]

@[simp] theorem sendAcquirePerm_chanC {n : Nat}
    {s s' : SymState HomeState NodeState n} {i j : Fin n} {grow : GrowParam} {source : SourceId}
    (h : SendAcquirePerm s s' i grow source) :
    (s'.locals j).chanC = (s.locals j).chanC := by
  rcases h with ⟨_, _, _, _, _, _, _, rfl⟩
  by_cases hji : j = i <;> simp [setFn, hji]

@[simp] theorem sendAcquireBlock_chanD {n : Nat}
    {s s' : SymState HomeState NodeState n} {i j : Fin n} {grow : GrowParam} {source : SourceId}
    (h : SendAcquireBlock s s' i grow source) :
    (s'.locals j).chanD = (s.locals j).chanD := by
  rcases h with ⟨_, _, _, _, _, _, _, rfl⟩
  by_cases hji : j = i <;> simp [setFn, hji]

@[simp] theorem sendAcquirePerm_chanD {n : Nat}
    {s s' : SymState HomeState NodeState n} {i j : Fin n} {grow : GrowParam} {source : SourceId}
    (h : SendAcquirePerm s s' i grow source) :
    (s'.locals j).chanD = (s.locals j).chanD := by
  rcases h with ⟨_, _, _, _, _, _, _, rfl⟩
  by_cases hji : j = i <;> simp [setFn, hji]

@[simp] theorem sendAcquireBlock_chanE {n : Nat}
    {s s' : SymState HomeState NodeState n} {i j : Fin n} {grow : GrowParam} {source : SourceId}
    (h : SendAcquireBlock s s' i grow source) :
    (s'.locals j).chanE = (s.locals j).chanE := by
  rcases h with ⟨_, _, _, _, _, _, _, rfl⟩
  by_cases hji : j = i <;> simp [setFn, hji]

@[simp] theorem sendAcquirePerm_chanE {n : Nat}
    {s s' : SymState HomeState NodeState n} {i j : Fin n} {grow : GrowParam} {source : SourceId}
    (h : SendAcquirePerm s s' i grow source) :
    (s'.locals j).chanE = (s.locals j).chanE := by
  rcases h with ⟨_, _, _, _, _, _, _, rfl⟩
  by_cases hji : j = i <;> simp [setFn, hji]

@[simp] theorem sendAcquireBlock_pendingSink {n : Nat}
    {s s' : SymState HomeState NodeState n} {i j : Fin n} {grow : GrowParam} {source : SourceId}
    (h : SendAcquireBlock s s' i grow source) :
    (s'.locals j).pendingSink = (s.locals j).pendingSink := by
  rcases h with ⟨_, _, _, _, _, _, _, rfl⟩
  by_cases hji : j = i <;> simp [setFn, hji]

@[simp] theorem sendAcquirePerm_pendingSink {n : Nat}
    {s s' : SymState HomeState NodeState n} {i j : Fin n} {grow : GrowParam} {source : SourceId}
    (h : SendAcquirePerm s s' i grow source) :
    (s'.locals j).pendingSink = (s.locals j).pendingSink := by
  rcases h with ⟨_, _, _, _, _, _, _, rfl⟩
  by_cases hji : j = i <;> simp [setFn, hji]

@[simp] theorem sendAcquireBlock_releaseInFlight {n : Nat}
    {s s' : SymState HomeState NodeState n} {i j : Fin n} {grow : GrowParam} {source : SourceId}
    (h : SendAcquireBlock s s' i grow source) :
    (s'.locals j).releaseInFlight = (s.locals j).releaseInFlight := by
  rcases h with ⟨_, _, _, _, _, _, _, rfl⟩
  by_cases hji : j = i <;> simp [setFn, hji]

@[simp] theorem sendAcquirePerm_releaseInFlight {n : Nat}
    {s s' : SymState HomeState NodeState n} {i j : Fin n} {grow : GrowParam} {source : SourceId}
    (h : SendAcquirePerm s s' i grow source) :
    (s'.locals j).releaseInFlight = (s.locals j).releaseInFlight := by
  rcases h with ⟨_, _, _, _, _, _, _, rfl⟩
  by_cases hji : j = i <;> simp [setFn, hji]

@[simp] theorem sendGrantState_line {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) (tx : ManagerTxn) :
    ((sendGrantState s i tx).locals j).line = (s.locals j).line := by
  by_cases hji : j = i <;> simp [sendGrantState, sendGrantLocals, setFn, hji]

@[simp] theorem sendGrantState_chanA {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) (tx : ManagerTxn) :
    ((sendGrantState s i tx).locals j).chanA = (s.locals j).chanA := by
  by_cases hji : j = i <;> simp [sendGrantState, sendGrantLocals, setFn, hji]

@[simp] theorem sendGrantState_chanB {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) (tx : ManagerTxn) :
    ((sendGrantState s i tx).locals j).chanB = (s.locals j).chanB := by
  by_cases hji : j = i <;> simp [sendGrantState, sendGrantLocals, setFn, hji]

@[simp] theorem sendGrantState_chanC {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) (tx : ManagerTxn) :
    ((sendGrantState s i tx).locals j).chanC = (s.locals j).chanC := by
  by_cases hji : j = i <;> simp [sendGrantState, sendGrantLocals, setFn, hji]

@[simp] theorem sendGrantState_chanE {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) (tx : ManagerTxn) :
    ((sendGrantState s i tx).locals j).chanE = (s.locals j).chanE := by
  by_cases hji : j = i <;> simp [sendGrantState, sendGrantLocals, setFn, hji]

@[simp] theorem sendGrantState_pendingSource {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) (tx : ManagerTxn) :
    ((sendGrantState s i tx).locals j).pendingSource = (s.locals j).pendingSource := by
  by_cases hji : j = i <;> simp [sendGrantState, sendGrantLocals, setFn, hji]

@[simp] theorem sendGrantState_releaseInFlight {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) (tx : ManagerTxn) :
    ((sendGrantState s i tx).locals j).releaseInFlight = (s.locals j).releaseInFlight := by
  by_cases hji : j = i <;> simp [sendGrantState, sendGrantLocals, setFn, hji]

@[simp] theorem recvGrantState_chanA {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) (tx : ManagerTxn) :
    ((recvGrantState s i tx).locals j).chanA = (s.locals j).chanA := by
  by_cases hji : j = i <;> simp [recvGrantState, recvGrantLocals, recvGrantLocal, setFn, hji]

@[simp] theorem recvGrantState_chanB {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) (tx : ManagerTxn) :
    ((recvGrantState s i tx).locals j).chanB = (s.locals j).chanB := by
  by_cases hji : j = i <;> simp [recvGrantState, recvGrantLocals, recvGrantLocal, setFn, hji]

@[simp] theorem recvGrantState_chanC {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) (tx : ManagerTxn) :
    ((recvGrantState s i tx).locals j).chanC = (s.locals j).chanC := by
  by_cases hji : j = i <;> simp [recvGrantState, recvGrantLocals, recvGrantLocal, setFn, hji]

@[simp] theorem recvGrantState_pendingSink {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) (tx : ManagerTxn) :
    ((recvGrantState s i tx).locals j).pendingSink =
      if j = i then (s.locals j).pendingSink else (s.locals j).pendingSink := by
  by_cases hji : j = i <;> simp [recvGrantState, recvGrantLocals, recvGrantLocal, setFn, hji]

@[simp] theorem recvGrantState_releaseInFlight {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) (tx : ManagerTxn) :
    ((recvGrantState s i tx).locals j).releaseInFlight = (s.locals j).releaseInFlight := by
  by_cases hji : j = i <;> simp [recvGrantState, recvGrantLocals, recvGrantLocal, setFn, hji]

@[simp] theorem recvGrantAckState_line {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) :
    ((recvGrantAckState s i).locals j).line = (s.locals j).line := by
  by_cases hji : j = i <;> simp [recvGrantAckState, recvGrantAckLocals, setFn, hji]

@[simp] theorem recvGrantAckState_chanA {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) :
    ((recvGrantAckState s i).locals j).chanA = (s.locals j).chanA := by
  by_cases hji : j = i <;> simp [recvGrantAckState, recvGrantAckLocals, setFn, hji]

@[simp] theorem recvGrantAckState_chanB {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) :
    ((recvGrantAckState s i).locals j).chanB = (s.locals j).chanB := by
  by_cases hji : j = i <;> simp [recvGrantAckState, recvGrantAckLocals, setFn, hji]

@[simp] theorem recvGrantAckState_chanC {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) :
    ((recvGrantAckState s i).locals j).chanC = (s.locals j).chanC := by
  by_cases hji : j = i <;> simp [recvGrantAckState, recvGrantAckLocals, setFn, hji]

@[simp] theorem recvGrantAckState_chanD {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) :
    ((recvGrantAckState s i).locals j).chanD = (s.locals j).chanD := by
  by_cases hji : j = i <;> simp [recvGrantAckState, recvGrantAckLocals, setFn, hji]

@[simp] theorem recvGrantAckState_pendingSource {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) :
    ((recvGrantAckState s i).locals j).pendingSource = (s.locals j).pendingSource := by
  by_cases hji : j = i <;> simp [recvGrantAckState, recvGrantAckLocals, setFn, hji]

@[simp] theorem recvGrantAckState_releaseInFlight {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) :
    ((recvGrantAckState s i).locals j).releaseInFlight = (s.locals j).releaseInFlight := by
  by_cases hji : j = i <;> simp [recvGrantAckState, recvGrantAckLocals, setFn, hji]

@[simp] theorem sendReleaseState_chanA {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) (param : PruneReportParam) (withData : Bool) :
    ((sendReleaseState s i param withData).locals j).chanA = (s.locals j).chanA := by
  by_cases hji : j = i <;> simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji]

@[simp] theorem sendReleaseState_chanB {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) (param : PruneReportParam) (withData : Bool) :
    ((sendReleaseState s i param withData).locals j).chanB = (s.locals j).chanB := by
  by_cases hji : j = i <;> simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji]

@[simp] theorem sendReleaseState_chanD {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) (param : PruneReportParam) (withData : Bool) :
    ((sendReleaseState s i param withData).locals j).chanD = (s.locals j).chanD := by
  by_cases hji : j = i <;> simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji]

@[simp] theorem sendReleaseState_chanE {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) (param : PruneReportParam) (withData : Bool) :
    ((sendReleaseState s i param withData).locals j).chanE = (s.locals j).chanE := by
  by_cases hji : j = i <;> simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji]

@[simp] theorem sendReleaseState_pendingSource {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) (param : PruneReportParam) (withData : Bool) :
    ((sendReleaseState s i param withData).locals j).pendingSource = (s.locals j).pendingSource := by
  by_cases hji : j = i <;> simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji]

@[simp] theorem sendReleaseState_pendingSink {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) (param : PruneReportParam) (withData : Bool) :
    ((sendReleaseState s i param withData).locals j).pendingSink = (s.locals j).pendingSink := by
  by_cases hji : j = i <;> simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji]

@[simp] theorem sendReleaseState_releaseInFlight {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) (param : PruneReportParam) (withData : Bool) :
    ((sendReleaseState s i param withData).locals j).releaseInFlight =
      if j = i then true else (s.locals j).releaseInFlight := by
  by_cases hji : j = i <;> simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji]

@[simp] theorem recvReleaseState_line {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) (msg : CMsg) (param : PruneReportParam) :
    ((recvReleaseState s i msg param).locals j).line = (s.locals j).line := by
  by_cases hji : j = i <;> simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn, hji]

@[simp] theorem recvReleaseState_chanA {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) (msg : CMsg) (param : PruneReportParam) :
    ((recvReleaseState s i msg param).locals j).chanA = (s.locals j).chanA := by
  by_cases hji : j = i <;> simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn, hji]

@[simp] theorem recvReleaseState_chanB {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) (msg : CMsg) (param : PruneReportParam) :
    ((recvReleaseState s i msg param).locals j).chanB = (s.locals j).chanB := by
  by_cases hji : j = i <;> simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn, hji]

@[simp] theorem recvReleaseState_chanE {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) (msg : CMsg) (param : PruneReportParam) :
    ((recvReleaseState s i msg param).locals j).chanE = (s.locals j).chanE := by
  by_cases hji : j = i <;> simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn, hji]

@[simp] theorem recvReleaseState_pendingSource {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) (msg : CMsg) (param : PruneReportParam) :
    ((recvReleaseState s i msg param).locals j).pendingSource = (s.locals j).pendingSource := by
  by_cases hji : j = i <;> simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn, hji]

@[simp] theorem recvReleaseState_pendingSink {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) (msg : CMsg) (param : PruneReportParam) :
    ((recvReleaseState s i msg param).locals j).pendingSink = (s.locals j).pendingSink := by
  by_cases hji : j = i <;> simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn, hji]

@[simp] theorem recvReleaseState_releaseInFlight {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) (msg : CMsg) (param : PruneReportParam) :
    ((recvReleaseState s i msg param).locals j).releaseInFlight = (s.locals j).releaseInFlight := by
  by_cases hji : j = i <;> simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn, hji]

@[simp] theorem recvReleaseAckState_line {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) :
    ((recvReleaseAckState s i).locals j).line = (s.locals j).line := by
  by_cases hji : j = i <;> simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn, hji]

@[simp] theorem recvReleaseAckState_chanA {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) :
    ((recvReleaseAckState s i).locals j).chanA = (s.locals j).chanA := by
  by_cases hji : j = i <;> simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn, hji]

@[simp] theorem recvReleaseAckState_chanB {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) :
    ((recvReleaseAckState s i).locals j).chanB = (s.locals j).chanB := by
  by_cases hji : j = i <;> simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn, hji]

@[simp] theorem recvReleaseAckState_chanC {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) :
    ((recvReleaseAckState s i).locals j).chanC = (s.locals j).chanC := by
  by_cases hji : j = i <;> simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn, hji]

@[simp] theorem recvReleaseAckState_chanE {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) :
    ((recvReleaseAckState s i).locals j).chanE = (s.locals j).chanE := by
  by_cases hji : j = i <;> simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn, hji]

@[simp] theorem recvReleaseAckState_pendingSource {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) :
    ((recvReleaseAckState s i).locals j).pendingSource = (s.locals j).pendingSource := by
  by_cases hji : j = i <;> simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn, hji]

@[simp] theorem recvReleaseAckState_pendingSink {n : Nat}
    (s : SymState HomeState NodeState n) (i j : Fin n) :
    ((recvReleaseAckState s i).locals j).pendingSink = (s.locals j).pendingSink := by
  by_cases hji : j = i <;> simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn, hji]

end TileLink.Messages
