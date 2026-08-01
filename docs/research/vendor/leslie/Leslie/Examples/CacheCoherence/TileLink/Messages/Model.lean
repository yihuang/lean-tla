import Leslie.Examples.CacheCoherence.TileLink.Messages.Helpers

open TLA SymShared Classical

/-! ## TileLink TL-C Message-Level Model

    Action predicates and the `tlMessages` spec for the explicit single-line
    message model with per-channel endpoint state.

    The current action slice covers acquire send/receive, explicit probe
    receive and probe-ack handling, explicit D/E grant completion, and
    explicit C/D release completion.

    Core type definitions live in `ModelDefs.lean`.
    Helper functions and state transformers live in `Helpers.lean`.
-/

namespace TileLink.Messages

open TileLink

def SendAcquireBlock {n : Nat}
    (s s' : SymState HomeState NodeState n)
    (i : Fin n) (grow : GrowParam) (source : SourceId) : Prop :=
  (s.locals i).chanA = none ∧
  (s.locals i).chanB = none ∧
  (s.locals i).chanC = none ∧
  (s.locals i).pendingSource = none ∧
  (s.locals i).releaseInFlight = false ∧
  (s.locals i).line.perm = .N ∧
  grow.legalFrom (s.locals i).line.perm ∧
  s' = { shared := s.shared
       , locals := setFn s.locals i
           { (s.locals i) with
               chanA := some (mkAcquireBlockMsg grow source)
               pendingSource := some source } }

def SendAcquirePerm {n : Nat}
    (s s' : SymState HomeState NodeState n)
    (i : Fin n) (grow : GrowParam) (source : SourceId) : Prop :=
  (s.locals i).chanA = none ∧
  (s.locals i).chanB = none ∧
  (s.locals i).chanC = none ∧
  (s.locals i).pendingSource = none ∧
  (s.locals i).releaseInFlight = false ∧
  grow.legalFrom (s.locals i).line.perm ∧
  grow.result = .T ∧
  s' = { shared := s.shared
       , locals := setFn s.locals i
           { (s.locals i) with
               chanA := some (mkAcquirePermMsg grow source)
               pendingSource := some source } }

def RecvAcquireBlockAtManager {n : Nat}
    (s s' : SymState HomeState NodeState n)
    (i : Fin n) (grow : GrowParam) (source : SourceId) : Prop :=
  s.shared.currentTxn = none ∧
  s.shared.pendingGrantAck = none ∧
  s.shared.pendingReleaseAck = none ∧
  (∀ j : Fin n, (s.locals j).chanC = none) ∧
  (∀ j : Fin n, (s.locals j).releaseInFlight = false) ∧
  (s.locals i).chanA = some (mkAcquireBlockMsg grow source) ∧
  (s.locals i).line.perm = .N ∧
  grow.legalFrom (s.locals i).line.perm ∧
  ((hasDirtyOther s i ∧ grow.result = .B) ∨
   (¬hasDirtyOther s i ∧ hasCachedOther s i ∧ grow.result = .B) ∨
   (allOthersInvalid s i ∧ grow.result = .T)) ∧
  allTargetBsEmpty s (probeMaskForResult s i grow.result) ∧
  s' = recvAcquireState s i .acquireBlock grow source

def RecvAcquirePermAtManager {n : Nat}
    (s s' : SymState HomeState NodeState n)
    (i : Fin n) (grow : GrowParam) (source : SourceId) : Prop :=
  s.shared.currentTxn = none ∧
  s.shared.pendingGrantAck = none ∧
  s.shared.pendingReleaseAck = none ∧
  (∀ j : Fin n, (s.locals j).chanC = none) ∧
  (∀ j : Fin n, (s.locals j).releaseInFlight = false) ∧
  (s.locals i).chanA = some (mkAcquirePermMsg grow source) ∧
  grow.legalFrom (s.locals i).line.perm ∧
  grow.result = .T ∧
  allTargetBsEmpty s (probeMaskForResult s i grow.result) ∧
  s' = recvAcquireState s i .acquirePerm grow source

def RecvAcquireAtManager {n : Nat}
    (s s' : SymState HomeState NodeState n) (i : Fin n) : Prop :=
  (∃ grow source, RecvAcquireBlockAtManager s s' i grow source) ∨
  (∃ grow source, RecvAcquirePermAtManager s s' i grow source)

def RecvProbeAtMaster {n : Nat}
    (s s' : SymState HomeState NodeState n) (i : Fin n) : Prop :=
  ∃ tx msg,
    s.shared.currentTxn = some tx ∧
    tx.phase = .probing ∧
    tx.probesRemaining i.1 = true ∧
    (s.locals i).chanB = some msg ∧
    msg.source = tx.source ∧
    msg.opcode = probeOpcodeOfKind tx.kind ∧
    msg.param = probeCapOfResult tx.resultPerm ∧
    (s.locals i).chanC = none ∧
    s' = recvProbeState s i msg

def RecvProbeAckAtManager {n : Nat}
    (s s' : SymState HomeState NodeState n) (i : Fin n) : Prop :=
  ∃ tx msg,
    s.shared.currentTxn = some tx ∧
    tx.phase = .probing ∧
    tx.probesRemaining i.1 = true ∧
    (s.locals i).chanC = some msg ∧
    msg.source = i.1 ∧
    probeAckMsgWellFormed msg ∧
    s' = recvProbeAckState s i tx msg

def SendGrantToRequester {n : Nat}
    (s s' : SymState HomeState NodeState n) (i : Fin n) : Prop :=
  ∃ tx,
    s.shared.currentTxn = some tx ∧
    tx.requester = i.1 ∧
    tx.phase = .grantReady ∧
    s.shared.pendingGrantAck = none ∧
    s.shared.pendingReleaseAck = none ∧
    (s.locals i).chanD = none ∧
    (s.locals i).chanE = none ∧
    (s.locals i).pendingSink = none ∧
    s' = sendGrantState s i tx

def RecvGrantAtMaster {n : Nat}
    (s s' : SymState HomeState NodeState n) (i : Fin n) : Prop :=
  ∃ tx msg,
    s.shared.currentTxn = some tx ∧
    tx.requester = i.1 ∧
    tx.phase = .grantPendingAck ∧
    s.shared.pendingGrantAck = some i.1 ∧
    (s.locals i).chanA = none ∧
    (s.locals i).chanD = some msg ∧
    (s.locals i).chanE = none ∧
    (s.locals i).pendingSink = some tx.sink ∧
    msg = grantMsgOfTxn tx ∧
    s' = recvGrantState s i tx

def RecvGrantAckAtManager {n : Nat}
    (s s' : SymState HomeState NodeState n) (i : Fin n) : Prop :=
  ∃ tx msg,
    s.shared.currentTxn = some tx ∧
    tx.requester = i.1 ∧
    tx.phase = .grantPendingAck ∧
    s.shared.pendingGrantAck = some i.1 ∧
    (s.locals i).chanD = none ∧
    (s.locals i).chanE = some msg ∧
    (s.locals i).pendingSink = some tx.sink ∧
    msg = ({ sink := tx.sink } : EMsg) ∧
    s' = recvGrantAckState s i

def SendRelease {n : Nat}
    (s s' : SymState HomeState NodeState n)
    (i : Fin n) (param : PruneReportParam) : Prop :=
  s.shared.currentTxn = none ∧
  s.shared.pendingGrantAck = none ∧
  s.shared.pendingReleaseAck = none ∧
  (∀ j : Fin n, j ≠ i → (s.locals j).chanC = none) ∧
  (s.locals i).chanA = none ∧
  (s.locals i).chanB = none ∧
  (s.locals i).chanC = none ∧
  (s.locals i).chanD = none ∧
  (s.locals i).chanE = none ∧
  (s.locals i).pendingSource = none ∧
  (s.locals i).pendingSink = none ∧
  (s.locals i).releaseInFlight = false ∧
  param.legalFrom (s.locals i).line.perm ∧
  (s.locals i).line.dirty = false ∧
  ((s.locals i).line.valid = true ∨ param.result = .N) ∧
  s' = sendReleaseState s i param false

def SendReleaseData {n : Nat}
    (s s' : SymState HomeState NodeState n)
    (i : Fin n) (param : PruneReportParam) : Prop :=
  s.shared.currentTxn = none ∧
  s.shared.pendingGrantAck = none ∧
  s.shared.pendingReleaseAck = none ∧
  (∀ j : Fin n, j ≠ i → (s.locals j).chanC = none) ∧
  (s.locals i).chanA = none ∧
  (s.locals i).chanB = none ∧
  (s.locals i).chanC = none ∧
  (s.locals i).chanD = none ∧
  (s.locals i).chanE = none ∧
  (s.locals i).pendingSource = none ∧
  (s.locals i).pendingSink = none ∧
  (s.locals i).releaseInFlight = false ∧
  param.legalFrom (s.locals i).line.perm ∧
  (s.locals i).line.dirty = true ∧
  s' = sendReleaseState s i param true

def RecvReleaseAtManager {n : Nat}
    (s s' : SymState HomeState NodeState n) (i : Fin n) : Prop :=
  ∃ msg param,
    s.shared.currentTxn = none ∧
    s.shared.pendingGrantAck = none ∧
    s.shared.pendingReleaseAck = none ∧
    (s.locals i).releaseInFlight = true ∧
    (s.locals i).chanC = some msg ∧
    msg.source = i.1 ∧
    releaseMsgWellFormed msg ∧
    msg.param = some param ∧
    (s.locals i).line.perm = param.result ∧
    (s.locals i).chanD = none ∧
    s' = recvReleaseState s i msg param

def RecvReleaseAckAtMaster {n : Nat}
    (s s' : SymState HomeState NodeState n) (i : Fin n) : Prop :=
  ∃ msg,
    s.shared.currentTxn = none ∧
    s.shared.pendingGrantAck = none ∧
    s.shared.pendingReleaseAck = some i.1 ∧
    (s.locals i).releaseInFlight = true ∧
    (s.locals i).chanD = some msg ∧
    msg = releaseAckMsg i.1 ∧
    s' = recvReleaseAckState s i

def Store {n : Nat}
    (s s' : SymState HomeState NodeState n)
    (i : Fin n) (v : Val) : Prop :=
  s.shared.currentTxn = none ∧
  s.shared.pendingGrantAck = none ∧
  s.shared.pendingReleaseAck = none ∧
  (∀ j : Fin n, (s.locals j).chanC = none) ∧
  (s.locals i).line.perm = .T ∧
  (s.locals i).chanA = none ∧
  (s.locals i).chanB = none ∧
  (s.locals i).chanC = none ∧
  (s.locals i).chanD = none ∧
  (s.locals i).chanE = none ∧
  (s.locals i).pendingSource = none ∧
  (s.locals i).releaseInFlight = false ∧
  s' = { shared := s.shared
       , locals := setFn s.locals i (storeLocal (s.locals i) v) }

def Read {n : Nat}
    (s s' : SymState HomeState NodeState n)
    (i : Fin n) : Prop :=
  s.shared.currentTxn = none ∧
  s.shared.pendingGrantAck = none ∧
  s.shared.pendingReleaseAck = none ∧
  (s.locals i).line.perm.allowsRead ∧
  (s.locals i).line.valid = true ∧
  (s.locals i).releaseInFlight = false ∧
  s' = s

def mkGetMsg (source : SourceId) : AMsg :=
  { opcode := .get, param := .NtoB, source := source }

def mkPutMsg (source : SourceId) : AMsg :=
  { opcode := .putFullData, param := .NtoB, source := source }

def UncachedGet {n : Nat}
    (s s' : SymState HomeState NodeState n)
    (i : Fin n) (source : SourceId) : Prop :=
  s.shared.currentTxn = none ∧
  s.shared.pendingGrantAck = none ∧
  s.shared.pendingReleaseAck = none ∧
  (s.locals i).chanA = none ∧
  (s.locals i).chanB = none ∧
  (s.locals i).chanC = none ∧
  (s.locals i).chanD = none ∧
  (s.locals i).chanE = none ∧
  (s.locals i).pendingSource = none ∧
  (s.locals i).releaseInFlight = false ∧
  s' = { shared := s.shared
       , locals := setFn s.locals i
           { (s.locals i) with
               chanA := some (mkGetMsg source)
               pendingSource := some source } }

def UncachedPut {n : Nat}
    (s s' : SymState HomeState NodeState n)
    (i : Fin n) (source : SourceId) (v : Val) : Prop :=
  s.shared.currentTxn = none ∧
  s.shared.pendingGrantAck = none ∧
  s.shared.pendingReleaseAck = none ∧
  (∀ j : Fin n, (s.locals j).line.perm = .N) ∧
  (s.locals i).chanA = none ∧
  (s.locals i).chanB = none ∧
  (s.locals i).chanC = none ∧
  (s.locals i).chanD = none ∧
  (s.locals i).chanE = none ∧
  (s.locals i).pendingSource = none ∧
  (s.locals i).releaseInFlight = false ∧
  s' = { shared := { s.shared with mem := v }
       , locals := setFn s.locals i
           { (s.locals i) with
               chanA := some (mkPutMsg source)
               pendingSource := some source } }

def RecvUncachedAtManager {n : Nat}
    (s s' : SymState HomeState NodeState n) (i : Fin n) : Prop :=
  s.shared.currentTxn = none ∧
  s.shared.pendingGrantAck = none ∧
  s.shared.pendingReleaseAck = none ∧
  ∃ msg : AMsg, (s.locals i).chanA = some msg ∧
    (msg.opcode = .get ∨ msg.opcode = .putFullData) ∧
    s' = { shared := s.shared
         , locals := setFn s.locals i
             { (s.locals i) with
                 chanA := none
                 chanD := some { opcode := if msg.opcode = .get then .accessAckData else .accessAck
                               , sink := 0, source := msg.source
                               , data := if msg.opcode = .get then some s.shared.mem else none } } }

def RecvAccessAckAtMaster {n : Nat}
    (s s' : SymState HomeState NodeState n) (i : Fin n) : Prop :=
  ∃ msg : DMsg, (s.locals i).chanD = some msg ∧
    (msg.opcode = .accessAck ∨ msg.opcode = .accessAckData) ∧
    s' = { shared := s.shared
         , locals := setFn s.locals i
             { (s.locals i) with
                 chanD := none
                 pendingSource := none } }

noncomputable def tlMessages : SymSharedSpec where
  Shared := HomeState
  Local := NodeState
  ActType := Act
  init_shared := fun sh =>
    sh.mem = 0 ∧
    (∀ k : Nat, sh.dir k = .N) ∧
    sh.currentTxn = none ∧
    sh.pendingGrantAck = none ∧
    sh.pendingReleaseAck = none ∧
    sh.nextSink = 0
  init_local := fun loc =>
    loc.line = { perm := .N, valid := false, dirty := false, data := 0 } ∧
    loc.chanA = none ∧
    loc.chanB = none ∧
    loc.chanC = none ∧
    loc.chanD = none ∧
    loc.chanE = none ∧
    loc.pendingSource = none ∧
    loc.pendingSink = none ∧
    loc.releaseInFlight = false
  step := fun _n i a s s' =>
    match a with
    | .sendAcquireBlock grow source => SendAcquireBlock s s' i grow source
    | .sendAcquirePerm grow source => SendAcquirePerm s s' i grow source
    | .recvAcquireAtManager => RecvAcquireAtManager s s' i
    | .recvProbeAtMaster => RecvProbeAtMaster s s' i
    | .recvProbeAckAtManager => RecvProbeAckAtManager s s' i
    | .sendGrantToRequester => SendGrantToRequester s s' i
    | .recvGrantAtMaster => RecvGrantAtMaster s s' i
    | .recvGrantAckAtManager => RecvGrantAckAtManager s s' i
    | .sendRelease param => SendRelease s s' i param
    | .sendReleaseData param => SendReleaseData s s' i param
    | .recvReleaseAtManager => RecvReleaseAtManager s s' i
    | .recvReleaseAckAtMaster => RecvReleaseAckAtMaster s s' i
    | .store v => Store s s' i v
    | .read => Read s s' i
    | .uncachedGet source => UncachedGet s s' i source
    | .uncachedPut source v => UncachedPut s s' i source v
    | .recvUncachedAtManager => RecvUncachedAtManager s s' i
    | .recvAccessAckAtMaster => RecvAccessAckAtMaster s s' i

end TileLink.Messages
