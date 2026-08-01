import Leslie.SymShared
import Leslie.Examples.CacheCoherence.TileLink.Common

open TLA SymShared Classical

/-! ## TileLink TL-C Message-Level Model — Core Type Definitions

    Core type definitions for the explicit single-line message model:
    message records, transaction state, shared/local state, and the action enum.

    Helper functions and simp lemmas live in `Helpers.lean`.
    Action predicates and the `tlMessages` spec live in `Model.lean`.
-/

namespace TileLink.Messages

open TileLink

def lineAddr : Addr := 0

inductive ReqKind where
  | acquireBlock
  | acquirePerm
  deriving DecidableEq, Repr

inductive TxnPhase where
  | probing
  | grantReady
  | grantPendingAck
  deriving DecidableEq, Repr

structure AMsg where
  opcode : AOpcode
  param : GrowParam
  source : SourceId
  address : Addr := lineAddr
  deriving DecidableEq, Repr

structure BMsg where
  opcode : BOpcode
  param : CapParam
  source : SourceId
  address : Addr := lineAddr
  deriving DecidableEq, Repr

structure CMsg where
  opcode : COpcode
  param : Option PruneReportParam := none
  source : SourceId := 0
  sink : Option SinkId := none
  address : Addr := lineAddr
  data : Option Val := none
  deriving DecidableEq, Repr

structure DMsg where
  opcode : DOpcode
  sink : SinkId
  source : SourceId
  param : Option CapParam := none
  address : Addr := lineAddr
  data : Option Val := none
  deriving DecidableEq, Repr

structure EMsg where
  opcode : EOpcode := .grantAck
  sink : SinkId
  deriving DecidableEq, Repr

structure ManagerTxn where
  requester : Nat
  source : SourceId
  sink : SinkId
  kind : ReqKind
  grow : GrowParam
  phase : TxnPhase
  grantHasData : Bool
  resultPerm : TLPerm
  transferVal : Val
  usedDirtySource : Bool
  probesNeeded : Nat → Bool
  probesRemaining : Nat → Bool
  preLines : Nat → CacheLine

structure HomeState where
  mem : Val
  dir : Nat → TLPerm
  currentTxn : Option ManagerTxn
  pendingGrantAck : Option Nat
  pendingReleaseAck : Option Nat
  nextSink : SinkId

structure NodeState where
  line : CacheLine
  chanA : Option AMsg := none
  chanB : Option BMsg := none
  chanC : Option CMsg := none
  chanD : Option DMsg := none
  chanE : Option EMsg := none
  pendingSource : Option SourceId := none
  pendingSink : Option SinkId := none
  releaseInFlight : Bool := false
  deriving DecidableEq, Repr

inductive Act where
  | sendAcquireBlock (grow : GrowParam) (source : SourceId)
  | sendAcquirePerm (grow : GrowParam) (source : SourceId)
  | recvAcquireAtManager
  | recvProbeAtMaster
  | recvProbeAckAtManager
  | sendGrantToRequester
  | recvGrantAtMaster
  | recvGrantAckAtManager
  | sendRelease (param : PruneReportParam)
  | sendReleaseData (param : PruneReportParam)
  | recvReleaseAtManager
  | recvReleaseAckAtMaster
  | store (v : Val)
  | read
  | uncachedGet (source : SourceId)
  | uncachedPut (source : SourceId) (v : Val)
  | recvUncachedAtManager
  | recvAccessAckAtMaster
  deriving DecidableEq

end TileLink.Messages
