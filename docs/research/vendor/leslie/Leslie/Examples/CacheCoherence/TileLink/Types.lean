/-! ## TileLink TL-C Shared Types

    Basic protocol vocabulary shared by the TileLink cache-coherence models.
    This file contains only enums and small records, with no protocol dynamics.
-/

namespace TileLink

abbrev Val := Nat
abbrev Addr := Nat
abbrev SourceId := Nat
abbrev SinkId := Nat
abbrev Size := Nat

/-- TileLink coherence permissions. -/
inductive TLPerm where
  | N
  | B
  | T
  deriving DecidableEq, Repr, BEq

/-- Acquire growth parameters. -/
inductive GrowParam where
  | NtoB
  | NtoT
  | BtoT
  deriving DecidableEq, Repr, BEq

/-- Probe cap parameters. -/
inductive CapParam where
  | toT
  | toB
  | toN
  deriving DecidableEq, Repr, BEq

/-- C-channel prune/report parameters. -/
inductive PruneReportParam where
  | TtoB
  | TtoN
  | BtoN
  | TtoT
  | BtoB
  | NtoN
  deriving DecidableEq, Repr, BEq

/-- A-channel opcodes relevant to cached TileLink systems. -/
inductive AOpcode where
  | putFullData
  | putPartialData
  | arithmeticData
  | logicalData
  | get
  | hint
  | acquireBlock
  | acquirePerm
  deriving DecidableEq, Repr, BEq

/-- B-channel opcodes relevant to cached TileLink systems. -/
inductive BOpcode where
  | probeBlock
  | probePerm
  | get
  | putFullData
  | putPartialData
  | arithmeticData
  | logicalData
  | hint
  deriving DecidableEq, Repr, BEq

/-- C-channel opcodes relevant to cached TileLink systems. -/
inductive COpcode where
  | accessAck
  | accessAckData
  | hintAck
  | probeAck
  | probeAckData
  | release
  | releaseData
  deriving DecidableEq, Repr, BEq

/-- D-channel opcodes relevant to cached TileLink systems. -/
inductive DOpcode where
  | accessAck
  | accessAckData
  | hintAck
  | grant
  | grantData
  | releaseAck
  deriving DecidableEq, Repr, BEq

/-- E-channel opcodes relevant to cached TileLink systems. -/
inductive EOpcode where
  | grantAck
  deriving DecidableEq, Repr, BEq

/-- A small transaction key used to match request/response obligations. -/
structure TxnKey where
  address : Addr
  source : SourceId
  sink : Option SinkId := none
  deriving DecidableEq, Repr, BEq

def TxnKey.withSink (key : TxnKey) (sink : SinkId) : TxnKey :=
  { key with sink := some sink }

def TxnKey.clearSink (key : TxnKey) : TxnKey :=
  { key with sink := none }

@[simp] theorem TxnKey.withSink_address (key : TxnKey) (sink : SinkId) :
    (key.withSink sink).address = key.address := rfl

@[simp] theorem TxnKey.withSink_source (key : TxnKey) (sink : SinkId) :
    (key.withSink sink).source = key.source := rfl

@[simp] theorem TxnKey.withSink_sink (key : TxnKey) (sink : SinkId) :
    (key.withSink sink).sink = some sink := rfl

@[simp] theorem TxnKey.clearSink_sink (key : TxnKey) :
    key.clearSink.sink = none := rfl

end TileLink
