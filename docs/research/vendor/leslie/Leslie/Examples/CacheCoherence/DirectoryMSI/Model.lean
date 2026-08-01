import Leslie.Action
import Leslie.Gadgets.SetFn
import Leslie.Gadgets.FrameLemmaGen

open TLA

/-! ## Directory-based MSI Cache Coherence Protocol — Model

    Types, state, named state transformers, frame simp-lemmas,
    actions, init, and transition relation.
    No proofs. Imported by all other files in this module.
-/

namespace DirectoryMSI

abbrev Val := Nat

-- ── Message types ──────────────────────────────────────────────────────────

inductive ReqCmd where
  | empty | getS | getM
  deriving DecidableEq, Repr, BEq

inductive D2CCmd where
  | empty | gntS | gntE | inv | fetch
  deriving DecidableEq, Repr, BEq

inductive C2DCmd where
  | empty | ack
  deriving DecidableEq, Repr, BEq

structure ReqMsg where
  cmd  : ReqCmd := .empty
  data : Val    := 0
  deriving DecidableEq, Repr

structure D2CMsg where
  cmd  : D2CCmd := .empty
  data : Val    := 0
  deriving DecidableEq, Repr

structure C2DMsg where
  cmd  : C2DCmd := .empty
  data : Val    := 0
  deriving DecidableEq, Repr

-- ── Cache / Directory state types ─────────────────────────────────────────

inductive CState where
  | M | S | I
  deriving DecidableEq, Repr, BEq

inductive DirSt where
  | Uncached | Shared | Exclusive
  deriving DecidableEq, Repr, BEq

structure CacheEntry where
  state : CState := .I
  data  : Val    := 0
  deriving DecidableEq, Repr

-- ── Global state ──────────────────────────────────────────────────────────

structure MState (n : Nat) where
  cache   : Fin n → CacheEntry
  reqChan : Fin n → ReqMsg
  d2cChan : Fin n → D2CMsg
  c2dChan : Fin n → C2DMsg
  dirSt   : DirSt
  shrSet  : Fin n → Bool
  exNode  : Fin n
  curCmd  : ReqCmd
  curNode : Fin n
  invSet  : Fin n → Bool
  memData : Val
  auxData : Val

-- ── setFn helper ──────────────────────────────────────────────────────────

-- ── Named state-transformer helpers ───────────────────────────────────────

-- Action 1: processor sends GetS (no directory state change)
-- (pure channel write, no named transformer needed — done inline)

-- Action 3: directory grants S when Uncached
def recvGetS_UncachedState {n} (s : MState n) (i : Fin n) : MState n :=
  { s with
    d2cChan := setFn s.d2cChan i { cmd := .gntS, data := s.memData }
    shrSet  := setFn s.shrSet  i true
    dirSt   := .Shared
    reqChan := setFn s.reqChan i {} }

-- Action 4: directory grants S when already Shared
def recvGetS_SharedState {n} (s : MState n) (i : Fin n) : MState n :=
  { s with
    d2cChan := setFn s.d2cChan i { cmd := .gntS, data := s.memData }
    shrSet  := setFn s.shrSet  i true
    reqChan := setFn s.reqChan i {} }

-- Action 5: directory sends fetch to exclusive holder when GetS arrives
def recvGetS_ExclusiveState {n} (s : MState n) (i : Fin n) : MState n :=
  { s with
    d2cChan := setFn s.d2cChan s.exNode { cmd := .fetch, data := 0 }
    curCmd  := .getS
    curNode := i
    reqChan := setFn s.reqChan i {} }

-- Action 6: directory grants E when Uncached
def recvGetM_UncachedState {n} (s : MState n) (i : Fin n) : MState n :=
  { s with
    d2cChan := setFn s.d2cChan i { cmd := .gntE, data := s.memData }
    exNode  := i
    dirSt   := .Exclusive
    reqChan := setFn s.reqChan i {}
    auxData := s.memData }

-- Action 7: directory starts invalidation when GetM arrives in Shared state
def recvGetM_SharedState {n} (s : MState n) (i : Fin n) : MState n :=
  { s with
    curCmd  := .getM
    curNode := i
    invSet  := setFn s.shrSet i false
    shrSet  := setFn s.shrSet i false
    reqChan := setFn s.reqChan i {} }

-- Action 8: directory sends inv to exclusive holder when GetM arrives (Exclusive state)
def recvGetM_ExclusiveState {n} (s : MState n) (i : Fin n) : MState n :=
  { s with
    d2cChan := setFn s.d2cChan s.exNode { cmd := .inv, data := 0 }
    curCmd  := .getM
    curNode := i
    reqChan := setFn s.reqChan i {} }

-- Action 9: directory sends a pending invalidation to node j
def sendInvState {n} (s : MState n) (j : Fin n) : MState n :=
  { s with
    d2cChan := setFn s.d2cChan j { cmd := .inv, data := 0 }
    invSet  := setFn s.invSet  j false }

-- Action 10: after all sharer acks received (GetM_Shared case), grant E to curNode
--   shrSet is already cleared per ack; just send grant and update directory state.
def sendGntE_AfterSharedState {n} (s : MState n) : MState n :=
  { s with
    d2cChan := setFn s.d2cChan s.curNode { cmd := .gntE, data := s.memData }
    dirSt   := .Exclusive
    exNode  := s.curNode
    curCmd  := .empty
    auxData := s.memData }

-- Action 11: cache receives gntS
def recvGntSState {n} (s : MState n) (i : Fin n) : MState n :=
  { s with
    cache   := setFn s.cache   i { state := .S, data := (s.d2cChan i).data }
    d2cChan := setFn s.d2cChan i {} }

-- Action 12: cache receives gntE
def recvGntEState {n} (s : MState n) (i : Fin n) : MState n :=
  { s with
    cache   := setFn s.cache   i { state := .M, data := (s.d2cChan i).data }
    d2cChan := setFn s.d2cChan i {} }

-- Action 13: cache receives inv, sends ack with data
def recvInvState {n} (s : MState n) (i : Fin n) : MState n :=
  { s with
    cache   := setFn s.cache   i { (s.cache i) with state := .I }
    c2dChan := setFn s.c2dChan i { cmd := .ack, data := (s.cache i).data }
    d2cChan := setFn s.d2cChan i {} }

-- Action 14: cache receives fetch (from exclusive holder), sends ack with data
def recvFetchState {n} (s : MState n) (i : Fin n) : MState n :=
  { s with
    cache   := setFn s.cache   i { (s.cache i) with state := .I }
    c2dChan := setFn s.c2dChan i { cmd := .ack, data := (s.cache i).data }
    d2cChan := setFn s.d2cChan i {} }

-- Action 15: directory receives ack in GetM/Shared context — clears ack and shrSet entry
def recvAck_GetM_SharedState {n} (s : MState n) (j : Fin n) : MState n :=
  { s with
    c2dChan := setFn s.c2dChan j {}
    shrSet  := setFn s.shrSet j false }

-- Action 16a: directory receives writeback ack from old M-holder (GetM/Exclusive case)
--   Writes data to memory, becomes Uncached. curCmd stays getM — grant sent separately.
def recvAck_GetM_ExclusiveState {n} (s : MState n) (j : Fin n) : MState n :=
  { s with
    memData := (s.c2dChan j).data
    auxData := (s.c2dChan j).data
    c2dChan := setFn s.c2dChan j {}
    dirSt   := .Uncached }

-- Action 16b: directory sends gntE to new requester after exclusive writeback
def sendGntE_AfterExclusiveState {n} (s : MState n) : MState n :=
  { s with
    d2cChan := setFn s.d2cChan s.curNode { cmd := .gntE, data := s.memData }
    dirSt   := .Exclusive
    exNode  := s.curNode
    curCmd  := .empty }

-- Action 17a: directory receives fetch ack from old M-holder (GetS/Exclusive case)
--   Writes data to memory, becomes Uncached. curCmd stays getS — grant sent separately.
def recvAck_GetSState {n} (s : MState n) (j : Fin n) : MState n :=
  { s with
    memData := (s.c2dChan j).data
    auxData := (s.c2dChan j).data
    c2dChan := setFn s.c2dChan j {}
    dirSt   := .Uncached }

-- Action 17b: directory sends gntS to pending GetS requester after fetch writeback
def sendGntS_AfterFetchState {n} (s : MState n) : MState n :=
  { s with
    d2cChan := setFn s.d2cChan s.curNode { cmd := .gntS, data := s.memData }
    dirSt   := .Shared
    shrSet  := setFn s.shrSet s.curNode true
    curCmd  := .empty }

-- ── Auto-generated frame simp-lemmas ─────────────────────────────────────

#gen_frame_lemmas recvGetS_UncachedState
#gen_frame_lemmas recvGetS_SharedState
#gen_frame_lemmas recvGetS_ExclusiveState
#gen_frame_lemmas recvGetM_UncachedState
#gen_frame_lemmas recvGetM_SharedState
#gen_frame_lemmas recvGetM_ExclusiveState
#gen_frame_lemmas sendInvState
#gen_frame_lemmas sendGntE_AfterSharedState
#gen_frame_lemmas recvGntSState
#gen_frame_lemmas recvGntEState
#gen_frame_lemmas recvInvState
#gen_frame_lemmas recvFetchState
#gen_frame_lemmas recvAck_GetM_SharedState
#gen_frame_lemmas recvAck_GetM_ExclusiveState
#gen_frame_lemmas recvAck_GetSState
#gen_frame_lemmas sendGntE_AfterExclusiveState
#gen_frame_lemmas sendGntS_AfterFetchState

-- ── Manual lemmas for cases not yet handled by #gen_frame_lemmas ─────────

-- Cross-field assignment: invSet := setFn s.shrSet i false (reads shrSet, not invSet)
@[simp] theorem recvGetM_SharedState_invSet_ne {n} (s : MState n) (i j : Fin n) (h : j ≠ i) :
    (recvGetM_SharedState s i).invSet j = s.shrSet j := by simp [recvGetM_SharedState, h]

-- Nested field lemmas: cache state/data when setFn updates a sub-structure
@[simp] theorem recvGntSState_cache_state_self {n} (s : MState n) (i) : ((recvGntSState s i).cache i).state = .S := by simp [recvGntSState]
@[simp] theorem recvGntSState_cache_data_self  {n} (s : MState n) (i) : ((recvGntSState s i).cache i).data  = (s.d2cChan i).data := by simp [recvGntSState]
@[simp] theorem recvGntSState_cache_state_ne   {n} (s : MState n) (i j : Fin n) (h : j ≠ i) : ((recvGntSState s i).cache j).state = (s.cache j).state := by simp [recvGntSState, h]
@[simp] theorem recvGntSState_cache_data_ne    {n} (s : MState n) (i j : Fin n) (h : j ≠ i) : ((recvGntSState s i).cache j).data  = (s.cache j).data  := by simp [recvGntSState, h]

@[simp] theorem recvGntEState_cache_state_self {n} (s : MState n) (i) : ((recvGntEState s i).cache i).state = .M := by simp [recvGntEState]
@[simp] theorem recvGntEState_cache_data_self  {n} (s : MState n) (i) : ((recvGntEState s i).cache i).data  = (s.d2cChan i).data := by simp [recvGntEState]
@[simp] theorem recvGntEState_cache_state_ne   {n} (s : MState n) (i j : Fin n) (h : j ≠ i) : ((recvGntEState s i).cache j).state = (s.cache j).state := by simp [recvGntEState, h]
@[simp] theorem recvGntEState_cache_data_ne    {n} (s : MState n) (i j : Fin n) (h : j ≠ i) : ((recvGntEState s i).cache j).data  = (s.cache j).data  := by simp [recvGntEState, h]

@[simp] theorem recvInvState_cache_state_self {n} (s : MState n) (i) : ((recvInvState s i).cache i).state = .I := by simp [recvInvState]
@[simp] theorem recvInvState_cache_data_self  {n} (s : MState n) (i) : ((recvInvState s i).cache i).data  = (s.cache i).data := by simp [recvInvState]
@[simp] theorem recvInvState_cache_state_ne   {n} (s : MState n) (i j : Fin n) (h : j ≠ i) : ((recvInvState s i).cache j).state = (s.cache j).state := by simp [recvInvState, h]
@[simp] theorem recvInvState_cache_data_ne    {n} (s : MState n) (i j : Fin n) (h : j ≠ i) : ((recvInvState s i).cache j).data  = (s.cache j).data  := by simp [recvInvState, h]

@[simp] theorem recvFetchState_cache_state_self {n} (s : MState n) (i) : ((recvFetchState s i).cache i).state = .I := by simp [recvFetchState]
@[simp] theorem recvFetchState_cache_data_self  {n} (s : MState n) (i) : ((recvFetchState s i).cache i).data  = (s.cache i).data := by simp [recvFetchState]
@[simp] theorem recvFetchState_cache_state_ne   {n} (s : MState n) (i j : Fin n) (h : j ≠ i) : ((recvFetchState s i).cache j).state = (s.cache j).state := by simp [recvFetchState, h]
@[simp] theorem recvFetchState_cache_data_ne    {n} (s : MState n) (i j : Fin n) (h : j ≠ i) : ((recvFetchState s i).cache j).data  = (s.cache j).data  := by simp [recvFetchState, h]

-- ── Actions ───────────────────────────────────────────────────────────────

-- 1. Processor sends GetS (cache is in I, reqChan is empty)
def SendGetS (s s' : MState n) (i : Fin n) : Prop :=
  (s.reqChan i).cmd = .empty ∧
  (s.cache i).state = .I ∧
  s' = { s with reqChan := setFn s.reqChan i { cmd := .getS } }

-- 2. Processor sends GetM (cache is not in M, reqChan is empty)
def SendGetM (s s' : MState n) (i : Fin n) : Prop :=
  (s.reqChan i).cmd = .empty ∧
  (s.cache i).state ≠ .M ∧
  s' = { s with reqChan := setFn s.reqChan i { cmd := .getM } }

-- 3. Directory processes GetS when Uncached — immediately grants S
def RecvGetS_Uncached (s s' : MState n) (i : Fin n) : Prop :=
  (s.reqChan i).cmd = .getS ∧
  s.curCmd = .empty ∧
  s.dirSt = .Uncached ∧
  (s.d2cChan i).cmd = .empty ∧
  s' = recvGetS_UncachedState s i

-- 4. Directory processes GetS when Shared — grants another S
def RecvGetS_Shared (s s' : MState n) (i : Fin n) : Prop :=
  (s.reqChan i).cmd = .getS ∧
  s.curCmd = .empty ∧
  s.dirSt = .Shared ∧
  (s.d2cChan i).cmd = .empty ∧
  s' = recvGetS_SharedState s i

-- 5. Directory processes GetS when Exclusive — fetches data from exclusive holder
def RecvGetS_Exclusive (s s' : MState n) (i : Fin n) : Prop :=
  (s.reqChan i).cmd = .getS ∧
  s.curCmd = .empty ∧
  s.dirSt = .Exclusive ∧
  (s.d2cChan s.exNode).cmd = .empty ∧
  s' = recvGetS_ExclusiveState s i

-- 6. Directory processes GetM when Uncached — immediately grants E
def RecvGetM_Uncached (s s' : MState n) (i : Fin n) : Prop :=
  (s.reqChan i).cmd = .getM ∧
  s.curCmd = .empty ∧
  s.dirSt = .Uncached ∧
  (s.d2cChan i).cmd = .empty ∧
  s' = recvGetM_UncachedState s i

-- 7. Directory processes GetM when Shared — start sending invalidations
def RecvGetM_Shared (s s' : MState n) (i : Fin n) : Prop :=
  (s.reqChan i).cmd = .getM ∧
  s.curCmd = .empty ∧
  s.dirSt = .Shared ∧
  s' = recvGetM_SharedState s i

-- 8. Directory processes GetM when Exclusive — invalidate current exclusive holder
def RecvGetM_Exclusive (s s' : MState n) (i : Fin n) : Prop :=
  (s.reqChan i).cmd = .getM ∧
  s.curCmd = .empty ∧
  s.dirSt = .Exclusive ∧
  s.exNode ≠ i ∧
  (s.d2cChan s.exNode).cmd = .empty ∧
  s' = recvGetM_ExclusiveState s i

-- 9. Directory sends a pending invalidation
def SendInv (s s' : MState n) (j : Fin n) : Prop :=
  s.invSet j = true ∧
  (s.d2cChan j).cmd = .empty ∧
  s' = sendInvState s j

-- 10. After all sharer acks received (shrSet fully cleared), grant E to curNode
def SendGntE_AfterShared (s s' : MState n) : Prop :=
  s.curCmd = .getM ∧
  s.dirSt = .Shared ∧
  (∀ j : Fin n, s.shrSet j = false) ∧
  (∀ j : Fin n, s.invSet j = false) ∧
  (s.d2cChan s.curNode).cmd = .empty ∧
  s' = sendGntE_AfterSharedState s

-- 11. Cache receives gntS
def RecvGntS (s s' : MState n) (i : Fin n) : Prop :=
  (s.d2cChan i).cmd = .gntS ∧
  s' = recvGntSState s i

-- 12. Cache receives gntE
def RecvGntE (s s' : MState n) (i : Fin n) : Prop :=
  (s.d2cChan i).cmd = .gntE ∧
  s' = recvGntEState s i

-- 13. Cache receives inv, sends ack carrying data
def RecvInv (s s' : MState n) (i : Fin n) : Prop :=
  (s.d2cChan i).cmd = .inv ∧
  (s.c2dChan i).cmd = .empty ∧
  s' = recvInvState s i

-- 14. Cache receives fetch (exclusive → I, send ack with data)
def RecvFetch (s s' : MState n) (i : Fin n) : Prop :=
  (s.d2cChan i).cmd = .fetch ∧
  (s.c2dChan i).cmd = .empty ∧
  s' = recvFetchState s i

-- 15. Directory receives ack in GetM/Shared context
def RecvAck_GetM_Shared (s s' : MState n) (j : Fin n) : Prop :=
  (s.c2dChan j).cmd = .ack ∧
  s.curCmd = .getM ∧
  s.dirSt = .Shared ∧
  s' = recvAck_GetM_SharedState s j

-- 16a. Directory receives writeback ack from old M-holder (GetM/Exclusive case)
def RecvAck_GetM_Exclusive (s s' : MState n) (j : Fin n) : Prop :=
  (s.c2dChan j).cmd = .ack ∧
  s.curCmd = .getM ∧
  s.dirSt = .Exclusive ∧
  s' = recvAck_GetM_ExclusiveState s j

-- 16b. Directory sends gntE to new requester after exclusive writeback received
def SendGntE_AfterExclusive (s s' : MState n) : Prop :=
  s.curCmd = .getM ∧
  s.dirSt = .Uncached ∧
  (s.d2cChan s.curNode).cmd = .empty ∧
  s' = sendGntE_AfterExclusiveState s

-- 17a. Directory receives fetch ack from old M-holder (GetS/Exclusive case)
def RecvAck_GetS (s s' : MState n) (j : Fin n) : Prop :=
  (s.c2dChan j).cmd = .ack ∧
  s.curCmd = .getS ∧
  s' = recvAck_GetSState s j

-- 17b. Directory sends gntS to pending requester after fetch writeback received
def SendGntS_AfterFetch (s s' : MState n) : Prop :=
  s.curCmd = .getS ∧
  s.dirSt = .Uncached ∧
  (s.d2cChan s.curNode).cmd = .empty ∧
  s' = sendGntS_AfterFetchState s

-- ── Initial state ─────────────────────────────────────────────────────────

def init (n : Nat) (s : MState n) : Prop :=
  (∀ i, s.cache   i = {}) ∧
  (∀ i, s.reqChan i = {}) ∧
  (∀ i, s.d2cChan i = {}) ∧
  (∀ i, s.c2dChan i = {}) ∧
  s.dirSt  = .Uncached ∧
  (∀ i, s.shrSet i = false) ∧
  (∀ i, s.invSet i = false) ∧
  s.curCmd  = .empty ∧
  s.memData = s.auxData

-- ── Transition relation ───────────────────────────────────────────────────

def next (n : Nat) (s s' : MState n) : Prop :=
  (∃ i, SendGetS s s' i) ∨
  (∃ i, SendGetM s s' i) ∨
  (∃ i, RecvGetS_Uncached s s' i) ∨
  (∃ i, RecvGetS_Shared s s' i) ∨
  (∃ i, RecvGetS_Exclusive s s' i) ∨
  (∃ i, RecvGetM_Uncached s s' i) ∨
  (∃ i, RecvGetM_Shared s s' i) ∨
  (∃ i, RecvGetM_Exclusive s s' i) ∨
  (∃ j, SendInv s s' j) ∨
  SendGntE_AfterShared s s' ∨
  (∃ i, RecvGntS s s' i) ∨
  (∃ i, RecvGntE s s' i) ∨
  (∃ i, RecvInv s s' i) ∨
  (∃ i, RecvFetch s s' i) ∨
  (∃ j, RecvAck_GetM_Shared s s' j) ∨
  (∃ j, RecvAck_GetM_Exclusive s s' j) ∨
  SendGntE_AfterExclusive s s' ∨
  (∃ j, RecvAck_GetS s s' j) ∨
  SendGntS_AfterFetch s s'

def directoryMSISpec (n : Nat) : Spec (MState n) where
  init := init n
  next := next n
  fair := []

end DirectoryMSI
