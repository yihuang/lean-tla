import Leslie.Action
import Leslie.Gadgets.SetFn

open TLA

/-! ## German Cache Coherence Protocol — Model

    Types, state, actions, init, and transition relation.
    No proofs. Imported by all other files in this module.
-/

namespace GermanMessages

abbrev Val := Nat

inductive CacheState where
  | I | S | E
  deriving DecidableEq, Repr, BEq

inductive MsgCmd where
  | empty | reqS | reqE | inv | invAck | gntS | gntE
  deriving DecidableEq, Repr, BEq

structure CacheLine where
  state : CacheState
  data  : Val
  deriving DecidableEq, Repr

structure Msg where
  cmd  : MsgCmd
  data : Val
  deriving DecidableEq, Repr

structure MState (n : Nat) where
  cache   : Fin n → CacheLine
  chan1   : Fin n → Msg
  chan2   : Fin n → Msg
  chan3   : Fin n → Msg
  invSet  : Fin n → Bool
  shrSet  : Fin n → Bool
  exGntd  : Bool
  curCmd  : MsgCmd
  curPtr  : Fin n
  memData : Val
  auxData : Val

inductive MAction (n : Nat) where
  | sendReqS  (i : Fin n)
  | sendReqE  (i : Fin n)
  | recvReqS  (i : Fin n)
  | recvReqE  (i : Fin n)
  | sendInv   (i : Fin n)
  | sendInvAck (i : Fin n)
  | recvInvAck (i : Fin n)
  | sendGntS  (i : Fin n)
  | sendGntE  (i : Fin n)
  | recvGntS  (i : Fin n)
  | recvGntE  (i : Fin n)
  | store     (i : Fin n) (d : Val)
  deriving DecidableEq

-- ── Named state-transformer helpers ───────────────────────────────────────

def recvGntEState {n} (s : MState n) (i : Fin n) : MState n :=
  { s with
    cache := setFn s.cache i { state := .E, data := (s.chan2 i).data }
    chan2  := setFn s.chan2 i { (s.chan2 i) with cmd := .empty } }

def sendInvAckState {n} (s : MState n) (i : Fin n) : MState n :=
  { s with
    chan2  := setFn s.chan2 i { (s.chan2 i) with cmd := .empty }
    chan3  := setFn s.chan3 i
               { cmd  := .invAck
               , data := if (s.cache i).state = .E then (s.cache i).data
                         else (s.chan3 i).data }
    cache  := setFn s.cache i { (s.cache i) with state := .I } }

def storeState {n} (s : MState n) (i : Fin n) (d : Val) : MState n :=
  { s with
    cache   := setFn s.cache i { (s.cache i) with data := d }
    auxData := d }

-- ── Frame simp-lemmas for recvGntEState ──────────────────────────────────

@[simp] theorem recvGntEState_exGntd  {n} (s : MState n) (i) : (recvGntEState s i).exGntd  = s.exGntd  := rfl
@[simp] theorem recvGntEState_shrSet  {n} (s : MState n) (i) : (recvGntEState s i).shrSet  = s.shrSet  := rfl
@[simp] theorem recvGntEState_memData {n} (s : MState n) (i) : (recvGntEState s i).memData = s.memData := rfl
@[simp] theorem recvGntEState_auxData {n} (s : MState n) (i) : (recvGntEState s i).auxData = s.auxData := rfl
@[simp] theorem recvGntEState_chan1   {n} (s : MState n) (i) : (recvGntEState s i).chan1    = s.chan1   := rfl
@[simp] theorem recvGntEState_chan3   {n} (s : MState n) (i) : (recvGntEState s i).chan3    = s.chan3   := rfl
@[simp] theorem recvGntEState_invSet  {n} (s : MState n) (i) : (recvGntEState s i).invSet  = s.invSet  := rfl
@[simp] theorem recvGntEState_curCmd  {n} (s : MState n) (i) : (recvGntEState s i).curCmd  = s.curCmd  := rfl
@[simp] theorem recvGntEState_curPtr  {n} (s : MState n) (i) : (recvGntEState s i).curPtr  = s.curPtr  := rfl

@[simp] theorem recvGntEState_cache_state_other {n} (s : MState n) {i j : Fin n} (h : j ≠ i) :
    ((recvGntEState s i).cache j).state = (s.cache j).state := by simp [recvGntEState, h]
@[simp] theorem recvGntEState_cache_data_other  {n} (s : MState n) {i j : Fin n} (h : j ≠ i) :
    ((recvGntEState s i).cache j).data  = (s.cache j).data  := by simp [recvGntEState, h]
@[simp] theorem recvGntEState_chan2_cmd_other   {n} (s : MState n) {i j : Fin n} (h : j ≠ i) :
    ((recvGntEState s i).chan2 j).cmd   = (s.chan2 j).cmd    := by simp [recvGntEState, h]
@[simp] theorem recvGntEState_cache_state_self  {n} (s : MState n) (i : Fin n) :
    ((recvGntEState s i).cache i).state = .E                 := by simp [recvGntEState]
@[simp] theorem recvGntEState_cache_data_self   {n} (s : MState n) (i : Fin n) :
    ((recvGntEState s i).cache i).data  = (s.chan2 i).data   := by simp [recvGntEState]
@[simp] theorem recvGntEState_chan2_cmd_self    {n} (s : MState n) (i : Fin n) :
    ((recvGntEState s i).chan2 i).cmd   = .empty              := by simp [recvGntEState]

-- ── Frame simp-lemmas for sendInvAckState ────────────────────────────────

@[simp] theorem sendInvAckState_exGntd  {n} (s : MState n) (i) : (sendInvAckState s i).exGntd  = s.exGntd  := rfl
@[simp] theorem sendInvAckState_shrSet  {n} (s : MState n) (i) : (sendInvAckState s i).shrSet  = s.shrSet  := rfl
@[simp] theorem sendInvAckState_invSet  {n} (s : MState n) (i) : (sendInvAckState s i).invSet  = s.invSet  := rfl
@[simp] theorem sendInvAckState_curCmd  {n} (s : MState n) (i) : (sendInvAckState s i).curCmd  = s.curCmd  := rfl
@[simp] theorem sendInvAckState_curPtr  {n} (s : MState n) (i) : (sendInvAckState s i).curPtr  = s.curPtr  := rfl
@[simp] theorem sendInvAckState_memData {n} (s : MState n) (i) : (sendInvAckState s i).memData = s.memData := rfl
@[simp] theorem sendInvAckState_auxData {n} (s : MState n) (i) : (sendInvAckState s i).auxData = s.auxData := rfl
@[simp] theorem sendInvAckState_chan1   {n} (s : MState n) (i) : (sendInvAckState s i).chan1    = s.chan1   := rfl

@[simp] theorem sendInvAckState_cache_state_self  {n} (s : MState n) (i) :
    ((sendInvAckState s i).cache i).state = .I := by simp [sendInvAckState]
@[simp] theorem sendInvAckState_cache_state_other {n} (s : MState n) {i j : Fin n} (h : j ≠ i) :
    ((sendInvAckState s i).cache j).state = (s.cache j).state := by simp [sendInvAckState, h]
@[simp] theorem sendInvAckState_chan2_cmd_self     {n} (s : MState n) (i) :
    ((sendInvAckState s i).chan2 i).cmd = .empty := by simp [sendInvAckState]
@[simp] theorem sendInvAckState_chan2_cmd_other    {n} (s : MState n) {i j : Fin n} (h : j ≠ i) :
    ((sendInvAckState s i).chan2 j).cmd = (s.chan2 j).cmd := by simp [sendInvAckState, h]
@[simp] theorem sendInvAckState_chan3_cmd_self     {n} (s : MState n) (i) :
    ((sendInvAckState s i).chan3 i).cmd = .invAck := by simp [sendInvAckState]
@[simp] theorem sendInvAckState_chan3_cmd_other    {n} (s : MState n) {i j : Fin n} (h : j ≠ i) :
    ((sendInvAckState s i).chan3 j).cmd = (s.chan3 j).cmd := by simp [sendInvAckState, h]

-- ── Frame simp-lemmas for storeState ────────────────────────────────────

@[simp] theorem storeState_exGntd  {n} (s : MState n) (i) (d) : (storeState s i d).exGntd  = s.exGntd  := rfl
@[simp] theorem storeState_shrSet  {n} (s : MState n) (i) (d) : (storeState s i d).shrSet  = s.shrSet  := rfl
@[simp] theorem storeState_memData {n} (s : MState n) (i) (d) : (storeState s i d).memData = s.memData := rfl
@[simp] theorem storeState_chan1   {n} (s : MState n) (i) (d) : (storeState s i d).chan1    = s.chan1   := rfl
@[simp] theorem storeState_chan2   {n} (s : MState n) (i) (d) : (storeState s i d).chan2    = s.chan2   := rfl
@[simp] theorem storeState_chan3   {n} (s : MState n) (i) (d) : (storeState s i d).chan3    = s.chan3   := rfl
@[simp] theorem storeState_invSet  {n} (s : MState n) (i) (d) : (storeState s i d).invSet  = s.invSet  := rfl
@[simp] theorem storeState_curCmd  {n} (s : MState n) (i) (d) : (storeState s i d).curCmd  = s.curCmd  := rfl
@[simp] theorem storeState_curPtr  {n} (s : MState n) (i) (d) : (storeState s i d).curPtr  = s.curPtr  := rfl

@[simp] theorem storeState_cache_state_self  {n} (s : MState n) (i) (d) :
    ((storeState s i d).cache i).state = (s.cache i).state := by simp [storeState]
@[simp] theorem storeState_cache_data_self   {n} (s : MState n) (i) (d) :
    ((storeState s i d).cache i).data  = d                 := by simp [storeState]
@[simp] theorem storeState_cache_state_other {n} (s : MState n) {i j : Fin n} (d) (h : j ≠ i) :
    ((storeState s i d).cache j).state = (s.cache j).state := by simp [storeState, h]
@[simp] theorem storeState_cache_data_other  {n} (s : MState n) {i j : Fin n} (d) (h : j ≠ i) :
    ((storeState s i d).cache j).data  = (s.cache j).data  := by simp [storeState, h]

-- ── Initial state ─────────────────────────────────────────────────────────

def init (n : Nat) : MState n → Prop := fun s =>
  (∀ i, s.cache  i = { state := .I, data := 1 }) ∧
  (∀ i, s.chan1  i = { cmd := .empty, data := 1 }) ∧
  (∀ i, s.chan2  i = { cmd := .empty, data := 1 }) ∧
  (∀ i, s.chan3  i = { cmd := .empty, data := 1 }) ∧
  (∀ i, s.invSet i = false) ∧
  (∀ i, s.shrSet i = false) ∧
  s.exGntd  = false ∧
  s.curCmd  = .empty ∧
  s.memData = 1 ∧
  s.auxData = 1

-- ── Transition relation ───────────────────────────────────────────────────

def next (n : Nat) : MState n → MState n → Prop := fun s s' =>
  ∃ a : MAction n, match a with
  | .sendReqS i =>
      (s.chan1 i).cmd = .empty ∧ (s.cache i).state = .I ∧
      s' = { s with chan1 := setFn s.chan1 i { (s.chan1 i) with cmd := .reqS } }
  | .sendReqE i =>
      (s.chan1 i).cmd = .empty ∧ ((s.cache i).state = .I ∨ (s.cache i).state = .S) ∧
      s' = { s with chan1 := setFn s.chan1 i { (s.chan1 i) with cmd := .reqE } }
  | .recvReqS i =>
      s.curCmd = .empty ∧ (s.chan1 i).cmd = .reqS ∧
      s' = { s with curCmd := .reqS
                    curPtr := i
                    chan1 := setFn s.chan1 i { (s.chan1 i) with cmd := .empty }
                    invSet := fun j => s.shrSet j }
  | .recvReqE i =>
      s.curCmd = .empty ∧ (s.chan1 i).cmd = .reqE ∧
      s' = { s with curCmd := .reqE
                    curPtr := i
                    chan1 := setFn s.chan1 i { (s.chan1 i) with cmd := .empty }
                    invSet := fun j => s.shrSet j }
  | .sendInv i =>
      (s.chan2 i).cmd = .empty ∧ s.invSet i = true ∧
      (s.curCmd = .reqE ∨ (s.curCmd = .reqS ∧ s.exGntd = true)) ∧
      s' = { s with chan2 := setFn s.chan2 i { (s.chan2 i) with cmd := .inv }
                    invSet := setFn s.invSet i false }
  | .sendInvAck i =>
      (s.chan2 i).cmd = .inv ∧ (s.chan3 i).cmd = .empty ∧
      s' = sendInvAckState s i
  | .recvInvAck i =>
      (s.chan3 i).cmd = .invAck ∧ s.curCmd ≠ .empty ∧
      (((s.exGntd = true) ∧
        s' = { s with chan3 := setFn s.chan3 i { (s.chan3 i) with cmd := .empty }
                      shrSet := setFn s.shrSet i false
                      exGntd := false
                      memData := (s.chan3 i).data }) ∨
       ((s.exGntd = false) ∧
        s' = { s with chan3 := setFn s.chan3 i { (s.chan3 i) with cmd := .empty }
                      shrSet := setFn s.shrSet i false }))
  | .sendGntS i =>
      s.curCmd = .reqS ∧ s.curPtr = i ∧ (s.chan2 i).cmd = .empty ∧ s.exGntd = false ∧
      s' = { s with chan2 := setFn s.chan2 i { cmd := .gntS, data := s.memData }
                    shrSet := setFn s.shrSet i true
                    curCmd := .empty }
  | .sendGntE i =>
      s.curCmd = .reqE ∧ s.curPtr = i ∧ (s.chan2 i).cmd = .empty ∧ s.exGntd = false ∧
      (∀ j, s.shrSet j = false) ∧
      s' = { s with chan2 := setFn s.chan2 i { cmd := .gntE, data := s.memData }
                    shrSet := setFn s.shrSet i true
                    exGntd := true
                    curCmd := .empty }
  | .recvGntS i =>
      (s.chan2 i).cmd = .gntS ∧
      s' = { s with cache := setFn s.cache i { state := .S, data := (s.chan2 i).data }
                    chan2 := setFn s.chan2 i { (s.chan2 i) with cmd := .empty } }
  | .recvGntE i =>
      (s.chan2 i).cmd = .gntE ∧ s' = recvGntEState s i
  | .store i d =>
      (s.cache i).state = .E ∧ s' = storeState s i d

def germanMessagesSpec (n : Nat) : Spec (MState n) where
  init := init n
  next := next n
  fair := []

end GermanMessages
