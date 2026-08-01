import Leslie.Action
import Leslie.Gadgets.SetFn

open TLA

/-! ## German Cache Coherence Protocol with Explicit Messages

    This file encodes a message-level version of German's cache coherence
    protocol, closely following the TLA model supplied by the user.

    Compared with `German.lean`, this model makes the protocol's control flow
    more explicit:

    - requests are sent on `chan1` and later received by the directory
    - invalidations are sent on `chan2` and later acknowledged on `chan3`
    - grants are sent and later consumed as separate steps
    - directory bookkeeping state (`invSet`, `shrSet`, `exGntd`, `curCmd`,
      `curPtr`) is explicit in the state

    The result is a less atomic model that better reflects the message / ack
    structure of an implementation.

    This file currently includes:

    - the faithful transition-system model
    - the TLA-style safety predicates (`ctrlProp`, `dataProp`, `invariant`)
    - a stronger bookkeeping invariant (`strongInvariant`) that is intended as
      the right inductive proof target for the finer-grained protocol
-/

namespace GermanMessages

abbrev Val := Nat

inductive CacheState where
  | I
  | S
  | E
  deriving DecidableEq, Repr, BEq

inductive MsgCmd where
  | empty
  | reqS
  | reqE
  | inv
  | invAck
  | gntS
  | gntE
  deriving DecidableEq, Repr, BEq

structure CacheLine where
  state : CacheState
  data : Val
  deriving DecidableEq, Repr

structure Msg where
  cmd : MsgCmd
  data : Val
  deriving DecidableEq, Repr

structure MState (n : Nat) where
  cache : Fin n → CacheLine
  chan1 : Fin n → Msg
  chan2 : Fin n → Msg
  chan3 : Fin n → Msg
  invSet : Fin n → Bool
  shrSet : Fin n → Bool
  exGntd : Bool
  curCmd : MsgCmd
  curPtr : Fin n
  memData : Val
  auxData : Val

inductive MAction (n : Nat) where
  | sendReqS (i : Fin n)
  | sendReqE (i : Fin n)
  | recvReqS (i : Fin n)
  | recvReqE (i : Fin n)
  | sendInv (i : Fin n)
  | sendInvAck (i : Fin n)
  | recvInvAck (i : Fin n)
  | sendGntS (i : Fin n)
  | sendGntE (i : Fin n)
  | recvGntS (i : Fin n)
  | recvGntE (i : Fin n)
  | store (i : Fin n) (d : Val)
  deriving DecidableEq


@[simp] theorem cache_set_other {n : Nat} (cache : Fin n → CacheLine) {i j : Fin n} (line : CacheLine)
    (h : j ≠ i) : (setFn cache i line j).state = (cache j).state := by
  simp [setFn_ne, h]

@[simp] theorem cache_data_set_other {n : Nat} (cache : Fin n → CacheLine) {i j : Fin n} (line : CacheLine)
    (h : j ≠ i) : (setFn cache i line j).data = (cache j).data := by
  simp [setFn_ne, h]

@[simp] theorem msg_cmd_set_other {n : Nat} (ch : Fin n → Msg) {i j : Fin n} (msg : Msg)
    (h : j ≠ i) : (setFn ch i msg j).cmd = (ch j).cmd := by
  simp [setFn_ne, h]

@[simp] theorem msg_data_set_other {n : Nat} (ch : Fin n → Msg) {i j : Fin n} (msg : Msg)
    (h : j ≠ i) : (setFn ch i msg j).data = (ch j).data := by
  simp [setFn_ne, h]

@[simp] theorem cache_state_store_self {n : Nat} (cache : Fin n → CacheLine) (i : Fin n) (d : Val) :
    (setFn cache i { (cache i) with data := d } i).state = (cache i).state := by
  simp [setFn]

@[simp] theorem cache_data_store_self {n : Nat} (cache : Fin n → CacheLine) (i : Fin n) (d : Val) :
    (setFn cache i { (cache i) with data := d } i).data = d := by
  simp [setFn]

def recvGntEState {n : Nat} (s : MState n) (i : Fin n) : MState n :=
  { s with
    cache := setFn s.cache i { state := .E, data := (s.chan2 i).data }
    chan2 := setFn s.chan2 i { (s.chan2 i) with cmd := .empty } }

def sendInvAckState {n : Nat} (s : MState n) (i : Fin n) : MState n :=
  { s with
    chan2 := setFn s.chan2 i { (s.chan2 i) with cmd := .empty }
    chan3 := setFn s.chan3 i
      { cmd := .invAck
      , data := if (s.cache i).state = .E then (s.cache i).data else (s.chan3 i).data }
    cache := setFn s.cache i { (s.cache i) with state := .I } }

def storeState {n : Nat} (s : MState n) (i : Fin n) (d : Val) : MState n :=
  { s with
    cache := setFn s.cache i { (s.cache i) with data := d }
    auxData := d }

@[simp] theorem recvGntEState_exGntd {n : Nat} (s : MState n) (i : Fin n) :
    (recvGntEState s i).exGntd = s.exGntd := rfl

@[simp] theorem recvGntEState_shrSet {n : Nat} (s : MState n) (i : Fin n) :
    (recvGntEState s i).shrSet = s.shrSet := rfl

@[simp] theorem recvGntEState_memData {n : Nat} (s : MState n) (i : Fin n) :
    (recvGntEState s i).memData = s.memData := rfl

@[simp] theorem recvGntEState_auxData {n : Nat} (s : MState n) (i : Fin n) :
    (recvGntEState s i).auxData = s.auxData := rfl

@[simp] theorem recvGntEState_cache_state_other {n : Nat} (s : MState n) {i j : Fin n} (h : j ≠ i) :
    ((recvGntEState s i).cache j).state = (s.cache j).state := by
  simp [recvGntEState, h]

@[simp] theorem recvGntEState_cache_data_other {n : Nat} (s : MState n) {i j : Fin n} (h : j ≠ i) :
    ((recvGntEState s i).cache j).data = (s.cache j).data := by
  simp [recvGntEState, h]

@[simp] theorem recvGntEState_chan2_cmd_other {n : Nat} (s : MState n) {i j : Fin n} (h : j ≠ i) :
    ((recvGntEState s i).chan2 j).cmd = (s.chan2 j).cmd := by
  simp [recvGntEState, h]

@[simp] theorem recvGntEState_cache_state_self {n : Nat} (s : MState n) (i : Fin n) :
    ((recvGntEState s i).cache i).state = .E := by
  simp [recvGntEState]

@[simp] theorem recvGntEState_cache_data_self {n : Nat} (s : MState n) (i : Fin n) :
    ((recvGntEState s i).cache i).data = (s.chan2 i).data := by
  simp [recvGntEState]

@[simp] theorem recvGntEState_chan2_cmd_self {n : Nat} (s : MState n) (i : Fin n) :
    ((recvGntEState s i).chan2 i).cmd = .empty := by
  simp [recvGntEState]

@[simp] theorem sendInvAckState_cache_state_self {n : Nat} (s : MState n) (i : Fin n) :
    ((sendInvAckState s i).cache i).state = .I := by
  simp [sendInvAckState]

@[simp] theorem sendInvAckState_cache_state_other {n : Nat} (s : MState n) {i j : Fin n} (h : j ≠ i) :
    ((sendInvAckState s i).cache j).state = (s.cache j).state := by
  simp [sendInvAckState, h]

@[simp] theorem sendInvAckState_chan2_cmd_self {n : Nat} (s : MState n) (i : Fin n) :
    ((sendInvAckState s i).chan2 i).cmd = .empty := by
  simp [sendInvAckState]

@[simp] theorem sendInvAckState_chan2_cmd_other {n : Nat} (s : MState n) {i j : Fin n} (h : j ≠ i) :
    ((sendInvAckState s i).chan2 j).cmd = (s.chan2 j).cmd := by
  simp [sendInvAckState, h]

@[simp] theorem sendInvAckState_chan3_cmd_self {n : Nat} (s : MState n) (i : Fin n) :
    ((sendInvAckState s i).chan3 i).cmd = .invAck := by
  simp [sendInvAckState]

@[simp] theorem sendInvAckState_chan3_cmd_other {n : Nat} (s : MState n) {i j : Fin n} (h : j ≠ i) :
    ((sendInvAckState s i).chan3 j).cmd = (s.chan3 j).cmd := by
  simp [sendInvAckState, h]

@[simp] theorem storeState_exGntd {n : Nat} (s : MState n) (i : Fin n) (d : Val) :
    (storeState s i d).exGntd = s.exGntd := rfl

@[simp] theorem storeState_shrSet {n : Nat} (s : MState n) (i : Fin n) (d : Val) :
    (storeState s i d).shrSet = s.shrSet := rfl

@[simp] theorem storeState_memData {n : Nat} (s : MState n) (i : Fin n) (d : Val) :
    (storeState s i d).memData = s.memData := rfl

@[simp] theorem storeState_cache_state_other {n : Nat} (s : MState n) {i j : Fin n} (d : Val) (h : j ≠ i) :
    ((storeState s i d).cache j).state = (s.cache j).state := by
  simp [storeState, h]

@[simp] theorem storeState_cache_data_other {n : Nat} (s : MState n) {i j : Fin n} (d : Val) (h : j ≠ i) :
    ((storeState s i d).cache j).data = (s.cache j).data := by
  simp [storeState, h]

def init (n : Nat) : MState n → Prop :=
  fun s =>
    (∀ i, s.cache i = { state := .I, data := 1 }) ∧
    (∀ i, s.chan1 i = { cmd := .empty, data := 1 }) ∧
    (∀ i, s.chan2 i = { cmd := .empty, data := 1 }) ∧
    (∀ i, s.chan3 i = { cmd := .empty, data := 1 }) ∧
    (∀ i, s.invSet i = false) ∧
    (∀ i, s.shrSet i = false) ∧
    s.exGntd = false ∧
    s.curCmd = .empty ∧
    s.memData = 1 ∧
    s.auxData = 1

def next (n : Nat) : MState n → MState n → Prop :=
  fun s s' =>
    ∃ a : MAction n,
      match a with
      | .sendReqS i =>
          (s.chan1 i).cmd = .empty ∧
          (s.cache i).state = .I ∧
          s' = { s with chan1 := setFn s.chan1 i { (s.chan1 i) with cmd := .reqS } }
      | .sendReqE i =>
          (s.chan1 i).cmd = .empty ∧
          ((s.cache i).state = .I ∨ (s.cache i).state = .S) ∧
          s' = { s with chan1 := setFn s.chan1 i { (s.chan1 i) with cmd := .reqE } }
      | .recvReqS i =>
          s.curCmd = .empty ∧
          (s.chan1 i).cmd = .reqS ∧
          s' = { s with
                  curCmd := .reqS
                  curPtr := i
                  chan1 := setFn s.chan1 i { (s.chan1 i) with cmd := .empty }
                  invSet := fun j => s.shrSet j }
      | .recvReqE i =>
          s.curCmd = .empty ∧
          (s.chan1 i).cmd = .reqE ∧
          s' = { s with
                  curCmd := .reqE
                  curPtr := i
                  chan1 := setFn s.chan1 i { (s.chan1 i) with cmd := .empty }
                  invSet := fun j => s.shrSet j }
      | .sendInv i =>
          (s.chan2 i).cmd = .empty ∧
          s.invSet i = true ∧
          (s.curCmd = .reqE ∨ (s.curCmd = .reqS ∧ s.exGntd = true)) ∧
          s' = { s with
                  chan2 := setFn s.chan2 i { (s.chan2 i) with cmd := .inv }
                  invSet := setFn s.invSet i false }
      | .sendInvAck i =>
          (s.chan2 i).cmd = .inv ∧
          (s.chan3 i).cmd = .empty ∧
          s' = { s with
                  chan2 := setFn s.chan2 i { (s.chan2 i) with cmd := .empty }
                  chan3 := setFn s.chan3 i
                    { cmd := .invAck
                    , data := if (s.cache i).state = .E then (s.cache i).data else (s.chan3 i).data }
                  cache := setFn s.cache i { (s.cache i) with state := .I } }
      | .recvInvAck i =>
          (s.chan3 i).cmd = .invAck ∧
          s.curCmd ≠ .empty ∧
          (((s.exGntd = true) ∧
            s' = { s with
                    chan3 := setFn s.chan3 i { (s.chan3 i) with cmd := .empty }
                    shrSet := setFn s.shrSet i false
                    exGntd := false
                    memData := (s.chan3 i).data }) ∨
           ((s.exGntd = false) ∧
            s' = { s with
                    chan3 := setFn s.chan3 i { (s.chan3 i) with cmd := .empty }
                    shrSet := setFn s.shrSet i false }))
      | .sendGntS i =>
          s.curCmd = .reqS ∧
          s.curPtr = i ∧
          (s.chan2 i).cmd = .empty ∧
          s.exGntd = false ∧
          s' = { s with
                  chan2 := setFn s.chan2 i { cmd := .gntS, data := s.memData }
                  shrSet := setFn s.shrSet i true
                  curCmd := .empty }
      | .sendGntE i =>
          s.curCmd = .reqE ∧
          s.curPtr = i ∧
          (s.chan2 i).cmd = .empty ∧
          s.exGntd = false ∧
          (∀ j, s.shrSet j = false) ∧
          s' = { s with
                  chan2 := setFn s.chan2 i { cmd := .gntE, data := s.memData }
                  shrSet := setFn s.shrSet i true
                  exGntd := true
                  curCmd := .empty }
      | .recvGntS i =>
          (s.chan2 i).cmd = .gntS ∧
          s' = { s with
                  cache := setFn s.cache i { state := .S, data := (s.chan2 i).data }
                  chan2 := setFn s.chan2 i { (s.chan2 i) with cmd := .empty } }
      | .recvGntE i =>
          (s.chan2 i).cmd = .gntE ∧
          s' = { s with
                  cache := setFn s.cache i { state := .E, data := (s.chan2 i).data }
                  chan2 := setFn s.chan2 i { (s.chan2 i) with cmd := .empty } }
      | .store i d =>
          (s.cache i).state = .E ∧
          s' = { s with
                  cache := setFn s.cache i { (s.cache i) with data := d }
                  auxData := d }

def germanMessagesSpec (n : Nat) : Spec (MState n) where
  init := init n
  next := next n
  fair := []

/-- Control safety: at most one exclusive holder, and shared copies exclude exclusive ones. -/
def ctrlProp (n : Nat) (s : MState n) : Prop :=
  ∀ i j : Fin n, i ≠ j →
    ((s.cache i).state = .E → (s.cache j).state = .I) ∧
    ((s.cache i).state = .S → (s.cache j).state = .I ∨ (s.cache j).state = .S)

/-- Data safety from the TLA model: memory matches `auxData` when no exclusive
    grant is outstanding, and every valid cache copy matches `auxData`. -/
def dataProp (n : Nat) (s : MState n) : Prop :=
  ((s.exGntd = false) → s.memData = s.auxData) ∧
  (∀ i : Fin n, (s.cache i).state ≠ .I → (s.cache i).data = s.auxData)

def invariant (n : Nat) (s : MState n) : Prop :=
  ctrlProp n s ∧ dataProp n s

def cacheInShrSet (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.cache i).state ≠ .I → s.shrSet i = true

def grantDataProp (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, ((s.chan2 i).cmd = .gntS ∨ (s.chan2 i).cmd = .gntE) → (s.chan2 i).data = s.auxData

def invAckDataProp (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, s.exGntd = true → (s.chan3 i).cmd = .invAck → (s.chan3 i).data = s.auxData

def noExclusiveWhenFalse (n : Nat) (s : MState n) : Prop :=
  s.exGntd = false → ∀ i : Fin n, (s.cache i).state ≠ .E ∧ (s.chan2 i).cmd ≠ .gntE

def invSetSubsetShrSet (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, s.invSet i = true → s.shrSet i = true

def exclusiveImpliesExGntd (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, ((s.cache i).state = .E ∨ (s.chan2 i).cmd = .gntE) → s.exGntd = true

def noSharedWhenExGntd (n : Nat) (s : MState n) : Prop :=
  s.exGntd = true → ∀ i : Fin n, (s.cache i).state ≠ .S ∧ (s.chan2 i).cmd ≠ .gntS

def chanImpliesShrSet (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n,
    (((s.chan2 i).cmd = .inv) ∨
     ((s.chan2 i).cmd = .gntS) ∨
     ((s.chan2 i).cmd = .gntE) ∨
     ((s.chan3 i).cmd = .invAck)) →
    s.shrSet i = true

def uniqueShrSetWhenExGntd (n : Nat) (s : MState n) : Prop :=
  s.exGntd = true →
  ∀ i j : Fin n, i ≠ j → s.shrSet i = true → s.shrSet j = false

def exclusiveSelfClean (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.cache i).state = .E →
    (s.chan2 i).cmd ≠ .gntS ∧
    (s.chan2 i).cmd ≠ .gntE ∧
    (s.chan3 i).cmd ≠ .invAck

def grantImpliesInvalid (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, ((s.chan2 i).cmd = .gntS ∨ (s.chan2 i).cmd = .gntE) → (s.cache i).state = .I

def invAckImpliesInvalid (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.chan3 i).cmd = .invAck → (s.cache i).state = .I

def pendingRequesterInvalid (n : Nat) (s : MState n) : Prop :=
  s.curCmd = .empty ∨ (s.cache s.curPtr).state = .I

def strongInvariant (n : Nat) (s : MState n) : Prop :=
  invariant n s ∧
  cacheInShrSet n s ∧
  grantDataProp n s ∧
  invAckDataProp n s ∧
  noExclusiveWhenFalse n s ∧
  invSetSubsetShrSet n s ∧
  exclusiveImpliesExGntd n s ∧
  noSharedWhenExGntd n s ∧
  chanImpliesShrSet n s ∧
  uniqueShrSetWhenExGntd n s

theorem germanMessages_init_ctrlProp (n : Nat) :
    ∀ s : MState n, init n s → ctrlProp n s := by
  intro s hinit i j hij
  rcases hinit with ⟨hcache, _, _, _, _, _, _, _, _, _⟩
  constructor
  · intro hiE
    have hj := hcache j
    simp [hj]
  · intro hiS
    left
    have hj := hcache j
    simp [hj]

theorem germanMessages_init_dataProp (n : Nat) :
    ∀ s : MState n, init n s → dataProp n s := by
  intro s hinit
  rcases hinit with ⟨hcache, _, _, _, _, _, hex, _, hmem, haux⟩
  constructor
  · intro _
    rw [hmem, haux]
  · intro i hi
    have hc := hcache i
    simp [hc] at hi

theorem germanMessages_init_invariant (n : Nat) :
    ∀ s : MState n, init n s → invariant n s := by
  intro s hinit
  exact ⟨germanMessages_init_ctrlProp n s hinit, germanMessages_init_dataProp n s hinit⟩

theorem germanMessages_init_strongInvariant (n : Nat) :
    ∀ s : MState n, init n s → strongInvariant n s := by
  intro s hinit
  have hinit0 := hinit
  rcases hinit with ⟨hcache, _, hchan2, hchan3, hInv, hShr, hEx, _, _, hAux⟩
  refine ⟨germanMessages_init_invariant n s hinit0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have := hcache i
    simp [this] at hi
  · intro i hi
    have := hchan2 i
    simp [this] at hi
  · intro i hex hi
    simp [hEx] at hex
  · intro hex i
    have hc := hcache i
    have h2 := hchan2 i
    constructor <;> simp [hc, h2]
  · intro i hi
    simp [hInv i] at hi
  · intro i hi
    have hc := hcache i
    have h2 := hchan2 i
    simp [hc, h2] at hi
  · intro hex i
    simp [hEx] at hex
  · intro i hi
    have h2 := hchan2 i
    have h3 := hchan3 i
    simp [h2, h3] at hi
  · intro hex i j hij hi
    simp [hEx] at hex

theorem germanMessages_init_exclusiveSelfClean (n : Nat) :
    ∀ s : MState n, init n s → exclusiveSelfClean n s := by
  intro s hinit i hiE
  rcases hinit with ⟨hcache, _, hchan2, hchan3, _, _, _, _, _, _⟩
  have hc := hcache i
  simp [hc] at hiE

private theorem strongInvariant_preserved_sendReqS
    {n : Nat} {s s' : MState n} {i : Fin n}
    (hs : strongInvariant n s)
    (hstep : (s.chan1 i).cmd = .empty ∧ (s.cache i).state = .I ∧
      s' = { s with chan1 := setFn s.chan1 i { (s.chan1 i) with cmd := .reqS } }) :
    strongInvariant n s' := by
  rcases hstep with ⟨_, _, rfl⟩
  simpa [strongInvariant, invariant, ctrlProp, dataProp, cacheInShrSet, grantDataProp,
    invAckDataProp, noExclusiveWhenFalse, invSetSubsetShrSet, exclusiveImpliesExGntd,
    noSharedWhenExGntd, chanImpliesShrSet, uniqueShrSetWhenExGntd] using hs

private theorem strongInvariant_preserved_sendReqE
    {n : Nat} {s s' : MState n} {i : Fin n}
    (hs : strongInvariant n s)
    (hstep : (s.chan1 i).cmd = .empty ∧ ((s.cache i).state = .I ∨ (s.cache i).state = .S) ∧
      s' = { s with chan1 := setFn s.chan1 i { (s.chan1 i) with cmd := .reqE } }) :
    strongInvariant n s' := by
  rcases hstep with ⟨_, _, rfl⟩
  simpa [strongInvariant, invariant, ctrlProp, dataProp, cacheInShrSet, grantDataProp,
    invAckDataProp, noExclusiveWhenFalse, invSetSubsetShrSet, exclusiveImpliesExGntd,
    noSharedWhenExGntd, chanImpliesShrSet, uniqueShrSetWhenExGntd] using hs

private theorem strongInvariant_preserved_recvReqS
    {n : Nat} {s s' : MState n} {i : Fin n}
    (hs : strongInvariant n s)
    (hstep : s.curCmd = .empty ∧ (s.chan1 i).cmd = .reqS ∧
      s' = { s with
              curCmd := .reqS
              curPtr := i
              chan1 := setFn s.chan1 i { (s.chan1 i) with cmd := .empty }
              invSet := fun j => s.shrSet j }) :
    strongInvariant n s' := by
  rcases hs with ⟨hinv, hcacheShr, hgrant, hinvAck, hnoExFalse, hinvSub, hexImpl, hnoSharedEx, hchanShr, huniqShr⟩
  rcases hstep with ⟨_, _, rfl⟩
  refine ⟨hinv, hcacheShr, hgrant, hinvAck, hnoExFalse, ?_, hexImpl, hnoSharedEx, hchanShr, huniqShr⟩
  intro j hj
  simpa using hj

private theorem strongInvariant_preserved_recvReqE
    {n : Nat} {s s' : MState n} {i : Fin n}
    (hs : strongInvariant n s)
    (hstep : s.curCmd = .empty ∧ (s.chan1 i).cmd = .reqE ∧
      s' = { s with
              curCmd := .reqE
              curPtr := i
              chan1 := setFn s.chan1 i { (s.chan1 i) with cmd := .empty }
              invSet := fun j => s.shrSet j }) :
    strongInvariant n s' := by
  rcases hs with ⟨hinv, hcacheShr, hgrant, hinvAck, hnoExFalse, hinvSub, hexImpl, hnoSharedEx, hchanShr, huniqShr⟩
  rcases hstep with ⟨_, _, rfl⟩
  refine ⟨hinv, hcacheShr, hgrant, hinvAck, hnoExFalse, ?_, hexImpl, hnoSharedEx, hchanShr, huniqShr⟩
  intro j hj
  simpa using hj

private theorem strongInvariant_preserved_sendInv
    {n : Nat} {s s' : MState n} {i : Fin n}
    (hs : strongInvariant n s)
    (hstep : (s.chan2 i).cmd = .empty ∧ s.invSet i = true ∧
      (s.curCmd = .reqE ∨ (s.curCmd = .reqS ∧ s.exGntd = true)) ∧
      s' = { s with
              chan2 := setFn s.chan2 i { (s.chan2 i) with cmd := .inv }
              invSet := setFn s.invSet i false }) :
    strongInvariant n s' := by
  rcases hs with ⟨hinv, hcacheShr, hgrant, hinvAck, hnoExFalse, hinvSub, hexImpl, hnoSharedEx, hchanShr, huniqShr⟩
  rcases hstep with ⟨hchan2i, hinvi, _, rfl⟩
  refine ⟨hinv, hcacheShr, ?_, hinvAck, ?_, ?_, ?_, ?_, ?_, huniqShr⟩
  · intro j hj
    by_cases hji : j = i
    · subst hji
      simp [setFn] at hj
    · have hj' : (s.chan2 j).cmd = .gntS ∨ (s.chan2 j).cmd = .gntE := by
        simpa [setFn, hji] using hj
      simpa [setFn, hji] using hgrant j hj'
  · intro hexFalse j
    by_cases hji : j = i
    · subst hji
      constructor
      · exact (hnoExFalse hexFalse j).1
      · simp [setFn]
    · simpa [setFn, hji] using hnoExFalse hexFalse j
  · intro j hj
    by_cases hji : j = i
    · subst hji
      simp [setFn] at hj
    · have := hinvSub j
      simp [setFn, hji] at hj ⊢
      exact this hj
  · intro j hj
    by_cases hji : j = i
    · subst hji
      have hj' : (s.cache j).state = .E ∨ (s.chan2 j).cmd = .gntE := by
        simp [setFn] at hj
        exact Or.inl hj
      exact hexImpl j hj'
    · have hj' : (s.cache j).state = .E ∨ (s.chan2 j).cmd = .gntE := by
        simpa [setFn, hji] using hj
      exact hexImpl j hj'
  · intro hexTrue j
    by_cases hji : j = i
    · subst hji
      constructor
      · exact (hnoSharedEx hexTrue j).1
      · simp [setFn]
    · simpa [setFn, hji] using hnoSharedEx hexTrue j
  · intro j hj
    by_cases hji : j = i
    · subst hji
      rcases hj with hj | hj | hj | hj
      · exact hinvSub j hinvi
      · simp [setFn] at hj
      · simp [setFn] at hj
      · have hj' : (s.chan3 j).cmd = .invAck := by simpa using hj
        exact hchanShr j (Or.inr <| Or.inr <| Or.inr hj')
    · have hj' : ((s.chan2 j).cmd = .inv) ∨
        ((s.chan2 j).cmd = .gntS) ∨
        ((s.chan2 j).cmd = .gntE) ∨
        ((s.chan3 j).cmd = .invAck) := by
          simpa [setFn, hji] using hj
      exact hchanShr j hj'

private theorem strongInvariant_preserved_sendGntS
    {n : Nat} {s s' : MState n} {i : Fin n}
    (hs : strongInvariant n s)
    (hstep : s.curCmd = .reqS ∧ s.curPtr = i ∧ (s.chan2 i).cmd = .empty ∧ s.exGntd = false ∧
      s' = { s with
              chan2 := setFn s.chan2 i { cmd := .gntS, data := s.memData }
              shrSet := setFn s.shrSet i true
              curCmd := .empty }) :
    strongInvariant n s' := by
  rcases hs with ⟨hinv, hcacheShr, hgrant, hinvAck, hnoExFalse, hinvSub, hexImpl, hnoSharedEx, hchanShr, huniqShr⟩
  rcases hstep with ⟨_, _, hchan2i, hexFalse, rfl⟩
  refine ⟨hinv, ?_, ?_, hinvAck, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    by_cases hji : j = i
    · subst hji
      simp [setFn]
    · simpa [setFn, hji] using hcacheShr j hj
  · intro j hj
    by_cases hji : j = i
    · subst hji
      simp [setFn]
      exact hinv.2.1 hexFalse
    · have hj' : (s.chan2 j).cmd = .gntS ∨ (s.chan2 j).cmd = .gntE := by
        simpa [setFn, hji] using hj
      simpa [setFn, hji] using hgrant j hj'
  · intro hexFalse' j
    by_cases hji : j = i
    · subst hji
      constructor
      · exact (hnoExFalse hexFalse j).1
      · simp [setFn]
    · simpa [setFn, hji] using hnoExFalse hexFalse j
  · intro j hj
    have := hinvSub j hj
    by_cases hji : j = i
    · subst hji
      simp [setFn]
    · simpa [setFn, hji] using this
  · intro j hj
    by_cases hji : j = i
    · subst hji
      have hnotE : (s.cache j).state ≠ .E := (hnoExFalse hexFalse j).1
      simp [setFn] at hj
      exact (hnotE hj).elim
    · have hj' : (s.cache j).state = .E ∨ (s.chan2 j).cmd = .gntE := by
        simpa [setFn, hji] using hj
      exact hexImpl j hj'
  · intro hexTrue
    simp [hexFalse] at hexTrue
  · intro j hj
    by_cases hji : j = i
    · subst hji
      rcases hj with hj | hj | hj | hj
      · simp [setFn] at hj
      · simp [setFn]
      · simp [setFn] at hj
      · simp [setFn]
    · have hj' : ((s.chan2 j).cmd = .inv) ∨
        ((s.chan2 j).cmd = .gntS) ∨
        ((s.chan2 j).cmd = .gntE) ∨
        ((s.chan3 j).cmd = .invAck) := by
          simpa [setFn, hji] using hj
      simpa [setFn, hji] using hchanShr j hj'
  · intro hexTrue
    simp [hexFalse] at hexTrue

private theorem cache_I_of_shr_false
    {n : Nat} {s : MState n}
    (hs : strongInvariant n s)
    (hshrFalse : ∀ j, s.shrSet j = false) :
    ∀ j, (s.cache j).state = .I := by
  rcases hs with ⟨_, hcacheShr, _, _, _, _, _, _, _, _⟩
  intro j
  by_contra hne
  have hjShr : s.shrSet j = true := hcacheShr j hne
  rw [hshrFalse j] at hjShr
  simp at hjShr

private theorem no_chan_msg_of_shr_false
    {n : Nat} {s : MState n}
    (hs : strongInvariant n s)
    (hshrFalse : ∀ j, s.shrSet j = false) :
    ∀ j, (s.chan2 j).cmd ≠ .inv ∧ (s.chan2 j).cmd ≠ .gntS ∧
      (s.chan2 j).cmd ≠ .gntE ∧ (s.chan3 j).cmd ≠ .invAck := by
  rcases hs with ⟨_, _, _, _, _, _, _, _, hchanShr, _⟩
  intro j
  constructor
  · intro h
    have hjShr : s.shrSet j = true := hchanShr j (Or.inl h)
    rw [hshrFalse j] at hjShr
    simp at hjShr
  constructor
  · intro h
    have hjShr : s.shrSet j = true := hchanShr j (Or.inr <| Or.inl h)
    rw [hshrFalse j] at hjShr
    simp at hjShr
  constructor
  · intro h
    have hjShr : s.shrSet j = true := hchanShr j (Or.inr <| Or.inr <| Or.inl h)
    rw [hshrFalse j] at hjShr
    simp at hjShr
  · intro h
    have hjShr : s.shrSet j = true := hchanShr j (Or.inr <| Or.inr <| Or.inr h)
    rw [hshrFalse j] at hjShr
    simp at hjShr

private theorem cache_I_of_unique_sharer
    {n : Nat} {s : MState n} {i j : Fin n}
    (hs : strongInvariant n s)
    (hexTrue : s.exGntd = true)
    (hshrI : s.shrSet i = true)
    (hij : i ≠ j) :
    (s.cache j).state = .I := by
  rcases hs with ⟨_, hcacheShr, _, _, _, _, _, _, _, huniqShr⟩
  have hjFalse : s.shrSet j = false := huniqShr hexTrue i j hij hshrI
  by_contra hjNotI
  have hjShr : s.shrSet j = true := hcacheShr j hjNotI
  rw [hjFalse] at hjShr
  simp at hjShr

private theorem no_shared_cache_of_exclusive
    {n : Nat} {s : MState n} {j : Fin n}
    (hs : strongInvariant n s)
    (hexTrue : s.exGntd = true) :
    (s.cache j).state ≠ .S := by
  rcases hs with ⟨_, _, _, _, _, _, _, hnoSharedEx, _, _⟩
  exact (hnoSharedEx hexTrue j).1

private theorem no_gntS_when_exclusive
    {n : Nat} {s : MState n} {j : Fin n}
    (hs : strongInvariant n s)
    (hexTrue : s.exGntd = true) :
    (s.chan2 j).cmd ≠ .gntS := by
  rcases hs with ⟨_, _, _, _, _, _, _, hnoSharedEx, _, _⟩
  exact (hnoSharedEx hexTrue j).2

private theorem strongInvariant_preserved_sendGntE
    {n : Nat} {s s' : MState n} {i : Fin n}
    (hs : strongInvariant n s)
    (hstep : s.curCmd = .reqE ∧ s.curPtr = i ∧ (s.chan2 i).cmd = .empty ∧ s.exGntd = false ∧
      (∀ j, s.shrSet j = false) ∧
      s' = { s with
              chan2 := setFn s.chan2 i { cmd := .gntE, data := s.memData }
              shrSet := setFn s.shrSet i true
              exGntd := true
              curCmd := .empty }) :
    strongInvariant n s' := by
  have hs0 := hs
  rcases hs with ⟨hinv, hcacheShr, hgrant, hinvAck, hnoExFalse, hinvSub, hexImpl, hnoSharedEx, hchanShr, huniqShr⟩
  rcases hstep with ⟨_, _, hchan2i, hexFalse, hshrFalse, rfl⟩
  have hcacheI := cache_I_of_shr_false hs0 hshrFalse
  have hnochan := no_chan_msg_of_shr_false hs0 hshrFalse
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · simpa [ctrlProp] using hinv.1
    · constructor
      · intro hfalse
        cases hfalse
      · intro j hjNotI
        have hjI : (s.cache j).state = .I := hcacheI j
        exact (hjNotI (by simpa [setFn] using hjI)).elim
  · intro j hjNotI
    have hjI : (s.cache j).state = .I := hcacheI j
    exact (hjNotI (by simpa [setFn] using hjI)).elim
  · intro j hjGrant
    by_cases hji : j = i
    · subst hji
      simp [setFn]
      exact hinv.2.1 hexFalse
    · have hjGrant' : (s.chan2 j).cmd = .gntS ∨ (s.chan2 j).cmd = .gntE := by
        simpa [setFn, hji] using hjGrant
      rcases hjGrant' with hjGntS | hjGntE
      · exact ((hnochan j).2.1 hjGntS).elim
      · exact ((hnochan j).2.2.1 hjGntE).elim
  · intro j hexTrue hjAck
    by_cases hji : j = i
    · subst hji
      have hjAck' : (s.chan3 j).cmd = .invAck := by simpa [setFn] using hjAck
      exact ((hnochan j).2.2.2 hjAck').elim
    · have hjAck' : (s.chan3 j).cmd = .invAck := by simpa [setFn, hji] using hjAck
      exact ((hnochan j).2.2.2 hjAck').elim
  · intro hfalse
    cases hfalse
  · intro j hjInv
    have hshr : s.shrSet j = true := hinvSub j hjInv
    rw [hshrFalse j] at hshr
    simp at hshr
  · intro j hjEx
    simp
  · intro hexTrue j
    constructor
    · have hjI : (s.cache j).state = .I := hcacheI j
      intro hjS
      cases hjS.symm.trans hjI
    · by_cases hji : j = i
      · subst hji
        simp [setFn]
      · intro hjGntS
        have hjGntS' : (s.chan2 j).cmd = .gntS := by simpa [setFn, hji] using hjGntS
        exact (hnochan j).2.1 hjGntS'
  · intro j hjMsg
    by_cases hji : j = i
    · subst hji
      rcases hjMsg with hjInv | hjRest
      · simp [setFn] at hjInv
      · rcases hjRest with hjGntS | hjRest
        · simp [setFn] at hjGntS
        · rcases hjRest with hjGntE | hjAck
          · simp [setFn]
          · have hjAck' : (s.chan3 j).cmd = .invAck := by simpa [setFn] using hjAck
            exact ((hnochan j).2.2.2 hjAck').elim
    · have hjMsg' : ((s.chan2 j).cmd = .inv) ∨
        ((s.chan2 j).cmd = .gntS) ∨
        ((s.chan2 j).cmd = .gntE) ∨
        ((s.chan3 j).cmd = .invAck) := by
          simpa [setFn, hji] using hjMsg
      rcases hjMsg' with hjInv | hjRest
      · exact ((hnochan j).1 hjInv).elim
      · rcases hjRest with hjGntS | hjRest
        · exact ((hnochan j).2.1 hjGntS).elim
        · rcases hjRest with hjGntE | hjAck
          · exact ((hnochan j).2.2.1 hjGntE).elim
          · exact ((hnochan j).2.2.2 hjAck).elim
  · intro hexTrue j k hjk hjShr
    by_cases hji : j = i
    · subst hji
      by_cases hki : k = j
      · exact False.elim (hjk hki.symm)
      · have hkFalse : s.shrSet k = false := hshrFalse k
        simp [setFn, hki, hkFalse]
    · have hjShr' : s.shrSet j = true := by simpa [setFn, hji] using hjShr
      rw [hshrFalse j] at hjShr'
      simp at hjShr'

private theorem strongInvariant_preserved_recvGntS
    {n : Nat} {s s' : MState n} {i : Fin n}
    (hs : strongInvariant n s)
    (hstep : (s.chan2 i).cmd = .gntS ∧
      s' = { s with
              cache := setFn s.cache i { state := .S, data := (s.chan2 i).data }
              chan2 := setFn s.chan2 i { (s.chan2 i) with cmd := .empty } }) :
    strongInvariant n s' := by
  rcases hs with ⟨hinv, hcacheShr, hgrant, hinvAck, hnoExFalse, hinvSub, hexImpl, hnoSharedEx, hchanShr, huniqShr⟩
  rcases hstep with ⟨hchan2i, rfl⟩
  have hexFalse : s.exGntd = false := by
    by_contra hexTrue
    exact (hnoSharedEx (by simpa using hexTrue) i).2 hchan2i
  have hshrI : s.shrSet i = true := hchanShr i (Or.inr <| Or.inl hchan2i)
  have hdataI : (s.chan2 i).data = s.auxData := hgrant i (Or.inl hchan2i)
  refine ⟨?_, ?_, ?_, hinvAck, ?_, hinvSub, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro j k hjk
      constructor
      · intro hjE
        by_cases hji : j = i
        · subst hji
          have : False := by
            simp [setFn] at hjE
          exact False.elim this
        · have hjE' : (s.cache j).state = .E := by simpa [setFn, hji] using hjE
          have : False := (hnoExFalse hexFalse j).1 hjE'
          exact False.elim this
      · intro hjS
        by_cases hji : j = i
        · subst hji
          by_cases hki : k = j
          · exact False.elim (hjk hki.symm)
          · have hkNotE : (s.cache k).state ≠ .E := (hnoExFalse hexFalse k).1
            cases hstate : (s.cache k).state
            · left
              simp [setFn, hki, hstate]
            · right
              simp [setFn, hki, hstate]
            · exfalso
              exact hkNotE hstate
        · have hjS' : (s.cache j).state = .S := by simpa [setFn, hji] using hjS
          have hkIS := (hinv.1 j k hjk).2 hjS'
          by_cases hki : k = i
          · subst hki
            right
            simp [setFn]
          · simpa [setFn, hki] using hkIS
    · constructor
      · intro hfalse
        exact hinv.2.1 hfalse
      · intro j hjNotI
        by_cases hji : j = i
        · subst hji
          simpa [setFn] using hdataI
        · have hjNotI' : (s.cache j).state ≠ .I := by simpa [setFn, hji] using hjNotI
          simpa [setFn, hji] using hinv.2.2 j hjNotI'
  · intro j hjNotI
    by_cases hji : j = i
    · subst hji
      simpa [setFn] using hshrI
    · have hjNotI' : (s.cache j).state ≠ .I := by simpa [setFn, hji] using hjNotI
      simpa [setFn, hji] using hcacheShr j hjNotI'
  · intro j hjGrant
    by_cases hji : j = i
    · subst hji
      simp [setFn] at hjGrant
    · have hjGrant' : (s.chan2 j).cmd = .gntS ∨ (s.chan2 j).cmd = .gntE := by
        simpa [setFn, hji] using hjGrant
      simpa [setFn, hji] using hgrant j hjGrant'
  · intro hfalse j
    by_cases hji : j = i
    · subst hji
      constructor
      · simp [setFn]
      · simp [setFn]
    · simpa [setFn, hji] using hnoExFalse hfalse j
  · intro j hjEx
    by_cases hji : j = i
    · subst hji
      rcases hjEx with hjE | hjGntE
      · simp [setFn] at hjE
      · simp [setFn] at hjGntE
    · have hjEx' : (s.cache j).state = .E ∨ (s.chan2 j).cmd = .gntE := by
        simpa [setFn, hji] using hjEx
      exact hexImpl j hjEx'
  · intro hexTrue
    simp [hexFalse] at hexTrue
  · intro j hjMsg
    by_cases hji : j = i
    · subst hji
      rcases hjMsg with hjInv | hjRest
      · simp [setFn] at hjInv
      · rcases hjRest with hjGntS | hjRest
        · simp [setFn] at hjGntS
        · rcases hjRest with hjGntE | hjAck
          · simp [setFn] at hjGntE
          · simpa [setFn] using hchanShr j (Or.inr <| Or.inr <| Or.inr hjAck)
    · have hjMsg' : ((s.chan2 j).cmd = .inv) ∨
        ((s.chan2 j).cmd = .gntS) ∨
        ((s.chan2 j).cmd = .gntE) ∨
        ((s.chan3 j).cmd = .invAck) := by
          simpa [setFn, hji] using hjMsg
      simpa [setFn, hji] using hchanShr j hjMsg'
  · intro hexTrue
    simp [hexFalse] at hexTrue

private theorem strongInvariant_preserved_recvGntE
    {n : Nat} {s : MState n} {i : Fin n}
    (hs : strongInvariant n s)
    (hstep : (s.chan2 i).cmd = .gntE) :
    strongInvariant n (recvGntEState s i) := by
  have hs0 := hs
  rcases hs with ⟨hinv, hcacheShr, hgrant, hinvAck, hnoExFalse, hinvSub, hexImpl, hnoSharedEx, hchanShr, huniqShr⟩
  have hexTrue : s.exGntd = true := hexImpl i (Or.inr hstep)
  have hshrI : s.shrSet i = true := hchanShr i (Or.inr <| Or.inr <| Or.inl hstep)
  have hdataI : (s.chan2 i).data = s.auxData := hgrant i (Or.inr hstep)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro j k hjk
      constructor
      · intro hjE
        by_cases hji : j = i
        · subst hji
          have hik : j ≠ k := hjk
          have hkI : (s.cache k).state = .I := cache_I_of_unique_sharer (i := j) hs0 hexTrue hshrI hik
          by_cases hki : k = j
          · exact False.elim (hjk hki.symm)
          · simpa [recvGntEState, hki] using hkI
        · have hij : i ≠ j := by
            intro hj
            exact hji hj.symm
          have hjI : (s.cache j).state = .I := cache_I_of_unique_sharer hs0 hexTrue hshrI hij
          have hjE' : (s.cache j).state = .E := by simpa [recvGntEState, hji] using hjE
          exact False.elim (by cases hjE'.symm.trans hjI)
      · intro hjS
        by_cases hji : j = i
        · subst hji
          simp [recvGntEState] at hjS
        · have hjS' : (s.cache j).state = .S := by simpa [recvGntEState, hji] using hjS
          exact ((no_shared_cache_of_exclusive (j := j) hs0 hexTrue) hjS').elim
    · constructor
      · intro hfalse
        have : s.exGntd = false := by simpa [recvGntEState] using hfalse
        exfalso
        rw [hexTrue] at this
        simp at this
      · intro j hjNotI
        by_cases hji : j = i
        · subst hji
          simp [recvGntEState, hdataI]
        · have hjNotI' : (s.cache j).state ≠ .I := by simpa [recvGntEState, hji] using hjNotI
          simpa [recvGntEState, hji] using hinv.2.2 j hjNotI'
  · intro j hjNotI
    by_cases hji : j = i
    · subst hji
      simpa using hshrI
    · have hjNotI' : (s.cache j).state ≠ .I := by simpa [recvGntEState, hji] using hjNotI
      simpa [recvGntEState, hji] using hcacheShr j hjNotI'
  · intro j hjGrant
    by_cases hji : j = i
    · subst hji
      simp [recvGntEState] at hjGrant
    · have hjGrant' : (s.chan2 j).cmd = .gntS ∨ (s.chan2 j).cmd = .gntE := by
        simpa [recvGntEState, hji] using hjGrant
      simpa [recvGntEState, hji] using hgrant j hjGrant'
  · intro j hexTrue' hjAck
    simpa [recvGntEState] using hinvAck j hexTrue' hjAck
  · intro hfalse
    have : s.exGntd = false := by simpa [recvGntEState] using hfalse
    exfalso
    rw [hexTrue] at this
    simp at this
  · simpa [recvGntEState]
  · intro j hjEx
    simpa [recvGntEState] using hexTrue
  · intro hexTrue' j
    constructor
    · by_cases hji : j = i
      · subst hji
        simp [recvGntEState]
      · intro hjS
        have hjS' : (s.cache j).state = .S := by simpa [recvGntEState, hji] using hjS
        exact (no_shared_cache_of_exclusive (j := j) hs0 hexTrue) hjS'
    · by_cases hji : j = i
      · subst hji
        simp [recvGntEState]
      · intro hjGntS
        have hjGntS' : (s.chan2 j).cmd = .gntS := by simpa [recvGntEState, hji] using hjGntS
        exact (no_gntS_when_exclusive (j := j) hs0 hexTrue) hjGntS'
  · intro j hjMsg
    by_cases hji : j = i
    · subst hji
      rcases hjMsg with hjInv | hjRest
      · simp [recvGntEState] at hjInv
      · rcases hjRest with hjGntS | hjRest
        · simp [recvGntEState] at hjGntS
        · rcases hjRest with hjGntE | hjAck
          · simp [recvGntEState] at hjGntE
          · simpa [recvGntEState] using hchanShr j (Or.inr <| Or.inr <| Or.inr hjAck)
    · have hjMsg' : ((s.chan2 j).cmd = .inv) ∨
        ((s.chan2 j).cmd = .gntS) ∨
        ((s.chan2 j).cmd = .gntE) ∨
        ((s.chan3 j).cmd = .invAck) := by
          simpa [recvGntEState, hji] using hjMsg
      simpa [recvGntEState, hji] using hchanShr j hjMsg'
  · simpa [recvGntEState] using huniqShr

private theorem strongInvariant_preserved_store_of_clean_self
    {n : Nat} {s : MState n} {i : Fin n} {d : Val}
    (hs : strongInvariant n s)
    (hcacheE : (s.cache i).state = .E)
    (hnoGntS : (s.chan2 i).cmd ≠ .gntS)
    (hnoGntE : (s.chan2 i).cmd ≠ .gntE)
    (hnoAck : (s.chan3 i).cmd ≠ .invAck) :
    strongInvariant n (storeState s i d) := by
  have hs0 := hs
  rcases hs with ⟨hinv, hcacheShr, hgrant, hinvAck, hnoExFalse, hinvSub, hexImpl, hnoSharedEx, hchanShr, huniqShr⟩
  have hexTrue : s.exGntd = true := hexImpl i (Or.inl hcacheE)
  have hcacheNotI : (s.cache i).state ≠ .I := by
    rw [hcacheE]
    simp
  have hshrI : s.shrSet i = true := hcacheShr i hcacheNotI
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro j k hjk
      constructor
      · intro hjE
        by_cases hji : j = i
        · subst hji
          have hik : j ≠ k := hjk
          have hkI : (s.cache k).state = .I := cache_I_of_unique_sharer (i := j) hs0 hexTrue hshrI hik
          by_cases hki : k = j
          · exact False.elim (hjk hki.symm)
          · simpa [storeState, hki] using hkI
        · have hij : i ≠ j := by
            intro hj
            exact hji hj.symm
          have hjI : (s.cache j).state = .I := cache_I_of_unique_sharer hs0 hexTrue hshrI hij
          have hjE' : (s.cache j).state = .E := by simpa [storeState, hji] using hjE
          exact False.elim (by cases hjE'.symm.trans hjI)
      · intro hjS
        by_cases hji : j = i
        · subst hji
          simp [storeState, hcacheE] at hjS
        · have hjS' : (s.cache j).state = .S := by simpa [storeState, hji] using hjS
          exact ((no_shared_cache_of_exclusive (j := j) hs0 hexTrue) hjS').elim
    · constructor
      · intro hfalse
        have : s.exGntd = false := by simpa [storeState] using hfalse
        exfalso
        rw [hexTrue] at this
        simp at this
      · intro j hjNotI
        by_cases hji : j = i
        · subst hji
          simp [storeState]
        · have hij : i ≠ j := by
            intro hj
            exact hji hj.symm
          have hjI : (s.cache j).state = .I := cache_I_of_unique_sharer hs0 hexTrue hshrI hij
          have hjNotI' : ((storeState s i d).cache j).state ≠ .I := hjNotI
          have : ((storeState s i d).cache j).state = .I := by simpa [storeState, hji] using hjI
          exact False.elim (hjNotI' this)
  · intro j hjNotI
    by_cases hji : j = i
    · subst hji
      simpa [storeState] using hshrI
    · have hij : i ≠ j := by
        intro hj
        exact hji hj.symm
      have hjI : (s.cache j).state = .I := cache_I_of_unique_sharer hs0 hexTrue hshrI hij
      have : ((storeState s i d).cache j).state = .I := by simpa [storeState, hji] using hjI
      exact False.elim (hjNotI this)
  · intro j hjGrant
    by_cases hji : j = i
    · subst hji
      rcases hjGrant with hjGntS | hjGntE
      · exact (hnoGntS hjGntS).elim
      · exact (hnoGntE hjGntE).elim
    · have hjGrant' : (s.chan2 j).cmd = .gntS ∨ (s.chan2 j).cmd = .gntE := by
        simpa [storeState, hji] using hjGrant
      have hjShr : s.shrSet j = true := by
        rcases hjGrant' with hjGntS | hjGntE
        · exact hchanShr j (Or.inr <| Or.inl hjGntS)
        · exact hchanShr j (Or.inr <| Or.inr <| Or.inl hjGntE)
      have hij : i ≠ j := by
        intro hj
        exact hji hj.symm
      have hjFalse : s.shrSet j = false := huniqShr hexTrue i j hij hshrI
      rw [hjFalse] at hjShr
      simp at hjShr
  · intro j hexTrue' hjAck
    by_cases hji : j = i
    · subst hji
      exact (hnoAck hjAck).elim
    · have hjAck' : (s.chan3 j).cmd = .invAck := by simpa [storeState, hji] using hjAck
      have hjShr : s.shrSet j = true := hchanShr j (Or.inr <| Or.inr <| Or.inr hjAck')
      have hij : i ≠ j := by
        intro hj
        exact hji hj.symm
      have hjFalse : s.shrSet j = false := huniqShr hexTrue i j hij hshrI
      rw [hjFalse] at hjShr
      simp at hjShr
  · intro hfalse
    have : s.exGntd = false := by simpa [storeState] using hfalse
    exfalso
    rw [hexTrue] at this
    simp at this
  · simpa [storeState]
  · intro j hjEx
    simpa [storeState] using hexTrue
  · intro hexTrue' j
    constructor
    · by_cases hji : j = i
      · subst hji
        simp [storeState, hcacheE]
      · intro hjS
        have hjS' : (s.cache j).state = .S := by simpa [storeState, hji] using hjS
        exact (no_shared_cache_of_exclusive (j := j) hs0 hexTrue) hjS'
    · by_cases hji : j = i
      · subst hji
        intro hjGntS
        exact (hnoGntS hjGntS).elim
      · intro hjGntS
        have hjGntS' : (s.chan2 j).cmd = .gntS := by simpa [storeState, hji] using hjGntS
        exact (no_gntS_when_exclusive (j := j) hs0 hexTrue) hjGntS'
  · intro j hjMsg
    by_cases hji : j = i
    · subst hji
      rcases hjMsg with hjInv | hjRest
      · simpa [storeState] using hchanShr j (Or.inl hjInv)
      · rcases hjRest with hjGntS | hjRest
        · exact (hnoGntS hjGntS).elim
        · rcases hjRest with hjGntE | hjAck
          · exact (hnoGntE hjGntE).elim
          · exact (hnoAck hjAck).elim
    · have hjMsg' : ((s.chan2 j).cmd = .inv) ∨
        ((s.chan2 j).cmd = .gntS) ∨
        ((s.chan2 j).cmd = .gntE) ∨
        ((s.chan3 j).cmd = .invAck) := by
          simpa [storeState, hji] using hjMsg
      simpa [storeState] using hchanShr j hjMsg'
  · simpa [storeState] using huniqShr

/-- If chan2[i]=gntE then chan3[i]≠invAck. Prevents conflicting in-flight messages. -/
private def grantExcludesInvAck (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.chan2 i).cmd = .gntE → (s.chan3 i).cmd ≠ .invAck

/-- exGntd is witnessed by a cache in E, or a gntE/invAck in flight. -/
private def exGntdWitness (n : Nat) (s : MState n) : Prop :=
  s.exGntd = true →
    ∃ j : Fin n, (s.cache j).state = .E ∨ (s.chan2 j).cmd = .gntE ∨ (s.chan3 j).cmd = .invAck

/-- Channel inv only arises during reqE or reqS-with-exclusive -/
private def invReasonProp (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.chan2 i).cmd = .inv → s.exGntd = true ∨ s.curCmd = .reqE

/-- When idle or ready to grant S, no invAcks pending in chan3 -/
private def cleanChannelWhenReady (n : Nat) (s : MState n) : Prop :=
  (s.curCmd = .empty ∨ (s.curCmd = .reqS ∧ s.exGntd = false)) →
    ∀ i : Fin n, (s.chan3 i).cmd ≠ .invAck

/-- gntS in chan2 and invAck in chan3 cannot coexist for the same client -/
private def gntSExcludesInvAck (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.chan2 i).cmd = .gntS → (s.chan3 i).cmd ≠ .invAck

/-- When chan3[j] has invAck, chan2[j] is empty (sendInvAck cleared it) -/
private def invAckClearsGrant (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.chan3 i).cmd = .invAck → (s.chan2 i).cmd = .empty

/-- When invSet[j]=true, chan3[j] is empty (not yet invited) -/
private def invSetImpliesClean (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, s.invSet i = true → (s.chan3 i).cmd = .empty

/-- When chan2[j]=inv (invitation sent), invSet[j]=false (already cleared by sendInv) -/
private def invClearsInvSet (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.chan2 i).cmd = .inv → s.invSet i = false

/-- chan3 messages are always either empty or invAck (protocol-structural invariant) -/
private def chan3IsInvAck (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.chan3 i).cmd = .empty ∨ (s.chan3 i).cmd = .invAck

/-- When chan2[i]=inv, the controller is busy (curCmd≠empty).
    Follows from invReasonProp + sendGntS/E guards blocking curCmd=empty while inv in flight. -/
private def invRequiresNonEmpty (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.chan2 i).cmd = .inv → s.curCmd ≠ .empty

/-- Full inductive invariant: strongInvariant + twelve auxiliary properties. -/
private def fullStrongInvariant (n : Nat) (s : MState n) : Prop :=
  strongInvariant n s ∧
  exclusiveSelfClean n s ∧
  grantExcludesInvAck n s ∧
  exGntdWitness n s ∧
  invAckImpliesInvalid n s ∧
  gntSExcludesInvAck n s ∧
  cleanChannelWhenReady n s ∧
  invReasonProp n s ∧
  invAckClearsGrant n s ∧
  invSetImpliesClean n s ∧
  invClearsInvSet n s ∧
  chan3IsInvAck n s ∧
  invRequiresNonEmpty n s

private theorem init_grantExcludesInvAck (n : Nat) :
    ∀ s : MState n, init n s → grantExcludesInvAck n s := by
  intro s hinit i hgntE
  rcases hinit with ⟨_, _, hchan2, _, _, _, _, _, _, _⟩
  simp [hchan2 i] at hgntE

private theorem init_exGntdWitness (n : Nat) :
    ∀ s : MState n, init n s → exGntdWitness n s := by
  intro s hinit hexTrue
  rcases hinit with ⟨_, _, _, _, _, _, hexGntd, _, _, _⟩
  simp [hexGntd] at hexTrue

private theorem init_invAckImpliesInvalid (n : Nat) :
    ∀ s : MState n, init n s → invAckImpliesInvalid n s := by
  intro s hinit i hack
  rcases hinit with ⟨_, _, _, hchan3, _, _, _, _, _, _⟩
  simp [hchan3 i] at hack

private theorem init_gntSExcludesInvAck (n : Nat) :
    ∀ s : MState n, init n s → gntSExcludesInvAck n s := by
  intro s hinit i hgntS
  rcases hinit with ⟨_, _, hchan2, _, _, _, _, _, _, _⟩
  simp [hchan2 i] at hgntS

private theorem init_cleanChannelWhenReady (n : Nat) :
    ∀ s : MState n, init n s → cleanChannelWhenReady n s := by
  intro s hinit _ i
  rcases hinit with ⟨_, _, _, hchan3, _, _, _, _, _, _⟩
  simp [hchan3 i]

private theorem init_invReasonProp (n : Nat) :
    ∀ s : MState n, init n s → invReasonProp n s := by
  intro s hinit i hinv
  rcases hinit with ⟨_, _, hchan2, _, _, _, _, _, _, _⟩
  simp [hchan2 i] at hinv

private theorem init_invAckClearsGrant (n : Nat) :
    ∀ s : MState n, init n s → invAckClearsGrant n s := by
  intro s hinit i hack
  rcases hinit with ⟨_, _, _, hchan3, _, _, _, _, _, _⟩
  simp [hchan3 i] at hack

private theorem init_invSetImpliesClean (n : Nat) :
    ∀ s : MState n, init n s → invSetImpliesClean n s := by
  intro s hinit i hinvSet
  rcases hinit with ⟨_, _, _, hchan3, hInvSet, _, _, _, _, _⟩
  simp [hInvSet i] at hinvSet

private theorem init_invClearsInvSet (n : Nat) :
    ∀ s : MState n, init n s → invClearsInvSet n s := by
  intro s hinit i hinv
  rcases hinit with ⟨_, _, hchan2, _, _, _, _, _, _, _⟩
  simp [hchan2 i] at hinv

private theorem init_chan3IsInvAck (n : Nat) :
    ∀ s : MState n, init n s → chan3IsInvAck n s := by
  intro s hinit i
  rcases hinit with ⟨_, _, _, hchan3, _, _, _, _, _, _⟩
  simp [hchan3 i]

private theorem init_invRequiresNonEmpty (n : Nat) :
    ∀ s : MState n, init n s → invRequiresNonEmpty n s := by
  intro s hinit i hinv
  rcases hinit with ⟨_, _, hchan2, _, _, _, _, _, _, _⟩
  simp [hchan2 i] at hinv

private theorem init_fullStrongInvariant (n : Nat) :
    ∀ s : MState n, init n s → fullStrongInvariant n s := by
  intro s hinit
  exact ⟨germanMessages_init_strongInvariant n s hinit,
         germanMessages_init_exclusiveSelfClean n s hinit,
         init_grantExcludesInvAck n s hinit,
         init_exGntdWitness n s hinit,
         init_invAckImpliesInvalid n s hinit,
         init_gntSExcludesInvAck n s hinit,
         init_cleanChannelWhenReady n s hinit,
         init_invReasonProp n s hinit,
         init_invAckClearsGrant n s hinit,
         init_invSetImpliesClean n s hinit,
         init_invClearsInvSet n s hinit,
         init_chan3IsInvAck n s hinit,
         init_invRequiresNonEmpty n s hinit⟩

/-- When chan2[i]=inv, chan3[i]=empty, and cache[i]≠E, exGntd must be false. -/
private theorem exGntd_false_of_inv_not_E
    {n : Nat} {s : MState n} {i : Fin n}
    (hs : strongInvariant n s)
    (hExWit : exGntdWitness n s)
    (hchan2i : (s.chan2 i).cmd = .inv)
    (hchan3i : (s.chan3 i).cmd = .empty)
    (hcacheNotE : (s.cache i).state ≠ .E) :
    s.exGntd = false := by
  rcases hs with ⟨_, hcacheShr, _, _, _, _, _, _, hchanShr, huniqShr⟩
  by_contra hexTrue
  simp at hexTrue
  have hshrI : s.shrSet i = true := hchanShr i (Or.inl hchan2i)
  obtain ⟨j, hj⟩ := hExWit hexTrue
  by_cases hji : j = i
  · subst hji
    rcases hj with hjE | hjGntE | hjAck
    · exact hcacheNotE hjE
    · simp [hchan2i] at hjGntE
    · simp [hchan3i] at hjAck
  · have hjShrFalse := huniqShr hexTrue i j (Ne.symm hji) hshrI
    rcases hj with hjE | hjGntE | hjAck
    · exact absurd (hcacheShr j (by intro h; cases hjE.symm.trans h))
        (by simp [hjShrFalse])
    · exact absurd (hchanShr j (Or.inr <| Or.inr <| Or.inl hjGntE))
        (by simp [hjShrFalse])
    · exact absurd (hchanShr j (Or.inr <| Or.inr <| Or.inr hjAck))
        (by simp [hjShrFalse])

private theorem strongInvariant_preserved_sendInvAck
    {n : Nat} {s : MState n} {i : Fin n}
    (hs : strongInvariant n s)
    (hExWit : exGntdWitness n s)
    (hstep : (s.chan2 i).cmd = .inv ∧ (s.chan3 i).cmd = .empty) :
    strongInvariant n (sendInvAckState s i) := by
  have hs0 := hs
  rcases hs with ⟨hinv, hcacheShr, hgrant, hinvAck, hnoExFalse, hinvSub, hexImpl, hnoSharedEx, hchanShr, huniqShr⟩
  rcases hstep with ⟨hchan2i, hchan3i⟩
  have hshrI : s.shrSet i = true := hchanShr i (Or.inl hchan2i)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- invariant (ctrlProp ∧ dataProp)
    refine ⟨?_, ?_⟩
    · intro j k hjk
      constructor
      · intro hjE
        by_cases hji : j = i
        · simp [hji, sendInvAckState] at hjE
        · by_cases hki : k = i
          · simp [hki, sendInvAckState]
          · have hjE' : (s.cache j).state = .E := by simpa [sendInvAckState, hji] using hjE
            simpa [sendInvAckState, hki] using (hinv.1 j k hjk).1 hjE'
      · intro hjS
        by_cases hji : j = i
        · simp [hji, sendInvAckState] at hjS
        · by_cases hki : k = i
          · left; simp [hki, sendInvAckState]
          · have hjS' : (s.cache j).state = .S := by simpa [sendInvAckState, hji] using hjS
            have hkIS := (hinv.1 j k hjk).2 hjS'
            rcases hkIS with hkI | hkS
            · left; simpa [sendInvAckState, hki] using hkI
            · right; simpa [sendInvAckState, hki] using hkS
    · constructor
      · simpa [sendInvAckState] using hinv.2.1
      · intro j hjNotI
        by_cases hji : j = i
        · simp [hji, sendInvAckState] at hjNotI
        · have hjNotI' : (s.cache j).state ≠ .I := by simpa [sendInvAckState, hji] using hjNotI
          simpa [sendInvAckState, hji] using hinv.2.2 j hjNotI'
  · -- cacheInShrSet
    intro j hjNotI
    by_cases hji : j = i
    · simp [hji, sendInvAckState] at hjNotI
    · exact hcacheShr j (by simpa [sendInvAckState, hji] using hjNotI)
  · -- grantDataProp
    intro j hjGrant
    by_cases hji : j = i
    · simp [hji, sendInvAckState] at hjGrant
    · have hjGrant' : (s.chan2 j).cmd = .gntS ∨ (s.chan2 j).cmd = .gntE := by
        simpa [sendInvAckState, hji] using hjGrant
      simpa [sendInvAckState, hji] using hgrant j hjGrant'
  · -- invAckDataProp
    intro j hexTrue hjAck
    by_cases hji : j = i
    · -- j = i: chan3[i] has data from conditional on cache[i]=E
      by_cases hcacheE : (s.cache i).state = .E
      · have hdata := hinv.2.2 i (by rw [hcacheE]; exact fun h => by simp at h)
        simp [hji, sendInvAckState, hcacheE, hdata]
      · -- cache[i]≠E → exGntd=false → contradiction with hexTrue
        have hexFalse := exGntd_false_of_inv_not_E hs0 hExWit hchan2i hchan3i hcacheE
        simp [sendInvAckState] at hexTrue
        rw [hexFalse] at hexTrue; simp at hexTrue
    · have hjAck' : (s.chan3 j).cmd = .invAck := by simpa [sendInvAckState, hji] using hjAck
      simp [sendInvAckState] at hexTrue
      simpa [sendInvAckState, hji] using hinvAck j hexTrue hjAck'
  · -- noExclusiveWhenFalse
    intro hexFalse j
    simp [sendInvAckState] at hexFalse
    by_cases hji : j = i
    · exact ⟨by simp [hji, sendInvAckState], by simp [hji, sendInvAckState]⟩
    · exact ⟨by simpa [sendInvAckState, hji] using (hnoExFalse hexFalse j).1,
             by simpa [sendInvAckState, hji] using (hnoExFalse hexFalse j).2⟩
  · -- invSetSubsetShrSet
    exact hinvSub
  · -- exclusiveImpliesExGntd
    intro j hjEx
    by_cases hji : j = i
    · rcases hjEx with hjE | hjGntE
      · simp [hji, sendInvAckState] at hjE
      · simp [hji, sendInvAckState] at hjGntE
    · have hjEx' : (s.cache j).state = .E ∨ (s.chan2 j).cmd = .gntE := by
        simpa [sendInvAckState, hji] using hjEx
      exact hexImpl j hjEx'
  · -- noSharedWhenExGntd
    intro hexTrue j
    simp [sendInvAckState] at hexTrue
    by_cases hji : j = i
    · exact ⟨by simp [hji, sendInvAckState], by simp [hji, sendInvAckState]⟩
    · simpa [sendInvAckState, hji] using hnoSharedEx hexTrue j
  · -- chanImpliesShrSet
    intro j hjMsg
    by_cases hji : j = i
    · rcases hjMsg with hjInv | hjGntS | hjGntE | hjAck
      · simp [hji, sendInvAckState] at hjInv
      · simp [hji, sendInvAckState] at hjGntS
      · simp [hji, sendInvAckState] at hjGntE
      · simpa [hji, sendInvAckState] using hshrI
    · have hjMsg' : ((s.chan2 j).cmd = .inv) ∨
        ((s.chan2 j).cmd = .gntS) ∨
        ((s.chan2 j).cmd = .gntE) ∨
        ((s.chan3 j).cmd = .invAck) := by
          simpa [sendInvAckState, hji] using hjMsg
      exact hchanShr j hjMsg'
  · -- uniqueShrSetWhenExGntd
    exact huniqShr

/-! ### strongInvariant preserved under recvInvAck and store -/

private theorem strongInvariant_preserved_recvInvAck
    {n : Nat} {s s' : MState n} {i : Fin n}
    (hs : strongInvariant n s)
    (hackI : invAckImpliesInvalid n s)
    (hInvSetClean : invSetImpliesClean n s)
    (hackClears : invAckClearsGrant n s)
    (hstep : (s.chan3 i).cmd = .invAck ∧ s.curCmd ≠ .empty ∧
      (((s.exGntd = true) ∧ s' = { s with
              chan3 := setFn s.chan3 i { (s.chan3 i) with cmd := .empty }
              shrSet := setFn s.shrSet i false
              exGntd := false
              memData := (s.chan3 i).data }) ∨
       ((s.exGntd = false) ∧ s' = { s with
              chan3 := setFn s.chan3 i { (s.chan3 i) with cmd := .empty }
              shrSet := setFn s.shrSet i false }))) :
    strongInvariant n s' := by
  rcases hs with ⟨hinv, hcacheShr, hgrant, hinvAck, hnoExFalse, hinvSub, hexImpl, hnoSharedEx,
    hchanShr, huniqShr⟩
  rcases hstep with ⟨hchan3i, _, hcases⟩
  have hcacheI : (s.cache i).state = .I := hackI i hchan3i
  have hshrI : s.shrSet i = true := hchanShr i (Or.inr <| Or.inr <| Or.inr hchan3i)
  have hchan2I : (s.chan2 i).cmd = .empty := hackClears i hchan3i
  rcases hcases with ⟨hexTrue, rfl⟩ | ⟨hexFalse, rfl⟩
  · have hnoE : ∀ j : Fin n, (s.cache j).state ≠ .E := by
      intro j hjE
      by_cases hji : j = i
      · subst hji
        simp [hcacheI] at hjE
      · have hjShr : s.shrSet j = true := hcacheShr j (by simp [hjE])
        have hjFalse := huniqShr hexTrue i j (Ne.symm hji) hshrI
        simp [hjShr] at hjFalse
    have hnoGntE : ∀ j : Fin n, (s.chan2 j).cmd ≠ .gntE := by
      intro j hjGntE
      by_cases hji : j = i
      · subst hji
        simp [hchan2I] at hjGntE
      · have hjShr : s.shrSet j = true := hchanShr j (Or.inr <| Or.inr <| Or.inl hjGntE)
        have hjFalse := huniqShr hexTrue i j (Ne.symm hji) hshrI
        simp [hjShr] at hjFalse
    have hnoS : ∀ j : Fin n, (s.cache j).state ≠ .S := fun j => (hnoSharedEx hexTrue j).1
    have hcacheI_all : ∀ j : Fin n, (s.cache j).state = .I := by
      intro j
      cases hstate : (s.cache j).state with
      | I => rfl
      | S => exact False.elim (hnoS j hstate)
      | E => exact False.elim (hnoE j hstate)
    have hmemAux : (s.chan3 i).data = s.auxData := hinvAck i hexTrue hchan3i
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro j k hjk
        constructor
        · intro hjE
          simp [hcacheI_all j] at hjE
        · intro hjS
          simp [hcacheI_all j] at hjS
      · constructor
        · intro _
          exact hmemAux
        · intro j hjNotI
          simp [hcacheI_all j] at hjNotI
    · intro j hjNotI
      simp [hcacheI_all j] at hjNotI
    · intro j hjGrant
      exact hgrant j hjGrant
    · intro j hexFalse' hjAck
      simp at hexFalse'
    · intro _ j
      exact ⟨hnoE j, hnoGntE j⟩
    · intro j hj
      by_cases hji : j = i
      · subst hji
        exfalso
        have : (s.chan3 j).cmd = .empty := hInvSetClean j hj
        simp [hchan3i] at this
      · simpa [setFn, hji] using hinvSub j hj
    · intro j hjEx
      rcases hjEx with hjE | hjGntE
      · exact False.elim (hnoE j hjE)
      · exact False.elim (hnoGntE j hjGntE)
    · intro hexFalse' j
      simp at hexFalse'
    · intro j hjMsg
      by_cases hji : j = i
      · subst hji
        rcases hjMsg with hjInv | hjRest
        · simp [hchan2I] at hjInv
        · rcases hjRest with hjGntS | hjRest
          · simp [hchan2I] at hjGntS
          · rcases hjRest with hjGntE | hjAck
            · simp [hchan2I] at hjGntE
            · simp at hjAck
      · have hjMsg' : ((s.chan2 j).cmd = .inv) ∨ ((s.chan2 j).cmd = .gntS) ∨
            ((s.chan2 j).cmd = .gntE) ∨ ((s.chan3 j).cmd = .invAck) := by
          rcases hjMsg with h | h | h | h
          · exact Or.inl <| by simpa [setFn, hji] using h
          · exact Or.inr <| Or.inl <| by simpa [setFn, hji] using h
          · exact Or.inr <| Or.inr <| Or.inl <| by simpa [setFn, hji] using h
          · exact Or.inr <| Or.inr <| Or.inr <| by simpa [setFn, hji] using h
        simpa [setFn, hji] using hchanShr j hjMsg'
    · intro hexFalse'
      simp at hexFalse'
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hinv
    · intro j hjNotI
      by_cases hji : j = i
      · subst hji
        simp [hcacheI] at hjNotI
      · simpa [setFn, hji] using hcacheShr j hjNotI
    · exact hgrant
    · intro j hexFalse' hjAck
      simp [hexFalse] at hexFalse'
    · intro _ j
      exact hnoExFalse hexFalse j
    · intro j hj
      by_cases hji : j = i
      · subst hji
        exfalso
        have : (s.chan3 j).cmd = .empty := hInvSetClean j hj
        simp [hchan3i] at this
      · simpa [setFn, hji] using hinvSub j hj
    · intro j hjEx
      rcases hjEx with hjE | hjGntE
      · exact False.elim ((hnoExFalse hexFalse j).1 hjE)
      · exact False.elim ((hnoExFalse hexFalse j).2 hjGntE)
    · intro hexTrue' j
      simp [hexFalse] at hexTrue'
    · intro j hjMsg
      by_cases hji : j = i
      · subst hji
        rcases hjMsg with hjInv | hjRest
        · simp [hchan2I] at hjInv
        · rcases hjRest with hjGntS | hjRest
          · simp [hchan2I] at hjGntS
          · rcases hjRest with hjGntE | hjAck
            · simp [hchan2I] at hjGntE
            · simp at hjAck
      · have hjMsg' : ((s.chan2 j).cmd = .inv) ∨ ((s.chan2 j).cmd = .gntS) ∨
            ((s.chan2 j).cmd = .gntE) ∨ ((s.chan3 j).cmd = .invAck) := by
          rcases hjMsg with h | h | h | h
          · exact Or.inl <| by simpa [setFn, hji] using h
          · exact Or.inr <| Or.inl <| by simpa [setFn, hji] using h
          · exact Or.inr <| Or.inr <| Or.inl <| by simpa [setFn, hji] using h
          · exact Or.inr <| Or.inr <| Or.inr <| by simpa [setFn, hji] using h
        simpa [setFn, hji] using hchanShr j hjMsg'
    · intro hexTrue'
      simp [hexFalse] at hexTrue'

private theorem strongInvariant_preserved_store
    {n : Nat} {s s' : MState n} {i : Fin n} {d : Val}
    (hs : strongInvariant n s)
    (hexcl : exclusiveSelfClean n s)
    (hstep : (s.cache i).state = .E ∧
      s' = { s with
              cache := setFn s.cache i { (s.cache i) with data := d }
              auxData := d }) :
    strongInvariant n s' := by
  rcases hstep with ⟨hcacheE, rfl⟩
  have ⟨hnoGntS, hnoGntE, hnoAck⟩ := hexcl i hcacheE
  exact strongInvariant_preserved_store_of_clean_self hs hcacheE hnoGntS hnoGntE hnoAck

end GermanMessages
