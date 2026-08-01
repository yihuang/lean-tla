import Leslie.Action
import Leslie.Rules.StatePred

/-! ## Chandy-Lamport Distributed Snapshot

    A compact `ActionSpec` model of the Chandy-Lamport snapshot algorithm
    over `n` processes with FIFO point-to-point channels.

    The model has two kinds of packets:

    - application packets carrying a `Nat` payload
    - `marker` packets used by the snapshot algorithm

    The state also contains a small amount of ghost/history information:

    - `recvLog src dst` records the sequence of application payloads ever
      received on channel `src → dst`
    - `recordCut src dst` is the length of `recvLog src dst` when `dst`
      records its local state
    - `closeCut src dst` is the length of `recvLog src dst` when `dst`
      receives the marker from `src`

    These ghosts make the main snapshot invariants easy to state:
    the recorded channel state is exactly the slice of `recvLog` between
    `recordCut` and `closeCut` (or the current frontier if the marker has
    not yet arrived).

    ### Protocol overview

    Each process executes ordinary local steps and may send or receive
    application packets at any time. A snapshot starts when some process
    records its local state and sends one `marker` on each outgoing channel.

    The intended Chandy-Lamport behaviour is:

    - when a process records for the first time, it stores its current local
      state in `snapLocal` and remembers the current receive frontier of every
      incoming channel in `recordCut`
    - while an incoming channel's marker has not yet been seen, every
      application packet received on that channel is appended to `chanSnap`
    - when the marker for `src → dst` is received, recording for that channel
      stops and `closeCut src dst` is fixed to the current receive frontier

    In this encoding, `chanSnap` is the executable state used by the protocol,
    while `recvLog`, `recordCut`, and `closeCut` are ghost variables used to
    characterize the snapshot mathematically.
-/

open TLA

namespace ChandyLamport

variable (n : Nat)

/-- Packets carried on FIFO channels. -/
inductive Packet where
  | app (payload : Nat)
  | marker
  deriving DecidableEq, Repr

/-- Global state for Chandy-Lamport. -/
structure CLState (n : Nat) where
  locals : Fin n → Nat
  chan : Fin n → Fin n → List Packet
  recorded : Fin n → Bool
  snapLocal : Fin n → Nat
  sentMarker : Fin n → Fin n → Bool
  seenMarker : Fin n → Fin n → Bool
  chanSnap : Fin n → Fin n → List Nat
  recvLog : Fin n → Fin n → List Nat
  recordCut : Fin n → Fin n → Nat
  closeCut : Fin n → Fin n → Nat

/-- Replace a single channel `src → dst` by `msgs`. -/
def updateChan (s : CLState n) (src dst : Fin n) (msgs : List Packet) : Fin n → Fin n → List Packet :=
  fun i j =>
    if i = src then
      if j = dst then msgs else s.chan i j
    else
      s.chan i j

/-- Record process `p`'s local state and enqueue markers on all outgoing channels. -/
def recordProcess (s : CLState n) (p : Fin n) : CLState n :=
  { s with
    recorded := fun q => if q = p then true else s.recorded q,
    snapLocal := fun q => if q = p then s.locals p else s.snapLocal q,
    sentMarker := fun src dst =>
      if src = p then
        if dst = p then false else true
      else
        s.sentMarker src dst,
    chan := fun src dst =>
      if src = p then
        if dst = p then s.chan src dst else s.chan src dst ++ [.marker]
      else
        s.chan src dst,
    recordCut := fun src dst =>
      if dst = p then (s.recvLog src p).length else s.recordCut src dst }

theorem updateChan_self (s : CLState n) {src dst p : Fin n} {msgs : List Packet}
    (hneq : src ≠ dst) :
    updateChan n s src dst msgs p p = s.chan p p := by
  unfold updateChan
  by_cases hps : p = src
  · by_cases hpd : p = dst
    · exfalso
      exact hneq (hps.symm.trans hpd)
    · have hsd : src ≠ dst := by
        intro hsdEq
        exact hpd (hps.trans hsdEq)
      simp [hps, hsd]
  · simp [hps]

theorem recordProcess_chan_self (s : CLState n) (q p : Fin n) :
    (recordProcess n s q).chan p p = s.chan p p := by
  by_cases hpq : p = q
  · subst hpq
    simp [recordProcess]
  · simp [recordProcess, hpq]

theorem recordProcess_chanSnap_self (s : CLState n) (q p : Fin n) :
    (recordProcess n s q).chanSnap p p = s.chanSnap p p := by
  simp [recordProcess]

theorem recordProcess_sent_self (s : CLState n) (q p : Fin n)
    (hself : s.sentMarker p p = false) :
    (recordProcess n s q).sentMarker p p = false := by
  by_cases hpq : p = q
  · subst hpq
    simp [recordProcess]
  · simp [recordProcess, hpq, hself]

theorem recordProcess_seen_self (s : CLState n) (q p : Fin n)
    (hself : s.seenMarker p p = false) :
    (recordProcess n s q).seenMarker p p = false := by
  simp [recordProcess, hself]

theorem sendApp_chan_self (s : CLState n) {src dst p : Fin n} {payload : Nat}
    (hneq : src ≠ dst) :
    (if p = src then if p = dst then s.chan p p ++ [Packet.app payload] else s.chan p p else s.chan p p) =
      s.chan p p := by
  by_cases hps : p = src
  · by_cases hpd : p = dst
    · exfalso
      exact hneq (hps.symm.trans hpd)
    · have hsd : src ≠ dst := by
        intro hsdEq
        exact hpd (hps.trans hsdEq)
      simp [hps, hsd]
  · simp [hps]

theorem recvApp_chanSnap_self (s : CLState n) {src dst p : Fin n} {payload : Nat}
    (hneq : src ≠ dst) :
    (if p = src then
        if p = dst then
          if s.recorded dst = true ∧ s.seenMarker src dst = false
          then s.chanSnap p p ++ [payload]
          else s.chanSnap p p
        else s.chanSnap p p
      else s.chanSnap p p) = s.chanSnap p p := by
  by_cases hps : p = src
  · by_cases hpd : p = dst
    · exfalso
      exact hneq (hps.symm.trans hpd)
    · have hsd : src ≠ dst := by
        intro hsdEq
        exact hpd (hps.trans hsdEq)
      simp [hps, hsd]
  · simp [hps]

theorem recvMarker_seen_self (s : CLState n) {src dst p : Fin n}
    (hneq : src ≠ dst) (hself : s.seenMarker p p = false) :
    (if p = src then decide (p = dst) || s.seenMarker p p else s.seenMarker p p) = false := by
  by_cases hps : p = src
  · by_cases hpd : p = dst
    · exfalso
      exact hneq (hps.symm.trans hpd)
    · have hsd : src ≠ dst := by
        intro hsdEq
        exact hpd (hps.trans hsdEq)
      simpa [hps, hsd] using hself
  · simp [hps, hself]

/-- Slice `xs[lo, hi)`. Used to state channel-snapshot invariants. -/
def channelWindow (xs : List Nat) (lo hi : Nat) : List Nat :=
  (xs.drop lo).take (hi - lo)

/-- A marker is still in transit on `src → dst`. -/
def markerInTransit (s : CLState n) (src dst : Fin n) : Prop :=
  Packet.marker ∈ s.chan src dst

theorem count_marker_append_app (xs : List Packet) (payload : Nat) :
    (xs ++ [Packet.app payload]).count Packet.marker = xs.count Packet.marker := by
  simp

theorem count_marker_append_marker_zero (xs : List Packet)
    (h : xs.count Packet.marker = 0) :
    (xs ++ [Packet.marker]).count Packet.marker = 1 := by
  rw [List.count_append, h]
  simp

theorem count_marker_tail_of_head_marker_le_one (xs : List Packet)
    (h : (Packet.marker :: xs).count Packet.marker ≤ 1) :
    xs.count Packet.marker = 0 := by
  simp at h
  omega

theorem marker_mem_of_count_pos (xs : List Packet)
    (h : 0 < xs.count Packet.marker) :
    Packet.marker ∈ xs := by
  simpa using List.count_pos_iff.mp h

theorem drop_append_singleton_of_le {α : Type} (xs : List α) (x : α) (n : Nat)
    (h : n ≤ xs.length) :
    (xs ++ [x]).drop n = xs.drop n ++ [x] := by
  induction xs generalizing n with
  | nil =>
      simp at h
      subst n
      simp
  | cons y ys ih =>
      cases n with
      | zero =>
          simp
      | succ n =>
          simp at h
          simp [ih n h]

theorem take_append_singleton_of_le {α : Type} (xs : List α) (x : α) (n : Nat)
    (h : n ≤ xs.length) :
    (xs ++ [x]).take n = xs.take n := by
  induction xs generalizing n with
  | nil =>
      simp at h
      subst n
      simp
  | cons y ys ih =>
      cases n with
      | zero =>
          simp
      | succ n =>
          simp at h
          simp [ih n h]

theorem take_length_self {α : Type} (xs : List α) :
    xs.take xs.length = xs := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

theorem channelWindow_at_end (xs : List Nat) (lo : Nat) :
    channelWindow xs lo xs.length = xs.drop lo := by
  unfold channelWindow
  rw [List.take_of_length_le]
  simp [List.length_drop]

theorem channelWindow_append_irrel (xs : List Nat) (x lo hi : Nat)
    (hlo : lo ≤ hi) (hhi : hi ≤ xs.length) :
    channelWindow (xs ++ [x]) lo hi = channelWindow xs lo hi := by
  unfold channelWindow
  rw [drop_append_singleton_of_le xs x lo (Nat.le_trans hlo hhi)]
  have htake : hi - lo ≤ (xs.drop lo).length := by
    simpa [List.length_drop] using Nat.sub_le_sub_right hhi lo
  rw [take_append_singleton_of_le (xs.drop lo) x (hi - lo) htake]

/-- Actions of the Chandy-Lamport system. -/
inductive CLAction (n : Nat) where
  | localStep (p : Fin n)
  | sendApp (src dst : Fin n) (payload : Nat)
  | recvApp (src dst : Fin n)
  | startSnapshot (p : Fin n)
  | recvMarker (src dst : Fin n)

/-- The concrete Chandy-Lamport `ActionSpec`. -/
def clSpec : ActionSpec (CLState n) (CLAction n) where
  init := fun s =>
    (∀ p, s.locals p = 0) ∧
    (∀ p q, s.chan p q = []) ∧
    (∀ p, s.recorded p = false) ∧
    (∀ p, s.snapLocal p = 0) ∧
    (∀ p q, s.sentMarker p q = false) ∧
    (∀ p q, s.seenMarker p q = false) ∧
    (∀ p q, s.chanSnap p q = []) ∧
    (∀ p q, s.recvLog p q = []) ∧
    (∀ p q, s.recordCut p q = 0) ∧
    (∀ p q, s.closeCut p q = 0)
  actions := fun
    | .localStep p => {
        gate := fun _ => True
        transition := fun s s' =>
          s' = { s with locals := fun q => if q = p then s.locals p + 1 else s.locals q } }
    | .sendApp src dst payload => {
        gate := fun _ => src ≠ dst
        transition := fun s s' =>
          s' = { s with
            chan := fun i j =>
              if i = src then
                if j = dst then s.chan i j ++ [.app payload] else s.chan i j
              else
                s.chan i j } }
    | .recvApp src dst => {
        gate := fun s =>
          src ≠ dst ∧ ∃ payload rest, s.chan src dst = .app payload :: rest
        transition := fun s s' =>
          ∃ payload rest, src ≠ dst ∧ s.chan src dst = .app payload :: rest ∧
            s' = { s with
              locals := fun q => if q = dst then s.locals dst + payload else s.locals q,
              chan := updateChan n s src dst rest,
              recvLog := fun i j =>
                if i = src then
                  if j = dst then s.recvLog i j ++ [payload] else s.recvLog i j
                else
                  s.recvLog i j,
              chanSnap := fun i j =>
                if i = src then
                  if j = dst then
                    if s.recorded dst ∧ ¬ s.seenMarker src dst
                    then s.chanSnap i j ++ [payload]
                    else s.chanSnap i j
                  else
                    s.chanSnap i j
                else
                  s.chanSnap i j } }
    | .startSnapshot p => {
        gate := fun s => s.recorded p = false
        transition := fun s s' =>
          s' = recordProcess n s p }
    | .recvMarker src dst => {
        gate := fun s =>
          src ≠ dst ∧ ∃ rest, s.chan src dst = .marker :: rest
        transition := fun s s' =>
          ∃ rest, src ≠ dst ∧ s.chan src dst = .marker :: rest ∧
            let s1 : CLState n := { s with chan := updateChan n s src dst rest }
            let s2 : CLState n := if s.recorded dst then s1 else recordProcess n s1 dst
            let cut := (s.recvLog src dst).length
            s' = { s2 with
              seenMarker := fun i j =>
                if i = src then
                  if j = dst then true else s2.seenMarker i j
                else
                  s2.seenMarker i j,
              closeCut := fun i j =>
                if i = src then
                  if j = dst then cut else s2.closeCut i j
                else
                  s2.closeCut i j } }
  fair := []

/-! ## Main invariants

    These are the key state predicates one would preserve inductively in a
    safety proof of Chandy-Lamport. They are stated here, but not yet proved.
-/

/-- Self-channels are permanently unused. -/
def invNoSelfTraffic (s : CLState n) : Prop :=
  ∀ p,
    s.chan p p = [] ∧
    s.chanSnap p p = [] ∧
    s.sentMarker p p = false ∧
    s.seenMarker p p = false

/-- Markers are sent only after a process records, and seen only after send. -/
def invMarkerBookkeeping (s : CLState n) : Prop :=
  (∀ src dst, s.sentMarker src dst = true → src ≠ dst ∧ s.recorded src = true) ∧
  (∀ src dst, s.seenMarker src dst = true →
    src ≠ dst ∧ s.sentMarker src dst = true ∧ s.recorded dst = true)

/-- Each FIFO channel contains at most one marker packet. -/
def invAtMostOneMarker (s : CLState n) : Prop :=
  ∀ src dst, (s.chan src dst).count Packet.marker ≤ 1

/-- If the marker on `src → dst` has been sent but not yet seen, then it is
    still present in the channel buffer. -/
def invPendingMarker (s : CLState n) : Prop :=
  ∀ src dst,
    s.sentMarker src dst = true →
    s.seenMarker src dst = false →
    markerInTransit n s src dst

/-- A process only starts storing channel state after it has recorded locally. -/
def invUnrecordedChannelsEmpty (s : CLState n) : Prop :=
  ∀ src dst, s.recorded dst = false → s.chanSnap src dst = []

/-- The cut indices are well formed with respect to the receive history. -/
def invCutsWellFormed (s : CLState n) : Prop :=
  (∀ src dst, s.recorded dst = true → s.recordCut src dst ≤ (s.recvLog src dst).length) ∧
  (∀ src dst, s.seenMarker src dst = true →
    s.recordCut src dst ≤ s.closeCut src dst ∧
    s.closeCut src dst ≤ (s.recvLog src dst).length)

/-- While the marker on `src → dst` is still pending, the recorded channel state
    is the suffix of the receive log starting at the receiver's local-cut index. -/
def invOpenChannelWindow (s : CLState n) : Prop :=
  ∀ src dst,
    s.recorded dst = true →
    s.seenMarker src dst = false →
    s.chanSnap src dst = (s.recvLog src dst).drop (s.recordCut src dst)

/-- Once the marker on `src → dst` has been seen, the recorded channel state is
    frozen to the slice of the receive log between `recordCut` and `closeCut`. -/
def invClosedChannelWindow (s : CLState n) : Prop :=
  ∀ src dst,
    s.seenMarker src dst = true →
    s.chanSnap src dst =
      channelWindow ((s.recvLog src dst)) (s.recordCut src dst) (s.closeCut src dst)

/-- Combined invariant package for the snapshot algorithm. -/
def snapshotInv (s : CLState n) : Prop :=
  invNoSelfTraffic n s ∧
  invMarkerBookkeeping n s ∧
  invAtMostOneMarker n s ∧
  invPendingMarker n s ∧
  invUnrecordedChannelsEmpty n s ∧
  invCutsWellFormed n s ∧
  invOpenChannelWindow n s ∧
  invClosedChannelWindow n s

def sentMarker_exact (s : CLState n) : Prop :=
  ∀ src dst, s.sentMarker src dst = true ↔ src ≠ dst ∧ s.recorded src = true

def markerCount_exact (s : CLState n) : Prop :=
  ∀ src dst,
    (s.chan src dst).count Packet.marker =
      if s.sentMarker src dst = true ∧ s.seenMarker src dst = false then 1 else 0

def seenMarker_exact (s : CLState n) : Prop :=
  ∀ src dst,
    s.seenMarker src dst = true →
      src ≠ dst ∧ s.sentMarker src dst = true ∧ s.recorded dst = true

def markerCoreInv (s : CLState n) : Prop :=
  sentMarker_exact n s ∧ markerCount_exact n s ∧ seenMarker_exact n s

/-
`markerCoreInv` is the exact bookkeeping layer for markers.  Instead of
proving the public marker properties (`invMarkerBookkeeping`,
`invAtMostOneMarker`, `invPendingMarker`) independently, we first show the
stronger facts:

- `sentMarker` is exactly "the sender has already recorded"
- the channel buffer contains a marker iff it has been sent and not yet seen
- `seenMarker` implies both endpoints are in the expected recorded state

The exported marker invariants are then projections from this exact core.
-/

def strongSnapshotInv (s : CLState n) : Prop :=
  invNoSelfTraffic n s ∧
  markerCoreInv n s ∧
  invUnrecordedChannelsEmpty n s ∧
  invCutsWellFormed n s ∧
  invOpenChannelWindow n s ∧
  invClosedChannelWindow n s

theorem sentMarker_false_of_recorded_false {s : CLState n}
    (hcore : markerCoreInv n s) {src dst : Fin n}
    (hrec : s.recorded src = false) :
    s.sentMarker src dst = false := by
  rcases hcore with ⟨hsent, _, _⟩
  by_cases hsent' : s.sentMarker src dst = true
  · have h := (hsent src dst).1 hsent'
    simpa [hrec] using h.2
  · cases hbool : s.sentMarker src dst with
    | false => rfl
    | true => exact False.elim (hsent' hbool)

theorem seenMarker_false_of_recorded_false {s : CLState n}
    (hcore : markerCoreInv n s) {src dst : Fin n}
    (hrec : s.recorded src = false) :
    s.seenMarker src dst = false := by
  rcases hcore with ⟨hsent, _, hseen⟩
  by_cases hseen' : s.seenMarker src dst = true
  · have h := hseen src dst hseen'
    have hsent' := h.2.1
    have hsentInfo := (hsent src dst).1 hsent'
    simpa [hrec] using hsentInfo.2
  · cases hbool : s.seenMarker src dst with
    | false => rfl
    | true => exact False.elim (hseen' hbool)

theorem markerCount_le_one_of_exact {s : CLState n}
    (hcount : markerCount_exact n s) (src dst : Fin n) :
    (s.chan src dst).count Packet.marker ≤ 1 := by
  rw [hcount src dst]
  split <;> omega

theorem head_marker_implies_sent_true_seen_false {s : CLState n}
    (hcore : markerCoreInv n s) {src dst : Fin n} {rest : List Packet}
    (hhead : s.chan src dst = Packet.marker :: rest) :
    s.sentMarker src dst = true ∧ s.seenMarker src dst = false := by
  rcases hcore with ⟨_, hcount, _⟩
  have hpos : 0 < (s.chan src dst).count Packet.marker := by
    rw [hhead]
    simp
  by_cases hpending : s.sentMarker src dst = true ∧ s.seenMarker src dst = false
  · exact hpending
  · rw [hcount src dst, if_neg hpending] at hpos
    omega

theorem markerCoreInv_implies_markerBookkeeping {s : CLState n}
    (hcore : markerCoreInv n s) :
    invMarkerBookkeeping n s := by
  rcases hcore with ⟨hsent, _, hseen⟩
  constructor
  · intro src dst h
    exact (hsent src dst).1 h
  · intro src dst h
    exact hseen src dst h

theorem markerCoreInv_implies_atMostOneMarker {s : CLState n}
    (hcore : markerCoreInv n s) :
    invAtMostOneMarker n s := by
  rcases hcore with ⟨_, hcount, _⟩
  intro src dst
  exact markerCount_le_one_of_exact n hcount src dst

theorem markerCoreInv_implies_pendingMarker {s : CLState n}
    (hcore : markerCoreInv n s) :
    invPendingMarker n s := by
  rcases hcore with ⟨_, hcount, _⟩
  intro src dst hsent hseen
  have hcount' : (s.chan src dst).count Packet.marker = 1 := by
    rw [hcount src dst]
    simp [hsent, hseen]
  exact List.count_pos_iff.1 (by omega)

theorem strongSnapshotInv_implies_snapshotInv {s : CLState n}
    (h : strongSnapshotInv n s) :
    snapshotInv n s := by
  rcases h with ⟨hself, hcore, hunrec, hcuts, hopen, hclosed⟩
  exact ⟨hself,
    markerCoreInv_implies_markerBookkeeping n hcore,
    markerCoreInv_implies_atMostOneMarker n hcore,
    markerCoreInv_implies_pendingMarker n hcore,
    hunrec, hcuts, hopen, hclosed⟩

theorem sentMarker_false_of_not_recorded_src {s : CLState n}
    (hcore : markerCoreInv n s) {src dst : Fin n}
    (hrec : s.recorded src = false) :
    s.sentMarker src dst = false := by
  rcases hcore with ⟨hsent, _, _⟩
  by_cases h : s.sentMarker src dst = true
  · have hs := (hsent src dst).mp h
    simp [hrec] at hs
  · simp [h]

theorem seenMarker_false_of_not_recorded_src {s : CLState n}
    (hcore : markerCoreInv n s) {src dst : Fin n}
    (hrec : s.recorded src = false) :
    s.seenMarker src dst = false := by
  rcases hcore with ⟨hsent, _, hseen⟩
  by_cases h : s.seenMarker src dst = true
  · have hs := hseen src dst h
    have hsentTrue := hs.2.1
    have hsrc := (hsent src dst).mp hsentTrue
    simp [hrec] at hsrc
  · simp [h]

theorem seenMarker_false_of_not_recorded_dst {s : CLState n}
    (hcore : markerCoreInv n s) {src dst : Fin n}
    (hrec : s.recorded dst = false) :
    s.seenMarker src dst = false := by
  rcases hcore with ⟨_, _, hseen⟩
  by_cases h : s.seenMarker src dst = true
  · have hs := hseen src dst h
    simp [hrec] at hs
  · simp [h]

theorem sent_false_of_unrecorded_source (s : CLState n)
    (hsent : sentMarker_exact n s) {src dst : Fin n}
    (hrec : s.recorded src = false) :
    s.sentMarker src dst = false := by
  by_cases h : s.sentMarker src dst = true
  · have hs := (hsent src dst).mp h
    simp [hrec] at hs
  · simp [h]

theorem seen_false_of_unrecorded_source (s : CLState n)
    (hsent : sentMarker_exact n s) (hseen : seenMarker_exact n s)
    {src dst : Fin n} (hrec : s.recorded src = false) :
    s.seenMarker src dst = false := by
  by_cases h : s.seenMarker src dst = true
  · have hs := hseen src dst h
    have hsentTrue := hs.2.1
    have hsrc := (hsent src dst).mp hsentTrue
    simp [hrec] at hsrc
  · simp [h]

theorem marker_head_sent_unseen {s : CLState n}
    (hcore : markerCoreInv n s) {src dst : Fin n} {rest : List Packet}
    (hhead : s.chan src dst = Packet.marker :: rest) :
    s.sentMarker src dst = true ∧ s.seenMarker src dst = false := by
  rcases hcore with ⟨_, hcount, _⟩
  have hcnt := hcount src dst
  rw [hhead] at hcnt
  by_cases hcond : s.sentMarker src dst = true ∧ s.seenMarker src dst = false
  · exact hcond
  · simp [hcond] at hcnt

theorem marker_head_tail_count_zero {s : CLState n}
    (hcore : markerCoreInv n s) {src dst : Fin n} {rest : List Packet}
    (hhead : s.chan src dst = Packet.marker :: rest) :
    rest.count Packet.marker = 0 := by
  have hcond := marker_head_sent_unseen (n := n) hcore hhead
  rcases hcore with ⟨_, hcount, _⟩
  have hcnt : (Packet.marker :: rest).count Packet.marker = 1 := by
    simpa [hhead, hcond] using hcount src dst
  have hle : (Packet.marker :: rest).count Packet.marker ≤ 1 := by
    omega
  exact count_marker_tail_of_head_marker_le_one rest hle

theorem sent_true_seen_false_of_head_marker (s : CLState n)
    (hcount : markerCount_exact n s) {src dst : Fin n} {rest : List Packet}
    (hhead : s.chan src dst = Packet.marker :: rest) :
    s.sentMarker src dst = true ∧ s.seenMarker src dst = false := by
  by_cases hcond : s.sentMarker src dst = true ∧ s.seenMarker src dst = false
  · exact hcond
  · have hcnt := hcount src dst
    rw [hhead] at hcnt
    simp [hcond] at hcnt

theorem tail_marker_count_zero_of_head_marker (s : CLState n)
    (hcount : markerCount_exact n s) {src dst : Fin n} {rest : List Packet}
    (hhead : s.chan src dst = Packet.marker :: rest) :
    rest.count Packet.marker = 0 := by
  have hcond := sent_true_seen_false_of_head_marker n s hcount hhead
  have hcnt : (Packet.marker :: rest).count Packet.marker = 1 := by
    simpa [hhead, hcond] using hcount src dst
  have hle : (Packet.marker :: rest).count Packet.marker ≤ 1 := by
    omega
  exact count_marker_tail_of_head_marker_le_one rest hle

def channelSnap_exact (s : CLState n) : Prop :=
  ∀ src dst,
    s.chanSnap src dst =
      if s.recorded dst then
        channelWindow (s.recvLog src dst) (s.recordCut src dst)
          (if s.seenMarker src dst then s.closeCut src dst else (s.recvLog src dst).length)
      else
        []

def windowCoreInv (s : CLState n) : Prop :=
  invCutsWellFormed n s ∧ channelSnap_exact n s

def snapshotCoreInv (s : CLState n) : Prop :=
  invNoSelfTraffic n s ∧ markerCoreInv n s ∧ windowCoreInv n s

/-! ### Proof outline

    The proof is organized in three layers.

    1. `invNoSelfTraffic`:
       self-channels are never used, so they can be discharged by a direct
       action-by-action proof.

    2. `markerCoreInv`:
       marker traffic is proved via exact equalities rather than weaker
       one-way implications. This makes the `recvMarker` and
       `startSnapshot` cases algebraic: counting markers in the channel
       buffer determines whether a marker is pending.

    3. `windowCoreInv` / `snapshotCoreInv`:
       the snapshot content is proved with the stronger predicate
       `channelSnap_exact`, saying that `chanSnap src dst` is exactly the
       appropriate window of `recvLog src dst`.

       - before `dst` records: the window is empty
       - after `dst` records but before `src`'s marker arrives: the window is
         the suffix starting at `recordCut`
       - after the marker arrives: the window is frozen to the slice
         `[recordCut, closeCut)`

    The user-facing invariants are then obtained by projecting from
    `snapshotCoreInv`. This keeps the inductive step concentrated in one place
    and leaves the exported theorems easy to read.
-/

theorem sentMarker_false_of_unrecorded
    {s : CLState n} (hsent : sentMarker_exact n s)
    {src dst : Fin n} (hrec : s.recorded src = false) :
    s.sentMarker src dst = false := by
  by_cases hsend : s.sentMarker src dst = true
  · have h := (hsent src dst).mp hsend
    simp [hrec] at h
  · exact Bool.eq_false_iff.mpr hsend

theorem seenMarker_false_of_unrecorded
    {s : CLState n} (hseen : seenMarker_exact n s)
    {src dst : Fin n} (hrec : s.recorded dst = false) :
    s.seenMarker src dst = false := by
  by_cases hvør : s.seenMarker src dst = true
  · have h := hseen src dst hvør
    simp [hrec] at h
  · exact Bool.eq_false_iff.mpr hvør

theorem marker_head_info
    {s : CLState n} (hcount : markerCount_exact n s)
    {src dst : Fin n} {rest : List Packet}
    (hhead : s.chan src dst = Packet.marker :: rest) :
    s.sentMarker src dst = true ∧ s.seenMarker src dst = false ∧ rest.count Packet.marker = 0 := by
  exact ⟨(sent_true_seen_false_of_head_marker n s hcount hhead).1,
    (sent_true_seen_false_of_head_marker n s hcount hhead).2,
    tail_marker_count_zero_of_head_marker n s hcount hhead⟩

theorem seenMarker_false_of_unsent
    {s : CLState n} (hseen : seenMarker_exact n s)
    {src dst : Fin n} (hsent : s.sentMarker src dst = false) :
    s.seenMarker src dst = false := by
  by_cases hvør : s.seenMarker src dst = true
  · have h := hseen src dst hvør
    simp [hsent] at h
  · exact Bool.eq_false_iff.mpr hvør

theorem invNoSelfTraffic_init :
    ∀ s, (clSpec n).init s → invNoSelfTraffic n s := by
  intro s hinit p
  rcases hinit with ⟨hlocals, hchan, hrecorded, hsnapLocal, hsent, hseen, hchanSnap, hrecvLog, hrecordCut, hcloseCut⟩
  exact ⟨hchan p p, hchanSnap p p, hsent p p, hseen p p⟩

theorem invNoSelfTraffic_next :
    ∀ s s', (∃ a, ((clSpec n).actions a).fires s s') → invNoSelfTraffic n s → invNoSelfTraffic n s' := by
  intro s s' ⟨a, hfire⟩ hinv p
  rcases hinv p with ⟨hchanpp, hsnapp, hsentpp, hseenpp⟩
  cases a with
  | localStep q =>
      simp [clSpec, GatedAction.fires] at hfire
      rcases hfire with rfl
      exact ⟨hchanpp, ⟨hsnapp, ⟨hsentpp, hseenpp⟩⟩⟩
  | sendApp src dst payload =>
      simp [clSpec, GatedAction.fires] at hfire
      rcases hfire with ⟨hneq, rfl⟩
      exact ⟨by
          have hch := sendApp_chan_self n s (src := src) (dst := dst) (p := p) (payload := payload) hneq
          simpa [hch] using hchanpp,
        ⟨hsnapp, ⟨hsentpp, hseenpp⟩⟩⟩
  | recvApp src dst =>
      simp [clSpec, GatedAction.fires] at hfire
      rcases hfire with ⟨_, hneq, payload, rest, hhead, rfl⟩
      exact ⟨by
          have hch := updateChan_self n s (src := src) (dst := dst) (p := p) (msgs := rest) hneq
          simpa [hch] using hchanpp,
        ⟨by
            have hsnap := recvApp_chanSnap_self n s (src := src) (dst := dst) (p := p) (payload := payload) hneq
            simpa [hsnap] using hsnapp,
          ⟨hsentpp, hseenpp⟩⟩⟩
  | startSnapshot q =>
      simp [clSpec, GatedAction.fires] at hfire
      rcases hfire with ⟨_, rfl⟩
      exact ⟨by simpa [recordProcess_chan_self n s q p] using hchanpp,
        ⟨by simpa [recordProcess_chanSnap_self n s q p] using hsnapp,
          ⟨by simpa using recordProcess_sent_self n s q p hsentpp,
            by simpa using recordProcess_seen_self n s q p hseenpp⟩⟩⟩
  | recvMarker src dst =>
      by_cases hrec : s.recorded dst
      · simp [clSpec, GatedAction.fires, hrec] at hfire
        rcases hfire with ⟨_, hneq, rest, hhead, rfl⟩
        exact ⟨by
            have hch := updateChan_self n s (src := src) (dst := dst) (p := p) (msgs := rest) hneq
            simpa [hch] using hchanpp,
          ⟨hsnapp, ⟨hsentpp, by simpa using recvMarker_seen_self n s hneq hseenpp⟩⟩⟩
      · simp [clSpec, GatedAction.fires, hrec] at hfire
        rcases hfire with ⟨_, hneq, rest, hhead, rfl⟩
        let s1 : CLState n := { s with chan := updateChan n s src dst rest }
        exact ⟨by
            have hs1 : s1.chan p p = s.chan p p := by
              simp [s1, updateChan_self n s hneq]
            calc
              (recordProcess n s1 dst).chan p p = s1.chan p p := recordProcess_chan_self n s1 dst p
              _ = s.chan p p := hs1
              _ = [] := hchanpp,
          ⟨by
            have hs1 : s1.chanSnap p p = s.chanSnap p p := by simp [s1]
            calc
              (recordProcess n s1 dst).chanSnap p p = s1.chanSnap p p := recordProcess_chanSnap_self n s1 dst p
              _ = s.chanSnap p p := hs1
              _ = [] := hsnapp,
            ⟨by
              have hs1 : s1.sentMarker p p = s.sentMarker p p := by simp [s1]
              have hbase : s1.sentMarker p p = false := by simpa [s1] using hsentpp
              calc
                (recordProcess n s1 dst).sentMarker p p = false := recordProcess_sent_self n s1 dst p hbase
                _ = false := rfl,
              by
                have hs1 : s1.seenMarker p p = s.seenMarker p p := by simp [s1]
                have hbase : s1.seenMarker p p = false := by simpa [s1] using hseenpp
                have hseen2 : (recordProcess n s1 dst).seenMarker p p = false := by
                  simpa using recordProcess_seen_self n s1 dst p hbase
                simpa [s1] using recvMarker_seen_self n (recordProcess n s1 dst) hneq hseen2⟩⟩⟩

theorem noSelfTraffic_invariant :
    pred_implies (clSpec n).toSpec.safety [tlafml| □ ⌜invNoSelfTraffic n⌝] := by
  apply init_invariant
  · exact invNoSelfTraffic_init n
  · intro s s' hnext hinv
    exact invNoSelfTraffic_next n s s' hnext hinv

theorem markerCoreInv_init :
    ∀ s, (clSpec n).init s → markerCoreInv n s := by
  intro s hinit
  rcases hinit with ⟨hlocals, hchan, hrecorded, hsnapLocal, hsent, hseen, hchanSnap, hrecvLog, hrecordCut, hcloseCut⟩
  refine ⟨?_, ?_, ?_⟩
  · intro src dst
    simp [hsent src dst, hrecorded src]
  · intro src dst
    simp [hchan src dst, hsent src dst, hseen src dst]
  · intro src dst h
    simp [hseen src dst] at h

theorem markerCoreInv_next :
    ∀ s s', (∃ a, ((clSpec n).actions a).fires s s') → markerCoreInv n s → markerCoreInv n s' := by
  intro s s' ⟨a, hfire⟩ ⟨hsent, hcount, hseen⟩
  cases a with
  | localStep q =>
      simp [clSpec, GatedAction.fires] at hfire
      rcases hfire with rfl
      exact ⟨hsent, hcount, hseen⟩
  | sendApp src dst payload =>
      simp [clSpec, GatedAction.fires] at hfire
      rcases hfire with ⟨hneq, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · intro i j
        simp [hsent i j]
      · intro i j
        by_cases his : i = src
        · by_cases hjd : j = dst
          · simpa [his, hjd, count_marker_append_app] using hcount i j
          · simpa [his, hjd] using hcount i j
        · simpa [his] using hcount i j
      · intro i j hij
        simpa using hseen i j hij
  | recvApp src dst =>
      simp [clSpec, GatedAction.fires] at hfire
      rcases hfire with ⟨_, hneq, payload, rest, hhead, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · intro i j
        simp [hsent i j]
      · intro i j
        by_cases his : i = src
        · by_cases hjd : j = dst
          · simpa [updateChan, his, hjd, hhead] using hcount i j
          · simpa [updateChan, his, hjd] using hcount i j
        · simpa [updateChan, his] using hcount i j
      · intro i j hij
        simpa using hseen i j hij
  | startSnapshot p =>
      simp [clSpec, GatedAction.fires] at hfire
      rcases hfire with ⟨hrecp, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · intro src dst
        by_cases hsrc : src = p
        · subst src
          by_cases hdst : dst = p
          · simp [recordProcess, hdst]
          · have hpd : p ≠ dst := by
              intro hEq
              exact hdst hEq.symm
            have hdp : dst ≠ p := hdst
            simp [recordProcess, hpd, hdp]
        · simpa [recordProcess, hsrc] using hsent src dst
      · intro src dst
        by_cases hsrc : src = p
        · subst src
          by_cases hdst : dst = p
          · have hsentpp : s.sentMarker p p = false := sent_false_of_unrecorded_source n s hsent hrecp
            simpa [recordProcess, hdst, hsentpp] using hcount p p
          · have hseenpd : s.seenMarker p dst = false := by
              simpa using seen_false_of_unrecorded_source n s hsent hseen hrecp (src := p) (dst := dst)
            have hpd : p ≠ dst := by
              intro hEq
              exact hdst hEq.symm
            have hdp : dst ≠ p := hdst
            have hcount0 : (s.chan p dst).count Packet.marker = 0 := by
              have hsentpd : s.sentMarker p dst = false := sent_false_of_unrecorded_source n s hsent hrecp
              simpa [hsentpd, hseenpd] using hcount p dst
            have hcount1 : (s.chan p dst ++ [Packet.marker]).count Packet.marker = 1 := by
              exact count_marker_append_marker_zero (s.chan p dst) hcount0
            simpa [recordProcess, hpd, hdp, hseenpd] using hcount1
        · simpa [recordProcess, hsrc] using hcount src dst
      · intro src dst hseen'
        by_cases hsrc : src = p
        · subst src
          have hseenOld : s.seenMarker p dst = true := by
            simpa [recordProcess] using hseen'
          have hfalse : s.seenMarker p dst = false := by
            simpa using seen_false_of_unrecorded_source n s hsent hseen hrecp (src := p) (dst := dst)
          simp [hfalse] at hseenOld
        · have hseenOld : s.seenMarker src dst = true := by
            simpa [recordProcess, hsrc] using hseen'
          have hbase := hseen src dst hseenOld
          refine ⟨hbase.1, ?_, ?_⟩
          · simp [recordProcess, hsrc, hbase.2.1]
          · by_cases hdst : dst = p
            · subst hdst
              simp [recordProcess]
            · simp [recordProcess, hdst, hbase.2.2]
  | recvMarker src dst =>
      by_cases hrec : s.recorded dst
      · simp [clSpec, GatedAction.fires, hrec] at hfire
        rcases hfire with ⟨_, hneq, rest, hhead, rfl⟩
        have hcond : s.sentMarker src dst = true ∧ s.seenMarker src dst = false :=
          sent_true_seen_false_of_head_marker n s hcount hhead
        have hrest0 : rest.count Packet.marker = 0 :=
          tail_marker_count_zero_of_head_marker n s hcount hhead
        refine ⟨?_, ?_, ?_⟩
        · intro i j
          simp [hsent i j]
        · intro i j
          by_cases his : i = src
          · subst i
            by_cases hjd : j = dst
            · subst j
              simp [updateChan, hrest0, hcond]
            · simpa [updateChan, hjd] using hcount src j
          · simpa [updateChan, his] using hcount i j
        · intro i j hij
          by_cases his : i = src
          · subst i
            by_cases hjd : j = dst
            · subst j
              exact ⟨hneq, hcond.1, hrec⟩
            · have hseenOld : s.seenMarker src j = true := by
                simpa [hjd] using hij
              simpa [hjd] using hseen src j hseenOld
          · have hseenOld : s.seenMarker i j = true := by
              simpa [his] using hij
            simpa [his] using hseen i j hseenOld
      · simp [clSpec, GatedAction.fires, hrec] at hfire
        rcases hfire with ⟨_, hneq, rest, hhead, rfl⟩
        have hrecFalse : s.recorded dst = false := by
          cases hrd : s.recorded dst with
          | false => rfl
          | true => exact False.elim (hrec hrd)
        have hcond : s.sentMarker src dst = true ∧ s.seenMarker src dst = false :=
          sent_true_seen_false_of_head_marker n s hcount hhead
        have hrest0 : rest.count Packet.marker = 0 :=
          tail_marker_count_zero_of_head_marker n s hcount hhead
        refine ⟨?_, ?_, ?_⟩
        · intro i j
          by_cases hid : i = dst
          · subst i
            by_cases hjd : j = dst
            · subst j
              simp [recordProcess]
            · have hneqdj : dst ≠ j := by
                intro hEq
                exact hjd hEq.symm
              simp [recordProcess, hjd, hneqdj]
          · simpa [recordProcess, hid] using hsent i j
        · intro i j
          by_cases hid : i = dst
          · subst i
            by_cases hjd : j = dst
            · subst j
              have hsentdd : s.sentMarker dst dst = false := by
                exact sent_false_of_unrecorded_source n s hsent hrecFalse
              have hneqds : dst ≠ src := Ne.symm hneq
              simpa [updateChan, recordProcess, hneqds, hsentdd] using hcount dst dst
            · have hneqdj : dst ≠ j := by
                intro hEq
                exact hjd hEq.symm
              have hneqds : dst ≠ src := Ne.symm hneq
              have hseenFalse : s.seenMarker dst j = false := by
                simpa using seen_false_of_unrecorded_source n s hsent hseen hrecFalse (src := dst) (dst := j)
              have hsentFalse : s.sentMarker dst j = false := by
                exact sent_false_of_unrecorded_source n s hsent hrecFalse
              have hcount0 : (s.chan dst j).count Packet.marker = 0 := by
                simpa [hsentFalse, hseenFalse] using hcount dst j
              have hcount1 : (s.chan dst j ++ [Packet.marker]).count Packet.marker = 1 := by
                exact count_marker_append_marker_zero (s.chan dst j) hcount0
              simpa [hjd, updateChan, recordProcess, hneqds, hseenFalse] using hcount1
          · by_cases his : i = src
            · subst i
              by_cases hjd : j = dst
              · subst j
                simp [updateChan, recordProcess, hrest0, hcond]
              · simpa [updateChan, recordProcess, hneq, hjd] using hcount src j
            · simpa [updateChan, recordProcess, his, hid] using hcount i j
        · intro i j hij
          by_cases his : i = src
          · subst i
            by_cases hjd : j = dst
            · subst j
              refine ⟨hneq, ?_, by simp [recordProcess]⟩
              simp [recordProcess, hneq, hcond.1]
            · have hseenOld : s.seenMarker src j = true := by
                simpa [recordProcess, hjd] using hij
              have hbase := hseen src j hseenOld
              refine ⟨hbase.1, ?_, ?_⟩
              · simp [recordProcess, hneq, hbase.2.1]
              · simpa [recordProcess, hjd] using hbase.2.2
          · by_cases hid : i = dst
            · subst i
              have hfalse : s.seenMarker dst j = false := by
                simpa using seen_false_of_unrecorded_source n s hsent hseen hrecFalse (src := dst) (dst := j)
              have hseenOld : s.seenMarker dst j = true := by
                simpa [recordProcess, his, hneq] using hij
              simp [hfalse] at hseenOld
            · by_cases hjd : j = dst
              · subst j
                have hfalse : s.seenMarker i dst = false := by
                  exact seenMarker_false_of_not_recorded_dst n ⟨hsent, hcount, hseen⟩ hrecFalse
                have hseenOld : s.seenMarker i dst = true := by
                  simpa [recordProcess, his, hid, hneq] using hij
                simp [hfalse] at hseenOld
              · have hseenOld : s.seenMarker i j = true := by
                  simpa [recordProcess, his, hid, hjd] using hij
                simpa [recordProcess, his, hid, hjd] using hseen i j hseenOld

theorem markerCore_invariant :
    pred_implies (clSpec n).toSpec.safety [tlafml| □ ⌜markerCoreInv n⌝] := by
  apply init_invariant
  · exact markerCoreInv_init n
  · intro s s' hnext hinv
    exact markerCoreInv_next n s s' hnext hinv

theorem markerBookkeeping_invariant :
    pred_implies (clSpec n).toSpec.safety [tlafml| □ ⌜invMarkerBookkeeping n⌝] := by
  apply pred_implies_trans (q := [tlafml| □ ⌜markerCoreInv n⌝])
  · exact markerCore_invariant n
  · apply always_monotone
    intro e h
    constructor
    · intro src dst hsent'
      exact (h.1 src dst).1 hsent'
    · intro src dst hseen'
      exact h.2.2 src dst hseen'

theorem atMostOneMarker_invariant :
    pred_implies (clSpec n).toSpec.safety [tlafml| □ ⌜invAtMostOneMarker n⌝] := by
  apply pred_implies_trans (q := [tlafml| □ ⌜markerCoreInv n⌝])
  · exact markerCore_invariant n
  · apply always_monotone
    intro e h src dst
    have hcount' := h.2.1 src dst
    by_cases hcond : (e 0).sentMarker src dst = true ∧ (e 0).seenMarker src dst = false
    · have hone : ((e 0).chan src dst).count Packet.marker = 1 := by
        simpa [markerCount_exact, hcond] using hcount'
      omega
    · have hzero : ((e 0).chan src dst).count Packet.marker = 0 := by
        simpa [markerCount_exact, hcond] using hcount'
      omega

theorem pendingMarker_invariant :
    pred_implies (clSpec n).toSpec.safety [tlafml| □ ⌜invPendingMarker n⌝] := by
  apply pred_implies_trans (q := [tlafml| □ ⌜markerCoreInv n⌝])
  · exact markerCore_invariant n
  · apply always_monotone
    intro e h src dst hsent' hseen'
    have hone : ((e 0).chan src dst).count Packet.marker = 1 := by
      simpa [markerCount_exact, hsent', hseen'] using h.2.1 src dst
    exact marker_mem_of_count_pos (((e 0).chan src dst)) (by omega)

theorem windowCoreInv_init :
    ∀ s, (clSpec n).init s → windowCoreInv n s := by
  intro s hinit
  rcases hinit with ⟨_, _, hrecorded, _, _, hseen, hchanSnap, hrecvLog, hrecordCut, hcloseCut⟩
  constructor
  · constructor
    · intro src dst hrec
      have hfalse : False := by
        simp [hrecorded dst] at hrec
      exact False.elim hfalse
    · intro src dst hseen'
      simp [hseen src dst] at hseen'
  · intro src dst
    simp [hrecorded dst, hchanSnap src dst]

theorem windowCoreInv_next :
    ∀ s s', (∃ a, ((clSpec n).actions a).fires s s') →
      markerCoreInv n s → windowCoreInv n s → windowCoreInv n s' := by
  intro s s' ⟨a, hfire⟩ hcore hwin
  rcases hcore with ⟨hsent, hcount, hseen⟩
  rcases hwin with ⟨hcuts, hchanExact⟩
  rcases hcuts with ⟨hcutRec, hcutSeen⟩
  cases a with
  | localStep p =>
      simp [clSpec, GatedAction.fires] at hfire
      rcases hfire with rfl
      exact ⟨⟨hcutRec, hcutSeen⟩, hchanExact⟩
  | sendApp src dst payload =>
      simp [clSpec, GatedAction.fires] at hfire
      rcases hfire with ⟨_, rfl⟩
      exact ⟨⟨hcutRec, hcutSeen⟩, hchanExact⟩
  | recvApp src dst =>
      simp [clSpec, GatedAction.fires] at hfire
      rcases hfire with ⟨_, hneq, payload, rest, hhead, rfl⟩
      constructor
      · constructor
        · intro i j hrec
          by_cases his : i = src
          · subst i
            by_cases hjd : j = dst
            · subst j
              have hbase := hcutRec src dst hrec
              have hstep : s.recordCut src dst ≤ (s.recvLog src dst).length + 1 := by omega
              simpa [hhead] using hstep
            · simpa [hhead, hjd] using hcutRec src j hrec
          · simpa [hhead, his] using hcutRec i j hrec
        · intro i j hseen'
          by_cases his : i = src
          · subst i
            by_cases hjd : j = dst
            · subst j
              have hbase := hcutSeen src dst hseen'
              simp
              omega
            · simpa [hhead, hjd] using hcutSeen src j hseen'
          · simpa [hhead, his] using hcutSeen i j hseen'
      · intro i j
        by_cases his : i = src
        · subst i
          by_cases hjd : j = dst
          · subst j
            by_cases hrec : s.recorded dst = true
            · by_cases hseen' : s.seenMarker src dst = true
              · have hgoal :
                    (if s.recorded dst ∧ s.seenMarker src dst = false
                      then s.chanSnap src dst ++ [payload] else s.chanSnap src dst) =
                    (if s.recorded dst then
                        channelWindow (s.recvLog src dst ++ [payload]) (s.recordCut src dst)
                          (if s.seenMarker src dst then s.closeCut src dst else (s.recvLog src dst ++ [payload]).length)
                      else []) := by
                    calc
                      (if s.recorded dst ∧ s.seenMarker src dst = false
                        then s.chanSnap src dst ++ [payload] else s.chanSnap src dst)
                          = s.chanSnap src dst := by simp [hrec, hseen']
                      _ = channelWindow (s.recvLog src dst) (s.recordCut src dst) (s.closeCut src dst) := by
                        simpa [channelSnap_exact, hrec, hseen'] using hchanExact src dst
                      _ = channelWindow (s.recvLog src dst ++ [payload]) (s.recordCut src dst) (s.closeCut src dst) := by
                        symm
                        exact channelWindow_append_irrel (s.recvLog src dst) payload
                          (s.recordCut src dst) (s.closeCut src dst)
                          (hcutSeen src dst hseen').1 (hcutSeen src dst hseen').2
                      _ = (if s.recorded dst then
                            channelWindow (s.recvLog src dst ++ [payload]) (s.recordCut src dst)
                              (if s.seenMarker src dst then s.closeCut src dst else (s.recvLog src dst ++ [payload]).length)
                          else []) := by
                        simp [hrec, hseen']
                simpa [hhead] using hgoal
              · have hbound := hcutRec src dst hrec
                have hnewbound : s.recordCut src dst ≤ (s.recvLog src dst ++ [payload]).length := by
                  simp
                  omega
                have hgoal :
                    (if s.recorded dst ∧ s.seenMarker src dst = false
                      then s.chanSnap src dst ++ [payload] else s.chanSnap src dst) =
                    (if s.recorded dst then
                        channelWindow (s.recvLog src dst ++ [payload]) (s.recordCut src dst)
                          (if s.seenMarker src dst then s.closeCut src dst else (s.recvLog src dst ++ [payload]).length)
                      else []) := by
                    calc
                      (if s.recorded dst ∧ s.seenMarker src dst = false
                        then s.chanSnap src dst ++ [payload] else s.chanSnap src dst)
                          = s.chanSnap src dst ++ [payload] := by simp [hrec, hseen']
                      _ = (s.recvLog src dst).drop (s.recordCut src dst) ++ [payload] := by
                        rw [show s.chanSnap src dst =
                          channelWindow (s.recvLog src dst) (s.recordCut src dst) (s.recvLog src dst).length by
                            simpa [channelSnap_exact, hrec, hseen'] using hchanExact src dst]
                        rw [channelWindow_at_end (s.recvLog src dst) (s.recordCut src dst)]
                      _ = (s.recvLog src dst ++ [payload]).drop (s.recordCut src dst) := by
                        symm
                        exact drop_append_singleton_of_le (s.recvLog src dst) payload (s.recordCut src dst) hbound
                      _ = channelWindow (s.recvLog src dst ++ [payload]) (s.recordCut src dst)
                            (s.recvLog src dst ++ [payload]).length := by
                        symm
                        exact channelWindow_at_end (s.recvLog src dst ++ [payload]) (s.recordCut src dst)
                      _ = (if s.recorded dst then
                            channelWindow (s.recvLog src dst ++ [payload]) (s.recordCut src dst)
                              (if s.seenMarker src dst then s.closeCut src dst else (s.recvLog src dst ++ [payload]).length)
                          else []) := by
                        simp [hrec, hseen']
                simpa [hhead] using hgoal
            · have hsnap : s.chanSnap src dst = [] := by
                simpa [channelSnap_exact, hrec] using hchanExact src dst
              simp [hrec, hsnap]
          · simpa [hhead, hjd] using hchanExact src j
        · simpa [hhead, his] using hchanExact i j
  | startSnapshot p =>
      simp [clSpec, GatedAction.fires] at hfire
      rcases hfire with ⟨hrecp, rfl⟩
      constructor
      · constructor
        · intro src dst hrec
          by_cases hdp : dst = p
          · subst dst
            simp [recordProcess]
          · have hrecOld : s.recorded dst = true := by
              simpa [recordProcess, hdp] using hrec
            simpa [recordProcess, hdp] using hcutRec src dst hrecOld
        · intro src dst hseen'
          by_cases hdp : dst = p
          · subst dst
            have hfalse : s.seenMarker src p = false := by
              exact seenMarker_false_of_not_recorded_dst n ⟨hsent, hcount, hseen⟩ hrecp
            simp [recordProcess, hfalse] at hseen'
          · have hseenOld : s.seenMarker src dst = true := by
              simpa [recordProcess, hdp] using hseen'
            simpa [recordProcess, hdp] using hcutSeen src dst hseenOld
      · intro src dst
        by_cases hdp : dst = p
        · subst dst
          have hfalse : s.seenMarker src p = false := by
            exact seenMarker_false_of_not_recorded_dst n ⟨hsent, hcount, hseen⟩ hrecp
          have hsnap : s.chanSnap src p = [] := by
            simpa [channelSnap_exact, hrecp] using hchanExact src p
          simp [recordProcess, hfalse, hsnap, channelWindow]
        · simpa [recordProcess, hdp] using hchanExact src dst
  | recvMarker src dst =>
      by_cases hrec : s.recorded dst = true
      · simp [clSpec, GatedAction.fires, hrec] at hfire
        rcases hfire with ⟨_, hneq, rest, hhead, rfl⟩
        have hcond : s.sentMarker src dst = true ∧ s.seenMarker src dst = false :=
          sent_true_seen_false_of_head_marker n s hcount hhead
        constructor
        · constructor
          · intro i j hrec'
            simpa [updateChan, hhead] using hcutRec i j hrec'
          · intro i j hseen'
            by_cases his : i = src
            · subst i
              by_cases hjd : j = dst
              · subst j
                have hbound := hcutRec src dst hrec
                simp [hbound]
              · have hseenOld : s.seenMarker src j = true := by
                  simpa [updateChan, hjd] using hseen'
                simpa [updateChan, hjd] using hcutSeen src j hseenOld
            · have hseenOld : s.seenMarker i j = true := by
                simpa [updateChan, his] using hseen'
              simpa [updateChan, his] using hcutSeen i j hseenOld
        · intro i j
          by_cases his : i = src
          · subst i
            by_cases hjd : j = dst
            · subst j
              simpa [updateChan, hhead, hrec, hcond.2] using hchanExact src dst
            · simpa [updateChan, hjd] using hchanExact src j
          · simpa [updateChan, his] using hchanExact i j
      · simp [clSpec, GatedAction.fires, hrec] at hfire
        rcases hfire with ⟨_, hneq, rest, hhead, rfl⟩
        have hrecFalse : s.recorded dst = false := by
          cases hrd : s.recorded dst with
          | false => rfl
          | true => exact False.elim (hrec hrd)
        constructor
        · constructor
          · intro i j hrec'
            by_cases hjd : j = dst
            · subst j
              simp [recordProcess]
            · have hrecOld : s.recorded j = true := by
                simpa [recordProcess, hjd] using hrec'
              simpa [recordProcess, hjd] using hcutRec i j hrecOld
          · intro i j hseen'
            by_cases hjd : j = dst
            · subst j
              by_cases his : i = src
              · subst i
                simp [recordProcess]
              · have hfalse : s.seenMarker i dst = false := by
                  exact seenMarker_false_of_not_recorded_dst n ⟨hsent, hcount, hseen⟩ hrecFalse
                simp [recordProcess, his, hfalse] at hseen'
            · have hseenOld : s.seenMarker i j = true := by
                simpa [recordProcess, hjd] using hseen'
              simpa [recordProcess, hjd] using hcutSeen i j hseenOld
        · intro i j
          by_cases hjd : j = dst
          · subst j
            by_cases his : i = src
            · subst i
              have hsnap : s.chanSnap src dst = [] := by
                simpa [channelSnap_exact, hrecFalse] using hchanExact src dst
              simp [recordProcess, hsnap, channelWindow]
            · have hsnap : s.chanSnap i dst = [] := by
                simpa [channelSnap_exact, hrecFalse] using hchanExact i dst
              have hseenFalse : s.seenMarker i dst = false := by
                exact seenMarker_false_of_not_recorded_dst n ⟨hsent, hcount, hseen⟩ hrecFalse
              simp [recordProcess, his, hseenFalse, hsnap, channelWindow]
          · simpa [recordProcess, hjd] using hchanExact i j

theorem snapshotCoreInv_init :
    ∀ s, (clSpec n).init s → snapshotCoreInv n s := by
  intro s hinit
  exact ⟨invNoSelfTraffic_init n s hinit, markerCoreInv_init n s hinit, windowCoreInv_init n s hinit⟩

theorem snapshotCoreInv_next :
    ∀ s s', (∃ a, ((clSpec n).actions a).fires s s') →
      snapshotCoreInv n s → snapshotCoreInv n s' := by
  intro s s' hnext hcore
  rcases hcore with ⟨hself, hmark, hwin⟩
  exact ⟨invNoSelfTraffic_next n s s' hnext hself,
    markerCoreInv_next n s s' hnext hmark,
    windowCoreInv_next n s s' hnext hmark hwin⟩

theorem snapshotCoreInv_invariant :
    pred_implies (clSpec n).toSpec.safety [tlafml| □ ⌜snapshotCoreInv n⌝] := by
  apply init_invariant
  · exact snapshotCoreInv_init n
  · intro s s' hnext hinv
    exact snapshotCoreInv_next n s s' hnext hinv

theorem snapshotCoreInv_implies_unrecorded {s : CLState n}
    (h : snapshotCoreInv n s) :
    invUnrecordedChannelsEmpty n s := by
  rcases h with ⟨_, _, ⟨_, hchan⟩⟩
  intro src dst hrec
  simpa [channelSnap_exact, hrec] using hchan src dst

theorem snapshotCoreInv_implies_cuts {s : CLState n}
    (h : snapshotCoreInv n s) :
    invCutsWellFormed n s := h.2.2.1

theorem snapshotCoreInv_implies_open {s : CLState n}
    (h : snapshotCoreInv n s) :
    invOpenChannelWindow n s := by
  rcases h with ⟨_, _, ⟨hcuts, hchan⟩⟩
  rcases hcuts with ⟨hcutRec, _⟩
  intro src dst hrec hseen
  have hshape := hchan src dst
  have hbound := hcutRec src dst hrec
  simpa [channelSnap_exact, hrec, hseen, channelWindow_at_end (s.recvLog src dst) (s.recordCut src dst)] using hshape

theorem snapshotCoreInv_implies_closed {s : CLState n}
    (h : snapshotCoreInv n s) :
    invClosedChannelWindow n s := by
  rcases h with ⟨_, hcore, ⟨_, hchan⟩⟩
  intro src dst hseen'
  have hrec : s.recorded dst = true := (hcore.2.2 src dst hseen').2.2
  simpa [channelSnap_exact, hrec, hseen'] using hchan src dst

theorem snapshotCoreInv_implies_snapshotInv {s : CLState n}
    (h : snapshotCoreInv n s) :
    snapshotInv n s := by
  rcases h with ⟨hself, hcore, hwin⟩
  exact ⟨hself,
    markerCoreInv_implies_markerBookkeeping n hcore,
    markerCoreInv_implies_atMostOneMarker n hcore,
    markerCoreInv_implies_pendingMarker n hcore,
    snapshotCoreInv_implies_unrecorded n ⟨hself, hcore, hwin⟩,
    snapshotCoreInv_implies_cuts n ⟨hself, hcore, hwin⟩,
    snapshotCoreInv_implies_open n ⟨hself, hcore, hwin⟩,
    snapshotCoreInv_implies_closed n ⟨hself, hcore, hwin⟩⟩

theorem unrecordedChannelsEmpty_invariant :
    pred_implies (clSpec n).toSpec.safety [tlafml| □ ⌜invUnrecordedChannelsEmpty n⌝] := by
  apply pred_implies_trans (q := [tlafml| □ ⌜snapshotCoreInv n⌝])
  · exact snapshotCoreInv_invariant n
  · apply always_monotone
    intro e h
    exact snapshotCoreInv_implies_unrecorded n h

theorem cutsWellFormed_invariant :
    pred_implies (clSpec n).toSpec.safety [tlafml| □ ⌜invCutsWellFormed n⌝] := by
  apply pred_implies_trans (q := [tlafml| □ ⌜snapshotCoreInv n⌝])
  · exact snapshotCoreInv_invariant n
  · apply always_monotone
    intro e h
    exact snapshotCoreInv_implies_cuts n h

theorem openChannelWindow_invariant :
    pred_implies (clSpec n).toSpec.safety [tlafml| □ ⌜invOpenChannelWindow n⌝] := by
  apply pred_implies_trans (q := [tlafml| □ ⌜snapshotCoreInv n⌝])
  · exact snapshotCoreInv_invariant n
  · apply always_monotone
    intro e h
    exact snapshotCoreInv_implies_open n h

theorem closedChannelWindow_invariant :
    pred_implies (clSpec n).toSpec.safety [tlafml| □ ⌜invClosedChannelWindow n⌝] := by
  apply pred_implies_trans (q := [tlafml| □ ⌜snapshotCoreInv n⌝])
  · exact snapshotCoreInv_invariant n
  · apply always_monotone
    intro e h
    exact snapshotCoreInv_implies_closed n h

theorem snapshotInv_invariant :
    pred_implies (clSpec n).toSpec.safety [tlafml| □ ⌜snapshotInv n⌝] := by
  apply pred_implies_trans (q := [tlafml| □ ⌜snapshotCoreInv n⌝])
  · exact snapshotCoreInv_invariant n
  · apply always_monotone
    intro e h
    exact snapshotCoreInv_implies_snapshotInv n h

end ChandyLamport
