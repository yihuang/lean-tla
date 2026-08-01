import Leslie.Examples.LeaseLock

/-! ## Message-Passing Lease Lock with Forward Simulation

    A message-passing variant of the `LeaseLock` model and a forward
    simulation proof that it refines the atomic `LeaseLock` model.

    Each atomic action (acquire/writeOk/release) is decomposed into
    send → process → receive. The forward simulation fires the atomic
    action at the server **processing** step. Client receive steps are
    stuttering steps where the concrete client catches up to the abstract.

    ### Heartbeat extension (Track B of `ddb-lock-rs` plan)

    Extended with `sendHeartbeatReq` / `processHeartbeat` / `recvHeartbeatResp`
    so the model covers lease refresh. Heartbeats are **stuttering** w.r.t. the
    atomic `LeaseLock` — they refresh the lease without rotating the fencing
    token or changing holder / leaseActive / journal. Motivation: bridge-prep
    for the Rust `ddb-lock-rs` client (sibling repo at
    `/Users/rupak/Code/tla/ddb-lock-rs/`), whose `protocol::heartbeat` function
    needs a Leslie-side counterpart for the Verus→Lean bridge.

    ### Modeling caveat: three non-local gates

    Three action gates in this model reference **global absence** of specific
    message variants in `s.network`:

    1. `processHeartbeat p token`: `(∀ t, Msg.acquireResp p t ∉ s.network) ∧
       Msg.heartbeatResp p token ∉ s.network`
    2. `recvReleaseResp p token`: `∀ t, Msg.heartbeatResp p t ∉ s.network`

    These are **not node-local** — neither the server (for processHeartbeat)
    nor the client (for recvReleaseResp) can observe, in a distributed system,
    that no such message exists anywhere in the network. They can only inspect
    their own inbox.

    #### Why these gates are acceptable for synchronous-RPC implementations

    The canonical implementation target is `ddb-lock-rs`, which uses
    **synchronous RPC** with DynamoDB as a shared-state backend:

    - Heartbeat is a single `storage.update_if(expect_rvn, owner, new_lock)`
      call that returns `Ok` or `ConditionalCheckFailed` synchronously.
    - There is no `heartbeatResp` message that lingers in any queue; the
      response is the return value of the call.
    - There is no `acquireResp` either — `protocol::acquire` returns a
      `LockItem` directly to the caller.
    - There is no client-side `believesLeader` flag that can go stale while
      an "in flight" response sits around.

    Under this synchronous-RPC specialization, every `send*Req → process* →
    recv*Resp` triple collapses to an atomic RPC with no intermediate network
    state. The three non-local gates above are therefore **vacuously true**:
    by the time any subsequent action fires, the previous heartbeat or
    acquire's `response in flight` doesn't exist (it was consumed
    synchronously on return). Every `ddb-lock-rs` execution trace corresponds
    to an interleaving of this model where these gates trivially hold.

    So for the Rust implementation specifically, the non-local gates describe
    a sound specialization — the proof here is stronger than Rust strictly
    needs, but not wrong.

    #### Plan for a realistic async model (future work)

    For a fully asynchronous LeaseLock — where heartbeats can race, stale
    responses linger, the network reorders, and implementations might be
    built on unreliable pub/sub rather than DynamoDB — the three non-local
    gates must be eliminated. Planned strategy:

    - **B (transition-level filter)** for `recvReleaseResp`. Instead of
      gating on "no heartbeatResp p in network", make the transition
      additionally erase any pending `heartbeatResp p _` from the client's
      own inbox as part of the recv step. Client filtering its own inbox
      is node-local. Cost: ~10–15 proof updates in the `recvReleaseResp`
      case of `msgNetInv_step` and in the corresponding `sim_step` case.

    - **C (invariant derivation)** for the two `processHeartbeat` gates.
      Add invariant clauses:

          heartbeatReq_excl_acq  : heartbeatReq p t ∈ network →
                                   ∀ t', acquireResp p t' ∉ network
          heartbeatReq_excl_hbresp : heartbeatReq p t ∈ network →
                                     ∀ t', heartbeatResp p t' ∉ network

      These are preserved by all send/recv actions (they're monotone) and
      by `processAcquire` (filters foreign `acqResp`) and `processHeartbeat`
      (replaces exactly one `heartbeatReq` with one `heartbeatResp`).
      Once these invariants hold, `processHeartbeat`'s gate can simply
      consume the `heartbeatReq p token ∈ network` clause and use the
      invariants to conclude no stale `acquireResp` or `heartbeatResp` is
      around — dropping both non-local gate clauses.

    **Reminder:** revisit this after the Verus→Lean bridge work for
    `ddb-lock-rs` is complete. At that point, if we want to cover a second
    (async) implementation — e.g., etcd- or Redis-backed — we need the
    realistic model. See memory entry `async_leaselock_todo.md` in the
    user's project memory.
-/

open TLA

namespace MsgLeaseLock

/-! ### Messages -/

inductive Msg (n : Nat) where
  | acquireReq    (p : Fin n)
  | acquireResp   (p : Fin n) (token : Nat)
  | writeReq      (p : Fin n) (v : Nat) (token : Nat) (seq : Nat)
  | writeResp     (p : Fin n) (token : Nat) (seq : Nat)
  | releaseReq    (p : Fin n) (token : Nat)
  | releaseResp   (p : Fin n) (token : Nat)
  | heartbeatReq  (p : Fin n) (token : Nat)
  | heartbeatResp (p : Fin n) (token : Nat)
  deriving DecidableEq

def Msg.isRequest : Msg n → Bool
  | .acquireReq _       => true
  | .writeReq _ _ _ _   => true
  | .releaseReq _ _     => true
  | .heartbeatReq _ _   => true
  | _                   => false

/-! ### State -/

structure MsgLeaseState (n : Nat) where
  nextToken : Nat
  lockHolder : Option (Fin n)
  leaseActive : Bool
  myToken : Fin n → Nat
  writeSeq : Fin n → Nat
  believesLeader : Fin n → Bool
  highToken : Nat
  highSeq : Nat
  journal : List LeaseLock.WriteEntry
  network : List (Msg n)

def initialMsgLease (n : Nat) : MsgLeaseState n where
  nextToken := 1
  lockHolder := none
  leaseActive := false
  myToken := fun _ => 0
  writeSeq := fun _ => 0
  believesLeader := fun _ => false
  highToken := 0
  highSeq := 0
  journal := []
  network := []

/-! ### Actions -/

inductive MsgLeaseAction (n : Nat) where
  | sendAcquireReq    (p : Fin n)
  | processAcquire    (p : Fin n)
  | recvAcquireResp   (p : Fin n) (token : Nat)
  | sendWriteReq      (p : Fin n) (v : Nat)
  | processWrite      (p : Fin n) (v : Nat) (token : Nat) (seq : Nat)
  | recvWriteResp     (p : Fin n) (token : Nat) (seq : Nat)
  | sendReleaseReq    (p : Fin n)
  | processRelease    (p : Fin n) (token : Nat)
  | recvReleaseResp   (p : Fin n) (token : Nat)
  | sendHeartbeatReq  (p : Fin n)
  | processHeartbeat  (p : Fin n) (token : Nat)
  | recvHeartbeatResp (p : Fin n) (token : Nat)
  | expireLease
  | dropMsg           (msg : Msg n)

def msgLeaseSpec (n : Nat) : ActionSpec (MsgLeaseState n) (MsgLeaseAction n) where
  init := fun s => s = initialMsgLease n
  actions := fun
    | .sendAcquireReq p => {
        gate := fun _ => True
        transition := fun s s' =>
          s' = { s with network := s.network ++ [Msg.acquireReq p] } }
    | .processAcquire p => {
        gate := fun s =>
          Msg.acquireReq p ∈ s.network ∧
          (s.lockHolder = none ∨ s.leaseActive = false)
        transition := fun s s' =>
          s' = { s with
            lockHolder := some p
            leaseActive := true
            nextToken := s.nextToken + 1
            -- Erase acquireReq, invalidate old acquireResp for p, drop stale heartbeatResps for p,
            -- issue new acquireResp.
            network := (s.network.erase (Msg.acquireReq p)).filter
              (fun m => match m with
                | .acquireResp q _ => decide (q ≠ p)
                | .heartbeatResp q _ => decide (q ≠ p)
                | _ => true) ++
              [Msg.acquireResp p s.nextToken] } }
    | .recvAcquireResp p token => {
        gate := fun s => Msg.acquireResp p token ∈ s.network
        transition := fun s s' =>
          s' = { s with
            myToken := fun q => if q = p then token else s.myToken q
            writeSeq := fun q => if q = p then 0 else s.writeSeq q
            believesLeader := fun q =>
              if q = p then true else s.believesLeader q
            -- New generation: erase acquireResp and filter stale responses for p
            network := (s.network.erase (Msg.acquireResp p token)).filter
              (fun m => match m with
                | .writeResp q _ _ => decide (q ≠ p)
                | .releaseResp q _ => decide (q ≠ p)
                | _ => true) } }
    | .sendWriteReq p v => {
        gate := fun s => s.believesLeader p = true
        transition := fun s s' =>
          s' = { s with
            network := s.network ++
              [Msg.writeReq p v (s.myToken p) (s.writeSeq p + 1)] } }
    | .processWrite p v token seq => {
        gate := fun s =>
          Msg.writeReq p v token seq ∈ s.network ∧
          (token > s.highToken ∨ (token = s.highToken ∧ seq > s.highSeq)) ∧
          token + 1 = s.nextToken
        transition := fun s s' =>
          s' = { s with
            highToken := token
            highSeq := seq
            journal := s.journal ++ [⟨v, token, seq⟩]
            network := s.network.erase (Msg.writeReq p v token seq) ++
              [Msg.writeResp p token seq] } }
    | .recvWriteResp p token seq => {
        -- Client only processes write responses from its current generation.
        -- Also discards stale writeReqs for (p, token) — they can never be
        -- processed (server high-water mark blocks them) and would violate
        -- the writeReq_seq invariant after writeSeq updates.
        gate := fun s => Msg.writeResp p token seq ∈ s.network ∧ s.myToken p = token
        transition := fun s s' =>
          s' = { s with
            writeSeq := fun q => if q = p then seq else s.writeSeq q
            network := (s.network.erase (Msg.writeResp p token seq)).filter
              (fun m => match m with
                | .writeReq q _ t _ => decide (q ≠ p ∨ t ≠ token)
                | _ => true) } }
    | .sendReleaseReq p => {
        gate := fun _ => True
        transition := fun s s' =>
          s' = { s with network := s.network ++ [Msg.releaseReq p (s.myToken p)] } }
    | .processRelease p token => {
        gate := fun s =>
          Msg.releaseReq p token ∈ s.network ∧
          s.lockHolder = some p ∧ s.leaseActive = true ∧
          token + 1 = s.nextToken
        transition := fun s s' =>
          s' = { s with
            lockHolder := none
            leaseActive := false
            network := s.network.erase (Msg.releaseReq p token) ++
              [Msg.releaseResp p token] } }
    | .recvReleaseResp p token => {
        -- Client only processes release responses from its current generation.
        -- Additional gate: no pending heartbeatResp for p. Otherwise this
        -- action would flip believesLeader p to false while stale
        -- heartbeatResp p _ lingered, violating heartbeatResp_bl.
        -- (Liveness requirement: client must drain pending heartbeats before
        -- accepting a release response.)
        gate := fun s =>
          Msg.releaseResp p token ∈ s.network ∧
          s.myToken p = token ∧
          (∀ t, Msg.heartbeatResp p t ∉ s.network)
        transition := fun s s' =>
          s' = { s with
            believesLeader := fun q =>
              if q = p then false else s.believesLeader q
            network := s.network.erase (Msg.releaseResp p token) } }
    | .sendHeartbeatReq p => {
        -- A client that believes it's leader wants to refresh its lease.
        gate := fun s => s.believesLeader p = true
        transition := fun s s' =>
          s' = { s with
            network := s.network ++ [Msg.heartbeatReq p (s.myToken p)] } }
    | .processHeartbeat p token => {
        -- Server accepts heartbeat iff the client is current holder with latest
        -- token AND lease is still active. Does NOT rotate the token or change
        -- highToken/highSeq/journal — heartbeat refreshes the LEASE, not the
        -- fencing generation.
        gate := fun s =>
          Msg.heartbeatReq p token ∈ s.network ∧
          s.lockHolder = some p ∧
          s.leaseActive = true ∧
          token + 1 = s.nextToken ∧
          (∀ t, Msg.acquireResp p t ∉ s.network) ∧
          Msg.heartbeatResp p token ∉ s.network
        transition := fun s s' =>
          s' = { s with
            network := s.network.erase (Msg.heartbeatReq p token) ++
              [Msg.heartbeatResp p token] } }
    | .recvHeartbeatResp p token => {
        gate := fun s =>
          Msg.heartbeatResp p token ∈ s.network ∧ s.myToken p = token
        transition := fun s s' =>
          s' = { s with
            network := s.network.erase (Msg.heartbeatResp p token) } }
    | .expireLease => {
        gate := fun s => s.leaseActive = true
        transition := fun s s' => s' = { s with leaseActive := false } }
    | .dropMsg msg => {
        gate := fun s => msg ∈ s.network ∧ msg.isRequest = true
        transition := fun s s' =>
          s' = { s with network := s.network.erase msg } }

/-! ### Network invariant

    Token freshness, generation coherence, and high-water-mark bounds.
    Maintained by all transitions; used in the forward simulation proof. -/

structure MsgNetInv {n : Nat} (ms : MsgLeaseState n) : Prop where
  myToken_lt      : ∀ p, ms.myToken p < ms.nextToken
  acqResp_lt      : ∀ p t, Msg.acquireResp p t ∈ ms.network → t < ms.nextToken
  acqResp_gt      : ∀ p t, Msg.acquireResp p t ∈ ms.network → ms.myToken p < t
  writeReq_tok    : ∀ p v t s, Msg.writeReq p v t s ∈ ms.network → t ≤ ms.myToken p
  releaseReq_tok  : ∀ p t, Msg.releaseReq p t ∈ ms.network → t ≤ ms.myToken p
  writeResp_eq    : ∀ p t s, Msg.writeResp p t s ∈ ms.network → t = ms.myToken p
  releaseResp_eq  : ∀ p t, Msg.releaseResp p t ∈ ms.network → t = ms.myToken p
  acqResp_excl_wr : ∀ p t, Msg.acquireResp p t ∈ ms.network →
                    ∀ seq, Msg.writeResp p t seq ∉ ms.network
  acqResp_excl_rel: ∀ p t, Msg.acquireResp p t ∈ ms.network →
                    Msg.releaseResp p t ∉ ms.network
  writeReq_seq    : ∀ p v s, Msg.writeReq p v (ms.myToken p) s ∈ ms.network →
                    s = ms.writeSeq p + 1
  writeResp_seq   : ∀ p s, Msg.writeResp p (ms.myToken p) s ∈ ms.network →
                    s = ms.writeSeq p + 1
  writeResp_hw    : ∀ p t s, Msg.writeResp p t s ∈ ms.network →
                    ms.highToken > t ∨ (ms.highToken = t ∧ ms.highSeq ≥ s)
  releaseResp_bl  : ∀ p t, Msg.releaseResp p t ∈ ms.network →
                    ms.believesLeader p = true
  acqResp_unique  : ∀ p t₁ t₂, Msg.acquireResp p t₁ ∈ ms.network →
                    Msg.acquireResp p t₂ ∈ ms.network → t₁ = t₂
  acqResp_count   : ∀ p t, ms.network.count (Msg.acquireResp p t) ≤ 1
  holder_believes : ∀ p, ms.lockHolder = some p →
                    ms.believesLeader p = true ∨ (∃ t, Msg.acquireResp p t ∈ ms.network)
  holder_rel_acq  : ∀ p t, ms.lockHolder = some p → Msg.releaseResp p t ∈ ms.network →
                    ∃ t', Msg.acquireResp p t' ∈ ms.network
  releaseResp_count : ∀ p t, ms.network.count (Msg.releaseResp p t) ≤ 1
  writeResp_count : ∀ p t s, ms.network.count (Msg.writeResp p t s) ≤ 1
  heartbeatReq_tok   : ∀ p t, Msg.heartbeatReq p t ∈ ms.network → t ≤ ms.myToken p
  heartbeatResp_eq   : ∀ p t, Msg.heartbeatResp p t ∈ ms.network → t = ms.myToken p
  heartbeatResp_bl   : ∀ p t, Msg.heartbeatResp p t ∈ ms.network →
                       ms.believesLeader p = true
  heartbeatResp_count: ∀ p t, ms.network.count (Msg.heartbeatResp p t) ≤ 1
  acqResp_excl_hb    : ∀ p t, Msg.acquireResp p t ∈ ms.network →
                       ∀ tok, Msg.heartbeatResp p tok ∉ ms.network

private theorem count_filter_le {n : Nat} (a : Msg n) (l : List (Msg n)) (f : Msg n → Bool) :
    List.count a (List.filter f l) ≤ List.count a l := by
  induction l with
  | nil => simp
  | cons b t ih =>
    simp only [List.filter, List.count_cons]
    by_cases hf : f b <;> simp [hf, List.count_cons] <;> omega

private theorem count_filter_false_msg {n : Nat} (a : Msg n) (l : List (Msg n))
    (f : Msg n → Bool) (hf : f a = false) :
    List.count a (List.filter f l) = 0 := by
  rw [List.count_eq_zero]; intro hm
  exact absurd ((List.mem_filter.mp hm).2) (by rw [hf]; decide)

/-! ### Forward Simulation

    Simulation relation: server/storage state matches exactly. Client
    state in the abstract model may be "ahead" when responses are in flight.
    When a response for client p is in the network, the abstract client
    state reflects the committed operation. When no response is pending,
    abstract client state matches concrete. -/

structure SimRel {n : Nat} (ms : MsgLeaseState n) (a : LeaseLock.LeaseState n) : Prop where
  nextToken_eq    : a.nextToken = ms.nextToken
  lockHolder_eq   : a.lockHolder = ms.lockHolder
  leaseActive_eq  : a.leaseActive = ms.leaseActive
  highToken_eq    : a.highToken = ms.highToken
  highSeq_eq      : a.highSeq = ms.highSeq
  journal_eq      : a.journal = ms.journal
  -- Pending-response invariants (abstract is ahead)
  acq_resp_token  : ∀ p token, Msg.acquireResp p token ∈ ms.network →
                    a.myToken p = token ∧ a.writeSeq p = 0 ∧ a.believesLeader p = true
  write_resp_seq  : ∀ p tok seq, Msg.writeResp p tok seq ∈ ms.network →
                    (∀ t, Msg.acquireResp p t ∉ ms.network) →
                    ms.myToken p = tok →
                    a.writeSeq p = seq
  rel_resp_leader : ∀ p tok, Msg.releaseResp p tok ∈ ms.network →
                    (∀ t, Msg.acquireResp p t ∉ ms.network) →
                    ms.myToken p = tok →
                    a.believesLeader p = false
  -- No-response invariants (abstract matches concrete)
  myToken_match   : ∀ p, (∀ t, Msg.acquireResp p t ∉ ms.network) →
                    a.myToken p = ms.myToken p
  writeSeq_match  : ∀ p, (∀ t, Msg.acquireResp p t ∉ ms.network) →
                    (∀ tok s, Msg.writeResp p tok s ∉ ms.network) →
                    a.writeSeq p = ms.writeSeq p
  believes_match  : ∀ p, (∀ t, Msg.acquireResp p t ∉ ms.network) →
                    (∀ tok, Msg.releaseResp p tok ∉ ms.network) →
                    a.believesLeader p = ms.believesLeader p

section Simulation
variable {n : Nat}

theorem sim_init :
    ∀ s, (msgLeaseSpec n).init s →
    ∃ a, (LeaseLock.leaseSpec n).init a ∧ @SimRel n s a := by
  intro s hs; subst hs
  refine ⟨{ nextToken := 1, lockHolder := none, leaseActive := false,
            myToken := fun _ => 0, writeSeq := fun _ => 0,
            believesLeader := fun _ => false,
            highToken := 0, highSeq := 0, journal := [] },
    ⟨rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl, rfl, rfl⟩, ?_⟩
  constructor <;> simp [initialMsgLease]

theorem sim_step :
    ∀ (ms ms' : MsgLeaseState n) (a : LeaseLock.LeaseState n),
    @MsgNetInv n ms →
    @SimRel n ms a →
    ((msgLeaseSpec n).toSpec).next ms ms' →
    ∃ a', Star ((LeaseLock.leaseSpec n).toSpec).next a a' ∧ @SimRel n ms' a' := by
  intro ms ms' a hinv hR ⟨act, hgate, htrans⟩
  cases act with
  -- ── Stutter cases: send / recv / drop ──────────────────────────
  | sendAcquireReq p =>
    -- Stutter: appends acquireReq p; no response msg added
    simp only [msgLeaseSpec] at htrans; subst htrans
    refine ⟨a, .refl, ?_⟩
    constructor
    · exact hR.nextToken_eq
    · exact hR.lockHolder_eq
    · exact hR.leaseActive_eq
    · exact hR.highToken_eq
    · exact hR.highSeq_eq
    · exact hR.journal_eq
    · intro q tok hm
      rw [List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | hm
      · exact hR.acq_resp_token q tok hm
      · exact absurd hm (by simp)
    · intro q tok seq hm hna
      rw [List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | hm
      · intro htok
        exact hR.write_resp_seq q tok seq hm
          (fun t ht => hna t (List.mem_append.mpr (Or.inl ht))) htok
      · exact absurd hm (by simp)
    · intro q tok hm hna
      rw [List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | hm
      · intro htok
        exact hR.rel_resp_leader q tok hm
          (fun t ht => hna t (List.mem_append.mpr (Or.inl ht))) htok
      · exact absurd hm (by simp)
    · intro q hnot; apply hR.myToken_match
      intro tok hc; apply hnot tok; rw [List.mem_append]; left; exact hc
    · intro q hna hns; apply hR.writeSeq_match
      · intro tok hc; apply hna tok; rw [List.mem_append]; left; exact hc
      · intro tok s hc; apply hns tok s; rw [List.mem_append]; left; exact hc
    · intro q hna hnr; apply hR.believes_match
      · intro tok hc; apply hna tok; rw [List.mem_append]; left; exact hc
      · intro tok hc; apply hnr tok; rw [List.mem_append]; left; exact hc
  | sendWriteReq p v =>
    -- Stutter: appends writeReq; no response msg added
    simp only [msgLeaseSpec] at htrans; subst htrans
    refine ⟨a, .refl, ?_⟩
    constructor
    · exact hR.nextToken_eq
    · exact hR.lockHolder_eq
    · exact hR.leaseActive_eq
    · exact hR.highToken_eq
    · exact hR.highSeq_eq
    · exact hR.journal_eq
    · intro q tok hm
      rw [List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | hm
      · exact hR.acq_resp_token q tok hm
      · exact absurd hm (by simp)
    · intro q tok seq hm hna
      rw [List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | hm
      · intro htok
        exact hR.write_resp_seq q tok seq hm
          (fun t ht => hna t (List.mem_append.mpr (Or.inl ht))) htok
      · exact absurd hm (by simp)
    · intro q tok hm hna
      rw [List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | hm
      · intro htok
        exact hR.rel_resp_leader q tok hm
          (fun t ht => hna t (List.mem_append.mpr (Or.inl ht))) htok
      · exact absurd hm (by simp)
    · intro q hnot; apply hR.myToken_match
      intro tok hc; apply hnot tok; rw [List.mem_append]; left; exact hc
    · intro q hna hns; apply hR.writeSeq_match
      · intro tok hc; apply hna tok; rw [List.mem_append]; left; exact hc
      · intro tok s hc; apply hns tok s; rw [List.mem_append]; left; exact hc
    · intro q hna hnr; apply hR.believes_match
      · intro tok hc; apply hna tok; rw [List.mem_append]; left; exact hc
      · intro tok hc; apply hnr tok; rw [List.mem_append]; left; exact hc
  | sendReleaseReq p =>
    -- Stutter: appends releaseReq; no response msg added
    simp only [msgLeaseSpec] at htrans; subst htrans
    refine ⟨a, .refl, ?_⟩
    constructor
    · exact hR.nextToken_eq
    · exact hR.lockHolder_eq
    · exact hR.leaseActive_eq
    · exact hR.highToken_eq
    · exact hR.highSeq_eq
    · exact hR.journal_eq
    · intro q tok hm
      rw [List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | hm
      · exact hR.acq_resp_token q tok hm
      · exact absurd hm (by simp)
    · intro q tok seq hm hna
      rw [List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | hm
      · intro htok
        exact hR.write_resp_seq q tok seq hm
          (fun t ht => hna t (List.mem_append.mpr (Or.inl ht))) htok
      · exact absurd hm (by simp)
    · intro q tok hm hna
      rw [List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | hm
      · intro htok
        exact hR.rel_resp_leader q tok hm
          (fun t ht => hna t (List.mem_append.mpr (Or.inl ht))) htok
      · exact absurd hm (by simp)
    · intro q hnot; apply hR.myToken_match
      intro tok hc; apply hnot tok; rw [List.mem_append]; left; exact hc
    · intro q hna hns; apply hR.writeSeq_match
      · intro tok hc; apply hna tok; rw [List.mem_append]; left; exact hc
      · intro tok s hc; apply hns tok s; rw [List.mem_append]; left; exact hc
    · intro q hna hnr; apply hR.believes_match
      · intro tok hc; apply hna tok; rw [List.mem_append]; left; exact hc
      · intro tok hc; apply hnr tok; rw [List.mem_append]; left; exact hc
  | dropMsg msg =>
    -- Stutter: dropMsg restricted to requests. Responses can't be in the erased set.
    simp only [msgLeaseSpec] at hgate htrans; subst htrans
    obtain ⟨hmem, hreq⟩ := hgate
    have hsub : ∀ m, m ∈ ms.network.erase msg → m ∈ ms.network :=
      fun _m hm => List.erase_subset hm
    -- Request messages are not responses, so all response membership delegates directly.
    have h_not_acqResp : ∀ q t, msg ≠ Msg.acquireResp q t := by
      intro q t h; subst h; simp [Msg.isRequest] at hreq
    have h_not_wrResp : ∀ q tok seq, msg ≠ Msg.writeResp q tok seq := by
      intro q tok seq h; subst h; simp [Msg.isRequest] at hreq
    have h_not_relResp : ∀ q tok, msg ≠ Msg.releaseResp q tok := by
      intro q tok h; subst h; simp [Msg.isRequest] at hreq
    -- Any response in erased network was in old network
    -- AND: any response in old network is in erased network (since msg ≠ response)
    have h_resp_iff_acq : ∀ q t, Msg.acquireResp q t ∈ ms.network.erase msg ↔
        Msg.acquireResp q t ∈ ms.network :=
      fun q t => ⟨fun hm => hsub _ hm,
        fun hm => List.mem_erase_of_ne (h_not_acqResp q t ·.symm) |>.mpr hm⟩
    have h_resp_iff_wr : ∀ q tok seq, Msg.writeResp q tok seq ∈ ms.network.erase msg ↔
        Msg.writeResp q tok seq ∈ ms.network :=
      fun q tok seq => ⟨fun hm => hsub _ hm,
        fun hm => List.mem_erase_of_ne (h_not_wrResp q tok seq ·.symm) |>.mpr hm⟩
    have h_resp_iff_rel : ∀ q tok, Msg.releaseResp q tok ∈ ms.network.erase msg ↔
        Msg.releaseResp q tok ∈ ms.network :=
      fun q tok => ⟨fun hm => hsub _ hm,
        fun hm => List.mem_erase_of_ne (h_not_relResp q tok ·.symm) |>.mpr hm⟩
    refine ⟨a, .refl, ?_⟩
    constructor
    · exact hR.nextToken_eq
    · exact hR.lockHolder_eq
    · exact hR.leaseActive_eq
    · exact hR.highToken_eq
    · exact hR.highSeq_eq
    · exact hR.journal_eq
    · intro q tok hm; exact hR.acq_resp_token q tok (hsub _ hm)
    · intro q tok seq hm hna htok
      exact hR.write_resp_seq q tok seq (hsub _ hm)
        (fun t ht => hna t ((h_resp_iff_acq q t).mpr ht)) htok
    · intro q tok hm hna htok
      exact hR.rel_resp_leader q tok (hsub _ hm)
        (fun t ht => hna t ((h_resp_iff_acq q t).mpr ht)) htok
    · intro q hnot; exact hR.myToken_match q
        (fun t ht => hnot t ((h_resp_iff_acq q t).mpr ht))
    · intro q hna hns; exact hR.writeSeq_match q
        (fun t ht => hna t ((h_resp_iff_acq q t).mpr ht))
        (fun tok s hs => hns tok s ((h_resp_iff_wr q tok s).mpr hs))
    · intro q hna hnr; exact hR.believes_match q
        (fun t ht => hna t ((h_resp_iff_acq q t).mpr ht))
        (fun tok hs => hnr tok ((h_resp_iff_rel q tok).mpr hs))
  | recvAcquireResp p token =>
    -- Stutter: concrete client catches up to abstract.
    -- Network is (erase acquireResp).filter (drop stale writeResp/releaseResp for p).
    simp only [msgLeaseSpec] at htrans; subst htrans
    have hmem : Msg.acquireResp p token ∈ ms.network := hgate
    have hpre := hR.acq_resp_token p token hmem
    -- Filter membership helpers
    let filt := (fun m => match m with
      | Msg.writeResp q _ _ => decide (q ≠ p)
      | Msg.releaseResp q _ => decide (q ≠ p)
      | _ => true : Msg n → Bool)
    have h_filt_sub : ∀ m, m ∈ (ms.network.erase (Msg.acquireResp p token)).filter filt →
        m ∈ ms.network :=
      fun m hm => List.erase_subset (List.mem_filter.mp hm).1
    -- acquireResp passes the filter (it's not writeResp/releaseResp)
    have h_acq_filt : ∀ q tok, Msg.acquireResp q tok ∈
        (ms.network.erase (Msg.acquireResp p token)).filter filt →
        Msg.acquireResp q tok ∈ ms.network.erase (Msg.acquireResp p token) := by
      intro q tok hm; exact (List.mem_filter.mp hm).1
    -- No writeResp for p in filtered network
    have h_no_wr_p : ∀ tok seq, Msg.writeResp p tok seq ∉
        (ms.network.erase (Msg.acquireResp p token)).filter filt := by
      intro tok seq hm
      have := (List.mem_filter.mp hm).2; simp [filt] at this
    -- No releaseResp for p in filtered network
    have h_no_rel_p : ∀ tok, Msg.releaseResp p tok ∉
        (ms.network.erase (Msg.acquireResp p token)).filter filt := by
      intro tok hm
      have := (List.mem_filter.mp hm).2; simp [filt] at this
    -- For q ≠ p: non-p messages pass filter and erase
    have h_acq_ne : ∀ q tok, q ≠ p → Msg.acquireResp q tok ∈ ms.network →
        Msg.acquireResp q tok ∈ (ms.network.erase (Msg.acquireResp p token)).filter filt := by
      intro q tok hqp hm
      apply List.mem_filter.mpr
      exact ⟨List.mem_erase_of_ne (by simp [hqp]) |>.mpr hm, by simp [filt]⟩
    have h_wr_ne : ∀ q tok seq, q ≠ p → Msg.writeResp q tok seq ∈ ms.network →
        Msg.writeResp q tok seq ∈ (ms.network.erase (Msg.acquireResp p token)).filter filt := by
      intro q tok seq hqp hm
      apply List.mem_filter.mpr
      exact ⟨List.mem_erase_of_ne (by simp) |>.mpr hm, by simp [filt, hqp]⟩
    have h_rel_ne : ∀ q tok, q ≠ p → Msg.releaseResp q tok ∈ ms.network →
        Msg.releaseResp q tok ∈ (ms.network.erase (Msg.acquireResp p token)).filter filt := by
      intro q tok hqp hm
      apply List.mem_filter.mpr
      exact ⟨List.mem_erase_of_ne (by simp) |>.mpr hm, by simp [filt, hqp]⟩
    refine ⟨a, .refl, ?_⟩
    constructor
    · exact hR.nextToken_eq
    · exact hR.lockHolder_eq
    · exact hR.leaseActive_eq
    · exact hR.highToken_eq
    · exact hR.highSeq_eq
    · exact hR.journal_eq
    · intro q tok' hm; exact hR.acq_resp_token q tok' (h_filt_sub _ hm)
    · -- write_resp_seq: no writeResp for p in filtered net → q=p vacuous
      intro q tok seq hm hna htok
      by_cases hqp : q = p
      · subst hqp; exfalso; exact h_no_wr_p tok seq hm
      · exact hR.write_resp_seq q tok seq (h_filt_sub _ hm)
          (fun t ht => hna t (h_acq_ne q t hqp ht))
          (by simp only [hqp, ite_false] at htok; exact htok)
    · -- rel_resp_leader: no releaseResp for p in filtered net → q=p vacuous
      intro q tok hm hna htok
      by_cases hqp : q = p
      · subst hqp; exfalso; exact h_no_rel_p tok hm
      · exact hR.rel_resp_leader q tok (h_filt_sub _ hm)
          (fun t ht => hna t (h_acq_ne q t hqp ht))
          (by simp only [hqp, ite_false] at htok; exact htok)
    · -- myToken_match
      intro q hnot
      simp only
      by_cases hqp : q = p
      · subst hqp; simp only [ite_true]; exact hpre.1
      · simp only [hqp, ite_false]
        apply hR.myToken_match
        intro tok' hc; exact hnot tok' (h_acq_ne q tok' hqp hc)
    · -- writeSeq_match
      intro q hna hns
      simp only
      by_cases hqp : q = p
      · subst hqp; simp only [ite_true]; exact hpre.2.1
      · simp only [hqp, ite_false]
        apply hR.writeSeq_match
        · intro tok' hc; exact hna tok' (h_acq_ne q tok' hqp hc)
        · intro tok s hc; exact hns tok s (h_wr_ne q tok s hqp hc)
    · -- believes_match
      intro q hna hnr
      simp only
      by_cases hqp : q = p
      · subst hqp; simp only [ite_true]; exact hpre.2.2
      · simp only [hqp, ite_false]
        apply hR.believes_match
        · intro tok' hc; exact hna tok' (h_acq_ne q tok' hqp hc)
        · intro tok hc; exact hnr tok (h_rel_ne q tok hqp hc)
  | recvWriteResp p token seq =>
    -- Stutter: writeResp erased + stale writeReqs filtered; abstract writeSeq p already = seq.
    simp only [msgLeaseSpec] at htrans; subst htrans
    obtain ⟨hmem, htok_gate⟩ := hgate
    refine ⟨a, .refl, ?_⟩
    -- Membership helpers for erase+filter network
    have hsub : ∀ m, m ∈ (ms.network.erase (Msg.writeResp p token seq)).filter
        (fun m => match m with | .writeReq q _ t _ => decide (q ≠ p ∨ t ≠ token) | _ => true) →
        m ∈ ms.network :=
      fun _m hm => List.erase_subset (List.mem_filter.mp hm).1
    -- Put a response message back into the filtered network
    have hput_acq : ∀ q t, Msg.acquireResp q t ∈ ms.network →
        Msg.acquireResp q t ∈ (ms.network.erase (Msg.writeResp p token seq)).filter
          (fun m => match m with | .writeReq q _ t _ => decide (q ≠ p ∨ t ≠ token) | _ => true) :=
      fun q t hm => List.mem_filter.mpr ⟨(List.mem_erase_of_ne (by simp)).mpr hm, rfl⟩
    have hput_wr : ∀ q t' s', Msg.writeResp q t' s' ∈ ms.network →
        Msg.writeResp q t' s' ≠ Msg.writeResp p token seq →
        Msg.writeResp q t' s' ∈ (ms.network.erase (Msg.writeResp p token seq)).filter
          (fun m => match m with | .writeReq q _ t _ => decide (q ≠ p ∨ t ≠ token) | _ => true) :=
      fun q t' s' hm hne => List.mem_filter.mpr ⟨(List.mem_erase_of_ne hne).mpr hm, rfl⟩
    have hput_rel : ∀ q t, Msg.releaseResp q t ∈ ms.network →
        Msg.releaseResp q t ∈ (ms.network.erase (Msg.writeResp p token seq)).filter
          (fun m => match m with | .writeReq q _ t _ => decide (q ≠ p ∨ t ≠ token) | _ => true) :=
      fun q t hm => List.mem_filter.mpr ⟨(List.mem_erase_of_ne (by simp)).mpr hm, rfl⟩
    constructor
    · exact hR.nextToken_eq
    · exact hR.lockHolder_eq
    · exact hR.leaseActive_eq
    · exact hR.highToken_eq
    · exact hR.highSeq_eq
    · exact hR.journal_eq
    · intro q tok hm; exact hR.acq_resp_token q tok (hsub _ hm)
    · -- write_resp_seq
      intro q tok' seq' hm hna htok
      exact hR.write_resp_seq q tok' seq' (hsub _ hm)
        (fun t ht => hna t (hput_acq q t ht)) htok
    · -- rel_resp_leader
      intro q tok' hm hna htok
      exact hR.rel_resp_leader q tok' (hsub _ hm)
        (fun t ht => hna t (hput_acq q t ht)) htok
    · intro q hnot; apply hR.myToken_match
      intro tok' hc; exact hnot tok' (hput_acq q tok' hc)
    · -- writeSeq_match
      intro q hna hns
      simp only
      by_cases hqp : q = p
      · simp only [hqp, ite_true]
        have hna' : ∀ t, Msg.acquireResp p t ∉ ms.network :=
          fun t ht => hna t (by rw [hqp]; exact hput_acq p t ht)
        exact hR.write_resp_seq p token seq hmem hna' htok_gate
      · simp only [hqp, ite_false]
        apply hR.writeSeq_match
        · intro tok' hc; exact hna tok' (hput_acq q tok' hc)
        · intro tok' s hc; exact hns tok' s (hput_wr q tok' s hc (by simp [hqp]))
    · -- believes_match
      intro q hna hnr; apply hR.believes_match
      · intro tok' hc; exact hna tok' (hput_acq q tok' hc)
      · intro tok' hc; exact hnr tok' (hput_rel q tok' hc)
  | recvReleaseResp p token =>
    -- Stutter: releaseResp erased; abstract believesLeader p already = false (when no acquireResp).
    simp only [msgLeaseSpec] at htrans; subst htrans
    obtain ⟨hmem, htok_gate, _⟩ := hgate
    refine ⟨a, .refl, ?_⟩
    have hsub : ∀ m, m ∈ ms.network.erase (Msg.releaseResp p token) → m ∈ ms.network :=
      fun _m hm => List.erase_subset hm
    constructor
    · exact hR.nextToken_eq
    · exact hR.lockHolder_eq
    · exact hR.leaseActive_eq
    · exact hR.highToken_eq
    · exact hR.highSeq_eq
    · exact hR.journal_eq
    · intro q tok hm; exact hR.acq_resp_token q tok (hsub _ hm)
    · -- write_resp_seq
      intro q tok' seq' hm hna htok
      exact hR.write_resp_seq q tok' seq' (hsub _ hm)
        (fun t ht => hna t (List.mem_erase_of_ne (by simp) |>.mpr ht))
        htok
    · -- rel_resp_leader
      intro q tok' hm hna htok
      exact hR.rel_resp_leader q tok' (hsub _ hm)
        (fun t ht => hna t (List.mem_erase_of_ne (by simp) |>.mpr ht))
        htok
    · intro q hnot; apply hR.myToken_match
      intro tok' hc; exact hnot tok' (List.mem_erase_of_ne (by simp) |>.mpr hc)
    · -- writeSeq_match
      intro q hna hns; apply hR.writeSeq_match
      · intro tok' hc; exact hna tok' (List.mem_erase_of_ne (by simp) |>.mpr hc)
      · intro tok' s hc; exact hns tok' s (List.mem_erase_of_ne (by simp) |>.mpr hc)
    · -- believes_match
      intro q hna hnr
      simp only
      by_cases hqp : q = p
      · simp only [hqp, ite_true]
        have hna' : ∀ t, Msg.acquireResp p t ∉ ms.network :=
          fun t ht => hna t (by rw [hqp]; exact List.mem_erase_of_ne (by simp) |>.mpr ht)
        exact hR.rel_resp_leader p token hmem hna' htok_gate
      · simp only [hqp, ite_false]
        apply hR.believes_match
        · intro tok' hc; exact hna tok' (List.mem_erase_of_ne (by simp) |>.mpr hc)
        · intro tok' hc; exact hnr tok' (List.mem_erase_of_ne (by simp [hqp]) |>.mpr hc)
  | sendHeartbeatReq p =>
    -- Stutter: appends heartbeatReq p (myToken p); no response msg involved.
    simp only [msgLeaseSpec] at htrans; subst htrans
    refine ⟨a, .refl, ?_⟩
    -- Membership iffs for non-heartbeat messages: appending a heartbeatReq
    -- does not affect whether acquireResp/writeResp/releaseResp are in net.
    have h_iff_acq : ∀ q t, Msg.acquireResp q t ∈
        ms.network ++ [Msg.heartbeatReq p (ms.myToken p)] ↔
        Msg.acquireResp q t ∈ ms.network := by
      intro q t
      rw [List.mem_append, List.mem_singleton]; simp
    have h_iff_wr : ∀ q tok seq, Msg.writeResp q tok seq ∈
        ms.network ++ [Msg.heartbeatReq p (ms.myToken p)] ↔
        Msg.writeResp q tok seq ∈ ms.network := by
      intro q tok seq
      rw [List.mem_append, List.mem_singleton]; simp
    have h_iff_rel : ∀ q tok, Msg.releaseResp q tok ∈
        ms.network ++ [Msg.heartbeatReq p (ms.myToken p)] ↔
        Msg.releaseResp q tok ∈ ms.network := by
      intro q tok
      rw [List.mem_append, List.mem_singleton]; simp
    constructor
    · exact hR.nextToken_eq
    · exact hR.lockHolder_eq
    · exact hR.leaseActive_eq
    · exact hR.highToken_eq
    · exact hR.highSeq_eq
    · exact hR.journal_eq
    · intro q tok hm; exact hR.acq_resp_token q tok ((h_iff_acq q tok).mp hm)
    · intro q tok seq hm hna htok
      exact hR.write_resp_seq q tok seq ((h_iff_wr q tok seq).mp hm)
        (fun t ht => hna t ((h_iff_acq q t).mpr ht)) htok
    · intro q tok hm hna htok
      exact hR.rel_resp_leader q tok ((h_iff_rel q tok).mp hm)
        (fun t ht => hna t ((h_iff_acq q t).mpr ht)) htok
    · intro q hnot; exact hR.myToken_match q
        (fun t ht => hnot t ((h_iff_acq q t).mpr ht))
    · intro q hna hns; exact hR.writeSeq_match q
        (fun t ht => hna t ((h_iff_acq q t).mpr ht))
        (fun tok s hs => hns tok s ((h_iff_wr q tok s).mpr hs))
    · intro q hna hnr; exact hR.believes_match q
        (fun t ht => hna t ((h_iff_acq q t).mpr ht))
        (fun tok hs => hnr tok ((h_iff_rel q tok).mpr hs))
  | processHeartbeat p token =>
    -- Stutter: erases heartbeatReq p token, appends heartbeatResp p token.
    -- No acquireResp/writeResp/releaseResp touched. Abstract state unchanged.
    simp only [msgLeaseSpec] at hgate htrans
    obtain ⟨_, _, _, _, _, _⟩ := hgate; subst htrans
    refine ⟨a, .refl, ?_⟩
    -- Membership iffs for non-heartbeat messages.
    have h_iff_acq : ∀ q t, Msg.acquireResp q t ∈
        ms.network.erase (Msg.heartbeatReq p token) ++ [Msg.heartbeatResp p token] ↔
        Msg.acquireResp q t ∈ ms.network := by
      intro q t
      rw [List.mem_append, List.mem_singleton]
      refine ⟨?_, ?_⟩
      · rintro (hm | heq)
        · exact List.erase_subset hm
        · simp at heq
      · intro hm
        exact Or.inl (List.mem_erase_of_ne (by simp) |>.mpr hm)
    have h_iff_wr : ∀ q tok seq, Msg.writeResp q tok seq ∈
        ms.network.erase (Msg.heartbeatReq p token) ++ [Msg.heartbeatResp p token] ↔
        Msg.writeResp q tok seq ∈ ms.network := by
      intro q tok seq
      rw [List.mem_append, List.mem_singleton]
      refine ⟨?_, ?_⟩
      · rintro (hm | heq)
        · exact List.erase_subset hm
        · simp at heq
      · intro hm
        exact Or.inl (List.mem_erase_of_ne (by simp) |>.mpr hm)
    have h_iff_rel : ∀ q tok, Msg.releaseResp q tok ∈
        ms.network.erase (Msg.heartbeatReq p token) ++ [Msg.heartbeatResp p token] ↔
        Msg.releaseResp q tok ∈ ms.network := by
      intro q tok
      rw [List.mem_append, List.mem_singleton]
      refine ⟨?_, ?_⟩
      · rintro (hm | heq)
        · exact List.erase_subset hm
        · simp at heq
      · intro hm
        exact Or.inl (List.mem_erase_of_ne (by simp) |>.mpr hm)
    constructor
    · exact hR.nextToken_eq
    · exact hR.lockHolder_eq
    · exact hR.leaseActive_eq
    · exact hR.highToken_eq
    · exact hR.highSeq_eq
    · exact hR.journal_eq
    · intro q tok hm; exact hR.acq_resp_token q tok ((h_iff_acq q tok).mp hm)
    · intro q tok seq hm hna htok
      exact hR.write_resp_seq q tok seq ((h_iff_wr q tok seq).mp hm)
        (fun t ht => hna t ((h_iff_acq q t).mpr ht)) htok
    · intro q tok hm hna htok
      exact hR.rel_resp_leader q tok ((h_iff_rel q tok).mp hm)
        (fun t ht => hna t ((h_iff_acq q t).mpr ht)) htok
    · intro q hnot; exact hR.myToken_match q
        (fun t ht => hnot t ((h_iff_acq q t).mpr ht))
    · intro q hna hns; exact hR.writeSeq_match q
        (fun t ht => hna t ((h_iff_acq q t).mpr ht))
        (fun tok s hs => hns tok s ((h_iff_wr q tok s).mpr hs))
    · intro q hna hnr; exact hR.believes_match q
        (fun t ht => hna t ((h_iff_acq q t).mpr ht))
        (fun tok hs => hnr tok ((h_iff_rel q tok).mpr hs))
  | recvHeartbeatResp p token =>
    -- Stutter: erases heartbeatResp p token. No response-type message affected.
    simp only [msgLeaseSpec] at hgate htrans
    obtain ⟨_, _⟩ := hgate; subst htrans
    refine ⟨a, .refl, ?_⟩
    have hsub : ∀ m, m ∈ ms.network.erase (Msg.heartbeatResp p token) → m ∈ ms.network :=
      fun _m hm => List.erase_subset hm
    have h_iff_acq : ∀ q t, Msg.acquireResp q t ∈
        ms.network.erase (Msg.heartbeatResp p token) ↔
        Msg.acquireResp q t ∈ ms.network :=
      fun q t => ⟨fun hm => hsub _ hm,
        fun hm => List.mem_erase_of_ne (by simp) |>.mpr hm⟩
    have h_iff_wr : ∀ q tok seq, Msg.writeResp q tok seq ∈
        ms.network.erase (Msg.heartbeatResp p token) ↔
        Msg.writeResp q tok seq ∈ ms.network :=
      fun q tok seq => ⟨fun hm => hsub _ hm,
        fun hm => List.mem_erase_of_ne (by simp) |>.mpr hm⟩
    have h_iff_rel : ∀ q tok, Msg.releaseResp q tok ∈
        ms.network.erase (Msg.heartbeatResp p token) ↔
        Msg.releaseResp q tok ∈ ms.network :=
      fun q tok => ⟨fun hm => hsub _ hm,
        fun hm => List.mem_erase_of_ne (by simp) |>.mpr hm⟩
    constructor
    · exact hR.nextToken_eq
    · exact hR.lockHolder_eq
    · exact hR.leaseActive_eq
    · exact hR.highToken_eq
    · exact hR.highSeq_eq
    · exact hR.journal_eq
    · intro q tok hm; exact hR.acq_resp_token q tok ((h_iff_acq q tok).mp hm)
    · intro q tok seq hm hna htok
      exact hR.write_resp_seq q tok seq ((h_iff_wr q tok seq).mp hm)
        (fun t ht => hna t ((h_iff_acq q t).mpr ht)) htok
    · intro q tok hm hna htok
      exact hR.rel_resp_leader q tok ((h_iff_rel q tok).mp hm)
        (fun t ht => hna t ((h_iff_acq q t).mpr ht)) htok
    · intro q hnot; exact hR.myToken_match q
        (fun t ht => hnot t ((h_iff_acq q t).mpr ht))
    · intro q hna hns; exact hR.writeSeq_match q
        (fun t ht => hna t ((h_iff_acq q t).mpr ht))
        (fun tok s hs => hns tok s ((h_iff_wr q tok s).mpr hs))
    · intro q hna hnr; exact hR.believes_match q
        (fun t ht => hna t ((h_iff_acq q t).mpr ht))
        (fun tok hs => hnr tok ((h_iff_rel q tok).mpr hs))
  -- ── Non-stutter cases: process / expire ────────────────────────
  | expireLease =>
    simp only [msgLeaseSpec] at htrans; subst htrans
    refine ⟨{ a with leaseActive := false },
      .single ⟨LeaseLock.LeaseAction.expireLease, ?_, ?_⟩,
      { hR with leaseActive_eq := rfl }⟩
    · -- gate
      show a.leaseActive = true; rw [hR.leaseActive_eq]; exact hgate
    · -- transition
      simp only [LeaseLock.leaseSpec]
  | processAcquire p =>
    -- Fire abstract acquire p. New network filters old acquireResp for p.
    simp only [msgLeaseSpec] at hgate htrans
    obtain ⟨_, hgl⟩ := hgate; subst htrans
    have hntEq : a.nextToken = ms.nextToken := hR.nextToken_eq
    -- Membership helpers for the filtered+appended network
    let filt_pa := (fun m => match m with
      | .acquireResp q _ => decide (q ≠ p)
      | .heartbeatResp q _ => decide (q ≠ p)
      | _ => true : Msg n → Bool)
    let net' := (ms.network.erase (Msg.acquireReq p)).filter filt_pa
      ++ [Msg.acquireResp p ms.nextToken]
    have h_acq_in : Msg.acquireResp p ms.nextToken ∈ net' :=
      List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
    -- Any msg in filtered part is in ms.network
    have h_filt_sub : ∀ m, m ∈ (ms.network.erase (Msg.acquireReq p)).filter filt_pa →
        m ∈ ms.network :=
      fun m hm => List.erase_subset (List.mem_filter.mp hm).1
    -- acquireResp for p is NOT in the filtered part (filter removes it)
    have h_no_acq_p : ∀ tok, Msg.acquireResp p tok ∉ (ms.network.erase (Msg.acquireReq p)).filter
        filt_pa := by
      intro tok hm
      have := (List.mem_filter.mp hm).2; simp [filt_pa] at this
    -- For q ≠ p, acquireResp q tok in ms.network → in net'
    have h_acq_ne : ∀ q tok, q ≠ p → Msg.acquireResp q tok ∈ ms.network →
        Msg.acquireResp q tok ∈ net' := by
      intro q tok hqp hm
      apply List.mem_append.mpr; left
      apply List.mem_filter.mpr
      exact ⟨List.mem_erase_of_ne (by simp) |>.mpr hm, by simp [filt_pa, hqp]⟩
    refine ⟨{ a with
        lockHolder := some p
        leaseActive := true
        nextToken := a.nextToken + 1
        myToken := fun q => if q = p then a.nextToken else a.myToken q
        writeSeq := fun q => if q = p then 0 else a.writeSeq q
        believesLeader := fun q => if q = p then true else a.believesLeader q },
      .single ⟨LeaseLock.LeaseAction.acquire p, ?_, ?_⟩, ?_⟩
    · simp only [LeaseLock.leaseSpec]; rwa [hR.lockHolder_eq, hR.leaseActive_eq]
    · simp only [LeaseLock.leaseSpec]
    · constructor
      · simp [hntEq]
      · rfl
      · rfl
      · exact hR.highToken_eq
      · exact hR.highSeq_eq
      · exact hR.journal_eq
      · -- acq_resp_token: only acquireResp for p is the new one
        intro q tok hm
        rw [List.mem_append, List.mem_singleton] at hm
        rcases hm with hm | hm
        · -- From filtered old network: q ≠ p (filter removed acquireResp for p)
          have hm' := h_filt_sub _ hm
          have hpre := hR.acq_resp_token q tok hm'
          have hqp : q ≠ p := by
            intro heq; subst heq; exact h_no_acq_p tok hm
          simp only [hqp, ite_false]; exact hpre
        · -- The new acquireResp p ms.nextToken
          simp only [Msg.acquireResp.injEq] at hm
          obtain ⟨rfl, rfl⟩ := hm
          simp only [ite_true]; exact ⟨hntEq, trivial, trivial⟩
      · -- write_resp_seq: q=p → exfalso (acquireResp p ms.nextToken in net')
        intro q tok seq hm hna htok
        rw [List.mem_append, List.mem_singleton] at hm
        rcases hm with hm | hm
        · by_cases hqp : q = p
          · subst hqp; exfalso; exact hna ms.nextToken h_acq_in
          · simp only [hqp, ite_false]
            exact hR.write_resp_seq q tok seq (h_filt_sub _ hm)
              (fun t ht => hna t (h_acq_ne q t hqp ht)) htok
        · exact absurd hm (by simp)
      · -- rel_resp_leader: same pattern
        intro q tok hm hna htok
        rw [List.mem_append, List.mem_singleton] at hm
        rcases hm with hm | hm
        · by_cases hqp : q = p
          · subst hqp; exfalso; exact hna ms.nextToken h_acq_in
          · simp only [hqp, ite_false]
            exact hR.rel_resp_leader q tok (h_filt_sub _ hm)
              (fun t ht => hna t (h_acq_ne q t hqp ht)) htok
        · exact absurd hm (by simp)
      · -- myToken_match: q=p → exfalso
        intro q hnot
        simp only
        by_cases hqp : q = p
        · subst hqp; exfalso; exact hnot ms.nextToken h_acq_in
        · simp only [hqp, ite_false]
          apply hR.myToken_match; intro tok hc
          exact hnot tok (h_acq_ne q tok hqp hc)
      · -- writeSeq_match: q=p → exfalso
        intro q hna hns
        simp only
        by_cases hqp : q = p
        · subst hqp; exfalso; exact hna ms.nextToken h_acq_in
        · simp only [hqp, ite_false]
          apply hR.writeSeq_match
          · intro tok hc; exact hna tok (h_acq_ne q tok hqp hc)
          · intro tok s hc
            apply hns tok s; apply List.mem_append.mpr; left
            exact List.mem_filter.mpr ⟨List.mem_erase_of_ne (by simp) |>.mpr hc, by simp⟩
      · -- believes_match: q=p → exfalso
        intro q hna hnr
        simp only
        by_cases hqp : q = p
        · subst hqp; exfalso; exact hna ms.nextToken h_acq_in
        · simp only [hqp, ite_false]
          apply hR.believes_match
          · intro tok hc; exact hna tok (h_acq_ne q tok hqp hc)
          · intro tok hc
            apply hnr tok; apply List.mem_append.mpr; left
            exact List.mem_filter.mpr ⟨List.mem_erase_of_ne (by simp) |>.mpr hc, by simp⟩
  | processWrite p v token seq =>
    simp only [msgLeaseSpec] at hgate htrans
    obtain ⟨hmem_w, hfence, htok_fresh⟩ := hgate; subst htrans
    -- Invariant-level facts derived from hinv + gate
    have htok_eq : ms.myToken p = token := by
      have h1 := hinv.writeReq_tok p v token seq hmem_w  -- token ≤ myToken p
      have h2 := hinv.myToken_lt p                       -- myToken p < nextToken = token + 1
      omega
    have hno_acq : ∀ t, Msg.acquireResp p t ∉ ms.network := by
      intro t ht
      have h1 := hinv.acqResp_gt p t ht   -- myToken p < t
      have h2 := hinv.acqResp_lt p t ht   -- t < nextToken = token + 1
      rw [htok_eq] at h1; omega
    have hno_wresp : ∀ tok s, Msg.writeResp p tok s ∉ ms.network := by
      intro tok' s' hs
      have heq := hinv.writeResp_eq p tok' s' hs  -- tok' = myToken p
      have hs' : Msg.writeResp p (ms.myToken p) s' ∈ ms.network := heq ▸ hs
      have hseq' := hinv.writeResp_seq p s' hs'   -- s' = writeSeq p + 1
      have hhw := hinv.writeResp_hw p tok' s' hs
      rw [heq, htok_eq, hseq'] at hhw
      have hseq_eq' := hinv.writeReq_seq p v seq (htok_eq ▸ hmem_w)
      omega
    have hseq_eq : seq = ms.writeSeq p + 1 :=
      hinv.writeReq_seq p v seq (htok_eq ▸ hmem_w)
    -- Derived abstract equalities
    have ha_tok : a.myToken p = token := by rw [← htok_eq]; exact hR.myToken_match p hno_acq
    have ha_seq : a.writeSeq p = ms.writeSeq p := hR.writeSeq_match p hno_acq hno_wresp
    -- Fire abstract writeOk p v
    refine ⟨{ a with
        highToken := a.myToken p
        highSeq := a.writeSeq p + 1
        writeSeq := fun q => if q = p then a.writeSeq p + 1 else a.writeSeq q
        journal := a.journal ++ [⟨v, a.myToken p, a.writeSeq p + 1⟩] },
      .single ⟨LeaseLock.LeaseAction.writeOk p v, ?_, ?_⟩, ?_⟩
    · -- Abstract gate
      show a.myToken p > a.highToken ∨ (a.myToken p = a.highToken ∧ a.writeSeq p + 1 > a.highSeq)
      rw [ha_tok, ha_seq, hR.highToken_eq, hR.highSeq_eq, ← hseq_eq]; exact hfence
    · simp only [LeaseLock.leaseSpec]
    · -- SimRel for post-state
      have hsub : ∀ m, m ∈ ms.network.erase (Msg.writeReq p v token seq) → m ∈ ms.network :=
        fun _m hm => List.erase_subset hm
      constructor
      · exact hR.nextToken_eq
      · exact hR.lockHolder_eq
      · exact hR.leaseActive_eq
      · show a.myToken p = token; exact ha_tok
      · show a.writeSeq p + 1 = seq; rw [ha_seq, hseq_eq]
      · show a.journal ++ [⟨v, a.myToken p, a.writeSeq p + 1⟩] = ms.journal ++ [⟨v, token, seq⟩]
        rw [hR.journal_eq, ha_tok, ha_seq, hseq_eq]
      · -- acq_resp_token
        intro q tok hm
        rw [List.mem_append, List.mem_singleton] at hm
        rcases hm with hm | hm
        · have hpre := hR.acq_resp_token q tok (hsub _ hm)
          by_cases hqp : q = p
          · subst hqp; exfalso; exact hno_acq tok (hsub _ hm)
          · simp only [hqp, ite_false]; exact hpre
        · exact absurd hm (by simp)
      · -- write_resp_seq: new writeResp p token seq in network
        intro q tok' seq' hm hna htok
        rw [List.mem_append, List.mem_singleton] at hm
        rcases hm with hm | hm
        · by_cases hqp : q = p
          · subst hqp; exfalso; exact hno_wresp tok' seq' (hsub _ hm)
          · simp only [hqp, ite_false]
            exact hR.write_resp_seq q tok' seq' (hsub _ hm)
              (fun t ht => hna t (List.mem_append.mpr (Or.inl
                (List.mem_erase_of_ne (by simp) |>.mpr ht)))) htok
        · simp only [Msg.writeResp.injEq] at hm
          obtain ⟨rfl, rfl, rfl⟩ := hm
          simp only [ite_true]; rw [ha_seq, hseq_eq]
      · -- rel_resp_leader: no releaseResp added
        intro q tok' hm hna htok
        rw [List.mem_append, List.mem_singleton] at hm
        rcases hm with hm | hm
        · exact hR.rel_resp_leader q tok' (hsub _ hm)
            (fun t ht => hna t (List.mem_append.mpr (Or.inl
              (List.mem_erase_of_ne (by simp) |>.mpr ht)))) htok
        · exact absurd hm (by simp)
      · -- myToken_match
        intro q hnot; apply hR.myToken_match
        intro tok' hc; exact hnot tok' (List.mem_append.mpr (Or.inl
          (List.mem_erase_of_ne (by simp) |>.mpr hc)))
      · -- writeSeq_match: q=p vacuous (writeResp p token seq in network)
        intro q hna hns
        simp only
        by_cases hqp : q = p
        · subst hqp; exfalso; apply hns token seq
          exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
        · simp only [hqp, ite_false]; apply hR.writeSeq_match
          · intro tok' hc; exact hna tok' (List.mem_append.mpr (Or.inl
              (List.mem_erase_of_ne (by simp) |>.mpr hc)))
          · intro tok' s hc; exact hns tok' s (List.mem_append.mpr (Or.inl
              (List.mem_erase_of_ne (by simp) |>.mpr hc)))
      · -- believes_match
        intro q hna hnr; apply hR.believes_match
        · intro tok' hc; exact hna tok' (List.mem_append.mpr (Or.inl
            (List.mem_erase_of_ne (by simp) |>.mpr hc)))
        · intro tok' hc; exact hnr tok' (List.mem_append.mpr (Or.inl
            (List.mem_erase_of_ne (by simp) |>.mpr hc)))
  | processRelease p token =>
    simp only [msgLeaseSpec] at hgate htrans
    obtain ⟨hmem_r, hhold, hactive, htok_fresh⟩ := hgate; subst htrans
    -- Invariant-level facts derived from hinv + gate
    have htok_eq : ms.myToken p = token := by
      have h1 := hinv.releaseReq_tok p token hmem_r
      have h2 := hinv.myToken_lt p
      omega
    have hno_acq : ∀ t, Msg.acquireResp p t ∉ ms.network := by
      intro t ht
      have h1 := hinv.acqResp_gt p t ht
      have h2 := hinv.acqResp_lt p t ht
      rw [htok_eq] at h1; omega
    -- Fire abstract release p
    refine ⟨{ a with
        lockHolder := none
        leaseActive := false
        believesLeader := fun q => if q = p then false else a.believesLeader q },
      .single ⟨LeaseLock.LeaseAction.release p, ?_, ?_⟩, ?_⟩
    · show a.lockHolder = some p ∧ a.leaseActive = true
      exact ⟨hR.lockHolder_eq ▸ hhold, hR.leaseActive_eq ▸ hactive⟩
    · simp only [LeaseLock.leaseSpec]
    · have hsub : ∀ m, m ∈ ms.network.erase (Msg.releaseReq p token) → m ∈ ms.network :=
        fun _m hm => List.erase_subset hm
      constructor
      · exact hR.nextToken_eq
      · rfl
      · rfl
      · exact hR.highToken_eq
      · exact hR.highSeq_eq
      · exact hR.journal_eq
      · -- acq_resp_token
        intro q tok hm
        rw [List.mem_append, List.mem_singleton] at hm
        rcases hm with hm | hm
        · have hpre := hR.acq_resp_token q tok (hsub _ hm)
          by_cases hqp : q = p
          · subst hqp; exfalso; exact hno_acq tok (hsub _ hm)
          · simp only [hqp, ite_false]; exact hpre
        · exact absurd hm (by simp)
      · -- write_resp_seq: no writeResp added
        intro q tok' seq' hm hna htok
        rw [List.mem_append, List.mem_singleton] at hm
        rcases hm with hm | hm
        · exact hR.write_resp_seq q tok' seq' (hsub _ hm)
            (fun t ht => hna t (List.mem_append.mpr (Or.inl
              (List.mem_erase_of_ne (by simp) |>.mpr ht)))) htok
        · exact absurd hm (by simp)
      · -- rel_resp_leader: new releaseResp p token
        intro q tok' hm hna htok
        rw [List.mem_append, List.mem_singleton] at hm
        rcases hm with hm | hm
        · by_cases hqp : q = p
          · subst hqp; simp only [ite_true]
          · simp only [hqp, ite_false]
            exact hR.rel_resp_leader q tok' (hsub _ hm)
              (fun t ht => hna t (List.mem_append.mpr (Or.inl
                (List.mem_erase_of_ne (by simp) |>.mpr ht)))) htok
        · simp only [Msg.releaseResp.injEq] at hm
          obtain ⟨rfl, rfl⟩ := hm; simp only [ite_true]
      · -- myToken_match
        intro q hnot; apply hR.myToken_match
        intro tok' hc; exact hnot tok' (List.mem_append.mpr (Or.inl
          (List.mem_erase_of_ne (by simp) |>.mpr hc)))
      · -- writeSeq_match
        intro q hna hns; apply hR.writeSeq_match
        · intro tok' hc; exact hna tok' (List.mem_append.mpr (Or.inl
            (List.mem_erase_of_ne (by simp) |>.mpr hc)))
        · intro tok' s hc; exact hns tok' s (List.mem_append.mpr (Or.inl
            (List.mem_erase_of_ne (by simp) |>.mpr hc)))
      · -- believes_match: q=p vacuous (releaseResp p token in network)
        intro q hna hnr
        simp only
        by_cases hqp : q = p
        · subst hqp; exfalso; apply hnr token
          exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
        · simp only [hqp, ite_false]; apply hR.believes_match
          · intro tok' hc; exact hna tok' (List.mem_append.mpr (Or.inl
              (List.mem_erase_of_ne (by simp) |>.mpr hc)))
          · intro tok' hc; exact hnr tok' (List.mem_append.mpr (Or.inl
              (List.mem_erase_of_ne (by simp) |>.mpr hc)))

/-- The network invariant holds initially. -/
theorem msgNetInv_init : ∀ s, (msgLeaseSpec n).init s → @MsgNetInv n s := by
  intro s hs; subst hs
  constructor <;> simp [initialMsgLease]

/-- Helper: count in singleton of a different Msg constructor is 0. -/
private theorem count_singleton_ne {n : Nat} (a b : Msg n) (h : a ≠ b) :
    List.count a [b] = 0 := List.count_eq_zero.mpr (by simp [h])

/-- The network invariant is preserved by all transitions. -/
theorem msgNetInv_step :
    ∀ s s', @MsgNetInv n s → ((msgLeaseSpec n).toSpec).next s s' → @MsgNetInv n s' := by
  intro s s' hinv ⟨act, hgate, htrans⟩
  cases act with
  | expireLease =>
    simp only [msgLeaseSpec] at hgate htrans; subst htrans
    exact ⟨hinv.myToken_lt, hinv.acqResp_lt, hinv.acqResp_gt, hinv.writeReq_tok,
      hinv.releaseReq_tok, hinv.writeResp_eq, hinv.releaseResp_eq, hinv.acqResp_excl_wr,
      hinv.acqResp_excl_rel, hinv.writeReq_seq, hinv.writeResp_seq, hinv.writeResp_hw,
      hinv.releaseResp_bl, hinv.acqResp_unique, hinv.acqResp_count, hinv.holder_believes,
      hinv.holder_rel_acq, hinv.releaseResp_count, hinv.writeResp_count,
      hinv.heartbeatReq_tok, hinv.heartbeatResp_eq, hinv.heartbeatResp_bl,
      hinv.heartbeatResp_count, hinv.acqResp_excl_hb⟩
  | sendAcquireReq p =>
    simp only [msgLeaseSpec] at hgate htrans; subst htrans
    have hmem : ∀ {m}, m ∈ s.network ++ [Msg.acquireReq p] → m ≠ Msg.acquireReq p → m ∈ s.network :=
      fun h hne => (List.mem_append.mp h).elim id (fun h => absurd (List.mem_singleton.mp h) hne)
    exact ⟨hinv.myToken_lt,
      fun p t h => hinv.acqResp_lt p t (hmem h (by simp)),
      fun p t h => hinv.acqResp_gt p t (hmem h (by simp)),
      fun p v t sq h => hinv.writeReq_tok p v t sq (hmem h (by simp)),
      fun p t h => hinv.releaseReq_tok p t (hmem h (by simp)),
      fun p t sq h => hinv.writeResp_eq p t sq (hmem h (by simp)),
      fun p t h => hinv.releaseResp_eq p t (hmem h (by simp)),
      fun p t h seq habs => hinv.acqResp_excl_wr p t (hmem h (by simp)) seq
        (hmem habs (by simp)),
      fun p t h habs => hinv.acqResp_excl_rel p t (hmem h (by simp))
        (hmem habs (by simp)),
      fun p v sq h => hinv.writeReq_seq p v sq (hmem h (by simp)),
      fun p sq h => hinv.writeResp_seq p sq (hmem h (by simp)),
      fun p t sq h => hinv.writeResp_hw p t sq (hmem h (by simp)),
      fun p t h => hinv.releaseResp_bl p t (hmem h (by simp)),
      fun p t1 t2 h1 h2 => hinv.acqResp_unique p t1 t2
        (hmem h1 (by simp)) (hmem h2 (by simp)),
      fun p t => by simp [List.count_append, List.count_nil]; exact hinv.acqResp_count p t,
      fun p h => (hinv.holder_believes p h).imp id (fun ⟨t, ht⟩ => ⟨t, List.mem_append.mpr (.inl ht)⟩),
      fun q t h hrel => let ⟨t', ht'⟩ := hinv.holder_rel_acq q t h (hmem hrel (by simp));
        ⟨t', List.mem_append.mpr (.inl ht')⟩,
      fun p t => by simp [List.count_append, List.count_nil]; exact hinv.releaseResp_count p t,
      fun p t sq => by simp [List.count_append, List.count_nil]; exact hinv.writeResp_count p t sq,
      fun p t h => hinv.heartbeatReq_tok p t (hmem h (by simp)),
      fun p t h => hinv.heartbeatResp_eq p t (hmem h (by simp)),
      fun p t h => hinv.heartbeatResp_bl p t (hmem h (by simp)),
      fun p t => by simp [List.count_append, List.count_nil]; exact hinv.heartbeatResp_count p t,
      fun p t h tok hhb => hinv.acqResp_excl_hb p t (hmem h (by simp)) tok (hmem hhb (by simp))⟩
  | processAcquire p =>
    simp only [msgLeaseSpec] at hgate htrans
    obtain ⟨hmem_a, hgl⟩ := hgate; subst htrans
    -- Abbreviations for the filtered+appended network
    let filt := (fun m => match m with
      | Msg.acquireResp q _ => decide (q ≠ p)
      | Msg.heartbeatResp q _ => decide (q ≠ p)
      | _ => true : Msg n → Bool)
    let net' := (s.network.erase (Msg.acquireReq p)).filter filt ++ [Msg.acquireResp p s.nextToken]
    -- Membership helpers
    have h_filt_sub : ∀ m, m ∈ (s.network.erase (Msg.acquireReq p)).filter filt → m ∈ s.network :=
      fun m hm => List.erase_subset (List.mem_filter.mp hm).1
    -- acquireResp for p is NOT in the filtered part (filter removes it)
    have h_no_acq_p : ∀ tok, Msg.acquireResp p tok ∉ (s.network.erase (Msg.acquireReq p)).filter filt := by
      intro tok hm; have := (List.mem_filter.mp hm).2; simp [filt] at this
    -- heartbeatResp for p is NOT in the filtered part (filter removes it)
    have h_no_hb_p : ∀ tok, Msg.heartbeatResp p tok ∉ (s.network.erase (Msg.acquireReq p)).filter filt := by
      intro tok hm; have := (List.mem_filter.mp hm).2; simp [filt] at this
    -- New acquireResp p s.nextToken is in net'
    have h_acq_in : Msg.acquireResp p s.nextToken ∈ net' :=
      List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
    -- For q ≠ p: acquireResp q tok passes filter
    have h_acq_ne : ∀ q tok, q ≠ p → Msg.acquireResp q tok ∈ s.network →
        Msg.acquireResp q tok ∈ (s.network.erase (Msg.acquireReq p)).filter filt := by
      intro q tok hqp hm
      exact List.mem_filter.mpr ⟨List.mem_erase_of_ne (by simp) |>.mpr hm, by simp [filt, hqp]⟩
    -- Non-acquireResp messages pass the filter
    have h_wr_filt : ∀ q v t sq, Msg.writeReq q v t sq ∈ s.network →
        Msg.writeReq q v t sq ∈ (s.network.erase (Msg.acquireReq p)).filter filt := by
      intro q v t sq hm
      exact List.mem_filter.mpr ⟨List.mem_erase_of_ne (by simp) |>.mpr hm, by simp [filt]⟩
    have h_rel_req_filt : ∀ q t, Msg.releaseReq q t ∈ s.network →
        Msg.releaseReq q t ∈ (s.network.erase (Msg.acquireReq p)).filter filt := by
      intro q t hm
      exact List.mem_filter.mpr ⟨List.mem_erase_of_ne (by simp) |>.mpr hm, by simp [filt]⟩
    have h_wr_resp_filt : ∀ q t sq, Msg.writeResp q t sq ∈ s.network →
        Msg.writeResp q t sq ∈ (s.network.erase (Msg.acquireReq p)).filter filt := by
      intro q t sq hm
      exact List.mem_filter.mpr ⟨List.mem_erase_of_ne (by simp) |>.mpr hm, by simp [filt]⟩
    have h_rel_resp_filt : ∀ q t, Msg.releaseResp q t ∈ s.network →
        Msg.releaseResp q t ∈ (s.network.erase (Msg.acquireReq p)).filter filt := by
      intro q t hm
      exact List.mem_filter.mpr ⟨List.mem_erase_of_ne (by simp) |>.mpr hm, by simp [filt]⟩
    -- Membership in net': either from filtered old or the new singleton
    have hnew : ∀ {m}, m ∈ net' → m ∈ (s.network.erase (Msg.acquireReq p)).filter filt ∨
        m = Msg.acquireResp p s.nextToken := by
      intro m hm; rw [List.mem_append, List.mem_singleton] at hm; exact hm
    exact ⟨
      -- myToken_lt: nextToken increased by 1
      fun q => by show s.myToken q < s.nextToken + 1; have := hinv.myToken_lt q; omega,
      -- acqResp_lt
      fun q t h => by
        show t < s.nextToken + 1
        rcases hnew h with h | h
        · have := hinv.acqResp_lt q t (h_filt_sub _ h); omega
        · simp only [Msg.acquireResp.injEq] at h; omega,
      -- acqResp_gt
      fun q t h => by
        rcases hnew h with h | h
        · exact hinv.acqResp_gt q t (h_filt_sub _ h)
        · simp only [Msg.acquireResp.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          exact hinv.myToken_lt q,
      -- writeReq_tok
      fun q v t sq h => by
        rcases hnew h with h | h
        · exact hinv.writeReq_tok q v t sq (h_filt_sub _ h)
        · exact absurd h (by simp),
      -- releaseReq_tok
      fun q t h => by
        rcases hnew h with h | h
        · exact hinv.releaseReq_tok q t (h_filt_sub _ h)
        · exact absurd h (by simp),
      -- writeResp_eq
      fun q t sq h => by
        rcases hnew h with h | h
        · exact hinv.writeResp_eq q t sq (h_filt_sub _ h)
        · exact absurd h (by simp),
      -- releaseResp_eq
      fun q t h => by
        rcases hnew h with h | h
        · exact hinv.releaseResp_eq q t (h_filt_sub _ h)
        · exact absurd h (by simp),
      -- acqResp_excl_wr
      fun q t h seq habs => by
        rcases hnew h with h | h
        · rcases hnew habs with habs | habs
          · exact hinv.acqResp_excl_wr q t (h_filt_sub _ h) seq (h_filt_sub _ habs)
          · exact absurd habs (by simp)
        · simp only [Msg.acquireResp.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          rcases hnew habs with habs | habs
          · have heq := hinv.writeResp_eq q s.nextToken seq (h_filt_sub _ habs)
            have hlt := hinv.myToken_lt q; omega
          · exact absurd habs (by simp),
      -- acqResp_excl_rel
      fun q t h habs => by
        rcases hnew h with h | h
        · rcases hnew habs with habs | habs
          · exact hinv.acqResp_excl_rel q t (h_filt_sub _ h) (h_filt_sub _ habs)
          · exact absurd habs (by simp)
        · simp only [Msg.acquireResp.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          rcases hnew habs with habs | habs
          · have heq := hinv.releaseResp_eq q s.nextToken (h_filt_sub _ habs)
            have hlt := hinv.myToken_lt q; omega
          · exact absurd habs (by simp),
      -- writeReq_seq: myToken unchanged, writeReq passes filter
      fun q v sq h => by
        rcases hnew h with h | h
        · exact hinv.writeReq_seq q v sq (h_filt_sub _ h)
        · exact absurd h (by simp),
      -- writeResp_seq: myToken unchanged
      fun q sq h => by
        rcases hnew h with h | h
        · exact hinv.writeResp_seq q sq (h_filt_sub _ h)
        · exact absurd h (by simp),
      -- writeResp_hw
      fun q t sq h => by
        rcases hnew h with h | h
        · exact hinv.writeResp_hw q t sq (h_filt_sub _ h)
        · exact absurd h (by simp),
      -- releaseResp_bl: believesLeader unchanged
      fun q t h => by
        rcases hnew h with h | h
        · exact hinv.releaseResp_bl q t (h_filt_sub _ h)
        · exact absurd h (by simp),
      -- acqResp_unique: after filter, no acquireResp for p remains, new one is unique
      fun q t1 t2 h1 h2 => by
        rcases hnew h1 with h1 | h1 <;> rcases hnew h2 with h2 | h2
        · exact hinv.acqResp_unique q t1 t2 (h_filt_sub _ h1) (h_filt_sub _ h2)
        · simp only [Msg.acquireResp.injEq] at h2; obtain ⟨rfl, rfl⟩ := h2
          exfalso; exact h_no_acq_p t1 h1
        · simp only [Msg.acquireResp.injEq] at h1; obtain ⟨rfl, rfl⟩ := h1
          exfalso; exact h_no_acq_p t2 h2
        · simp only [Msg.acquireResp.injEq] at h1 h2; omega,
      -- acqResp_count
      fun q t => by
        show List.count (Msg.acquireResp q t) net' ≤ 1
        by_cases hqp : q = p
        · subst hqp
          rw [List.count_append]
          have h0 : List.count (Msg.acquireResp q t) ((s.network.erase (Msg.acquireReq q)).filter filt) = 0 :=
            List.count_eq_zero.mpr (h_no_acq_p t)
          rw [h0, Nat.zero_add]
          simp [List.count_cons, List.count_nil]; split <;> omega
        · rw [show net' = (s.network.erase (Msg.acquireReq p)).filter filt ++ [Msg.acquireResp p s.nextToken] from rfl]
          rw [List.count_append, count_singleton_ne _ _ (by simp [hqp]), Nat.add_zero]
          exact Nat.le_trans (count_filter_le _ _ _)
            (by rw [List.count_erase_of_ne (by simp)]; exact hinv.acqResp_count q t),
      -- holder_believes: lockHolder = some p
      fun q h => by
        simp only [Option.some.injEq] at h; subst h
        exact Or.inr ⟨s.nextToken, h_acq_in⟩,
      -- holder_rel_acq: lockHolder = some p
      fun q t h hrel => by
        simp only [Option.some.injEq] at h; subst h
        exact ⟨s.nextToken, h_acq_in⟩,
      -- releaseResp_count
      fun q t => by
        show List.count (Msg.releaseResp q t) net' ≤ 1
        rw [show net' = (s.network.erase (Msg.acquireReq p)).filter filt ++ [Msg.acquireResp p s.nextToken] from rfl]
        rw [List.count_append, count_singleton_ne _ _ (by simp), Nat.add_zero]
        exact Nat.le_trans (count_filter_le _ _ _)
          (by rw [List.count_erase_of_ne (by simp)]; exact hinv.releaseResp_count q t),
      -- writeResp_count
      fun q t sq => by
        show List.count (Msg.writeResp q t sq) net' ≤ 1
        rw [show net' = (s.network.erase (Msg.acquireReq p)).filter filt ++ [Msg.acquireResp p s.nextToken] from rfl]
        rw [List.count_append, count_singleton_ne _ _ (by simp), Nat.add_zero]
        exact Nat.le_trans (count_filter_le _ _ _)
          (by rw [List.count_erase_of_ne (by simp)]; exact hinv.writeResp_count q t sq),
      -- heartbeatReq_tok: heartbeatReq passes the filter (filt returns true for it)
      fun q t h => by
        rcases hnew h with h | h
        · exact hinv.heartbeatReq_tok q t (h_filt_sub _ h)
        · exact absurd h (by simp),
      -- heartbeatResp_eq: heartbeatResp passes filter; myToken unchanged
      fun q t h => by
        rcases hnew h with h | h
        · exact hinv.heartbeatResp_eq q t (h_filt_sub _ h)
        · exact absurd h (by simp),
      -- heartbeatResp_bl: believesLeader unchanged
      fun q t h => by
        rcases hnew h with h | h
        · exact hinv.heartbeatResp_bl q t (h_filt_sub _ h)
        · exact absurd h (by simp),
      -- heartbeatResp_count: count can only decrease through filter+erase
      fun q t => by
        show List.count (Msg.heartbeatResp q t) net' ≤ 1
        rw [show net' = (s.network.erase (Msg.acquireReq p)).filter filt ++ [Msg.acquireResp p s.nextToken] from rfl]
        rw [List.count_append, count_singleton_ne _ _ (by simp), Nat.add_zero]
        exact Nat.le_trans (count_filter_le _ _ _)
          (by rw [List.count_erase_of_ne (by simp)]; exact hinv.heartbeatResp_count q t),
      -- acqResp_excl_hb: new net' filters heartbeatResp for p; so heartbeatResp p tok ∉ net'.
      fun q t h tok hhb => by
        rcases hnew h with h | h
        · rcases hnew hhb with hhb | hhb
          · exact hinv.acqResp_excl_hb q t (h_filt_sub _ h) tok (h_filt_sub _ hhb)
          · exact absurd hhb (by simp)
        · simp only [Msg.acquireResp.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          -- acquireResp p s.nextToken is the new one. heartbeatResp p tok in net'?
          -- Filter removed heartbeatResp p _: h_no_hb_p says heartbeatResp p tok ∉ filtered part.
          rcases hnew hhb with hhb | hhb
          · exact absurd hhb (h_no_hb_p tok)
          · exact absurd hhb (by simp)⟩
  | recvAcquireResp p token =>
    simp only [msgLeaseSpec] at hgate htrans; subst htrans
    have hmem : Msg.acquireResp p token ∈ s.network := hgate
    -- Abbreviation for the filter predicate
    let filt := (fun m => match m with
      | Msg.writeResp q _ _ => decide (q ≠ p)
      | Msg.releaseResp q _ => decide (q ≠ p)
      | _ => true : Msg n → Bool)
    let net' := (s.network.erase (Msg.acquireResp p token)).filter filt
    -- Membership: anything in net' is in s.network
    have h_filt_sub : ∀ m, m ∈ net' → m ∈ s.network :=
      fun m hm => List.erase_subset (List.mem_filter.mp hm).1
    -- acquireResp passes the filter (not writeResp/releaseResp)
    have h_acq_filt : ∀ q tok, Msg.acquireResp q tok ∈ net' →
        Msg.acquireResp q tok ∈ s.network.erase (Msg.acquireResp p token) :=
      fun q tok hm => (List.mem_filter.mp hm).1
    -- No writeResp for p in net'
    have h_no_wr_p : ∀ tok seq, Msg.writeResp p tok seq ∉ net' := by
      intro tok seq hm; have := (List.mem_filter.mp hm).2; simp [filt] at this
    -- No releaseResp for p in net'
    have h_no_rel_p : ∀ tok, Msg.releaseResp p tok ∉ net' := by
      intro tok hm; have := (List.mem_filter.mp hm).2; simp [filt] at this
    -- No acquireResp p _ in net' (erase removes the one copy; count ≤ 1)
    have h_no_acq_p : ∀ tok, Msg.acquireResp p tok ∉ net' := by
      intro tok hm
      have hm' := h_acq_filt p tok hm
      have heq := hinv.acqResp_unique p tok token (List.erase_subset hm') hmem
      have h1 := List.count_erase_self (a := Msg.acquireResp p token) (l := s.network)
      have h2 := hinv.acqResp_count p token
      have h3 : List.count (Msg.acquireResp p token) (s.network.erase (Msg.acquireResp p token)) = 0 := by omega
      rw [heq] at hm'
      exact absurd hm' (List.count_eq_zero.mp h3)
    -- For q ≠ p: acquireResp q tok passes erase+filter
    have h_acq_ne : ∀ q tok, q ≠ p → Msg.acquireResp q tok ∈ s.network →
        Msg.acquireResp q tok ∈ net' := by
      intro q tok hqp hm
      exact List.mem_filter.mpr ⟨List.mem_erase_of_ne (by simp [hqp]) |>.mpr hm, by simp [filt]⟩
    -- writeReq passes erase+filter
    have h_wr_req_filt : ∀ q v t sq, Msg.writeReq q v t sq ∈ s.network →
        Msg.writeReq q v t sq ∈ net' := by
      intro q v t sq hm
      exact List.mem_filter.mpr ⟨List.mem_erase_of_ne (by simp) |>.mpr hm, by simp [filt]⟩
    -- releaseReq passes erase+filter
    have h_rel_req_filt : ∀ q t, Msg.releaseReq q t ∈ s.network →
        Msg.releaseReq q t ∈ net' := by
      intro q t hm
      exact List.mem_filter.mpr ⟨List.mem_erase_of_ne (by simp) |>.mpr hm, by simp [filt]⟩
    -- writeResp for q ≠ p passes
    have h_wr_ne : ∀ q tok seq, q ≠ p → Msg.writeResp q tok seq ∈ s.network →
        Msg.writeResp q tok seq ∈ net' := by
      intro q tok seq hqp hm
      exact List.mem_filter.mpr ⟨List.mem_erase_of_ne (by simp) |>.mpr hm, by simp [filt, hqp]⟩
    -- releaseResp for q ≠ p passes
    have h_rel_ne : ∀ q tok, q ≠ p → Msg.releaseResp q tok ∈ s.network →
        Msg.releaseResp q tok ∈ net' := by
      intro q tok hqp hm
      exact List.mem_filter.mpr ⟨List.mem_erase_of_ne (by simp) |>.mpr hm, by simp [filt, hqp]⟩
    exact ⟨
      -- myToken_lt: for q = p, token < nextToken (acqResp_lt); for q ≠ p, unchanged
      fun q => by
        show (if q = p then token else s.myToken q) < s.nextToken
        by_cases hqp : q = p
        · simp [hqp]; exact hinv.acqResp_lt p token hmem
        · simp [hqp]; exact hinv.myToken_lt q,
      -- acqResp_lt: acquireResps in net' ⊆ s.network
      fun q t h => hinv.acqResp_lt q t (h_filt_sub _ h),
      -- acqResp_gt: for q ≠ p, myToken q unchanged; for q = p, vacuous (no acqResp p in net')
      fun q t h => by
        show (if q = p then token else s.myToken q) < t
        by_cases hqp : q = p
        · subst hqp; exfalso; exact h_no_acq_p t h
        · simp [hqp]; exact hinv.acqResp_gt q t (h_filt_sub _ h),
      -- writeReq_tok: writeReqs pass filter; for q = p, token ≥ old myToken ≥ t
      fun q v t' sq h => by
        show t' ≤ (if q = p then token else s.myToken q)
        have hm := h_filt_sub _ h
        by_cases hqp : q = p
        · subst hqp; simp
          have := hinv.writeReq_tok q v t' sq hm
          have := hinv.acqResp_gt q token hmem
          omega
        · simp [hqp]; exact hinv.writeReq_tok q v t' sq hm,
      -- releaseReq_tok: similar
      fun q t' h => by
        show t' ≤ (if q = p then token else s.myToken q)
        have hm := h_filt_sub _ h
        by_cases hqp : q = p
        · subst hqp; simp
          have := hinv.releaseReq_tok q t' hm
          have := hinv.acqResp_gt q token hmem
          omega
        · simp [hqp]; exact hinv.releaseReq_tok q t' hm,
      -- writeResp_eq: writeResp for p filtered out; for q ≠ p, myToken q unchanged
      fun q t' sq h => by
        show t' = (if q = p then token else s.myToken q)
        by_cases hqp : q = p
        · subst hqp; exfalso; exact h_no_wr_p t' sq h
        · simp [hqp]; exact hinv.writeResp_eq q t' sq (h_filt_sub _ h),
      -- releaseResp_eq: releaseResp for p filtered out; for q ≠ p, myToken q unchanged
      fun q t' h => by
        show t' = (if q = p then token else s.myToken q)
        by_cases hqp : q = p
        · subst hqp; exfalso; exact h_no_rel_p t' h
        · simp [hqp]; exact hinv.releaseResp_eq q t' (h_filt_sub _ h),
      -- acqResp_excl_wr: acquireResp in net' has q ≠ p; writeResp in net' also has q ≠ p
      fun q t' h seq habs => hinv.acqResp_excl_wr q t' (h_filt_sub _ h) seq (h_filt_sub _ habs),
      -- acqResp_excl_rel: similar
      fun q t' h habs => hinv.acqResp_excl_rel q t' (h_filt_sub _ h) (h_filt_sub _ habs),
      -- writeReq_seq: for q = p, no writeReq with token exists (vacuous); for q ≠ p, unchanged
      fun q v sq h => by
        by_cases hqp : q = p
        · subst hqp; simp only [ite_true] at h ⊢
          have hm_old := h_filt_sub _ h
          have := hinv.writeReq_tok q v token sq hm_old
          have := hinv.acqResp_gt q token hmem
          omega
        · simp only [hqp, ite_false] at h ⊢
          exact hinv.writeReq_seq q v sq (h_filt_sub _ h),
      -- writeResp_seq: for q = p, no writeResp (vacuous); for q ≠ p, unchanged
      fun q sq h => by
        by_cases hqp : q = p
        · subst hqp; simp only [ite_true] at h ⊢
          exfalso; exact h_no_wr_p token sq h
        · simp only [hqp, ite_false] at h ⊢
          exact hinv.writeResp_seq q sq (h_filt_sub _ h),
      -- writeResp_hw: unchanged, writeResp in net' → in s.network
      fun q t' sq h => hinv.writeResp_hw q t' sq (h_filt_sub _ h),
      -- releaseResp_bl: for q = p, filtered out (vacuous); for q ≠ p, believesLeader unchanged
      fun q t' h => by
        show (if q = p then true else s.believesLeader q) = true
        by_cases hqp : q = p
        · simp [hqp]
        · simp [hqp]; exact hinv.releaseResp_bl q t' (h_filt_sub _ h),
      -- acqResp_unique: no acquireResp for p in net'; for q ≠ p, from hinv
      fun q t1 t2 h1 h2 => hinv.acqResp_unique q t1 t2 (h_filt_sub _ h1) (h_filt_sub _ h2),
      -- acqResp_count
      fun q t => by
        show List.count (Msg.acquireResp q t) net' ≤ 1
        exact Nat.le_trans (count_filter_le _ _ _)
          (by
            by_cases hqt : Msg.acquireResp q t = Msg.acquireResp p token
            · simp [Msg.acquireResp.injEq] at hqt; obtain ⟨rfl, rfl⟩ := hqt
              rw [List.count_erase_self]; have := hinv.acqResp_count q t; omega
            · rw [List.count_erase_of_ne hqt]; exact hinv.acqResp_count q t),
      -- holder_believes: lockHolder unchanged; for q = p, believesLeader p = true
      fun q h => by
        show (if q = p then true else s.believesLeader q) = true ∨
          ∃ t, Msg.acquireResp q t ∈ net'
        by_cases hqp : q = p
        · left; simp [hqp]
        · rcases hinv.holder_believes q h with hbl | ⟨t', ht'⟩
          · left; simp [hqp, hbl]
          · right; exact ⟨t', h_acq_ne q t' hqp ht'⟩,
      -- holder_rel_acq: lockHolder unchanged; releaseResp for p filtered out
      fun q t' h hrel => by
        by_cases hqp : q = p
        · subst hqp; exfalso; exact h_no_rel_p t' hrel
        · have hrel_old := h_filt_sub _ hrel
          obtain ⟨t'', ht''⟩ := hinv.holder_rel_acq q t' h hrel_old
          exact ⟨t'', h_acq_ne q t'' hqp ht''⟩,
      -- releaseResp_count: for q = p, filtered out (count = 0); for q ≠ p, ≤ count in old
      fun q t' => by
        show List.count (Msg.releaseResp q t') net' ≤ 1
        by_cases hqp : q = p
        · subst hqp; have := List.count_eq_zero.mpr (h_no_rel_p t'); omega
        · exact Nat.le_trans (count_filter_le _ _ _)
            (by rw [List.count_erase_of_ne (by simp)]; exact hinv.releaseResp_count q t'),
      -- writeResp_count: for q = p, filtered out (count = 0); for q ≠ p, ≤ count in old
      fun q t' sq => by
        show List.count (Msg.writeResp q t' sq) net' ≤ 1
        by_cases hqp : q = p
        · subst hqp; have := List.count_eq_zero.mpr (h_no_wr_p t' sq); omega
        · exact Nat.le_trans (count_filter_le _ _ _)
            (by rw [List.count_erase_of_ne (by simp)]; exact hinv.writeResp_count q t' sq),
      -- heartbeatReq_tok: heartbeatReq passes filter; myToken updated for p but heartbeatReq in
      -- net' must have been there before (passes erase+filter); tok ≤ myToken p ≤ new myToken p
      fun q t h => by
        show t ≤ (if q = p then token else s.myToken q)
        have hm := h_filt_sub _ h
        by_cases hqp : q = p
        · subst hqp; simp
          have := hinv.heartbeatReq_tok q t hm
          have := hinv.acqResp_gt q token hmem
          omega
        · simp [hqp]; exact hinv.heartbeatReq_tok q t hm,
      -- heartbeatResp_eq: q = p vacuous by acqResp_excl_hb; q ≠ p, myToken q unchanged
      fun q t h => by
        show t = (if q = p then token else s.myToken q)
        have hm := h_filt_sub _ h
        by_cases hqp : q = p
        · subst hqp; exfalso; exact hinv.acqResp_excl_hb q token hmem t hm
        · simp [hqp]; exact hinv.heartbeatResp_eq q t hm,
      -- heartbeatResp_bl: q = p vacuous by above; q ≠ p, believesLeader unchanged
      fun q t h => by
        show (if q = p then true else s.believesLeader q) = true
        have hm := h_filt_sub _ h
        by_cases hqp : q = p
        · subst hqp; exfalso; exact hinv.acqResp_excl_hb q token hmem t hm
        · simp [hqp]; exact hinv.heartbeatResp_bl q t hm,
      -- heartbeatResp_count: erase+filter can only decrease
      fun q t => by
        show List.count (Msg.heartbeatResp q t) net' ≤ 1
        exact Nat.le_trans (count_filter_le _ _ _)
          (by rw [List.count_erase_of_ne (by simp)]; exact hinv.heartbeatResp_count q t),
      -- acqResp_excl_hb: acquireResp q t in net' → heartbeatResp q tok ∉ net'
      fun q t h tok hhb => hinv.acqResp_excl_hb q t (h_filt_sub _ h) tok (h_filt_sub _ hhb)⟩
  | sendWriteReq p v =>
    simp only [msgLeaseSpec] at hgate htrans; subst htrans
    have hmem : ∀ {m}, m ∈ s.network ++ [Msg.writeReq p v (s.myToken p) (s.writeSeq p + 1)] →
        m ≠ Msg.writeReq p v (s.myToken p) (s.writeSeq p + 1) → m ∈ s.network :=
      fun h hne => (List.mem_append.mp h).elim id (fun h => absurd (List.mem_singleton.mp h) hne)
    have hnew : ∀ {m}, m ∈ s.network ++ [Msg.writeReq p v (s.myToken p) (s.writeSeq p + 1)] →
        m ∈ s.network ∨ m = Msg.writeReq p v (s.myToken p) (s.writeSeq p + 1) :=
      fun h => List.mem_append.mp h |>.imp id (List.mem_singleton.mp)
    exact ⟨hinv.myToken_lt,
      fun p t h => hinv.acqResp_lt p t (hmem h (by simp)),
      fun p t h => hinv.acqResp_gt p t (hmem h (by simp)),
      fun q w t sq h => by
        rcases hnew h with h | h
        · exact hinv.writeReq_tok q w t sq h
        · obtain ⟨rfl, -, rfl, -⟩ := h; exact Nat.le_refl _,
      fun p t h => hinv.releaseReq_tok p t (hmem h (by simp)),
      fun p t sq h => hinv.writeResp_eq p t sq (hmem h (by simp)),
      fun p t h => hinv.releaseResp_eq p t (hmem h (by simp)),
      fun p t h seq habs => hinv.acqResp_excl_wr p t (hmem h (by simp)) seq
        (hmem habs (by simp)),
      fun p t h habs => hinv.acqResp_excl_rel p t (hmem h (by simp))
        (hmem habs (by simp)),
      fun q w sq h => by
        rcases hnew h with h | h
        · exact hinv.writeReq_seq q w sq h
        · obtain ⟨-, -, -, rfl⟩ := h; rfl,
      fun p sq h => hinv.writeResp_seq p sq (hmem h (by simp)),
      fun p t sq h => hinv.writeResp_hw p t sq (hmem h (by simp)),
      fun p t h => hinv.releaseResp_bl p t (hmem h (by simp)),
      fun p t1 t2 h1 h2 => hinv.acqResp_unique p t1 t2
        (hmem h1 (by simp)) (hmem h2 (by simp)),
      fun p t => by simp [List.count_append, List.count_nil]; exact hinv.acqResp_count p t,
      fun p h => (hinv.holder_believes p h).imp id (fun ⟨t, ht⟩ => ⟨t, List.mem_append.mpr (.inl ht)⟩),
      fun q t h hrel => let ⟨t', ht'⟩ := hinv.holder_rel_acq q t h (hmem hrel (by simp));
        ⟨t', List.mem_append.mpr (.inl ht')⟩,
      fun p t => by simp [List.count_append, List.count_nil]; exact hinv.releaseResp_count p t,
      fun p t sq => by simp [List.count_append, List.count_nil]; exact hinv.writeResp_count p t sq,
      fun p t h => hinv.heartbeatReq_tok p t (hmem h (by simp)),
      fun p t h => hinv.heartbeatResp_eq p t (hmem h (by simp)),
      fun p t h => hinv.heartbeatResp_bl p t (hmem h (by simp)),
      fun p t => by simp [List.count_append, List.count_nil]; exact hinv.heartbeatResp_count p t,
      fun p t h tok hhb => hinv.acqResp_excl_hb p t (hmem h (by simp)) tok (hmem hhb (by simp))⟩
  | processWrite p v token seq =>
    simp only [msgLeaseSpec] at hgate htrans
    obtain ⟨hmem_w, hfence, htok_fresh⟩ := hgate; subst htrans
    -- Derived facts
    have htok_eq : s.myToken p = token := by
      have h1 := hinv.writeReq_tok p v token seq hmem_w
      have h2 := hinv.myToken_lt p; omega
    have hseq_eq : seq = s.writeSeq p + 1 :=
      hinv.writeReq_seq p v seq (htok_eq ▸ hmem_w)
    have hno_acq : ∀ t, Msg.acquireResp p t ∉ s.network := by
      intro t ht
      have h1 := hinv.acqResp_gt p t ht
      have h2 := hinv.acqResp_lt p t ht
      rw [htok_eq] at h1; omega
    have hno_wresp : ∀ t' sq, Msg.writeResp p t' sq ∉ s.network := by
      intro t' sq hs
      have heq := hinv.writeResp_eq p t' sq hs
      have hs' : Msg.writeResp p (s.myToken p) sq ∈ s.network := heq ▸ hs
      have hseq' := hinv.writeResp_seq p sq hs'
      have hhw := hinv.writeResp_hw p t' sq hs
      rw [heq, htok_eq, hseq'] at hhw
      have hseq_eq' := hinv.writeReq_seq p v seq (htok_eq ▸ hmem_w)
      omega
    -- Membership helpers
    have hsub : ∀ {m}, m ∈ s.network.erase (Msg.writeReq p v token seq) → m ∈ s.network :=
      fun h => List.erase_subset h
    have hnew : ∀ {m}, m ∈ s.network.erase (Msg.writeReq p v token seq) ++ [Msg.writeResp p token seq] →
        m ∈ s.network ∨ m = Msg.writeResp p token seq :=
      fun h => by rw [List.mem_append, List.mem_singleton] at h; exact h.imp hsub id
    exact ⟨hinv.myToken_lt,
      -- acqResp_lt
      fun q t h => by rcases hnew h with h | h; exact hinv.acqResp_lt q t h; exact absurd h (by simp),
      -- acqResp_gt
      fun q t h => by rcases hnew h with h | h; exact hinv.acqResp_gt q t h; exact absurd h (by simp),
      -- writeReq_tok
      fun q w t sq h => by rcases hnew h with h | h; exact hinv.writeReq_tok q w t sq h; exact absurd h (by simp),
      -- releaseReq_tok
      fun q t h => by rcases hnew h with h | h; exact hinv.releaseReq_tok q t h; exact absurd h (by simp),
      -- writeResp_eq: for old writeResps by hinv; for new writeResp p token seq: token = myToken p
      fun q t sq h => by
        rcases hnew h with h | h
        · exact hinv.writeResp_eq q t sq h
        · simp only [Msg.writeResp.injEq] at h; obtain ⟨rfl, rfl, -⟩ := h; exact htok_eq.symm,
      -- releaseResp_eq
      fun q t h => by rcases hnew h with h | h; exact hinv.releaseResp_eq q t h; exact absurd h (by simp),
      -- acqResp_excl_wr
      fun q t hacq seq hwr => by
        rcases hnew hacq with hacq_old | hacq_new
        · rcases hnew hwr with hwr_old | hwr_new
          · exact hinv.acqResp_excl_wr q t hacq_old seq hwr_old
          · simp only [Msg.writeResp.injEq] at hwr_new
            obtain ⟨rfl, rfl, -⟩ := hwr_new
            exact absurd hacq_old (hno_acq t)
        · exact absurd hacq_new (by simp),
      -- acqResp_excl_rel
      fun q t h habs => by
        rcases hnew h with h | h
        · rcases hnew habs with habs | habs
          · exact hinv.acqResp_excl_rel q t h habs
          · exact absurd habs (by simp)
        · exact absurd h (by simp),
      -- writeReq_seq
      fun q w sq h => by rcases hnew h with h | h; exact hinv.writeReq_seq q w sq h; exact absurd h (by simp),
      -- writeResp_seq: for old by hinv; for new writeResp p token seq: token = myToken p, seq = writeSeq p + 1
      fun q sq h => by
        rcases hnew h with h | h
        · exact hinv.writeResp_seq q sq h
        · simp only [Msg.writeResp.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact hseq_eq,
      -- writeResp_hw: highToken := token, highSeq := seq
      fun q t sq h => by
        show token > t ∨ (token = t ∧ seq ≥ sq)
        rcases hnew h with h | h
        · -- old writeResp: combine old hw bound with fence condition
          have hold := hinv.writeResp_hw q t sq h
          rcases hfence with hf | ⟨hf1, hf2⟩
          · rcases hold with hold | ⟨hold1, hold2⟩
            · left; omega
            · left; omega
          · rcases hold with hold | ⟨hold1, hold2⟩
            · left; omega
            · right; constructor <;> omega
        · -- new writeResp p token seq: need token > token ∨ (token = token ∧ seq ≥ seq)
          simp only [Msg.writeResp.injEq] at h; obtain ⟨-, rfl, rfl⟩ := h
          right; exact ⟨rfl, Nat.le_refl _⟩,
      -- releaseResp_bl
      fun q t h => by rcases hnew h with h | h; exact hinv.releaseResp_bl q t h; exact absurd h (by simp),
      -- acqResp_unique
      fun q t1 t2 h1 h2 => by
        rcases hnew h1 with h1 | h1 <;> rcases hnew h2 with h2 | h2
        · exact hinv.acqResp_unique q t1 t2 h1 h2
        · exact absurd h2 (by simp)
        · exact absurd h1 (by simp)
        · exact absurd h1 (by simp),
      -- acqResp_count
      fun q t => by
        show List.count (Msg.acquireResp q t)
          (s.network.erase (Msg.writeReq p v token seq) ++ [Msg.writeResp p token seq]) ≤ 1
        rw [List.count_append, count_singleton_ne _ _ (by simp), Nat.add_zero,
            List.count_erase_of_ne (show Msg.acquireResp q t ≠ Msg.writeReq p v token seq by simp)]
        exact hinv.acqResp_count q t,
      -- holder_believes: lockHolder unchanged
      fun q hhold => (hinv.holder_believes q hhold).imp id (fun ⟨t, ht⟩ =>
        ⟨t, List.mem_append.mpr (.inl (List.mem_erase_of_ne (show Msg.acquireResp q t ≠ Msg.writeReq p v token seq by simp) |>.mpr ht))⟩),
      -- holder_rel_acq: lockHolder unchanged
      fun q t hhold hrel => by
        rcases hnew hrel with hrel | hrel
        · obtain ⟨t', ht'⟩ := hinv.holder_rel_acq q t hhold hrel
          exact ⟨t', List.mem_append.mpr (.inl (List.mem_erase_of_ne (by simp) |>.mpr ht'))⟩
        · exact absurd hrel (by simp),
      -- releaseResp_count
      fun q t => by
        show List.count (Msg.releaseResp q t)
          (s.network.erase (Msg.writeReq p v token seq) ++ [Msg.writeResp p token seq]) ≤ 1
        rw [List.count_append, count_singleton_ne _ _ (by simp), Nat.add_zero,
            List.count_erase_of_ne (show Msg.releaseResp q t ≠ Msg.writeReq p v token seq by simp)]
        exact hinv.releaseResp_count q t,
      -- writeResp_count
      fun q t' sq => by
        show List.count (Msg.writeResp q t' sq)
          (s.network.erase (Msg.writeReq p v token seq) ++ [Msg.writeResp p token seq]) ≤ 1
        by_cases hqts : Msg.writeResp q t' sq = Msg.writeResp p token seq
        · rw [hqts, List.count_append, List.count_erase_of_ne (by simp), List.count_singleton_self]
          have : List.count (Msg.writeResp p token seq) s.network = 0 :=
            List.count_eq_zero.mpr (hno_wresp token seq)
          omega
        · rw [List.count_append, count_singleton_ne _ _ hqts, Nat.add_zero,
              List.count_erase_of_ne (show Msg.writeResp q t' sq ≠ Msg.writeReq p v token seq by simp)]
          exact hinv.writeResp_count q t' sq,
      -- heartbeatReq_tok: erase+append writeResp; heartbeatReq passes through
      fun q t h => by rcases hnew h with h | h; exact hinv.heartbeatReq_tok q t h; exact absurd h (by simp),
      -- heartbeatResp_eq: heartbeatResp passes through
      fun q t h => by rcases hnew h with h | h; exact hinv.heartbeatResp_eq q t h; exact absurd h (by simp),
      -- heartbeatResp_bl: heartbeatResp passes through
      fun q t h => by rcases hnew h with h | h; exact hinv.heartbeatResp_bl q t h; exact absurd h (by simp),
      -- heartbeatResp_count: erase writeReq, append writeResp; heartbeatResp unchanged
      fun q t => by
        show List.count (Msg.heartbeatResp q t)
          (s.network.erase (Msg.writeReq p v token seq) ++ [Msg.writeResp p token seq]) ≤ 1
        rw [List.count_append, count_singleton_ne _ _ (by simp), Nat.add_zero,
            List.count_erase_of_ne (show Msg.heartbeatResp q t ≠ Msg.writeReq p v token seq by simp)]
        exact hinv.heartbeatResp_count q t,
      -- acqResp_excl_hb: passes through (erase writeReq, append writeResp; acquireResp unaffected)
      fun q t h tok hhb => by
        rcases hnew h with h | h
        · rcases hnew hhb with hhb | hhb
          · exact hinv.acqResp_excl_hb q t h tok hhb
          · exact absurd hhb (by simp)
        · exact absurd h (by simp)⟩
  | recvWriteResp p token seq =>
    simp only [msgLeaseSpec] at hgate htrans; subst htrans
    obtain ⟨hmem, htok⟩ := hgate
    have hseq : seq = s.writeSeq p + 1 := hinv.writeResp_seq p seq (htok ▸ hmem)
    -- Forward membership: m ∈ new network → m ∈ s.network
    have hsub : ∀ m, m ∈ (s.network.erase (Msg.writeResp p token seq)).filter
        (fun m => match m with | .writeReq q _ t _ => decide (q ≠ p ∨ t ≠ token) | _ => true) →
        m ∈ s.network :=
      fun _m hm => List.erase_subset (List.mem_filter.mp hm).1
    -- acquireResp passes through filter (not a writeReq, different from erased writeResp)
    have hput_acq : ∀ q t, Msg.acquireResp q t ∈ s.network →
        Msg.acquireResp q t ∈ (s.network.erase (Msg.writeResp p token seq)).filter
          (fun m => match m with | .writeReq q _ t _ => decide (q ≠ p ∨ t ≠ token) | _ => true) :=
      fun q t hm => List.mem_filter.mpr ⟨(List.mem_erase_of_ne (by simp)).mpr hm, rfl⟩
    -- No writeReq for (p, token) survives the filter
    have hno_wreq_pt : ∀ v' s', Msg.writeReq p v' token s' ∉
        (s.network.erase (Msg.writeResp p token seq)).filter
          (fun m => match m with | .writeReq q _ t _ => decide (q ≠ p ∨ t ≠ token) | _ => true) := by
      intro v' s' hm
      have hf := (List.mem_filter.mp hm).2
      simp at hf
    -- No writeResp p token _ survives erase+filter (count argument)
    have hno_wresp_pt : ∀ sq, Msg.writeResp p token sq ∉
        (s.network.erase (Msg.writeResp p token seq)).filter
          (fun m => match m with | .writeReq q _ t _ => decide (q ≠ p ∨ t ≠ token) | _ => true) := by
      intro sq hm
      have hmem' := hsub _ hm
      have heq := hinv.writeResp_eq p token sq hmem'
      have hseq' := hinv.writeResp_seq p sq (heq ▸ hmem')
      -- hseq' : sq = s.writeSeq p + 1, hseq : seq = s.writeSeq p + 1
      -- So sq = seq. But writeResp p token seq was erased from network, and count ≤ 1 in old.
      have hsqeq : sq = seq := by omega
      have hm_er := (List.mem_filter.mp hm).1
      rw [hsqeq] at hm_er
      have hc := List.count_erase_self (a := Msg.writeResp p token seq) (l := s.network)
      have hcold := hinv.writeResp_count p token seq
      have hmem_old : Msg.writeResp p token seq ∈ s.network := hmem
      have hcpos : List.count (Msg.writeResp p token seq) s.network ≥ 1 :=
        List.count_pos_iff.mpr hmem_old
      have : List.count (Msg.writeResp p token seq) (s.network.erase (Msg.writeResp p token seq)) = 0 := by omega
      rw [List.count_eq_zero] at this
      exact absurd hm_er (this)
    exact ⟨hinv.myToken_lt,
      -- acqResp_lt
      fun q t hm => hinv.acqResp_lt q t (hsub _ hm),
      -- acqResp_gt
      fun q t hm => hinv.acqResp_gt q t (hsub _ hm),
      -- writeReq_tok
      fun q v' t sq hm => hinv.writeReq_tok q v' t sq (hsub _ hm),
      -- releaseReq_tok
      fun q t hm => hinv.releaseReq_tok q t (hsub _ hm),
      -- writeResp_eq
      fun q t sq hm => hinv.writeResp_eq q t sq (hsub _ hm),
      -- releaseResp_eq
      fun q t hm => hinv.releaseResp_eq q t (hsub _ hm),
      -- acqResp_excl_wr: acquireResp in net' → in old; writeResp in net' → in old
      fun q t hacq sq hwr => hinv.acqResp_excl_wr q t (hsub _ hacq) sq (hsub _ hwr),
      -- acqResp_excl_rel
      fun q t hacq hrel => hinv.acqResp_excl_rel q t (hsub _ hacq) (hsub _ hrel),
      -- writeReq_seq
      fun q v' sq hm => by
        simp only
        by_cases hqp : q = p
        · subst hqp
          -- writeReq p v' (myToken p) sq ∈ net'. myToken p = token (by htok).
          -- But filter removes all writeReqs for (p, token). Contradiction.
          rw [htok] at hm; exact absurd hm (hno_wreq_pt v' sq)
        · simp [hqp]; exact hinv.writeReq_seq q v' sq (hsub _ hm),
      -- writeResp_seq
      fun q sq hm => by
        simp only
        by_cases hqp : q = p
        · subst hqp
          -- writeResp p (myToken p) sq ∈ net'. myToken p = token.
          -- But no writeResp p token _ survives. Contradiction.
          rw [htok] at hm; exact absurd hm (hno_wresp_pt sq)
        · simp [hqp]; exact hinv.writeResp_seq q sq (hsub _ hm),
      -- writeResp_hw
      fun q t sq hm => hinv.writeResp_hw q t sq (hsub _ hm),
      -- releaseResp_bl
      fun q t hm => hinv.releaseResp_bl q t (hsub _ hm),
      -- acqResp_unique
      fun q t1 t2 h1 h2 => hinv.acqResp_unique q t1 t2 (hsub _ h1) (hsub _ h2),
      -- acqResp_count
      fun q t => by
        apply Nat.le_trans (count_filter_le _ _ _)
        rw [List.count_erase_of_ne (show Msg.acquireResp q t ≠ Msg.writeResp p token seq by simp)]
        exact hinv.acqResp_count q t,
      -- holder_believes
      fun q hhold => (hinv.holder_believes q hhold).imp id (fun ⟨t, ht⟩ => ⟨t, hput_acq q t ht⟩),
      -- holder_rel_acq
      fun q t hhold hrel => by
        obtain ⟨t', ht'⟩ := hinv.holder_rel_acq q t hhold (hsub _ hrel)
        exact ⟨t', hput_acq q t' ht'⟩,
      -- releaseResp_count
      fun q t => by
        apply Nat.le_trans (count_filter_le _ _ _)
        rw [List.count_erase_of_ne (show Msg.releaseResp q t ≠ Msg.writeResp p token seq by simp)]
        exact hinv.releaseResp_count q t,
      -- writeResp_count
      fun q t' sq => by
        apply Nat.le_trans (count_filter_le _ _ _)
        by_cases hqts : Msg.writeResp q t' sq = Msg.writeResp p token seq
        · rw [hqts, List.count_erase_self]; have := hinv.writeResp_count p token seq; omega
        · rw [List.count_erase_of_ne hqts]; exact hinv.writeResp_count q t' sq,
      -- heartbeatReq_tok: heartbeatReq passes erase+filter (not writeReq/writeResp)
      fun q t hm => hinv.heartbeatReq_tok q t (hsub _ hm),
      -- heartbeatResp_eq: heartbeatResp passes through
      fun q t hm => hinv.heartbeatResp_eq q t (hsub _ hm),
      -- heartbeatResp_bl: heartbeatResp passes through
      fun q t hm => hinv.heartbeatResp_bl q t (hsub _ hm),
      -- heartbeatResp_count: erase+filter can only decrease
      fun q t => by
        apply Nat.le_trans (count_filter_le _ _ _)
        rw [List.count_erase_of_ne (show Msg.heartbeatResp q t ≠ Msg.writeResp p token seq by simp)]
        exact hinv.heartbeatResp_count q t,
      -- acqResp_excl_hb: passes through (erase writeResp, filter writeReqs)
      fun q t h tok hhb => hinv.acqResp_excl_hb q t (hsub _ h) tok (hsub _ hhb)⟩
  | sendReleaseReq p =>
    simp only [msgLeaseSpec] at hgate htrans; subst htrans
    have hmem : ∀ {m}, m ∈ s.network ++ [Msg.releaseReq p (s.myToken p)] →
        m ≠ Msg.releaseReq p (s.myToken p) → m ∈ s.network :=
      fun h hne => (List.mem_append.mp h).elim id (fun h => absurd (List.mem_singleton.mp h) hne)
    have hnew : ∀ {m}, m ∈ s.network ++ [Msg.releaseReq p (s.myToken p)] →
        m ∈ s.network ∨ m = Msg.releaseReq p (s.myToken p) :=
      fun h => List.mem_append.mp h |>.imp id (List.mem_singleton.mp)
    exact ⟨hinv.myToken_lt,
      fun p t h => hinv.acqResp_lt p t (hmem h (by simp)),
      fun p t h => hinv.acqResp_gt p t (hmem h (by simp)),
      fun p v t sq h => hinv.writeReq_tok p v t sq (hmem h (by simp)),
      fun q t h => by
        rcases hnew h with h | h
        · exact hinv.releaseReq_tok q t h
        · obtain ⟨rfl, rfl⟩ := h; exact Nat.le_refl _,
      fun p t sq h => hinv.writeResp_eq p t sq (hmem h (by simp)),
      fun p t h => hinv.releaseResp_eq p t (hmem h (by simp)),
      fun p t h seq habs => hinv.acqResp_excl_wr p t (hmem h (by simp)) seq
        (hmem habs (by simp)),
      fun p t h habs => hinv.acqResp_excl_rel p t (hmem h (by simp))
        (hmem habs (by simp)),
      fun p v sq h => hinv.writeReq_seq p v sq (hmem h (by simp)),
      fun p sq h => hinv.writeResp_seq p sq (hmem h (by simp)),
      fun p t sq h => hinv.writeResp_hw p t sq (hmem h (by simp)),
      fun p t h => hinv.releaseResp_bl p t (hmem h (by simp)),
      fun p t1 t2 h1 h2 => hinv.acqResp_unique p t1 t2
        (hmem h1 (by simp)) (hmem h2 (by simp)),
      fun p t => by simp [List.count_append, List.count_nil]; exact hinv.acqResp_count p t,
      fun p h => (hinv.holder_believes p h).imp id (fun ⟨t, ht⟩ => ⟨t, List.mem_append.mpr (.inl ht)⟩),
      fun q t h hrel => let ⟨t', ht'⟩ := hinv.holder_rel_acq q t h (hmem hrel (by simp));
        ⟨t', List.mem_append.mpr (.inl ht')⟩,
      fun p t => by simp [List.count_append, List.count_nil]; exact hinv.releaseResp_count p t,
      fun p t sq => by simp [List.count_append, List.count_nil]; exact hinv.writeResp_count p t sq,
      fun p t h => hinv.heartbeatReq_tok p t (hmem h (by simp)),
      fun p t h => hinv.heartbeatResp_eq p t (hmem h (by simp)),
      fun p t h => hinv.heartbeatResp_bl p t (hmem h (by simp)),
      fun p t => by simp [List.count_append, List.count_nil]; exact hinv.heartbeatResp_count p t,
      fun p t h tok hhb => hinv.acqResp_excl_hb p t (hmem h (by simp)) tok (hmem hhb (by simp))⟩
  | processRelease p token =>
    simp only [msgLeaseSpec] at hgate htrans
    obtain ⟨hmem_r, hhold, hactive, htok_fresh⟩ := hgate; subst htrans
    -- Derived facts
    have htok_eq : s.myToken p = token := by
      have h1 := hinv.releaseReq_tok p token hmem_r
      have h2 := hinv.myToken_lt p; omega
    have hno_acq : ∀ t, Msg.acquireResp p t ∉ s.network := by
      intro t ht
      have h1 := hinv.acqResp_gt p t ht
      have h2 := hinv.acqResp_lt p t ht
      rw [htok_eq] at h1; omega
    -- Membership helpers
    have hsub : ∀ {m}, m ∈ s.network.erase (Msg.releaseReq p token) → m ∈ s.network :=
      fun h => List.erase_subset h
    have hnew : ∀ {m}, m ∈ s.network.erase (Msg.releaseReq p token) ++ [Msg.releaseResp p token] →
        m ∈ s.network ∨ m = Msg.releaseResp p token :=
      fun h => by rw [List.mem_append, List.mem_singleton] at h; exact h.imp hsub id
    -- No releaseResp p token in old network: if it were, acqResp_excl_rel + holder_rel_acq would conflict
    -- Actually, we need to show releaseResp p token wasn't already there.
    -- From releaseResp_eq: any releaseResp p t has t = myToken p = token.
    -- From holder_rel_acq: lockHolder = some p ∧ releaseResp p token ∈ network → acquireResp p t' ∈ network.
    -- But we showed no acquireResp for p. So releaseResp p token ∉ network.
    have hno_relresp_p : ∀ t', Msg.releaseResp p t' ∉ s.network := by
      intro t' ht'
      have heq := hinv.releaseResp_eq p t' ht'
      have : t' = token := by omega
      subst this
      have ⟨t'', ht''⟩ := hinv.holder_rel_acq p t' hhold ht'
      exact hno_acq t'' ht''
    -- believesLeader p = true (for releaseResp_bl on the new msg)
    have hbl : s.believesLeader p = true := by
      rcases hinv.holder_believes p hhold with hbl | ⟨t, ht⟩
      · exact hbl
      · exact absurd ht (hno_acq t)
    exact ⟨hinv.myToken_lt,
      fun q t h => by rcases hnew h with h | h; exact hinv.acqResp_lt q t h; exact absurd h (by simp),
      fun q t h => by rcases hnew h with h | h; exact hinv.acqResp_gt q t h; exact absurd h (by simp),
      fun q v t sq h => by rcases hnew h with h | h; exact hinv.writeReq_tok q v t sq h; exact absurd h (by simp),
      fun q t h => by rcases hnew h with h | h; exact hinv.releaseReq_tok q t h; exact absurd h (by simp),
      fun q t sq h => by rcases hnew h with h | h; exact hinv.writeResp_eq q t sq h; exact absurd h (by simp),
      -- releaseResp_eq: for new msg, token = myToken p
      fun q t h => by
        rcases hnew h with h | h
        · exact hinv.releaseResp_eq q t h
        · simp only [Msg.releaseResp.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact htok_eq.symm,
      -- acqResp_excl_wr
      fun q t h seq habs => by
        rcases hnew h with h | h
        · rcases hnew habs with habs | habs
          · exact hinv.acqResp_excl_wr q t h seq habs
          · exact absurd habs (by simp)
        · exact absurd h (by simp),
      -- acqResp_excl_rel
      fun q t h habs => by
        rcases hnew h with h | h
        · rcases hnew habs with habs | habs
          · exact hinv.acqResp_excl_rel q t h habs
          · simp only [Msg.releaseResp.injEq] at habs
            exact absurd (habs.1 ▸ h) (hno_acq t)
        · exact absurd h (by simp),
      -- writeReq_seq
      fun q v sq h => by rcases hnew h with h | h; exact hinv.writeReq_seq q v sq h; exact absurd h (by simp),
      -- writeResp_seq
      fun q sq h => by rcases hnew h with h | h; exact hinv.writeResp_seq q sq h; exact absurd h (by simp),
      -- writeResp_hw
      fun q t sq h => by rcases hnew h with h | h; exact hinv.writeResp_hw q t sq h; exact absurd h (by simp),
      -- releaseResp_bl
      fun q t h => by
        rcases hnew h with h | h
        · exact hinv.releaseResp_bl q t h
        · simp only [Msg.releaseResp.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact hbl,
      -- acqResp_unique
      fun q t1 t2 h1 h2 => by
        rcases hnew h1 with h1 | h1 <;> rcases hnew h2 with h2 | h2
        · exact hinv.acqResp_unique q t1 t2 h1 h2
        · exact absurd h2 (by simp)
        · exact absurd h1 (by simp)
        · exact absurd h1 (by simp),
      -- acqResp_count
      fun q t => by
        show List.count (Msg.acquireResp q t)
          (s.network.erase (Msg.releaseReq p token) ++ [Msg.releaseResp p token]) ≤ 1
        have hne : Msg.acquireResp q t ≠ Msg.releaseResp p token := by simp
        rw [List.count_append, count_singleton_ne _ _ hne, Nat.add_zero,
            List.count_erase_of_ne (show Msg.acquireResp q t ≠ Msg.releaseReq p token by simp)]
        exact hinv.acqResp_count q t,
      -- holder_believes: lockHolder = none in post-state, so vacuous
      fun q h => by exact absurd h (show none ≠ some q by simp),
      -- holder_rel_acq: lockHolder = none in post-state, so vacuous
      fun q t h _ => by exact absurd h (show none ≠ some q by simp),
      -- releaseResp_count
      fun q t => by
        show List.count (Msg.releaseResp q t)
          (s.network.erase (Msg.releaseReq p token) ++ [Msg.releaseResp p token]) ≤ 1
        by_cases hqt : Msg.releaseResp q t = Msg.releaseResp p token
        · rw [hqt, List.count_append, List.count_erase_of_ne (by simp), List.count_singleton_self]
          have : List.count (Msg.releaseResp p token) s.network = 0 :=
            List.count_eq_zero.mpr (hno_relresp_p token)
          omega
        · rw [List.count_append, count_singleton_ne _ _ hqt, Nat.add_zero,
              List.count_erase_of_ne (show Msg.releaseResp q t ≠ Msg.releaseReq p token by simp)]
          exact hinv.releaseResp_count q t,
      -- writeResp_count
      fun q t sq => by
        show List.count (Msg.writeResp q t sq)
          (s.network.erase (Msg.releaseReq p token) ++ [Msg.releaseResp p token]) ≤ 1
        rw [List.count_append, count_singleton_ne _ _ (by simp), Nat.add_zero,
            List.count_erase_of_ne (show Msg.writeResp q t sq ≠ Msg.releaseReq p token by simp)]
        exact hinv.writeResp_count q t sq,
      -- heartbeatReq_tok: heartbeatReq passes erase+append (not releaseReq/releaseResp)
      fun q t h => by rcases hnew h with h | h; exact hinv.heartbeatReq_tok q t h; exact absurd h (by simp),
      -- heartbeatResp_eq: heartbeatResp passes through
      fun q t h => by rcases hnew h with h | h; exact hinv.heartbeatResp_eq q t h; exact absurd h (by simp),
      -- heartbeatResp_bl: heartbeatResp passes through
      fun q t h => by rcases hnew h with h | h; exact hinv.heartbeatResp_bl q t h; exact absurd h (by simp),
      -- heartbeatResp_count: erase releaseReq, append releaseResp; heartbeatResp unchanged
      fun q t => by
        show List.count (Msg.heartbeatResp q t)
          (s.network.erase (Msg.releaseReq p token) ++ [Msg.releaseResp p token]) ≤ 1
        rw [List.count_append, count_singleton_ne _ _ (by simp), Nat.add_zero,
            List.count_erase_of_ne (show Msg.heartbeatResp q t ≠ Msg.releaseReq p token by simp)]
        exact hinv.heartbeatResp_count q t,
      -- acqResp_excl_hb: lockHolder = none post-state, vacuous via hno_acq (no acqResp for p);
      -- for q ≠ p, passes through erase+append
      fun q t h tok hhb => by
        rcases hnew h with h | h
        · rcases hnew hhb with hhb | hhb
          · exact hinv.acqResp_excl_hb q t h tok hhb
          · exact absurd hhb (by simp)
        · exact absurd h (by simp)⟩
  | recvReleaseResp p token =>
    simp only [msgLeaseSpec] at hgate htrans; subst htrans
    obtain ⟨hmem_rel, htok, hno_hbresp⟩ := hgate
    have hsub : ∀ {m}, m ∈ s.network.erase (Msg.releaseResp p token) → m ∈ s.network :=
      fun h => List.erase_subset h
    have hne_acq : ∀ q t, Msg.acquireResp q t ≠ Msg.releaseResp p token := by
      intros; simp
    have hne_wr : ∀ q t sq, Msg.writeResp q t sq ≠ Msg.releaseResp p token := by
      intros; simp
    -- For releaseResp_bl: any releaseResp q t still in erased network with q = p
    -- has t = myToken p = token by releaseResp_eq. But we erased releaseResp p token
    -- and count ≤ 1, so no releaseResp p token remains. Contradiction.
    have hno_rel_p : ∀ t', Msg.releaseResp p t' ∉ s.network.erase (Msg.releaseResp p token) := by
      intro t' h
      have hmem_old := hsub h
      have heq := hinv.releaseResp_eq p t' hmem_old
      -- heq : t' = s.myToken p, htok : s.myToken p = token, so t' = token
      have ht_eq : t' = token := by omega
      subst ht_eq
      -- Now: releaseResp p token ∈ s.network.erase (releaseResp p token)
      -- But count ≤ 1 in original, so after erase count = 0.
      have hcnt := hinv.releaseResp_count p t'
      have hcnt_erase : List.count (Msg.releaseResp p t') (s.network.erase (Msg.releaseResp p t')) = 0 := by
        rw [List.count_erase_self]; omega
      exact absurd (List.count_pos_iff.mpr h) (by omega)
    exact ⟨hinv.myToken_lt,
      fun q t h => hinv.acqResp_lt q t (hsub h),
      fun q t h => hinv.acqResp_gt q t (hsub h),
      fun q v t sq h => hinv.writeReq_tok q v t sq (hsub h),
      fun q t h => hinv.releaseReq_tok q t (hsub h),
      fun q t sq h => hinv.writeResp_eq q t sq (hsub h),
      fun q t h => hinv.releaseResp_eq q t (hsub h),
      fun q t h seq habs => hinv.acqResp_excl_wr q t (hsub h) seq (hsub habs),
      fun q t h habs => hinv.acqResp_excl_rel q t (hsub h) (hsub habs),
      fun q v sq h => hinv.writeReq_seq q v sq (hsub h),
      fun q sq h => hinv.writeResp_seq q sq (hsub h),
      fun q t sq h => hinv.writeResp_hw q t sq (hsub h),
      -- releaseResp_bl
      fun q t h => by
        by_cases hqp : q = p
        · subst hqp; exact absurd h (hno_rel_p t)
        · simp [hqp]; exact hinv.releaseResp_bl q t (hsub h),
      fun q t1 t2 h1 h2 => hinv.acqResp_unique q t1 t2 (hsub h1) (hsub h2),
      fun q t => by
        rw [List.count_erase_of_ne (hne_acq q t)]; exact hinv.acqResp_count q t,
      -- holder_believes
      fun q h => by
        dsimp only []
        by_cases hqp : q = p
        · subst hqp; simp
          have hlock : s.lockHolder = some q := h
          exact hinv.holder_rel_acq q token hlock hmem_rel
        · simp [hqp]
          have hlock : s.lockHolder = some q := h
          rcases hinv.holder_believes q hlock with hbl | ⟨t, ht⟩
          · exact Or.inl hbl
          · exact Or.inr ⟨t, ht⟩,
      -- holder_rel_acq
      fun q t h hrel => by
        dsimp only []
        by_cases hqp : q = p
        · subst hqp; exact absurd hrel (hno_rel_p t)
        · have hrel_old := hsub hrel
          have ⟨t', ht'⟩ := hinv.holder_rel_acq q t h hrel_old
          exact ⟨t', (List.mem_erase_of_ne (hne_acq q t')).mpr ht'⟩,
      fun q t => by
        dsimp only []
        by_cases hqt : Msg.releaseResp q t = Msg.releaseResp p token
        · rw [hqt, List.count_erase_self]
          have := hinv.releaseResp_count p token; omega
        · rw [List.count_erase_of_ne hqt]; exact hinv.releaseResp_count q t,
      fun q t sq => by
        rw [List.count_erase_of_ne (hne_wr q t sq)]; exact hinv.writeResp_count q t sq,
      -- heartbeatReq_tok: heartbeatReq passes erase (erase releaseResp, which ≠ heartbeatReq)
      fun q t h => hinv.heartbeatReq_tok q t (hsub h),
      -- heartbeatResp_eq: heartbeatResp passes through
      fun q t h => hinv.heartbeatResp_eq q t (hsub h),
      -- heartbeatResp_bl: q = p vacuous by hno_hbresp gate; q ≠ p unchanged
      fun q t h => by
        show (if q = p then false else s.believesLeader q) = true
        by_cases hqp : q = p
        · subst hqp; exact absurd (hsub h) (hno_hbresp t)
        · simp [hqp]; exact hinv.heartbeatResp_bl q t (hsub h),
      -- heartbeatResp_count: erase releaseResp; heartbeatResp unchanged
      fun q t => by
        rw [List.count_erase_of_ne (show Msg.heartbeatResp q t ≠ Msg.releaseResp p token by simp)]
        exact hinv.heartbeatResp_count q t,
      -- acqResp_excl_hb: erase releaseResp; acquireResp and heartbeatResp pass through
      fun q t h tok hhb => hinv.acqResp_excl_hb q t (hsub h) tok (hsub hhb)⟩
  | dropMsg msg =>
    simp only [msgLeaseSpec] at hgate htrans; obtain ⟨hmem, hreq⟩ := hgate; subst htrans
    have hsub : ∀ {m}, m ∈ s.network.erase msg → m ∈ s.network :=
      fun h => List.erase_subset h
    have hne_resp : ∀ {m : Msg n}, m.isRequest = false → m ≠ msg :=
      fun hf heq => by rw [heq] at hf; simp [hreq] at hf
    exact ⟨hinv.myToken_lt,
      fun p t h => hinv.acqResp_lt p t (hsub h),
      fun p t h => hinv.acqResp_gt p t (hsub h),
      fun p v t sq h => hinv.writeReq_tok p v t sq (hsub h),
      fun p t h => hinv.releaseReq_tok p t (hsub h),
      fun p t sq h => hinv.writeResp_eq p t sq (hsub h),
      fun p t h => hinv.releaseResp_eq p t (hsub h),
      fun p t h seq habs => hinv.acqResp_excl_wr p t (hsub h) seq (hsub habs),
      fun p t h habs => hinv.acqResp_excl_rel p t (hsub h) (hsub habs),
      fun p v sq h => hinv.writeReq_seq p v sq (hsub h),
      fun p sq h => hinv.writeResp_seq p sq (hsub h),
      fun p t sq h => hinv.writeResp_hw p t sq (hsub h),
      fun p t h => hinv.releaseResp_bl p t (hsub h),
      fun p t1 t2 h1 h2 => hinv.acqResp_unique p t1 t2 (hsub h1) (hsub h2),
      fun p t => by rw [List.count_erase_of_ne (hne_resp (by simp [Msg.isRequest]))]; exact hinv.acqResp_count p t,
      fun p h => by
        rcases hinv.holder_believes p h with hb | ⟨t, ht⟩
        · exact Or.inl hb
        · right; exact ⟨t, (List.mem_erase_of_ne (hne_resp (by simp [Msg.isRequest]))).mpr ht⟩,
      fun q t h hrel => by
        have hrel_old := hsub hrel
        have ⟨t', ht'⟩ := hinv.holder_rel_acq q t h hrel_old
        exact ⟨t', (List.mem_erase_of_ne (hne_resp (by simp [Msg.isRequest]))).mpr ht'⟩,
      fun p t => by rw [List.count_erase_of_ne (hne_resp (by simp [Msg.isRequest]))]; exact hinv.releaseResp_count p t,
      fun p t sq => by rw [List.count_erase_of_ne (hne_resp (by simp [Msg.isRequest]))]; exact hinv.writeResp_count p t sq,
      -- heartbeatReq_tok: heartbeatReq is a request, so msg might = heartbeatReq; erase decreases
      fun p t h => hinv.heartbeatReq_tok p t (hsub h),
      -- heartbeatResp_eq: heartbeatResp is NOT a request, so msg ≠ heartbeatResp
      fun p t h => hinv.heartbeatResp_eq p t (hsub h),
      -- heartbeatResp_bl: same
      fun p t h => hinv.heartbeatResp_bl p t (hsub h),
      -- heartbeatResp_count: msg is a request so msg ≠ heartbeatResp
      fun p t => by rw [List.count_erase_of_ne (hne_resp (by simp [Msg.isRequest]))]; exact hinv.heartbeatResp_count p t,
      -- acqResp_excl_hb: erase request; acquireResp and heartbeatResp pass through
      fun p t h tok hhb => hinv.acqResp_excl_hb p t (hsub h) tok (hsub hhb)⟩
  -- ── New heartbeat actions ──────────────────────────────────────────
  | sendHeartbeatReq p =>
    -- Appends heartbeatReq p (myToken p). All existing invariants preserved since
    -- heartbeatReq is a request message and everything else is unchanged.
    simp only [msgLeaseSpec] at hgate htrans; subst htrans
    have hmem : ∀ {m}, m ∈ s.network ++ [Msg.heartbeatReq p (s.myToken p)] →
        m ≠ Msg.heartbeatReq p (s.myToken p) → m ∈ s.network :=
      fun h hne => (List.mem_append.mp h).elim id (fun h => absurd (List.mem_singleton.mp h) hne)
    have hnew : ∀ {m}, m ∈ s.network ++ [Msg.heartbeatReq p (s.myToken p)] →
        m ∈ s.network ∨ m = Msg.heartbeatReq p (s.myToken p) :=
      fun h => List.mem_append.mp h |>.imp id (List.mem_singleton.mp)
    exact ⟨hinv.myToken_lt,
      fun q t h => hinv.acqResp_lt q t (hmem h (by simp)),
      fun q t h => hinv.acqResp_gt q t (hmem h (by simp)),
      fun q v t sq h => hinv.writeReq_tok q v t sq (hmem h (by simp)),
      fun q t h => hinv.releaseReq_tok q t (hmem h (by simp)),
      fun q t sq h => hinv.writeResp_eq q t sq (hmem h (by simp)),
      fun q t h => hinv.releaseResp_eq q t (hmem h (by simp)),
      fun q t h seq habs => hinv.acqResp_excl_wr q t (hmem h (by simp)) seq (hmem habs (by simp)),
      fun q t h habs => hinv.acqResp_excl_rel q t (hmem h (by simp)) (hmem habs (by simp)),
      fun q v sq h => hinv.writeReq_seq q v sq (hmem h (by simp)),
      fun q sq h => hinv.writeResp_seq q sq (hmem h (by simp)),
      fun q t sq h => hinv.writeResp_hw q t sq (hmem h (by simp)),
      fun q t h => hinv.releaseResp_bl q t (hmem h (by simp)),
      fun q t1 t2 h1 h2 => hinv.acqResp_unique q t1 t2 (hmem h1 (by simp)) (hmem h2 (by simp)),
      fun q t => by simp [List.count_append, List.count_nil]; exact hinv.acqResp_count q t,
      fun q h => (hinv.holder_believes q h).imp id (fun ⟨t, ht⟩ => ⟨t, List.mem_append.mpr (.inl ht)⟩),
      fun q t h hrel => let ⟨t', ht'⟩ := hinv.holder_rel_acq q t h (hmem hrel (by simp));
        ⟨t', List.mem_append.mpr (.inl ht')⟩,
      fun q t => by simp [List.count_append, List.count_nil]; exact hinv.releaseResp_count q t,
      fun q t sq => by simp [List.count_append, List.count_nil]; exact hinv.writeResp_count q t sq,
      -- heartbeatReq_tok: new heartbeatReq p (myToken p) satisfies tok ≤ myToken p (reflexivity)
      fun q t h => by
        rcases hnew h with h | h
        · exact hinv.heartbeatReq_tok q t h
        · obtain ⟨rfl, rfl⟩ := h; exact Nat.le_refl _,
      -- heartbeatResp_eq: no heartbeatResp added
      fun q t h => hinv.heartbeatResp_eq q t (hmem h (by simp)),
      -- heartbeatResp_bl: no heartbeatResp added
      fun q t h => hinv.heartbeatResp_bl q t (hmem h (by simp)),
      -- heartbeatResp_count: no heartbeatResp added
      fun q t => by simp [List.count_append, List.count_nil]; exact hinv.heartbeatResp_count q t,
      -- acqResp_excl_hb: no heartbeatResp added
      fun q t h tok hhb => hinv.acqResp_excl_hb q t (hmem h (by simp)) tok (hmem hhb (by simp))⟩
  | processHeartbeat p token =>
    -- Erases heartbeatReq p token, appends heartbeatResp p token.
    -- Gate ensures: lockHolder = some p, leaseActive = true, token + 1 = nextToken,
    --               ∀ t, acquireResp p t ∉ network.
    simp only [msgLeaseSpec] at hgate htrans
    obtain ⟨hmem_hr, hhold, hactive, htok_fresh, hno_acq_gate, hno_hbresp⟩ := hgate; subst htrans
    -- token = myToken p: from heartbeatReq_tok (token ≤ myToken p) and myToken_lt (myToken p < nextToken = token+1)
    have htok_eq : s.myToken p = token := by
      have h1 := hinv.heartbeatReq_tok p token hmem_hr
      have h2 := hinv.myToken_lt p; omega
    -- believesLeader p = true: from holder_believes + lockHolder = some p
    have hbl : s.believesLeader p = true := by
      rcases hinv.holder_believes p hhold with hbl | ⟨t, ht⟩
      · exact hbl
      · exact absurd ht (hno_acq_gate t)
    -- Membership helpers
    have hsub : ∀ {m}, m ∈ s.network.erase (Msg.heartbeatReq p token) → m ∈ s.network :=
      fun h => List.erase_subset h
    have hnew : ∀ {m}, m ∈ s.network.erase (Msg.heartbeatReq p token) ++ [Msg.heartbeatResp p token] →
        m ∈ s.network ∨ m = Msg.heartbeatResp p token :=
      fun h => by rw [List.mem_append, List.mem_singleton] at h; exact h.imp hsub id
    -- No heartbeatResp p token in old network? Not necessarily, but count ≤ 1.
    -- Actually heartbeatResp_count says count ≤ 1 in the new network too.
    exact ⟨hinv.myToken_lt,
      fun q t h => by rcases hnew h with h | h; exact hinv.acqResp_lt q t h; exact absurd h (by simp),
      fun q t h => by rcases hnew h with h | h; exact hinv.acqResp_gt q t h; exact absurd h (by simp),
      fun q v t sq h => by rcases hnew h with h | h; exact hinv.writeReq_tok q v t sq h; exact absurd h (by simp),
      fun q t h => by rcases hnew h with h | h; exact hinv.releaseReq_tok q t h; exact absurd h (by simp),
      fun q t sq h => by rcases hnew h with h | h; exact hinv.writeResp_eq q t sq h; exact absurd h (by simp),
      fun q t h => by rcases hnew h with h | h; exact hinv.releaseResp_eq q t h; exact absurd h (by simp),
      fun q t h seq habs => by
        rcases hnew h with h | h; rcases hnew habs with habs | habs
        · exact hinv.acqResp_excl_wr q t h seq habs
        · exact absurd habs (by simp)
        · exact absurd h (by simp),
      fun q t h habs => by
        rcases hnew h with h | h; rcases hnew habs with habs | habs
        · exact hinv.acqResp_excl_rel q t h habs
        · exact absurd habs (by simp)
        · exact absurd h (by simp),
      fun q v sq h => by rcases hnew h with h | h; exact hinv.writeReq_seq q v sq h; exact absurd h (by simp),
      fun q sq h => by rcases hnew h with h | h; exact hinv.writeResp_seq q sq h; exact absurd h (by simp),
      fun q t sq h => by rcases hnew h with h | h; exact hinv.writeResp_hw q t sq h; exact absurd h (by simp),
      fun q t h => by rcases hnew h with h | h; exact hinv.releaseResp_bl q t h; exact absurd h (by simp),
      fun q t1 t2 h1 h2 => by
        rcases hnew h1 with h1 | h1 <;> rcases hnew h2 with h2 | h2
        · exact hinv.acqResp_unique q t1 t2 h1 h2
        · exact absurd h2 (by simp)
        · exact absurd h1 (by simp)
        · exact absurd h1 (by simp),
      -- acqResp_count
      fun q t => by
        show List.count (Msg.acquireResp q t)
          (s.network.erase (Msg.heartbeatReq p token) ++ [Msg.heartbeatResp p token]) ≤ 1
        rw [List.count_append, count_singleton_ne _ _ (by simp), Nat.add_zero,
            List.count_erase_of_ne (show Msg.acquireResp q t ≠ Msg.heartbeatReq p token by simp)]
        exact hinv.acqResp_count q t,
      -- holder_believes: lockHolder unchanged
      fun q hhold' => (hinv.holder_believes q hhold').imp id (fun ⟨t, ht⟩ =>
        ⟨t, List.mem_append.mpr (.inl (List.mem_erase_of_ne (show Msg.acquireResp q t ≠ Msg.heartbeatReq p token by simp) |>.mpr ht))⟩),
      -- holder_rel_acq: lockHolder unchanged
      fun q t hhold' hrel => by
        rcases hnew hrel with hrel | hrel
        · obtain ⟨t', ht'⟩ := hinv.holder_rel_acq q t hhold' hrel
          exact ⟨t', List.mem_append.mpr (.inl (List.mem_erase_of_ne (by simp) |>.mpr ht'))⟩
        · exact absurd hrel (by simp),
      -- releaseResp_count
      fun q t => by
        show List.count (Msg.releaseResp q t)
          (s.network.erase (Msg.heartbeatReq p token) ++ [Msg.heartbeatResp p token]) ≤ 1
        rw [List.count_append, count_singleton_ne _ _ (by simp), Nat.add_zero,
            List.count_erase_of_ne (show Msg.releaseResp q t ≠ Msg.heartbeatReq p token by simp)]
        exact hinv.releaseResp_count q t,
      -- writeResp_count
      fun q t sq => by
        show List.count (Msg.writeResp q t sq)
          (s.network.erase (Msg.heartbeatReq p token) ++ [Msg.heartbeatResp p token]) ≤ 1
        rw [List.count_append, count_singleton_ne _ _ (by simp), Nat.add_zero,
            List.count_erase_of_ne (show Msg.writeResp q t sq ≠ Msg.heartbeatReq p token by simp)]
        exact hinv.writeResp_count q t sq,
      -- heartbeatReq_tok: heartbeatReq q t in new net. The erased heartbeatReq p token is gone.
      -- For remaining heartbeatReq q t: from old hinv (via hsub).
      fun q t h => by
        rcases hnew h with h | h
        · exact hinv.heartbeatReq_tok q t h
        · exact absurd h (by simp),
      -- heartbeatResp_eq: new heartbeatResp p token has token = myToken p = s.myToken p.
      -- Others: from old hinv.
      fun q t h => by
        rcases hnew h with h | h
        · exact hinv.heartbeatResp_eq q t h
        · simp only [Msg.heartbeatResp.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          exact htok_eq.symm,
      -- heartbeatResp_bl: new heartbeatResp p token has believesLeader p = true (hbl).
      fun q t h => by
        rcases hnew h with h | h
        · exact hinv.heartbeatResp_bl q t h
        · simp only [Msg.heartbeatResp.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          exact hbl,
      -- heartbeatResp_count: new heartbeatResp p token; old ones pass through erase.
      fun q t => by
        show List.count (Msg.heartbeatResp q t)
          (s.network.erase (Msg.heartbeatReq p token) ++ [Msg.heartbeatResp p token]) ≤ 1
        by_cases hqt : Msg.heartbeatResp q t = Msg.heartbeatResp p token
        · rw [hqt, List.count_append, List.count_erase_of_ne (by simp), List.count_singleton_self]
          -- Gate: heartbeatResp p token ∉ s.network → count = 0 in old network → new count = 1
          have h0 : List.count (Msg.heartbeatResp p token) s.network = 0 :=
            List.count_eq_zero.mpr hno_hbresp
          omega
        · rw [List.count_append, count_singleton_ne _ _ hqt, Nat.add_zero,
              List.count_erase_of_ne (show Msg.heartbeatResp q t ≠ Msg.heartbeatReq p token by simp)]
          exact hinv.heartbeatResp_count q t,
      -- acqResp_excl_hb: gate says no acquireResp p in old network. New heartbeatResp p token added.
      -- For q = p: acquireResp p t ∈ new net → acquireResp p t ∈ old net (erase only heartbeatReq).
      --   But gate says acquireResp p t ∉ old net. Contradiction.
      -- For q ≠ p: acquireResp q t ∈ new net → acquireResp q t ∈ old net.
      --   heartbeatResp q tok ∈ new net → heartbeatResp q tok ∈ old net (it's not the new p one).
      --   By old acqResp_excl_hb: contradiction.
      fun q t h tok hhb => by
        rcases hnew h with h1 | h1
        · rcases hnew hhb with hhb | hhb
          · exact hinv.acqResp_excl_hb q t h1 tok hhb
          · -- hhb : heartbeatResp q tok = heartbeatResp p token → q = p ∧ tok = token.
            simp only [Msg.heartbeatResp.injEq] at hhb; obtain ⟨rfl, rfl⟩ := hhb
            -- h1 : acquireResp p t ∈ s.network. But hno_acq_gate t says it's not. Contradiction.
            exact absurd h1 (hno_acq_gate t)
        · exact absurd h1 (by simp)⟩
  | recvHeartbeatResp p token =>
    -- Erases heartbeatResp p token from network. All invariants preserved (erase is monotone).
    simp only [msgLeaseSpec] at hgate htrans
    obtain ⟨hmem_hr, htok_hr⟩ := hgate; subst htrans
    have hsub : ∀ {m}, m ∈ s.network.erase (Msg.heartbeatResp p token) → m ∈ s.network :=
      fun h => List.erase_subset h
    have hne_acq : ∀ q t, Msg.acquireResp q t ≠ Msg.heartbeatResp p token := by intros; simp
    have hne_hbResp : ∀ q t, Msg.heartbeatResp q t ≠ Msg.heartbeatResp p token →
        (Msg.heartbeatResp q t ∈ s.network.erase (Msg.heartbeatResp p token) ↔
         Msg.heartbeatResp q t ∈ s.network) := by
      intro q t hne
      exact ⟨hsub, (List.mem_erase_of_ne hne).mpr⟩
    exact ⟨hinv.myToken_lt,
      fun q t h => hinv.acqResp_lt q t (hsub h),
      fun q t h => hinv.acqResp_gt q t (hsub h),
      fun q v t sq h => hinv.writeReq_tok q v t sq (hsub h),
      fun q t h => hinv.releaseReq_tok q t (hsub h),
      fun q t sq h => hinv.writeResp_eq q t sq (hsub h),
      fun q t h => hinv.releaseResp_eq q t (hsub h),
      fun q t h seq habs => hinv.acqResp_excl_wr q t (hsub h) seq (hsub habs),
      fun q t h habs => hinv.acqResp_excl_rel q t (hsub h) (hsub habs),
      fun q v sq h => hinv.writeReq_seq q v sq (hsub h),
      fun q sq h => hinv.writeResp_seq q sq (hsub h),
      fun q t sq h => hinv.writeResp_hw q t sq (hsub h),
      fun q t h => hinv.releaseResp_bl q t (hsub h),
      fun q t1 t2 h1 h2 => hinv.acqResp_unique q t1 t2 (hsub h1) (hsub h2),
      fun q t => by
        rw [List.count_erase_of_ne (hne_acq q t)]; exact hinv.acqResp_count q t,
      fun q h => (hinv.holder_believes q h).imp id (fun ⟨t, ht⟩ =>
        ⟨t, (List.mem_erase_of_ne (hne_acq q t)).mpr ht⟩),
      fun q t h hrel => by
        obtain ⟨t', ht'⟩ := hinv.holder_rel_acq q t h (hsub hrel)
        exact ⟨t', (List.mem_erase_of_ne (hne_acq q t')).mpr ht'⟩,
      fun q t => by
        rw [List.count_erase_of_ne (show Msg.releaseResp q t ≠ Msg.heartbeatResp p token by simp)]
        exact hinv.releaseResp_count q t,
      fun q t sq => by
        rw [List.count_erase_of_ne (show Msg.writeResp q t sq ≠ Msg.heartbeatResp p token by simp)]
        exact hinv.writeResp_count q t sq,
      -- heartbeatReq_tok: erase heartbeatResp; heartbeatReq passes through
      fun q t h => hinv.heartbeatReq_tok q t (hsub h),
      -- heartbeatResp_eq: erase decreases; remaining heartbeatResps are in old network
      fun q t h => hinv.heartbeatResp_eq q t (hsub h),
      -- heartbeatResp_bl: erase decreases
      fun q t h => hinv.heartbeatResp_bl q t (hsub h),
      -- heartbeatResp_count: erase decreases count
      fun q t => by
        by_cases hqt : Msg.heartbeatResp q t = Msg.heartbeatResp p token
        · rw [hqt, List.count_erase_self]; have := hinv.heartbeatResp_count p token; omega
        · rw [List.count_erase_of_ne hqt]; exact hinv.heartbeatResp_count q t,
      -- acqResp_excl_hb: erase heartbeatResp; acquireResp passes through; heartbeatResp erase is monotone
      fun q t h tok hhb => hinv.acqResp_excl_hb q t (hsub h) tok (hsub hhb)⟩

/-- The forward simulation: message-passing LeaseLock refines atomic LeaseLock. -/
noncomputable def leaseLockSim :
    SimulationRelInv (MsgLeaseState n) (LeaseLock.LeaseState n) where
  concrete := (msgLeaseSpec n).toSpec
  abstract := (LeaseLock.leaseSpec n).toSpec
  R := @SimRel n
  inv := @MsgNetInv n
  inv_init := msgNetInv_init
  inv_next := msgNetInv_step
  init_sim := sim_init
  step_sim := sim_step

/-- Write serialization transfers from atomic to message-passing model. -/
theorem msg_writes_serialized :
    pred_implies (msgLeaseSpec n).toSpec.safety
      [tlafml| □ ⌜fun (s : MsgLeaseState n) =>
        LeaseLock.Sorted (fun e₁ e₂ => LeaseLock.entry_lt e₁ e₂) s.journal⌝] :=
  leaseLockSim.preserves_invariant
    (LeaseLock.lease_inv n)
    (LeaseLock.lease_inv_init n)
    (fun a a' hinv ⟨act, hfire⟩ => LeaseLock.lease_inv_step n act a a' hinv hfire.1 hfire.2)
    (fun s => LeaseLock.Sorted (fun e₁ e₂ => LeaseLock.entry_lt e₁ e₂) s.journal)
    (fun s a hR hinv => by
      show LeaseLock.Sorted _ s.journal
      rw [← hR.journal_eq]; exact hinv.2.2.2.1)

end Simulation

end MsgLeaseLock
