import Leslie.Action

/-! ## Distributed Lease Lock with Fencing Tokens

    ### Overview

    We model a distributed lease-based lock protecting a storage node.
    The system has three components:

    1. **Lock service**: Issues time-bounded leases with monotonically
       increasing fencing tokens. At most one process holds a valid
       lease at any time. Leases can expire non-deterministically
       (modeling real-world timeouts, GC pauses, network partitions).

    2. **Processes** (`Fin n`): Each process can acquire the lock,
       perform writes while it believes it is the leader, and release
       the lock. A process that holds an expired lease does NOT know
       the lease has expired — it continues to believe it is the leader
       until its write is rejected.

    3. **Storage node**: Accepts writes tagged with (fencingToken, seqNum).
       Maintains a high-water mark of the highest (token, seq) pair seen.
       Rejects any write whose (token, seq) is not strictly greater than
       the high-water mark. This ensures writes are totally ordered even
       when a stale leader (with an expired lease) attempts a write.

    ### The Kleppmann scenario (why fencing tokens are needed)

    Without fencing tokens, the following unsafe scenario is possible:

    1. Process P₁ acquires the lock.
    2. P₁ is paused (GC, network delay) longer than the lease duration.
    3. The lease expires. P₂ acquires the lock with a new lease.
    4. P₂ writes to storage.
    5. P₁ wakes up, unaware the lease expired, and writes to storage.
    6. P₁'s write overwrites P₂'s — violating mutual exclusion!

    With fencing tokens: P₂ gets token 2 (> P₁'s token 1). P₂ writes
    with token 2; the storage node records high-water mark 2. When P₁
    attempts to write with token 1, the storage node rejects it (1 < 2).

    Reference: Martin Kleppmann, "How to do distributed locking" (2016).
    https://martin.kleppmann.com/2016/02/08/how-to-do-distributed-locking.html

    ### Generation numbers

    Each leader numbers its own writes sequentially within its generation
    (= fencing token). A write carries (fencingToken, seqNum). The
    storage node accepts a write iff its (token, seq) pair is strictly
    greater than the current high-water mark in lexicographic order:

        (token₂, seq₂) > (token₁, seq₁)  iff
        token₂ > token₁ ∨ (token₂ = token₁ ∧ seq₂ > seq₁)

    This ensures that:
    - Writes from different leaders are ordered by fencing token.
    - Writes from the same leader are ordered by sequence number.
    - Stale writes are always rejected.

    ### Properties proved

    1. **Leader exclusivity** (`leader_has_highest_token`):
       If process p holds a valid (non-expired) lease, then p's fencing
       token is strictly greater than every other process's token. This
       means p's writes will always pass the fencing check.

    2. **Write serialization** (`writes_serialized`):
       The storage journal is strictly ordered by (fencingToken, seqNum).
       Every accepted write has a (token, seq) pair strictly greater
       than all previously accepted writes.
-/

open TLA

namespace LeaseLock

variable (n : Nat)

/-! ### State

    The global state combines the lock service, per-process state,
    and the storage node into a single record. -/

/-- An entry in the storage journal: a value tagged with its
    fencing token and sequence number. -/
structure WriteEntry where
  value : Nat
  token : Nat
  seq : Nat
  deriving DecidableEq, Repr

/-- Global system state. -/
structure LeaseState (n : Nat) where
  -- ── Lock service ──────────────────────────────────────────────
  /-- Next fencing token to issue. Starts at 1, incremented on each acquire.
      Invariant: always strictly greater than any issued token. -/
  nextToken : Nat
  /-- Current lock holder, or `none` if the lock is free. -/
  lockHolder : Option (Fin n)
  /-- Whether the current lease is still valid (not yet expired). -/
  leaseActive : Bool

  -- ── Per-process state ─────────────────────────────────────────
  /-- Fencing token received by each process on its most recent acquire.
      0 means the process has never held the lock. -/
  myToken : Fin n → Nat
  /-- Per-process write counter within the current generation.
      Reset to 0 when a process acquires the lock. -/
  writeSeq : Fin n → Nat
  /-- Whether the process believes it currently holds the lock.
      This can be TRUE even after the lease has expired — the process
      only discovers it lost the lock when its write is rejected. -/
  believesLeader : Fin n → Bool

  -- ── Storage node ──────────────────────────────────────────────
  /-- Highest fencing token seen in an accepted write. -/
  highToken : Nat
  /-- Highest sequence number seen at the `highToken` level. -/
  highSeq : Nat
  /-- Journal of accepted writes, in order. Each entry carries the
      value written along with its (token, seq) pair. -/
  journal : List WriteEntry

/-! ### Actions

    Five actions model the protocol. Each action is a `GatedAction`:
    it has a precondition (`gate`) that must hold for the action to
    fire, and a state transition. -/

inductive LeaseAction (n : Nat) where
  /-- A process requests the lock. Succeeds if the lock is free or
      the lease has expired. The lock service issues a new fencing
      token (strictly greater than all previous tokens). -/
  | acquire (p : Fin n)
  /-- The current lease expires. Models a timeout, GC pause, or
      network partition. The lock becomes available but the old
      holder is NOT notified — it still believes it is the leader. -/
  | expireLease
  /-- A process writes a value to storage. The storage node checks
      the fencing token: the write is accepted only if (myToken, seq+1)
      is strictly greater than the current (highToken, highSeq). -/
  | writeOk (p : Fin n) (v : Nat)
  /-- A process voluntarily releases the lock. -/
  | release (p : Fin n)

/-! ### Specification

    The `ActionSpec` defines the initial state and all possible
    transitions. The `gate` field is the precondition; the
    `transition` field defines the state change. -/

def leaseSpec : ActionSpec (LeaseState n) (LeaseAction n) where
  init := fun s =>
    -- Initially: no lock holder, no tokens issued, empty journal.
    s.nextToken = 1 ∧
    s.lockHolder = none ∧
    s.leaseActive = false ∧
    (∀ p, s.myToken p = 0) ∧
    (∀ p, s.writeSeq p = 0) ∧
    (∀ p, s.believesLeader p = false) ∧
    s.highToken = 0 ∧
    s.highSeq = 0 ∧
    s.journal = []
  actions := fun
    | .acquire p => {
        -- ── Acquire the lock ──────────────────────────────────────
        -- A process can acquire if the lock is free (no holder) or
        -- the current lease has expired. This models both initial
        -- acquisition and takeover after timeout.
        gate := fun s =>
          s.lockHolder = none ∨ s.leaseActive = false
        transition := fun s s' =>
          -- Issue a new fencing token (= nextToken) to the acquirer.
          -- Increment nextToken to ensure future tokens are higher.
          -- Reset the acquirer's write sequence number.
          -- The acquirer now believes it is the leader.
          -- NOTE: if there was a previous holder whose lease expired,
          -- that process's believesLeader is NOT cleared — it will
          -- discover it lost the lock only on its next write attempt.
          s' = { s with
            lockHolder := some p
            leaseActive := true
            nextToken := s.nextToken + 1
            myToken := fun q => if q = p then s.nextToken else s.myToken q
            writeSeq := fun q => if q = p then 0 else s.writeSeq q
            believesLeader := fun q =>
              if q = p then true else s.believesLeader q }
      }
    | .expireLease => {
        -- ── Lease expires ─────────────────────────────────────────
        -- The lease times out. The lock service marks the lease as
        -- inactive, but the holder is NOT notified. The holder
        -- continues to believe it is the leader. This models the
        -- Kleppmann scenario where a GC pause or network partition
        -- causes the lease to expire while the holder is unaware.
        gate := fun s =>
          s.leaseActive = true
        transition := fun s s' =>
          s' = { s with leaseActive := false }
      }
    | .writeOk p v => {
        -- ── Write to storage (accepted) ───────────────────────────
        -- A process attempts to write to storage.
        -- The storage node checks the fencing token:
        --   accept iff (myToken, writeSeq+1) > (highToken, highSeq)
        -- in lexicographic order. If accepted, the storage node
        -- updates its high-water mark and appends the write to the
        -- journal. The process increments its write sequence number.
        --
        -- Note: the process does NOT need to actually hold a valid
        -- lease for the write to succeed — only the fencing token
        -- matters. A stale leader whose token is still the highest
        -- can write. But once a newer leader has written (with a
        -- higher token), the stale leader's writes will be rejected.
        gate := fun s =>
          s.myToken p > s.highToken ∨
          (s.myToken p = s.highToken ∧ s.writeSeq p + 1 > s.highSeq)
        transition := fun s s' =>
          s' = { s with
            highToken := s.myToken p
            highSeq := s.writeSeq p + 1
            writeSeq := fun q =>
              if q = p then s.writeSeq p + 1 else s.writeSeq q
            journal := s.journal ++ [⟨v, s.myToken p, s.writeSeq p + 1⟩] }
      }
    | .release p => {
        -- ── Voluntary release ─────────────────────────────────────
        -- A process that holds a valid lease releases it voluntarily.
        -- This clears the lock holder and marks the lease as inactive.
        -- The process no longer believes it is the leader.
        gate := fun s =>
          s.lockHolder = some p ∧ s.leaseActive = true
        transition := fun s s' =>
          s' = { s with
            lockHolder := none
            leaseActive := false
            believesLeader := fun q =>
              if q = p then false else s.believesLeader q }
      }
  fair := []

/-! ### Safety properties -/

/-- The lexicographic order on (token, seq) pairs.
    Write entry e₁ is "before" entry e₂ iff e₁'s token is smaller,
    or both tokens are equal and e₁'s seq is smaller. -/
def entry_lt (e₁ e₂ : WriteEntry) : Prop :=
  e₁.token < e₂.token ∨ (e₁.token = e₂.token ∧ e₁.seq < e₂.seq)

/-- **Property 1: Leader exclusivity.**
    If process `p` holds a valid (non-expired) lease, then `p`'s
    fencing token is strictly greater than every other process's token.
    This means the valid leader's writes will always pass the fencing
    check — no other process can interfere. -/
def leader_has_highest_token (s : LeaseState n) : Prop :=
  ∀ p : Fin n, s.lockHolder = some p → s.leaseActive = true →
    ∀ q : Fin n, q ≠ p → s.myToken q < s.myToken p

/-- A list is sorted by relation `R` if `R` holds between every
    pair of adjacent elements. -/
inductive Sorted (R : α → α → Prop) : List α → Prop where
  | nil : Sorted R []
  | singleton (a : α) : Sorted R [a]
  | cons {a b : α} {rest : List α} : R a b → Sorted R (b :: rest) → Sorted R (a :: b :: rest)

/-- **Property 2: Write serialization.**
    The storage journal is strictly ordered by (token, seq). For any
    two entries where e₁ was written before e₂, e₁ < e₂ in the
    lexicographic (token, seq) order.

    This is the key safety property: even if multiple processes
    believe they are the leader (due to expired leases), the fencing
    mechanism ensures all accepted writes are totally ordered. -/
def writes_serialized (s : LeaseState n) : Prop :=
  Sorted (fun e₁ e₂ => entry_lt e₁ e₂) s.journal

/-! ### Inductive invariant

    The invariant combines both safety properties with auxiliary
    state that is needed for the inductive argument. -/

def lease_inv (s : LeaseState n) : Prop :=
  -- (1) Token monotonicity: every issued token is < nextToken.
  --     This ensures new tokens are always fresh.
  (∀ p : Fin n, s.myToken p < s.nextToken) ∧
  -- (2) nextToken starts at 1 and is always positive.
  s.nextToken > 0 ∧
  -- (3) Leader has the highest token: if the lease is active,
  --     the holder's token exceeds all others.
  leader_has_highest_token n s ∧
  -- (4) Write serialization: the journal is strictly ordered.
  writes_serialized n s ∧
  -- (5) High-water mark consistency: all journal entries are
  --     ≤ (highToken, highSeq) in lexicographic order.
  (∀ e ∈ s.journal, e.token < s.highToken ∨
    (e.token = s.highToken ∧ e.seq ≤ s.highSeq)) ∧
  -- (6) Last entry matches high-water mark: if the journal is
  --     non-empty, the last entry's (token, seq) = (highToken, highSeq).
  (s.journal = [] →  s.highToken = 0 ∧ s.highSeq = 0) ∧
  (∀ (h : s.journal ≠ []),
    (s.journal.getLast h).token = s.highToken ∧
    (s.journal.getLast h).seq = s.highSeq) ∧
  -- (7) Storage tokens are bounded by nextToken.
  s.highToken < s.nextToken

/-! ### Helper lemmas -/

/-- Appending to a Sorted list preserves sorting if the new
    element is related to the last element. -/
private theorem sorted_append_singleton {R : α → α → Prop}
    {l : List α} {x : α}
    (h_sorted : Sorted R l)
    (h_last : l = [] ∨ ∃ y, l.getLast? = some y ∧ R y x) :
    Sorted R (l ++ [x]) := by
  induction l with
  | nil => exact Sorted.singleton x
  | cons a t ih =>
    cases t with
    | nil =>
      simp only [List.cons_append, List.nil_append]
      rcases h_last with h | ⟨y, hy, hR⟩
      · exact absurd h (by simp)
      · simp [List.getLast?] at hy
        subst hy
        exact Sorted.cons hR (Sorted.singleton x)
    | cons b u =>
      simp only [List.cons_append]
      have h_rest : Sorted R (b :: u) := by
        cases h_sorted with
        | cons hab hrest => exact hrest
      have h_ab : R a b := by
        cases h_sorted with
        | cons hab _ => exact hab
      constructor
      · exact h_ab
      · apply ih h_rest
        rcases h_last with h | ⟨y, hy, hR⟩
        · exact absurd h (by simp)
        · right
          refine ⟨y, ?_, hR⟩
          simp [List.getLast?] at hy ⊢
          exact hy

/-! ### Invariant proof: initialization -/

theorem lease_inv_init :
    ∀ s, (leaseSpec n).init s → lease_inv n s := by
  intro s ⟨hnt, hhold, hlease, htok, hseq, hbel, hht, hhs, hj⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) Token monotonicity
    intro p ; rw [htok p, hnt] ; omega
  · -- (2) nextToken > 0
    rw [hnt] ; omega
  · -- (3) Leader exclusivity: no active lease initially
    intro p hp ; rw [hhold] at hp ; simp at hp
  · -- (4) Write serialization: empty journal
    simp only [writes_serialized] ; rw [hj] ; exact Sorted.nil
  · -- (5) All entries ≤ high-water mark: empty journal
    intro e he ; rw [hj] at he ; simp at he
  · -- (6a) Empty journal → high-water mark = (0, 0)
    intro _ ; exact ⟨hht, hhs⟩
  · -- (6b) Non-empty → last matches: journal is empty, vacuous
    intro h ; exact (h (by rw [hj])).elim
  · -- (7) highToken < nextToken
    rw [hht, hnt] ; omega

/-! ### Invariant proof: action preservation -/

theorem lease_inv_step :
    ∀ (a : LeaseAction n) (s s' : LeaseState n),
    lease_inv n s →
    ((leaseSpec n).actions a).gate s →
    ((leaseSpec n).actions a).transition s s' →
    lease_inv n s' := by
  intro a s s' ⟨h_tok_mono, h_nt_pos, h_leader, h_serial, h_entries_le, h_empty_hw, h_last_hw, h_ht_bound⟩ hgate htrans
  cases a with
  | acquire p =>
    -- ── acquire(p): issue new token, set up new leader ────────
    -- Journal, highToken, highSeq unchanged.
    -- myToken[p] := nextToken, nextToken++.
    simp only [leaseSpec] at hgate htrans
    subst htrans
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- (1) Token monotonicity: myToken[p] = old nextToken < new nextToken.
      --     For q ≠ p: myToken[q] < old nextToken < new nextToken.
      intro q ; simp only
      by_cases hq : q = p
      · subst hq ; simp
      · simp [hq] ; exact Nat.lt_succ_of_lt (h_tok_mono q)
    · -- (2) nextToken > 0
      simp
    · -- (3) Leader exclusivity: p is the new holder with highest token.
      intro q hq hlease r hr
      simp at hq hlease
      subst hq
      simp only
      by_cases hrp : r = p
      · exact (hr hrp).elim
      · simp [hrp] ; exact h_tok_mono r
    · -- (4) Write serialization: journal unchanged
      simpa using h_serial
    · -- (5) Entries ≤ high-water mark: journal unchanged
      simpa using h_entries_le
    · -- (6a) Empty journal: high-water mark unchanged
      simpa using h_empty_hw
    · -- (6b) Last entry: journal unchanged
      simpa using h_last_hw
    · -- (7) highToken < nextToken: highToken unchanged, nextToken++
      simp ; exact Nat.lt_succ_of_lt h_ht_bound
  | expireLease =>
    -- ── expireLease: mark lease as inactive ────────────────────
    -- Only leaseActive changes. Everything else preserved.
    simp only [leaseSpec] at hgate htrans
    subst htrans
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using h_tok_mono
    · simpa using h_nt_pos
    · -- Leader exclusivity: lease is now inactive, so vacuously true
      intro p hp hlease ; simp at hlease
    · simpa using h_serial
    · simpa using h_entries_le
    · simpa using h_empty_hw
    · simpa using h_last_hw
    · simpa using h_ht_bound
  | writeOk p v =>
    -- ── writeOk(p, v): append entry to journal ────────────────
    -- The gate ensures (myToken p, writeSeq p + 1) > (highToken, highSeq).
    -- The storage node updates its high-water mark and appends the entry.
    simp only [leaseSpec] at hgate htrans
    subst htrans
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- (1) Token monotonicity: unchanged
      simpa using h_tok_mono
    · -- (2) nextToken > 0: unchanged
      simpa using h_nt_pos
    · -- (3) Leader exclusivity: lockHolder/leaseActive unchanged
      simpa using h_leader
    · -- (4) Write serialization: journal ++ [new entry]
      --     The old journal is Sorted. The new entry is > the last old entry
      --     (by the fencing gate + high-water mark invariant).
      simp only [writes_serialized] at h_serial ⊢
      apply sorted_append_singleton h_serial
      by_cases hj : s.journal = []
      · left ; exact hj
      · right
        have ⟨htok_last, hseq_last⟩ := h_last_hw hj
        refine ⟨s.journal.getLast hj, ?_, ?_⟩
        · simp [List.getLast?_eq_some_getLast hj]
        · -- entry_lt (last old entry) (new entry)
          unfold entry_lt
          dsimp only
          rw [htok_last, hseq_last]
          rcases hgate with h | ⟨h1, h2⟩
          · left ; omega
          · right ; constructor <;> omega
    · -- (5) All entries ≤ new high-water mark (myToken p, writeSeq p + 1).
      --     Old entries were ≤ old (highToken, highSeq).
      --     By the fencing gate: old (highToken, highSeq) < new.
      --     So old entries < new. And the new entry = new high-water mark.
      intro e he
      simp only [List.mem_append, List.mem_singleton] at he
      rcases he with he | he
      · -- Old entry: ≤ old high-water mark < new high-water mark
        have h_old := h_entries_le e he
        rcases hgate with htgt | ⟨hteq, hsgt⟩
        · left ; simp only ; rcases h_old with h | ⟨h, _⟩ <;> omega
        · rcases h_old with h_lt | ⟨h_eq, h_le⟩
          · left ; simp only ; omega
          · right ; simp only ; constructor <;> omega
      · -- New entry = new high-water mark
        subst he ; simp
    · -- (6a) Empty journal → high-water mark
      simp
    · -- (6b) Last entry of journal ++ [new] = new entry
      intro h
      constructor <;> simp [show (s.journal ++ [⟨v, s.myToken p, s.writeSeq p + 1⟩]).getLast h =
        ⟨v, s.myToken p, s.writeSeq p + 1⟩ from List.getLast_concat]
    · -- (7) highToken < nextToken: highToken := myToken p < nextToken
      simp ; exact h_tok_mono p
  | release p =>
    -- ── release(p): clear lock holder ─────────────────────────
    -- Journal, highToken, highSeq, myToken, nextToken unchanged.
    simp only [leaseSpec] at hgate htrans
    subst htrans
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using h_tok_mono
    · simpa using h_nt_pos
    · -- Leader exclusivity: lockHolder := none, vacuously true
      intro q hq ; simp at hq
    · simpa using h_serial
    · simpa using h_entries_le
    · simpa using h_empty_hw
    · simpa using h_last_hw
    · simpa using h_ht_bound

/-! ### Safety theorem: the invariant is preserved -/

/-- The inductive invariant holds in all reachable states. -/
theorem lease_inv_always :
    pred_implies (leaseSpec n).safety
      [tlafml| □ ⌜lease_inv n⌝] := by
  apply init_invariant
  · exact lease_inv_init n
  · intro s s' ⟨a, hfire⟩ hinv
    exact lease_inv_step n a s s' hinv hfire.1 hfire.2

/-! ### Safety theorem: leader exclusivity -/

/-- The valid leader always has the highest fencing token. -/
theorem leader_exclusivity :
    pred_implies (leaseSpec n).safety
      [tlafml| □ ⌜leader_has_highest_token n⌝] := by
  apply pred_implies_trans (q := [tlafml| □ ⌜lease_inv n⌝])
  · exact lease_inv_always n
  · apply always_monotone
    intro e h ; exact h.2.2.1

/-- All writes accepted by the storage node are totally ordered. -/
theorem write_serialization :
    pred_implies (leaseSpec n).safety
      [tlafml| □ ⌜writes_serialized n⌝] := by
  apply pred_implies_trans (q := [tlafml| □ ⌜lease_inv n⌝])
  · exact lease_inv_always n
  · apply always_monotone
    intro e h ; exact h.2.2.2.1

/-! ### Design note: why this is action-based, not round-based

    Fencing tokens resemble "rounds" or "ballots" (as in Paxos): each
    is a monotonically increasing identifier assigned to successive
    leaders. Generation numbers (writeSeq) resemble "phases" within
    a round. However, the protocol is NOT round-based in the Leslie
    `RoundAlg` sense:

    | Round-based (`RoundAlg`)              | Lease Lock                          |
    |-----------------------------------------|-------------------------------------|
    | All processes act simultaneously        | Only the leader writes; others idle |
    | Communication is synchronous per round  | Writes are asynchronous             |
    | Round advances are global               | Token advances are local (acquire)  |
    | Messages broadcast to all               | Writes go to one storage node       |
    | HO sets model message loss              | Lease expiry models loss of authority |

    The lease lock is fundamentally **asynchronous and asymmetric**:
    one leader writes, the storage node validates, and other processes
    are passive until they acquire. There is no "everyone sends,
    everyone receives" structure that `RoundAlg` assumes.

    A round-based formulation could force each fencing token generation
    into a "round" (Phase 0 = acquire, Phase 1..k = writes, Phase 2 =
    expire/release), but this distorts the model: the number of writes
    per generation is unbounded, other processes don't participate, and
    the interesting behavior (stale leader writes after expiry) spans
    across rounds rather than within a single round.

    That said, the **safety argument** mirrors round-based proofs:
    the fencing token plays the role of the ballot number, the
    high-water mark at the storage node plays the role of "last
    accepted ballot," and the invariant "writes are ordered by token"
    mirrors the Paxos ballot ordering. The key difference is that
    ordering is enforced by the **storage node** (rejecting stale
    tokens) rather than by **communication closure** (messages
    delivered only within their round). -/

end LeaseLock
