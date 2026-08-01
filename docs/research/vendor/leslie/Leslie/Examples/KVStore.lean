import Leslie.Action

/-! ## Distributed Key-Value Store with Replicated Journal

    ### System overview

    We model a distributed single-key store backed by a replicated
    journal. There are three replicas (`r1`, `r2`, `r3`) and two
    possible values (`v0`, `v1`). Clients write through a designated
    leader and read from any replica.

    ### The journal

    The journal is an abstract, totally-ordered, append-only log of
    values. It is the single source of truth for the system. In a
    real implementation the journal would be a consensus-based
    replicated log (e.g., Raft or Multi-Paxos); here we treat it as
    a black box that provides two guarantees:

    1. **Atomic append.** A successful write atomically appends one
       entry to the end of the journal.
    2. **Lease-based writer election.** The journal maintains an
       internal `leader` field. Only the current lease holder may
       append; writes from any other replica are rejected.

    ### Leader election and stale leaders

    Any replica may acquire the lease at any time (modeled by the
    non-deterministic `acquire` action). When replica `r` acquires
    the lease, the journal's `leader` field is set to `r` and `r`
    records that it believes itself to be the leader. Crucially, the
    *previous* leader is **not notified** — it continues to believe
    it holds the lease until it attempts a write and is rejected
    (the `writeFail` action).

    This models the real-world scenario where leases expire silently
    and the old leader discovers the loss only on its next operation.

    ### Write path

    A replica that believes it is the leader may attempt a write:

    - **`writeOk r`**: The journal confirms `r` is the current lease
      holder. The value `v` is appended to the journal. Replica `r`
      also caches the write locally — its `store` is updated to
      `some v` and its `cursor` advances past the new entry. This
      means the writer sees its own writes immediately, without
      waiting for a journal round-trip.

    - **`writeFail r`**: The journal rejects the write because `r`
      is no longer the lease holder. Replica `r` learns it has lost
      the lease and sets `believes_leader` to `false`.

    ### Read path

    Every replica (including the writer) maintains a `cursor` into
    the journal and a local `store` holding the most recently
    consumed value. The `consume r` action reads the entry at
    `journal[cursor]`, copies it into `store`, and advances the
    cursor. Clients read from `store` directly — there is no
    coordination on the read path.

    Because each replica consumes the journal independently, replicas
    may be at different positions. A replica whose cursor is behind
    will serve stale reads. However, all replicas see writes in the
    **same order** because they all read from the same journal.

    ### Properties proved

    We define an inductive invariant `kv_inv` and derive three
    safety properties, all without sorry:

    - **Store consistency** (`kv_inv`): Each replica's local store
      matches the journal entry at its cursor position. Formally,
      if `cursor r > 0` then `store r = journal[cursor r - 1]?`.

    - **Writer exclusivity** (`writer_exclusivity`): At most one
      replica can successfully write at any point. If two replicas
      can both fire `writeOk`, they must be the same replica (because
      `leader` is a single `Option Replica`).

    - **Write serialization** (`write_serialization`): Two replicas
      at the same cursor position always agree on the stored value.
      This follows directly from the invariant: both stores equal the
      same journal entry.

    - **Store reflects journal** (`store_from_journal`): A replica
      that has consumed at least one entry always has `some v` in its
      store (never `none`).

    ### What this does *not* model

    - **Multiple keys.** We model a single key. Extending to multiple
      keys is straightforward (the journal already serializes all
      writes regardless of key).

    - **Liveness / convergence.** We prove safety only. Showing that
      all replicas eventually catch up requires weak fairness on the
      `consume` actions.

    - **Full linearizability of reads.** Reads are purely local and
      may be stale.  We prove per-replica read consistency (each
      store equals the sequential value at its cursor) and write
      linearizability (refinement to a sequential spec), but full
      read linearizability would require modeling client-visible
      timestamps and constraining read freshness.
-/

open TLA

namespace KVStore

/-! ### Types -/

inductive Replica where | r1 | r2 | r3
  deriving DecidableEq, Repr

inductive Value where | v0 | v1
  deriving DecidableEq, Repr

/-! ### State -/

structure KVState where
  /-- The replicated journal (total order of all writes) -/
  journal : List Value
  /-- Which replica currently holds the journal lease -/
  leader : Option Replica
  /-- Per-replica local store (single key) -/
  store : Replica → Option Value
  /-- Per-replica journal consumption cursor -/
  cursor : Replica → Nat
  /-- Per-replica belief about holding the lease -/
  believes_leader : Replica → Bool

/-! ### Actions -/

inductive KVAction where
  | acquire (r : Replica)
  | writeOk (r : Replica)
  | writeFail (r : Replica)
  | consume (r : Replica)

def kvstore : ActionSpec KVState KVAction where
  init := fun s =>
    s.journal = [] ∧
    s.leader = none ∧
    (∀ r, s.store r = none) ∧
    (∀ r, s.cursor r = 0) ∧
    (∀ r, s.believes_leader r = false)
  actions := fun
    | .acquire r => {
        gate := fun _ => True
        transition := fun s s' =>
          s' = { s with
            leader := some r
            believes_leader := fun r' => if r' = r then true else s.believes_leader r' }
      }
    | .writeOk r => {
        gate := fun s => s.believes_leader r = true ∧ s.leader = some r
        transition := fun s s' => ∃ v : Value,
          s' = { s with
            journal := s.journal ++ [v]
            store := fun r' => if r' = r then some v else s.store r'
            cursor := fun r' => if r' = r then s.journal.length + 1 else s.cursor r' }
      }
    | .writeFail r => {
        gate := fun s => s.believes_leader r = true ∧ s.leader ≠ some r
        transition := fun s s' =>
          s' = { s with
            believes_leader := fun r' => if r' = r then false else s.believes_leader r' }
      }
    | .consume r => {
        gate := fun s => s.cursor r < s.journal.length
        transition := fun s s' =>
          ∃ v, s.journal[s.cursor r]? = some v ∧
          s' = { s with
            store := fun r' => if r' = r then some v else s.store r'
            cursor := fun r' => if r' = r then s.cursor r + 1 else s.cursor r' }
      }

/-! ### Protocol Invariant -/

def kv_inv (s : KVState) : Prop :=
  (∀ r, s.cursor r ≤ s.journal.length) ∧
  (∀ r, s.cursor r = 0 → s.store r = none) ∧
  (∀ r, s.cursor r > 0 → s.store r = s.journal[s.cursor r - 1]?)

/-! ### List indexing helper lemmas -/

private theorem getElem?_append_single (l : List α) (a : α) :
    (l ++ [a])[l.length]? = some a := by
  induction l with
  | nil => rfl
  | cons _ xs ih => simp

/-! ### Invariant proofs -/

theorem kv_inv_init : ∀ s, kvstore.init s → kv_inv s := by
  intro s ⟨hj, _, hst, hc, _⟩
  exact ⟨fun r => by simp [hj, hc r],
         fun r _ => hst r,
         fun r h => by simp [hc r] at h⟩

theorem kv_inv_next : ∀ s s', kv_inv s →
    (∃ i, (kvstore.actions i).fires s s') → kv_inv s' := by
  intro s s' ⟨hcb, hst0, hstk⟩ ⟨i, hfire⟩
  cases i with
  | acquire r =>
    obtain ⟨_, ht⟩ := hfire
    dsimp only [kvstore] at ht; subst ht
    exact ⟨hcb, hst0, hstk⟩
  | writeFail r =>
    obtain ⟨_, ht⟩ := hfire
    dsimp only [kvstore] at ht; subst ht
    exact ⟨hcb, hst0, hstk⟩
  | writeOk r =>
    obtain ⟨_, ht⟩ := hfire
    dsimp only [kvstore] at ht
    obtain ⟨v, ht⟩ := ht; subst ht
    refine ⟨?_, ?_, ?_⟩
    -- Cursor bounded
    · intro r'; dsimp only
      by_cases h : r' = r
      · subst h; simp
      · simp [h]; have := hcb r'; omega
    -- Store at cursor 0
    · intro r' hc; dsimp only at hc ⊢
      by_cases h : r' = r
      · subst h; simp at hc
      · simp [h] at hc ⊢; exact hst0 r' hc
    -- Store at cursor k > 0
    · intro r' hc; dsimp only at hc ⊢
      by_cases h : r' = r
      · subst h; simp
      · simp [h] at hc ⊢
        rw [hstk r' hc]
        have hle := hcb r'
        exact (List.getElem?_append_left (by omega)).symm
  | consume r =>
    obtain ⟨hg, ht⟩ := hfire
    dsimp only [kvstore] at hg ht
    obtain ⟨v, hgv, ht⟩ := ht; subst ht
    refine ⟨?_, ?_, ?_⟩
    -- Cursor bounded
    · intro r'; dsimp only
      by_cases h : r' = r
      · subst h; simp; omega
      · simp [h]; exact hcb r'
    -- Store at cursor 0
    · intro r' hc; dsimp only at hc ⊢
      by_cases h : r' = r
      · subst h; simp at hc
      · simp [h] at hc ⊢; exact hst0 r' hc
    -- Store at cursor k > 0
    · intro r' hc; dsimp only at hc ⊢
      by_cases h : r' = r
      · subst h; simp; exact hgv.symm
      · simp [h] at hc ⊢; exact hstk r' hc

/-! ### Derived Properties -/

/-- **Writer exclusivity**: at most one replica can successfully write. -/
theorem writer_exclusivity (s : KVState) (r₁ r₂ : Replica)
    (h₁ : (kvstore.actions (.writeOk r₁)).gate s)
    (h₂ : (kvstore.actions (.writeOk r₂)).gate s) : r₁ = r₂ := by
  dsimp only [kvstore] at h₁ h₂
  obtain ⟨_, hl₁⟩ := h₁
  obtain ⟨_, hl₂⟩ := h₂
  rw [hl₁] at hl₂; injection hl₂

/-- **Write serialization**: two replicas at the same cursor position
    have the same local store value. -/
theorem write_serialization (s : KVState) (hinv : kv_inv s)
    (r₁ r₂ : Replica)
    (hc₁ : s.cursor r₁ > 0) (hc₂ : s.cursor r₂ > 0)
    (heq : s.cursor r₁ = s.cursor r₂) :
    s.store r₁ = s.store r₂ := by
  obtain ⟨_, _, hstk⟩ := hinv
  rw [hstk r₁ hc₁, hstk r₂ hc₂, heq]

/-- **Store reflects journal**: if a replica has consumed entries, its store
    holds a value from the journal. -/
theorem store_from_journal (s : KVState) (hinv : kv_inv s)
    (r : Replica) (hc : s.cursor r > 0) :
    ∃ v, s.store r = some v := by
  obtain ⟨hcb, _, hstk⟩ := hinv
  have hle := hcb r
  rw [hstk r hc]
  have hlt : s.cursor r - 1 < s.journal.length := by omega
  exact ⟨s.journal[s.cursor r - 1], by simp [hlt]⟩

/-! ### Small Model Theorem

    A write-serialization violation is witnessed by exactly two replicas
    (`r₁` and `r₂` at the same cursor position but with different stores).
    We define reachability, prove the invariant holds for all reachable
    states, and conclude that no two replicas can ever disagree.

    We also show the check is **non-vacuous**: there exist reachable
    states where two distinct replicas have both consumed entries
    (cursor > 0) and the serialization property is actively enforced.
-/

/-- A state is reachable if it is an initial state or follows from a
    reachable state by firing some action. -/
inductive Reachable : KVState → Prop where
  | init (s : KVState) : kvstore.init s → Reachable s
  | step (s s' : KVState) (i : KVAction) :
      Reachable s → (kvstore.actions i).fires s s' → Reachable s'

/-- An inconsistency witness: two replicas at the same cursor position
    disagree on the stored value. -/
def inconsistent (s : KVState) : Prop :=
  ∃ r₁ r₂, s.cursor r₁ > 0 ∧ s.cursor r₂ > 0 ∧
    s.cursor r₁ = s.cursor r₂ ∧ s.store r₁ ≠ s.store r₂

/-- The invariant holds for every reachable state. -/
theorem kv_inv_reachable : ∀ s, Reachable s → kv_inv s := by
  intro s hr; induction hr with
  | init s hs => exact kv_inv_init s hs
  | step s s' i _ hfire ih => exact kv_inv_next s s' ih ⟨i, hfire⟩

/-- **Small model theorem**: no reachable state is inconsistent.
    Any potential violation would involve exactly two replicas, and
    we prove no such pair can disagree in any reachable state. -/
theorem small_model : ∀ s, Reachable s → ¬inconsistent s := by
  intro s hr ⟨r₁, r₂, hc₁, hc₂, heq, hne⟩
  exact hne (write_serialization s (kv_inv_reachable s hr) r₁ r₂ hc₁ hc₂ heq)

set_option linter.unreachableTactic false in
/-- **Non-vacuity**: the small model check is meaningful.
    We construct a concrete 3-step execution (acquire → write → consume)
    that reaches a state where two replicas have both consumed the same
    entry. The serialization property is actively constraining this state. -/
theorem small_model_nontrivial :
    ∃ s, Reachable s ∧
      s.cursor .r1 > 0 ∧ s.cursor .r2 > 0 ∧
      s.cursor .r1 = s.cursor .r2 ∧
      s.store .r1 = s.store .r2 := by
  -- Concrete states along the execution:
  -- s0 (init) → s1 (acquire r1) → s2 (writeOk r1 v0) → s3 (consume r2)
  let s0 : KVState :=
    ⟨[], none, fun _ => none, fun _ => 0, fun _ => false⟩
  let s1 : KVState :=
    ⟨[], some .r1, fun _ => none, fun _ => 0,
     fun r => if r = .r1 then true else false⟩
  let s2 : KVState :=
    ⟨[.v0], some .r1,
     fun r => if r = .r1 then some .v0 else none,
     fun r => if r = .r1 then 1 else 0,
     fun r => if r = .r1 then true else false⟩
  let s3 : KVState :=
    ⟨[.v0], some .r1,
     fun r => if r = .r2 then some .v0 else
              if r = .r1 then some .v0 else none,
     fun r => if r = .r2 then 1 else
              if r = .r1 then 1 else 0,
     fun r => if r = .r1 then true else false⟩
  -- s0 is initial
  have hr0 : Reachable s0 :=
    .init s0 ⟨rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  -- Step 1: acquire r1
  have hf1 : (kvstore.actions (.acquire .r1)).fires s0 s1 :=
    ⟨trivial, by dsimp only [kvstore, s0, s1]⟩
  have hr1 : Reachable s1 := .step s0 s1 _ hr0 hf1
  -- Step 2: writeOk r1 with value v0
  have hf2 : (kvstore.actions (.writeOk .r1)).fires s1 s2 := by
    refine ⟨⟨by dsimp [s1], by dsimp [s1]⟩, .v0, ?_⟩
    dsimp only [kvstore, s1, s2]; congr 1 <;> funext r <;> cases r <;> simp
  have hr2 : Reachable s2 := .step s1 s2 _ hr1 hf2
  -- Step 3: consume r2
  have hf3 : (kvstore.actions (.consume .r2)).fires s2 s3 := by
    refine ⟨by dsimp [kvstore, s2]; decide, .v0, by dsimp [kvstore, s2]; decide, ?_⟩
    dsimp only [kvstore, s2, s3]; congr 1 <;> funext r <;> cases r <;> simp
  have hr3 : Reachable s3 := .step s2 s3 _ hr2 hf3
  exact ⟨s3, hr3, by decide, by decide, by decide, by decide⟩

/-! ### Linearizability

    The journal provides a total order on all writes.  We formalize
    linearizability along three axes:

    1. **Structural monotonicity.**  The journal is append-only and
       each replica's cursor is non-decreasing.

    2. **Write linearizability via refinement.**  We define a sequential
       single-key store (`SeqKV`) whose state is `Option Value` and
       whose only action is "write `v`".  The mapping
       `kv_abs s = s.journal.getLast?` witnesses a stuttering refinement
       from the distributed protocol to `SeqKV`.

    3. **Per-replica read consistency.**  Each replica's local store
       equals the sequential value at its cursor position in the
       journal, so every read is linearizable at the point when the
       replica consumed that journal entry.
-/

/-- The sequential value at position `k` in a journal:
    `none` if `k = 0`, otherwise the `(k-1)`-th journal entry. -/
def seq_value (j : List Value) (k : Nat) : Option Value :=
  if k = 0 then none else j[k - 1]?

/-- Each replica's store equals the sequential value at its cursor position.
    This is the core per-replica linearizability statement. -/
theorem replica_reads_consistent (s : KVState) (hinv : kv_inv s) (r : Replica) :
    s.store r = seq_value s.journal (s.cursor r) := by
  obtain ⟨_, hst0, hstk⟩ := hinv
  simp only [seq_value]
  by_cases h : s.cursor r = 0
  · simp [h, hst0 r h]
  · simp [h, hstk r (by omega)]

/-- In any step, the journal only grows by appending. -/
theorem journal_append_only (s s' : KVState)
    (hstep : ∃ i, (kvstore.actions i).fires s s') :
    ∃ suffix, s'.journal = s.journal ++ suffix := by
  obtain ⟨i, hfire⟩ := hstep
  cases i with
  | acquire r =>
    obtain ⟨_, ht⟩ := hfire; dsimp only [kvstore] at ht; subst ht
    exact ⟨[], by simp⟩
  | writeFail r =>
    obtain ⟨_, ht⟩ := hfire; dsimp only [kvstore] at ht; subst ht
    exact ⟨[], by simp⟩
  | writeOk r =>
    obtain ⟨_, ht⟩ := hfire; dsimp only [kvstore] at ht
    obtain ⟨v, ht⟩ := ht; subst ht
    exact ⟨[v], rfl⟩
  | consume r =>
    obtain ⟨_, ht⟩ := hfire; dsimp only [kvstore] at ht
    obtain ⟨v, _, ht⟩ := ht; subst ht
    exact ⟨[], by simp⟩

/-- In any step, no replica's cursor decreases (requires the invariant for writeOk). -/
theorem cursor_monotone (s s' : KVState) (hinv : kv_inv s)
    (hstep : ∃ i, (kvstore.actions i).fires s s') (r : Replica) :
    s.cursor r ≤ s'.cursor r := by
  obtain ⟨i, hfire⟩ := hstep
  cases i with
  | acquire r' =>
    obtain ⟨_, ht⟩ := hfire; dsimp only [kvstore] at ht; subst ht; simp
  | writeFail r' =>
    obtain ⟨_, ht⟩ := hfire; dsimp only [kvstore] at ht; subst ht; simp
  | writeOk r' =>
    obtain ⟨_, ht⟩ := hfire; dsimp only [kvstore] at ht
    obtain ⟨v, ht⟩ := ht; subst ht; dsimp only
    by_cases h : r = r'
    · subst h; simp; exact Nat.le_succ_of_le (hinv.1 r)
    · simp [h]
  | consume r' =>
    obtain ⟨_, ht⟩ := hfire; dsimp only [kvstore] at ht
    obtain ⟨v, _, ht⟩ := ht; subst ht; dsimp only
    by_cases h : r = r'
    · subst h; simp
    · simp [h]

/-! #### Write Linearizability via Refinement Mapping -/

/-- The sequential single-key store specification.
    State is `Option Value`; the only action is writing a new value. -/
def SeqKV : Spec (Option Value) where
  init := fun v => v = none
  next := fun _ v' => ∃ w : Value, v' = some w

/-- Refinement mapping: project to the last journal entry. -/
def kv_abs : KVState → Option Value :=
  fun s => s.journal.getLast?

private theorem getLast?_append_singleton (l : List α) (a : α) :
    (l ++ [a]).getLast? = some a := by
  rw [List.getLast?_eq_some_getLast (by simp)]; simp

/-- **Write linearizability**: the distributed KV store refines the
    sequential single-key store (with stuttering).  Every `writeOk`
    maps to a sequential write; all other actions stutter. -/
theorem kv_write_linearizable :
    refines_via kv_abs kvstore.toSpec.safety SeqKV.safety_stutter := by
  apply refinement_mapping_stutter kvstore.toSpec SeqKV kv_abs
  · -- Init: journal is empty, so getLast? = none
    intro s ⟨hj, _⟩
    simp [kv_abs, SeqKV, hj]
  · -- Next: each action either writes (abstract step) or stutters
    intro s s' ⟨i, hfire⟩
    cases i with
    | acquire r =>
      obtain ⟨_, ht⟩ := hfire; dsimp only [kvstore] at ht; subst ht
      right; rfl
    | writeFail r =>
      obtain ⟨_, ht⟩ := hfire; dsimp only [kvstore] at ht; subst ht
      right; rfl
    | writeOk r =>
      obtain ⟨_, ht⟩ := hfire; dsimp only [kvstore] at ht
      obtain ⟨v, ht⟩ := ht; subst ht
      left; exact ⟨v, by rw [kv_abs, getLast?_append_singleton]⟩
    | consume r =>
      obtain ⟨_, ht⟩ := hfire; dsimp only [kvstore] at ht
      obtain ⟨v, _, ht⟩ := ht; subst ht
      right; rfl

/-! #### Read-Your-Writes -/

/-- **Read-your-writes**: after a successful write, the writer's store
    equals the latest journal entry and its cursor is fully caught up. -/
theorem read_your_writes (s s' : KVState) (r : Replica)
    (hfire : (kvstore.actions (.writeOk r)).fires s s') :
    s'.store r = s'.journal.getLast? ∧ s'.cursor r = s'.journal.length := by
  obtain ⟨_, ht⟩ := hfire
  dsimp only [kvstore] at ht
  obtain ⟨v, ht⟩ := ht; subst ht
  simp

end KVStore
