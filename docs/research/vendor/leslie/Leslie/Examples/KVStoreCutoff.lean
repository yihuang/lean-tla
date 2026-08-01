import Leslie.Examples.KVStore

/-! ## Small Model Theorem for Journal-Based Key-Value Stores

    ### What this file proves

    Any bug in a journal-based key-value store can be caught by a
    **single consume test**: write one value `v`, consume it, check
    that the store holds `some v`.

    More precisely, we prove three results:

    1. **Small model** (`small_model'`): if `full_safe` (per-replica
       consistency + write-serialization) is violated in *any*
       n-node execution of *any* length, then the `consume_test`
       fails — a 2-step witness exists.

    2. **Node cutoff** (`simulation`): any n-node reachable state
       has a 2-node counterpart with the same journal and witness
       local state.

    3. **Journal provenance** (`journal_by_writes_always`): every
       reachable journal was built entirely by `write_act` steps.
       No out-of-thin-air values. This is an independent structural
       theorem following from `ax_writes_only`.

    ### Proof architecture

    **Trace bound** (§ Trace Bound, needs `TraceAxioms` + `consume_test`):

    The per-replica invariant is inductive. The proof is by induction
    on reachability, with three cases:

    - *Write by the witness*: by `write_preserves`, (store, cursor)
      are unchanged. The journal only grew by appending, so
      `journal'[cursor-1]? = journal[cursor-1]?`. Trivially preserved.
    - *Consume by the witness*: `consume_replay` transfers the
      consume result from the 2-step test to the current context;
      `consume_nontrivial` ensures the test is non-vacuous.
    - *Action by another replica*: the witness's local state is
      unchanged; the journal only grows by appending.

    **Node cutoff** (§ Node Cutoff, needs only core axioms):

    The simulation replays the witness replica's actions and uses
    a builder replica to reproduce the journal via `acquire_act` +
    `write_act`. Locality ensures the builder's state doesn't
    interfere with the witness.

    **Journal provenance** (§ Combined, needs `ax_writes_only`):

    By `ax_writes_only`, every journal-modifying step uses
    `write_act r v`. The `JournalByWrites` inductive tracks this
    through the execution. Proved for all reachable states by
    induction.

    ### Modeling shared state

    Shared state (leadership) is absorbed into the nondeterminism
    of `next`. The `acquire_act` models leadership acquisition
    (always enabled, preserves store/cursor). Writes require a
    prior acquire (`ax_write_after_acquire`). This avoids explicit
    shared state while keeping the leadership protocol visible.

    ### What this does *not* prove

    - **Realization**: the converse (oracle bug → real bug) would
      require showing oracle schedules are realizable.

    - **Liveness**: we prove safety only.

    ### Summary of results

    | Theorem                    | Statement                                |
    |----------------------------|------------------------------------------|
    | `simulation`               | n-node state → 2-node state, same (j, r) |
    | `node_cutoff`              | per-replica violation → 2-node violation  |
    | `node_cutoff_serial`       | write-serial violation → 2-node violation |
    | `trace_invariant`          | TraceAxioms + consume_test → invariant    |
    | `journal_by_writes_always` | ax_writes_only → no out-of-thin-air       |
    | `full_safe_always`         | TraceAxioms + consume_test → full_safe    |
    | `small_model'`             | full_safe violation → consume_test fails  |
    | `small_model_witness`      | full_safe violation → explicit witness    |
    | `buggy_has_bug`            | buggy KV store violates full_safe         |
    | `buggy_caught`             | small model theorem catches the bug       |
-/

namespace JournalKV

/-! ### Abstract Interface

    A `Spec` captures any journal-based KV store.

    **No explicit shared state.** Leadership, epoch numbers, etc.
    are absorbed into the nondeterminism of `next`. Leadership
    acquisition is modeled by `acquire_act` (always enabled,
    preserves store/cursor). Writes require a prior acquire
    (`ax_write_after_acquire`), and `ax_writes_only` ensures
    that `write_act` is the only way to grow the journal.

    **State decomposition:**
    - A shared **journal** (`List V`): the append-only log.
    - Per-replica **local state** (`Local`): the local store,
      cursor, and any implementation-specific auxiliary data.

    **Locality** is structural: `next` takes one replica's local
    state and produces one replica's new local state. Other replicas
    are untouched by construction.
-/

structure Spec (R V : Type) where
  /-- Per-replica local state (store, cursor, aux). -/
  Local : Type
  /-- Action index type. -/
  Act : Type
  /-- Which replica performs the action. -/
  actor : Act → R
  /-- Initial local state predicate. -/
  init : Local → Prop
  /-- Transition relation.
      `next a j l (l', sfx)` means: action `a`, seeing journal `j`
      and local state `l`, can produce new local state `l'` and
      journal suffix `sfx` (appended to `j`).

      The relation is nondeterministic: multiple `(l', sfx)` pairs
      may be possible for the same `(a, j, l)`, modeling different
      shared-state contexts (e.g., whether the replica holds the
      leadership lease). -/
  next : Act → List V → Local → Local × List V → Prop
  /-- Project the key-value store from local state. -/
  proj_store : Local → Option V
  /-- Project the journal cursor from local state. -/
  proj_cursor : Local → Nat

  -- ═══════════════════ Core axioms ═══════════════════

  /-- Cursor starts at 0. -/
  ax_init_cursor : ∀ l, init l → proj_cursor l = 0
  /-- Store starts empty. -/
  ax_init_store : ∀ l, init l → proj_store l = none
  /-- At least one initial state exists. -/
  ax_init_exists : ∃ l, init l
  /-- Cursor never exceeds journal length. -/
  ax_cursor_bound : ∀ a j l l' sfx,
    next a j l (l', sfx) → proj_cursor l ≤ j.length →
    proj_cursor l' ≤ (j ++ sfx).length
  /-- A distinguished leadership-acquisition action per replica. -/
  acquire_act : R → Act
  /-- `acquire_act r` is attributed to `r`. -/
  ax_acquire_actor : ∀ r, actor (acquire_act r) = r
  /-- **Acquire is always enabled**: any replica can acquire
      leadership from any state, without modifying the journal. -/
  ax_acquire_enabled : ∀ r j l, ∃ l', next (acquire_act r) j l (l', [])
  /-- Acquire does not change the store. -/
  ax_acquire_store : ∀ r j l l',
    next (acquire_act r) j l (l', []) → proj_store l' = proj_store l
  /-- Acquire does not change the cursor. -/
  ax_acquire_cursor : ∀ r j l l',
    next (acquire_act r) j l (l', []) → proj_cursor l' = proj_cursor l
  /-- A distinguished write action per replica and value. -/
  write_act : R → V → Act
  /-- `write_act r v` is attributed to `r`. -/
  ax_write_actor : ∀ r v, actor (write_act r v) = r
  /-- **Write after acquire**: after acquiring leadership, a replica
      can append any single value to the journal. This models the
      two-step pattern `acquire` then `writeOk` from the concrete
      `kvstore`. -/
  ax_write_after_acquire : ∀ r v j l l_acq,
    next (acquire_act r) j l (l_acq, []) →
    ∃ l', next (write_act r v) j l_acq (l', [v])
  /-- The ONLY way to grow the journal is through `write_act`.
      No out-of-thin-air values. -/
  ax_writes_only : ∀ a j l l' sfx,
    next a j l (l', sfx) → sfx ≠ [] →
    ∃ r v, a = write_act r v ∧ sfx = [v]

/-! ### System State and Dynamics

    The full system state pairs the shared journal with a function
    mapping each replica to its local state. The `fires` relation
    updates one replica's local state and appends to the journal;
    other replicas' local states are unchanged (locality by construction).
-/

variable {R V : Type} [DecidableEq R] [DecidableEq V]

/-- The full system state: a journal and per-replica local states. -/
structure State (spec : Spec R V) where
  journal : List V
  locals : R → spec.Local

/-- An action `a` fires on state `s` to produce `s'`: the acting
    replica's local state updates, a suffix is appended to the
    journal, and all other replicas' local states are unchanged
    (locality by construction). -/
def Spec.fires (spec : Spec R V) (a : spec.Act)
    (s s' : State spec) : Prop :=
  ∃ l' sfx,
    spec.next a s.journal (s.locals (spec.actor a)) (l', sfx) ∧
    s'.journal = s.journal ++ sfx ∧
    s'.locals = fun r => if r = spec.actor a then l' else s.locals r

/-- Reachability: the reflexive-transitive closure of `fires`. -/
inductive Reachable (spec : Spec R V) :
    State spec → Prop where
  | init (s : State spec) :
      s.journal = [] → (∀ r, spec.init (s.locals r)) → Reachable spec s
  | step (s s' : State spec) (a : spec.Act) :
      Reachable spec s → spec.fires a s s' → Reachable spec s'

/-- Reachability restricted to a subset of replicas. -/
inductive ReachableBy (spec : Spec R V)
    (allowed : R → Prop) : State spec → Prop where
  | init (s : State spec) :
      s.journal = [] → (∀ r, spec.init (s.locals r)) →
      ReachableBy spec allowed s
  | step (s s' : State spec) (a : spec.Act) :
      ReachableBy spec allowed s → allowed (spec.actor a) →
      spec.fires a s s' → ReachableBy spec allowed s'

/-! ### Safety Properties

    Three properties:

    1. **Per-replica invariant** (`per_replica_ok`): each replica's
       local store matches the journal at its cursor position.

    2. **Write-serialization** (`write_serial_ok`): two replicas at
       the same cursor position agree on the stored value.
       A consequence of the per-replica invariant.

    3. **Journal provenance** (`JournalByWrites`): every journal
       entry traces back to a `write_act` step. No out-of-thin-air
       values. Proved independently from `ax_writes_only`.

    Properties 1–2 form `full_safe` (the target of the small model
    theorem). Property 3 is a standalone structural guarantee.
-/

/-- Per-replica consistency: if `cursor > 0`, the stored value
    equals the journal entry at `cursor - 1`. -/
def per_replica_ok (spec : Spec R V) (s : State spec) (r : R) : Prop :=
  spec.proj_cursor (s.locals r) > 0 →
  spec.proj_store (s.locals r) = s.journal[spec.proj_cursor (s.locals r) - 1]?

/-- Write-serialization: two replicas at the same cursor agree. -/
def write_serial_ok (spec : Spec R V) (s : State spec) (r₁ r₂ : R) : Prop :=
  spec.proj_cursor (s.locals r₁) > 0 →
  spec.proj_cursor (s.locals r₂) > 0 →
  spec.proj_cursor (s.locals r₁) = spec.proj_cursor (s.locals r₂) →
  spec.proj_store (s.locals r₁) = spec.proj_store (s.locals r₂)

/-- Execution-level provenance: every journal entry traces back to
    a `write_act` step. No out-of-thin-air values. -/
inductive JournalByWrites (spec : Spec R V) : State spec → Prop where
  | init (s : State spec) :
      s.journal = [] → (∀ r, spec.init (s.locals r)) →
      JournalByWrites spec s
  | step_idle (s s' : State spec) (a : spec.Act) :
      JournalByWrites spec s →
      spec.fires a s s' →
      s'.journal = s.journal →
      JournalByWrites spec s'
  | step_write (s s' : State spec) (r : R) (v : V) :
      JournalByWrites spec s →
      spec.fires (spec.write_act r v) s s' →
      s'.journal = s.journal ++ [v] →
      JournalByWrites spec s'

/-- Full safety: per-replica consistency + write-serialization. -/
def full_safe (spec : Spec R V) (s : State spec) : Prop :=
  (∀ r, per_replica_ok spec s r) ∧
  (∀ r₁ r₂, write_serial_ok spec s r₁ r₂)

omit [DecidableEq R] [DecidableEq V] in
/-- Write-serialization follows from the per-replica invariant:
    both stores equal the same journal entry. -/
theorem per_replica_implies_serial (spec : Spec R V) (s : State spec)
    (h₁ : per_replica_ok spec s r₁) (h₂ : per_replica_ok spec s r₂) :
    write_serial_ok spec s r₁ r₂ :=
  fun hc₁ hc₂ heq => by rw [h₁ hc₁, h₂ hc₂, heq]

omit [DecidableEq R] [DecidableEq V] in
/-- Contrapositive: a write-serialization violation implies a
    per-replica violation for at least one of the two replicas. -/
theorem serial_violation_implies_per_replica (spec : Spec R V)
    (s : State spec) (hv : ¬ write_serial_ok spec s r₁ r₂) :
    ¬ per_replica_ok spec s r₁ ∨ ¬ per_replica_ok spec s r₂ := by
  -- Assume both hold, derive contradiction with the serialization violation
  by_contra h
  rw [not_or] at h
  have h1 := Classical.byContradiction fun c => h.1 c
  have h2 := Classical.byContradiction fun c => h.2 c
  exact hv (per_replica_implies_serial spec s h1 h2)

/-! ### Node Cutoff

    **Goal**: any reachable state of the n-node system has a
    counterpart reachable by just two replicas {r, b} with the same
    journal and the same local state for the witness replica r.

    **Proof idea**: walk through the original execution step by step.

    - If the current action is by `r`: replay it on the simulated
      state. The journal and `r`'s local state match, so the same
      transition is available.

    - If the current action is by another replica and modifies the
      journal: use the builder `b` to write the same entries via
      `acquire_act` + `write_act`. The builder's local state is
      corrupted, but we don't care — only `r`'s state matters.

    - If the current action is by another replica and does NOT
      modify the journal: skip it. By locality, `r`'s state and
      the journal are unchanged.
-/

omit [DecidableEq V] in
/-- Helper: the builder can grow the journal by any suffix,
    without affecting the witness's local state. -/
private theorem builder_writes (spec : Spec R V)
    (r b : R) (hrb : r ≠ b) (sfx : List V)
    (t : State spec) (ht : ReachableBy spec (fun x => x = r ∨ x = b) t) :
    ∃ t' : State spec,
      ReachableBy spec (fun x => x = r ∨ x = b) t' ∧
      t'.journal = t.journal ++ sfx ∧
      t'.locals r = t.locals r := by
  -- Induction on the suffix: append one value at a time via acquire + write
  induction sfx generalizing t with
  | nil => exact ⟨t, ht, by simp, rfl⟩
  | cons v vs ih =>
    -- Step 1: builder acquires leadership
    obtain ⟨l_acq, hacq⟩ := spec.ax_acquire_enabled b t.journal (t.locals b)
    let t_acq : State spec :=
      ⟨t.journal, fun r' => if r' = b then l_acq else t.locals r'⟩
    have ht_acq : ReachableBy spec (fun x => x = r ∨ x = b) t_acq := by
      apply ReachableBy.step t t_acq (spec.acquire_act b) ht
      · show spec.actor (spec.acquire_act b) = r ∨ spec.actor (spec.acquire_act b) = b
        rw [spec.ax_acquire_actor]; exact Or.inr rfl
      · refine ⟨l_acq, [], ?_, ?_, ?_⟩
        · rw [spec.ax_acquire_actor]; exact hacq
        · simp [t_acq]
        · funext r'; simp only [t_acq, spec.ax_acquire_actor]
    -- Step 2: builder writes v (enabled because it just acquired)
    obtain ⟨l_b', hwrite⟩ := spec.ax_write_after_acquire b v t.journal (t.locals b) l_acq hacq
    let t₁ : State spec :=
      ⟨t.journal ++ [v], fun r' => if r' = b then l_b' else t.locals r'⟩
    have ht₁ : ReachableBy spec (fun x => x = r ∨ x = b) t₁ := by
      apply ReachableBy.step t_acq t₁ (spec.write_act b v) ht_acq
      · show spec.actor (spec.write_act b v) = r ∨ spec.actor (spec.write_act b v) = b
        rw [spec.ax_write_actor]; exact Or.inr rfl
      · -- t_acq.locals b = l_acq, and write fires from l_acq
        have hlacq : t_acq.locals (spec.actor (spec.write_act b v)) = l_acq := by
          show (if spec.actor (spec.write_act b v) = b then l_acq else _) = l_acq
          rw [spec.ax_write_actor, if_pos rfl]
        refine ⟨l_b', [v], ?_, rfl, ?_⟩
        · rw [hlacq]; exact hwrite
        · funext r'; show (if r' = b then l_b' else t.locals r') =
            if r' = spec.actor (spec.write_act b v) then l_b'
            else (if r' = b then l_acq else t.locals r')
          rw [spec.ax_write_actor]
          split <;> rfl
    -- r's local state is unaffected through both steps (r ≠ b)
    have ht₁_local : t₁.locals r = t.locals r := by
      show (if r = b then l_b' else t.locals r) = t.locals r
      split
      · next h => exact absurd h hrb
      · rfl
    -- Continue with the remaining suffix
    obtain ⟨t', ht', htj', htl'⟩ := ih t₁ ht₁
    exact ⟨t', ht',
           by rw [htj']; simp [t₁, List.append_assoc],
           by rw [htl', ht₁_local]⟩

omit [DecidableEq V] in
/-- **Simulation lemma**: for any reachable state `s`, there exists a
    state reachable by `{r, b}` alone that has the same journal and
    the same local state for the witness replica `r`. -/
theorem simulation (spec : Spec R V)
    (r b : R) (hrb : r ≠ b) (s : State spec) (hs : Reachable spec s) :
    ∃ t : State spec,
      ReachableBy spec (fun x => x = r ∨ x = b) t ∧
      t.journal = s.journal ∧
      t.locals r = s.locals r := by
  -- Induction on the reachability derivation
  induction hs with
  | init s hj hinit =>
    -- Both systems start from the same initial state
    exact ⟨s, .init s hj hinit, rfl, rfl⟩
  | step s s' a _ hstep ih =>
    obtain ⟨t, ht, ht_j, ht_l⟩ := ih
    obtain ⟨l', sfx, hnext, hj', hlocals'⟩ := hstep
    -- Case split: is the current action by the witness r?
    by_cases hactor : spec.actor a = r
    · -- Case 1: action is by r — replay it directly on the simulated state.
      -- Since journal and r's local state match, the same transition fires.
      let t' : State spec :=
        ⟨t.journal ++ sfx, fun r' => if r' = r then l' else t.locals r'⟩
      have ht'_fires : spec.fires a t t' := by
        refine ⟨l', sfx, ?_, rfl, ?_⟩
        · -- Rewrite the actor to r, then use matching journal and local state
          have : t.locals (spec.actor a) = s.locals (spec.actor a) := by
            rw [hactor, ht_l]
          rw [this, ht_j]; exact hnext
        · funext r'; simp only [t']; rw [hactor]
      exact ⟨t', .step t t' a ht (Or.inl hactor) ht'_fires,
             by simp [t', hj', ht_j],
             by simp [t', hlocals', hactor]⟩
    · -- Case 2: action is by another replica.
      -- r's local state is unchanged (locality). The builder grows
      -- the journal by the same suffix via ax_write_any.
      have hlr : s'.locals r = s.locals r := by
        rw [hlocals']; simp [Ne.symm hactor]
      obtain ⟨t', ht', htj', htl'⟩ := builder_writes spec r b hrb sfx t ht
      exact ⟨t', ht',
             by rw [htj', ht_j, hj'],
             by rw [htl', ht_l, hlr]⟩

omit [DecidableEq V] in
/-- **Node cutoff (per-replica)**: if the per-replica invariant is
    violated for replica `r` in some n-node reachable state, then it
    is also violated in a state reachable by just `{r, b}`. -/
theorem node_cutoff (spec : Spec R V)
    (r b : R) (hrb : r ≠ b) (s : State spec) (hs : Reachable spec s)
    (hviol : ¬ per_replica_ok spec s r) :
    ∃ t : State spec,
      ReachableBy spec (fun x => x = r ∨ x = b) t ∧
      ¬ per_replica_ok spec t r := by
  -- The simulated state has the same (journal, locals r), so the
  -- violation transfers.
  obtain ⟨t, ht, ht_j, ht_l⟩ := simulation spec r b hrb s hs
  exact ⟨t, ht, fun h => hviol (fun hc => by
    have := h (by rw [ht_l]; exact hc)
    rwa [ht_l, ht_j] at this)⟩

omit [DecidableEq V] in
/-- **Node cutoff (write-serialization)**: reduces to per-replica
    via `serial_violation_implies_per_replica`. -/
theorem node_cutoff_serial (spec : Spec R V)
    (r₁ r₂ b : R) (h₁b : r₁ ≠ b) (h₂b : r₂ ≠ b)
    (s : State spec) (hs : Reachable spec s)
    (hviol : ¬ write_serial_ok spec s r₁ r₂) :
    (∃ t, ReachableBy spec (fun x => x = r₁ ∨ x = b) t ∧
      ¬ per_replica_ok spec t r₁) ∨
    (∃ t, ReachableBy spec (fun x => x = r₂ ∨ x = b) t ∧
      ¬ per_replica_ok spec t r₂) := by
  -- Split the serialization violation into a per-replica violation for r₁ or r₂
  rcases serial_violation_implies_per_replica spec s hviol with h | h
  · exact Or.inl (node_cutoff spec r₁ b h₁b s hs h)
  · exact Or.inr (node_cutoff spec r₂ b h₂b s hs h)

/-! ### Trace Axioms

    Four structural axioms about individual transitions. These are
    properties of the *implementation*, easily verifiable by inspection:

    1. **Write preserves**: journal-modifying actions do NOT touch
       (store, cursor). The written value reaches the local store
       later via a regular consume, just like any other replica.
       This is the general pattern; "read-your-own-writes" is a
       special-case optimization, not the default.

    2. **Consume cursor**: a consume advances the cursor by exactly 1.

    3. **Consume replay**: the consume store result depends only on
       the journal entry value.

    4. **Consume nontrivial**: a meaningful consume is meaningful
       in every context.

    Under these axioms, writes trivially preserve the invariant
    (store and cursor are unchanged, journal only grew by appending,
    earlier entries are unaffected). The *only* source of per-replica
    violations is a buggy consume.
-/

structure TraceAxioms (spec : Spec R V) : Prop where
  /-- **Write preserves**: journal-modifying actions (sfx ≠ []) do
      not change (store, cursor). The writer appends to the journal
      but its local store only updates later via consume. -/
  write_preserves : ∀ a j l l' sfx,
    spec.next a j l (l', sfx) → sfx ≠ [] →
    spec.proj_store l' = spec.proj_store l ∧
    spec.proj_cursor l' = spec.proj_cursor l
  /-- **Consume cursor**: a consume that changes (store, cursor)
      advances the cursor by exactly 1. -/
  consume_cursor : ∀ a j l l',
    spec.next a j l (l', []) →
    (spec.proj_store l' ≠ spec.proj_store l ∨
     spec.proj_cursor l' ≠ spec.proj_cursor l) →
    spec.proj_cursor l' = spec.proj_cursor l + 1
  /-- **Consume replay**: the consume store result depends only on
      the entry value at the cursor position. If the same action
      fires from a different (journal, local) context with the same
      entry at the cursor, the resulting store is identical. -/
  consume_replay : ∀ a j₁ j₂ l₁ l₂ l₁',
    spec.next a j₁ l₁ (l₁', []) →
    (spec.proj_store l₁' ≠ spec.proj_store l₁ ∨
     spec.proj_cursor l₁' ≠ spec.proj_cursor l₁) →
    spec.proj_cursor l₁ < j₁.length →
    spec.proj_cursor l₂ < j₂.length →
    j₁[spec.proj_cursor l₁]? = j₂[spec.proj_cursor l₂]? →
    ∃ l₂', spec.next a j₂ l₂ (l₂', []) ∧
      spec.proj_store l₂' = spec.proj_store l₁'
  /-- **Consume nontrivial**: if a consume changes (store, cursor)
      when the cursor is in bounds, it also changes them in any
      other in-bounds context. This allows a consume to be a no-op
      when `cursor ≥ journal.length` (nothing to read). -/
  consume_nontrivial : ∀ a j₁ j₂ l₁ l₂ l₁' l₂',
    spec.next a j₁ l₁ (l₁', []) →
    spec.next a j₂ l₂ (l₂', []) →
    (spec.proj_store l₁' ≠ spec.proj_store l₁ ∨
     spec.proj_cursor l₁' ≠ spec.proj_cursor l₁) →
    spec.proj_cursor l₁ < j₁.length →
    spec.proj_cursor l₂ < j₂.length →
    (spec.proj_store l₂' ≠ spec.proj_store l₂ ∨
     spec.proj_cursor l₂' ≠ spec.proj_cursor l₂)

/-! ### Consume Test

    The **consume test** is a 2-step execution:
    1. Builder writes value `v` → journal = `[v]`.
    2. Witness (at cursor 0) consumes `v` → check `store = some v`.

    This is the ONLY test needed. If it passes for every value `v`
    and every consume action `a`, then the system is correct for all
    `n` and all trace lengths.
-/

/-- A consume action that fires on an initial local state with
    journal `[v]` and changes (store, cursor) must produce
    `store = some v`. This is the single test the small model
    theorem reduces correctness to. -/
def consume_test (spec : Spec R V) : Prop :=
  ∀ (a : spec.Act) (v : V) (l₀ l₁ : spec.Local),
    spec.init l₀ →
    spec.next a [v] l₀ (l₁, []) →
    (spec.proj_store l₁ ≠ spec.proj_store l₀ ∨
     spec.proj_cursor l₁ ≠ spec.proj_cursor l₀) →
    spec.proj_store l₁ = some v

/-! ### Trace Bound: Inductive Invariant

    The core technical lemma: under `TraceAxioms`, the per-replica
    invariant is inductive (preserved by every transition), provided
    the `consume_test` passes.

    The proof is by induction on `Reachable`. At each step:

    - **Write by the witness**: by `write_preserves`, (store, cursor)
      are unchanged. The journal only grew by appending, so
      `journal'[cursor-1]? = journal[cursor-1]?`. Invariant preserved
      trivially.

    - **Consume by the witness** (the interesting case):
      1. The consume reads entry `v = journal[cursor]`.
      2. By `consume_replay`, replaying the same action on journal
         `[v]` from the initial state produces the same store.
      3. By `consume_nontrivial`, the replay changes (store, cursor).
      4. By `consume_test`, the replayed store is `some v`.
      5. By `consume_cursor`, the new cursor is `cursor + 1`.
      6. Therefore `store = some v = journal[cursor] = journal[cursor'-1]?`.

    - **Action by another replica**: the witness's local state is
      unchanged. The journal grows by appending, so `journal[cursor-1]?`
      is preserved (the cursor points to an earlier entry).
-/

/-- Combined invariant: cursor bounded + per-replica correct. -/
private def safe (spec : Spec R V) (s : State spec) : Prop :=
  (∀ r, spec.proj_cursor (s.locals r) ≤ s.journal.length) ∧
  (∀ r, per_replica_ok spec s r)

set_option linter.unusedSectionVars false in
set_option linter.unusedSimpArgs false in
/-- **Trace invariant**: if `TraceAxioms` hold and every single-entry
    consume test passes, then the per-replica invariant holds in every
    reachable state. This is the heart of the small model theorem:
    correctness of arbitrarily long traces reduces to a single
    consume test. -/
theorem trace_invariant (spec : Spec R V)
    (tax : TraceAxioms spec) (htest : consume_test spec)
    (s : State spec) (hs : Reachable spec s) :
    safe spec s := by
  induction hs with
  | init s hj hinit =>
    -- Base case: cursor = 0, invariant holds vacuously.
    exact ⟨fun r => by rw [spec.ax_init_cursor _ (hinit r), hj]; simp,
           fun r hc => by rw [spec.ax_init_cursor _ (hinit r)] at hc; omega⟩
  | step s s' a hs_reach hstep ih =>
    obtain ⟨hcb, hprok⟩ := ih
    obtain ⟨l', sfx, hnext, hj', hlocals'⟩ := hstep
    have hloc_eq : ∀ r', s'.locals r' =
        if r' = spec.actor a then l' else s.locals r' := by
      intro r'; rw [hlocals']
    refine ⟨?_, ?_⟩
    · ---- Part 1: Cursor bounded ----
      intro r'
      rw [hloc_eq]
      by_cases ha : r' = spec.actor a
      · -- Acting replica: use ax_cursor_bound
        rw [if_pos ha, hj']
        exact spec.ax_cursor_bound a s.journal _ l' sfx hnext (ha ▸ hcb r')
      · -- Other replica: cursor unchanged, journal only grew
        rw [if_neg ha, hj']
        have := hcb r'; simp [List.length_append]; omega
    · ---- Part 2: Per-replica OK ----
      intro r' hcursor
      rw [hloc_eq] at hcursor ⊢
      by_cases ha : r' = spec.actor a
      · ---- Sub-case: action is by r' ----
        rw [if_pos ha] at hcursor ⊢
        subst ha
        by_cases hsfx : sfx = []
        · ---- Non-writing action (consume or no-op) ----
          have hj'_eq : s'.journal = s.journal := by rw [hj', hsfx, List.append_nil]
          rw [hj'_eq]
          have hnext' : spec.next a s.journal (s.locals (spec.actor a)) (l', []) := by
            rw [← hsfx]; exact hnext
          by_cases hchange :
              spec.proj_store l' ≠ spec.proj_store (s.locals (spec.actor a)) ∨
              spec.proj_cursor l' ≠ spec.proj_cursor (s.locals (spec.actor a))
          · ---- Meaningful consume: the key case ----
            -- Step 1: cursor advanced by 1
            have hc_adv := tax.consume_cursor a s.journal (s.locals (spec.actor a)) l'
              hnext' hchange
            -- Step 2: old cursor < journal length (from cursor bound + advance)
            have hc_lt : spec.proj_cursor (s.locals (spec.actor a)) < s.journal.length := by
              have hbound := spec.ax_cursor_bound a s.journal (s.locals (spec.actor a)) l' [] hnext' (hcb (spec.actor a))
              simp at hbound; omega
            -- Step 3: the journal entry at cursor is well-defined
            have hentry := List.getElem?_eq_getElem hc_lt
            have hval : s.journal[spec.proj_cursor (s.locals (spec.actor a))]? =
              some s.journal[spec.proj_cursor (s.locals (spec.actor a))] := hentry
            -- Step 4: replay the consume on journal [v] from initial state
            obtain ⟨l₀, hl₀⟩ := spec.ax_init_exists
            have hc0 : spec.proj_cursor l₀ = 0 := spec.ax_init_cursor l₀ hl₀
            have hc0_lt : spec.proj_cursor l₀ <
                [s.journal[spec.proj_cursor (s.locals (spec.actor a))]].length := by
              rw [hc0]; simp
            have hentries : s.journal[spec.proj_cursor (s.locals (spec.actor a))]? =
                ([s.journal[spec.proj_cursor (s.locals (spec.actor a))]] : List V)[spec.proj_cursor l₀]? := by
              rw [hc0]; simp
            -- consume_replay: the replayed consume produces the same store
            obtain ⟨l₂', hl₂'_next, hl₂'_store⟩ :=
              tax.consume_replay a s.journal
                [s.journal[spec.proj_cursor (s.locals (spec.actor a))]]
                (s.locals (spec.actor a)) l₀ l'
                hnext' hchange hc_lt hc0_lt hentries
            -- consume_nontrivial: the replay also changes (store, cursor)
            have hl₂'_change := tax.consume_nontrivial a s.journal
              [s.journal[spec.proj_cursor (s.locals (spec.actor a))]]
              (s.locals (spec.actor a)) l₀ l' l₂' hnext' hl₂'_next hchange
              hc_lt hc0_lt
            -- Step 5: consume_test gives store = some v in the replay
            have htest_result := htest a
              s.journal[spec.proj_cursor (s.locals (spec.actor a))]
              l₀ l₂' hl₀ hl₂'_next hl₂'_change
            -- Step 6: transfer back — l' has the same store as l₂'
            rw [← hl₂'_store, htest_result, hc_adv, Nat.add_sub_cancel]
            exact hentry.symm
          · ---- No change in (store, cursor): invariant trivially preserved ----
            rw [not_or] at hchange
            obtain ⟨h1, h2⟩ := hchange
            rw [Decidable.not_not] at h1 h2
            -- Store and cursor unchanged, so the old invariant still holds
            rw [h1, h2]
            exact hprok (spec.actor a) (by omega)
        · ---- Writing action (sfx ≠ []) ----
          -- By write_preserves: store and cursor are unchanged
          have ⟨hst_eq, hcr_eq⟩ := tax.write_preserves a s.journal
            (s.locals (spec.actor a)) l' sfx hnext hsfx
          rw [hj', hst_eq, hcr_eq]
          -- journal only grew by appending; earlier entries are preserved
          have hprev := hprok (spec.actor a) (by rw [hcr_eq] at hcursor; exact hcursor)
          rw [hprev]
          have := hcb (spec.actor a)
          exact (List.getElem?_append_left (by omega)).symm
      · ---- Sub-case: action is by another replica ----
        rw [if_neg ha] at hcursor ⊢
        rw [hj']
        -- r's state is unchanged; journal only grew by appending.
        -- Earlier entries (at cursor - 1 < old journal length) are preserved.
        have hprev := hprok r' hcursor
        rw [hprev]
        have := hcb r'
        exact (List.getElem?_append_left (by omega)).symm

/-! ### Combined Small Model Theorem

    The main results:

    - `journal_by_writes_always`: every reachable journal was built
      by `write_act` steps (from `ax_writes_only`, no other axioms).

    - `full_safe_always`: under `TraceAxioms` + `consume_test`,
      `full_safe` (per-replica + write-serialization) holds for all
      reachable states.

    - `small_model'`: violation of `full_safe` → `consume_test` fails.
-/

omit [DecidableEq V] in
/-- Journal provenance holds for all reachable states. By induction
    on `Reachable`, using `ax_writes_only` to classify each step. -/
theorem journal_by_writes_always (spec : Spec R V)
    (s : State spec) (hs : Reachable spec s) :
    JournalByWrites spec s := by
  induction hs with
  | init s hj hinit =>
    exact JournalByWrites.init s hj hinit
  | step s s' a _ hfire ih =>
    obtain ⟨l', sfx, hnext, hj', hlocals'⟩ := hfire
    by_cases hsfx : sfx = []
    · -- sfx = []: journal unchanged
      exact JournalByWrites.step_idle s s' a ih
        ⟨l', sfx, hnext, hj', hlocals'⟩
        (by rw [hj', hsfx, List.append_nil])
    · -- sfx ≠ []: by ax_writes_only, a = write_act r v and sfx = [v]
      obtain ⟨r, v, ha_eq, hsfx_eq⟩ := spec.ax_writes_only a s.journal
        (s.locals (spec.actor a)) l' sfx hnext hsfx
      subst ha_eq
      have hfire' : spec.fires (spec.write_act r v) s s' :=
        ⟨l', sfx, hnext, hj', hlocals'⟩
      exact JournalByWrites.step_write s s' r v ih hfire'
        (by rw [hj', hsfx_eq])

/-- **Full safety theorem**: under `TraceAxioms` + `consume_test`,
    per-replica consistency and write-serialization hold for every
    reachable state. -/
theorem full_safe_always (spec : Spec R V)
    (tax : TraceAxioms spec) (htest : consume_test spec)
    (s : State spec) (hs : Reachable spec s) :
    full_safe spec s := by
  have ⟨_, hprok⟩ := trace_invariant spec tax htest s hs
  exact ⟨hprok,
         fun r₁ r₂ => per_replica_implies_serial spec s (hprok r₁) (hprok r₂)⟩

/-- Either the system is fully safe, or the consume test fails. -/
theorem small_model (spec : Spec R V)
    (tax : TraceAxioms spec) :
    (∀ s, Reachable spec s → full_safe spec s) ∨
    ¬ consume_test spec := by
  by_cases h : consume_test spec
  · exact Or.inl (fun s hs => full_safe_always spec tax h s hs)
  · exact Or.inr h

/-- **Main result**: a violation of any of the three safety properties
    in any n-node execution implies the 2-step consume test fails. -/
theorem small_model' (spec : Spec R V)
    (tax : TraceAxioms spec)
    (hbug : ∃ s, Reachable spec s ∧ ¬ full_safe spec s) :
    ¬ consume_test spec := by
  intro htest
  obtain ⟨s, hs, hviol⟩ := hbug
  exact hviol (full_safe_always spec tax htest s hs)

/-- Explicit witness extraction: a violation of full_safe yields a
    concrete action, value, and pair of local states such that
    consuming `v` from `[v]` gives `store ≠ some v`. -/
theorem small_model_witness (spec : Spec R V)
    (tax : TraceAxioms spec)
    (hbug : ∃ s, Reachable spec s ∧ ¬ full_safe spec s) :
    ∃ (a : spec.Act) (v : V) (l₀ l₁ : spec.Local),
      spec.init l₀ ∧
      spec.next a [v] l₀ (l₁, []) ∧
      (spec.proj_store l₁ ≠ spec.proj_store l₀ ∨
       spec.proj_cursor l₁ ≠ spec.proj_cursor l₀) ∧
      spec.proj_store l₁ ≠ some v := by
  have h := small_model' spec tax hbug
  unfold consume_test at h
  -- Push negation through ∀ and → to extract witnesses
  have ⟨a, h⟩ := Classical.not_forall.mp h
  have ⟨v, h⟩ := Classical.not_forall.mp h
  have ⟨l₀, h⟩ := Classical.not_forall.mp h
  have ⟨l₁, h⟩ := Classical.not_forall.mp h
  rw [not_imp] at h; obtain ⟨hinit, h⟩ := h
  rw [not_imp] at h; obtain ⟨hnext, h⟩ := h
  rw [not_imp] at h; obtain ⟨hchange, hne⟩ := h
  exact ⟨a, v, l₀, l₁, hinit, hnext, hchange, hne⟩

/-! ### Non-vacuity: Buggy KV Store

    We construct a concrete KV store with a deliberate bug:
    the consume action **always stores `v0`**, ignoring the
    actual journal entry.

    We show:
    1. The implementation satisfies all `TraceAxioms` (the bug is
       in the store value, not in the structural properties).
    2. The system has a reachable violation: after writing `v1` and
       consuming, the consumer stores `v0 ≠ v1`.
    3. The `consume_test` catches the bug: consuming `v1` from
       journal `[v1]` produces `v0 ≠ v1`.
    4. The small model theorem connects 2 and 3.
-/

namespace BuggyKV

open KVStore

instance : Inhabited Replica := ⟨.r1⟩

/-- Minimal local state: just store and cursor (no leadership). -/
structure BLocal where
  store : Option Value
  cursor : Nat
  deriving DecidableEq

inductive BAct where
  | acquire (r : Replica)
  | write (r : Replica) (v : Value)
  | consume (r : Replica)

def bActor : BAct → Replica
  | .acquire r | .write r _ | .consume r => r

/-- Buggy transition relation: consume always stores `v0`. A correct
    implementation would store `j[c]`. -/
def bNext : BAct → List Value → BLocal → BLocal × List Value → Prop
  | .acquire _, _, l, (l', sfx) =>
      l' = l ∧ sfx = []  -- acquire is a no-op on local state
  | .write _ v, _, l, (l', sfx) =>
      l' = l ∧ sfx = [v]
  | .consume _, j, ⟨_, c⟩, (l', sfx) =>
      c < j.length ∧
      l' = ⟨some .v0, c + 1⟩ ∧  -- BUG: should be `some j[c]`
      sfx = []

def buggySpec : Spec Replica Value where
  Local := BLocal
  Act := BAct
  actor := bActor
  init := fun l => l = ⟨none, 0⟩
  next := bNext
  proj_store := BLocal.store
  proj_cursor := BLocal.cursor
  ax_init_cursor := fun l h => by subst h; rfl
  ax_init_store := fun l h => by subst h; rfl
  ax_init_exists := ⟨⟨none, 0⟩, rfl⟩
  ax_cursor_bound := by
    intro a j l l' sfx hnext hbound
    cases a with
    | acquire r =>
      simp [bNext] at hnext; obtain ⟨hl', hsfx⟩ := hnext; subst hl' hsfx; simp; exact hbound
    | write r w =>
      simp only [bNext] at hnext
      obtain ⟨hl', hsfx⟩ := hnext; rw [hl']; subst hsfx; simp; omega
    | consume r =>
      match l with
      | ⟨s, c⟩ =>
        simp [bNext] at hnext
        obtain ⟨hlt, hl', hsfx⟩ := hnext; subst hl' hsfx; simp; omega
  acquire_act := fun r => .acquire r
  ax_acquire_actor := fun _ => rfl
  ax_acquire_enabled := by
    intro r j l; exact ⟨l, rfl, rfl⟩
  ax_acquire_store := by
    intro r j l l' hnext
    simp only [bNext] at hnext; exact hnext.1 ▸ rfl
  ax_acquire_cursor := by
    intro r j l l' hnext
    simp only [bNext] at hnext; exact hnext.1 ▸ rfl
  write_act := fun r v => .write r v
  ax_write_actor := fun _ _ => rfl
  ax_write_after_acquire := by
    intro r v j l l_acq hacq
    simp only [bNext] at hacq
    rw [hacq.1]
    exact ⟨l, rfl, rfl⟩
  ax_writes_only := by
    intro a j l l' sfx hnext hne
    cases a with
    | acquire r =>
      simp [bNext] at hnext; exact absurd hnext.2 hne
    | write r v =>
      simp only [bNext] at hnext
      obtain ⟨hl', hsfx⟩ := hnext
      exact ⟨r, v, rfl, hsfx⟩
    | consume r =>
      match l with
      | ⟨s, c⟩ =>
        simp [bNext] at hnext
        exact absurd hnext.2.2 hne

set_option linter.unusedSectionVars false in
set_option linter.unusedSimpArgs false in
/-- The buggy KV store satisfies all `TraceAxioms`. The bug is in the
    *value* stored by consume, not in the structural properties. -/
theorem buggy_trace_axioms : TraceAxioms buggySpec where
  write_preserves := by
    intro a j l l' sfx hnext hne
    cases a with
    | acquire r =>
      -- acquire has sfx = [] — contradicts hne
      simp only [buggySpec, bNext] at hnext; exact absurd hnext.2 hne
    | write r w =>
      -- write: l' = l (store/cursor unchanged), sfx = [v]
      change l' = l ∧ sfx = [w] at hnext
      obtain ⟨hl', _⟩ := hnext; subst hl'; exact ⟨rfl, rfl⟩
    | consume r =>
      -- consume has sfx = [] — contradicts hne
      match l with
      | ⟨s, c⟩ => simp [buggySpec, bNext] at hnext; exact absurd hnext.2.2 hne
  consume_cursor := by
    intro a j l l' hnext hchange
    cases a with
    | acquire r =>
      -- Acquire: l' = l, so (store, cursor) unchanged — contradicts hchange
      simp only [buggySpec, bNext] at hnext
      exfalso; rcases hchange with h | h <;> exact h (by rw [hnext.1])
    | write r v => exfalso; simp [buggySpec, bNext] at hnext
    | consume r =>
      match l with
      | ⟨s, c⟩ =>
        simp [buggySpec, bNext] at hnext
        rw [hnext.2]; rfl
  consume_replay := by
    intro a j₁ j₂ l₁ l₂ l₁' hnext₁ hchange hlt₁ hlt₂ hentry
    cases a with
    | acquire r =>
      simp only [buggySpec, bNext] at hnext₁
      exfalso; rcases hchange with h | h <;> exact h (by rw [hnext₁.1])
    | write r v => exfalso; simp [buggySpec, bNext] at hnext₁
    | consume r =>
      match l₁ with
      | ⟨s₁, c₁⟩ => match l₂ with
        | ⟨s₂, c₂⟩ =>
          simp [buggySpec, bNext] at hnext₁
          exact ⟨⟨some .v0, c₂ + 1⟩,
                 by simp [buggySpec, bNext]; exact hlt₂,
                 by rw [hnext₁.2]; rfl⟩
  consume_nontrivial := by
    intro a j₁ j₂ l₁ l₂ l₁' l₂' hn₁ hn₂ hch₁ _hlt₁ _hlt₂
    cases a with
    | acquire r =>
      simp only [buggySpec, bNext] at hn₁
      exfalso; rcases hch₁ with h | h <;> exact h (by rw [hn₁.1])
    | write r v => exfalso; simp [buggySpec, bNext] at hn₁
    | consume r =>
      match l₂ with
      | ⟨s₂, c₂⟩ =>
        simp [buggySpec, bNext] at hn₂
        rw [hn₂.2]; right; simp [buggySpec]

/-- The consume test fails: consuming value `v1` from
    journal `[v1]` produces store `some v0 ≠ some v1`. -/
theorem buggy_test_fails : ¬ consume_test buggySpec := by
  intro h
  -- Instantiate consume_test with action (consume r1), value v1
  have := h (.consume .r1) Value.v1 ⟨none, 0⟩ ⟨some .v0, 1⟩
    rfl
    (by simp [buggySpec, bNext])
    (by right; simp [buggySpec])
  -- store = some v0 ≠ some v1, contradiction
  simp [buggySpec] at this

/-- The buggy KV store has a reachable `full_safe` violation:
    `init → r1 acquires → r1 writes v1 → r2 consumes (gets v0)`. -/
theorem buggy_has_bug :
    ∃ s, Reachable buggySpec s ∧ ¬ full_safe buggySpec s := by
  let s₀ : State buggySpec := ⟨[], fun _ => ⟨none, 0⟩⟩
  have hs₀ : Reachable buggySpec s₀ := .init s₀ rfl (fun _ => rfl)
  -- Step 1: r1 acquires leadership (no-op on local state)
  have hstep_acq : buggySpec.fires (.acquire .r1) s₀ s₀ := by
    refine ⟨⟨none, 0⟩, [], ?_, by simp, ?_⟩
    · exact ⟨rfl, rfl⟩
    · funext r; cases r <;> rfl
  have hs₀' : Reachable buggySpec s₀ := .step s₀ s₀ _ hs₀ hstep_acq
  -- Step 2: r1 writes v1 (journal grows, but r1's local state unchanged)
  let s₁ : State buggySpec :=
    ⟨[.v1], fun _ => ⟨none, 0⟩⟩
  have hstep₁ : buggySpec.fires (.write .r1 .v1) s₀ s₁ := by
    refine ⟨⟨none, 0⟩, [.v1], ?_, ?_, ?_⟩
    · exact ⟨rfl, rfl⟩
    · rfl
    · funext r; cases r <;> rfl
  have hs₁ : Reachable buggySpec s₁ := .step s₀ s₁ _ hs₀' hstep₁
  -- Step 3: r2 consumes — BUG: stores v0 instead of v1
  let s₂ : State buggySpec :=
    ⟨[.v1], fun r => if r = .r2 then ⟨some .v0, 1⟩ else ⟨none, 0⟩⟩
  have hstep₂ : buggySpec.fires (.consume .r2) s₁ s₂ := by
    refine ⟨⟨some .v0, 1⟩, [], ?_, ?_, ?_⟩
    · exact ⟨by decide, rfl, rfl⟩
    · rfl
    · funext r; cases r <;> rfl
  have hs₂ : Reachable buggySpec s₂ := .step s₁ s₂ _ hs₁ hstep₂
  -- The violation is in per_replica_ok (component 1 of full_safe)
  refine ⟨s₂, hs₂, ?_⟩
  intro ⟨hpr, _⟩
  have := hpr .r2 (by show BLocal.cursor (s₂.locals .r2) > 0; decide)
  simp [s₂, buggySpec] at this

/-- The small model theorem **catches the bug**: `small_model'`
    applied to `buggy_has_bug` gives `¬ consume_test buggySpec`. -/
theorem buggy_caught : ¬ consume_test buggySpec :=
  small_model' buggySpec buggy_trace_axioms buggy_has_bug

end BuggyKV

end JournalKV
