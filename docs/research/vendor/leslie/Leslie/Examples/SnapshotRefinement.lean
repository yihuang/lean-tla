import Leslie.Action

/-! ## Linearizability of a Simplified Snapshot Object

    This file shows that a simplified version of the snapshot object
    defined by Afek et al. [1] is **linearizable**, i.e., it refines
    an atomic specification.  This is done in two phases:

    1. A **forward simulation** from the double-collect implementation
       to an intermediate object called the *Concurrent Specification*.
    2. A **backward simulation** from the Concurrent Specification to
       an *Atomic Specification*.

    Both proofs are **sorry-free** and include equality of return values
    in their simulation relations.

    [1] Afek, Y., Attiya, H., Dolev, D., Gafni, E., Merritt, M., and
        Shavit, N.  Atomic snapshots of shared memory.
        *J. ACM* 40, 4 (1993), 873–890.
-/

/-! ## Part 1: Forward Simulation (Implementation → Concurrent Specification)

    We prove that the double-collect snapshot implementation refines the
    Concurrent Specification via a forward simulation relation
    (cf. `SimulationRel` in `Leslie/Refinement.lean`).

    ### The snapshot object interface

    A snapshot object provides two operations on a shared array
    `mem : Fin n → Cell Val` of size `n`:

    - `update(i, data)`: write `data` to cell `i` (with incremented version).
    - `scan()`: return a consistent snapshot of the entire array.

    ### Implementation (concrete)

    Each cell carries a value **and a monotonically increasing version**.
    - `update(i, data)`: writes `⟨data, ver+1⟩` to `mem[i]`.
    - `scan()` uses **double collect**:
      1. First collect: read all cells one-by-one into `r1`.
      2. Repeat:  copy `r1` into `r2`;  re-read all cells into `r1`;
         if `r1 = r2` (both values and versions match), return `r1.vals`;
         else repeat.

    ### Concurrent Specification (abstract)

    - `update(i, data)`: same as the implementation.
    - `scan()`:
      1. Enter a `scanning` loop with an empty snapshot list.
      2. Nondeterministically take zero or more **atomic snapshots**
         of `mem` (each captured in a single step, appended to `snaps`).
      3. Return any element of `snaps`.

    ### Simulation relation (no ghost state variables)

    The relation `sim_rel` between concrete and abstract states has
    six conditions.  The key idea is condition (4): for each scanner
    in the repeat-collect phase, there exists a **witness**
    `gs_cells : Fin n → Cell Val` (full cells with versions)
    representing the snapshot taken at the start of this collect.
    This existential plays the role of a ghost variable but lives
    inside the relation, not in the concrete state.

    ### The version-sandwich argument

    When the double-collect succeeds (`r1 = r2` at `cmp_eq`), we must
    show that the witness `gs_cells` equals `r1` (and hence its values
    match the concrete return value).  The key insight:

    - **Lower bound**: `r2[i].ver ≤ gs_cells[i].ver` because `r2` was
      read *before* the snapshot, and versions only increase.
    - **Upper bound**: `gs_cells[i].ver ≤ r1[i].ver` because `r1` was
      read *after* the snapshot, and versions only increase.
    - **Sandwich**: `r1[i] = r2[i]` forces `r1[i].ver = r2[i].ver`,
      so all three are equal: `r2[i].ver = gs_cells[i].ver = r1[i].ver`.
    - **Same version → same cell**: since `u_write` increments the
      version by 1, equal versions at two time points mean no write
      occurred in between, hence the value is unchanged.  Therefore
      `gs_cells[i] = mem[i]` (at read time) `= r1[i]`.

    The "same version → same cell" condition is tracked directly
    in the simulation relation (condition 4c) and maintained
    inductively: writes make it vacuously true (version strictly
    increases past the snapshot), and non-writes preserve it trivially.

    ### Step correspondence (forward)

    | Concrete action            | Abstract steps               |
    |----------------------------|------------------------------|
    | `u_call`, `u_write`, `u_ret` | matching abstract step (1) |
    | `s_call`                   | abstract `s_call` (1 step)   |
    | `s_ret`                    | abstract `s_ret` (1 step)    |
    | `enter_repeat`, `cmp_neq`  | abstract `snap` (1 step)     |
    | `read_fst`, `read_rpt`    | stutter (0 steps)            |
    | `cmp_eq`                   | stutter (0 steps)            |
-/

open TLA

namespace Snapshot

variable {n : Nat} {Val : Type} {Tid : Type}

/-! ### Common definitions -/

/-- A memory cell: a value paired with a **monotonically increasing version**.
    Each `update` increments the version by 1, so equal versions at two
    time points guarantee no write occurred in between. -/
structure Cell (Val : Type) where
  val : Val
  ver : Nat
  deriving DecidableEq

/-- The operation a thread will perform (fixed per invocation). -/
inductive Op (n : Nat) (Val : Type) where
  | update (i : Fin n) (d : Val)
  | scan

/-! ### Concrete specification (double-collect implementation) -/

/-- Concrete program counter.
    - **Update path**: `idle → u_called → u_done → returned`.
    - **Scan path**: `idle → fst_collect 0 → ⋯ → fst_collect n`
      `→ collect 0 → ⋯ → collect n → (s_done | collect 0 → ⋯) → returned`.

    The index `j` in `fst_collect j` / `collect j` tracks which cell
    is about to be read next (`j = n` means the collect phase is done). -/
inductive CPC where
  | idle
  | u_called                     -- update: about to write
  | u_done                       -- update: write done, about to return
  | fst_collect (j : Nat)       -- scan: first collect, next cell to read is j
  | collect (j : Nat)           -- scan: repeat-collect, next cell to read is j
  | s_done                       -- scan: double-collect succeeded (r1 = r2)
  | returned

/-- Concrete state.
    - `mem`:  shared memory (value + version per cell).
    - `pc`:   per-thread program counter.
    - `op`:   per-thread operation (fixed per invocation).
    - `r1`:   scanner-local array — result of the *current* collect.
    - `r2`:   scanner-local array — result of the *previous* collect.
    - `ret`:  per-thread return value (set by `s_ret`). -/
structure CState (n : Nat) (Val : Type) (Tid : Type) where
  mem : Fin n → Cell Val
  pc  : Tid → @CPC
  op  : Tid → Op n Val
  r1  : Tid → (Fin n → Cell Val)
  r2  : Tid → (Fin n → Cell Val)
  ret : Tid → (Fin n → Val)

/-- Labels for the 10 concrete actions. -/
inductive CAction (n : Nat) (Val : Type) (Tid : Type) where
  | u_call (t : Tid)         -- update: external call
  | u_write (t : Tid)        -- update: write mem[i] := ⟨d, ver+1⟩
  | u_ret (t : Tid)          -- update: external return
  | s_call (t : Tid)         -- scan: external call
  | read_fst (t : Tid)       -- scan: read next cell in first collect
  | enter_repeat (t : Tid)   -- scan: first collect done → enter repeat loop
  | read_rpt (t : Tid)       -- scan: read next cell in repeat-collect
  | cmp_eq (t : Tid)         -- scan: r1 = r2 → double-collect success
  | cmp_neq (t : Tid)        -- scan: r1 ≠ r2 → restart repeat-collect
  | s_ret (t : Tid)          -- scan: external return (sets ret)

variable [DecidableEq Tid] [DecidableEq Val] [Inhabited Val] [NeZero n]

/-- The concrete (double-collect) snapshot specification.
    Initially all cells are `⟨default, 0⟩` and all threads are idle. -/
def conc_snap : ActionSpec (CState n Val Tid) (CAction n Val Tid) where
  init := fun s =>
    (∀ i, s.mem i = ⟨default, 0⟩) ∧ (∀ t, s.pc t = .idle) ∧
    (∀ t, s.r1 t = fun _ => ⟨default, 0⟩) ∧ (∀ t, s.r2 t = fun _ => ⟨default, 0⟩) ∧
    (∀ t, s.ret t = fun _ => default)
  actions := fun
    -- ── Update actions ──────────────────────────────────────────────
    | .u_call t => {
        gate := fun s => s.pc t = .idle ∧ ∃ i d, s.op t = .update i d
        transition := fun s s' =>
          s' = { s with pc := fun t' => if t' = t then .u_called else s.pc t' } }
    | .u_write t => {
        gate := fun s => s.pc t = .u_called ∧ ∃ i d, s.op t = .update i d
        transition := fun s s' =>
          -- Write ⟨d, ver+1⟩ to cell i:
          ∃ i d, s.op t = .update i d ∧
          s' = { s with
            mem := fun j => if j = i then ⟨d, (s.mem i).ver + 1⟩ else s.mem j
            pc := fun t' => if t' = t then .u_done else s.pc t' } }
    | .u_ret t => {
        gate := fun s => s.pc t = .u_done
        transition := fun s s' =>
          s' = { s with pc := fun t' => if t' = t then .returned else s.pc t' } }
    -- ── Scan actions ────────────────────────────────────────────────
    | .s_call t => {
        gate := fun s => s.pc t = .idle ∧ s.op t = .scan
        transition := fun s s' =>
          s' = { s with pc := fun t' => if t' = t then .fst_collect 0 else s.pc t' } }
    | .read_fst t => {
        -- Read cell j in the first collect: r1[j] ← mem[j]
        gate := fun s => ∃ j, s.pc t = .fst_collect j ∧ j < n
        transition := fun s s' =>
          ∃ j, ∃ hj : j < n, s.pc t = .fst_collect j ∧
          s' = { s with
            r1 := fun t' => if t' = t
              then fun k => if k = ⟨j, hj⟩ then s.mem ⟨j, hj⟩ else s.r1 t k
              else s.r1 t'
            pc := fun t' => if t' = t then .fst_collect (j + 1) else s.pc t' } }
    | .enter_repeat t => {
        -- First collect done: save r1 into r2, start repeat-collect
        gate := fun s => s.pc t = .fst_collect n
        transition := fun s s' =>
          s' = { s with
            r2 := fun t' => if t' = t then s.r1 t else s.r2 t'
            pc := fun t' => if t' = t then .collect 0 else s.pc t' } }
    | .read_rpt t => {
        -- Read cell j in a repeat-collect: r1[j] ← mem[j]
        gate := fun s => ∃ j, s.pc t = .collect j ∧ j < n
        transition := fun s s' =>
          ∃ j, ∃ hj : j < n, s.pc t = .collect j ∧
          s' = { s with
            r1 := fun t' => if t' = t
              then fun k => if k = ⟨j, hj⟩ then s.mem ⟨j, hj⟩ else s.r1 t k
              else s.r1 t'
            pc := fun t' => if t' = t then .collect (j + 1) else s.pc t' } }
    | .cmp_eq t => {
        -- Double-collect success: r1 = r2 (values + versions match)
        gate := fun s => s.pc t = .collect n ∧ s.r1 t = s.r2 t
        transition := fun s s' =>
          s' = { s with pc := fun t' => if t' = t then .s_done else s.pc t' } }
    | .cmp_neq t => {
        -- Double-collect failure: save r1 into r2, restart repeat-collect
        gate := fun s => s.pc t = .collect n ∧ s.r1 t ≠ s.r2 t
        transition := fun s s' =>
          s' = { s with
            r2 := fun t' => if t' = t then s.r1 t else s.r2 t'
            pc := fun t' => if t' = t then .collect 0 else s.pc t' } }
    | .s_ret t => {
        -- Scan return: set the return value to r1.vals
        gate := fun s => s.pc t = .s_done
        transition := fun s s' =>
          s' = { s with
            pc := fun t' => if t' = t then .returned else s.pc t'
            ret := fun t' => if t' = t then (fun i => (s.r1 t i).val) else s.ret t' } }

/-! ### Concurrent Specification (abstract for forward simulation) -/

/-- Abstract program counter.
    - **Update path**: `idle → u_called → u_done → returned`.
    - **Scan path**: `idle → scanning → returned`. -/
inductive APC where
  | idle | u_called | u_done | scanning | returned
  deriving DecidableEq

/-- Abstract state.
    `snaps t` is the list of atomic snapshots accumulated by scanner `t`. -/
structure AState (n : Nat) (Val : Type) (Tid : Type) where
  mem   : Fin n → Cell Val
  pc    : Tid → APC
  op    : Tid → Op n Val
  snaps : Tid → List (Fin n → Val)
  ret   : Tid → (Fin n → Val)

/-- Labels for the 6 abstract actions. -/
inductive AAction (n : Nat) (Val : Type) (Tid : Type) where
  | u_call (t : Tid) | u_write (t : Tid) | u_ret (t : Tid)
  | s_call (t : Tid)   -- enter scanning (snaps reset to [])
  | snap (t : Tid)     -- atomic snapshot: snaps ← snaps ++ [mem.vals]
  | s_ret (t : Tid)    -- return: pick any element of snaps

/-- The Concurrent Specification.
    - `s_call`: enters scanning with an empty snapshot list.
    - `snap`:   atomically reads the entire array in one step.
    - `s_ret`:  nondeterministically picks a snapshot from `snaps`. -/
def abst_snap : ActionSpec (AState n Val Tid) (AAction n Val Tid) where
  init := fun s =>
    (∀ i, s.mem i = ⟨default, 0⟩) ∧ (∀ t, s.pc t = .idle) ∧
    (∀ t, s.snaps t = []) ∧ (∀ t, s.ret t = fun _ => default)
  actions := fun
    -- ── Update actions (identical to concrete) ──────────────────────
    | .u_call t => {
        gate := fun s => s.pc t = .idle ∧ ∃ i d, s.op t = .update i d
        transition := fun s s' =>
          s' = { s with pc := fun t' => if t' = t then .u_called else s.pc t' } }
    | .u_write t => {
        gate := fun s => s.pc t = .u_called ∧ ∃ i d, s.op t = .update i d
        transition := fun s s' =>
          ∃ i d, s.op t = .update i d ∧
          s' = { s with
            mem := fun j => if j = i then ⟨d, (s.mem i).ver + 1⟩ else s.mem j
            pc := fun t' => if t' = t then .u_done else s.pc t' } }
    | .u_ret t => {
        gate := fun s => s.pc t = .u_done
        transition := fun s s' =>
          s' = { s with pc := fun t' => if t' = t then .returned else s.pc t' } }
    -- ── Scan actions ────────────────────────────────────────────────
    | .s_call t => {
        gate := fun s => s.pc t = .idle ∧ s.op t = .scan
        transition := fun s s' =>
          s' = { s with
            pc := fun t' => if t' = t then .scanning else s.pc t'
            snaps := fun t' => if t' = t then [] else s.snaps t' } }
    | .snap t => {
        -- Atomic snapshot: reads the entire array in one step
        gate := fun s => s.pc t = .scanning
        transition := fun s s' =>
          s' = { s with
            snaps := fun t' => if t' = t
              then s.snaps t ++ [fun i => (s.mem i).val] else s.snaps t' } }
    | .s_ret t => {
        -- Return: pick any snapshot from the accumulated list
        gate := fun s => s.pc t = .scanning ∧ s.snaps t ≠ []
        transition := fun s s' =>
          ∃ rv, rv ∈ s.snaps t ∧
          s' = { s with
            pc := fun t' => if t' = t then .returned else s.pc t'
            ret := fun t' => if t' = t then rv else s.ret t' } }

/-! ### Simulation relation -/

/-- PC correspondence: all scan-internal concrete states (`fst_collect`,
    `collect`, `s_done`) map to the single abstract state `scanning`. -/
def pc_rel : @CPC → APC → Prop
  | .idle,          .idle     => True
  | .u_called,      .u_called => True
  | .u_done,        .u_done   => True
  | .fst_collect _, .scanning => True
  | .collect _,     .scanning => True
  | .s_done,        .scanning => True
  | .returned,      .returned => True
  | _,              _         => False

-- `pc_rel` is functional: each concrete PC determines a unique abstract PC.
@[simp] theorem pc_rel_idle : pc_rel CPC.idle apc ↔ apc = APC.idle := by
  cases apc <;> simp [pc_rel]
@[simp] theorem pc_rel_u_called : pc_rel CPC.u_called apc ↔ apc = APC.u_called := by
  cases apc <;> simp [pc_rel]
@[simp] theorem pc_rel_u_done : pc_rel CPC.u_done apc ↔ apc = APC.u_done := by
  cases apc <;> simp [pc_rel]
@[simp] theorem pc_rel_fst_collect : pc_rel (CPC.fst_collect j) apc ↔ apc = APC.scanning := by
  cases apc <;> simp [pc_rel]
@[simp] theorem pc_rel_collect : pc_rel (CPC.collect j) apc ↔ apc = APC.scanning := by
  cases apc <;> simp [pc_rel]
@[simp] theorem pc_rel_s_done : pc_rel CPC.s_done apc ↔ apc = APC.scanning := by
  cases apc <;> simp [pc_rel]
@[simp] theorem pc_rel_returned : pc_rel CPC.returned apc ↔ apc = APC.returned := by
  cases apc <;> simp [pc_rel]

/-- The simulation relation between concrete and abstract states.

    **Condition 1** (`mem`): shared memory agrees.
    **Condition 2** (`op`): per-thread operations agree.
    **Condition 3** (`pc`): program counters correspond via `pc_rel`.
    **Condition 4** (`snapshot witness`): for scanners in `collect j` or
      `s_done`, there exists a witness `gs_cells : Fin n → Cell Val`
      (representing full cells at the time the abstract took a snapshot)
      satisfying:
      - **(4a)** `gs_cells.vals ∈ snaps` — the snapshot values are in
        the abstract's accumulated list.
      - **(4b)** `gs_cells[i].ver ≤ mem[i].ver` — versions only increase
        since the snapshot.
      - **(4c)** `gs_cells[i].ver = mem[i].ver → gs_cells[i] = mem[i]`
        — **same version implies same cell** (no write occurred, so
        the value is unchanged).  This is the core invariant: writes
        increment the version by 1, making this vacuously true for
        the written cell; non-writes preserve it trivially.
      - **(4d)** `r2[i].ver ≤ gs_cells[i].ver` — `r2` was read
        *before* the snapshot.
      - **(4e)** For cells `i < j` where `r1[i] = r2[i]`:
        `gs_cells[i] = r1[i]`.  This **conditional match** is established
        at each `read_rpt` step via the version-sandwich argument.
      - **(4f)** At `s_done`: `gs_cells[i] = r1[i]` for all `i`.
        This follows from (4e) at `j = n` plus `r1 = r2`.
    **Condition 5** (`ret`): return values agree (only `s_ret` modifies them).
    **Condition 6** (`r1 version bound`): for cells already read into `r1`,
      `r1[i].ver ≤ mem[i].ver`.  This supports (4d) at `enter_repeat`/`cmp_neq`
      (where `r2 := r1` and the snapshot is `mem`). -/
def sim_rel (cs : CState n Val Tid) (as : AState n Val Tid) : Prop :=
  -- (1) mem agrees
  cs.mem = as.mem ∧
  -- (2) op agrees
  cs.op = as.op ∧
  -- (3) PCs related
  (∀ t, pc_rel (cs.pc t) (as.pc t)) ∧
  -- (4) snapshot witness for scanners in collect/s_done
  (∀ t, (∃ j, cs.pc t = .collect j) ∨ cs.pc t = .s_done →
    ∃ gs_cells : Fin n → Cell Val,
      -- (4a) values in snaps
      (fun i => (gs_cells i).val) ∈ as.snaps t ∧
      -- (4b) snapshot versions ≤ current mem versions
      (∀ i, (gs_cells i).ver ≤ (cs.mem i).ver) ∧
      -- (4c) same version → same cell
      (∀ i, (gs_cells i).ver = (cs.mem i).ver → gs_cells i = cs.mem i) ∧
      -- (4d) r2 versions ≤ snapshot versions
      (∀ i, (cs.r2 t i).ver ≤ (gs_cells i).ver) ∧
      -- (4e) conditional match: for already-read cells where r1 = r2
      (∀ j', cs.pc t = .collect j' →
        ∀ i : Fin n, i.val < j' → cs.r1 t i = cs.r2 t i → gs_cells i = cs.r1 t i) ∧
      -- (4f) at s_done: full match
      (cs.pc t = .s_done → ∀ i, gs_cells i = cs.r1 t i)) ∧
  -- (5) return values agree
  (∀ t, cs.ret t = as.ret t) ∧
  -- (6) r1 version bound (for cells already read into r1)
  (∀ t, (∀ j, cs.pc t = .fst_collect j →
          ∀ i : Fin n, i.val < j → (cs.r1 t i).ver ≤ (cs.mem i).ver) ∧
        (∀ j, cs.pc t = .collect j →
          ∀ i : Fin n, i.val < j → (cs.r1 t i).ver ≤ (cs.mem i).ver) ∧
        (cs.pc t = .s_done →
          ∀ i : Fin n, (cs.r1 t i).ver ≤ (cs.mem i).ver))

/-! ### Proof helpers -/

/-- After a step that changes only thread `t`'s PC to `new_cpc`/`new_apc`,
    `pc_rel` is preserved for all threads. -/
private theorem pc_rel_update {Tid : Type} [DecidableEq Tid]
    {cpc_fn : Tid → @CPC} {apc_fn : Tid → APC}
    (hpc : ∀ t', pc_rel (cpc_fn t') (apc_fn t'))
    (t : Tid) (new_cpc : @CPC) (new_apc : APC)
    (h_new : pc_rel new_cpc new_apc) :
    ∀ t', pc_rel (if t' = t then new_cpc else cpc_fn t')
                  (if t' = t then new_apc else apc_fn t') := by
  intro t'; by_cases h : t' = t <;> simp [h, h_new, hpc t']

/-- If `i.val < j + 1` and `i ≠ ⟨j, hj⟩`, then `i.val < j`. -/
private theorem fin_lt_succ_ne {n j : Nat} {hj : j < n} {i : Fin n}
    (hi : i.val < j + 1) (hne : i ≠ ⟨j, hj⟩) : i.val < j := by
  have : i.val ≠ j := fun h => hne (Fin.ext h)
  omega

/-! ### The forward simulation proof -/

/-- **Part 1 main theorem**: the double-collect implementation is a
    forward simulation of the Concurrent Specification.

    The proof is by case analysis on the 10 concrete actions:
    - **Update** (`u_call`, `u_write`, `u_ret`): matched 1-to-1.
    - **`s_call`**: abstract `s_call` (1 step).
    - **`s_ret`**: abstract `s_ret` (1 step), choosing `rv = gs_cells.vals`.
    - **`enter_repeat`, `cmp_neq`**: abstract `snap` (1 step) — records
      `mem` as the new witness `gs_cells`.
    - **`read_fst`, `read_rpt`**: stutter — the witness carries over.
    - **`cmp_eq`**: stutter — derives `gs_cells = r1` from (4e) + `r1 = r2`. -/
def snapshot_sim : SimulationRel (CState n Val Tid) (AState n Val Tid) where
  concrete := (conc_snap (n := n) (Val := Val) (Tid := Tid)).toSpec
  abstract := (abst_snap (n := n) (Val := Val) (Tid := Tid)).toSpec
  R := sim_rel

  -- ── Initial states ──────────────────────────────────────────────
  -- The abstract initial state mirrors the concrete one.
  -- No thread is in collect/s_done, so condition (4) is vacuous.
  init_sim := by
    intro s ⟨hmem, hpc, _, _, hret⟩
    refine ⟨⟨s.mem, fun _ => .idle, s.op, fun _ => [], fun _ => fun _ => default⟩,
            ⟨hmem, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩,
            rfl, rfl, fun t => by simp [pc_rel, hpc],
            fun t h => ?_,
            fun t => by simp [hret],
            fun t => ⟨fun j hj => by simp [hpc] at hj,
                       fun j hj => by simp [hpc] at hj,
                       fun hj => by simp [hpc] at hj⟩⟩
    -- Vacuous: no thread is in collect/s_done initially
    rcases h with ⟨j, hj⟩ | hj <;> simp [hpc] at hj

  -- ── Step simulation ─────────────────────────────────────────────
  step_sim := by
    intro s s' a ⟨hmem, hop, hpc_r, hsnap, hret_eq, hver⟩ ⟨act, hg, htrans⟩
    cases act with

    --  ╔═══════════════════════════════════════════════════════════╗
    --  ║  UPDATE ACTIONS: one-to-one correspondence               ║
    --  ╚═══════════════════════════════════════════════════════════╝

    | u_call t =>
      -- idle → u_called. Abstract: u_call (1 step).
      -- Conditions (4)–(6): thread t's new PC (u_called) is not
      -- collect/s_done/fst_collect, so all conditions are vacuous for t;
      -- unchanged for other threads.
      obtain ⟨hpc_t, i, d, hop_t⟩ := hg ; subst htrans
      have ha : a.pc t = .idle := by have := hpc_r t; rwa [hpc_t, pc_rel_idle] at this
      refine ⟨{ a with pc := fun t' => if t' = t then .u_called else a.pc t' },
             Star.single ⟨.u_call t, ⟨ha, i, d, hop ▸ hop_t⟩, rfl⟩,
             hmem, hop, pc_rel_update hpc_r t _ _ trivial,
             fun t' ht' => by (by_cases h : t' = t <;> simp_all),
             fun t' => by simp [hret_eq],
             fun t' => ?_⟩
      -- Condition (6): version bounds for all threads
      refine ⟨fun j' hj' => ?_, fun j' hj' => ?_, fun hj' => ?_⟩
      · by_cases h : t' = t
        · rw [h] at hj'; simp at hj'  -- u_called ≠ fst_collect
        · simp only [show ¬(t' = t) from h, if_false] at hj'; exact (hver t').1 j' hj'
      · by_cases h : t' = t
        · rw [h] at hj'; simp at hj'  -- u_called ≠ collect
        · simp only [show ¬(t' = t) from h, if_false] at hj'; exact (hver t').2.1 j' hj'
      · by_cases h : t' = t
        · rw [h] at hj'; simp at hj'  -- u_called ≠ s_done
        · simp only [show ¬(t' = t) from h, if_false] at hj'; exact (hver t').2.2 hj'

    | u_write t =>
      -- u_called → u_done, mem[i] := ⟨d, ver+1⟩. Abstract: u_write (1 step).
      -- Key for (4b)/(4c): the written cell's version increases by 1,
      -- so gs_cells.ver ≤ old ver < new ver — making (4c) vacuously
      -- true for that cell.  Other cells unchanged.
      obtain ⟨hpc_t, _⟩ := hg
      obtain ⟨i, d, hop_eq, hs'⟩ := htrans ; subst hs'
      have ha : a.pc t = .u_called := by have := hpc_r t; rwa [hpc_t, pc_rel_u_called] at this
      refine ⟨{ a with
                mem := fun j => if j = i then ⟨d, (a.mem i).ver + 1⟩ else a.mem j
                pc := fun t' => if t' = t then .u_done else a.pc t' },
             Star.single ⟨.u_write t, ⟨ha, i, d, hop ▸ hop_eq⟩, i, d, hop ▸ hop_eq, rfl⟩,
             ?_, hop, pc_rel_update hpc_r t _ _ trivial,
             ?_, fun t' => by simp [hret_eq], ?_⟩
      · -- (1) mem: both sides update the same cell identically
        funext j; simp [hmem]
      · -- (4) snapshot witness: for other threads in collect/s_done
        intro t' ht'
        by_cases h : t' = t
        · rw [h] at ht'; simp at ht'  -- u_done ≠ collect/s_done
        · simp only [show ¬(t' = t) from h, if_false] at ht' ⊢
          obtain ⟨gs_cells, hgs_mem, hgs_ver, hgs_eq, hgs_r2, hgs_cond, hgs_done⟩ := hsnap t' ht'
          refine ⟨gs_cells, hgs_mem, ?_, ?_, hgs_r2, hgs_cond, hgs_done⟩
          · -- (4b) snapshot ver ≤ new mem ver
            intro k; by_cases hk : k = i
            · subst hk; simp; exact Nat.le_succ_of_le (hgs_ver k)
            · simp [hk]; exact hgs_ver k
          · -- (4c) same ver → same cell: for the written cell k=i,
            -- new ver = old ver + 1 > gs_cells.ver, so vacuously true
            intro k hk_eq
            by_cases hki : k = i
            · subst hki; simp at hk_eq; have := hgs_ver k; omega
            · simp [hki] at hk_eq ⊢; exact hgs_eq k hk_eq
      · -- (6) r1 version bound: written cell's version increases
        intro t'
        refine ⟨fun j' hj' k hk => ?_, fun j' hj' k hk => ?_, fun hj' k => ?_⟩
        · by_cases ht : t' = t
          · rw [ht] at hj'; simp at hj'
          · simp only [show ¬(t' = t) from ht, if_false] at hj' ⊢
            have h0 := (hver t').1 j' hj' k hk
            by_cases hki : k = i
            · subst hki; simp; exact Nat.le_succ_of_le h0
            · simp [hki]; exact h0
        · by_cases ht : t' = t
          · rw [ht] at hj'; simp at hj'
          · simp only [show ¬(t' = t) from ht, if_false] at hj' ⊢
            have h0 := (hver t').2.1 j' hj' k hk
            by_cases hki : k = i
            · subst hki; simp; exact Nat.le_succ_of_le h0
            · simp [hki]; exact h0
        · by_cases ht : t' = t
          · rw [ht] at hj'; simp at hj'
          · simp only [show ¬(t' = t) from ht, if_false] at hj' ⊢
            have h0 := (hver t').2.2 hj' k
            by_cases hki : k = i
            · subst hki; simp; exact Nat.le_succ_of_le h0
            · simp [hki]; exact h0

    | u_ret t =>
      -- u_done → returned. Abstract: u_ret (1 step). Straightforward.
      subst htrans
      have ha : a.pc t = .u_done := by have := hpc_r t; rwa [hg, pc_rel_u_done] at this
      refine ⟨{ a with pc := fun t' => if t' = t then .returned else a.pc t' },
             Star.single ⟨.u_ret t, ha, rfl⟩,
             hmem, hop, pc_rel_update hpc_r t _ _ trivial,
             fun t' ht' => by (by_cases h : t' = t <;> simp_all),
             fun t' => by simp [hret_eq],
             fun t' => ?_⟩
      refine ⟨fun j' hj' => ?_, fun j' hj' => ?_, fun hj' => ?_⟩
      · by_cases h : t' = t
        · rw [h] at hj'; simp at hj'
        · simp only [show ¬(t' = t) from h, if_false] at hj'; exact (hver t').1 j' hj'
      · by_cases h : t' = t
        · rw [h] at hj'; simp at hj'
        · simp only [show ¬(t' = t) from h, if_false] at hj'; exact (hver t').2.1 j' hj'
      · by_cases h : t' = t
        · rw [h] at hj'; simp at hj'
        · simp only [show ¬(t' = t) from h, if_false] at hj'; exact (hver t').2.2 hj'

    --  ╔═══════════════════════════════════════════════════════════╗
    --  ║  SCAN CALL: abstract s_call (1 step)                     ║
    --  ╚═══════════════════════════════════════════════════════════╝

    | s_call t =>
      -- idle → fst_collect 0. Abstract: s_call (1 step).
      -- No thread enters collect, so (4) is vacuous for t.
      obtain ⟨hpc_t, hop_t⟩ := hg ; subst htrans
      have ha : a.pc t = .idle := by have := hpc_r t; rwa [hpc_t, pc_rel_idle] at this
      refine ⟨{ a with
                pc := fun t' => if t' = t then .scanning else a.pc t'
                snaps := fun t' => if t' = t then [] else a.snaps t' },
             Star.single ⟨.s_call t, ⟨ha, hop ▸ hop_t⟩, rfl⟩,
             hmem, hop, pc_rel_update hpc_r t _ _ trivial,
             fun t' ht' => by (by_cases h : t' = t <;> simp_all),
             fun t' => by simp [hret_eq],
             fun t' => ?_⟩
      refine ⟨fun j' hj' => ?_, fun j' hj' => ?_, fun hj' => ?_⟩
      · by_cases h : t' = t
        · rw [h] at hj'; simp at hj'; intro k hk; omega  -- fst_collect 0: no cells read yet
        · simp only [show ¬(t' = t) from h, if_false] at hj' ⊢; exact (hver t').1 j' hj'
      · by_cases h : t' = t
        · rw [h] at hj'; simp at hj'  -- fst_collect 0 ≠ collect
        · simp only [show ¬(t' = t) from h, if_false] at hj' ⊢; exact (hver t').2.1 j' hj'
      · by_cases h : t' = t
        · rw [h] at hj'; simp at hj'  -- fst_collect 0 ≠ s_done
        · simp only [show ¬(t' = t) from h, if_false] at hj' ⊢; exact (hver t').2.2 hj'

    --  ╔═══════════════════════════════════════════════════════════╗
    --  ║  SCAN READS: abstract stutters (0 steps)                 ║
    --  ╚═══════════════════════════════════════════════════════════╝

    | read_fst t =>
      -- fst_collect j → fst_collect (j+1), r1[j] := mem[j].
      -- Abstract stutters. Only r1 and pc change; witness unchanged.
      obtain ⟨j, hj, hpc_t, hs'⟩ := htrans ; subst hs'
      have ha : a.pc t = .scanning := by have := hpc_r t; rwa [hpc_t, pc_rel_fst_collect] at this
      refine ⟨a, .refl, hmem, hop, ?_, ?_, ?_, ?_⟩
      · -- (3) pc_rel: fst_collect(j+1) ↔ scanning
        intro t'; by_cases h : t' = t
        · simp [h, ha, pc_rel]
        · simp only [show ¬(t' = t) from h]; exact hpc_r t'
      · -- (4) snapshot witness: fst_collect(j+1) is not collect/s_done → vacuous for t
        intro t' ht'; by_cases h : t' = t
        · simp [h] at ht'
        · simp only [show ¬(t' = t) from h] at ht' ⊢; exact hsnap t' ht'
      · -- (5) ret unchanged
        intro t'; by_cases h : t' = t <;> simp [h, hret_eq]
      · -- (6) r1 version bound: cell j was just read, so r1[j].ver = mem[j].ver ≤ mem[j].ver
        intro t'
        refine ⟨fun j' hj' k hk => ?_, fun j' hj' k hk => ?_, fun hj' k => ?_⟩
        · by_cases ht : t' = t
          · rw [ht] at hj'; simp at hj'; subst hj'
            by_cases hkj : k = ⟨j, hj⟩
            · subst hkj; simp [ht]  -- r1[j] = mem[j], so ver ≤ ver
            · simp only [ht, if_true, show ¬(k = ⟨j, hj⟩) from hkj, if_false]
              exact (hver t).1 j hpc_t k (fin_lt_succ_ne hk hkj)
          · simp only [show ¬(t' = t) from ht, if_false] at hj' ⊢
            exact (hver t').1 j' hj' k hk
        · by_cases ht : t' = t
          · rw [ht] at hj'; simp at hj'  -- fst_collect(j+1) ≠ collect
          · simp only [show ¬(t' = t) from ht, if_false] at hj' ⊢
            exact (hver t').2.1 j' hj' k hk
        · by_cases ht : t' = t
          · rw [ht] at hj'; simp at hj'  -- fst_collect(j+1) ≠ s_done
          · simp only [show ¬(t' = t) from ht, if_false] at hj' ⊢
            exact (hver t').2.2 hj' k

    | read_rpt t =>
      -- collect j → collect (j+1), r1[j] := mem[j].
      -- Abstract stutters. The witness gs_cells carries over.
      --
      -- KEY STEP: maintaining (4e) for cell j.  If r1_new[j] = r2[j]:
      --   • r1_new[j] = mem[j]  (just read NOW)
      --   • r2[j].ver ≤ gs_cells[j].ver ≤ mem[j].ver  (conditions 4d, 4b)
      --   • r1_new[j].ver = r2[j].ver  (from r1_new[j] = r2[j])
      --   • Version sandwich: gs_cells[j].ver = mem[j].ver
      --   • By (4c): gs_cells[j] = mem[j] = r1_new[j]  ✓
      obtain ⟨j, hj, hpc_t, hs'⟩ := htrans ; subst hs'
      have ha : a.pc t = .scanning := by have := hpc_r t; rwa [hpc_t, pc_rel_collect] at this
      refine ⟨a, .refl, hmem, hop, ?_, ?_, ?_, ?_⟩
      · -- (3) pc_rel
        intro t'; by_cases h : t' = t
        · simp [h, ha, pc_rel]
        · simp only [show ¬(t' = t) from h]; exact hpc_r t'
      · -- (4) snapshot witness
        intro t' ht'; by_cases h : t' = t
        · simp only [h] at ht' ⊢
          -- Carry the witness from collect(j), extending (4e) to cell j
          obtain ⟨gs_cells, hgs_mem, hgs_ver, hgs_eq_cell, hgs_r2, hgs_cond, hgs_done⟩ :=
            hsnap t (Or.inl ⟨j, hpc_t⟩)
          refine ⟨gs_cells, hgs_mem, hgs_ver, hgs_eq_cell, hgs_r2, ?_, fun hd => ?_⟩
          · -- (4e) conditional match for cells i < j+1 where r1_new[i] = r2[i]
            intro j' hpc_j'
            have hj'_eq : j + 1 = j' := by simp at hpc_j'; exact hpc_j'
            subst hj'_eq
            intro i hi_lt hr1r2
            by_cases hji : i = ⟨j, hj⟩
            · -- Cell j: the version-sandwich argument
              subst hji; simp at hr1r2
              -- r1_new[j] = mem[j] (just read), and r1_new[j] = r2[j] (given)
              -- So mem[j] = r2[j], hence mem[j].ver = r2[j].ver
              have h_ver_eq : (s.mem ⟨j, hj⟩).ver = (s.r2 t ⟨j, hj⟩).ver :=
                congrArg Cell.ver hr1r2
              -- Version sandwich: r2.ver ≤ gs.ver ≤ mem.ver = r2.ver
              have hd_le := hgs_r2 ⟨j, hj⟩
              have hb_le := hgs_ver ⟨j, hj⟩
              have hgs_ver_eq : (gs_cells ⟨j, hj⟩).ver = (s.mem ⟨j, hj⟩).ver := by omega
              -- Same version → same cell
              have hgs_eq_mem := hgs_eq_cell ⟨j, hj⟩ hgs_ver_eq
              -- gs_cells[j] = mem[j] = r1_new[j]
              simp; exact hgs_eq_mem
            · -- Cell i < j: carried from the hypothesis
              have hi_lt_j : i.val < j := fin_lt_succ_ne hi_lt hji
              simp [hji] at hr1r2
              have := hgs_cond j hpc_t i hi_lt_j hr1r2
              simp [hji]; exact this
          · -- (4f) s_done: impossible (we're at collect(j+1))
            simp at hd
        · simp only [show ¬(t' = t) from h] at ht' ⊢; exact hsnap t' ht'
      · -- (5) ret unchanged
        intro t'; by_cases h : t' = t <;> simp [h, hret_eq]
      · -- (6) r1 version bound: extend to cell j (just read from mem)
        intro t'
        refine ⟨fun j' hj' k hk => ?_, fun j' hj' k hk => ?_, fun hj' k => ?_⟩
        · by_cases ht : t' = t
          · rw [ht] at hj'; simp at hj'  -- collect(j+1) ≠ fst_collect
          · simp only [show ¬(t' = t) from ht, if_false] at hj' ⊢
            exact (hver t').1 j' hj' k hk
        · by_cases ht : t' = t
          · rw [ht] at hj'; simp at hj'; subst hj'
            by_cases hkj : k = ⟨j, hj⟩
            · subst hkj; simp [ht]  -- r1[j] = mem[j]
            · simp only [ht, if_true, show ¬(k = ⟨j, hj⟩) from hkj, if_false]
              exact (hver t).2.1 j hpc_t k (fin_lt_succ_ne hk hkj)
          · simp only [show ¬(t' = t) from ht, if_false] at hj' ⊢
            exact (hver t').2.1 j' hj' k hk
        · by_cases ht : t' = t
          · rw [ht] at hj'; simp at hj'  -- collect(j+1) ≠ s_done
          · simp only [show ¬(t' = t) from ht, if_false] at hj' ⊢
            exact (hver t').2.2 hj' k

    --  ╔═══════════════════════════════════════════════════════════╗
    --  ║  SNAPSHOT-TAKING: abstract snap (1 step)                 ║
    --  ║  Records current mem as the new witness gs_cells.        ║
    --  ╚═══════════════════════════════════════════════════════════╝

    | enter_repeat t =>
      -- fst_collect n → collect 0, r2 := r1.
      -- Abstract: snap (snaps t ← snaps t ++ [mem.vals]).
      -- New witness gs_cells := mem (full cells). Condition (4d)
      -- uses (6) to get r2.ver = r1.ver ≤ mem.ver = gs_cells.ver.
      subst htrans
      have ha : a.pc t = .scanning := by have := hpc_r t; rwa [hg, pc_rel_fst_collect] at this
      let a' := { a with snaps := fun t' => if t' = t
                    then a.snaps t ++ [fun i => (a.mem i).val] else a.snaps t' }
      refine ⟨a', Star.single ⟨.snap t, ha, rfl⟩, hmem, hop, ?_, ?_, ?_, ?_⟩
      · -- (3) pc_rel: snap doesn't change PC; collect 0 ↔ scanning
        intro t'; show pc_rel _ (a.pc t')
        by_cases h : t' = t
        · simp [h, ha, pc_rel]
        · simp only [if_neg h]; exact hpc_r t'
      · -- (4) snapshot witness: gs_cells := mem
        intro t' ht'; by_cases h : t' = t
        · simp only [h, if_true, a'] at ht' ⊢
          refine ⟨fun i => s.mem i, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · -- (4a) mem.vals ∈ snaps (just appended)
            show (fun i => (s.mem i).val) ∈ a.snaps t ++ [fun i => (a.mem i).val]
            rw [← hmem]; exact List.mem_append.mpr (Or.inr (List.mem_cons_self))
          · -- (4b) gs.ver ≤ mem.ver (gs IS mem)
            intro i; exact Nat.le_refl _
          · -- (4c) same ver → same cell (trivially, gs = mem)
            intro i _; rfl
          · -- (4d) r2.ver ≤ gs.ver: r2 = r1 (just set), and r1.ver ≤ mem.ver by (6)
            intro i; exact (hver t).1 n hg i i.isLt
          · -- (4e) conditional match: j = 0, so vacuous
            intro j' hpc_j'; simp at hpc_j'; omega
          · -- (4f) s_done: impossible (we're at collect 0)
            intro hd; simp at hd
        · simp only [show ¬(t' = t) from h, if_false, a'] at ht' ⊢
          exact hsnap t' ht'
      · -- (5) ret unchanged (snap doesn't change ret)
        intro t'; show s.ret t' = a'.ret t'; simp [a', hret_eq]
      · -- (6) r1 version bound
        intro t'
        refine ⟨fun j' hj' k hk => ?_, fun j' hj' k hk => ?_, fun hj' k => ?_⟩
        · by_cases ht : t' = t
          · rw [ht] at hj'; simp at hj'  -- collect 0 ≠ fst_collect
          · simp only [show ¬(t' = t) from ht, if_false] at hj' ⊢
            exact (hver t').1 j' hj' k hk
        · by_cases ht : t' = t
          · rw [ht] at hj'; simp at hj'; omega  -- collect 0: no cells read yet
          · simp only [show ¬(t' = t) from ht, if_false] at hj' ⊢
            exact (hver t').2.1 j' hj' k hk
        · by_cases ht : t' = t
          · rw [ht] at hj'; simp at hj'  -- collect 0 ≠ s_done
          · simp only [show ¬(t' = t) from ht, if_false] at hj' ⊢
            exact (hver t').2.2 hj' k

    | cmp_neq t =>
      -- collect n → collect 0, r2 := r1 (restart after mismatch).
      -- Abstract: snap (same construction as enter_repeat).
      obtain ⟨hpc_t, _⟩ := hg ; subst htrans
      have ha : a.pc t = .scanning := by have := hpc_r t; rwa [hpc_t, pc_rel_collect] at this
      let a' := { a with snaps := fun t' => if t' = t
                    then a.snaps t ++ [fun i => (a.mem i).val] else a.snaps t' }
      refine ⟨a', Star.single ⟨.snap t, ha, rfl⟩, hmem, hop, ?_, ?_, ?_, ?_⟩
      · intro t'; show pc_rel _ (a.pc t')
        by_cases h : t' = t
        · simp [h, ha, pc_rel]
        · simp only [if_neg h]; exact hpc_r t'
      · intro t' ht'; by_cases h : t' = t
        · simp only [h, if_true, a'] at ht' ⊢
          refine ⟨fun i => s.mem i, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · show (fun i => (s.mem i).val) ∈ a.snaps t ++ [fun i => (a.mem i).val]
            rw [← hmem]; exact List.mem_append.mpr (Or.inr (List.mem_cons_self))
          · intro i; exact Nat.le_refl _
          · intro i _; rfl
          · -- (4d) r2.ver ≤ gs.ver: r2 = r1 (just set), r1.ver ≤ mem.ver by (6)
            intro i; exact (hver t).2.1 n hpc_t i i.isLt
          · intro j' hpc_j'; simp at hpc_j'; omega
          · intro hd; simp at hd
        · simp only [show ¬(t' = t) from h, if_false, a'] at ht' ⊢
          exact hsnap t' ht'
      · intro t'; show s.ret t' = a'.ret t'; simp [a', hret_eq]
      · intro t'
        refine ⟨fun j' hj' k hk => ?_, fun j' hj' k hk => ?_, fun hj' k => ?_⟩
        · by_cases ht : t' = t
          · rw [ht] at hj'; simp at hj'
          · simp only [show ¬(t' = t) from ht, if_false] at hj' ⊢
            exact (hver t').1 j' hj' k hk
        · by_cases ht : t' = t
          · rw [ht] at hj'; simp at hj'; omega
          · simp only [show ¬(t' = t) from ht, if_false] at hj' ⊢
            exact (hver t').2.1 j' hj' k hk
        · by_cases ht : t' = t
          · rw [ht] at hj'; simp at hj'
          · simp only [show ¬(t' = t) from ht, if_false] at hj' ⊢
            exact (hver t').2.2 hj' k

    --  ╔═══════════════════════════════════════════════════════════╗
    --  ║  COMPARE-EQUAL: abstract stutters (0 steps)              ║
    --  ║  Derives gs_cells = r1 from (4e) + r1 = r2.             ║
    --  ╚═══════════════════════════════════════════════════════════╝

    | cmp_eq t =>
      -- collect n → s_done (r1 = r2). Abstract stutters.
      -- From (4e) at j = n: for all i < n, r1[i] = r2[i] → gs_cells[i] = r1[i].
      -- Since r1 = r2 (for all cells) and i.val < n for every i : Fin n,
      -- we get gs_cells[i] = r1[i] for all i, establishing (4f).
      obtain ⟨hpc_t, hr1_eq_r2⟩ := hg ; subst htrans
      have ha : a.pc t = .scanning := by have := hpc_r t; rwa [hpc_t, pc_rel_collect] at this
      refine ⟨a, .refl, hmem, hop, ?_, ?_, ?_, ?_⟩
      · intro t'; by_cases h : t' = t
        · simp [h, ha, pc_rel]
        · simp only [if_neg h]; exact hpc_r t'
      · intro t' ht'; by_cases h : t' = t
        · -- Thread t: derive (4f) from (4e)
          simp only [h] at ht' ⊢
          obtain ⟨gs_cells, hgs_mem, hgs_ver, hgs_eq_cell, hgs_r2, hgs_cond, _⟩ :=
            hsnap t (Or.inl ⟨n, hpc_t⟩)
          refine ⟨gs_cells, hgs_mem, hgs_ver, hgs_eq_cell, hgs_r2, ?_, ?_⟩
          · -- (4e) at s_done: vacuous (not collect)
            intro j' hpc_j'; simp at hpc_j'
          · -- (4f) ∀ i, gs_cells i = r1 t i
            -- Apply (4e) at j = n with r1 = r2
            intro _ i
            exact hgs_cond n hpc_t i i.isLt (congrFun hr1_eq_r2 i)
        · simp only [if_neg h] at ht' ⊢; exact hsnap t' ht'
      · intro t'; by_cases h : t' = t <;> simp [h, hret_eq]
      · intro t'
        refine ⟨fun j' hj' k hk => ?_, fun j' hj' k hk => ?_, fun hj' k => ?_⟩
        · by_cases ht : t' = t
          · rw [ht] at hj'; simp at hj'
          · simp only [show ¬(t' = t) from ht, if_false] at hj' ⊢
            exact (hver t').1 j' hj' k hk
        · by_cases ht : t' = t
          · rw [ht] at hj'; simp at hj'
          · simp only [show ¬(t' = t) from ht, if_false] at hj' ⊢
            exact (hver t').2.1 j' hj' k hk
        · by_cases ht : t' = t
          · -- Thread t at s_done: use (6) from collect n
            rw [ht]; exact (hver t).2.1 n hpc_t k k.isLt
          · simp only [show ¬(t' = t) from ht, if_false] at hj' ⊢
            exact (hver t').2.2 hj' k

    --  ╔═══════════════════════════════════════════════════════════╗
    --  ║  SCAN RETURN: abstract s_ret (1 step)                    ║
    --  ╚═══════════════════════════════════════════════════════════╝

    | s_ret t =>
      -- s_done → returned, ret t := r1.vals.
      -- Abstract: s_ret picks rv = gs_cells.vals from snaps.
      -- By (4f), gs_cells = r1, so rv = r1.vals = concrete ret. ✓
      subst htrans
      have ha : a.pc t = .scanning := by have := hpc_r t; rwa [hg, pc_rel_s_done] at this
      -- Extract the witness with gs_cells = r1 (from 4f at s_done)
      obtain ⟨gs_cells, hgs_mem, _, _, _, _, hgs_done⟩ := hsnap t (Or.inr hg)
      have hgs_eq_r1 : ∀ i, gs_cells i = s.r1 t i := hgs_done hg
      have hgs_val : (fun i => (gs_cells i).val) = fun i => (s.r1 t i).val := by
        funext i; rw [hgs_eq_r1 i]
      refine ⟨{ a with
                pc := fun t' => if t' = t then .returned else a.pc t'
                ret := fun t' => if t' = t then (fun i => (gs_cells i).val) else a.ret t' },
             Star.single ⟨.s_ret t, ⟨ha, ?_⟩, (fun i => (gs_cells i).val), hgs_mem, rfl⟩,
             hmem, hop, pc_rel_update hpc_r t _ _ trivial, ?_, ?_, ?_⟩
      · -- snaps t ≠ [] (since gs_cells.vals ∈ snaps t)
        intro hempty; rw [hempty] at hgs_mem; exact absurd hgs_mem (List.not_mem_nil)
      · -- (4) returned is not collect/s_done → vacuous for t
        intro t' ht'; by_cases h : t' = t
        · simp [h] at ht'
        · simp only [if_neg h] at ht' ⊢; exact hsnap t' ht'
      · -- (5) return values agree: thread t gets r1.vals = gs_cells.vals
        intro t'; by_cases h : t' = t
        · simp [h, hgs_val]
        · simp [h, hret_eq]
      · -- (6) version bounds
        intro t'
        refine ⟨fun j' hj' k hk => ?_, fun j' hj' k hk => ?_, fun hj' k => ?_⟩
        · by_cases ht : t' = t
          · rw [ht] at hj'; simp at hj'
          · simp only [show ¬(t' = t) from ht, if_false] at hj' ⊢
            exact (hver t').1 j' hj' k hk
        · by_cases ht : t' = t
          · rw [ht] at hj'; simp at hj'
          · simp only [show ¬(t' = t) from ht, if_false] at hj' ⊢
            exact (hver t').2.1 j' hj' k hk
        · by_cases ht : t' = t
          · rw [ht] at hj'; simp at hj'
          · simp only [show ¬(t' = t) from ht, if_false] at hj' ⊢
            exact (hver t').2.2 hj' k


/-! ## Part 2: Backward Simulation (Concurrent Specification → Atomic Specification)

    We prove that the Concurrent Specification (`abst_snap`, defined in
    Part 1) refines a 3-step Atomic Specification via a backward
    simulation relation (cf. `BackwardSimulationRel` in
    `Leslie/Refinement.lean`).

    ### Atomic Specification (3-step scan)

    - `update(i, data)`: same as the implementation.
    - `scan()` proceeds in three steps:
      1. `s_call`:  `idle → s_called` (external call).
      2. `s_read`:  `s_called → s_read` — **deterministically** reads
         `mem.vals` into `local_snap t`.  This is the linearization point.
      3. `s_ret`:   `s_read → returned` — returns `local_snap t`.

    ### Key insight: linearization at `snap`

    The `snap` action in the Concurrent Specification atomically reads
    `mem.vals` and appends it to `snaps`.  In the backward simulation,
    we observe the *abstract post-state* `a'` and decide:

    - If `a'.pc t = .s_called`: the abstract scan hasn't read yet.
      The `snap` is a **stutter** (no abstract step).
    - If `a'.pc t = .s_read` with `a'.local_snap t ∈ old_snaps`:
      the abstract has already read, and the returned snapshot was
      in `snaps` *before* this snap.  **Stutter**.
    - If `a'.pc t = .s_read` with `a'.local_snap t ∉ old_snaps`:
      this `snap` produced the value that the abstract will return.
      Since `snap` appends `mem.vals` and `local_snap` is not in the
      old list, it must equal `mem.vals`.  The abstract performs
      `s_read`, which also reads `mem.vals`.  **This is the
      linearization point.**  Both `snap` and `s_read` read `mem` at
      the same moment, so they agree.

    ### Backward simulation relation (`bsim_rel2`)

    Relates `AState` (Concurrent Specification) to `AtState` (Atomic
    Specification):

    1. **mem**: shared memory agrees.
    2. **op**: per-thread operations agree.
    3. **pc**: PCs correspond via `bpc_rel2`.  Unlike the forward
       simulation, this is NOT a function: `scanning` can map to
       either `s_called` (abstract hasn't read yet) or `s_read`
       (abstract has read — linearization happened at a `snap`).
    4. **ret**: at `returned`, concrete and abstract return values agree.
    5. **snap membership**: when `as.pc t = s_read` and the concrete
       is still `scanning`, `as.local_snap t ∈ cs.snaps t`.
    6. **local_snap = ret**: at `returned`, `as.local_snap t = as.ret t`.
       This ensures the backward `s_ret` step works: the abstract
       `s_ret` sets `ret := local_snap`, so they must agree.

    ### Step correspondence (backward)

    | Concrete action (`AAction`)   | Abstract steps (backwards)              |
    |-------------------------------|-----------------------------------------|
    | `u_call`, `u_write`, `u_ret`  | matching step (1 step)                  |
    | `s_call`                      | abstract `s_call` (1 step)              |
    | `snap` (scanning → scanning)  | stutter OR `s_read` (linearization)     |
    | `s_ret` (scanning → returned) | abstract `s_ret` (1 step)               |
-/

/-! ### Atomic Specification (3-step scan, deterministic `s_read`) -/

/-- Atomic program counter.
    - **Update path**: `idle → u_called → u_done → returned`.
    - **Scan path**: `idle → s_called → s_read → returned`. -/
inductive AtPC where
  | idle | u_called | u_done | s_called | s_read | returned
  deriving DecidableEq

/-- Atomic state.
    - `local_snap t`: holds the snapshot value read at `s_read`.
      Only meaningful when `pc t ∈ {s_read, returned}`. -/
structure AtState (n : Nat) (Val : Type) (Tid : Type) where
  mem        : Fin n → Cell Val
  pc         : Tid → AtPC
  op         : Tid → Op n Val
  local_snap : Tid → (Fin n → Val)
  ret        : Tid → (Fin n → Val)

/-- Atomic action labels (6 actions: 3 for update + 3 for scan). -/
inductive AtAction (n : Nat) (Val : Type) (Tid : Type) where
  | u_call (t : Tid) | u_write (t : Tid) | u_ret (t : Tid)
  | s_call (t : Tid)   -- scan: idle → s_called
  | s_read (t : Tid)   -- scan: s_called → s_read (deterministic snapshot)
  | s_ret (t : Tid)    -- scan: s_read → returned (ret := local_snap)

/-- The Atomic Specification (3-step scan).
    - `s_call`: enters `s_called`.
    - `s_read`: **deterministic** — reads `mem.vals` into `local_snap t`.
    - `s_ret`:  returns `local_snap t`. -/
def atomic_snap : ActionSpec (AtState n Val Tid) (AtAction n Val Tid) where
  init := fun s =>
    (∀ i, s.mem i = ⟨default, 0⟩) ∧ (∀ t, s.pc t = .idle) ∧
    (∀ t, s.ret t = fun _ => default)
  actions := fun
    | .u_call t => {
        gate := fun s => s.pc t = .idle ∧ ∃ i d, s.op t = .update i d
        transition := fun s s' =>
          s' = { s with pc := fun t' => if t' = t then .u_called else s.pc t' } }
    | .u_write t => {
        gate := fun s => s.pc t = .u_called ∧ ∃ i d, s.op t = .update i d
        transition := fun s s' =>
          ∃ i d, s.op t = .update i d ∧
          s' = { s with
            mem := fun j => if j = i then ⟨d, (s.mem i).ver + 1⟩ else s.mem j
            pc := fun t' => if t' = t then .u_done else s.pc t' } }
    | .u_ret t => {
        gate := fun s => s.pc t = .u_done
        transition := fun s s' =>
          s' = { s with pc := fun t' => if t' = t then .returned else s.pc t' } }
    | .s_call t => {
        gate := fun s => s.pc t = .idle ∧ s.op t = .scan
        transition := fun s s' =>
          s' = { s with pc := fun t' => if t' = t then .s_called else s.pc t' } }
    | .s_read t => {
        -- Deterministic read: local_snap t := fun i => (mem i).val
        gate := fun s => s.pc t = .s_called
        transition := fun s s' =>
          s' = { s with
            pc := fun t' => if t' = t then .s_read else s.pc t'
            local_snap := fun t' => if t' = t
              then fun i => (s.mem i).val else s.local_snap t' } }
    | .s_ret t => {
        -- Deterministic return: set ret := local_snap (chosen at s_read)
        gate := fun s => s.pc t = .s_read
        transition := fun s s' =>
          s' = { s with
            pc := fun t' => if t' = t then .returned else s.pc t'
            ret := fun t' => if t' = t then s.local_snap t else s.ret t' } }

/-! ### Backward simulation relation -/

/-- Extensional equality for `AtState`: two states are equal iff all
    five fields agree. -/
private theorem at_state_eq {a b : AtState n Val Tid}
    (h1 : a.mem = b.mem) (h2 : a.pc = b.pc) (h3 : a.op = b.op)
    (h4 : a.local_snap = b.local_snap) (h5 : a.ret = b.ret) :
    a = b := by
  cases a; cases b; simp_all

/-- Extensional equality for `AState`. -/
private theorem a_state_eq {a b : AState n Val Tid}
    (h1 : a.mem = b.mem) (h2 : a.pc = b.pc) (h3 : a.op = b.op)
    (h4 : a.snaps = b.snaps) (h5 : a.ret = b.ret) :
    a = b := by
  cases a; cases b; simp_all

/-- PC correspondence for the backward simulation from the Concurrent
    Specification to the Atomic Specification.

    The key design: `scanning` can map to EITHER `s_called` (the
    atomic scan hasn't read yet) or `s_read` (the atomic scan has read
    but not returned).  This non-functionality is essential for the
    `snap` case, where we decide whether to linearize based on whether
    `local_snap` is in the old snaps list. -/
def bpc_rel2 : APC → AtPC → Prop
  | .idle,     .idle      => True
  | .u_called, .u_called  => True
  | .u_done,   .u_done    => True
  | .scanning, .s_called  => True
  | .scanning, .s_read    => True   -- scanning can map to either!
  | .returned, .returned  => True
  | _,         _          => False

@[simp] theorem bpc_rel2_idle : bpc_rel2 APC.idle apc ↔ apc = AtPC.idle := by
  cases apc <;> simp [bpc_rel2]
@[simp] theorem bpc_rel2_u_called : bpc_rel2 APC.u_called apc ↔ apc = AtPC.u_called := by
  cases apc <;> simp [bpc_rel2]
@[simp] theorem bpc_rel2_u_done : bpc_rel2 APC.u_done apc ↔ apc = AtPC.u_done := by
  cases apc <;> simp [bpc_rel2]
@[simp] theorem bpc_rel2_scanning :
    bpc_rel2 APC.scanning apc ↔ apc = AtPC.s_called ∨ apc = AtPC.s_read := by
  cases apc <;> simp [bpc_rel2]
@[simp] theorem bpc_rel2_returned : bpc_rel2 APC.returned apc ↔ apc = AtPC.returned := by
  cases apc <;> simp [bpc_rel2]

/-- The backward simulation relation from the Concurrent Specification
    (`abst_snap`) to the Atomic Specification (`atomic_snap`).

    **Condition 1** (`mem`):  shared memory agrees.
    **Condition 2** (`op`):   per-thread operations agree.
    **Condition 3** (`pc`):   PCs correspond via `bpc_rel2`.
    **Condition 4** (`ret`):  at `returned`, return values agree.
    **Condition 5** (`snap`): when the abstract is at `s_read` and the
      concrete is still `scanning`, `local_snap t ∈ snaps t` — the
      abstract's chosen snapshot is among the concrete's accumulated
      snapshots.
    **Condition 6** (`ls_ret`): at `returned`, `local_snap = ret` in
      the abstract.  This ensures the `s_ret` backward step works:
      the abstract `s_ret` sets `ret := local_snap`, so we need them
      to agree at `returned`. -/
def bsim_rel2 (cs : AState n Val Tid) (as : AtState n Val Tid) : Prop :=
  cs.mem = as.mem ∧
  cs.op = as.op ∧
  (∀ t, bpc_rel2 (cs.pc t) (as.pc t)) ∧
  (∀ t, cs.pc t = .returned → cs.ret t = as.ret t) ∧
  (∀ t, as.pc t = .s_read → cs.pc t = .scanning →
    as.local_snap t ∈ cs.snaps t) ∧
  (∀ t, cs.pc t = .returned → as.local_snap t = as.ret t)

/-! ### The backward simulation proof -/

/-- **Part 2 main theorem**: the Concurrent Specification is a backward
    simulation of the Atomic Specification.

    The linearization point is the `snap` action that produces the
    snapshot value the abstract scanner will return.  Looking backwards:
    if `local_snap t ∉ old_snaps` but `local_snap t ∈ old_snaps ++ [mem.vals]`,
    then `local_snap t = mem.vals`.  The abstract performs `s_read`,
    which deterministically sets `local_snap t := mem.vals`.  Since both
    the concrete `snap` and abstract `s_read` read `mem` at the same
    moment, they agree.  **Sorry-free.** -/
def backward_snap_atomic_sim :
    BackwardSimulationRel (AState n Val Tid) (AtState n Val Tid) where
  concrete := (abst_snap (n := n) (Val := Val) (Tid := Tid)).toSpec
  abstract := (atomic_snap (n := n) (Val := Val) (Tid := Tid)).toSpec
  R := bsim_rel2

  -- ── Initial states ──────────────────────────────────────────────
  init_sim := by
    intro s ⟨hmem, hpc, hsnaps, hret⟩
    refine ⟨⟨s.mem, fun _ => .idle, s.op,
             fun _ => fun _ => default, fun _ => fun _ => default⟩,
            ⟨hmem, fun _ => rfl, fun _ => rfl⟩,
            rfl, rfl,
            fun t => by simp [bpc_rel2, hpc],
            fun t ht => by simp [hpc] at ht,
            fun t hread _ => by simp at hread,
            fun t ht => by simp [hpc] at ht⟩

  -- ── Backward step simulation ───────────────────────────────────
  -- Given: concrete step cs → cs', and abstract post-state a' with
  --        bsim_rel2 cs' a'.
  -- Find:  abstract pre-state a₀ with bsim_rel2 cs a₀ and
  --        Star atomic_snap.next a₀ a'.
  step_sim := by
    intro cs cs' a' hR ⟨act, hg, htrans⟩
    obtain ⟨hmem', hop', hpc_r', hret', hsnap_inv', hls_ret'⟩ := hR
    cases act with

    -- ══════════════════════════════════════════════════════════════
    --  UPDATE ACTIONS: one-to-one correspondence
    -- ══════════════════════════════════════════════════════════════

    | u_call t =>
      obtain ⟨hpc_t, i, d, hop_t⟩ := hg; subst htrans
      have ha' : a'.pc t = .u_called := by
        have := hpc_r' t; simp at this; exact this
      let a₀ : AtState n Val Tid :=
        { a' with pc := fun t' => if t' = t then .idle else a'.pc t' }
      refine ⟨a₀, Star.single ⟨.u_call t, ⟨?_, i, d, ?_⟩, ?_⟩,
              ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [a₀]
      · show a₀.op t = .update i d; simp [a₀, ← hop', hop_t]
      · apply at_state_eq <;> simp [a₀]
        funext t'; by_cases h : t' = t <;> simp [h, ha']
      · exact hmem'
      · exact hop'
      · intro t'; by_cases h : t' = t
        · simp [a₀, h, hpc_t, bpc_rel2]
        · simp [a₀, h]; have := hpc_r' t'; simp [h] at this; exact this
      · intro t' hret_t'
        have hne : t' ≠ t := by intro heq; rw [heq, hpc_t] at hret_t'; simp at hret_t'
        have := hret' t'; simp [hne] at this; exact this hret_t'
      · intro t' hread hscan
        have hne : t' ≠ t := by intro heq; simp [a₀, heq] at hread
        simp [a₀, hne] at hread
        exact hsnap_inv' t' hread (by simp [hne] at hscan ⊢; exact hscan)
      · intro t' hret_t'
        have hne : t' ≠ t := by intro heq; rw [heq, hpc_t] at hret_t'; simp at hret_t'
        show a'.local_snap t' = a'.ret t'
        exact hls_ret' t' (by simp [hne] at hret_t' ⊢; exact hret_t')

    | u_write t =>
      obtain ⟨hpc_t, _⟩ := hg
      obtain ⟨i, d, hop_eq, hs'⟩ := htrans; subst hs'
      have ha' : a'.pc t = .u_done := by
        have := hpc_r' t; simp at this; exact this
      let a₀ : AtState n Val Tid :=
        { a' with
          mem := cs.mem
          pc := fun t' => if t' = t then .u_called else a'.pc t' }
      refine ⟨a₀, Star.single ⟨.u_write t, ⟨?_, i, d, ?_⟩, i, d, ?_, ?_⟩,
              ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [a₀]
      · show a₀.op t = .update i d; simp [a₀, ← hop', hop_eq]
      · show a₀.op t = .update i d; simp [a₀, ← hop', hop_eq]
      · apply at_state_eq
        · simp [a₀]; exact hmem'.symm
        · simp [a₀]; funext t'; by_cases h : t' = t <;> simp [h, ha']
        · simp [a₀]
        · simp [a₀]
        · simp [a₀]
      · simp [a₀]
      · show cs.op = a₀.op; simp [a₀]; exact hop'
      · intro t'; by_cases h : t' = t
        · simp [a₀, h, hpc_t, bpc_rel2]
        · simp [a₀, h]; have := hpc_r' t'; simp [h] at this; exact this
      · intro t' hret_t'
        have hne : t' ≠ t := by intro heq; rw [heq, hpc_t] at hret_t'; simp at hret_t'
        have := hret' t'; simp [hne] at this; exact this hret_t'
      · intro t' hread hscan
        have hne : t' ≠ t := by intro heq; simp [a₀, heq] at hread
        simp [a₀, hne] at hread
        exact hsnap_inv' t' hread (by simp [hne] at hscan ⊢; exact hscan)
      · intro t' hret_t'
        have hne : t' ≠ t := by intro heq; rw [heq, hpc_t] at hret_t'; simp at hret_t'
        show a'.local_snap t' = a'.ret t'
        exact hls_ret' t' (by simp [hne] at hret_t' ⊢; exact hret_t')

    | u_ret t =>
      subst htrans
      have hpc_t' : cs.pc t = .u_done := hg
      have ha' : a'.pc t = .returned := by
        have := hpc_r' t; simp at this; exact this
      let a₀ : AtState n Val Tid :=
        { a' with pc := fun t' => if t' = t then .u_done else a'.pc t' }
      refine ⟨a₀, Star.single ⟨.u_ret t, ?_, ?_⟩,
              ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show a₀.pc t = .u_done; simp [a₀]
      · apply at_state_eq <;> simp [a₀]
        funext t'; by_cases h : t' = t <;> simp [h, ha']
      · exact hmem'
      · exact hop'
      · intro t'; by_cases h : t' = t
        · simp [a₀, h, hpc_t', bpc_rel2]
        · simp [a₀, h]; have := hpc_r' t'; simp [h] at this; exact this
      · intro t' hret_t'
        by_cases h : t' = t
        · rw [h, hpc_t'] at hret_t'; simp at hret_t'
        · have := hret' t'; simp [h] at this; exact this hret_t'
      · intro t' hread hscan
        have hne : t' ≠ t := by intro heq; simp [a₀, heq] at hread
        simp [a₀, hne] at hread
        exact hsnap_inv' t' hread (by simp [hne] at hscan ⊢; exact hscan)
      · intro t' hret_t'
        by_cases h : t' = t
        · rw [h, hpc_t'] at hret_t'; simp at hret_t'
        · show a'.local_snap t' = a'.ret t'
          exact hls_ret' t' (by simp [h] at hret_t' ⊢; exact hret_t')

    -- ══════════════════════════════════════════════════════════════
    --  S_CALL: abstract s_call (1 step backward)
    -- ══════════════════════════════════════════════════════════════

    | s_call t =>
      obtain ⟨hpc_t, hop_t⟩ := hg; subst htrans
      -- Normalize: s_call only changes pc and snaps for t.
      -- cs'.mem = cs.mem, cs'.pc t = scanning, cs'.snaps t = []
      have hmem_eq : cs.mem = a'.mem := hmem'
      have hop_eq : cs.op = a'.op := hop'
      have ha' : a'.pc t = .s_called ∨ a'.pc t = .s_read := by
        have := hpc_r' t; simp at this; exact this
      have ha'_called : a'.pc t = .s_called := by
        rcases ha' with h | h
        · exact h
        · exfalso
          have h5 := hsnap_inv' t h (by simp)
          simp at h5
      let a₀ : AtState n Val Tid :=
        { a' with pc := fun t' => if t' = t then .idle else a'.pc t' }
      refine ⟨a₀, Star.single ⟨.s_call t, ⟨?_, ?_⟩, ?_⟩,
              ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [a₀]
      · show a₀.op t = .scan; simp [a₀, ← hop_eq, hop_t]
      · apply at_state_eq <;> simp [a₀]
        funext t'; by_cases h : t' = t <;> simp [h, ha'_called]
      · exact hmem_eq
      · exact hop_eq
      · intro t'; by_cases h : t' = t
        · simp [a₀, h, hpc_t, bpc_rel2]
        · simp [a₀, h]; have := hpc_r' t'; simp [h] at this ⊢; exact this
      · intro t' hret_t'
        have hne : t' ≠ t := by intro heq; rw [heq, hpc_t] at hret_t'; simp at hret_t'
        have := hret' t' (by simp [hne]; exact hret_t')
        simp at this; exact this
      · intro t' hread hscan
        have hne : t' ≠ t := by intro heq; simp [a₀, heq] at hread
        simp [a₀, hne] at hread
        have h5 := hsnap_inv' t' hread (by simp [hne]; exact hscan)
        simp [hne] at h5; exact h5
      · intro t' hret_t'
        have hne : t' ≠ t := by intro heq; rw [heq, hpc_t] at hret_t'; simp at hret_t'
        exact hls_ret' t' (by simp [hne]; exact hret_t')

    -- ══════════════════════════════════════════════════════════════
    --  SNAP: the KEY case — stutter or linearization
    --
    --  Concrete: scanning → scanning, snaps ← snaps ++ [mem.vals].
    --  Post-state a' has scanning, so a'.pc t ∈ {s_called, s_read}.
    --
    --  Case 1 (a'.pc t = .s_called):
    --    Stutter.  Pre has fewer snaps, abstract still s_called.
    --
    --  Case 2 (a'.pc t = .s_read):
    --    Condition 5 gives: a'.local_snap t ∈ snaps_post = old ++ [mem.vals].
    --    Sub-case 2a: a'.local_snap t ∈ old_snaps → stutter.
    --    Sub-case 2b: a'.local_snap t ∉ old_snaps →
    --      a'.local_snap t must be the new element, i.e. mem.vals.
    --      This is the LINEARIZATION POINT.  Abstract does s_read,
    --      which sets local_snap t := mem.vals (deterministic).
    --      Since both snap and s_read read mem at the same moment,
    --      they agree.  No sorry needed.
    -- ══════════════════════════════════════════════════════════════

    | snap t =>
      have hpc_t : cs.pc t = .scanning := hg
      -- snap only changes snaps; cs'.pc = cs.pc, cs'.mem = cs.mem, cs'.ret = cs.ret.
      -- We subst then use the fact that the record update preserves other fields.
      subst htrans
      -- After subst, all hypotheses reference the expanded record { cs with snaps := ... }.
      -- Key simplification: pc, mem, op, ret are unchanged by snap.
      -- We introduce clean versions of the hypotheses.
      replace hmem' : cs.mem = a'.mem := hmem'
      replace hop' : cs.op = a'.op := hop'
      replace hpc_r' : ∀ t₀, bpc_rel2 (cs.pc t₀) (a'.pc t₀) := by
        intro t₀; have := hpc_r' t₀; simp at this; exact this
      replace hret' : ∀ t₀, cs.pc t₀ = .returned → cs.ret t₀ = a'.ret t₀ := by
        intro t₀ h; have := hret' t₀ (by simp; exact h); simp at this; exact this
      replace hls_ret' : ∀ t₀, cs.pc t₀ = .returned → a'.local_snap t₀ = a'.ret t₀ := by
        intro t₀ h; exact hls_ret' t₀ (by simp; exact h)
      -- hsnap_inv' references the UPDATED snaps; we normalize per-thread.
      have hsnap_inv_norm : ∀ t₀, a'.pc t₀ = .s_read → cs.pc t₀ = .scanning →
          a'.local_snap t₀ ∈ (if t₀ = t then cs.snaps t ++ [fun i => (cs.mem i).val]
                                          else cs.snaps t₀) := by
        intro t₀ hr hs; have := hsnap_inv' t₀ hr (by simp; exact hs); simp at this ⊢
        by_cases h : t₀ = t <;> simp [h] at this ⊢ <;> exact this
      have ha' : a'.pc t = .s_called ∨ a'.pc t = .s_read := by
        have := hpc_r' t; rw [hpc_t, bpc_rel2_scanning] at this; exact this
      -- hsnap_inv_norm: normalized version of hsnap_inv' using cs.snaps directly
      rcases ha' with ha'_called | ha'_read
      · -- ── Case 1: a'.pc t = s_called ── STUTTER ──
        refine ⟨a', .refl, hmem', hop', ?_, ?_, ?_, ?_⟩
        · intro t'; by_cases h : t' = t
          · simp [h, hpc_t, bpc_rel2, ha'_called]
          · exact hpc_r' t'
        · intro t' hret_t'
          have hne : t' ≠ t := by intro heq; rw [heq, hpc_t] at hret_t'; simp at hret_t'
          exact hret' t' hret_t'
        · intro t' hread hscan
          by_cases h : t' = t
          · rw [h] at hread; rw [ha'_called] at hread; simp at hread
          · have := hsnap_inv_norm t' hread hscan; simp [h] at this; exact this
        · intro t' hret_t'
          have hne : t' ≠ t := by intro heq; rw [heq, hpc_t] at hret_t'; simp at hret_t'
          exact hls_ret' t' hret_t'

      · -- ── Case 2: a'.pc t = s_read ── Decide stutter vs. linearize ──
        -- From condition 5: local_snap t ∈ snaps_post = old ++ [mem.vals].
        have hmem_snap : a'.local_snap t ∈
            cs.snaps t ++ [fun i => (cs.mem i).val] := by
          have := hsnap_inv_norm t ha'_read hpc_t; simp at this
          rcases this with h | h
          · exact List.mem_append.mpr (Or.inl h)
          · exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr h))
        rcases Classical.em (a'.local_snap t ∈ cs.snaps t) with h_in_old | h_not_in_old
        · -- ── Sub-case 2a: local_snap ∈ old_snaps ── STUTTER ──
          refine ⟨a', .refl, hmem', hop', ?_, ?_, ?_, ?_⟩
          · intro t'; by_cases h : t' = t
            · simp [h, hpc_t, bpc_rel2, ha'_read]
            · exact hpc_r' t'
          · intro t' hret_t'
            have hne : t' ≠ t := by intro heq; rw [heq, hpc_t] at hret_t'; simp at hret_t'
            exact hret' t' hret_t'
          · intro t' hread hscan
            by_cases h : t' = t
            · rw [h]; exact h_in_old
            · have := hsnap_inv_norm t' hread hscan; simp [h] at this; exact this
          · intro t' hret_t'
            have hne : t' ≠ t := by intro heq; rw [heq, hpc_t] at hret_t'; simp at hret_t'
            exact hls_ret' t' hret_t'

        · -- ── Sub-case 2b: local_snap ∉ old_snaps ── LINEARIZATION ──
          -- Since local_snap ∈ old ++ [mem.vals] but ∉ old, it must equal mem.vals.
          have hls_eq : a'.local_snap t = fun i => (cs.mem i).val := by
            rw [List.mem_append] at hmem_snap
            rcases hmem_snap with h | h
            · exact absurd h h_not_in_old
            · exact List.mem_singleton.mp h
          -- Construct abstract pre-state with s_called (about to do s_read)
          let a₀ : AtState n Val Tid :=
            { a' with
              pc := fun t' => if t' = t then .s_called else a'.pc t'
              local_snap := fun t' => if t' = t
                then fun i => (cs.mem i).val else a'.local_snap t' }
          -- Abstract does s_read: s_called → s_read, local_snap := mem.vals.
          -- This is the LINEARIZATION POINT: both the concrete snap and
          -- the abstract s_read read mem.vals at exactly this moment.
          refine ⟨a₀, Star.single ⟨.s_read t, ?_, ?_⟩,
                  hmem', hop', ?_, ?_, ?_, ?_⟩
          · -- gate: a₀.pc t = s_called
            show a₀.pc t = .s_called; simp [a₀]
          · -- transition: a' = {a₀ with pc := s_read, local_snap := mem.vals}
            apply at_state_eq
            · simp [a₀]
            · simp [a₀]; funext t'; by_cases h : t' = t <;> simp [h, ha'_read]
            · simp [a₀]
            · simp [a₀]; funext t'; by_cases h : t' = t
              · simp [h, hls_eq]; funext i; simp [hmem']
              · simp [h]
            · simp [a₀]
          · -- pc
            intro t'; by_cases h : t' = t
            · simp [a₀, h, hpc_t, bpc_rel2]
            · simp [a₀, h]; exact hpc_r' t'
          · -- ret at returned: scanning ≠ returned → vacuous for t
            intro t' hret_t'
            have hne : t' ≠ t := by intro heq; rw [heq, hpc_t] at hret_t'; simp at hret_t'
            exact hret' t' hret_t'
          · -- condition 5: a₀.pc t = s_called (not s_read) → vacuous for t
            intro t' hread hscan
            have hne : t' ≠ t := by intro heq; simp [a₀, heq] at hread
            -- a₀.local_snap t' = a'.local_snap t' (since t' ≠ t)
            show a₀.local_snap t' ∈ cs.snaps t'
            simp [a₀, hne]
            simp [a₀, hne] at hread
            have := hsnap_inv_norm t' hread hscan; simp [hne] at this; exact this
          · -- condition 6: at returned → local_snap = ret. Vacuous for t.
            intro t' hret_t'
            have hne : t' ≠ t := by intro heq; rw [heq, hpc_t] at hret_t'; simp at hret_t'
            simp [a₀, hne]; exact hls_ret' t' hret_t'

    -- ══════════════════════════════════════════════════════════════
    --  S_RET: abstract s_ret (1 step backward)
    --
    --  Concrete: scanning → returned, ret t := rv, rv ∈ snaps t.
    --  Post: a'.pc t = returned.  Abstract pre: s_read → returned.
    --
    --  From condition 6 at the post-state: a'.local_snap t = a'.ret t.
    --  This is the key: abstract s_ret sets ret := local_snap, and
    --  we know they agree at the post-state.
    -- ══════════════════════════════════════════════════════════════

    | s_ret t =>
      obtain ⟨hpc_t, hsnaps_ne⟩ := hg
      obtain ⟨rv, hrv_mem, hs'⟩ := htrans; subst hs'
      have ha' : a'.pc t = .returned := by
        have := hpc_r' t; simp at this; exact this
      -- From condition 4: rv = a'.ret t
      have hret_eq : rv = a'.ret t := by
        have := hret' t (by simp); simp at this; exact this
      -- From condition 6: a'.local_snap t = a'.ret t
      have hls_eq : a'.local_snap t = a'.ret t :=
        hls_ret' t (by simp)
      -- Construct a₀ with s_read; abstract does s_ret: ret := local_snap
      let a₀ : AtState n Val Tid :=
        { a' with
          pc := fun t' => if t' = t then .s_read else a'.pc t'
          ret := fun t' => if t' = t then a'.local_snap t else a'.ret t' }
      refine ⟨a₀, Star.single ⟨.s_ret t, ?_, ?_⟩,
              ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- gate: a₀.pc t = s_read
        show a₀.pc t = .s_read; simp [a₀]
      · -- transition: a' = {a₀ with pc t := returned, ret t := local_snap t}
        apply at_state_eq
        · simp [a₀]
        · simp [a₀]; funext t'; by_cases h : t' = t <;> simp [h, ha']
        · simp [a₀]
        · simp [a₀]
        · simp [a₀]; funext t'; by_cases h : t' = t
          · simp [h]; exact hls_eq.symm
          · simp [h]
      · -- bsim_rel2: mem
        exact hmem'
      · -- op
        exact hop'
      · -- pc: scanning ↔ s_read (via bpc_rel2)
        intro t'; by_cases h : t' = t
        · simp [a₀, h, hpc_t, bpc_rel2]
        · simp [a₀, h]; have := hpc_r' t'; simp [h] at this; exact this
      · -- ret at returned: cs.pc t = scanning ≠ returned, vacuous for t
        intro t' hret_t'
        by_cases h : t' = t
        · rw [h, hpc_t] at hret_t'; simp at hret_t'
        · simp only [a₀, h, ite_false]
          have := hret' t'; simp [h] at this; exact this hret_t'
      · -- condition 5: at s_read with scanning → local_snap ∈ snaps
        -- For t: cs.pc t = scanning and a₀.pc t = s_read.
        -- Need: a'.local_snap t ∈ cs.snaps t.
        -- From hls_eq: a'.local_snap t = a'.ret t = rv (from hret_eq).
        -- rv ∈ cs.snaps t (from hrv_mem).
        intro t' hread hscan
        by_cases h : t' = t
        · simp [a₀, h] at hread
          rw [h]; rw [hls_eq, ← hret_eq]; exact hrv_mem
        · simp [a₀, h] at hread
          exact hsnap_inv' t' hread (by simp [h] at hscan ⊢; exact hscan)
      · -- condition 6: at returned, local_snap = ret
        -- For t: cs.pc t = scanning ≠ returned → vacuous
        intro t' hret_t'
        by_cases h : t' = t
        · rw [h, hpc_t] at hret_t'; simp at hret_t'
        · simp [a₀, h]
          exact hls_ret' t' (by simp [h] at hret_t' ⊢; exact hret_t')

end Snapshot
