import Leslie.AssumeGuarantee
import Leslie.Examples.CacheCoherence.MESI

/-! ## Parameterized MESI Cache Coherence Protocol

    ### Overview

    This file models the MESI cache coherence protocol for an arbitrary
    number of processors and proves the **SWMR (Single-Writer / Multiple-Reader)**
    property: in every reachable state, if any cache holds a line in
    Modified or Exclusive state, then every other cache holds it in Invalid.

    ### The model

    We model a snoopy-bus MESI protocol for a single cache line shared
    among `n + 1` processors. The protocol is formalized as a
    `SymSharedSpec` (see `Leslie/SymShared.lean`), which packages:

    - **Shared state** (`Val`): main memory value
    - **Local state** (`CacheState × Val`): per-processor cache state and cached value
    - **Actions** (`MESIAct`): `prRd` (processor read), `prWr v` (processor write),
      `evict` (cache eviction)

    Each action is modeled as the atomic combined effect of a processor
    request plus the resulting bus transaction and snoop responses.
    This is standard for TLA-style models of snoopy protocols, since
    the bus serializes all transactions.

    The transition relation (`mesi_sym.step`) has 10 cases:
    - **PrRd** (from Invalid): 4 subcases based on other caches' states.
      The reader gets Shared or Exclusive; an M holder flushes to memory.
    - **PrWr v**: 4 subcases (from I, S, E, M). Writes from I or S issue
      a bus invalidation; writes from E or M are silent.
    - **Evict**: 3 subcases (from M, E, S). An M eviction writes back.

    ### The proof

    The main theorem `mesi_param_swmr` states:

    > For all `n`, in every execution of the `(n+1)`-process MESI system
    > satisfying the safety specification (valid initial state and closed
    > under transitions), the SWMR property holds at every step.

    The proof is by **direct inductive invariant**. We define `conc_swmr`
    (the SWMR predicate on concrete N-process states) and show:

    1. **Base case** (`init → conc_swmr`): All caches start in I,
       so no two caches can both be in M or E.

    2. **Inductive step** (`conc_swmr ∧ next → conc_swmr'`): For each
       of the 10 transition cases, we show SWMR is preserved. The key
       arguments by case:
       - *PrRd*: The reader was in I and gets S or E. If it gets E, all
         others were already I (by the case guard). If it gets S, the
         snooped M/E cache also transitions to S. No new M or E is created
         that would violate SWMR.
       - *PrWr from I or S* (BusRdX/BusUpgr): The writer goes to M and
         all other caches are invalidated. SWMR holds trivially since
         only the writer has a non-I state.
       - *PrWr from E or M* (silent): The writer goes/stays M, others are
         unchanged. By the pre-state SWMR, others were already I (since
         the writer had E or M). So SWMR is preserved.
       - *Evict*: The evicter goes to I. This cannot create a new M or E
         violation; if anyone else had M/E, the pre-state SWMR already
         ensured the evicter was I.

    The proof uses `init_invariant` from Leslie's TLA rule library, which
    packages the base + inductive step into `□ conc_swmr`.

    ### Symmetry

    We also prove `mesi_symmetric`: the MESI specification is invariant
    under permutation of process indices (`IsSymmetric`). This is not
    used by the SWMR proof (which is directly inductive on the concrete
    system), but would be needed for lifting single-process properties to
    all processes via the `forall_from_focus` framework — useful for
    future properties like the data value invariant or linearizability.
-/

open TLA SymShared MESI

namespace MESIParam

/-! ### MESI Action Types -/

/-- Actions available to each processor. These are processor-initiated
    events; the bus transaction and snoop responses are folded into the
    atomic step in `mesi_sym.step`. -/
inductive MESIAct where
  | prRd          -- processor read (miss from I triggers BusRd)
  | prWr (v : Val) -- processor write (miss triggers BusRdX or BusUpgr)
  | evict          -- voluntary eviction / replacement
  deriving DecidableEq

/-! ### MESI as a Symmetric Shared-Memory Specification -/

/-- The MESI protocol for `n` processors sharing a single cache line.

    **Shared state**: main memory value (`Val = Nat`).

    **Local state per processor**: `(CacheState, Val)` — the cache state
    (M/E/S/I) and the cached data value.

    **Transitions** (`step n i a s s'`): process `i` performs action `a`,
    atomically updating the shared memory and all processors' local states
    (modeling the combined effect of the processor request, bus transaction,
    and snoop responses). -/
def mesi_sym : SymSharedSpec where
  Shared := Val
  Local := CacheState × Val
  ActType := MESIAct
  init_shared := fun mem => mem = 0
  init_local := fun ⟨cs, v⟩ => cs = .I ∧ v = 0
  step := fun n i a s s' =>
    match a with
    | .prRd =>
      -- PrRd: process i reads. Precondition: cache i is Invalid.
      -- (Reads from M/E/S are cache hits — no state change, modeled as stuttering.)
      (s.locals i).1 = .I ∧
      (-- Case 1: some j ≠ i has M — j flushes dirty value to memory, both go S
       (∃ j : Fin n, j ≠ i ∧ (s.locals j).1 = .M ∧
        s'.shared = (s.locals j).2 ∧
        s'.locals = fun k =>
          if k = i then (.S, (s.locals j).2)
          else if k = j then (.S, (s.locals j).2)
          else s.locals k) ∨
      -- Case 2: no M, some j ≠ i has E — j goes S, i gets S from memory
       ((¬∃ j : Fin n, j ≠ i ∧ (s.locals j).1 = .M) ∧
        (∃ j : Fin n, j ≠ i ∧ (s.locals j).1 = .E) ∧
        s'.shared = s.shared ∧
        s'.locals = fun k =>
          if k = i then (.S, s.shared)
          else if (s.locals k).1 = .E then (.S, (s.locals k).2)
          else s.locals k) ∨
      -- Case 3: no M, no E, some j ≠ i has S — i gets S from memory
       ((¬∃ j : Fin n, j ≠ i ∧ (s.locals j).1 = .M) ∧
        (¬∃ j : Fin n, j ≠ i ∧ (s.locals j).1 = .E) ∧
        (∃ j : Fin n, j ≠ i ∧ (s.locals j).1 = .S) ∧
        s'.shared = s.shared ∧
        s'.locals = fun k =>
          if k = i then (.S, s.shared)
          else s.locals k) ∨
      -- Case 4: all others Invalid — i gets E from memory
       ((∀ j : Fin n, j ≠ i → (s.locals j).1 = .I) ∧
        s'.shared = s.shared ∧
        s'.locals = fun k =>
          if k = i then (.E, s.shared)
          else s.locals k))

    | .prWr v =>
      -- PrWr v: process i writes value v.
      -- Case 1: from I — issues BusRdX (read-exclusive), invalidates all others
      (((s.locals i).1 = .I ∧
        ((∃ j : Fin n, j ≠ i ∧ (s.locals j).1 = .M ∧
          s'.shared = (s.locals j).2 ∧
          s'.locals = fun k =>
            if k = i then (.M, v)
            else (.I, (s.locals k).2)) ∨
         (¬∃ j : Fin n, j ≠ i ∧ (s.locals j).1 = .M) ∧
          s'.shared = s.shared ∧
          s'.locals = fun k =>
            if k = i then (.M, v)
            else (.I, (s.locals k).2))) ∨
      -- Case 2: from S — BusUpgr, invalidate others
       ((s.locals i).1 = .S ∧
        s'.shared = s.shared ∧
        s'.locals = fun k =>
          if k = i then (.M, v)
          else (.I, (s.locals k).2)) ∨
      -- Case 3: from E — silent upgrade, no bus needed
       ((s.locals i).1 = .E ∧
        s'.shared = s.shared ∧
        s'.locals = fun k =>
          if k = i then (.M, v)
          else s.locals k) ∨
      -- Case 4: from M — overwrite
       ((s.locals i).1 = .M ∧
        s'.shared = s.shared ∧
        s'.locals = fun k =>
          if k = i then (.M, v)
          else s.locals k))

    | .evict =>
      -- Evict: process i voluntarily evicts its cache line.
      (-- Case 1: from M — writeback dirty value to memory, go I
       ((s.locals i).1 = .M ∧
        s'.shared = (s.locals i).2 ∧
        s'.locals = fun k =>
          if k = i then (.I, (s.locals i).2)
          else s.locals k) ∨
       ((s.locals i).1 = .E ∧
        s'.shared = s.shared ∧
        s'.locals = fun k =>
          if k = i then (.I, (s.locals i).2)
          else s.locals k) ∨
       ((s.locals i).1 = .S ∧
        s'.shared = s.shared ∧
        s'.locals = fun k =>
          if k = i then (.I, (s.locals i).2)
          else s.locals k))

/-! ### MESI Symmetry

    The MESI specification treats all process indices uniformly: the step
    relation is defined in terms of the acting process `i` and quantified
    conditions on "others" (`j ≠ i`), with no distinguished process.

    We prove this formally as `IsSymmetric`: for any permutation `π` on
    `Fin n`, if state `s` can step to `s'`, then the permuted state
    `s.perm π` can step to `s'.perm π`. The proof permutes the acting
    process index (`i ↦ π.fwd i`) and the witness indices (`j ↦ π.fwd j`),
    using the identity `π.inv k = i ↔ k = π.fwd i` to reindex the
    if-then-else branches in the locals update functions.
-/
private theorem inv_eq_iff {n : Nat} (π : Perm n) (k i : Fin n) :
    π.inv k = i ↔ k = π.fwd i := by
  constructor
  · intro h; have := congrArg π.fwd h; rw [π.fwd_inv] at this; exact this
  · intro h; have := congrArg π.inv h; rw [π.inv_fwd] at this; exact this

-- Helper: transfer negated existentials through permutation
private theorem not_exists_perm {n : Nat} (π : Perm n) (i : Fin n)
    (P : Fin n → Prop) (h : ¬∃ j, j ≠ i ∧ P j) :
    ¬∃ j, j ≠ π.fwd i ∧ P (π.inv j) := by
  intro ⟨j', hj'i, hj'P⟩
  apply h; refine ⟨π.inv j', ?_, hj'P⟩
  intro heq; apply hj'i
  have := congrArg π.fwd heq; rwa [π.fwd_inv] at this

-- Helper: reindex locals through permutation for the funext + by_cases pattern.
-- When π.inv k = i, we have k = π.fwd i.
-- When π.inv k ≠ i, we have k ≠ π.fwd i.
private theorem perm_ite_eq {n : Nat} {α : Type} (π : Perm n) (i : Fin n)
    (a b : α) (k : Fin n) :
    (if π.inv k = i then a else b) = (if k = π.fwd i then a else b) := by
  by_cases h : π.inv k = i
  · rw [if_pos h, if_pos ((inv_eq_iff π k i).mp h)]
  · rw [if_neg h, if_neg (fun h' => h ((inv_eq_iff π k i).mpr h'))]

-- Two-condition version for PrRd Case 1 (if k = i then ... else if k = j then ... else ...)
private theorem perm_ite_eq2 {n : Nat} {α : Type} (π : Perm n) (i j : Fin n)
    (a b c : α) (k : Fin n) :
    (if π.inv k = i then a else if π.inv k = j then b else c) =
    (if k = π.fwd i then a else if k = π.fwd j then b else c) := by
  by_cases hi : π.inv k = i
  · rw [if_pos hi, if_pos ((inv_eq_iff π k i).mp hi)]
  · rw [if_neg hi, if_neg (fun h => hi ((inv_eq_iff π k i).mpr h))]
    by_cases hj : π.inv k = j
    · rw [if_pos hj, if_pos ((inv_eq_iff π k j).mp hj)]
    · rw [if_neg hj, if_neg (fun h => hj ((inv_eq_iff π k j).mpr h))]

theorem mesi_symmetric : mesi_sym.IsSymmetric where
  init_perm := by
    intro n π s ⟨hshared, hlocals⟩
    exact ⟨hshared, fun i => hlocals (π.inv i)⟩
  step_perm := by
    intro n π s s' ⟨i, a, hstep⟩
    refine ⟨π.fwd i, a, ?_⟩
    have inv_fwd_i : π.inv (π.fwd i) = i := π.inv_fwd i
    simp only [mesi_sym] at hstep
    show mesi_sym.step n (π.fwd i) a (SymState.perm π s) (SymState.perm π s')
    simp only [mesi_sym]
    -- Key: (SymState.perm π s).locals k = s.locals (π.inv k)
    -- Key: (SymState.perm π s).shared = s.shared
    match a with
    | .prRd =>
      obtain ⟨hpre, hcases⟩ := hstep
      refine ⟨?_, ?_⟩
      · -- precondition: (s.perm π).locals (π.fwd i) |>.1 = .I
        show (s.locals (π.inv (π.fwd i))).1 = .I
        rw [inv_fwd_i]; exact hpre
      · rcases hcases with
          ⟨j, hji, hjM, hshared', hlocals'⟩ |
          ⟨hnoM, ⟨j, hji, hjE⟩, hshared', hlocals'⟩ |
          ⟨hnoM, hnoE, ⟨j, hji, hjS⟩, hshared', hlocals'⟩ |
          ⟨hallI, hshared', hlocals'⟩
        · -- Case 1: j has M → both i,j get S
          left
          refine ⟨π.fwd j, fun h => hji (π.fwd_injective h), ?_, ?_, ?_⟩
          · show (s.locals (π.inv (π.fwd j))).1 = .M
            rw [π.inv_fwd]; exact hjM
          · show s'.shared = (s.locals (π.inv (π.fwd j))).2
            rw [π.inv_fwd]; exact hshared'
          · show (fun k => s'.locals (π.inv k)) = fun k =>
                if k = π.fwd i then (CacheState.S, (s.locals (π.inv (π.fwd j))).2)
                else if k = π.fwd j then (CacheState.S, (s.locals (π.inv (π.fwd j))).2)
                else s.locals (π.inv k)
            funext k
            rw [congrFun hlocals' (π.inv k)]
            rw [π.inv_fwd]
            exact perm_ite_eq2 π i j _ _ _ k
        · -- Case 2: no M, some j has E → i gets S, E-holders go S
          right; left
          refine ⟨not_exists_perm π i (fun j => (s.locals j).1 = .M) hnoM,
                  ⟨π.fwd j, fun h => hji (π.fwd_injective h), ?_⟩, ?_, ?_⟩
          · show (s.locals (π.inv (π.fwd j))).1 = .E
            rw [π.inv_fwd]; exact hjE
          · show s'.shared = s.shared; exact hshared'
          · show (fun k => s'.locals (π.inv k)) = fun k =>
                if k = π.fwd i then (CacheState.S, s.shared)
                else if (s.locals (π.inv k)).1 = CacheState.E
                     then (CacheState.S, (s.locals (π.inv k)).2)
                     else s.locals (π.inv k)
            funext k
            rw [congrFun hlocals' (π.inv k)]
            exact perm_ite_eq π i _ _ k
        · -- Case 3: no M, no E, some j has S → i gets S
          right; right; left
          refine ⟨not_exists_perm π i (fun j => (s.locals j).1 = .M) hnoM,
                  not_exists_perm π i (fun j => (s.locals j).1 = .E) hnoE,
                  ⟨π.fwd j, fun h => hji (π.fwd_injective h), ?_⟩, ?_, ?_⟩
          · show (s.locals (π.inv (π.fwd j))).1 = .S
            rw [π.inv_fwd]; exact hjS
          · show s'.shared = s.shared; exact hshared'
          · show (fun k => s'.locals (π.inv k)) = fun k =>
                if k = π.fwd i then (CacheState.S, s.shared) else s.locals (π.inv k)
            funext k
            rw [congrFun hlocals' (π.inv k)]
            exact perm_ite_eq π i _ _ k
        · -- Case 4: all others I → i gets E
          right; right; right
          refine ⟨?_, ?_, ?_⟩
          · intro j' hj'i
            show (s.locals (π.inv j')).1 = .I
            apply hallI; intro h; apply hj'i
            have := congrArg π.fwd h; rwa [π.fwd_inv] at this
          · show s'.shared = s.shared; exact hshared'
          · show (fun k => s'.locals (π.inv k)) = fun k =>
                if k = π.fwd i then (CacheState.E, s.shared) else s.locals (π.inv k)
            funext k
            rw [congrFun hlocals' (π.inv k)]
            exact perm_ite_eq π i _ _ k
    | .prWr v =>
      rcases hstep with
        ⟨hpre_I, hbus⟩ | ⟨hpre_S, hshared', hlocals'⟩ |
        ⟨hpre_E, hshared', hlocals'⟩ | ⟨hpre_M, hshared', hlocals'⟩
      · -- From I: BusRdX
        left; refine ⟨?_, ?_⟩
        · show (s.locals (π.inv (π.fwd i))).1 = .I
          rw [inv_fwd_i]; exact hpre_I
        · rcases hbus with ⟨j, hji, hjM, hshared', hlocals'⟩ | ⟨hnoM, hshared', hlocals'⟩
          · left
            refine ⟨π.fwd j, fun h => hji (π.fwd_injective h), ?_, ?_, ?_⟩
            · show (s.locals (π.inv (π.fwd j))).1 = .M
              rw [π.inv_fwd]; exact hjM
            · show s'.shared = (s.locals (π.inv (π.fwd j))).2
              rw [π.inv_fwd]; exact hshared'
            · show (fun k => s'.locals (π.inv k)) = fun k =>
                  if k = π.fwd i then (CacheState.M, v)
                  else (CacheState.I, (s.locals (π.inv k)).2)
              funext k
              rw [congrFun hlocals' (π.inv k)]
              exact perm_ite_eq π i _ _ k
          · right
            refine ⟨not_exists_perm π i (fun j => (s.locals j).1 = .M) hnoM, ?_, ?_⟩
            · show s'.shared = s.shared; exact hshared'
            · show (fun k => s'.locals (π.inv k)) = fun k =>
                  if k = π.fwd i then (CacheState.M, v)
                  else (CacheState.I, (s.locals (π.inv k)).2)
              funext k
              rw [congrFun hlocals' (π.inv k)]
              exact perm_ite_eq π i _ _ k
      · -- From S: BusUpgr
        right; left
        refine ⟨?_, ?_, ?_⟩
        · show (s.locals (π.inv (π.fwd i))).1 = .S
          rw [inv_fwd_i]; exact hpre_S
        · show s'.shared = s.shared; exact hshared'
        · show (fun k => s'.locals (π.inv k)) = fun k =>
              if k = π.fwd i then (CacheState.M, v)
              else (CacheState.I, (s.locals (π.inv k)).2)
          funext k
          rw [congrFun hlocals' (π.inv k)]
          exact perm_ite_eq π i _ _ k
      · -- From E: silent upgrade
        right; right; left
        refine ⟨?_, ?_, ?_⟩
        · show (s.locals (π.inv (π.fwd i))).1 = .E
          rw [inv_fwd_i]; exact hpre_E
        · show s'.shared = s.shared; exact hshared'
        · show (fun k => s'.locals (π.inv k)) = fun k =>
              if k = π.fwd i then (CacheState.M, v) else s.locals (π.inv k)
          funext k
          rw [congrFun hlocals' (π.inv k)]
          exact perm_ite_eq π i _ _ k
      · -- From M: overwrite
        right; right; right
        refine ⟨?_, ?_, ?_⟩
        · show (s.locals (π.inv (π.fwd i))).1 = .M
          rw [inv_fwd_i]; exact hpre_M
        · show s'.shared = s.shared; exact hshared'
        · show (fun k => s'.locals (π.inv k)) = fun k =>
              if k = π.fwd i then (CacheState.M, v) else s.locals (π.inv k)
          funext k
          rw [congrFun hlocals' (π.inv k)]
          exact perm_ite_eq π i _ _ k
    | .evict =>
      rcases hstep with
        ⟨hpre_M, hshared', hlocals'⟩ |
        ⟨hpre_E, hshared', hlocals'⟩ |
        ⟨hpre_S, hshared', hlocals'⟩
      · -- From M: writeback
        left
        refine ⟨?_, ?_, ?_⟩
        · show (s.locals (π.inv (π.fwd i))).1 = .M
          rw [inv_fwd_i]; exact hpre_M
        · show s'.shared = (s.locals (π.inv (π.fwd i))).2
          rw [inv_fwd_i]; exact hshared'
        · show (fun k => s'.locals (π.inv k)) = fun k =>
              if k = π.fwd i then (CacheState.I, (s.locals (π.inv (π.fwd i))).2)
              else s.locals (π.inv k)
          funext k
          rw [congrFun hlocals' (π.inv k), inv_fwd_i]
          exact perm_ite_eq π i _ _ k
      · -- From E: silent evict
        right; left
        refine ⟨?_, ?_, ?_⟩
        · show (s.locals (π.inv (π.fwd i))).1 = .E
          rw [inv_fwd_i]; exact hpre_E
        · show s'.shared = s.shared; exact hshared'
        · show (fun k => s'.locals (π.inv k)) = fun k =>
              if k = π.fwd i then (CacheState.I, (s.locals (π.inv (π.fwd i))).2)
              else s.locals (π.inv k)
          funext k
          rw [congrFun hlocals' (π.inv k), inv_fwd_i]
          exact perm_ite_eq π i _ _ k
      · -- From S: evict
        right; right
        refine ⟨?_, ?_, ?_⟩
        · show (s.locals (π.inv (π.fwd i))).1 = .S
          rw [inv_fwd_i]; exact hpre_S
        · show s'.shared = s.shared; exact hshared'
        · show (fun k => s'.locals (π.inv k)) = fun k =>
              if k = π.fwd i then (CacheState.I, (s.locals (π.inv (π.fwd i))).2)
              else s.locals (π.inv k)
          funext k
          rw [congrFun hlocals' (π.inv k), inv_fwd_i]
          exact perm_ite_eq π i _ _ k

/-! ### SWMR Invariant

    The SWMR (Single-Writer / Multiple-Reader) property says that in any
    reachable state, the cache states satisfy two conditions:

    1. **Single Writer**: if cache `i` is in Modified, then every other
       cache `j` is in Invalid.
    2. **Exclusive is exclusive**: if cache `i` is in Exclusive, then
       every other cache `j` is in Invalid.

    Together, these ensure that at most one cache holds the line in a
    "unique" state (M or E) at any time.
-/

/-- The SWMR predicate on an `(n+1)`-process state: for any two distinct
    processes `i ≠ j`, if `i` is Modified then `j` is Invalid, and
    if `i` is Exclusive then `j` is Invalid. -/
def conc_swmr (n : Nat) (s : SymState Val (CacheState × Val) (n + 1)) : Prop :=
  ∀ i j : Fin (n + 1), i ≠ j →
    ((s.locals i).1 = .M → (s.locals j).1 = .I) ∧
    ((s.locals i).1 = .E → (s.locals j).1 = .I)

/-- SWMR is preserved by every MESI transition (the inductive step).

    The proof proceeds by case analysis on the 10 transition cases.
    For each case, we take arbitrary processes `p ≠ q` and show
    that `(s'.locals p).1 = .M → (s'.locals q).1 = .I` (and similarly
    for E). The argument examines how `p` and `q` relate to the acting
    process `i` (and the snooped process `j` where applicable), using
    `congrFun hlocals' p` to rewrite `s'.locals p` in terms of `s.locals`. -/
private theorem conc_swmr_preserved (n : Nat)
    (s s' : SymState Val (CacheState × Val) (n + 1))
    (hswmr : conc_swmr n s) (hnext : (mesi_sym.toSpec (n + 1)).next s s') :
    conc_swmr n s' := by
  simp only [SymSharedSpec.toSpec, mesi_sym] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  intro p q hpq
  match a with
  | .prRd =>
    obtain ⟨_, hcases⟩ := hstep
    rcases hcases with
      ⟨j, hji, hjM, _, hlocals'⟩ |
      ⟨hnoM, ⟨j, hji, hjE⟩, _, hlocals'⟩ |
      ⟨hnoM3, hnoE3, _, _, hlocals'⟩ |
      ⟨hallI, _, hlocals'⟩
    · -- Case 1: j has M → post: i,j get S, others unchanged. No M/E possible.
      constructor
      · intro hpM
        have slp := congrFun hlocals' p
        by_cases hpi : p = i
        · rw [slp] at hpM; simp [hpi] at hpM
        · by_cases hpj : p = j
          · rw [slp] at hpM; simp [hpj] at hpM
          · rw [slp] at hpM; simp [hpi, hpj] at hpM
            exact absurd hpM (by rw [(hswmr j p (Ne.symm hpj)).1 hjM]; decide)
      · intro hpE
        have slp := congrFun hlocals' p
        by_cases hpi : p = i
        · rw [slp] at hpE; simp [hpi] at hpE
        · by_cases hpj : p = j
          · rw [slp] at hpE; simp [hpj] at hpE
          · rw [slp] at hpE; simp [hpi, hpj] at hpE
            exact absurd hpE (by rw [(hswmr j p (Ne.symm hpj)).1 hjM]; decide)
    · -- Case 2: no M, j has E → post: no M/E possible.
      constructor
      · intro hpM
        have slp := congrFun hlocals' p
        by_cases hpi : p = i
        · rw [slp] at hpM; simp [hpi] at hpM
        · rw [slp] at hpM; simp [hpi] at hpM
          by_cases hp_E : (s.locals p).1 = CacheState.E
          · simp [hp_E] at hpM
          · simp [hp_E] at hpM
            exfalso; exact hnoM ⟨p, (fun h => hpi (h ▸ rfl)), hpM⟩
      · intro hpE
        have slp := congrFun hlocals' p
        by_cases hpi : p = i
        · rw [slp] at hpE; simp [hpi] at hpE
        · rw [slp] at hpE; simp [hpi] at hpE
          by_cases hp_E : (s.locals p).1 = CacheState.E
          · simp [hp_E] at hpE
          · exfalso; simp [hp_E] at hpE
    · -- Case 3: no M, no E → post: no M/E possible.
      constructor
      · intro hpM
        have slp := congrFun hlocals' p
        by_cases hpi : p = i
        · rw [slp] at hpM; simp [hpi] at hpM
        · rw [slp] at hpM; simp [hpi] at hpM
          exfalso; exact hnoM3 ⟨p, (fun h => hpi (h ▸ rfl)), hpM⟩
      · intro hpE
        have slp := congrFun hlocals' p
        by_cases hpi : p = i
        · rw [slp] at hpE; simp [hpi] at hpE
        · rw [slp] at hpE; simp [hpi] at hpE
          exfalso; exact hnoE3 ⟨p, (fun h => hpi (h ▸ rfl)), hpE⟩
    · -- Case 4: all others I. i→E.
      constructor
      · intro hpM
        have slp := congrFun hlocals' p
        by_cases hpi : p = i
        · rw [slp] at hpM; simp [hpi] at hpM
        · rw [slp] at hpM; simp [hpi] at hpM
          exfalso; exact absurd hpM (by rw [hallI p (fun h => hpi (h ▸ rfl))]; decide)
      · intro hpE
        have slp := congrFun hlocals' p
        have slq := congrFun hlocals' q
        by_cases hpi : p = i
        · rw [slp] at hpE; simp [hpi] at hpE
          rw [slq]; by_cases hqi : q = i
          · exfalso; exact hpq (hpi ▸ hqi.symm)
          · simp [hqi]; exact hallI q hqi
        · rw [slp] at hpE; simp [hpi] at hpE
          exfalso; exact absurd hpE (by rw [hallI p (fun h => hpi (h ▸ rfl))]; decide)
  | .prWr v =>
    rcases hstep with
      ⟨_, hbus⟩ | ⟨hpre_S, _, hlocals'⟩ |
      ⟨hpre_E, _, hlocals'⟩ | ⟨hpre_M, _, hlocals'⟩
    · -- From I: BusRdX — i→M, all k≠i → (.I, _)
      rcases hbus with ⟨_, _, _, _, hlocals'⟩ | ⟨_, _, hlocals'⟩
      all_goals (
        have slp := congrFun hlocals' p
        have slq := congrFun hlocals' q
        constructor
        · intro hpM
          by_cases hpi : p = i
          · rw [slq]; by_cases hqi : q = i
            · exfalso; exact hpq (hpi ▸ hqi.symm)
            · simp [hqi]
          · rw [slp] at hpM; simp [hpi] at hpM
        · intro hpE
          by_cases hpi : p = i
          · rw [slp] at hpE; simp [hpi] at hpE
          · rw [slp] at hpE; simp [hpi] at hpE)
    · -- From S: BusUpgr
      have slp := congrFun hlocals' p
      have slq := congrFun hlocals' q
      constructor
      · intro hpM
        by_cases hpi : p = i
        · rw [slq]; by_cases hqi : q = i
          · exfalso; exact hpq (hpi ▸ hqi.symm)
          · simp [hqi]
        · rw [slp] at hpM; simp [hpi] at hpM
      · intro hpE
        by_cases hpi : p = i
        · rw [slp] at hpE; simp [hpi] at hpE
        · rw [slp] at hpE; simp [hpi] at hpE
    · -- From E: i→M, others unchanged
      have slp := congrFun hlocals' p
      have slq := congrFun hlocals' q
      constructor
      · intro hpM
        by_cases hpi : p = i
        · rw [slq]; by_cases hqi : q = i
          · exfalso; exact hpq (hpi ▸ hqi.symm)
          · simp [hqi]; exact (hswmr i q (fun h => hpq (hpi ▸ h))).2 hpre_E
        · rw [slp] at hpM; simp [hpi] at hpM
          rw [slq]; by_cases hqi : q = i
          · exfalso
            have := (hswmr p i (fun h => hpi (h ▸ rfl))).1 hpM
            rw [hpre_E] at this; exact absurd this (by decide)
          · simp [hqi]; exact (hswmr p q hpq).1 hpM
      · intro hpE
        by_cases hpi : p = i
        · rw [slp] at hpE; simp [hpi] at hpE
        · rw [slp] at hpE; simp [hpi] at hpE
          rw [slq]; by_cases hqi : q = i
          · exfalso
            have := (hswmr p i (fun h => hpi (h ▸ rfl))).2 hpE
            rw [hpre_E] at this; exact absurd this (by decide)
          · simp [hqi]; exact (hswmr p q hpq).2 hpE
    · -- From M: i→M, others unchanged
      have slp := congrFun hlocals' p
      have slq := congrFun hlocals' q
      constructor
      · intro hpM
        by_cases hpi : p = i
        · rw [slq]; by_cases hqi : q = i
          · exfalso; exact hpq (hpi ▸ hqi.symm)
          · simp [hqi]; exact (hswmr i q (fun h => hpq (hpi ▸ h))).1 hpre_M
        · rw [slp] at hpM; simp [hpi] at hpM
          rw [slq]; by_cases hqi : q = i
          · exfalso
            have := (hswmr p i (fun h => hpi (h ▸ rfl))).1 hpM
            rw [hpre_M] at this; exact absurd this (by decide)
          · simp [hqi]; exact (hswmr p q hpq).1 hpM
      · intro hpE
        by_cases hpi : p = i
        · rw [slp] at hpE; simp [hpi] at hpE
        · rw [slp] at hpE; simp [hpi] at hpE
          rw [slq]; by_cases hqi : q = i
          · exfalso
            have := (hswmr p i (fun h => hpi (h ▸ rfl))).2 hpE
            rw [hpre_M] at this; exact absurd this (by decide)
          · simp [hqi]; exact (hswmr p q hpq).2 hpE
  | .evict =>
    rcases hstep with
      ⟨_, _, hlocals'⟩ |
      ⟨_, _, hlocals'⟩ |
      ⟨_, _, hlocals'⟩
    all_goals (
      have slp := congrFun hlocals' p
      have slq := congrFun hlocals' q
      constructor
      · intro hpM
        by_cases hpi : p = i
        · rw [slp] at hpM; simp [hpi] at hpM
        · rw [slp] at hpM; simp [hpi] at hpM
          rw [slq]; by_cases hqi : q = i
          · simp [hqi]
          · simp [hqi]; exact (hswmr p q hpq).1 hpM
      · intro hpE
        by_cases hpi : p = i
        · rw [slp] at hpE; simp [hpi] at hpE
        · rw [slp] at hpE; simp [hpi] at hpE
          rw [slq]; by_cases hqi : q = i
          · simp [hqi]
          · simp [hqi]; exact (hswmr p q hpq).2 hpE)

/-! ### Parameterized SWMR Theorem

    The main result: SWMR holds for all `n`. The proof applies Leslie's
    `init_invariant` rule, which takes a base case (initial states satisfy
    SWMR) and an inductive step (SWMR is preserved by every transition),
    and concludes `□ conc_swmr` — SWMR holds at every point in every
    execution satisfying the safety specification.
-/

/-- **Main theorem.** SWMR holds for any number of processors: in every
    reachable state of the `(n+1)`-process MESI system, if cache `i` is
    Modified or Exclusive then every other cache `j ≠ i` is Invalid. -/
theorem mesi_param_swmr : ∀ (n : Nat),
    pred_implies (mesi_sym.toSpec (n + 1)).safety
      [tlafml| □ ⌜ fun s =>
        ∀ i j, i ≠ j →
          ((s.locals i).1 = .M → (s.locals j).1 = .I) ∧
          ((s.locals i).1 = .E → (s.locals j).1 = .I) ⌝] := by
  intro n
  apply init_invariant
  · intro s ⟨_, hlocals⟩ i j _
    have hi := (hlocals i).1
    exact ⟨fun hM => by rw [hi] at hM; exact absurd hM (by decide),
           fun hE => by rw [hi] at hE; exact absurd hE (by decide)⟩
  · intro s s' hnext hinv
    exact conc_swmr_preserved n s s' hinv hnext

end MESIParam
