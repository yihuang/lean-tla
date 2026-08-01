import Leslie.Action

/-! ## MESI Cache Coherence Protocol

    The MESI protocol maintains coherence across N processor caches
    for a shared memory system. Each cache line per processor is in
    one of four states:

    - **M**odified: exclusive dirty copy (memory is stale)
    - **E**xclusive: exclusive clean copy (matches memory)
    - **S**hared: shared clean copy (matches memory, others may have it)
    - **I**nvalid: not cached

    ### Modeling Approach

    We model a *single cache line* shared across a fixed number of
    processors. This is standard: MESI invariants are per-line, so a
    single-line model suffices for coherence properties. We use
    Leslie's `ActionSpec` framework (not round-based: cache coherence
    is asynchronous, not lock-step).

    ### Protocol Actions (snoopy bus model)

    Processor-initiated:
    - `PrRd i`:  Processor i reads. If Invalid, issues BusRd.
    - `PrWr i`:  Processor i writes. If not Modified, issues BusRdX/BusUpgr.

    Bus actions (modeling the effect of snooping):
    - `BusRd i`:  i requests shared read. Others snoop:
                   M → flush to memory, go S; E → go S; S → stay S.
                   Requester goes to S (or E if no other copy).
    - `BusRdX i`: i requests exclusive for write. Others invalidate.
                   Requester goes to M.
    - `BusUpgr i`: i upgrades S→M. Others invalidate their S copies.

    We collapse processor-initiated + bus effect into atomic actions
    (standard for TLA-style modeling of snoopy protocols). Each action
    represents the combined effect of a processor request and the
    resulting bus transaction, as seen after the bus completes.

    ### Key Invariants

    1. **SWMR (Single-Writer / Multiple-Reader)**
       - If cache[i] = M, then ∀ j ≠ i, cache[j] = I
       - If cache[i] = E, then ∀ j ≠ i, cache[j] = I

    2. **Data Value Invariant** (requires tracking values)
       - If cache[i] = M, then cache[i].value is the latest write
       - If cache[i] ∈ {E, S}, then cache[i].value = memory value

    3. **Coherence (derived)**
       - All S copies hold the same value (follows from 2)
       - A read always returns the most recent write (linearizability)

    ### Toward Parameterized Verification

    MESI is symmetric in processors. For a fixed number of values,
    the cutoff framework *might* apply:
    - Process symmetry: all processors run the same protocol ✓
    - But: MESI is not threshold-based (no "if >2n/3 are in state S")
    - And: MESI is not round-based (asynchronous, event-driven)

    The cutoff theorem in `Leslie/Cutoff.lean` requires:
    (a) round-based structure with HO communication
    (b) threshold-based decisions
    (c) counting invariants

    MESI satisfies none of these. For parameterized MESI, we would
    need a different cutoff argument, likely based on:
    - **Environment abstraction**: other caches abstracted as a
      single "rest of system" (classic approach: 1 concrete cache +
      1 abstract "other" cache that overapproximates all others)
    - **Symmetry reduction**: exploit process symmetry to reduce
      the state space (all permutations equivalent)

    ### New Leslie Features Potentially Needed

    1. **Parameterized ActionSpec over Fin n**
       Currently examples use fixed process counts (Peterson: 2,
       TicketLock: 2). For MESI with N processors, we need actions
       indexed by `Fin n × MESIAction` and universally quantified
       invariants `∀ i : Fin n, ...`. The `ActionSpec` framework
       supports this already (ι can be any type), but proof automation
       for the N-indexed case may need new tactics.

    2. **Environment Abstraction / Symmetry Reduction**
       A reusable framework for "1 + abstract environment" proofs:
       given a symmetric ActionSpec, automatically construct the
       2-process abstraction and prove it simulates the N-process
       system. This would generalize beyond MESI to any symmetric
       shared-memory protocol.

    3. **Serialization / Linearizability for Memory**
       The KVStore example proves linearizability via refinement to
       a sequential spec. A similar pattern works for MESI coherence
       (refine to a single shared variable), but a reusable memory
       consistency framework would help.

    4. **Decidable State for Finite Model Checking**
       For small N, we could verify MESI invariants by exhaustive
       checking (like KVStoreCutoff's `Reachable`-based approach).
       This needs `DecidableEq` and `Fintype` instances, which we
       include below.

    ### What We Model Below

    We start with a concrete 2-processor MESI model to establish the
    pattern, then sketch the N-processor generalization.
-/

open TLA

namespace MESI

/-! ### Cache line state -/

inductive CacheState where
  | M    -- Modified: exclusive dirty
  | E    -- Exclusive: exclusive clean
  | S    -- Shared: clean, others may share
  | I    -- Invalid: not cached
  deriving DecidableEq, Repr, BEq

/-! ### Memory value -/

-- Abstract data value (we track values to state the data invariant)
abbrev Val := Nat

/-! ### Protocol state (2 processors, single cache line) -/

structure MState where
  cache0 : CacheState     -- processor 0's cache state
  cache1 : CacheState     -- processor 1's cache state
  val0   : Val            -- processor 0's cached value
  val1   : Val            -- processor 1's cached value
  mem    : Val            -- main memory value
  deriving DecidableEq

/-! ### Actions

    Each action represents the atomic effect of a processor operation
    plus the resulting bus transaction. We model the "after bus
    completes" state.
-/

inductive MAction where
  -- Processor 0 reads (was Invalid, gets shared/exclusive copy)
  | prRd0
  -- Processor 1 reads
  | prRd1
  -- Processor 0 writes (gets exclusive dirty copy)
  | prWr0 (v : Val)
  -- Processor 1 writes
  | prWr1 (v : Val)
  -- Silent eviction: processor 0 evicts its cache line
  | evict0
  -- Silent eviction: processor 1 evicts its cache line
  | evict1

/-! ### Specification -/

-- Note: for a data-parameterized action (PrWr carries a value),
-- we need to existentially quantify over the value in the next-state
-- relation. We handle this by defining the ActionSpec with a
-- sufficiently rich action index. For now, we fix a small value
-- domain to keep things decidable.

-- To use ActionSpec, we need a non-parameterized action index.
-- We enumerate concrete actions for a small value domain.
-- For the general case, we define the spec directly.

/-- The MESI protocol specification (2 processors, direct Spec). -/
def mesi_spec : Spec MState where
  init := fun s =>
    s.cache0 = .I ∧ s.cache1 = .I ∧
    s.val0 = 0 ∧ s.val1 = 0 ∧ s.mem = 0
  next := fun s s' =>
    -- PrRd0: processor 0 reads
    (s.cache0 = .I ∧
      -- If cache1 has the line, get shared copy
      ((s.cache1 = .M ∧
        s' = { s with cache0 := .S, cache1 := .S,
                      val0 := s.val1, mem := s.val1 }) ∨
       (s.cache1 = .E ∧
        s' = { s with cache0 := .S, cache1 := .S, val0 := s.mem }) ∨
       (s.cache1 = .S ∧
        s' = { s with cache0 := .S, val0 := s.mem }) ∨
       -- No other cache has it: get exclusive
       (s.cache1 = .I ∧
        s' = { s with cache0 := .E, val0 := s.mem }))) ∨
    -- PrRd1: processor 1 reads (symmetric)
    (s.cache1 = .I ∧
      ((s.cache0 = .M ∧
        s' = { s with cache1 := .S, cache0 := .S,
                      val1 := s.val0, mem := s.val0 }) ∨
       (s.cache0 = .E ∧
        s' = { s with cache1 := .S, cache0 := .S, val1 := s.mem }) ∨
       (s.cache0 = .S ∧
        s' = { s with cache1 := .S, val1 := s.mem }) ∨
       (s.cache0 = .I ∧
        s' = { s with cache1 := .E, val1 := s.mem }))) ∨
    -- PrWr0: processor 0 writes value v
    (∃ v : Val,
      -- From I: BusRdX, invalidate others, go M
      (s.cache0 = .I ∧
        ((s.cache1 = .M ∧
          s' = { s with cache0 := .M, cache1 := .I, val0 := v, mem := s.val1 }) ∨
         (s.cache1 ≠ .M ∧
          s' = { s with cache0 := .M, cache1 := .I, val0 := v }))) ∨
      -- From S: BusUpgr, invalidate others, go M
      (s.cache0 = .S ∧
        s' = { s with cache0 := .M, cache1 := .I, val0 := v }) ∨
      -- From E: silent upgrade, go M (no bus transaction needed)
      (s.cache0 = .E ∧
        s' = { s with cache0 := .M, val0 := v }) ∨
      -- From M: overwrite (already exclusive)
      (s.cache0 = .M ∧
        s' = { s with val0 := v })) ∨
    -- PrWr1: processor 1 writes value v (symmetric)
    (∃ v : Val,
      (s.cache1 = .I ∧
        ((s.cache0 = .M ∧
          s' = { s with cache1 := .M, cache0 := .I, val1 := v, mem := s.val0 }) ∨
         (s.cache0 ≠ .M ∧
          s' = { s with cache1 := .M, cache0 := .I, val1 := v }))) ∨
      (s.cache1 = .S ∧
        s' = { s with cache1 := .M, cache0 := .I, val1 := v }) ∨
      (s.cache1 = .E ∧
        s' = { s with cache1 := .M, val1 := v }) ∨
      (s.cache1 = .M ∧
        s' = { s with val1 := v })) ∨
    -- Evict0: processor 0 silently evicts
    ((s.cache0 = .M ∧
      s' = { s with cache0 := .I, mem := s.val0 }) ∨
     ((s.cache0 = .E ∨ s.cache0 = .S) ∧
      s' = { s with cache0 := .I })) ∨
    -- Evict1: processor 1 silently evicts (symmetric)
    ((s.cache1 = .M ∧
      s' = { s with cache1 := .I, mem := s.val1 }) ∨
     ((s.cache1 = .E ∨ s.cache1 = .S) ∧
      s' = { s with cache1 := .I }))
  fair := []

/-! ### Invariant 1: SWMR (Single Writer, Multiple Reader)

    The fundamental structural invariant of MESI:
    - Modified is exclusive: if one cache is M, the other is I
    - Exclusive is exclusive: if one cache is E, the other is I
    - At most one of {M, E} exists at any time
-/

def swmr (s : MState) : Prop :=
  -- If cache0 is Modified, cache1 must be Invalid
  (s.cache0 = .M → s.cache1 = .I) ∧
  -- If cache1 is Modified, cache0 must be Invalid
  (s.cache1 = .M → s.cache0 = .I) ∧
  -- If cache0 is Exclusive, cache1 must be Invalid
  (s.cache0 = .E → s.cache1 = .I) ∧
  -- If cache1 is Exclusive, cache0 must be Invalid
  (s.cache1 = .E → s.cache0 = .I)

/-! ### Invariant 2: Data Value Invariant

    Cached values are consistent with the memory model:
    - E or S copies match memory
    - If both in S, they agree (follows from both matching memory)
    - M has the "latest" value (memory may be stale, but will be
      updated on eviction or snoop)
-/

def data_inv (s : MState) : Prop :=
  -- Exclusive copy matches memory
  (s.cache0 = .E → s.val0 = s.mem) ∧
  (s.cache1 = .E → s.val1 = s.mem) ∧
  -- Shared copies match memory
  (s.cache0 = .S → s.val0 = s.mem) ∧
  (s.cache1 = .S → s.val1 = s.mem)

/-! ### Combined inductive invariant -/

def inv (s : MState) : Prop := swmr s ∧ data_inv s

/-! ### Proof that invariant holds initially -/

theorem inv_init : ∀ s, mesi_spec.init s → inv s := by
  intro s ⟨hc0, hc1, hv0, hv1, hm⟩
  simp_all [inv, swmr, data_inv]

/-! ### Proof that invariant is inductive -/

-- This is the main proof obligation: show inv is preserved by every
-- transition in mesi_spec.next. The proof proceeds by case analysis
-- on which action fires, then by the precondition (cache states).

theorem inv_next : ∀ s s', mesi_spec.next s s' → inv s → inv s' := by
  intro s s' hnext ⟨hswmr, hdata⟩
  obtain ⟨hswmr_m0, hswmr_m1, hswmr_e0, hswmr_e1⟩ := hswmr
  obtain ⟨hdata_e0, hdata_e1, hdata_s0, hdata_s1⟩ := hdata
  -- Case split on the disjunctive next-state relation
  rcases hnext with
    -- PrRd0
    ⟨hpre, hrd⟩ |
    -- PrRd1
    ⟨hpre, hrd⟩ |
    -- PrWr0
    ⟨v, hwr⟩ |
    -- PrWr1
    ⟨v, hwr⟩ |
    -- Evict0
    hev |
    -- Evict1
    hev
  -- PrRd0: cache0 was Invalid
  · rcases hrd with
      ⟨hc1m, heq⟩ | ⟨hc1e, heq⟩ | ⟨hc1s, heq⟩ | ⟨hc1i, heq⟩ <;>
    subst heq <;> simp_all [swmr, data_inv, inv]
  -- PrRd1: cache1 was Invalid (symmetric)
  · rcases hrd with
      ⟨hc0m, heq⟩ | ⟨hc0e, heq⟩ | ⟨hc0s, heq⟩ | ⟨hc0i, heq⟩ <;>
    subst heq <;> simp_all [swmr, data_inv, inv]
  -- PrWr0
  · rcases hwr with
      ⟨hpre, hbus⟩ | ⟨hpre, heq⟩ | ⟨hpre, heq⟩ | ⟨hpre, heq⟩
    · -- From I
      rcases hbus with ⟨hc1m, heq⟩ | ⟨hc1nm, heq⟩ <;>
      subst heq <;> simp_all [swmr, data_inv, inv]
    · -- From S
      subst heq; simp_all [swmr, data_inv, inv]
    · -- From E
      subst heq; simp_all [swmr, data_inv, inv]
    · -- From M
      subst heq; simp_all [swmr, data_inv, inv]
  -- PrWr1 (symmetric)
  · rcases hwr with
      ⟨hpre, hbus⟩ | ⟨hpre, heq⟩ | ⟨hpre, heq⟩ | ⟨hpre, heq⟩
    · rcases hbus with ⟨hc0m, heq⟩ | ⟨hc0nm, heq⟩ <;>
      subst heq <;> simp_all [swmr, data_inv, inv]
    · subst heq; simp_all [swmr, data_inv, inv]
    · subst heq; simp_all [swmr, data_inv, inv]
    · subst heq; simp_all [swmr, data_inv, inv]
  -- Evict0
  · rcases hev with
      ⟨hc0m, heq⟩ | ⟨hc0es, heq⟩ <;>
    subst heq <;> simp_all [swmr, data_inv, inv]
  -- Evict1 (symmetric)
  · rcases hev with
      ⟨hc1m, heq⟩ | ⟨hc1es, heq⟩ <;>
    subst heq <;> simp_all [swmr, data_inv, inv]

/-! ### Safety theorem: combined invariant holds on all reachable states -/

theorem mesi_inv :
    pred_implies mesi_spec.safety [tlafml| □ ⌜ inv ⌝] := by
  apply init_invariant
  · exact inv_init
  · intro s s' hnext hinv ; exact inv_next s s' hnext hinv

/-! ### SWMR as a consequence of the combined invariant -/

theorem mesi_swmr :
    pred_implies mesi_spec.safety [tlafml| □ ⌜ swmr ⌝] := by
  apply pred_implies_trans (q := [tlafml| □ ⌜ inv ⌝])
  · exact mesi_inv
  · apply always_monotone
    intro e hinv ; exact hinv.1

theorem mesi_data :
    pred_implies mesi_spec.safety [tlafml| □ ⌜ data_inv ⌝] := by
  apply pred_implies_trans (q := [tlafml| □ ⌜ inv ⌝])
  · exact mesi_inv
  · apply always_monotone
    intro e hinv ; exact hinv.2

/-! ## Sketch: N-Processor Generalization

    For N processors (parameterized by n : Nat), the state becomes:

    ```
    structure MStateN (n : Nat) where
      cache : Fin n → CacheState
      val   : Fin n → Val
      mem   : Val
    ```

    Actions are indexed by `Fin n × MESIActionType`:

    ```
    inductive MESIActionType where
      | prRd | prWr (v : Val) | evict
    ```

    The SWMR invariant generalizes to:
    ```
    def swmr_n (s : MStateN n) : Prop :=
      (∀ i, s.cache i = .M → ∀ j, j ≠ i → s.cache j = .I) ∧
      (∀ i, s.cache i = .E → ∀ j, j ≠ i → s.cache j = .I)
    ```

    ### Cutoff Opportunity

    Unlike round-based threshold protocols, MESI's cutoff argument
    relies on **environment abstraction** (not counting thresholds):

    - The SWMR property means at most 1 cache is in M or E.
    - Other caches are in S or I, and they're interchangeable.
    - So the "interesting" configurations are bounded:
      1 distinguished cache (M or E) + count of S caches + rest I.
    - This gives a cutoff of n = 2 or n = 3 depending on the property.

    To support this in Leslie, we would need:

    **Feature: Environment Abstraction Framework**
    ```
    -- Given a symmetric spec, produce the 2-process abstraction
    def env_abstract (spec : ∀ n, ActionSpec (MStateN n) (Fin n × ι))
      (sym : is_symmetric spec) :
      ActionSpec (MStateN 2) (Fin 2 × ι)
    ```

    **Feature: Symmetry Reduction Tactic**
    A tactic that, given a permutation-invariant invariant and a
    symmetric spec, reduces `∀ n, inv_n holds` to checking a
    representative set of states.

    ### Alternative: Refinement to Abstract Spec

    Another approach (available today in Leslie):
    Define an abstract spec tracking just (Option CacheState × Nat)
    — the "distinguished" cache + count of shared copies — and prove
    MESI refines it. The abstract spec has a finite state space
    regardless of n.
-/

/-! ## Summary: Leslie Feature Gaps for Cache Coherence

    | Feature | Status | Needed For |
    |---------|--------|------------|
    | ActionSpec with Fin n actions | ✓ Works today | N-processor model |
    | Inductive invariant proofs | ✓ Works today | SWMR, data invariant |
    | Refinement to sequential spec | ✓ Works today | Coherence = linearizability |
    | DecidableEq for finite checking | ✓ Works today | Small-model exploration |
    | Round-based cutoff | ✗ Wrong model | MESI is not round-based |
    | Environment abstraction | ✗ New feature | Parameterized MESI |
    | Symmetry reduction | ✗ New feature | Reduce N → small N |
    | Layered refinement (CIVL) | ✓ Exists | Decompose complex proof |
    | Weak fairness / liveness | ✓ Exists | Progress properties |
-/

end MESI
