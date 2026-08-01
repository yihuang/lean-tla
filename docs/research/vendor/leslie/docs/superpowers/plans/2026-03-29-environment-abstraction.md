# Environment Abstraction Framework for Parameterized Cache Coherence

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build a reusable environment abstraction framework in Leslie that reduces parameterized symmetric shared-memory protocols (N processes) to small finite instances (typically 2-3 processes), enabling fully mechanized proofs of cache coherence protocols like MESI for arbitrary N.

**Architecture:** The framework has three layers:
1. **SymSharedSpec** — a structure for defining symmetric shared-memory protocols parameterized by process count. The step relation takes global state (`Shared × (Fin n → Local)`) and produces global state, with the acting process identified by index. Symmetry is expressed as permutation-equivariance of the entire `Spec`.
2. **Environment Abstraction** — given a symmetric spec and an abstraction function from N-1 local states to a summary, construct a 2-process abstract `Spec` (1 focus + 1 abstract environment) and prove soundness via `refinement_mapping_stutter_with_invariant` from `Refinement.lean`.
3. **Assume-Guarantee Composition** — a circular AG rule for symmetric systems with explicit non-interference conditions.

The key insight for cache coherence: SWMR means at most 1 process is in M or E, so the "environment" state can be abstracted as a summary (e.g., whether any other cache is M/E/S). The abstraction function maps `(Fin (n-1) → Local)` to `EnvState`, proven sound via refinement mapping.

**Tech Stack:** Lean 4 / Mathlib-lite, Leslie TLA framework (`Spec`, `refinement_mapping_stutter_with_invariant`, `init_invariant`, `refines_via`, `pred_implies`)

---

## File Structure

| File | Responsibility |
|------|---------------|
| `Leslie/SymShared.lean` | `SymSharedSpec` structure, `SymState`, `toSpec`, permutation invariance |
| `Leslie/EnvAbstraction.lean` | `EnvAbstraction` structure, `AbsState`, abstract spec, refinement mapping soundness |
| `Leslie/AssumeGuarantee.lean` | Circular AG rule for symmetric systems with non-interference |
| `Leslie/Examples/CacheCoherence/MESIParam.lean` | N-process MESI, environment abstraction, parameterized SWMR proof |
| Tests are proofs — each file contains theorems that Lean checks |

### Design Rationale

**Why not extend `Cutoff.lean`?** The cutoff framework requires round-based structure + threshold decisions. Cache coherence is asynchronous and makes binary (exclusive/shared) decisions, not threshold-based. Environment abstraction is the right tool.

**Why `SymSharedSpec` instead of raw `ActionSpec`?** Symmetry is a structural property that the abstraction construction and AG composition rule rely on. Encoding it in the type prevents misuse and enables the "by symmetry, extend from process 0 to all processes" argument. The step signature is kept simple (operates on full global state) to avoid redundant arguments and ease the symmetry proof.

**Why assume-guarantee?** For protocols where the environment abstraction alone is too coarse. For MESI, direct environment abstraction likely suffices, but AG makes the framework general enough for MOESI, directory-based protocols, etc.

**Key review-driven decisions:**
- Use `refinement_mapping_stutter_with_invariant` (not `SimulationRel`) since the abstraction mapping is a function, not a relation (reviewer issue C4)
- Step signature operates on `(Shared, Fin n → Local)` pairs with no redundant actor argument (reviewer issue C1)
- Abstract spec defines its own transitions via `focus_step` / `env_step` / `env_snoop`, not by calling `spec.step 2` (reviewer issue C3)
- `mkLocals` helper explicitly constructs N+1 locals from focus + N others (reviewer issue C2)
- Each task fills in at least one representative proof case to validate types (reviewer issue I5)
- The `EnvCacheSummary.hasM` variant does not store a value, avoiding `Classical.choose` issues (reviewer issue I4)

---

### Task 1: SymSharedSpec — Symmetric Shared-Memory Specifications

**Files:**
- Create: `Leslie/SymShared.lean`

- [ ] **Step 1: Define the SymSharedSpec structure**

```lean
import Leslie.Action

open TLA

/-! ## Symmetric Shared-Memory Specifications

    A symmetric shared-memory protocol where N identical processes
    interact through a shared state. Each process has identical local
    state type and identical actions. The global state is:
    - shared component (e.g., main memory, bus state)
    - per-process local state (Fin n → LocalState)

    Symmetry means: permuting process indices preserves the spec.
-/

/-- Global state for n processes. -/
structure SymState (Shared Local : Type) (n : Nat) where
  shared : Shared
  locals : Fin n → Local

/-- Permute a SymState by reindexing locals. -/
def SymState.perm {Shared Local : Type} {n : Nat}
    (π : Fin n ≃ Fin n) (s : SymState Shared Local n) :
    SymState Shared Local n where
  shared := s.shared
  locals := s.locals ∘ π.symm

/-- A symmetric shared-memory protocol parameterized by process count.
    The step relation operates on full global state: the acting process
    is identified by index, but pre/post state includes all locals. -/
structure SymSharedSpec where
  Shared : Type
  Local : Type
  ActType : Type
  init_shared : Shared → Prop
  init_local : Local → Prop
  /-- Transition: process i performs action a, transforming global state.
      The step may update any process's local state (e.g., snooping). -/
  step : (n : Nat) → Fin n → ActType →
         SymState Shared Local n → SymState Shared Local n → Prop
```

- [ ] **Step 2: Define toSpec and permutation invariance**

```lean
/-- Instantiate to a concrete Spec for n processes. -/
def SymSharedSpec.toSpec (spec : SymSharedSpec) (n : Nat) :
    Spec (SymState spec.Shared spec.Local n) where
  init := fun s => spec.init_shared s.shared ∧ ∀ i, spec.init_local (s.locals i)
  next := fun s s' => ∃ (i : Fin n) (a : spec.ActType), spec.step n i a s s'
  fair := []

/-- A SymSharedSpec is symmetric if its Spec is invariant under
    process permutation. This is weaker and easier to work with
    than step-level equivariance. -/
structure SymSharedSpec.IsSymmetric (spec : SymSharedSpec) : Prop where
  /-- Permuting init states preserves init. -/
  init_perm : ∀ (n : Nat) (π : Fin n ≃ Fin n) (s : SymState spec.Shared spec.Local n),
    (spec.toSpec n).init s → (spec.toSpec n).init (s.perm π)
  /-- Permuting step preserves step. -/
  step_perm : ∀ (n : Nat) (π : Fin n ≃ Fin n)
    (s s' : SymState spec.Shared spec.Local n),
    (spec.toSpec n).next s s' → (spec.toSpec n).next (s.perm π) (s'.perm π)

/-- Key lemma: symmetric spec + safety for process 0 → safety for all.
    If pred P holds for s.locals 0 in all reachable states, then by
    symmetry (swap 0 and i), P holds for s.locals i too. -/
theorem SymSharedSpec.toSpec_perm_invariant (spec : SymSharedSpec)
    (hsym : spec.IsSymmetric) (n : Nat) (π : Fin n ≃ Fin n) :
    refines_via (SymState.perm π) (spec.toSpec n).safety (spec.toSpec n).safety := by
  apply refinement_mapping_nostutter
  · intro s hinit; exact hsym.init_perm n π s hinit
  · intro s s' hnext; exact hsym.step_perm n π s s' hnext
```

- [ ] **Step 3: Define symmetric predicates and the forall-from-one lemma**

```lean
/-- Helper: swap permutation (transposes indices 0 and i). -/
def Fin.swap (n : Nat) (i : Fin n) : Fin n ≃ Fin n :=
  Equiv.swap 0 i

/-- If a per-process property holds for process 0 in all reachable states
    of a symmetric spec, it holds for all processes. -/
theorem SymSharedSpec.forall_from_focus (spec : SymSharedSpec)
    (hsym : spec.IsSymmetric) (n : Nat)
    (P : spec.Shared → spec.Local → Prop)
    (h0 : pred_implies (spec.toSpec n).safety
      [tlafml| □ ⌜ fun s => P s.shared (s.locals 0) ⌝]) :
    pred_implies (spec.toSpec n).safety
      [tlafml| □ ⌜ fun s => ∀ i, P s.shared (s.locals i) ⌝] := by
  sorry -- uses toSpec_perm_invariant with Fin.swap n i
```

- [ ] **Step 4: Verify compilation and test with a trivial symmetric spec**

Run: `lake env lean Leslie/SymShared.lean`
Expected: Compiles (sorry only in `forall_from_focus`)

- [ ] **Step 5: Commit**

```bash
git add Leslie/SymShared.lean
git commit -m "feat: SymSharedSpec for symmetric shared-memory protocols"
```

---

### Task 2: Environment Abstraction — The 2-Process Abstract System

**Files:**
- Create: `Leslie/EnvAbstraction.lean`
- Depends on: `Leslie/SymShared.lean`

- [ ] **Step 1: Define the mkLocals helper and EnvAbstraction structure**

```lean
import Leslie.SymShared

open TLA

/-! ## Environment Abstraction for Symmetric Protocols

    Given a SymSharedSpec and an abstraction of N-1 local states into
    a single "environment summary" state, construct a 2-process
    abstract system and prove it simulates the N-process system.

    Soundness: the abstraction function is a refinement mapping,
    so any invariant of the abstract system lifts to the concrete.
-/

/-- Construct an (n+1)-process locals map from a focus local and n others. -/
def mkLocals {L : Type} (focus : L) (others : Fin n → L) : Fin (n + 1) → L
  | ⟨0, _⟩ => focus
  | ⟨i + 1, h⟩ => others ⟨i, Nat.lt_of_succ_lt_succ h⟩

/-- Extract the non-focus locals from an (n+1)-process locals map. -/
def otherLocals {L : Type} (locals : Fin (n + 1) → L) : Fin n → L :=
  fun i => locals i.succ

/-- The abstract 2-process state: focus process + environment summary. -/
structure AbsState (Shared EnvState Local : Type) where
  shared : Shared
  focus : Local
  env : EnvState

/-- An environment abstraction packages:
    - An environment summary type
    - An abstraction function from N others' locals to env summary
    - Separate transition relations for the abstract system
    - Soundness conditions relating abstract to concrete -/
structure EnvAbstraction (spec : SymSharedSpec) where
  EnvState : Type
  /-- Abstract initial environment. -/
  env_init : EnvState → Prop
  /-- Abstraction: map n local states to environment summary. -/
  abs_env : (n : Nat) → (Fin n → spec.Local) → EnvState
  /-- Focus process step (focus acts, env reacts via snoop).
      Defined on abstract state directly. -/
  focus_step : spec.ActType →
    AbsState spec.Shared EnvState spec.Local →
    AbsState spec.Shared EnvState spec.Local → Prop
  /-- Environment step (some env process acts, may affect focus via snoop). -/
  env_step : spec.ActType →
    AbsState spec.Shared EnvState spec.Local →
    AbsState spec.Shared EnvState spec.Local → Prop
  /-- Soundness of init. -/
  init_sound : ∀ (n : Nat) (locals : Fin n → spec.Local),
    (∀ i, spec.init_local (locals i)) → env_init (abs_env n locals)
  /-- Soundness of focus_step: when process 0 acts in the concrete system,
      the abstract focus_step captures the effect on (focus, env). -/
  focus_step_sound : ∀ (n : Nat) (a : spec.ActType)
    (s s' : SymState spec.Shared spec.Local (n + 1)),
    spec.step (n + 1) 0 a s s' →
    focus_step a
      ⟨s.shared, s.locals 0, abs_env n (otherLocals s.locals)⟩
      ⟨s'.shared, s'.locals 0, abs_env n (otherLocals s'.locals)⟩
  /-- Soundness of env_step: when process i > 0 acts in the concrete system,
      some abstract env_step captures the effect. -/
  env_step_sound : ∀ (n : Nat) (i : Fin n) (a : spec.ActType)
    (s s' : SymState spec.Shared spec.Local (n + 1)),
    spec.step (n + 1) i.succ a s s' →
    env_step a
      ⟨s.shared, s.locals 0, abs_env n (otherLocals s.locals)⟩
      ⟨s'.shared, s'.locals 0, abs_env n (otherLocals s'.locals)⟩
```

- [ ] **Step 2: Define the abstract Spec and the refinement mapping**

```lean
/-- The abstract 2-process Spec. -/
def EnvAbstraction.toAbsSpec (spec : SymSharedSpec) (ea : EnvAbstraction spec) :
    Spec (AbsState spec.Shared ea.EnvState spec.Local) where
  init := fun s =>
    spec.init_shared s.shared ∧
    spec.init_local s.focus ∧
    ea.env_init s.env
  next := fun s s' =>
    (∃ a, ea.focus_step a s s') ∨
    (∃ a, ea.env_step a s s')
  fair := []

/-- The refinement mapping: N+1 process state → abstract state. -/
def EnvAbstraction.abs_map (spec : SymSharedSpec) (ea : EnvAbstraction spec)
    (n : Nat) (s : SymState spec.Shared spec.Local (n + 1)) :
    AbsState spec.Shared ea.EnvState spec.Local where
  shared := s.shared
  focus := s.locals 0
  env := ea.abs_env n (otherLocals s.locals)
```

- [ ] **Step 3: Prove the refinement mapping theorem (soundness)**

```lean
/-- The abstraction is a sound refinement mapping:
    concrete N+1 process spec refines abstract 2-process spec (with stutter). -/
theorem EnvAbstraction.refinement (spec : SymSharedSpec) (ea : EnvAbstraction spec)
    (n : Nat) :
    refines_via (ea.abs_map spec n)
      (spec.toSpec (n + 1)).safety
      (ea.toAbsSpec spec).safety_stutter := by
  apply refinement_mapping_stutter
  · -- init preserved
    intro s ⟨hsh, hlocs⟩
    exact ⟨hsh, hlocs 0, ea.init_sound n _ (fun i => hlocs i.succ)⟩
  · -- next preserved (or stutter)
    intro s s' ⟨i, a, hstep⟩
    cases i using Fin.cases with
    | zero => -- process 0 acted → focus_step
      left; left; exact ⟨a, ea.focus_step_sound n a s s' hstep⟩
    | succ j => -- process j+1 acted → env_step
      left; right; exact ⟨a, ea.env_step_sound n j a s s' hstep⟩
```

- [ ] **Step 4: Prove invariant lifting (abstract invariant → concrete per-process property)**

```lean
/-- Lift an abstract invariant to the concrete system (for process 0). -/
theorem EnvAbstraction.lift_to_focus (spec : SymSharedSpec) (ea : EnvAbstraction spec)
    (n : Nat)
    (inv : AbsState spec.Shared ea.EnvState spec.Local → Prop)
    (hinv : pred_implies (ea.toAbsSpec spec).safety_stutter [tlafml| □ ⌜ inv ⌝])
    (P : spec.Shared → spec.Local → Prop)
    (hP : ∀ s, inv s → P s.shared s.focus) :
    pred_implies (spec.toSpec (n + 1)).safety
      [tlafml| □ ⌜ fun s => P s.shared (s.locals 0) ⌝] := by
  apply refines_preserves_invariant_stutter (ea.abs_map spec n)
  · exact ea.refinement spec n
  · apply pred_implies_trans hinv
    apply always_monotone; intro e hinv; exact hP _ hinv

/-- Lift to all processes (requires symmetry). -/
theorem EnvAbstraction.lift_to_all (spec : SymSharedSpec) (ea : EnvAbstraction spec)
    (hsym : spec.IsSymmetric) (n : Nat)
    (inv : AbsState spec.Shared ea.EnvState spec.Local → Prop)
    (hinv : pred_implies (ea.toAbsSpec spec).safety_stutter [tlafml| □ ⌜ inv ⌝])
    (P : spec.Shared → spec.Local → Prop)
    (hP : ∀ s, inv s → P s.shared s.focus) :
    pred_implies (spec.toSpec (n + 1)).safety
      [tlafml| □ ⌜ fun s => ∀ i, P s.shared (s.locals i) ⌝] := by
  apply spec.forall_from_focus hsym
  exact ea.lift_to_focus spec n inv hinv P hP
```

- [ ] **Step 5: Verify compilation and test the refinement proof structure**

Run: `lake env lean Leslie/EnvAbstraction.lean`
Expected: Compiles (sorry only in inherited `forall_from_focus`)

- [ ] **Step 6: Commit**

```bash
git add Leslie/EnvAbstraction.lean
git commit -m "feat: environment abstraction with refinement mapping soundness"
```

---

### Task 3: Assume-Guarantee Rule for Symmetric Systems

**Files:**
- Create: `Leslie/AssumeGuarantee.lean`
- Depends on: `Leslie/SymShared.lean`, `Leslie/EnvAbstraction.lean`

- [ ] **Step 1: Define the AG proof obligation structure with non-interference**

```lean
import Leslie.EnvAbstraction

open TLA

/-! ## Assume-Guarantee Reasoning for Symmetric Systems

    Circular AG rule: prove G for one process assuming all others satisfy G,
    then conclude G for all processes by symmetry.

    Critical addition (from review): explicit non-interference condition —
    when another process acts, the focus process's guarantee is preserved.
-/

/-- An assume-guarantee proof for a symmetric protocol.
    The assumption IS the guarantee (Owicki-Gries style for symmetric systems). -/
structure SymAG (spec : SymSharedSpec) (ea : EnvAbstraction spec) where
  /-- The guarantee / invariant property per process. -/
  guarantee : spec.Shared → spec.Local → Prop
  /-- AG obligation (focus acts): assuming all others satisfy G
      and focus satisfies G, after focus acts, focus still satisfies G. -/
  focus_preserves :
    ∀ (s s' : AbsState spec.Shared ea.EnvState spec.Local),
    guarantee s.shared s.focus →
    (∃ a, ea.focus_step a s s') →
    guarantee s'.shared s'.focus
  /-- Non-interference (env acts): when another process acts,
      the focus process's guarantee is preserved. -/
  env_preserves :
    ∀ (s s' : AbsState spec.Shared ea.EnvState spec.Local),
    guarantee s.shared s.focus →
    (∃ a, ea.env_step a s s') →
    guarantee s'.shared s'.focus
  /-- Initial guarantee. -/
  init_guarantee :
    �� sh l, spec.init_shared sh → spec.init_local l → guarantee sh l
```

- [ ] **Step 2: Prove the AG composition theorem**

```lean
/-- The symmetric AG rule: guarantee holds for the focus process. -/
theorem SymAG.focus_inv (ag : SymAG spec ea) :
    pred_implies (ea.toAbsSpec spec).safety_stutter
      [tlafml| □ ⌜ fun s => ag.guarantee s.shared s.focus ⌝] := by
  apply init_invariant
  · -- init
    intro s ⟨hsh, hfoc, _���
    exact ag.init_guarantee s.shared s.focus hsh hfoc
  · -- next (or stutter)
    intro s s' hnext hG
    rcases hnext with ⟨a, hfoc⟩ | ⟨a, henv⟩ | heq
    · exact ag.focus_preserves s s' hG ⟨a, hfoc⟩
    · exact ag.env_preserves s s' hG ⟨a, henv⟩
    · subst heq; exact hG

/-- Lift to all processes in the N-process system. -/
theorem SymAG.compose (ag : SymAG spec ea) (hsym : spec.IsSymmetric) :
    ∀ (n : Nat),
    pred_implies (spec.toSpec (n + 1)).safety
      [tlafml| □ ⌜ fun s => ∀ i, ag.guarantee s.shared (s.locals i) ⌝] := by
  intro n
  apply ea.lift_to_all spec hsym n
    (fun s => ag.guarantee s.shared s.focus)
  · -- abstract invariant
    sorry -- from focus_inv, adapted for safety_stutter
  · -- extraction
    intro s hG; exact hG
```

- [ ] **Step 3: Verify compilation**

Run: `lake env lean Leslie/AssumeGuarantee.lean`
Expected: Compiles with targeted sorry

- [ ] **Step 4: Commit**

```bash
git add Leslie/AssumeGuarantee.lean
git commit -m "feat: assume-guarantee rule for symmetric protocols"
```

---

### Task 4: Parameterized MESI — Applying the Framework

**Files:**
- Create: `Leslie/Examples/CacheCoherence/MESIParam.lean`
- Depends on: `Leslie/AssumeGuarantee.lean`, existing `MESI.lean`

- [ ] **Step 1: Define MESI as a SymSharedSpec**

```lean
import Leslie.AssumeGuarantee
import Leslie.Examples.CacheCoherence.MESI

open TLA MESI

namespace MESIParam

/-- MESI action types (process-independent). -/
inductive MESIAct where
  | prRd | prWr (v : Val) | evict

/-- MESI as a symmetric shared-memory spec.
    Shared = Val (main memory). Local = CacheState × Val. -/
def mesi_sym : SymSharedSpec where
  Shared := Val
  Local := CacheState × Val
  ActType := MESIAct
  init_shared := fun mem => mem = 0
  init_local := fun ⟨cs, v⟩ => cs = .I ∧ v = 0
  step := fun n i a s s' =>
    s'.shared = s.shared ∧ -- default; overridden per case
    sorry -- full transition relation (see Step 1 body)
```

The full step relation follows the MESI protocol (PrRd, PrWr, Evict) as in
`MESI.lean` but parameterized over `Fin n`. Each action updates the actor's
local, the shared memory, and potentially snoops other caches. The concrete
definition will be filled in during implementation.

- [ ] **Step 2: Prove MESI is symmetric**

```lean
/-- MESI is symmetric: all processors run identical code. -/
theorem mesi_symmetric : mesi_sym.IsSymmetric where
  init_perm := by sorry -- init_local is the same for all; permutation preserves ∀
  step_perm := by sorry -- step treats all indices uniformly
```

- [ ] **Step 3: Define the environment abstraction for MESI**

```lean
/-- Environment summary for MESI.
    hasM = some env cache is Modified (value recoverable from shared on flush)
    hasE = some env cache is Exclusive
    someS = at least one env cache is Shared
    allI = all env caches are Invalid -/
inductive EnvCacheSummary where
  | hasM | hasE | someS | allI
  deriving DecidableEq

/-- The MESI environment abstraction. -/
def mesi_env : EnvAbstraction mesi_sym where
  EnvState := EnvCacheSummary
  env_init := fun e => e = .allI
  abs_env := fun n locals =>
    if ∃ i, (locals i).1 = .M then .hasM
    else if ∃ i, (locals i).1 = .E then .hasE
    else if ∃ i, (locals i).1 = .S then .someS
    else .allI
  focus_step := fun a s s' =>
    sorry -- abstract focus transition + env snoop
  env_step := fun a s s' =>
    sorry -- abstract env transition
  init_sound := by
    intro n locals hinit
    simp [abs_env]
    -- all locals are I initially
    sorry
  focus_step_sound := by sorry
  env_step_sound := by sorry
```

- [ ] **Step 4: Prove SWMR on the abstract system and lift**

```lean
/-- SWMR on the abstract state. -/
def abs_swmr (s : AbsState Val EnvCacheSummary (CacheState × Val)) : Prop :=
  (s.focus.1 = .M → s.env = .allI) ∧
  (s.focus.1 = .E → s.env = .allI) ∧
  (s.env = .hasM → s.focus.1 = .I) ∧
  (s.env = .hasE → s.focus.1 = .I)

/-- SWMR for all N. -/
theorem mesi_param_swmr : ∀ (n : Nat),
    pred_implies (mesi_sym.toSpec (n + 1)).safety
      [tlafml| □ ⌜ fun s =>
        ∀ i j, i ≠ j →
          ((s.locals i).1 = .M → (s.locals j).1 = .I) ∧
          ((s.locals i).1 = .E → (s.locals j).1 = .I) ⌝] := by
  sorry -- via lift_to_all + abs_swmr
```

- [ ] **Step 5: Validate N=2 equivalence with existing MESI.lean**

```lean
/-- Sanity check: the parameterized MESI for n=2 captures
    the same behaviors as the handwritten mesi_spec in MESI.lean. -/
theorem mesi_param_two_equiv :
    ∀ s s', (mesi_sym.toSpec 2).next s s' ↔
    ∃ (ms ms' : MState),
      s.shared = ms.mem ∧ s'.shared = ms'.mem ∧
      mesi_spec.next ms ms' := by
  sorry -- structural equivalence check
```

- [ ] **Step 6: Verify compilation**

Run: `lake env lean Leslie/Examples/CacheCoherence/MESIParam.lean`
Expected: Compiles with sorry-marked obligations

- [ ] **Step 7: Commit**

```bash
git add Leslie/Examples/CacheCoherence/MESIParam.lean
git commit -m "feat: parameterized MESI SWMR via environment abstraction"
```

---

### Task 5: Fill in Framework Proofs

**Files:**
- Modify: `Leslie/SymShared.lean`
- Modify: `Leslie/EnvAbstraction.lean`
- Modify: `Leslie/AssumeGuarantee.lean`

- [ ] **Step 1: Prove `forall_from_focus` in SymShared.lean**

Uses `toSpec_perm_invariant` with `Fin.swap n i` to show that if P holds for process 0 in all reachable states, then P holds for process i (by swapping 0 and i in the execution).

- [ ] **Step 2: Prove `SymAG.compose` in AssumeGuarantee.lean**

Connect `focus_inv` (abstract invariant) to `lift_to_all` via the refinement.

- [ ] **Step 3: Verify full compilation of framework files**

Run: `lake env lean Leslie/AssumeGuarantee.lean`
Expected: Clean (no sorry in framework files)

- [ ] **Step 4: Commit**

```bash
git add Leslie/SymShared.lean Leslie/EnvAbstraction.lean Leslie/AssumeGuarantee.lean
git commit -m "feat: complete framework proofs for env abstraction and AG"
```

---

### Task 6: Fill in MESI Application Proofs

**Files:**
- Modify: `Leslie/Examples/CacheCoherence/MESIParam.lean`

- [ ] **Step 1: Complete `mesi_sym.step` — the full N-process transition relation**

Implement PrRd, PrWr, Evict with snooping, following the patterns in `MESI.lean` but using `Fin n` indexing.

- [ ] **Step 2: Prove `mesi_symmetric`**

Show that `init_perm` and `step_perm` hold by the uniform treatment of indices.

- [ ] **Step 3: Complete `mesi_env` — abstract focus/env transitions**

Define `focus_step` and `env_step` for each MESI action, describing how `EnvCacheSummary` changes. Prove `focus_step_sound` and `env_step_sound` by case analysis.

- [ ] **Step 4: Prove `abs_swmr` as inductive invariant on abstract system**

Case analysis mirroring the 2-process proof in `MESI.lean`, adapted for `EnvCacheSummary`.

- [ ] **Step 5: Prove `mesi_param_swmr` and `mesi_param_two_equiv`**

- [ ] **Step 6: Verify full build**

Run: `lake build`
Expected: Full project builds

- [ ] **Step 7: Commit**

```bash
git add Leslie/Examples/CacheCoherence/MESIParam.lean
git commit -m "feat: complete parameterized MESI SWMR proof"
```

---

### Task 7: Integration

**Files:**
- Modify: `Leslie.lean` (add imports)

- [ ] **Step 1: Add imports to Leslie.lean**

```lean
import «Leslie».SymShared
import «Leslie».EnvAbstraction
import «Leslie».AssumeGuarantee
import «Leslie».Examples.CacheCoherence.MESI
import «Leslie».Examples.CacheCoherence.MESIParam
```

- [ ] **Step 2: Verify full build**

Run: `lake build`
Expected: Clean build

- [ ] **Step 3: Commit**

```bash
git add Leslie.lean
git commit -m "feat: integrate environment abstraction into Leslie"
```

---

## Design Decisions and Trade-offs

### Refinement mapping (function) vs SimulationRel (relation)

The abstraction mapping `abs_map` is a pure function from concrete to abstract state — there is no nondeterminism in the abstraction. Therefore we use `refinement_mapping_stutter` from `Refinement.lean`, which is simpler and already proven sound. `SimulationRel` would be needed only if the abstraction were nondeterministic (e.g., choosing between multiple abstract representations).

### Spec-level symmetry vs step-level equivariance

We define symmetry as `IsSymmetric` (a structure with `init_perm` and `step_perm` at the `Spec` level) rather than requiring step-level equivariance (`step n (π i) a ... = step n i a ...`). This is strictly weaker and easier to prove: the user shows that the overall next-state relation is permutation-invariant, without proving it for each individual step instantiation.

### `EnvCacheSummary` without stored values

The `hasM` variant does not store the Modified cache's value. Instead, the data value invariant is proved separately using the abstract system's shared memory field (which tracks the "true" memory value). This avoids the `Classical.choose` pitfall where different proof contexts might select different witnesses.

### Relationship to existing Leslie infrastructure

| New Component | Builds On | Mechanism |
|--------------|-----------|-----------|
| `SymSharedSpec.toSpec` | `Spec` | Direct construction |
| `toSpec_perm_invariant` | `refinement_mapping_nostutter` | Permutation as refinement |
| `EnvAbstraction.refinement` | `refinement_mapping_stutter` | Abstraction as refinement |
| `lift_to_focus` | `refines_preserves_invariant_stutter` | Invariant transfer |
| `lift_to_all` | `forall_from_focus` + above | Symmetry + transfer |
| `SymAG.focus_inv` | `init_invariant` | Inductive invariant |

> Guided by SageOx
