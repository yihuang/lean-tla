# Proof Strategy Guide for Leslie

This document captures lessons from building invariant proofs for distributed protocols in Leslie.
The patterns here apply whenever you need to prove `invariant` holds for all reachable states of a
parameterized transition system.

---

## The Core Proof Structure

Every reachability proof has three pieces:

```
1. Reachable n s    (inductive definition)
2. strongInv_init   (invariant holds initially)
3. strongInv_step   (invariant preserved by every transition)
   └── for each action A: strongInv_preserved_A
```

The difficulty lives entirely in step 3. Everything below is about making step 3 tractable.

---

## Pattern 1: Frame Lemmas

**The problem**: Most invariant components are trivially preserved by most actions because the
action doesn't touch the relevant state fields. But without explicit frame lemmas, every sub-goal
requires a manual proof even when the answer is "nothing changed".

**The fix**: For each action, prove *what it does not change* as a single reusable lemma.

```lean
-- Define what each action modifies as a structure equality
lemma sendReqS_frame {s s' : MState n} {i : Fin n}
    (h : s' = { s with chan1 := setFn s.chan1 i { (s.chan1 i) with cmd := .reqS } }) :
    s'.cache = s.cache ∧ s'.chan2 = s.chan2 ∧ s'.chan3 = s.chan3 ∧
    s'.invSet = s.invSet ∧ s'.shrSet = s.shrSet ∧ s'.exGntd = s.exGntd ∧
    s'.curCmd = s.curCmd ∧ s'.memData = s.memData ∧ s'.auxData = s.auxData := by
  subst h; simp [setFn]
```

Then any invariant component that only reads `{cache, chan2, chan3, ...}` is discharged by:

```lean
exact ⟨..., by rw [(sendReqS_frame h).1, (sendReqS_frame h).2.1, ...]; exact hcomp, ...⟩
```

Or better, annotate each frame lemma as `@[simp]` so that `simp [sendReqS_frame h]` closes all
trivially-preserved components at once.

**Impact**: For an M-action × N-component proof matrix, frame lemmas can reduce the number of
hand-written proofs from M×N to roughly M + (non-trivial sub-goals), often a 5–10× reduction.

---

## Pattern 2: Hierarchical Invariant Decomposition

**The problem**: A flat conjunction of N unrelated predicates forces you to maintain all N
components in every action proof, even when an action only affects one group.

**The fix**: Group invariant components by which state fields they read. An action that only
modifies `chan1` trivially preserves every group that doesn't read `chan1`.

```lean
-- Group by read-set
def channelCoherence n s : Prop :=
  -- predicates that only read chan2 and chan3
  grantExcludesInvAck n s ∧ gntSExcludesInvAck n s ∧
  invAckClearsGrant n s ∧ chan3IsInvAck n s

def cacheBookkeeping n s : Prop :=
  -- predicates that only read cache, shrSet, exGntd
  exclusiveSelfClean n s ∧ cacheInShrSet n s

def controlCoherence n s : Prop :=
  -- predicates that read curCmd, invSet, exGntd
  invRequiresNonEmpty n s ∧ invClearsInvSet n s ∧ invSetImpliesClean n s

def fullInvariant n s : Prop :=
  coreInvariant n s ∧ channelCoherence n s ∧
  cacheBookkeeping n s ∧ controlCoherence n s
```

Then prove group-level frame theorems:
```lean
lemma channelCoherence_preserved_of_chan2_chan3_eq
    (h2 : s'.chan2 = s.chan2) (h3 : s'.chan3 = s.chan3)
    (hc : channelCoherence n s) : channelCoherence n s' := by
  simp_all [channelCoherence, grantExcludesInvAck, ...]
```

This reduces the M×N matrix to roughly M × (number of groups) for trivial cases.

---

## Pattern 3: Factored Action Predicates

**The problem**: When `next` is an existential over a large `match`, proof contexts become unwieldy.
Unfolding `next` leaves you deep inside nested match arms, making it hard to reuse lemmas.

**The fix**: Define each action as its own named predicate, then `next` is a disjunction:

```lean
def SendReqS (s s' : MState n) (i : Fin n) : Prop :=
  (s.chan1 i).cmd = .empty ∧ (s.cache i).state = .I ∧
  s' = { s with chan1 := setFn s.chan1 i { (s.chan1 i) with cmd := .reqS } }

def Next n s s' : Prop :=
  (∃ i, SendReqS s s' i) ∨ (∃ i, SendReqE s s' i) ∨ ...
```

Benefits:
- Each `strongInv_preserved_A` takes `SendReqS s s' i` as a clean typed hypothesis
- The assembly proof `strongInv_step` is a single `rcases` on the disjunction
- Frame lemmas are stated once per action predicate, reused everywhere

---

## Pattern 4: Automation with Aesop

Register group-level preservation lemmas as `aesop` rules so the trivial layer is fully automated:

```lean
@[aesop safe apply]
lemma channelCoherence_preserved_chan1_only
    (hframe : s'.chan2 = s.chan2 ∧ s'.chan3 = s.chan3)
    (hc : channelCoherence n s) : channelCoherence n s' := ...

@[aesop safe apply]
lemma cacheBookkeeping_preserved_chan_only
    (hframe : s'.cache = s.cache ∧ s'.shrSet = s.shrSet ∧ s'.exGntd = s.exGntd)
    (hb : cacheBookkeeping n s) : cacheBookkeeping n s' := ...
```

Then for simple actions: `aesop [sendReqS_frame h]` closes the entire preservation proof.

---

## Recommended File Layout

For any non-trivial protocol proof, split across files by concern:

```
Protocol/
  Model.lean          -- State, actions (as named predicates), Next, Spec
                      -- No proofs. This is the spec layer.
  FrameLemmas.lean    -- For each action: what fields change and what don't
                      -- All @[simp]. These are purely structural.
  Invariant.lean      -- Invariant definition, decomposed into groups
                      -- coreInvariant, channelCoherence, etc.
  InitProof.lean      -- fullInvariant holds for init states
  StepProof.lean      -- fullInvariant preserved by Next
                      -- Imports FrameLemmas; trivial cases close by simp
  Theorem.lean        -- Reachable, main safety theorem, derived corollaries
```

Benefits:
- `StepProof.lean` stays small because frame lemmas handle the bulk
- Each file fits comfortably in a context window
- Model changes only require updating `Model.lean` + the directly affected proofs
- The non-trivial proof content (the actual invariant reasoning) is concentrated
  in a small part of `StepProof.lean`, easy to audit

---

## The Key Mental Model

Think of each action as having a **modification footprint** (which fields it writes) and each
invariant component as having a **read footprint** (which fields it reads). Preservation is:

```
footprint(action) ∩ footprint(invariant_component) = ∅  →  trivially preserved
```

The goal of proof infrastructure is to make this disjointness check mechanical. Frame lemmas
encode the action footprint; grouping encodes the invariant footprint. Once both are explicit,
automation handles the trivial cases and only the non-trivial interactions remain.

In a well-structured protocol proof, the non-trivial interactions should be ~10–20% of the
total obligations. If you're hand-proving more than that, there's missing infrastructure.

---

## Lessons from the Directory MSI Proof (4,476 lines, 19 actions, 35 invariant conjuncts)

The following patterns emerged from scaling the above principles to a more complex protocol.

---

### Pattern 5: Model Actions as Named Pure Functions

**The problem**: Defining actions as inline `s' = { s with ... }` inside a guard conjunction
works for small protocols, but for 19 actions the model becomes unreadable and simp lemmas
need to reference long compound expressions.

**The fix**: Factor each action into a *named state transformer* and a *guard predicate*:

```lean
-- Pure function: what the state becomes
def recvInvState {n} (s : MState n) (i : Fin n) : MState n :=
  { s with
    cache   := setFn s.cache   i { (s.cache i) with state := .I }
    c2dChan := setFn s.c2dChan i { cmd := .ack, data := (s.cache i).data }
    d2cChan := setFn s.d2cChan i {} }

-- Guard + equation
def RecvInv (s s' : MState n) (i : Fin n) : Prop :=
  (s.d2cChan i).cmd = .inv ∧
  (s.c2dChan i).cmd = .empty ∧
  s' = recvInvState s i
```

Benefits:
- Simp lemmas are stated against the named function: `recvInvState_cache_state_self`,
  `recvInvState_d2cChan_ne`, etc.
- The guard is clearly separated from the effect
- `subst hs'` in proofs replaces `s'` with a concrete term that simp can reduce

**Naming convention**: Name actions by their distinguishing *guard condition*, not their effect.
Use `RecvGetS_Uncached` / `RecvGetS_Shared` / `RecvGetS_Exclusive` (the directory state that
enables the action). Avoid ambiguous qualifiers like "After" — prefer "From" if describing
the pre-state.

---

### Pattern 6: Per-Field Indexed Simp Lemmas

**The problem**: When an action modifies an indexed field like `cache[i]`, proofs need to
distinguish `k = i` (self case) from `k ≠ i` (frame case) for every invariant that reads
that field. Without targeted lemmas, this requires manual `setFn` unfolding everywhere.

**The fix**: For each indexed field modified by an action, provide `_self` and `_ne` lemmas:

```lean
@[simp] theorem recvInvState_cache_state_self {n} (s : MState n) (i) :
    ((recvInvState s i).cache i).state = .I := by simp [recvInvState]

@[simp] theorem recvInvState_cache_state_ne {n} (s : MState n) (i j : Fin n) (h : j ≠ i) :
    ((recvInvState s i).cache j).state = (s.cache j).state := by simp [recvInvState, h]
```

For non-indexed fields, provide a single lemma:
```lean
@[simp] theorem recvInvState_dirSt {n} (s : MState n) (i) :
    (recvInvState s i).dirSt = s.dirSt := rfl
```

**Cost**: ~13 lemmas per action × 19 actions = ~250 lemmas. This is significant boilerplate
(~60% of Model.lean in DirectoryMSI). A `deriving` handler or metaprogram that auto-generates
these from the `{ s with ... }` expression would be valuable infrastructure.

**The proof pattern this enables**: Every indexed-field invariant is proved by:
```lean
by_cases hki : k = i
· subst hki; simp [actionState_field_self] ...  -- use the self lemma
· rw [actionState_field_ne s i k hki] ...       -- rewrite to pre-state, use hypothesis
```

This `by_cases` + `_self`/`_ne` dispatch is the dominant proof pattern (287 occurrences in
DirectoryMSI). It is a candidate for a custom `indexed_cases` elab tactic.

---

### Pattern 7: Invariant Strengthening Strategy

**The problem**: The public safety property (SWMR + data integrity) is not inductive — it is
not preserved by the transition relation alone. You need auxiliary invariants to make it
inductive, but discovering them is the hardest part of the proof.

**The approach**:

1. **Start with known invariant templates.** For cache coherence protocols, these categories
   cover most needed invariants:
   - *Directory-cache consistency*: `mImpliesExclusive`, `sImpliesShrSet`,
     `exclusiveConsistent`, `uncachedMeansAllInvalid`
   - *Data flow*: `gntSDataProp`, `gntEDataProp`, `ackDataProp` (messages carry correct data)
   - *Channel discipline*: `invAckExclusive`, `ackImpliesD2cEmpty` (no conflicting messages)
   - *Invalidation tracking*: `invSetSubsetShrSet`, `invImpliesInvSetFalse`
   - *Grant consistency*: `gntEImpliesExclusive`, `gntSImpliesDirShared`,
     `exclusiveNoDuplicateGrant`, `sharedNoGntE`

2. **Prove init + the 2 simplest actions first** to validate the invariant structure.
   Actions that only modify `reqChan` (like SendGetS, SendGetM) should be trivially
   preserved by frame lemmas.

3. **Work in order of action complexity.** When a proof fails, the error message usually
   reveals which auxiliary invariant is missing. Add it, prove init, update frame lemmas,
   then continue.

4. **Batch invariant additions.** Don't add one invariant at a time — each addition requires
   updating obtain/destructuring patterns across all proof files. Discover 3-5 missing
   invariants, then do one cross-cutting update.

**In DirectoryMSI**, the invariant grew from 12 to 35 conjuncts over the course of the proof.
The most productive discovery sessions came from attempting Tier 3 proofs (ack processing)
which revealed channel discipline invariants needed by simpler actions' proofs.

---

### Pattern 8: Tiered Proof Files by Action Complexity

**The problem**: With 19 actions, a single StepProof.lean would exceed 4,000 lines — too large
for human review or LLM context.

**The fix**: Split action proofs into tiers by complexity:

```
StepTier1.lean   -- Actions that only modify directory-side fields
                 -- (reqChan, curCmd, curNode, shrSet, invSet, d2cChan)
                 -- These don't touch cache/c2dChan, so ctrlProp/dataProp are trivial
StepTier2.lean   -- Directory-side actions that modify d2cChan (sends)
                 -- More by_cases work but no cache reasoning
StepTier3A.lean  -- Ack processing (RecvAck_*)
                 -- These consume c2dChan, may update memData/auxData/dirSt
StepTier3B.lean  -- Grant reception (RecvGntS, RecvGntE)
                 -- These update cache from d2cChan grants
StepTier3C.lean  -- Invalidation/fetch reception (RecvInv, RecvFetch)
                 -- These transition cache to I and create acks
StepProof.lean   -- Dispatch hub: imports all tiers, proves fullStrongInvariant_preserved
```

Each tier file exports public theorems that the dispatch hub calls. The dispatch hub itself
is ~30 lines of `rcases` + `exact`.

**Guideline**: Keep each tier file under 1,000 lines. If a single action proof exceeds 500
lines, it likely needs more derived lemmas to shorten the `by_cases` blocks.

---

### Pattern 9: Avoiding Fragile Conjunction Destructuring

**The problem**: A 35-conjunct `fullStrongInvariant` defined as nested `∧` requires a
35-variable `obtain` pattern in every proof:

```lean
obtain ⟨⟨⟨hctrl, hdataF, hdataS⟩, hexclCons, hmImpl, ...⟩,
    hackD, hcurNot, ..., hInvInvSet⟩ := h
```

Adding one new conjunct breaks every obtain pattern in every file.

**Better approach (recommended for future protocols)**: Define the invariant as a structure:

```lean
structure FullStrongInvariant (n : Nat) (s : MState n) : Prop where
  ctrl : ctrlProp n s
  dataFresh : s.dirSt ≠ .Exclusive → s.memData = s.auxData
  dataValid : ∀ i, (s.cache i).state ≠ .I → (s.cache i).data = s.auxData
  exclCons : exclusiveConsistent n s
  mImpl : mImpliesExclusive n s
  -- ... 30 more fields
```

Benefits:
- Access by name: `h.ctrl`, `h.exclCons` — no positional fragility
- Adding a new field only requires updating the definition + construction sites, not
  every access site
- Lean auto-generates projection functions
- Pattern matching on individual fields with `h.field` instead of destructuring everything

**Construction**: Use `exact ⟨proof1, proof2, ...⟩` or named field syntax:
```lean
exact { ctrl := ..., dataFresh := ..., dataValid := ..., exclCons := ..., ... }
```

---

### Pattern 10: Frame Lemma for New Invariants

**The problem**: When adding a new invariant conjunct to an existing proof, you need to prove
it is preserved by every action. For actions that don't touch the relevant fields, this should
be trivial — but getting it connected to the existing proof machinery is error-prone.

**The fix**: For every new invariant `P` that reads fields `f1, f2`:

1. Add a per-component frame lemma in FrameLemmas.lean:
   ```lean
   theorem P_preserved_of_f1_f2_eq (h1 : s'.f1 = s.f1) (h2 : s'.f2 = s.f2)
       (h : P n s) : P n s' := by
     intro i hi; rw [h1] at hi; rw [h2]; exact h i hi
   ```

2. Add it to the compound frame lemma (for trivial actions like SendGetS).

3. For non-trivial actions, prove `P` separately from the `simp + refine` block.
   **Do not add `P` to the simp list** — this changes the number of unresolved
   conjuncts after simp, breaking the `refine ⟨...⟩` term count for every proof.
   Instead, handle `P` as an opaque goal:
   ```lean
   refine ⟨..., ?_⟩  -- last ?_ is for P (not unfolded by simp)
   · -- P
     unfold P; intro k hk
     by_cases hki : k = i
     · ...
     · ...
   ```

   Or for actions where `f1` and `f2` are literally unchanged:
   ```lean
   refine ⟨..., P_preserved_of_f1_f2_eq rfl rfl hP⟩
   ```

This pattern avoids the "adding one invariant breaks all proofs" failure mode.
