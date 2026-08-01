# Task — Close `pi_n_AST_fair` (gap 1 + gap 2)

## Goal

Replace the `sorry` at `Leslie/Prob/Liveness.lean:511` (`pi_n_AST_fair`) with a sorry-free proof. This is the *parameterless* fair sublevel-finite-variant rule that `FairASTCertificate.sound`'s `partition_almostDiamond_fair` consumes. Closing it makes `FairASTCertificate.sound` axiom-clean and unblocks downstream `sorryAx` dependencies in protocol soundness theorems (notably `avss_termination_AS_fair`).

## Repo / branch state

- Path: `/Users/rupak/Code/tla/leslie`
- Branch: `feat/randomized-leslie-m3` (latest commit per `git log` at task start)
- Mathlib v4.27.0
- Build: `lake build Leslie.Prob.Index`
- Per-file: `lake env lean Leslie/Prob/Liveness.lean`
- Conservativity: `bash scripts/check-conservative.sh`
- Conservativity allowlist already covers `Leslie/Prob/` and `Leslie/Examples/Prob/` — no changes needed there.

## The sorry — exact location

`Leslie/Prob/Liveness.lean:511`:

```lean
theorem pi_n_AST_fair (cert : FairASTCertificate spec F terminated)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (h_init_inv : ∀ᵐ s ∂μ₀, cert.Inv s)
    (A : FairAdversary σ ι F) (N : ℕ) :
    ∀ᵐ ω ∂(traceDist spec A.toAdversary μ₀),
      (∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0)) → ∃ n, terminated (ω n).1 := by
  sorry
```

## The two gaps

The closure has two distinct obstacles. Both must be addressed.

### Gap 1 — Trajectory-progress witness is unextractable from `isWeaklyFair`

`FairnessAssumptions.isWeaklyFair : Adversary σ ι → Prop` (in `Adversary.lean:74-76`) is opaque. Concrete protocol instances (`brbFair`, `boFair`, `avssFair`, `ccFair`) all use `isWeaklyFair := True` placeholder. The proof needs the trajectory-form fairness witness:

```lean
∀ᵐ ω ∂(traceDist spec A.toAdversary μ₀),
  ∀ N : ℕ, ∃ n ≥ N, ∃ i ∈ F.fair_actions, (ω (n + 1)).2 = some i
```

(captured as `Leslie.Prob.FairASTCertificate.TrajectoryFairProgress`, defined in `Liveness.lean:536`).

`A.fair : F.isWeaklyFair A.toAdversary` reduces to `True` for every concrete instance and yields no information.

#### Resolution path for gap 1 (recommended: refactor `FairnessAssumptions`)

Refactor `FairnessAssumptions` (in `Leslie/Prob/Adversary.lean`) to require a trajectory-form witness:

```lean
structure FairnessAssumptions (σ : Type*) (ι : Type*) where
  fair_actions : Set ι
  isWeaklyFair : Adversary σ ι → Prop
  /-- Trajectory-form witness: under any adversary certified weakly fair,
  fair-required actions fire AE i.o. on the trace measure of any
  spec / `μ₀`. -/
  weak_fair_witness :
    ∀ {σ' : Type*} [Countable σ] [Countable ι]
      [MeasurableSpace σ] [MeasurableSingletonClass σ]
      [MeasurableSpace ι] [MeasurableSingletonClass ι]
      (spec : ProbActionSpec σ ι) (A : Adversary σ ι),
      isWeaklyFair A →
        ∀ (μ₀ : Measure σ) [IsProbabilityMeasure μ₀],
          ∀ᵐ ω ∂(traceDist spec A μ₀),
            ∀ N : ℕ, ∃ n ≥ N, ∃ i ∈ fair_actions, (ω (n + 1)).2 = some i
```

(The `σ'` is a placeholder — the field's actual quantification needs to be over the σ in scope. Adjust as Lean's elaborator requires.)

Then update concrete `FairnessAssumptions` instances (`brbFair`, `boFair`, `avssFair`, `ccFair`) to supply real witnesses. For protocols where `isWeaklyFair := True` (current placeholder), the witness is unprovable — those protocols need to be re-instantiated with REAL fairness predicates.

The natural real predicate for a schedule-based fair adversary:

```lean
isWeaklyFair A := ∀ history, ∀ i ∈ fair_actions,
  (∀ extension, ((spec.actions i).gate (currentState (history ++ extension)))) →
  ∃ extension, A.schedule (history ++ extension) = some i
```

(Schedule-level "fair-required actions fire eventually whenever continuously enabled".) From this, the trajectory-form witness is derivable via integration over `traceDist`.

**Alternatively (simpler refactor)**: instead of refactoring `FairnessAssumptions`, take the `TrajectoryFairProgress` witness as an explicit argument to `pi_n_AST_fair`. This changes `pi_n_AST_fair`'s signature and propagates upward to `partition_almostDiamond_fair` and `FairASTCertificate.sound`. Concrete callers must supply the witness. This matches the pattern already used by `pi_n_AST_fair_with_progress` and `pi_n_AST_fair_with_progress_det`.

**Choose one of these two approaches.** The refactor approach is cleaner long-term; the hypothesis approach is less invasive but pushes the obligation per-caller. For this task, **prefer the refactor** since it's the architecturally correct fix.

### Gap 2 — Chain construction (~250 LOC measure-theoretic bookkeeping)

Even with the progress witness, the textbook geometric-tail argument requires:

1. **Stopping-time function** `T : ℕ → Trace σ ι → ℕ` (the k-th fair-firing time on a trajectory). Defined via `Nat.find` on the i.o. fair-firing predicate from the trajectory-progress witness.
2. **Measurability** of `Nat.find`-derived stopping times against the discrete σ-algebra on `Trace σ ι`. With `[MeasurableSpace σ] [MeasurableSingletonClass σ]` plus discrete `Option ι`, every set on each coordinate is measurable, so `Nat.find` events are countable unions of cylinder sets.
3. **Decreasing chain** `C k := badSet ∩ {ω | by step T k ω, fewer than k strict-U-decreases at fair-firings}`. Note: `badSet := {ω | (∀ n, V ≤ N) ∧ ∀ n, ¬ terminated}`.
4. **Recurrence** `μ(C (k+1)) ≤ (1 - q) · μ(C k)`. Comes from `traceDist_kernel_step_bound` (already in `Refinement.lean:586`, sorry-free) applied at step `T k ω` — the kernel-step bound says the "U decreases here" event has conditional probability ≥ q where `q = min p 1` and `p` is from `cert.U_dec_prob`.
5. **Containment** `badSet ⊆ ⋂ k, C k`. On `badSet`, fair firings happen i.o. (from the trajectory progress witness) and U is bounded by M (from `cert.U_bdd_subl N`), so at most M strict decreases ever occur — hence after the M+1-th fair firing, the trajectory must have been in `C k` for some `k > M`, contradiction with `badSet`. Properly: `badSet ⊆ C k` for every k because the chain is "fewer than k decreases" which, on the bad set, holds since strict decreases are bounded.
6. **Conclude** `μ(badSet) ≤ inf_k μ(C k) ≤ inf_k (1-q)^k = 0` via `MeasureTheory.measure_iInter_eq_iInf` and `tendsto_pow_atTop_nhds_zero_of_lt_one`.

#### Resolution path for gap 2

The proof structure is **already scaffolded** in:

- `pi_n_AST_fair_with_progress` (line 716): replaces the `_h_progress` hypothesis call to `pi_n_AST_fair`. Its body REDUCES to a `μ(badSet) = 0` goal. The reduction (set the bad set, use `MeasureTheory.ae_iff`, simp the implication negation) is closed.

- `pi_n_AST_fair_chain_witness` (line 646): the auxiliary that asserts the existence of the geometric chain. Body is `sorry`. THIS is the concentrated location of the ~250 LOC bookkeeping.

- The geometric → 0 limit (extracting `q`, deriving `(1-q)^k → 0`, applying `le_of_tendsto_of_tendsto'`) is already closed in `pi_n_AST_fair_with_progress`'s body.

**Mathlib lemmas already used** (in the existing scaffold):
- `MeasureTheory.ae_iff`
- `ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one`
- `le_of_tendsto_of_tendsto'`
- `Refinement.AlmostBox_of_inductive` (for the trajectory-Inv lift)

**Mathlib lemmas needed for `pi_n_AST_fair_chain_witness` body**:
- `traceDist_kernel_step_bound` (in `Refinement.lean:586` — closed, sorry-free; key helper).
- `MeasureTheory.measure_iInter_eq_iInf` (or `tendsto_measure_iInter_atTop` — for decreasing chain measure).
- `Nat.find` / `Nat.find_spec` — for the stopping-time construction.
- `Function.Iterate` and basic iterate lemmas for the chain recursion.

## Concrete attack plan

Follow this order:

### Step 0 — Read the existing scaffold

Read `Leslie/Prob/Liveness.lean` from line 540 to line 1010. The structure is:
- Line 511: target sorry (`pi_n_AST_fair`).
- Line 536: `TrajectoryFairProgress` definition.
- Line 646: `pi_n_AST_fair_chain_witness` (sorry — gap 2).
- Line 716: `pi_n_AST_fair_with_progress` (closed via the chain witness).
- Line 1009: `pi_n_AST_fair_with_progress_det` (closed sorry-free, deterministic specialization).

Also read `Leslie/Prob/Refinement.lean:586` for `traceDist_kernel_step_bound` (the kernel-step bound helper, sorry-free).

### Step 1 — Resolve gap 1

Choose:
- **(1a)** Refactor `FairnessAssumptions` to add `weak_fair_witness` field. Update concrete instances. (Invasive; affects `BrachaRBC`, `BenOrAsync`, `AVSSStub`, `AVSS`, `CommonCoin`, `SyncVSS`. For protocols with `isWeaklyFair := True` placeholder, you'll need to either (i) add a meaningful schedule-level fairness predicate OR (ii) leave the field as a `sorry` per-instance — but that defeats the purpose.)
- **(1b)** Take `TrajectoryFairProgress` as an explicit hypothesis on `pi_n_AST_fair`. Propagate to `partition_almostDiamond_fair` and `FairASTCertificate.sound`. (Non-invasive; concrete callers supply the witness.)

For closing `pi_n_AST_fair` itself, **(1b) is sufficient** if you're willing to change the theorem signature. **(1a)** is required if you want `FairASTCertificate.sound` to keep its current parameterless shape.

Recommendation: pursue **(1b)** for this task. It's a one-line signature change on `pi_n_AST_fair` (add `(_h_progress : TrajectoryFairProgress spec F μ₀ A)` after `A`), then call `pi_n_AST_fair_with_progress` (which already takes the witness) directly. This makes `pi_n_AST_fair`'s body a one-liner — `exact pi_n_AST_fair_with_progress cert μ₀ h_init_inv A _h_progress N`.

The signature change propagates to `partition_almostDiamond_fair` and `FairASTCertificate.sound`. Update those too (mechanical; just add the hypothesis).

### Step 2 — Close gap 2 (the chain witness)

This is the genuine ~250 LOC of work. Open `pi_n_AST_fair_chain_witness` at line 646. Its current body is `sorry`. The signature:

```lean
theorem pi_n_AST_fair_chain_witness
    (cert : FairASTCertificate spec F terminated)
    (μ₀ : Measure σ) [IsProbabilityMeasure μ₀]
    (A : FairAdversary σ ι F)
    (_h_progress : TrajectoryFairProgress spec F μ₀ A)
    (N : ℕ) (q : ℝ≥0) (_hq_pos : 0 < q) (_hq_le_one : q ≤ 1)
    (_hq_dec_prob :
      ∀ (i : ι) (s : σ) (h : (spec.actions i).gate s),
        i ∈ F.fair_actions → cert.Inv s → ¬ terminated s →
        cert.V s ≤ (N : ℝ≥0) →
        (q : ENNReal) ≤
          ∑' (s' : σ),
            ((spec.actions i).effect s h) s' *
              (if cert.U s' < cert.U s then 1 else 0)) :
    ∃ C : ℕ → Set (Trace σ ι),
      (∀ k, {ω : Trace σ ι |
              (∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0)) ∧
                ∀ n, ¬ terminated (ω n).1} ⊆ C k) ∧
      (∀ k, (traceDist spec A.toAdversary μ₀) (C k) ≤
              (1 - (q : ENNReal)) ^ k)
```

**Implementation outline** (the body):

```lean
-- 1. Stopping time T k : Trace σ ι → ℕ  (k-th fair-firing time)
let T : ℕ → Trace σ ι → ℕ := fun k ω => ...
-- Defined via Nat.find on the predicate "after step n, a fair firing occurs".
-- For ω where the witness fails, default to 0 (we only care about the AE set).

-- 2. Measurability of T k events.
-- Each {ω | T k ω = m} is a countable union of cylinder sets, measurable
-- under the discrete coordinate measurable spaces.

-- 3. Define C k := badSet ∩ {ω | by step T k ω, fewer than k strict-U-decreases
--                                at fair firings}.
let C : ℕ → Set (Trace σ ι) := fun k => badSet ∩ {ω | ...}
-- This is what we want to bound below by (1-q)^k.

-- 4. Recurrence: μ(C (k+1)) ≤ (1 - q) · μ(C k).
have h_recur : ∀ k, μ(C (k+1)) ≤ (1 - q) · μ(C k) := by
  intro k
  -- Apply traceDist_kernel_step_bound at step T k ω.
  -- The kernel-step bound says: for the prefix-set "we're in C k AND
  -- fair-action fires at step T k + 1 from the right state", the joint
  -- mass on "AND U decreases at step T k + 1" is ≥ q · μ(C k).
  -- C (k+1) ⊆ C k \ "decrease-at-T-k", so
  -- μ(C (k+1)) = μ(C k) - μ(C k ∩ "decrease-at-T-k") ≤ (1 - q) · μ(C k).
  sorry  -- ~80 LOC of kernel-step plumbing.

-- 5. Iterate: μ(C k) ≤ (1 - q)^k.
have h_geom : ∀ k, μ(C k) ≤ (1 - q)^k := by
  intro k
  induction k with
  | zero => exact prob_le_one ...
  | succ k ih =>
    calc μ(C (k+1)) ≤ (1 - q) · μ(C k) := h_recur k
      _ ≤ (1 - q) · (1 - q)^k := by gcongr
      _ = (1 - q)^(k+1) := by ring

-- 6. Containment: badSet ⊆ C k for every k.
have h_sub : ∀ k, badSet ⊆ C k := by
  intro k ω hω
  -- On badSet, U is bounded by M = cert.U_bdd_subl N. Strict decreases
  -- are at most M. So "fewer than k strict decreases" holds for k > M
  -- (and trivially holds at the start). For all k, by induction.
  sorry  -- ~30 LOC.

exact ⟨C, h_sub, h_geom⟩
```

**Key technical detail for step 4** (the recurrence): use `traceDist_kernel_step_bound` with:
- `n := T k ω` (depends on ω; need to handle this via integration over T k's value).
- `S := C k` (the k-th level of the chain).
- `D := {next state has U < current U}` (the U-decrease set).
- `p := q`.
- `h_step` follows from `_hq_dec_prob` plus the fact that on `S`, a fair action fires at step `n+1` (from the chain's definition).

The integration over T k's value (since T k is itself a function of ω) is the tricky part. One clean way: use `tsum` over `m : ℕ`, with `T k ω = m` partitioning the trace space. For each m, apply the kernel-step bound at fixed `n := m`.

### Step 3 — Verify

- `lake env lean Leslie/Prob/Liveness.lean`: should show 0 sorries on `pi_n_AST_fair`, `pi_n_AST_fair_chain_witness`, `pi_n_AST_fair_with_progress`. The earlier sorry on `pi_n_AST` (demonic version, line 204) is **separate** — it has the stuttering issue and is NOT in scope for this task.
- `#print axioms FairASTCertificate.sound`: should show `[propext, Classical.choice, Quot.sound]` only.
- `lake build Leslie.Prob.Index`: green, sorry count drops from 3 in `Liveness.lean` to 1 (just the demonic `pi_n_AST` at line 204).

## Constraints

- **Allowed paths**: `Leslie/Prob/Liveness.lean` (target). May also touch `Leslie/Prob/Adversary.lean` if you do option (1a). Do NOT touch `Leslie/Examples/Prob/*` files unless necessary — they shouldn't need changes.
- No new dependencies in `lakefile.lean`.
- Must commit at end. Don't push to origin.
- Don't run destructive git ops.

## Out of scope

- The demonic `ASTCertificate.pi_n_AST` (line 204) — has the stuttering-adversary issue documented in `docs/randomized-leslie-spike/10-stuttering-adversary-finding.md`. Different problem.
- `BrachaRBC.brbProb_totality_AS_fair` (line 681) — orthogonal `AlmostDiamond_of_leads_to` use, already closed via the bridge.
- Any of the AVSS-side termination obligations.

## Acceptance

- `lake build Leslie.Prob.Index` green.
- `lake env lean Leslie/Prob/Liveness.lean` shows 0 sorries on the three theorems above.
- `#print axioms FairASTCertificate.sound` axiom-clean.
- `bash scripts/check-conservative.sh` passes (44-46 files in allowlist depending on if you touched Adversary.lean).
- One or two commits on the branch (per gap if you split). Final state: file builds without sorry on the targeted three theorems.

## Time budget

Realistic full-closure estimate: 2-4 days of focused work. Per phase:
- Gap 1 (signature refactor — option 1b): ~30 min.
- Gap 2 (chain construction): ~250 LOC, 4-8 hours of careful Lean work.
- Verification + commit: ~30 min.

For an agent: 200-300 minute budget. If hitting Mathlib API obstacles, fall back to the (1a) approach or document and stop.

## Final report (terse)

- gap 1 status (closed via (1a) or (1b))
- gap 2 status (closed / partial / blocked-on-X)
- New `Liveness.lean` sorry count
- `#print axioms` of `FairASTCertificate.sound`
- Commit SHA(s)
- Mathlib lemmas used
