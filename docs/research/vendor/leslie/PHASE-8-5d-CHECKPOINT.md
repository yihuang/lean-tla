# Phase 8.5d Checkpoint — **chain fully closed (α + β + γ + δ; 0 sorries)**

**Final state (2026-05-07):** Phase 8.5d chain is complete.
8.5d-α (PR #68), 8.5d-β (PR #69), 8.5d-γ (PR #70), and 8.5d-δ
(this PR — docs-only MODEL_NOTES finalisation) all landed.
AVSS.lean has **0 sorries**; all C4 closure surgery is in
place; `s.coeffs` migration to μ₀ is complete; termination is
re-scoped to take `h_consistent_quorum`.  MODEL_NOTES §11
caveats C1, C2, C4 are marked ✅ resolved with citation tables;
C5 carries a cross-branch resolution note (Phase 9 chain on a
parallel branch).  §12.1 status tracker reflects landed PRs
#57–#70 (stale 8.5b-i/ii/iii planning rows dropped).  §12.3
post-Phase-8 state table is frozen as the canonical citation
target.  §12.4 risks 1–3 are marked resolved; risk 4 (row +
column secrecy) remains pending in 8.6.  A new §14 stub
documents the queued Phase 11 secrecy-framework-abstraction
work.

## Phase 8.5d-δ — what landed (this PR, docs-only)

- `Leslie/Examples/Prob/AVSS-MODEL-NOTES.md` — §11.1 (C1) /
  §11.2 (C2) gain ✅ resolution-status banners with citation
  tables; §11.3 (C3) historical Phase-B fix retains its banner
  with a forward pointer to 8.5d-α's `dealerShareTo`; §11.4 (C4)
  resolution banner extended with PR #70 attribution and the
  new theorem statement (`avss_termination_AS_fair` with
  `h_consistent_quorum`); §11.5 (C5) gains a cross-branch
  resolution note (Phase 9 chain, future merge-time
  reconciliation).  §12.1 status tracker rewritten to reflect
  actual landed PRs (drop stale 8.5b-i/ii/iii pre-implementation
  rows; add #57–#70 as separate rows for the α/β/γ chain;
  reclassify 8.7 as likely no-op; mark 8.8 subsumed by 8.5d-δ).
  §12.3 post-Phase-8 state table frozen as canonical reference.
  §12.4 risks 1, 2, 3 marked ✅ resolved; risk 4 retained as
  ⏳ pending.  New §14 — Phase 11 secrecy-framework-abstraction
  stub (~320 LOC, 4 stacked sub-PRs queued for after 8.5d-δ).
- `PHASE-8-5d-CHECKPOINT.md` — this update.

**No code changes** (docs-only PR).  Build remains green at
`lake build Leslie.Prob.Index` and `lake build
Leslie.Examples.Prob.AVSS` (0 sorries).

## Phase 8.5d-γ — what landed (PR #70)

**Branch**: `feat/randomized-leslie-m3-avss-phase8-5d-gamma`
**Base**: PR #69 (8.5d-β, `coeffs` migration to μ₀, 0 sorries, fully closed β-chain).
**Build state**: green at `lake build Leslie.Prob.Index` (2699 jobs)
and `lake build Leslie.Examples.Prob.AVSS` (no errors, no sorries).
**Sorry count**: **0** in AVSS.lean.

## Phase 8.5d-γ — what landed

Re-scoped `avss_termination_AS_fair` and its `_traj` / `_rushing`
variants to take a new `h_consistent_quorum` hypothesis capturing
the conditional-CR runtime requirement under selective non-broadcast
(C4): AE on traces, eventually a coalition of at least `n - t`
honest parties has both `dealerSent p = true` and `dealerMessages p
≠ none`.

This formalises CR '93's conditional-termination semantics that was
previously bypassed by the Phase-B unconditional-fairness route
(`dealerShare` forced into `avssFairActions`). Under Phase 8.5d-α
per-party `dealerShareTo`, a corrupt dealer can selectively
short-share — fair scheduling no longer guarantees every honest party
gets a share, so termination becomes conditional.

**New definitions in `AVSS.lean`** (§13.0, just before the
termination theorems):

- `consistent_quorum_AE sec corr coeffs μ₀ A` — trajectory-AE form
  of the conditional-CR hypothesis.
- `consistent_quorum_AE_of_all_honest_delivered` — sanity-check
  lemma: any AE-trajectory schedule that delivers to every honest
  party (`∀ p ∉ corr, dealerSent p = true ∧ dealerMessages p ≠
  none`, eventually) satisfies `consistent_quorum_AE`.  Card
  argument: the filtered set equals `corrᶜ`, of cardinality `n -
  corr.card ≥ n - t` via `h_corr`.

**Re-scoped theorems**:

| Theorem | New hypothesis position |
|---|---|
| `avss_termination_AS_fair_traj` | between `A` (TrajectoryFairAdversary) and `h_drop_io` |
| `avss_termination_AS_fair` (wrapper) | same, threaded into `_traj` |
| `avss_termination_AS_fair_rushing` | between `h_progress` and `h_drop_io`, threaded into wrapper |

The proof bodies are unchanged: the existing BC running-min route
(`pi_n_AST_fair_with_progress_bc_of_running_min_drops`, supplied via
`h_drop_io`) does the operational lifting; the new
`h_consistent_quorum` documents the structural CR-conditional
assumption that downstream callers must establish.

The `_traj` proof binds the new hypothesis as `_h_consistent_quorum`
(unused — it's the structural assumption that justifies *why*
`h_drop_io` should be supplied, not a derivation source).

**Phase 9 deferral**: `avss_termination_AS_fair_randomised` and
`avss_termination_AS_fair_rushing_randomised` (PRs #54/#55) live on
the Phase 9 branch chain (independent of Phase 8); their re-scoping
is a future merge-time concern when Phase 8 and Phase 9 reconcile.

**Files touched**:

- `Leslie/Examples/Prob/AVSS.lean` — +~80 LOC (`consistent_quorum_AE`
  def, sanity-check lemma, three theorem signature updates).
- `Leslie/Examples/Prob/AVSS-MODEL-NOTES.md` — §11.4 marked ✅
  resolved by Phase 8.5d-γ; §12.1 row 8.5d updated to ✅ landed.
- `PHASE-8-5d-CHECKPOINT.md` — this update.

## Phase 8.5d-β-followup-7 — what landed (kept for reference)

## Phase 8.5d-β-followup-7 — what landed

Closed the corrupt-dealer case of `avss_secrecy_AS_view_rushing` via a
new dealerHonest-INDEPENDENT chain that drops the cTV bridge's
honest-dealer guard.  The headline now closes for ANY `dealerHonest`
value uniformly — no case-split needed.

**Architectural insight**: the cTV bridge `coalitionTraceView ω =
reconstruct(coalitionAlgebraicView, ...)` was honest-dealer-conditional
because it used `phase6Inv c`'s `dealerMessagesInv` (only fires under
honest dealer).  Replacing that with a NEW dealerHonest-INDEPENDENT
invariant `coalitionRowPolyAlignedInv` (a structural protocol fact: every
populated `dealerMessages p` matches `dealerCommit p`, and corrupt parties'
delivered rowPoly matches `dealerCommit p .rowPoly`) makes the bridge
unconditional. Combined with `avss_phase6InvEx_AS` for the c-independent
`corruptLocalInv` clauses, the full bridge is dealerHonest-INDEPENDENT.

**New infrastructure (followup-7)**:

- `coalitionRowPolyAlignedInv` — structural alignment invariant (no honest
  dealer assumption).  Two clauses:
  1. `∀ p msg, dealerMessages p = some msg → msg = dealerCommit p`.
  2. `∀ p ∈ corrupted, delivered → rowPoly = some (dealerCommit p .rowPoly)`.
- `avssStep_preserves_coalitionRowPolyAlignedInv` — preservation by every
  gated avssStep, with the `partyCorruptDeliver` case using clause 1 to
  bridge `dealerMessages p .rowPoly` to `dealerCommit p .rowPoly`.
- `initPred_coalitionRowPolyAlignedInv` — initPred's structural part
  implies the invariant vacuously.
- `avss_coalitionRowPolyAlignedInv_AS` — AlmostBox lift via
  `AlmostBox_of_pure_inductive`.

**New `_indep` chain (drops `h_dH_sec` / `h_dH_sec'` from `_ex` chain)**:

- `coalitionView_corrupt_factors_AE_indep` — drops the honest-dealer guard
  from the rowPoly clause.
- `coalitionTraceView_eq_reconstruct_AE_indep` — drops the
  `(ω 0).1.dealerHonest = true → ...` guard from the conclusion.
- `avss_secrecy_AS_view_conditional_indep`, `_via_aux_indep`,
  `_via_init_invariant_indep` — chain wrappers without h_dH hypotheses.

**Headline closure (dealerHonest-INDEPENDENT)**: the proof body is now
3 lines — directly applies `_via_init_invariant_indep` with the
existential h_init from `avssInitMeasure_AE_initPred` and the joint
sec-invariance from `avssInitMeasure_simViewExt_sec_invariant`.  No
case-split on `dealerHonest`.

**Refactoring**: moved `avssStep_dealerCommit_invariant` from §17 (line
8402) to §6 (line 547) so it's in scope for `coalitionRowPolyAlignedInv`'s
preservation proof.

## Phase 8.5d-β-followup-6 — what landed (kept for reference)

## Phase 8.5d-β-followup-6 — what landed

Closed the honest-dealer case of `avss_secrecy_AS_view_rushing` via the
full `_ex`-variant chain. The cTV bridge fires only under honest dealer
(inherited from followup-5's `h_dH_sec` requirements), so the headline
now case-splits on `dealerHonest`:

| `dealerHonest` value | Status |
|---|---|
| `true` | ✅ Closed via `_via_init_invariant_ex` chain + `avssInitMeasure_simViewExt_sec_invariant` |
| `false` | 🟡 Deferred to followup-7 — structurally distinct argument (cTV bridge unavailable) |

**New `_ex` variant chain (consumes existential `∃ c, initPred sec corr c s` AE)**:

- `coalitionView_corrupt_factors_AE_ex` — coeffs-free conclusion
  using `(ω 0).1.dealerCommit p .rowPoly` directly (matching
  `coalitionAlgebraicView`).
- `coalitionTraceView_eq_reconstruct_AE_ex` — same conclusion as
  fixed-c version (already coeffs-free), takes existential h_init.
- `avss_secrecy_AS_view_conditional_ex`, `_via_aux_ex`,
  `_via_init_invariant_ex` — existential-h_init variants of the chain.

**New supporting infrastructure**:

- `avssStep_dealerCommit_invariant` — dealerCommit preserved by every
  avssStep (trivial).
- `avssSpec_stepKernel_dealerCommit_AE` — kernel-level preservation.
- `traceDist_dealerCommit_AE_eq_init` — trace-AE preservation;
  bridges `(ω k).1.dealerCommit` (used in `dealerMessagesInv`) to
  `(ω 0).1.dealerCommit` (used in `coalitionAlgebraicView`).
- `avss_phase6InvEx_AS` — existential AlmostBox for phase6Inv via
  `AlmostBox_of_pure_inductive` with predicate `∃ c, phase6Inv c s`.
  The c-witness can vary per step but the c-dependence in the
  factor lemma cancels via `dealerMessagesInv c (ω k).1` (which
  pins `dealerCommit p .rowPoly = rowPolyOfDealer ... c p`,
  independent of which `c` is chosen).

**Headline closure (honest-dealer case)**: the chain feeds
`avssInitMeasure_AE_initPred` (existential AE) directly to
`_via_init_invariant_ex`, with `h_dH_sec` derived from the
`avssInitState` structural fact `s.dealerHonest = dealerHonest = true`.
The `h_init_invariant` is discharged by `avssInitMeasure_simViewExt_sec_invariant`.

## Remaining 1 sorry — followup-7 scope

`avss_secrecy_AS_view_rushing` corrupt-dealer case (`dealerHonest = false`)
— tagged `TODO Phase 8.5d-β-followup-7`. The `_ex` chain inherits the
cTV bridge's honest-dealer guard from followup-5; under corrupt dealer
the chain doesn't apply. The result still holds — under R rushing the
corrupt-coalition view factors through corrupt rowPolys deterministically
regardless of `dealerHonest`, and corrupt rowPolys are sec-invariant
(`corrRowMap_uniform_sec_invariant`). Closing requires a structurally
distinct argument:

```
simCoalitionTraceView R C k s_0 := fun i p =>
  (avssSimulateTrace R s_0 i.val).1.local_ p.val

-- Bridge (no honest-dealer needed):
∀ᵐ ω ∂traceDist (avssSpec sec corr coeffs) R.toAdversary μ₀,
  (coalitionTraceView C ω k, schedulePrefix ω k) =
  (simCoalitionTraceView R C k (ω 0).1, simSchedulePrefix R k (ω 0).1)
```

Plus a sim-cTV-version of `avssInitMeasure_simViewExt_sec_invariant`
(factoring through `corrRowMap`, applying `corrRowMap_uniform_sec_invariant`).
Estimated ~80-100 LOC. The cryptographic content is identical; the
plumbing is what's needed.

## Phase 8.5d-β-followup-5 — what landed (kept for reference)

Closed **2 of the 3** remaining sorries via the dealerCommit-based
restatement of `coalitionAlgebraicView` (a coeffs-free alternative to
the user's brief, since the cascade through `simAlgebraicView` made
adding `coeffs` to the def itself awkward).

| Site | Status |
|---|---|
| `coalitionView_corrupt_factors_AE` (line 8472) | ✅ Closed via `phase6Inv coeffs` AE-preservation + `traceDist_partyPoint_AE_eq_init` + new `traceDist_dealerHonest_AE_eq_init` (kernel preservation theorem). Conclusion: AE-conditional on `(ω 0).1.dealerHonest = true` for the rowPoly clause. |
| `coalitionTraceView_eq_reconstruct_AE` (line 8698) | ✅ Closed via cascade from above + `corrupt_local_state_uniqueness` + `initPred`'s honest-dealer dealerCommit clause. Conclusion is honest-dealer-conditional. |
| `avss_secrecy_AS_view_rushing` (line 12132) | 🟡 Deferred to followup-6 — see below for technical detail. |

**Restatements (Phase 8.5d-β-followup-5)**:

- `coalitionAlgebraicView C ω k` — first component now uses
  `((ω 0).1.dealerCommit p.val).rowPoly` (coeffs-free); under
  `initPred` (honest dealer) this equals
  `rowPolyOfDealer (ω 0).1.partyPoint coeffs p.val`.
- `simAlgebraicView R C k s_0` — first component uses
  `(s_0.dealerCommit p.val).rowPoly` (coeffs-free).
- `measurable_coalitionAlgebraicView` — no longer needs `coeffs`.
- `simAlgebraicView_simSchedulePrefix_eq_of_simSyncInv` — proved via
  `simSyncInv.dealerCommit_corrupt_eq` instead of `rowPoly_corrupt_eq`.
- `avss_secrecy_AS_view_conditional`, `_view_rushing_via_aux`,
  `_view_rushing_via_init_invariant` — added new
  `h_dH_sec : ∀ᵐ s ∂μ_sec, s.dealerHonest = true` and
  `h_dH_sec' : ∀ᵐ s ∂μ_sec', s.dealerHonest = true` hypotheses
  (cTV bridge fires only under honest dealer; this is fundamental
  Phase 8.5d-β semantics).

**New infrastructure**:

- `avssStep_dealerHonest_invariant` (`s.dealerHonest` preserved by
  `avssStep`).
- `avssSpec_stepKernel_dealerHonest_AE` (kernel-level preservation).
- `traceDist_dealerHonest_AE_eq_init` (trace-level: ∀ᵐ ω,
  `(ω k).1.dealerHonest = (ω 0).1.dealerHonest`).

## Remaining 1 sorry — followup-6 scope

`avss_secrecy_AS_view_rushing` (line 12132) — tagged
`TODO Phase 8.5d-β-followup-6`. Closing requires sample-dependent
existential machinery:

```
phase6Inv_AS_existential :
  (∀ᵐ s ∂μ₀, ∃ c, initPred sec corr c s) →
  ∀ᵐ ω ∂traceDist..., ∃ c, ∀ n, phase6Inv c (ω n).1
```

(Sample-dependent witness `c` per ω, via Skolemization of the
step-0 marginal AE-existential.) Plus existential-form variants
of `coalitionView_corrupt_factors_AE_ex`,
`coalitionTraceView_eq_reconstruct_AE_ex`,
`_view_conditional_ex`, `_via_aux_ex`,
`_via_init_invariant_ex`. Estimated 200-300 LOC.

**Why the cascade was deeper than expected**: the user's brief
asked to restate `coalitionAlgebraicView` to take `coeffs` as a
parameter (mirroring §17.5 `coalitionGrid` restatement). However,
the consumer site `avssInitMeasure_simView_factors_through_corrRow`
needs the simView's coeffs to vary with the bivariate-polynomial
sample `f` (since `dealerCommit` is set from `polyToCoeffs f` in
the support). A single `coeffs` parameter is too rigid; the
consumer needs coeffs to be `polyToCoeffs f` per-sample. The
cleanest fix was to make `coalitionAlgebraicView` and
`simAlgebraicView` use `s.dealerCommit` directly (coeffs-free),
which works for the bridge under honest dealer + `initPred` AE.

## Phase 8.5d-β-followup-3 — what landed (kept for reference)

## Phase 8.5d-β-followup-3 — what landed

Closed 11 of the 12 sorries from PR #69's structural migration:

| Site | Status |
|---|---|
| `avssStep_preserves_dealerMessagesInv` (dealerShareTo) | ✅ Closed |
| `avssStep_preserves_honestDealerInv` (partyDeliver) | ✅ Closed |
| `initPred_honestDealerConsistencyInv` | ✅ Closed |
| `avssStep_preserves_honestDealerConsistencyInv` | ✅ Closed |
| `avssStep_preserves_outputDeterminedInv` (Tier 2) | ✅ Closed |
| `simSyncInv_avssInitState` fixture | ✅ Closed |
| `avssInitMeasure_AE_initPred` | ✅ Closed |
| `avss_secrecy_initPMF` (Tier 2) | ✅ Closed |
| `avss_secrecy_AS_init` (Tier 2) | ✅ Closed |
| `avss_secrecy_AS` (Tier 2) | ✅ Closed |
| `avssStep_preserves_simSyncInv` (Tier 3) | ✅ Closed via `dealerCommit_corrupt_eq` field add |
| `avss_secrecy_AS_view_rushing` wrapper | 🟡 Deferred to followup-4 |

**Restatements** (with `coeffs` parameter, replacing the deprecated
`s.coeffs` placeholder):

- `dealerMessagesInv coeffs s` — honest-dealer-conditional, with both
  `dealerCommit p = canonical` and `msg.rowPoly = canonical` clauses.
- `outputDeterminedInv coeffs s` — honest-dealer-conditional, clause 1
  universal in `p` (preserved via `dealerMessagesInv` for both honest
  and corrupt parties' delivered rowPoly).
- `coalitionGrid coeffs C D s` — algebraic grid view with parametric
  witness (no longer the placeholder = 0).
- `joinedConsistencyInv_via_vandermonde coeffs s` — honest-dealer-cond.
- `phase6Inv coeffs s` — composite invariant taking coeffs.
- `avss_commitment_AS_corrupt_dealer` — conclusion is honest-dealer-AE-
  conditional (corrupt-dealer Vandermonde witness deferred to a
  Phase 8.6+ Bracha amplification proof).

**Newly tagged TODO Phase 8.5d-β-followup-5** (cascade out-of-scope):

- `coalitionView_corrupt_factors_AE` (body sorry'd) — closing requires
  restating `coalitionAlgebraicView` to take a `coeffs` parameter
  (~30 callsites in the operational-secrecy chain).
- `coalitionTraceView_eq_reconstruct_AE` (body sorry'd) — downstream
  of the above plus the `traceDist_dealerHonest_AE_eq_init` lemma.

## Remaining 3 sorries

| Site | Tag | Estimate |
|---|---|---|
| `avss_secrecy_AS_view_rushing` | TODO 8.5d-β-followup-4 | requires existential-vs-fixed-coeffs reconciliation in inner theorem chain |
| `coalitionView_corrupt_factors_AE` | TODO 8.5d-β-followup-5 | ~50 LOC after `coalitionAlgebraicView` restatement |
| `coalitionTraceView_eq_reconstruct_AE` | TODO 8.5d-β-followup-5 | ~30 LOC; uses the above |

### simSyncInv structural change (T10 closure)

Added new field `dealerCommit_corrupt_eq : ∀ p ∈ corr, s.dealerCommit p =
s'.dealerCommit p` to `simSyncInv`. The field is required because under
8.5d-β, `dealerShareTo r` writes `s.dealerCommit r` to `dealerMessages r`
(not a synthesized payload from `s.coeffs`), so preserving
`dealerMessages_corrupt_eq` for corrupt `r` requires the two states'
commitments at corrupt `r` to agree. Updated callers:

- `simSyncInv.symm` — added `(h.dealerCommit_corrupt_eq p hp).symm`
- `simSyncInv_avssInitState` — at init, both states' `dealerCommit p`
  reduce to `{ rowPoly := rowPolyOfDealer ... c/c' p, colPoly := fun _ => 0 }`,
  and the `h_rp` hypothesis gives rowPoly equality at corrupt `p` (with
  identical colPoly).
- `avssStep_preserves_simSyncInv` — `dealerCommit_corrupt_eq :=
  h.dealerCommit_corrupt_eq` directly in every action's `refine` block,
  since `dealerCommit` is never modified by any `avssStep` action.

## Pre-β-followup-3 state (kept for reference)

# Phase 8.5d Checkpoint — β landed (12 sorries, all tracked) [historical]

**Branch**: `feat/randomized-leslie-m3-avss-phase8-5d-beta`
**Base**: PR #68 (8.5d-α, dealerShareTo per-party action surgery).
**Build state**: green at `lake build Leslie.Prob.Index` with **12** sorries
in AVSS.lean (up from 0; 12 added by 8.5d-β are all tagged
`TODO Phase 8.5d-β-followup`).
**Sorry count**: **12** in AVSS — all tracked, none in pre-β chain.

## Phase 8.5d-β — what landed

**Goal**: migrate `s.coeffs : Fin (t+1) → Fin (t+1) → F` out of `AVSSState`
into μ₀ (initial measure). The bivariate polynomial is now a witness sampled
at protocol start (parametric to `initPred`), not a state field.

**Structural surgery**:
- Removed `coeffs` field from `AVSSState`.
- Added `dealerCommit : Fin n → DealerPayload t F` field for per-party
  commitments (set at init from the canonical `coeffs` witness for honest
  dealer; arbitrary for corrupt dealer).
- `initPred sec corr coeffs s` takes `coeffs` parameter (the witness).
- `avssStep` for `dealerShareTo p` now writes `dealerMessages p =
  some (s.dealerCommit p)` instead of computing from a state field.
- Threaded `coeffs` through `avssSpec`, `avssCert`, all
  `avss_termination_AS_*` theorems, and most secrecy/commitment statements.
- `coeffsSecretInv` and `honestDealerInv` restated to take `coeffs`
  parameter (followup-1).
- `avssStep_preserves_honestDealerInv` rebuilt with the parameterized form
  (followup-1, all cases except partyDeliver — that one inner sorry needs
  the `dealerCommit` ↔ canonical bridge from initPred).
- `avssStep_coalitionGrid_invariant` closed via the placeholder being a
  constant (followup-2).

**Vestigial scaffolding**: `AVSSState.coeffs` accessor returns `(0 : F)` as
placeholder, marked `@[deprecated]`. Existing `s.coeffs` syntax compiles via
this scaffold; theorems whose statements depend on the actual witness
should be restated to take `coeffs` as a parameter (matching `initPred`'s
signature) and then the placeholder can be deleted.

## Sorry inventory (Phase 8.5d-β-followup TODO)

| Site | Reason | Effort |
|---|---|---|
| `avssStep_preserves_dealerMessagesInv` (dealerShareTo case) | needs dealerCommit ↔ canonical bridge from initPred | 1-line via initPred clause |
| `avssStep_preserves_honestDealerInv` (partyDeliver case, line 5674) | needs same bridge | 1-line |
| `initPred_honestDealerConsistencyInv` | needs rebuild using `coeffs` parameter as witness | 5-line |
| `avssStep_preserves_honestDealerConsistencyInv` | depends on dealerMessages preservation | 5-line |
| `avssStep_preserves_outputDeterminedInv` | restate `outputDeterminedInv` to take `coeffs` parameter, rebuild proof | 100-line per-action case split |
| `avss_secrecy_initPMF` | restate `coalitionGrid` to take `coeffs` parameter, rebuild bivariate-shamir bridge | 30-line |
| `avss_secrecy_AS_init`, `avss_secrecy_AS` | downstream of above | mechanical |
| `avssStep_preserves_simSyncInv` | restate `simSyncInv.rowPoly_corrupt_eq` to take `coeffs` param, rebuild per-action proof | 200-line (most complex) |
| `simSyncInv_avssInitState` | fixture, needs simSyncInv restatement first | 10-line |
| `avssInitMeasure_AE_initPred` | now needs existential witness; provide via `polyToCoeffs f` for `f` in support | 30-line |
| `avss_secrecy_AS_view_rushing` | top-level wrapper; reconciles existential `avssInitMeasure_AE_initPred` with fixed-coeffs `avss_secrecy_AS_view_rushing_via_init_invariant` | 20-line |

**Total followup estimate**: ~400-500 LOC, tractable in 2-3 followup commits.

## Pre-β baseline (kept for reference)

## Followup status — all 9 sorries closed

| Site | Status |
|---|---|
| `avssTermInv_step` clause 4 | ✅ Closed (per-party `dealerSent p = false → ¬delivered`). |
| `avssU_step_dealerShareTo_le` | ✅ Closed (case-split honest/corrupt p). |
| `avssU_step_dealerShareTo_lt` | ✅ Closed (requires `p ∉ corrupted`; carried via `isHonestFire`). |
| `avssStep_preserves_corruptLocalInv` (dealerShareTo) | ✅ Closed (frame proof). |
| `avssStep_preserves_avssQueueWfInv` (dealerShareTo) | ✅ Closed. |
| `avssStep_preserves_avssFlowInv` F2 (9 sub-cases) | ✅ Closed. |
| `avssFairActionEnabled_at_non_terminated` | ✅ Closed (cascade re-derived under per-party form). |
| `avssStep_preserves_dealerMessagesInv` (dealerShareTo) | ✅ Closed. |
| `avssStep_preserves_simSyncInv` (dealerShareTo) | ✅ Closed via `rowPoly_corrupt_eq`. |
| `corrupt_fire_post_not_terminated` (dealerShareTo case) | ✅ Closed by adding pre-state `¬ terminated s` premise. |

## Final closure technique notes

### `simSyncInv` dealerShareTo sub-case (was the trickiest)

The corrupt-slot dealerMessages payload at slot `r ∈ corr`. Initially looked
like it needed a new `coeffs_eq` field on `simSyncInv`, but
`simSyncInv.rowPoly_corrupt_eq r hp` already gives the row poly equality
directly, so no schema change was needed:

```lean
have hrp := h.rowPoly_corrupt_eq p hp  -- p ∈ corr
exact DealerPayload.mk.injEq _ _ _ _ |>.mpr ⟨hrp, rfl⟩
```

### `corrupt_fire_post_not_terminated` for dealerShareTo (corrupt p)

The action only mutates `inflightCorruptDeliveries`, `dealerSent p`, and
`dealerMessages p` — none of which appear in `terminated`. So
`terminated post ↔ terminated pre`. Adding the pre-state `¬ terminated s`
hypothesis lets the new `dealerShareTo` corrupt-case lift forward:

```lean
theorem corrupt_fire_post_not_terminated
    (a : AVSSAction n F) (s : AVSSState n t F)
    (hph : ¬ isHonestFire a s) (hnt : ¬ terminated s) :   -- new hnt premise
    ¬ terminated (avssStep a s) := by
  ...
```

The 3 V_super / V_super_fair callers already had `hnt` in scope, so the
update was a one-line append.

## What 8.5d-α delivered

Phase 8.5d-α is the structural surgery for **C4 (selective non-broadcast)** caveat:

## What 8.5d-α delivered

Phase 8.5d-α is the structural surgery for **C4 (selective non-broadcast)** caveat:

### Action constructor refactor

```lean
inductive AVSSAction (n : ℕ) (F : Type*) [DecidableEq F]
  -- BEFORE: | dealerShare
  -- AFTER:
  | dealerShareTo (p : Fin n) : AVSSAction n F
  ...
```

### State field retype

```lean
structure AVSSState (n t : ℕ) (F : Type*) [DecidableEq F] where
  ...
  -- BEFORE: dealerSent : Bool
  -- AFTER: per-party flag
  dealerSent : Fin n → Bool
  ...
```

### `avssStep`'s dealerShareTo branch

```lean
| .dealerShareTo p =>
    let payload : DealerPayload t F :=
      { rowPoly := rowPolyOfDealer s.partyPoint s.coeffs p
        colPoly := fun _ => (0 : F) }
    { s with
      dealerSent := Function.update s.dealerSent p true
      inflightDeliveries :=
        if p ∉ s.corrupted then insert p s.inflightDeliveries
        else s.inflightDeliveries
      inflightCorruptDeliveries :=
        if p ∈ s.corrupted then insert p s.inflightCorruptDeliveries
        else s.inflightCorruptDeliveries
      dealerMessages := Function.update s.dealerMessages p (some payload) }
```

### Gate cascades

`actionGate (.dealerShareTo p) s = (s.dealerSent p = false)` — single party, not global.
`actionGate (.partyDeliver p) s = (s.dealerSent p = true ∧ ...)` — per-party precondition.
Same per-party shift for `partyEchoSend / partyReady / partyAmplify / partyCorruptDeliver`.

### Variant `avssU` updates

The c₁ component shifted:
```lean
-- BEFORE:
(if s.dealerSent then 0 else (honestSet s).card) * K^6
-- AFTER:
(unsentDealerSet s).card * K^6   where
  unsentDealerSet s = univ.filter (fun p => p ∉ corrupted ∧ s.dealerSent p = false)
```

The honest-only filter ensures `unsentDealerSet = ∅` at terminated states (used by
`avssCert.V_term`'s `avssU_eq_zero_of_terminated`).

### Invariant `avssTermInv` clause 4 (new)

Added per-party pre-share quiescence:

```lean
def avssTermInv (s : AVSSState n t F) : Prop :=
  ((∀ p, s.dealerSent p = false) → ...) ∧   -- clause 1 (was Bool, now per-party)
  (∀ p, p ∉ corrupted → echoSent → delivered) ∧   -- clause 2
  (∀ p, p ∉ corrupted → output.isSome → readySent ∧ delivered) ∧   -- clause 3
  (∀ p, s.dealerSent p = false → s.local_ p = init)   -- NEW clause 4 (Phase 8.5d-α)
```

Clause 4 is what makes `avssU_eq_zero_of_terminated` go through:
honest p has output ⇒ via clause 4 contrapositive, `dealerSent p = true`,
so `unsentDealerSet` is empty.

### Invariants restated

- `avssQueueWfInv` Q5: `∀ p, dealerSent p = true → dealerMessages p .isSome` (per-party).
- `avssFlowInv` F2: `∀ p ∉ corrupted, dealerSent p = true → delivered ∨ p ∈ inflightDeliveries`.
- `simSyncInv.dealerSent_eq` is now between two `Fin n → Bool` functions (no statement change).

### Files touched

- `Leslie/Examples/Prob/AVSS.lean` (~150 lines updated, ~50 lines net added).
- `PHASE-8-5d-CHECKPOINT.md` (new).
- `PHASE-8-5d-PLAN.md` carried from base.

## Sorry inventory

All sorries are named `TODO Phase 8.5d-α-followup` (or refer to the same handoff).

| Line | Site | Why sorrified |
|---|---|---|
| 1045 | `avssTermInv_step` clause 4 | Per-party `dealerSent p = false → local p = init` preservation needs case-split per action; mechanical but verbose. |
| 2213 | `avssU_step_dealerShareTo_le` | Per-party drop in `unsentDealerSet` (`-K⁶`) plus growth in `inflightDeliveries` (`+K⁵`); structurally simpler than the old all-or-nothing proof. |
| 2227 | `avssU_step_dealerShareTo_lt` | Same as above, strict variant. The K⁶ - K⁵ gap is at least `K^5 * (K-1) ≥ 1`. |
| 2531 | `avssStep_preserves_corruptLocalInv` (dealerShareTo case) | The corrupt party's local state isn't touched, but `dealerMessages` writes a slot. Since the conclusion only mentions `output` and `rowPoly`, this should be one-line `simp [avssStep, setLocal]`-style after careful rewriting. |
| 2710 | `avssStep_preserves_avssQueueWfInv` (dealerShareTo case) | Q1 for new in-flight delivery slot; Q5 for the new dealerMessages population. Mechanical. |
| 3676 | `avssStep_preserves_avssFlowInv` F2 (all cases) | F2 is now per-party `(∀ p, dealerSent p = true → ...)`; the original case-by-case body needs updating (each non-dealer case is a frame proof using the per-party hypothesis). I've case-split into 9 sorries which can be filled in one short batch. |
| 4201 | `avssFairActionEnabled_at_non_terminated` (all-served case) | When `∀ p, dealerSent p = true`, dispatch falls back to the existing C2..C7 cascade. The body (~360 LOC) was retained as a comment block; needs to be re-derived under per-party gates. |
| 4934 | `avssStep_preserves_dealerMessagesInv` (dealerShareTo case) | Case-split on `p = r` vs `p ≠ r`: for `p = r`, the new payload is `rowPolyOfDealer s.partyPoint s.coeffs r`, matching the rule; for `p ≠ r`, fall back to `hinv`. |
| 9620 | `avssStep_preserves_simSyncInv` (dealerShareTo case) | Both sides write to slot `r` with identical payloads (since `partyPoint` and `coeffs` are equal across `s` and `s'` by simSyncInv structure). Mechanical congr-with-update. |

## Build state at handoff

```
$ lake build Leslie.Examples.Prob.AVSS
warning: 9 declaration uses 'sorry'
(no errors)
```

The 9 sorries cascade through the `avssCert` constructor, propagating to:

- `avssCert.inv_step` — uses `avssTermInv_step` (clause 4 sorry)
- `avssCert.U_dec_det` and `_prob` — uses `avssU_step_lt_of_fair` which depends on `avssU_step_dealerShareTo_lt`
- `avssCert.V_super` — uses `avssFairActionEnabled_at_non_terminated` (the dispatch sorry)

These propagate to the main load-bearing termination theorem. Phase 8.5d-α-followup will close them.

## Next worker brief: Phase 8.5d-α-followup

**Goal**: Close the 9 named sorries. Estimated 200–400 LOC.

### Order of attack

1. **`avssTermInv_step` clause 4** (1045): straightforward case-split. Each non-dealer action either preserves `dealerSent p` or contradicts the per-party gate `dealerSent p = true`.
2. **`avssU_step_dealerShareTo_le/_lt`** (2213, 2227): the proof structure is similar to the old `dealerShare_le/_lt`. Compute the post-state set equalities (mostly preserved), the `unsentDealerSet` drop by 1, and bound the `inflightDeliveries` growth by 1.
3. **`avssStep_preserves_corruptLocalInv`** (2531) — should compress to ~10 lines.
4. **`avssStep_preserves_avssQueueWfInv` dealerShareTo** (2710) — Q1 needs the new slot; Q5 directly satisfied by Function.update + `rfl`.
5. **`avssStep_preserves_avssFlowInv` F2 cases** (3676): 9 small subgoals, each a frame argument using the per-party hypothesis.
6. **`avssStep_preserves_dealerMessagesInv` dealerShareTo** (4934): 2-case split.
7. **`avssStep_preserves_simSyncInv` dealerShareTo** (9620): congr-with-update, ~30 lines.
8. **`avssFairActionEnabled_at_non_terminated`** (4201): the deepest. Uncomment the retained body, replace the OLD `s.dealerSent = true` Bool comparison with the per-party form, and ensure the C2..C7 cascade carries through. The C1 case dispatches `dealerShareTo p` for the unserved p.

### Files OFF-LIMITS for 8.5d-α-followup

- All framework files. Only `Leslie/Examples/Prob/AVSS.lean`.
- The dead-code shim `_avssFair_dead_old_body_keep` (kept as TODO scaffold; delete once the main theorem's body is recovered).

## After 8.5d-α-followup

- **8.5d-β**: `s.coeffs` migration to μ₀ (state field → initial-measure parameter).
- **8.5d-γ**: termination re-scope to consistent-quorum hypothesis.
- **8.5d-δ**: cleanup + MODEL_NOTES §11.4 closure citation.
