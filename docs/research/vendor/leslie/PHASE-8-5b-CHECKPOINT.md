# Phase 8.5b Checkpoint — ✅ COMPLETE

**Branch**: `feat/randomized-leslie-m3-avss-phase8-5b-eps-remove-udec-prob`
**Base**: PR #66 (8.5c).
**Build state**: green at 2699 jobs.
**Sorry count**: **0** (chain fully closed).

## All load-bearing AVSS theorems axiom-clean

Verified via `mcp__lean-lsp__lean_verify` — all return `[propext, Classical.choice, Quot.sound]` only:

- `avss_correctness_AS_existential` ✅
- `avss_commitment_AS_corrupt_dealer` ✅
- `avss_secrecy_AS_view_rushing` ✅
- `avss_termination_AS_fair` ✅
- `avssCert` ✅

## What this PR (8.5b-ε) delivered

Removed the now-vestigial `U_dec_prob` field from `FairASTCertificate` and `ASTCertificate` in `Leslie/Prob/Liveness.lean`:

- After PR #65's switch to `pi_n_AST_fair_with_progress_bc_of_running_min_drops` (BC running-min route), no active soundness proof in the framework consumes `cert.U_dec_prob`.
- All 3 mentions of `cert.U_dec_prob` in Liveness.lean are in docstrings/comments documenting future probabilistic-descent plans (see lines 335, 871, 1492), never in proof bodies.
- Removed the field from 5 cert constructors:
  - `Leslie.Examples.Prob.AVSS.avssCert`
  - `Leslie.Examples.Prob.AVSSAbstract.avssCert`
  - `Leslie.Examples.Prob.BenOrAsync.boCert`
  - `Leslie.Examples.Prob.CommonCoin.ccCert`
  - `Leslie.Examples.Prob.RandomWalker1D.rwCert`

## Phase 8.5b chain summary

| PR | What it delivered | Sorries |
|---|---|---|
| #60 (8.5b-α) | C1+C2 model surgery + variant honest-firing premise + cert sorries | 0 → 11 |
| #61 (8.5b-β) | Cert dispatch + `avssFairActionEnabled_at_non_terminated` | 11 → 13 |
| #62 (8.5b-γ) | Freshness invariants + `actionGate_iff` + `simSyncInv` preservation | 13 → 4 |
| #63 (8.5b-γ-followup) | C5/C7 stuck cases via flow + threshold invariants | 4 → 3 |
| #64 (8.5b-γ-followup-2) | F4 preservation via per-pair `inflightReady` tokens | 3 → 2 |
| #65 (8.5b-δ) | BC running-min termination route switch (`U_dec_prob` becomes vestigial) | 2 → 2 (1 vestigial) |
| #66 (8.5c) | `coalitionView_corrupt_factors_AE` weakening + secrecy chain cascade | 2 → 1 (vestigial only) |
| **#NN (8.5b-ε, this PR)** | Remove vestigial `U_dec_prob` field from `FairASTCertificate` + `ASTCertificate` | **1 → 0** |

Total chain: **8 PRs, ~3000 LOC, 0 sorries**.

## What's resolved

- §11.1 (C1 — corrupt parties cannot send echoes/readys/amplify) ✅
- §11.2 (C2 — honest broadcasts only to honest receivers) ✅
- §11.4 (C4 — selective non-broadcast not modelled) — partially; `dealerShareTo` not yet introduced (would be 8.5d, deferred).
- All AVSS classical theorems (correctness, commitment, secrecy, termination) re-proven under the C1+C2 model with the BC running-min termination route.

## What remains for full Phase 8 closure

- **8.5d** — `dealerShareTo` (selective non-broadcast for C4) + `s.coeffs` migration to μ₀.
- **8.6** — operational secrecy under full adversary (row+column secrecy, deferred since SyncVSS).
- **8.7** — adapter retirement / cleanup.
- **8.8** — MODEL_NOTES rewrite reflecting the post-Phase-8 state.

These were originally part of the master 8.5 plan; Phase 8.5b focused on C1+C2 closure, with C4 (8.5d) intentionally deferred.
