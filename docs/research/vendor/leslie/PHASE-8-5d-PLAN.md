# Phase 8.5d — `dealerShareTo` (C4) + `s.coeffs` migration + termination re-scope

## Strategy

Same handoff-with-sorries strategy as Phase 8.5b worked. Sequence of stacked PRs, each ≤300 LOC, each ending build-green-with-tracked-sorries (or fully closed).

## Sequence

### PR 8.5d-α — `dealerShareTo` action surgery (C4)

Replace `dealerShare` (single all-or-nothing emit) with `dealerShareTo (p : Fin n)` (per-party emit). Adversary chooses firing order; corrupt dealers can selectively short-share.

**Changes**:
- `AVSSAction`: rename `dealerShare → dealerShareTo (p : Fin n)`.
- `actionGate`: gate is `s.dealerSent p = false ∧ ...`.
- `avssStep`: effect is "populate `s.dealerMessages p` for this single party + flag `s.dealerSent p = true`".
- `s.dealerSent : Bool` → `s.dealerSent : Fin n → Bool` (per-party flag).
- Or: introduce a separate per-party `dealerSentTo : Finset (Fin n)`.
- `avssFairActions`: `dealerShareTo p ∈ avssFairActions ↔ honestDealer ∧ p ∉ corrupted`. (For honest dealer + honest p, fair-required.)
- Update all callers of `s.dealerSent` (which is now per-party).
- Update `terminated` if it includes `dealerSent` quiescence.

Cascade through invariants:
- `avssTermInv` — `dealerSent = true → ...` becomes `dealerSent p = true → ...` for each affected clause.
- `avssQueueWfInv`, `avssFreshInv`, `avssFlowInv` — adapt.
- Variant: `unsentDealerSet := {p : ¬dealerSent p}` (new), or extend an existing component.

**LOC estimate**: ~300-400 LOC. Sorry-handoff if needed.

### PR 8.5d-β — `s.coeffs` migration to μ₀

Move `s.coeffs : Fin (t+1) → Fin (t+1) → F` from state to initial measure. The bivariate polynomial that an honest dealer uses is a witness sampled from μ₀, not a state field.

**Changes**:
- Remove `coeffs : Fin (t+1) → Fin (t+1) → F` from `AVSSState`.
- Update `initPred` to take a `coeffs` parameter (or via `avssInitMeasure`).
- Update theorems whose statement mentioned `s.coeffs` to use existential-witness form (which already exists from PRs #43, #45, #49).
- Delete or rephrase theorems from PR #47 that referenced `s.coeffs` directly (`avss_correctness_AS_randomised`, `avss_commitment_AS_randomised`).

**LOC estimate**: ~200-300 LOC. Lots of call-site updates.

### PR 8.5d-γ — Termination re-scope to consistent-quorum hypothesis

Currently `avss_termination_AS_fair` is unconditional under fair scheduling (modulo BC running-min from 8.5b-δ). Under the new model with C4 (selective non-broadcast), termination becomes conditional:

```lean
theorem avss_termination_AS_fair
    ...
    (h_consistent_quorum : ... ≥ n - t honest parties receive consistent shares ...)
    : AlmostDiamond ... terminated
```

The `h_consistent_quorum` is the conditional CR statement.

**Changes**:
- Identify the right hypothesis form (trajectory-level for fair-AST composition).
- Update `avss_termination_AS_fair` + `_traj` + `_rushing` + `_randomised` (PR #54) + `_rushing_randomised` (PR #55) signatures.

**LOC estimate**: ~200 LOC.

### PR 8.5d-δ — Cleanup + MODEL_NOTES

Final verification, axiom-clean check, MODEL_NOTES §11.4 (C4) closure citation, §12.1 row 8.5d → ✅.

**LOC estimate**: ~50 LOC docs.

## Total estimate

~750-1000 LOC, 4 stacked PRs.

## Handoff protocol

Same as 8.5b: each PR ends build-green with named sorries; next PR closes them. Sorries named `TODO Phase 8.5d-X`. `PHASE-8-5d-CHECKPOINT.md` tracks state.
