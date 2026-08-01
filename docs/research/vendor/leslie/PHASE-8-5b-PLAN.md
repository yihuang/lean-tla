# Phase 8.5b — Multi-PR Handoff Plan with Tracked Sorries

## Strategy

**Accept that one worker can't land 8.5b atomically.** The cascade is ~600-1000 LOC of cross-cutting changes spanning model surgery, cert dispatch, preservation cascades, and termination route. A single worker's context budget can carry ~200-300 LOC of careful coordination work; beyond that, output quality degrades and resets become wasteful.

**Solution**: serialize 8.5b as a chain of stacked PRs, each ≤300 LOC, each ending in a **build-green-with-tracked-sorries** state. Sorries are explicit bookmarks for the next worker. The chain shrinks the sorry count at every step and eventually reaches axiom-clean.

**Invariants per handoff**:
1. Build green — `lake build Leslie.Prob.Index` passes.
2. Sorries are **localised and named** — every `sorry` has a `-- TODO Phase 8.5b-X` comment naming the next-handoff PR responsible for closing it.
3. Sorry count is monotone non-increasing across the chain.
4. The MODEL_NOTES §12.1 row 8.5b sub-rows track who-does-what.

## PR sequence

Each PR ends with the file build-green and a documented sorry inventory.

### PR 8.5b-α — Model surgery + per-action variant lemma honest-firing premise + cert sorries

**Scope** (~300 LOC):
- Drop `p ∉ s.corrupted` from gates of `partyEchoSend`/`partyReady`/`partyAmplify` (C1).
- Drop `p ∉ s.corrupted` from `partyEchoReceive`/`partyReceiveReady` gates (C2).
- Broaden `partyEchoSend`'s broadcast filter from honest-only to `Finset.univ` (C2).
- Weaken `corruptLocalInv` from 6 clauses to 2 (`output = none ∧ delivered = false → rowPoly = none`).
- Add `isHonestFire a s : Prop` predicate for case-split dispatch.
- Update per-action `_lt` lemmas (`avssU_step_partyEchoSend_lt`, `_partyReady_lt`, `_partyAmplify_lt`) with `(hph : p ∉ s.corrupted)` premise + new gate tuple destructuring.
- Update `avssTermInv_step` preservation cases for new gate tuple shapes.
- Update `avssU_step_le` and `avssU_step_lt_of_fair` with `isHonestFire` premise.
- **Add `sorry` placeholders** in `avssCert.V_super` / `V_super_fair` / `U_dec_det` / `U_dec_prob` for the disjunct case-split (the actual dispatch is 8.5b-β's job).
- Update §12.1 row 8.5b-α → ✅ landed (with tracked-sorry note).

**Starting material**: my uncommitted WIP at `/tmp/AVSS-phase8-5b-checkpoint.patch` (394 LOC) does most of this. Apply, then add the cert sorries + fix the remaining preservation-lemma cascades in §15+ (lines 7274+, ~5 sites with mechanical gate-tuple fixes) — using sorries as bookmarks if those cascades grow too large.

**Expected state at handoff**:
- Build green with **4 sorries** in `avssCert` + possibly **5-10 sorries** in §15+ preservation lemmas (lines 7274+).
- Total sorry count: ~10-15.
- Every sorry has `-- TODO Phase 8.5b-X` comment.
- All sorries are listed in MODEL_NOTES §12.1 row 8.5b-α's "outstanding sorries" subsection.

**LOC delta**: ~300 LOC (insertions) + sorries.

**Worker brief**: pre-existing patch + clear instructions to add `sorry` rather than chase cascades. Hard cap: 300 LOC of changes; if exceeded, bisect into 8.5b-α-i / 8.5b-α-ii and let the next worker pick up.

---

### PR 8.5b-β — `avssFairActionEnabled_at_non_terminated` + cert dispatch

**Scope** (~200 LOC):
- Define new lemma `avssFairActionEnabled_at_non_terminated`:
  ```lean
  theorem avssFairActionEnabled_at_non_terminated
      (s : AVSSState n t F) (hinv : avssTermInv s)
      (hcorrupt : corruptLocalInv s) (hnt : ¬ terminated s) :
      ∃ j ∈ avssFairActions, actionGate j s
  ```
  Argument by case-split on `s.dealerSent`:
    * `dealerSent = false` → `dealerShare` is gated (it's fair, requires `dealerSent = false`).
    * `dealerSent = true` → some honest party is non-terminated; case-split on its protocol position to find a gated fair action (`partyDeliver`, `partyEchoSend`, etc.).
- Replace `avssCert.V_super` / `V_super_fair` / `U_dec_det` / `U_dec_prob` sorries with case-split-on-`isHonestFire` dispatch:
    * `isHonestFire` true (honest-fired) → call existing `avssU_step_*_lt` lemma → `Or.inl` (variant decreases).
    * `isHonestFire` false (corrupt-fired) → call `avssFairActionEnabled_at_non_terminated` → `Or.inr` (fair action enabled at post-state).
- Update §12.1 row 8.5b-β → ✅ landed.
- Verify `avssCert` axiom-clean.

**Starting material**: PR 8.5b-α's branch (build green with cert sorries). Apply the new lemma + cert dispatch.

**Expected state at handoff**:
- Build green.
- `avssCert` axiom-clean — `[propext, Classical.choice, Quot.sound]`.
- **Outstanding sorries**: the §15+ preservation cascades from 8.5b-α (if not fully closed there). 5-10 sorries remaining. Goal: 8.5b-γ closes them.

**LOC delta**: ~200 LOC. New lemma is the bulk; cert dispatch is mechanical.

**Risks**:
- The `avssFairActionEnabled_at_non_terminated` proof may bottom out in a case that genuinely doesn't have a fair action enabled — e.g., if all parties are at `delivered = true ∧ readySent = true` but none has `output.isSome` and no inflightReady remains. In that corner case, **terminated should hold** by the existing definition. Verify carefully; the lemma's correctness depends on `terminated`'s definition matching the protocol's actual quiescence states.
- If a corner case escapes, the resolution is to **strengthen `terminated`** OR add a missing fair action to `avssFairActions`. Either way, the worker reports the corner case and stops; user makes the design call.

---

### PR 8.5b-γ — §15+ preservation cascade closure

**Scope** (~150 LOC):
- Close the remaining sorries from 8.5b-α in §15+ preservation lemmas (lines 7274+ in the current state).
- These are mechanical gate-tuple destructuring fixes in places like `simSyncInv_step`, downstream invariant preservation, etc.
- Update §12.1 row 8.5b-γ → ✅ landed.

**Starting material**: PR 8.5b-β's branch (build green, axiom-clean cert). The remaining sorries are the ones at lines 7274+.

**Expected state at handoff**:
- Build green.
- **Zero AVSS-side sorries** at this point.
- All preservation lemmas axiom-clean.
- BUT: `avss_termination_AS_fair` and friends may still break — see 8.5b-δ.

**LOC delta**: ~150 LOC.

**Risks**: this is mostly mechanical but may surface unexpected callers of the old `corruptLocalInv` 6-tuple. Use sorries-as-bookmarks for any non-trivial cascade.

---

### PR 8.5b-δ — Termination AE-trajectory route switch

**Scope** (~200 LOC):
- AVSS termination uses `pi_n_AST_fair_with_progress_det` which requires `TrajectoryUMono`. Under C1+C2, `TrajectoryUMono` fails (corrupt-fired actions increase U).
- Switch the AE-trajectory hypothesis form. Two routes:
    * **Route A** — switch to `pi_n_AST_fair_with_progress_bc_of_running_min_drops` (the BC running-min route the PR #59 worker pre-identified). AVSS provides a "running min of U" trajectory witness instead of strict monotonicity.
    * **Route B** — keep `pi_n_AST_fair_with_progress_det` but weaken `TrajectoryUMono` to a disjunct form (matching `V_super`). Requires Liveness.lean modification (would re-open the framework file).
- **Recommended**: Route A. AVSS-side adaptation only; framework untouched after PR #59.
- Plumb through `_traj`, `_rushing`, `_randomised` (PR #54), `_rushing_randomised` (PR #55) variants.
- Update §12.1 row 8.5b-δ → ✅ landed.

**Starting material**: PR 8.5b-γ's branch (build green, no sorries).

**Expected state at handoff**:
- Build green.
- All AVSS termination theorems re-proven via Route A.
- AVSS-side fully closed for C1+C2.
- §11.1 (C1), §11.2 (C2) → ✅ resolved.

**LOC delta**: ~200 LOC.

**Risks**:
- Route A's preconditions may not be trivially satisfied by AVSS. Diagnose first by reading `pi_n_AST_fair_with_progress_bc_of_running_min_drops`'s signature.
- Randomised analogs (PR #54, #55) may not have a parallel `pi_n_AST_fair_with_progress_bc_of_running_min_drops_randomised`. If absent, that's a separate framework PR (defer to 9.x or use Route B for randomised).
- If neither A nor B works directly, ESCALATE — don't sorry through. The user makes the design call.

---

### PR 8.5b-ε — Verification + MODEL_NOTES finalisation

**Scope** (~50 LOC, mostly docs):
- Run `mcp__lean-lsp__lean_verify` on every load-bearing theorem; verify axiom-clean.
- Update §11.1 (C1), §11.2 (C2) to ✅ resolved.
- Update §12.1 row 8.5b master row → ✅ landed (with citations to 8.5b-α through 8.5b-δ).
- Final sanity: `lake build Leslie.Prob.Index` clean at 2700 jobs (or whatever the new count is).

**LOC delta**: ~50 LOC.

---

## Handoff protocol

1. **Each PR's branch is stacked**:
   - 8.5b-α off `feat/randomized-leslie-m3-vsuper-disjunct` (PR #59).
   - 8.5b-β off 8.5b-α's branch.
   - etc.

2. **Each PR's body** lists:
   - The build state at the start of the PR.
   - The build state at the end of the PR.
   - Outstanding sorries: count + line numbers + assigned next-handoff PR.
   - Anything the next worker needs to know.

3. **Each PR commits a `PHASE-8-5b-CHECKPOINT.md`** at the worktree root summarising:
   - Current cumulative state (sorry count, last completed handoff).
   - Next worker's exact task.
   - Any deferred design decisions awaiting user input.

4. **Sorry naming convention**:
   ```lean
   -- TODO Phase 8.5b-β: replace with isHonestFire case-split + Or.inr dispatch
   sorry
   ```
   Every sorry must name the handoff PR that's expected to close it.

5. **Re-spawning a worker**:
   - The new worker reads `PHASE-8-5b-CHECKPOINT.md` first.
   - The new worker's brief points at the specific sorries to close.
   - The new worker is told: "If you can't close all sorries, push what you have with new sorries documented; the next worker picks up."

## Risks at the plan level

1. **Cumulative LOC could exceed estimates.** If 8.5b-α's actual delta is 400+ LOC instead of 300, bisect it. The plan should be a guide, not a contract.

2. **Sorries may compound.** If a worker introduces sorries faster than they close, the chain doesn't converge. Mitigation: each worker brief includes a hard rule — "your sorry budget is N; exceeding it requires escalation."

3. **The cert dispatch in 8.5b-β may have a corner case.** The recommended response: escalate to user, don't sorry through architectural decisions.

4. **Termination route switch in 8.5b-δ may need a new framework lemma.** If the BC running-min route's preconditions don't fit AVSS, the worker reports and stops. User decides whether to add framework support (Route B) or accept partial closure.

## Decision points needing user input

- **Plan approval** — does this 5-PR sequence look right?
- **Sorry budget per PR** — I propose ≤15 sorries at the 8.5b-α handoff; tighten/loosen?
- **Handoff PR base** — stacked PRs (each based on the previous) or all based on PR #59 with cherry-picks? Stacked is cleaner.
- **Use of /tmp checkpoint** — should I commit my current 176/-112 WIP as the foundation for 8.5b-α's worker, or have the worker re-derive from scratch with the patch as a reference?

## My current uncommitted work

The 176/-112 LOC of changes in `/Users/rupak/.worktrees/leslie/AVSS-phase8-5b-proper/Leslie/Examples/Prob/AVSS.lean` (saved at `/tmp/AVSS-phase8-5b-checkpoint.patch`) constitutes most of 8.5b-α's model surgery + variant honest-firing premise work. **Recommendation**: commit this as the foundation of 8.5b-α (with cert sorries added), then dispatch the 8.5b-α worker only for the §15+ preservation cascade fixes. That saves an entire worker session.
