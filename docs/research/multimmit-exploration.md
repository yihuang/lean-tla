# Multimmit exploration: one-round Byzantine voting in TlaDsl

Status: exploration slices complete (2026-08-04). The consensus-core slice
is formalized in [`../../TlaDsl/Examples/Minimmit.lean`](../../TlaDsl/Examples/Minimmit.lean),
the extraction-core slice (Lemma 7, positions) in
[`../../TlaDsl/Examples/Multimmit.lean`](../../TlaDsl/Examples/Multimmit.lean),
and the timed slice (Lemma 5) in
[`../../TlaDsl/Examples/MinimmitTimed.lean`](../../TlaDsl/Examples/MinimmitTimed.lean).
The extension-carry and settledness slice (Lemma 7, heights) is also in
`TlaDsl/Examples/Multimmit.lean`. What remains scoped below is the
DA-certificate chain layer itself.

## The protocol

**Multimmit** (A. Lewis-Pye, P. O'Grady, *Multimmit: Extending Blocks for
Faster Finality*, arXiv:2607.21021v2; PDF and HTML saved under `papers/` and
`web/`) extends the **Minimmit** consensus skeleton (arXiv:2508.10862) with
multi-chain block dissemination:

* **Consensus layer (Minimmit)**: view-based Byzantine SMR with a single
  round of voting per view. With `n ≥ 5f+1` processors and at most `f`
  faulty, `n-f` votes for the leader's block (an **L-notarisation**) give
  finality; every view produces either a **V-notarisation** (≥ `2f+1` votes
  for a common block, plus novotes/equivocation records totaling `n-f`
  distinct view messages) or a **nullification** (`2f+1` nullify shares),
  each of which licenses advancing to the next view.
* **Chain layer (Multimmit)**: each processor builds its own chain of
  transaction blocks with **DA-certificates** (`n-2f` threshold, pipelining
  depth `d`); leader blocks carry a chain proposal (per-chain anchor + up to
  `d` payload hashes) and reference the previous V-QC; votes are vectors
  reporting per-chain positions plus up to `e` extension payloads.
  **Tips/Tips\*** extract safe/finalised per-chain tips by rank rules
  (discard `f` / discard `3f`) with extension-carry thresholds
  (`2f+1` / unanimity), and **Ord/Emit** build the total ordering by a
  horizontal sweep.

The safety skeleton of Section 3.1/5.1 of the paper is exactly the Minimmit
notarisation argument:

| Lemma | Statement | Needs |
|---|---|---|
| 2 | a correct processor votes at most once per view | action guard |
| 3 | vote–novote exclusivity | action guard |
| 4 | L-notarisation ⇒ at most `2f` votes for other view blocks | quorum intersection `(n-f) + (2f+1) - n = f+1` |
| 5 | L-notarised view receives no nullification | message-send times (minimality argument) |
| 6 | leader chain: later `2f+1`-voted blocks extend the L-notarised block | Lemma 5 + proposal/V-QC structure |
| 7 | `Tips(W)` extends the L-QC tips; equality when settled | rank/extraction combinatorics |
| Thm 1 | logs of correct processors are compatible | Lemmas 4–8 |

## What was formalized

[`TlaDsl/Examples/Minimmit.lean`](../../TlaDsl/Examples/Minimmit.lean)
models the abstract message-history core of the consensus layer:

* **Fault model**: Byzantine processors are a `Finset Proc` constant `Byz`
  with `ValidParams n f Byz := Byz ⊆ range n ∧ Byz.card ≤ f ∧ 5f+1 ≤ n`.
  Correct processors are those outside `Byz`; a `Byzantine` action lets
  faulty processors rewrite their own vote history arbitrarily, and the
  invariants quantify only over correct processors.
* **History state**: `votes : Proc → View → Finset Block` (so
  one-vote-per-view is a cardinality invariant), `novotes`/`nullifies` as
  per-(processor, view) flags.
* **Actions**: `Vote`, `Novote`, `Nullify` (guarded by `p ∉ Byz`, no prior
  vote/novote), `Byzantine`; `Next`, `Init`, `Spec`, all in the bracket DSL.
* **Invariants** `OneVotePerView` and `VoteNovoteExcl`, proved inductive
  (`init_inv`, `next_inv`, `stutter_inv`, `spec_entails_inv`).
* **Safety theorems**:
  * `Agree`: no two different blocks both receive `n-f` votes in the same
    view (two L-quorums overlap in a correct processor since
    `2(n-f) - n = n - 2f ≥ 3f+1 > f`);
  * `Designation`: if a block receives `n-f` votes, no other block in the
    view receives `2f+1` votes (the `(n-f)`-and-`(2f+1)` sets overlap in
    `f+1 > f` members — this half needs no `5f+1` hypothesis, matching the
    paper's observation that the threshold is about the view-exit
    mechanism, not the intersection);
  * temporal statements `spec_entails_agree`, `spec_entails_designation`
    under `ValidParams`.

Build status: full `lake build` green (including the whole `TlaDsl`
library), zero `sorry`, zero warnings. The example is wired into
`TlaDsl.lean` alongside the other examples.

## What was not formalized, and why

1. **Lemma 5 (no nullification for a notarised view)** — **done** in
   `TlaDsl/Examples/MinimmitTimed.lean`. The model adds message send times:
   a message log `sent : Msg → Option Nat` plus a clock `time : Nat` that
   advances by one per action and stamps each sent message; "sent strictly
   before" is `<` on the stamps. The proof runs the paper's least-timeslot
   argument as strong induction on the nullify time: a correct voter's
   evidence set must all be stamped strictly earlier (`EvidenceBefore`,
   made inductive by folding the strict-before stamp into the evidence
   disjunction), and its correct senders are all non-voters (≤ `f`) plus at
   most `f` faulty — fewer than `2f+1`. The protocol also gains the
   faithful rules it needs: `Vote` blocks novoted/nullified processors, and
   the evidence-based `NullifyEvidence` (lines 16-19) is separate from the
   timeout nullify.
2. **Lemma 6 / Theorem 1 (leader chain, cross-view consistency)**. Needs
   proposals anchored on V-QCs, nullifications for the skipped interval,
   and the parent relation between leader blocks — i.e. Lemma 5 first.
3. **Chain layer (Multimmit-specific)**. DA-votes/DA-certificates with
   pipelining (`Lemma 1`: certified blocks are compatible), chain proposals,
   vote vectors, and the `Tips`/`Tips*`/`Ord`/`Emit` extraction functions
   (`Lemma 7`: safe extension). **Position part done** in
   `TlaDsl/Examples/Multimmit.lean`: `RankAt` (the `(j+1)`-th largest
   position), the Byzantine overlap `rank_transfer` (of the `3f+1` pool
   votes, at least `f+1` correct ones appear in the V-notarisation tally),
   `rank_ge` (V-QC rank ≥ L-QC rank), and `safe_extension_positions` (the
   V-QC tip extends the L-QC tip), together with the `Chain`/`Extends`
   block-level machinery. **Extension carry and settledness done** at the
   height level: `CountsForHeight`/`Supported`/`IsDeepest` (downward-closed
   endorsed heights, deepest supported height), `carry_reaches_final`
   (Lemma 7a's extension half: unanimity-deepened `F` is reached by the
   V-QC's `2f+1` carry — the `n−3f ≥ 2f+1` overlap again),
   `carry_bounded_settled` (Lemma 7b: under settledness
   `β + (n−|P|) ≤ f`, no height above `F` is `2f+1`-supported: correct
   votes above `F` number at most `f`), and `safe_extension_settled`
   (`Tips(W) = F`). **Remaining**: the `Ord`/`Emit` total ordering, the
   exact-threshold theorem `⌈(n+3f)/2⌉`, and the chain-layer facts the
   height abstraction elides (certified blocks compatible; DA-vote at most
   once per height). This part is *pure combinatorics over finite vote
   sets* — no time, only Finset/cardinality reasoning.
4. **Liveness** (view synchronization, `2Δ` timeouts, GST). A larger
   temporal/real-time step, orthogonal to the safety core.

## DSL feedback (what this exercise surfaced)

**Gap found and fixed this session: the bracket elaborator had no `fun`
case.** State functions inside user-written lambdas — the natural way to
write per-coordinate updates like
`novotes' = Function.update novotes p (fun w : View => novotes[p][w] ∨ w = v)`
— fell through to plain elaboration and failed. `TlaDsl/Prime.lean` now
handles typed and untyped single-binder `fun` in both the state and action
lifters (mirroring the existing `∀`/`∃` cases), and the file's
`maxHeartbeats` is raised for the LCNF compilation of the (large) `partial
def` matcher. Remaining: multi-binder `fun x y => ...` and binder patterns.

**What worked well:**
* Byzantine actors are cheap to model: a `Finset` constant + `p ∉ Byz`
  guards; the invariants quantify only over correct processors, so the
  `Byzantine` action preserves them for free.
* The `[a| ∃ p v, A p v ∨ B p v ∨ ...]` composition of named actions
  (inherited from the Paxos example) kept `Next` readable.
* Quorum-intersection arithmetic is plain mathlib
  (`Finset.card_union_add_card_inter`, `Finset.card_le_card`, `omega`);
  the three overlap lemmas are short and reusable.

**What could be better (candidate DSL features):**
1. **Multi-binder `fun` support** in the brackets — **done**: the
   elaborator now handles `fun x y : T => ...` / `fun x y => ...` (and
   beyond, by recursing on the remaining binders) in both `[p|]` and `[a|]`,
   pinned by regression tests in `TlaDsl/Examples/Brackets.lean`.
2. **A `correct`-guarded action macro** — **done**: `[c| Byz, p | body]`
   expands to `CorrectAct Byz p [a| body]` (`p ∉ Byz ∧ body`), and the
   Minimmit example's honest actions (`Vote`, `Novote`, `Nullify`) now use
   it, dropping the repeated guard from the spec text while the proofs are
   unchanged.
3. **A quorum-intersection theorem/simp library**: one lemma
   `two_quorums_meet (h1 : a ≤ Q1.card) (h2 : b ≤ Q2.card)
   (h : Q1 ∪ Q2 ⊆ range n) : a + b - n ≤ (Q1 ∩ Q2).card` would collapse the
   three overlap lemmas into one; a DSL tactic could discharge
   "there is a correct member" goals.
4. **Message-kind support for time-based arguments**: an inductive message
   type plus a `sentAt`-style component would make Lemma 5's minimal-time
   argument the next interesting proof (and a good stress test of the DSL's
   support for history variables).
5. The `Inv`-threading (`init_inv`/`next_inv`/`stutter_inv` +
   `init_invariant_stut`) is already convenient via `tla_inv`; no change
   needed for this slice.

The extraction slice (pure mathlib, no DSL brackets) additionally showed
that the library layer is pleasant for protocol combinatorics: the whole
Byzantine overlap argument is two `Finset` cardinality lemmas plus `omega`,
and the rank rules state cleanly as counting predicates. A reusable
`two_quorums_meet` lemma (item 3 above) would shorten it further.

**The timed slice's feedback** (what modelling send times taught us):
* The `sent : Msg → Option Nat` + `time` clock idiom is exactly TLA+'s
  `SendTime ∈ [Msg → Nat ∪ {⊥}]` and fits the bracket DSL well; the
  message kind becomes an inductive `Msg`, which the elaborator handles.
* Two genuine modelling gotchas surfaced, both instructive:
  (a) `tla_unfold`'s `simp` rewrites `¬ ∃ b, P b` into `∀ b, ¬ P b`
  (`not_exists`), silently changing what `intro` binds — action guards and
  invariants should be stated in the `∀` form from the start;
  (b) the "evidence sent strictly before the nullify" fact is **not**
  recoverable from a single state by timestamps alone — it must be made an
  inductive invariant, and it only stays inductive if the strict-before
  stamp lives *inside* the evidence disjunction (a separate stamp clause
  breaks when an unrelated later message re-stamps an E-member).
* The paper's within-timeslot execution (evidence arrives and the nullify
  fires in the same timeslot) is modelled faithfully by a step-based
  system where the evidence is in the pre-state pool; the least-time
  minimality becomes plain strong induction on `Nat`, with
  `Nat.strong_induction_on` doing the well-founded work.

## Protocol insights worth keeping

* The single-round-finality threshold `5f+1` is really about the
  *view-exit* mechanism: the `(n-f)`/`(2f+1)` intersection of `f+1` correct
  processors works for any `n ≥ 3f+1`; the extra `2f` headroom buys "every
  view produces a V-notarisation or a nullification" (and the extraction
  thresholds `f` vs `3f`, `2f+1` vs unanimity, are forced at `n = 5f+1`).
* Multimmit's two mechanisms (proposal-relative voting and extension
  votes) both serve the same principle: a faulty non-leader can only delay
  its *own* chain's blocks. Censorship resistance ("extend or suppress the
  whole view") is the sharpened block-inclusion theorem of Section 5.
* For the DSL: Byzantine *safety* cores are already expressible and prove
  compactly; the next hard step is time-based reasoning (Lemma 5), and the
  extraction functions (Lemma 7) are the best pure-Lean slice to take next.
