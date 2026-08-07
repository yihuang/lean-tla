# North-star: relational rankings for liveness at scale

**Goal.** Formalize Kenneth L. McMillan, *Toward Liveness Proofs at Scale*
(CAV 2024, LNCS 14681, pp. 255–276,
[doi:10.1007/978-3-031-65627-9_13](https://doi.org/10.1007/978-3-031-65627-9_13))
inside TlaDsl: a **relational ranking** liveness engine that lets an
engineer prove `P ↝ Q` under justice conditions by supplying (a) a finite
relation per ranking component, (b) an invariant, and (c) scheduler
predicates — with the finiteness, conservation, reduction and scheduler
stability obligations discharged *by proof* rather than by an undecidable
SMT heuristic.

The PDF and a plain-text extraction are saved under
`docs/research/papers|web/toward-liveness-proofs-at-scale-mcmillan-cav2024.*`.

## Why this paper is the north star

The DSL already has two liveness engines:

- `wf1`/`sf1` (TLA's standard fairness rules) — one action, one invariant,
  one WF/SF fairness assumption;
- `leads_to_via_nat` — a **well-founded function** rank `f : σ → ℕ`, strong
  induction on the natural rank, used for ticket-lock/2PC/countdown.

The paper attacks exactly the gap between these and industrial liveness
proofs (its case study: the Apple generic CPU memory-subsystem model, ~1200
SLOC Ivy, 14 justice assumptions, lexicographic ranking, lemma-free proof in
280 SLOC):

1. **Ranks that need no well-founded domain.** A relational ranking is a
   *relation* `δ : σ → α → Prop` ordered by implication; "decreases" means
   "removes at least one element" (`reduces δ`), "never increases" means
   "adds no element" (`conserves δ`). Soundness comes from proving the
   relation *finite at every finite time* (Rule 5) — not from induction over
   an ordinal domain. This is the queue example's insight: `δ(τ) =
   pend(τ) ∧ τ ≤ t` is finite because each step adds at most one element,
   and the timestamp order itself need not be well-founded.
2. **Multiple justice conditions with stable schedulers** (Rule 8): a
   scheduler predicate `ψᵢ` per justice condition `rᵢ`; `ψᵢ` is stable until
   `rᵢ` fires, at least one scheduler is always on, and a scheduled `rᵢ`
   reduces `δᵢ`. This is how the DRAM-blocking and reorder-buffer lemmas
   become provable without model checking.
3. **Lexicographic combinations** (Rule 10, Theorem 1): ranks are ordered
   lexicographically, a lower rank may grow while a higher one is scheduled
   ("preempted" ranks need not be conserved), giving ordinal height up to
   `ωⁿ`. Theorem 1 (the lexicographic relational-ranking order is
   well-founded) is the paper's headline meta-theorem and the natural first
   thing to formalize verbatim.
4. **Parameterized justice conditions** (Rule 11): `∀x` over unbounded
   process/address/controller ids, handled by quantifying the scheduler
   predicates — the Apple model's unbounded cores/controllers case.

## Design notes for the Lean port

- The paper keeps verification conditions in EPR by *not* expressing
  finiteness in the logic. Lean is the opposite: we *can* express
  `Set.Finite {x | δ s x}` and prove it. So the soundness theorems are
  internalized: `relational_ranking_rule` takes finiteness of `R` (or a
  Rule-5 style finite-additions premise) as a first-class hypothesis, and
  the well-foundedness of the lexicographic order is a theorem, not an
  axiom.
- The paper's justice conditions `□◇r` are state/action predicates; in the
  DSL we take `r : Action σ` and `always (eventually (actionPred r))` (the
  action fires infinitely often) — the natural TLA reading, and what
  `WF/SF` already use.
- `reduces` and `conserves` are defined on pairs of states (pre/post), and
  the rule's step premises are per-step first-order conditions exactly like
  `wf1`'s `hstep`/`haq` — so `tla_grind`-style automation can discharge
  them and the human supplies only the ranking, invariant and schedulers.
- CSLib's `LeadsTo` bridge and `InfOcc` (`frequently_in_finite_type`
  pigeonhole) supply the finite-state ingredients for the fairness side;
  mathlib's `Set.ncard`/`Finset.ssubset_wf` supply the finite-descent core.

## Milestones (slices)

### M1 — Basic relational ranking (Rule 6) — *done*

- `Conserves`/`Reduces` (relation conservation/reduction per step);
- `finite_rank` (Rule 5): `R` finite at every time from initial-empty plus
  per-step finite additions;
- `relational_ranking_rule` (Rule 6): `□◇⟨r⟩ ⊢ p ↝ q` from invariant `φ`,
  ranking `δ`, finite envelope `R`, with C1/C2/C3 step premises proved
  under the spec `H`; soundness by strong induction on `|δ|` (finite
  descent), mirroring `leads_to_via_nat` — in
  [`TlaDsl/RelRank.lean`](../TlaDsl/RelRank.lean);
- `tla_rel_rank` tactic ([`TlaDsl/Tactic.lean`](../TlaDsl/Tactic.lean));
- example: the paper's timestamped queue (Fig. 1) in
  [`TlaDsl/Examples/TimestampedQueue.lean`](../TlaDsl/Examples/TimestampedQueue.lean)
  — `(□◇ poll) → (sent t ↝ recv t)` with `δ(τ) = pend τ ∧ τ ≤ t`,
  `φ = pend t`, `R = pend`, where the "sends add no element ≤ t" premise
  uses the increasing-order safety invariant.

### M2 — Chaining and tableau reasoning (Rule 7)

- `eventually_unfold`/`eventually_imp` — the `◇` tableau axioms;
- `relational_ranking_rule_leadsTo` (Rule 7): premises carry `◇q`, the
  justice condition is a rule parameter supplied by `D4` (while `φ` holds,
  `r` eventually fires) — in
  [`TlaDsl/RelRank.lean`](../TlaDsl/RelRank.lean);
- cascaded-queue example in
  [`TlaDsl/Examples/CascadedQueues.lean`](../TlaDsl/Examples/CascadedQueues.lean):
  `(□◇ poll₁) ∧ (□◇ poll₂) ⊢ sent₁ t ↝ recv₂ t` chained from two
  single-queue lemmas (Rule 6 instances) via Rule 7, with the coupling
  invariant `recv₁ t → sent₂ t` handing off when a poll₁ removes `t`.

### M3 — Stable schedulers (Rule 8) — *done via the Rule 10 machinery*

- the stable-scheduler machinery (`Pre`/`Req`, per-component
  conservation/reduction, scheduler stability until the justice fires,
  `∨ᵢ ψᵢ`, scheduled justice) is built into `rel_rank_lex` (Rule 10)
  rather than a standalone rule, and is exercised by the reordering
  example (M4, `n = 2`) and by the bounded-cascade example below;
- bounded-cascade / DRAM-blocking example (the paper's §3.3 bounded
  paragraph) — **done**, in
  [`TlaDsl/Examples/BoundedCascade.lean`](../TlaDsl/Examples/BoundedCascade.lean):
  queue 2 holds at most one timestamp, so `poll₁` blocks while it is
  non-empty, and the complementary schedulers
  `ψ₀ = no τ ≤ t in queue₂` / `ψ₁ = some τ ≤ t in queue₂` prioritize the
  action that unblocks the other. The Fig. 3 ranking
  `δ₀ = pend₁ ∩ {τ ≤ t}`, `δ₁ = (pend₁ ∪ queue₂) ∩ {τ ≤ t}` (a message
  moving from queue 1 to queue 2 conserves `δ₁`) gives
  `(□◇ poll₁) ∧ (□◇ poll₂) ⊢ sent₁(t) ↝ recv₂(t)`.

### M4 — Lexicographic rankings (Rule 10, Theorem 1)

- `LexLess` well-foundedness (Theorem 1), on `Fin n → σ → Finset α`, by
  induction on `n` with `WellFounded.prod_lex` +
  `Finset.ssubset_wf`;
- `rel_rank_lex` soundness (Theorem 2) with `preᵢ`/`reqᵢ` and the
  preemption clauses, in
  [`TlaDsl/RelRank.lean`](../TlaDsl/RelRank.lean): the descent produces a
  *monotone* lex order on component-cardinality vectors (`VecLexLess`),
  whose well-foundedness follows by embedding into the strict lex order on
  `Fin n → ℕ`; soundness is well-founded induction on that order, with the
  least-ever-scheduled index required forever (so higher-priority
  components are conserved and it strictly shrinks when its justice
  fires);
- remaining: a Rule-10 example — the paper's §3.4 reordering queue (two
  message classes, lexicographic rank, preempted lower component growing
  while a higher one is scheduled) — **done**, in
  [`TlaDsl/Examples/LexReordering.lean`](../TlaDsl/Examples/LexReordering.lean):
  `(□◇ poll₁A) ∧ (□◇ poll₂) ⊢ sent₁(t) ↝ recv₂(t)`, with the full
  six-clause inductive invariant and the L2 conserve/reduce/stability
  obligations discharged against `rel_rank_lex`.

  Two model-design notes from the exploration:

  1. **Unique timestamps are essential.** The paper implicitly assumes
     per-message unique timestamps; a class-`B` message sharing the tracked
     class-`A` timestamp `t` breaks `δ₁` conservation. The fix — a single
     shared, strictly-increasing `last` for both classes, with invariants
     `∀τ ∈ pendB, τ ∉ sentA` and `∀τ ∈ sentA, τ ≤ last` — makes the model
     correct.
  2. **`minArrival` made `ArrT` proofs cheap.** `ArrT` (the arrival of
     `t` in queue 2) is the deterministic *minimum* arrival; proving
     `ArrT s' t = ArrT s t` for the `δ₁` conserve clauses (when `poll₁B` /
     `poll₂` change queue 2) became one-line rewrites after introducing a
     `minArrival` helper with `minArrival_insert_ne` /
     `minArrival_erase_ne` lemmas, instead of unfolding `ArrT` and hitting
     heartbeat limits.

### M5 — Parameterized justice (Rule 11) and case-study scale

- `rel_rank_param` (Rule 11) — **theory done**, in
  [`TlaDsl/RelRank.lean`](../TlaDsl/RelRank.lean): schedulers `ψᵢ(x)` and
  justice actions `rᵢ(x)` parameterized over an unbounded set `X` (process
  ids, addresses, ...), with `preᵢ(ψ)(x) = ∃ j < i, ψⱼ(x)` and the
  per-parameter L2/P3/P4 premises. Soundness fixes the parameter `x₀` that
  schedules the least-ever-scheduled component `l` and runs the Rule 10
  descent at `(l, x₀)`;
- per-process-queue example — **done**, in
  [`TlaDsl/Examples/ParamQueue.lean`](../TlaDsl/Examples/ParamQueue.lean):
  unbounded processes, `Poll p` delivers the earliest message owned by `p`,
  fairness `∀p, □◇ Poll p`, scheduler `ψ(p) = owner t = p ∧ t ∈ pend`,
  giving `(∀p, □◇ Poll p) ⊢ sent(t) ↝ recv(t)`;
- remaining: a CPU-memory-subsystem-shaped example (unbounded
  cores/controllers, queue stages with reordering and blocking) as the DSL's
  analogue of the Apple case study; tie into CSLib LTS
  `imageFinite`/`finiteState` for the finite-state ingredients.

  *Update:* the memory-pipeline case study is **done**, in
  [`TlaDsl/Examples/MemoryPipeline.lean`](../TlaDsl/Examples/MemoryPipeline.lean):
  unbounded memory controllers with per-controller completion fairness
  (`∀c, □◇ Complete c`) plus `□◇ Retire`, and a reorder buffer that retires
  in timestamp order. It needs the *global* preemption variant of Rule 11
  (`rel_rank_param_global` in `TlaDsl/RelRank.lean`): the retire component
  is preempted whenever *any* controller still has a pending `op ≤ t`, and
  `δ₁ = done ∩ {op ≤ t}` may grow while completions are still possible. The
  proof is `t ∈ issued ↝ t ∈ retired`.

### M6 — BFT case study: Streamlet consistency

The BFT target case study (replacing the earlier Multimmit exploration) is
**Streamlet** (Chan & Shi, *Streamlet: Textbook Streamlined Blockchains*,
IACR ePrint 2020/088), chosen for being a modern, minimal protocol whose
safety argument is a *clean chain-tree statement* rather than a
message-passing invariant. Local reference material:
`docs/research/papers/streamlet-textbook-streamlined-blockchains-chan-shi-2020.pdf`
and the extracted text under `docs/research/web/`.

- **Formalization** — **done**, in
  [`TlaDsl/Examples/Streamlet.lean`](../TlaDsl/Examples/Streamlet.lean):
  the crash-fault protocol (Appendix A, `> n/2` quorums) with all nodes
  honest, modeled as the paper's abstract block tree
  (`Block.epoch`/`Block.length`/`Block.atLen`), votes per node per epoch,
  and a per-node `seen` relation recording notarized-chain lengths. The
  DSL actions (`Vote`, `Notarize`) encode Streamlet's rule: a node votes
  only for a proposal whose parent chain is a *longest* chain it has seen.
  Proved: `unique_notarization` (Lemma 10), `finality_no_conflict`
  (Lemma 11/14 — the main consistency lemma), and `consistency`
  (Theorem 12: two final chains are prefix-comparable), plus the
  temporal statement `spec_entails_consistency`.
- **The proof shape** — the whole safety argument reduces to one invariant,
  `VoteLenMono`: honest votes are for blocks of non-decreasing length
  (the longest-chain discipline). Lemma 14 is then a two-line length
  contradiction against a common voter; consistency is Lemma 14 applied to
  the shorter chain's finality witness. Timing-independence falls out: no
  delivery model appears anywhere.
- **Liveness structure** — **done**, in
  [`TlaDsl/Examples/StreamletLiveness.lean`](../TlaDsl/Examples/StreamletLiveness.lean):
  the epoch/proposal model behind the paper's Section 3.6 liveness proof.
  The state adds `cur : Epoch` and `proposed : Epoch → Option Block`;
  **epoch numbers are the timestamps** — "notarized by epoch `e`"
  (`NotarizedBy`) is a quorum that voted in epochs `≤ e`, so the paper's
  delivery facts (Fact 1/2, `2∆` epochs with `∆`-bounded delivery) are
  abstracted to an immediate-delivery predicate with no explicit time/seen
  state, and the "at that time" longest-chain conditions become plain
  epoch-bounded invariants. Proved: `proposal_growth` (Fact 3), the
  `longest_chain_by` bound, `main_liveness_lemma` (Lemma 5: no conflict at
  the third proposal's length), and `liveness_finality` (Theorem 6: five
  on-time proposals with growing lengths make `B₃` final), plus the safety
  core re-proved for the extended model. The remaining slice is the
  temporal wrapper — per-epoch leads-to progress (honest leaders propose,
  honest nodes vote) composed via `leads_to_via_nat`, which needs a
  fairness design for single-shot (non-recurring) epoch actions.

  *Update:* the **temporal wrapper is done**, still in
  `TlaDsl/Examples/StreamletLiveness.lean`. Since each `Propose`/`Vote`
  fires at most once, the DSL's recurring-action fairness (`□◇`, `WF`,
  `SF`) cannot force them; the honest-timing assumptions are therefore
  stated as per-epoch leads-to predicates (`ProposeAssumption`,
  `VoteAssumption`, `ClockAssumption`), bundled into the `H` spec. The
  theorem `liveness_spec` proves `cur = e0 ↝ FinalSome` under `H` for any
  `0 < e0`, via:
  - `epoch_step` — one epoch completes (propose → votes → clock) with the
    proposal chain-notarized;
  - `window_progress` — a strong induction on the remaining epochs
    (`k ≤ 5`), threading the `WindowDone` progress predicate;
  - `window_finality` — the final state applies Fact 3 four times and
    `liveness_finality` to conclude a block is final.
  This is the paper's Theorem 13 abstracted to epoch-granularity (the
  `2∆`/GST delivery is the immediate `NotarizedBy` predicate), and it
  exercises exactly the leads-to composition the north-star's liveness
  engines are for.
- **CSLib reuse in this slice** — the quorum-overlap argument reuses the
  `Quorum`/`quorum_overlap` pattern from `Paxos.lean`; `ChainNotarized` +
  `atLen` gives the chain/prefix machinery without a hash model. Still on
  the reuse list for the BFT target: CSLib's
  `Computability/Distributed/FLP` failure/fairness vocabulary
  (`ProcFaulty`, `ProcFair`, `AdmissibleRun`) for a Byzantine version, and
  `Semantics/FLTS` (deterministic step functions) if a leader-schedule /
  liveness layer is added.
- **DSL improvement that fell out** — the `[a|]` elaborator treated any
  identifier ending in `'` as a primed state variable, so bound variables
  like `e'` in `∀ e' : Epoch, ...` failed. Fixed in
  [`TlaDsl/Prime.lean`](../TlaDsl/Prime.lean): bound identifiers are
  resolved before the prime heuristic, so `e'`/`x'` are usable as binders
  inside bracket notation.
- **Next steps** — (a) liveness (the paper's Theorem 13: 5 consecutive
  honest-leader epochs after GST) with an explicit leader schedule
  `L : Epoch → Node` — **done**, in
  [`TlaDsl/Examples/StreamletLiveness.lean`](../TlaDsl/Examples/StreamletLiveness.lean):
  `LeaderProposeAssumption Byz L e` (the honest leader `L e ∉ Byz`
  proposes before the epoch passes), the leader-schedule spec `HL n Byz L`,
  and `liveness_spec_leader`: `HL n Byz L ⊢ cur = e0 ↝ FinalSome`, proved
  by reducing to the abstract `liveness_spec` (the honest model's liveness
  does not need to know who proposes, so the honest-leader condition is
  assumed and dropped). The `Byz` parameter is the bridge to the Byzantine
  liveness half;
  (b) a Byzantine version with `f < n/3` and an honest-node guard
  (`CorrectAct`/`[c| ... | ...]`), connecting to CSLib's FLP vocabulary;
  — **safety done**, in
  [`TlaDsl/Examples/StreamletByz.lean`](../TlaDsl/Examples/StreamletByz.lean):
  Byzantine quorums of size `> 2n/3`, the honest-overlap lemma (two
  quorums share an honest node when fewer than `n/3` are Byzantine), the
  honest-guarded `Vote`, the honest-restricted invariant (`VoteLenMonoByz`),
  and the Byzantine versions of Lemma 10 (unique notarization),
  finality-no-conflict, and Theorem 12 (two final chains are
  prefix-comparable). The liveness half (honest-leader epochs under a
  leader schedule) remains, as does the CSLib FLP vocabulary link;
  (c) an executable `FLTS`/`OmegaExecution` bridge so Streamlet's `Next`
  is also a runnable step function (the E1/E3 refinement path from the
  reviewer thread) — **done**, in
  [`TlaDsl/Examples/StreamletExec.lean`](../TlaDsl/Examples/StreamletExec.lean):
  a label-indexed step function over `Vote`/`Notarize` with the guards
  extracted from the bracket actions, and `step_spec_tr` proving every
  FLTS transition is a `[Next n]_vars`-step.

## Acceptance criteria

- zero `sorry`, zero warnings, green `lake build` at every commit;
- each rule is a *soundness theorem* over the DSL semantics (usable with
  `tla_grind`-discharged step premises), not an axiom;
- each example states a real TLA-style property (`P ↝ Q` under `□◇`-style
  justice) and the tactic turns it into ranking/scheduler obligations;
- the queue, cascade, bounded-blocking and reordering examples are all
  proof-carrying in-repo examples, mirroring the paper's Fig. 1/3/4.

## Related docs

- [`implementation-strategies.md`](implementation-strategies.md) — DSL
  roadmap; this document is the liveness-focused refinement of its phase-3
  items;
- [`tla-meta-theory.md`](tla-meta-theory.md) — reviewer points, including
  the leads-to lattice and `leads_to_via_nat` rank rule that M1 generalizes.
