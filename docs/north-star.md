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

### M3 — Stable schedulers (Rule 8)

- `rel_rank_scheduler` soundness: multiple `δᵢ`/`ψᵢ`/`rᵢ`, stability,
  `∨ᵢ ψᵢ`, per-component conservation/reduction; proof following the
  paper's Theorem 3 (reduce to Rule 6/10 machinery);
- bounded-cascade / DRAM-blocking example with priority scheduler.

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
  while a higher one is scheduled). *Exploration note (2026-08-05):* a
  first attempt at this example exposed a genuine model-design subtlety the
  paper glosses over — in a flat timestamp model, a class-`B` message may
  share the tracked timestamp `t` with a class-`A` message, and moving it
  to queue 2 adds a second arrival of `t`, which breaks conservation of
  `δ₁ = arrivals ≤ ta(t)`. The paper's scenario implicitly assumes
  per-message unique timestamps. The fix is to make the model timestamps
  globally unique (a single shared, strictly-increasing `last` for both
  classes, with `sentA ∩ sentB = ∅` as an invariant) or to define
  `ArrT` as the *minimum* arrival of `t` (so a later duplicate arrival is
  outside `δ₁`). Either fix is a clean next slice; the Rule 10 soundness
  engine itself is unaffected.

### M5 — Parameterized justice (Rule 11) and case-study scale

- `∀x` schedulers/justice over unbounded ids; auxiliary-variable witnesses
  for quantifier alternations (the paper's §4.2);
- a CPU-memory-subsystem-shaped example (unbounded cores/controllers, queue
  stages with reordering and blocking) as the DSL's analogue of the Apple
  case study; tie into CSLib LTS `imageFinite`/`finiteState` for the
  finite-state ingredients.

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
