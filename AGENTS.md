# AGENTS.md

Guidance for AI agents working in this repository.

## What this is

A Lean 4 (v4.33.0-rc2) lake project `lean_tla` formalizing TLA-style BFT specs.
The reusable framework lives in `Bft/` (`Core`, `Rules`, `RelRank`, `Obligation`,
`Tactic`); the case studies live in `Bft/Examples/` (`Streamlet/`, `Minimmit`, …).
Mathlib, `cslib`, and `aesop` are in `.lake/packages/`.

## Build & verify

- `lake build` (whole project) or `lake build <Target>` from the repo root;
  targets are dot-paths like `Bft.Examples.Streamlet.Proto`.
- Errors only: `lake build <Target> 2>&1 | grep -E 'error'`.
- Typecheck a scratch snippet against the project without editing it in:
  `lake env lean /tmp/chk.lean`.
- `lake build` replays cached oleans, so repeat runs are fast.

## Lean 4 gotchas (learned in the Streamlet refactor)

- **`subst` is broken inside `first | … | …` alternatives.** Under backtracking it
  surfaces as `Unknown identifier` (or a misleading `rewrite` failure in the *next*
  alternative). Replace it with `obtain ⟨rfl, rfl⟩ := Prod.mk.inj h` for a pair
  equality, or `rw [h]` for a single-component equality.
- **Section variables bind EXPLICITLY here.** `variable (n : ℕ) (Byz : …) (Δ GST f : ℕ) (L : …)`
  (parenthesized) auto-binds only the variables each declaration actually uses,
  as *explicit* parameters, in declaration order — not implicit. Call sites pass
  them positionally: `send_castVotes_mono n hsend`, `propCast_mono n L hsg hp`,
  `notarizedBy_stable_cast_vote n Byz f hcv hgt`.
  When unsure of the true parameter order, use `#check @lemma_name`.
- **`grind` closes the *monotone safety fields* of a structure invariant, but not the
  `∃`/transport fields.** For `Streamlet.Proto.Inv` (13 fields), after building the
  `hseenmono` / `hcvmono` / `hcpmono` / `hclockmono` helpers, `constructor <;> first
  | grind | <hard> | <bridge>` closes the 12 safety fields with `grind` (with the
  `[grind =>]`-tagged `_mono` lemmas). Hand-write only `propLongest`/`votedLongest`
  under `VoteH` (they need `notarizedBy_stable_cast_vote`) and the one-directional
  bridge field `sentMem` (via `sentMem_send`/`sentMem_deliver`/`sentMem_tick`).
  Without the helpers, `grind` just hits its term-generation limit (`gen := 8`),
  not the heartbeat.
- **`rcases`/`cases` choke on `Send`'s `match m.body`.** Destructuring a `Send`
  hypothesis with `-` patterns, or case-splitting `m.body` while the
  `match m.body …` update equations are in context, both fail with
  "Dependent elimination failed". Do the body case analysis once in a *clean*
  context (`send_hist` takes `bd` as a plain variable) and consume the equations
  via `rw` + the `send_hist` components.
- **Actions are grind-extractable by making their conjuncts match-free.** The
  `match m.body` history updates are buried in named helpers
  (`castVotesAdd`/`castPropsAdd`), so every `Send` conjunct is a plain equation
  and `have hcv : s'.castVotes = castVotesAdd n m.body m.src s.castVotes := by
  grind` extracts it by target type — no positional `obtain ⟨_h1, …, _h8⟩`.
  Actions and helpers carry `attribute [grind unfold]`. Two grind limitations
  to respect: it cannot *reduce* `castVotesAdd` with a concrete body (so
  branches that need the `insert`-form, e.g. `rw [hcv, Finset.mem_insert]`,
  normalize first: `simp [castVotesAdd, castPropsAdd] at hcv hcp`), and it
  chokes when a raw `Send` hyp with a *variable* body stays in context (so
  `step_inv` branches consume `hsend` via `obtain` before the `constructor
  <;> grind` — never keep a `have hsend' := hsend` copy around).
- **`first | t₁ | t₂` backtracks only on *failure*, not on "progress without closing".**
  A `simp`/`rw` alternative that rewrites the goal but leaves it open is treated as
  success and blocks later alternatives. So put `grind` first, and make every
  fallback either fully close or fail *before* rewriting (start it with an `intro`/
  `rw` that type-errors on non-matching goals).
- **`[grind =>]` is the attribute that powers `constructor <;> grind`** for
  conjunction invariants: tag your `_mono` lemmas with it. `[grind →]` is rejected
  on rules with `∀` premises (“failed to find patterns in the antecedents”).
- **A structure with a `Finset` field cannot `deriving Repr`** (drop `Repr`,
  keep `DecidableEq`). `Finset.mem_insert_self` and `Finset.filter_subset_filter`
  need explicit arguments (`m s.seen`, `(p := …)`).

## Design notes

- **Auxiliary/history variables (Lamport), one-directional.** For Streamlet, the cast
  history is accumulated in monotone `castVotes : Finset (Fin n × Blk)` /
  `castProps : Finset (Fin n × ℕ × Blk)` fields updated only in `Send`.
  `voteCast`/`propCast` are *defined as* membership in these histories
  (`propCast` reads the sender-stamped row `(L e, e, b)` — message sources are
  authenticated, so a Byzantine node's stray `.prop` body never speaks for the
  leader), and the only message-level invariant is the one direction the facts
  need: `Inv.sentMem : SentMem n s`, "every in-flight/delivered message is
  recorded in the histories". Proving it through the actions is factored into
  `send_hist` (the one body case analysis), `send_castVotes_mono`,
  `sentMem_send`, `sentMem_deliver`, `sentMem_tick` — no `↔` bridges.
- **Byzantine modeling: honest-notarization + guarded honest fields.** Faulty nodes
  run `SendB` (any well-formed message, any time — equivocation included). Every
  `Inv` field about a node's cast is guarded by `i ∉ Byz` / `L e ∉ Byz`, which
  Byzantine sends cannot disturb — *except* the length bounds (`propLongest` /
  `votedLongest`), which quantify over `NotarizedBy`: a late Byzantine vote for an
  old-epoch block could newly put it over the quorum at that epoch. Hence
  `NotarizedCast` counts **honest** cast votes only (`votersCast` filters by
  `∉ Byz`): Byzantine sends then leave every cast-side predicate unchanged
  (`hcvback`), while the delivery side (`votersSeen`/`NotarizedSeen`, Fact 2)
  still counts all delivered votes, connected by `honest_in_quorum`. Honest
  quorum is reachable: with `n = 3f+1` and `Byz.card ≤ f` there are `≥ 2f+1`
  honest voters.
- **Do not write spec-coupled custom tactics/elaborators.** A `tla_field` elab was
  tried and rejected: it was line-neutral, coupled to the spec, and harder to read.
  Prefer explicit hand-written branches plus small generic lemmas.
- **State-level theorems: factor the shared skeletons into named lemmas.** The
  liveness proofs (`longest_chain_by`, `main_liveness_lemma`, `liveness_finality`)
  only become readable after pulling their repeated steps out: `voted_eq_proposal_of_epoch`
  (`votedProposed` + `propUniq` epoch identification), `voted_le_proposal_of_earlier_epoch` /
  `proposal_le_voted_of_later_epoch` (the two `propLongest`/`votedLongest` directions), and
  `next_proposal_extends` (the adjacency used twice in Theorem 6). Keep each theorem body
  to the case split plus lemma calls.

## Editing

- When using the `edit` tool, make `old_string` unique and include a full line —
  a match that starts at the tail of the previous theorem can silently swallow
  that line. Read the surrounding lines first.
