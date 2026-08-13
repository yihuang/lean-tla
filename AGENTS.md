# AGENTS.md

Guidance for AI agents working in this repository.

## What this is

A Lean 4 (v4.33.0-rc2) lake project `lean_tla` formalizing TLA-style BFT specs.
The reusable framework lives in `Bft/` (`Core`, `Rules`, `RelRank`, `Obligation`,
`Tactic`); the case studies live in `Bft/Examples/` (`Streamlet*`, `Minimmit`, …).
Mathlib, `cslib`, and `aesop` are in `.lake/packages/`.

## Build & verify

- `lake build` (whole project) or `lake build <Target>` from the repo root;
  targets are dot-paths like `Bft.Examples.StreamletProto`.
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
  them positionally: `chainNotarizedSeen_mono n f hseenmono …`,
  `voteCast_send n hinf hseen i b`, `propCast_send n L hinf hseen e b`.
  When unsure of the true parameter order, use `#check @lemma_name`.
- **`grind` closes the *monotone safety fields* of a structure invariant, but not the
  `∃`/`↔`-transport fields.** For `StreamletProto.Inv` (14 fields), after building the
  `hseenmono` / `hcvmono` / `hcpmono` / `hclockmono` helpers, `constructor <;> first
  | grind | <hard> | <bridge>` closes the 12 safety fields with `grind` (with the
  `[grind =>]`-tagged `_mono` lemmas). Hand-write only `propLongest`/`votedLongest`
  under `VoteH` (they need `notarizedBy_stable_cast_vote`) and the two bridge fields
  (`castVotes_iff`/`castProps_iff`). Without the helpers, `grind` just hits its
  term-generation limit (`gen := 8`), not the heartbeat.
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

- **Auxiliary/history variables (Lamport).** For Streamlet, the cast history is
  accumulated in monotone `castVotes : Finset (Fin n × Blk)` / `castProps : Finset (ℕ × Blk)`
  fields updated only in `Send`. The safety invariant is restated over *direct
  membership* `(i,b) ∈ s.castVotes`, and two bridge fields connect it to the
  message-derived predicates: `castVotes_iff : (i,b) ∈ s.castVotes ↔ voteCast n s i b`,
  `castProps_iff : (e,b) ∈ s.castProps ↔ propCast n L s e b`. Proving the bridge
  through the actions is the hard part — factor it into small transport lemmas
  (`voteCast_send`, `propCast_send`, `sent_eq_deliver`, `notarizedBy_stable_cast_vote`)
  rather than a mega-`simp`.
- **Do not write spec-coupled custom tactics/elaborators.** A `tla_field` elab was
  tried and rejected: it was line-neutral, coupled to the spec, and harder to read.
  Prefer explicit hand-written branches plus small generic lemmas.

## Editing

- When using the `edit` tool, make `old_string` unique and include a full line —
  a match that starts at the tail of the previous theorem can silently swallow
  that line. Read the surrounding lines first.
