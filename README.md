# lean-tla

Exploration workspace for a **deep embedding of TLA+ in Lean 4**, with
Isabelle/TLA+ as the reference and mathlib/CSLib as leverage.

- [`docs/design-space.md`](docs/design-space.md) — the design-space
  exploration: embedding depth, value universe/typing, syntax/binding,
  stuttering semantics, proof architecture, mathlib/CSLib leverage, and a
  recommended layered architecture with a phased plan.
- [`docs/deep-vs-dsl.md`](docs/deep-vs-dsl.md) — the strategic question:
  deep-embed TLA+, or design a native TLA-flavored DSL in Lean? Includes a
  cost/benefit comparison, goal profiles, a decision framework, and the
  recommended "DSL + conformance oracle" synthesis.
- [`docs/implementation-strategies.md`](docs/implementation-strategies.md) —
  how to actually build it: gap analysis of Leslie/Lentil/coq-tla, the key
  design decisions (prime notation, lifting, tactics, model checking,
  composition), a priority-ordered improvement list, and a phased roadmap
  with UX acceptance criteria.
- [`docs/north-star.md`](docs/north-star.md) — the north-star goal:
  formalize McMillan's *relational rankings* (CAV 2024, "Toward Liveness
  Proofs at Scale") as the DSL's liveness engine — finite relations ordered
  by implication, stable schedulers, lexicographic combination — with a
  milestone roadmap (M1, the basic rule + queue example, is done).
- [`docs/research/`](docs/research/) — downloaded reference artifacts
  (papers, web pages, vendored sources: coq-tla, Lentil, Leslie; mathlib ZFC
  and CSLib LTS source files) with provenance in
  [`docs/research/README.md`](docs/research/README.md).
- [`docs/ux-notes.md`](docs/ux-notes.md) — notes from the first working
  prototype (the "feel the water" slice): what the notation and proof UX
  actually felt like, what broke, and what to prototype next.
- [`docs/tla-meta-theory.md`](docs/tla-meta-theory.md) — the current focus:
  TLA meta-theory first (stuttering equivalence, quotient characterization,
  rule soundness), the theorem list, and how it feeds the DSL.

## Prototype status

The working prototype lives in [`TlaDsl/`](TlaDsl/) and builds with
`lake build`: TLA-flavored semantics (behaviors, `□`/`◇`/`↝`, `[A]_v`,
`WF`/`SF`), pseudocode notation (`[p| ...]`, `[a| x' = x + 1 ∧ ...]`,
`[t| ...]`, implicit lifting), the `tla_var` command for declaring
variables, an invariant tactic, and machine-checked examples (counter,
refinement, ticket-lock liveness, two-process mutex with full-chain
liveness). Mathlib is a dependency (toolchain `v4.33.0-rc1`, matching
mathlib's pin) and `tla_grind` provides SMT-style automation.
The relational-ranking liveness engine
([`TlaDsl/RelRank.lean`](TlaDsl/RelRank.lean)) proves the paper's Rule 6
(finite-descent leads-to) and Theorem 1 (lexicographic rankings are
well-founded), with the timestamped-queue example
([`TlaDsl/Examples/TimestampedQueue.lean`](TlaDsl/Examples/TimestampedQueue.lean)).
