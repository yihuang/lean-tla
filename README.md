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
- [`docs/research/`](docs/research/) — downloaded reference artifacts
  (papers, web pages, vendored sources: coq-tla, Lentil, Leslie; mathlib ZFC
  and CSLib LTS source files) with provenance in
  [`docs/research/README.md`](docs/research/README.md).

The repository is currently design-documentation only; no Lean code yet.
