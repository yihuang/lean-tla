# Implementation strategies for a TLA-flavored Lean DSL

*Companion to [`deep-vs-dsl.md`](deep-vs-dsl.md) and
[`design-space.md`](design-space.md). Confirmed direction from the decision
framework: a **native, typed, TLA-flavored DSL in Lean 4**, with **engineer
UX as the top priority**. No `.tla` import, no TLA+ meta-theory. This document
analyzes what exists (Leslie, Lentil, coq-tla), what is missing for that goal,
and lays out implementation strategies and a prioritized roadmap.*

## 1. Where the existing projects stand (gap analysis)

### 1.1 What is already good

**Leslie** (Apache-2.0) is the closest thing to the target and the main base
to build on:

- semantic core: `exec σ := Nat → σ`, `pred σ := exec σ → Prop`, lifted
  connectives, `always`/`eventually`/`later`, `leads_to`, `weak_fairness`,
  `until` — all defined, with `[simp]`-style normal forms (`tlasimp`) and
  semantic proofs of the standard rules (`leads_to_trans`, `leads_to_chain`,
  `wf1`, `init_invariant`...);
- notation: a `tlafml` syntax category with macros (`□`, `◇`, `◯`, `↝`,
  `𝑈`, `𝒲ℱ`, binders, big operators) and delaborators;
- a real verification corpus: counters, 2PC, Paxos, cache-coherence, VR
  view-change, Heard-Of round models with cutoff theorems — usable as the
  test suite for anything we build;
- specification layer: `Spec` (init/next/fair), `GatedAction`/`ActionSpec`
  (multi-action, gated, fair), refinement mappings and Abadi–Lamport safety
  theorems, forward simulation relations, assume-guarantee, CIVL layers;
- tactic patterns: `tla_unfold_simp`, `tla_nontemporal_simp`,
  `@[tla_derive]`, `#tla_lift`.

**Lentil** (Apache-2.0) contributes the proof-UX experiment: an Iris-style
**proof mode** for TLA (`tla_start`, `tla_have`, `tla_suffices`, `tla_apply`,
`tla_rcases`, `tla_simp`, ...) with a named temporal context
(`Entails hyps fml`), PTL normalization tactics, and goal display
infrastructure.

**coq-tla** (no license file — treat as reference-only) has rule sets Leslie
never ported: strong fairness (`sf.v`), until (`until.v`), safety (`safety.v`),
and Ltac automation (`automation.v`).

### 1.2 What is missing or wrong for the UX-first goal

| Gap | Where | Why it matters | Evidence |
|---|---|---|---|
| No `Unchanged v` / `[A]_v` / `⟨A⟩_v` | Leslie | Stuttering is modeled as whole-state equality (`next ∨ s = s'`), which forbids changes to *unobserved* variables and is not TLA's per-variable `[A]_v`; breaks abstraction and composition | `Spec.safety_stutter`, `AssumeGuarantee.lean:50` |
| No semantic stuttering (`Sim`, `stutinv`) | Leslie, Lentil | Cannot state or prove that DSL operators are stuttering invariant; refinement theorems rest on the `s = s'` sugar instead of the real notion | grep for `Sim|stut` |
| No `\EE` (flexible-variable hiding) | Leslie, Lentil, coq-tla | Parallel composition (`Spec1 ∥ Spec2 := ∃ internal vars, Spec1 ∧ Spec2`) and refinement with auxiliary variables are inexpressible | — |
| No strong fairness `SF` | Leslie | Only `𝒲ℱ` exists; liveness beyond weak fairness impossible | `Spec.formula`, `Rules/WF.lean` |
| No prime syntax (`x'`, `x$`, `Unchanged x`) | all | The single most TLA-feeling surface: actions written as `fun s s' => s'.x = s.x + 1` instead of `x' = x + 1` | examples |
| Notation friction | Leslie | State predicates need explicit `⌜ ⌝` lifts; no `∃ x ∈ S`, `CHOOSE`, `[A]_v`, `IF` sugar; no ASCII fallback; separate `tlafml` category feels like a second language | `Basic.lean` macro rules |
| No high-level proof tactics | Leslie (thin: unfold/simp only), Lentil (proof mode, but not task-level) | Engineer flow "prove invariant / prove liveness" is manual: `init_invariant` must be applied by hand, then goals split by hand | `Rules/StatePred.lean` |
| No model-checking UX | Leslie has random sim + a *plan* for a tactic | TLC-style quick validation before/while proving is a core engineer loop | `Simulate.lean`, `docs/mc-tactic-plan.md` |
| No task-level liveness tactics | both | `wf1` exists as a theorem; no tactic that takes rank functions / fairness and discharges the boilerplate | `Rules/WF.lean` |
| Two diverging codebases to reconcile | Leslie vs Lentil | Same semantics, different UX layers; both thin in different places | — |
| Toolchain/dependency hygiene | Leslie pins Lean 4.27; Lentil similar | mathlib churn management needs a policy, not an accident | `lean-toolchain` |

### 1.3 CSLib: the foundations layer we adopt

**CSLib** (github.com/leanprover/cslib, same toolchain pin as mathlib main,
Apache-2.0) is building exactly the ω-semantics layer this project needs, so
we depend on it directly instead of re-implementing:

- `Cslib.ωSequence α` (a `ℕ → α` wrapper) is the carrier of
  `Tla.Behavior` (`TlaDsl/Basic.lean`). We inherit `head`/`tail`/`drop`/
  `take`/`extract`/`const`/`map`/`flatten` plus their simp lemmas
  (`get_drop`, `drop_drop`, ...), which is exactly the block-prefix
  machinery the `SimFull` run-compression proofs need.
- `ωSequence.Temporal` (`Step`, `LeadsTo`, frequently-lemmas) overlaps our
  `Rules.lean` leads-to laws; `ωSequence.InfOcc` is the "enabled infinitely
  often" predicate behind strong fairness — `sf1` is now bridgeable to the
  `∃ᶠ` filter vocabulary (`sf_enabled_frequently_iff`, `sf1_frequently`).
- `LTS`/`OmegaExecution`/`HasTau`/`TraceEq` are the labeled-transition layer
  a future refinement-through-τ story can build on.

Adoption notes:
- cslib main pins mathlib to its own rev; Lake kept our newer mathlib
  (`ae0d973d`, 2026-08-02) and compiled cslib cleanly against it. If a future
  `lake update` forces a mathlib rev move, expect one rebuild.
- The one behavioral difference that bit us: cslib's `drop n s = fun i =>
  s (i + n)` (ours was `e (n + i)`), and Lean's `Nat.add` reduces `n + 0`
  but not `0 + n`. Proofs that previously closed by `rfl`/`exact` now need a
  `simp` (which carries `Nat.add_zero`/`Nat.zero_add`/`get_drop`).

## 2. Implementation strategies: the big decisions

### D1. Fork Leslie vs. new package

- **Fork Leslie**: inherits examples and rules, but it is a research monolith
  (CIVL, Heard-Of, cutoff, Rust verification), its core stuttering semantics
  is the thing we need to *replace*, and the maintainer's priorities differ
  from a UX-first product.
- **New package** (this repo): port the semantic core, rule patterns,
  notation approach, and examples from Leslie (Apache-2.0, attribution
  required), fix the semantics from day one, and own the UX.

**Recommendation: new package**, structured as a library with the examples as
the test corpus. Do not fork; do not copy coq-tla (no license). Copying from
Leslie/Lentil is fine with attribution.

### D2. The semantics core: how deep, how visible

The DSL is shallow (formulas are Lean predicates), but it should implement
TLA's *semantic* operators, not sugar:

- `Unchanged v := fun s s' => v s' = v s`
- `⟨A⟩_v := A ∧ v' ≠ v`, `[A]_v := A ∨ Unchanged v` (as actions)
- `□[A]_v`, `◇`, `P ↝ Q`, `WF_v(A) := □(□Enabled ⟨A⟩_v ⇒ ◇⟨A⟩_v)`,
  `SF_v(A) := □(□◇Enabled ⟨A⟩_v ⇒ ◇⟨A⟩_v)`
- semantic stuttering: `Sim` on behaviors + `stutinv`/`nstutinv` predicates,
  with preservation lemmas for every operator (the AFP TLA\* pattern,
  ported to Lean) and an optional `StutQuot := Quot Sim` used by the
  refinement layer.

**Visibility strategy:** engineers write `[Next]_vars` and refinement
theorems; the quotient and stuttering-invariance lemmas live in the library
and are used *by* tactics and refinement machinery, not demanded of users.
This is "deep enough" semantics with shallow UX.

### D3. States, variables, and the prime notation

Two candidate state models:

- **A. Records**: `structure S where x : Nat; y : Bool; pc : Status`.
  Variables are field projections; `simp`/`ext`/automation work on real Lean
  fields; this is the engineering-friendly choice.
- **B. State-function style** (`σ → α`): matches TLA semantics and makes
  `\EE`/refinement cleaner, but every variable is an opaque function —
  worse automation and worse errors.

**Recommendation: records**, with the action notation built on top. The
prime-notation design is the key UX bet:

```lean
-- target UX (sketch):
def Next : Action S := [a| x' = x + 1 ∧ y' = y]          -- or ⟨...⟩
def Spec : Pred S := [t| Init ∧ □ [Next]_vars]
```

Implementation options: (i) a dedicated `action` syntax category whose macro
rewrites `x` → `s.x`, `x'` → `s'.x` inside a fixed pre/post pair (the TLA+
parser trick, now in Lean macros); (ii) a `StatePair` structure with notation
`x'` defined via projections and a `[simp]`-friendly semantics; (iii) plain
Lean (no sugar). **Prototype (i) and (ii) on the counter/mutex examples and
pick by feel** — this is the single biggest UX decision in the project.

`Unchanged x`, `[Next]_vars` (with `vars` a list of state functions), and
`Enabled` come along with the same layer.

### D4. Formula notation: one language or two

Options:

- **Leslie-style**: a separate `tlafml` syntax category with explicit lifts
  (`⌜ p ⌝`, `⟨ a ⟩`). Predictable, but two-language friction and noisy goals.
- **Scoped native notation + coercion-lifting**: TLA operators are ordinary
  Lean functions with notation in a `TLA` scope (`□ P`, `P ↝ Q`, `WF a`);
  state predicates `σ → Prop` auto-lift to `pred σ` via a `Coe` instance
  where the elaborator allows. Best-looking surface; risks ambiguous coercions
  (`σ → Prop` has existing `CoeFun` meaning).
- **Implicit-lifting elaborator** (Isabelle `Intensional`-style): automatic
  lifting of state/action level terms in modal contexts. Powerful; highest
  complexity and worst failure modes.

**Recommendation: start with (Leslie-style) explicit lifts plus scoped
notation for the temporal operators**, and add coercion-lifting behind a
flag; measure on examples. Keep ASCII aliases (`[]`, `<>`, `ENABLED`, `WF`,
`SF`, `/\`, `\/`) — engineers without unicode keyboards are real users.

### D5. Proof UX: tactics over proof mode

The engineer loop for TLA-style verification is small and deserves
task-level tactics:

1. **Invariant induction**: `tla_inv` — given `Init`, `Next`, `Inv`,
   generates `init ⇒ inv` and `Next ∧ inv ⇒ inv'` goals, discharging with
   `grind`/`omega` where possible (Leslie's `init_invariant` is the lemma
   underneath; the tactic is the UX).
2. **Liveness (implemented 2026-08-02)**: `tla_wf1`/`tla_sf1` — apply the
   semantically proved `wf1`/`sf1` rules to a
   `Init ∧ □[N]_v ∧ WF_v(A) ⊢ P ↝ Q` goal, discharging the step and
   angle-step obligations with `tla_grind` and leaving the enabledness
   witness (which `grind` cannot construct — the one creative step). The
   TicketLock liveness proof is now `tla_wf1; exact henable`; the Mutex's
   four WF1 theorems and TwoPhase's two are the same shape.
3. **Leads-to choreography (implemented 2026-08-02)**: `tla_leads_to` —
   closes `P ↝ Q` goals by assumption, disjunction on the left, or
   transitivity through a chain of leads-to facts in context (right-recursive
   so arbitrarily long chains work; the left premise must be an assumption,
   which also bounds the search). The Mutex chains (`lB2`, `lCq`, `lDq`, the
   TwoProcess/TwoPhase finals) are now one tactic call each.
   `tla_leads_to_cases` applies the invariant-guided case split
   (`leads_to_cases`) — the Mutex `turn1Chain` case analysis is now a single
   call.
   `tla_sf1` is demoed on a strong-fairness example
   (`TlaDsl/Examples/StrongFair.lean`): `SF_v(Set) ⊢ p ↝ q` where `Set`
   marks a flag; the example documents why the enablement premise is
   immediate under a stuttering semantics (the standard spec-relative
   `p ∧ [N]_v ⇒ ◇ Enabled ⟨A⟩_v` SF1 is the tracked refinement).
4. **Fallback**: `tla_unfold` + `grind` for anything structural.

Lentil's full proof mode is a *second* UX layer; keep it as a candidate but
do not build it first — task-level tactics give 90% of the value for 20% of
the code, and Lean's native `have`/`obtain` already cover the interactive
case.

### D6. Model checking / validation UX

- **Implemented (2026-08-02)**: `TlaDsl/ModelCheck.lean` —
  `mcInvariant` computes the reachable-state fixpoint for a finite state
  type (saturating within `Fintype.card` iterations) and `mcInvariant_sound`
  turns a successful `native_decide` check into a machine-checked invariant
  theorem over all behaviors; `mcEntails` gives the DSL form
  (`Init ∧ □[Next]_v ⊢ □Inv`). Example: `TlaDsl/Examples/ModelCheck.lean`
  proves mutual exclusion for a finite two-process mutex by `native_decide`
  alone. Counterexample extraction (`mcTrace`, given an explicit state
  enumeration — Finset→List is noncomputable in this mathlib) prints the
  failing trace, and bounded liveness (`mcLeadsTo` + `mcLeadsTo_sound`) checks
  `P ↝ Q` via the inevitability fixpoint (`goodN`, computed as an
  accumulator so evaluation is linear in the state count; a naive nested-∀
  filter formulation blows up exponentially under evaluation). Design notes:
  decidable predicates over concrete finite specs need explicit
  `DecidablePred`/`DecidableRel` instances (`unfold ...; infer_instance`);
  `v` must be the full state for true stuttering; and liveness in DSL form
  (`mcEntailsLeadsTo`) requires fairness — under `□[Next]_v` an infinite
  stutter is a legal behavior, so `P ↝ Q` without fairness is false whenever
  `P` can stutter forever (the plain-`next` check is the fairness-free case).
- Keep random trace simulation (Leslie's `Simulate`), add counterexample
  printing.
- Later: bounded invariant checking as a test harness (`#eval` runs of the
  spec on finite prefixes), mirroring TLC's role in the engineer loop.

### D7. Composition, refinement, `\EE`

- Refinement mappings and forward simulations exist in Leslie; re-prove them
  over the corrected `[A]_v` semantics.
- `\EE` (hiding) is the missing composition primitive. Typed formulation to
  prototype: for `F : pred (σ × τ)` (state extended with a hidden variable),
  `hide F : pred σ := ∃ f : σ → τ, ...` with behaviors extended pointwise by
  `f`, plus the stuttering caveat (the hidden variable may stutter — this is
  exactly what `\EE` means in TLA). Document the typed divergence; this is
  medium-term, not v1.

## 3. Priority-ordered improvement list (on top of existing projects)

| # | Improvement | Difficulty | Depends on |
|---|---|---|---|
| 1 | Port Leslie's semantic core + rules into a new package (attribution) | easy | — |
| 2 | `Unchanged v`, `[A]_v`, `⟨A⟩_v`, `SF`, `Enabled` semantics | easy–medium | 1 |
| 3 | `Sim` + `stutinv`/`nstutinv` with operator-preservation lemmas; optional `StutQuot` | medium | 2 |
| 4 | Record-state action notation with primes (`x'`, `Unchanged x`, `[Next]_vars`) | medium (prototype-driven) | 1, 2 |
| 5 | Scoped temporal notation + ASCII aliases + improved delaborators/errors | medium | 4 |
| 6 | `tla_inv` invariant tactic | easy | 1 |
| 7 | `tla_wf1`/`tla_sf1` liveness tactics with rank functions | `tla_wf1`/`tla_sf1`/`tla_sf1_standard` done (WF1/SF1 proved from semantics, enabledness left as the human input); rank-function pattern done (`TlaDsl/Examples/Countdown.lean`: `i = k ↝ i = 0` via WF1 + strong induction on the counter, plus a spec-level `◇ i = 0`); mutex/ticket-lock/two-phase liveness examples in `TlaDsl/Examples/Mutex.lean` | 2, 6 |
| 8 | `tla_leads_to` choreography automation | easy–medium | 1 |
| 9 | `native_decide` finite model-check tactic + trace sim with counterexamples | medium | 1, decidability instances |
| 10 | Refinement over `[A]_v` semantics (Abadi–Lamport), re-proved | medium | 2, 3 |
| 11 | `\EE` hiding for composition | hard (typed design) | 10 |
| 12 | Pattern library + tutorials (counter → mutex → 2PC → Paxos-safety → Paxos→Consensus refinement → Byzantine consensus) | counter, mutex, ticket lock, 2PC, Paxos-safety done (`TlaDsl/Examples/Paxos.lean`: Voting-spec port, `ShowsSafety` theorem, agreement invariant); refinement done (`TlaDsl/Examples/PaxosConsensus.lean`: Voting→Consensus via `refinement_mapping_inv`); elaborator: `some v`/polymorphic apps, single- and multi-binder `fun` lambdas, `[c| Byz, p | body]` honest-processor action macro (`CorrectAct`) with the Minimmit example refactored onto it; Byzantine one-round voting done (`TlaDsl/Examples/Minimmit.lean`); extraction core done (`TlaDsl/Examples/Multimmit.lean`: rank rules + Lemma 7 positions + extension-carry/settledness); timed core done (`TlaDsl/Examples/MinimmitTimed.lean`: send times + Lemma 5); exploration write-up in `docs/research/multimmit-exploration.md` | all |
| 13 | Toolchain policy (pinned mathlib, CI, lints), optional cslib LTS bridge | easy–medium | 1 |

## 4. Roadmap (phases with acceptance criteria)

**Phase 0 — Skeleton (days–weeks)**
New lake package; port semantic core + rules from Leslie; `Unchanged`/`[A]_v`/
`SF`; scoped notation; port the counter example. *Accept:* counter safety
proved with `tla_inv; grind` and no Leslie imports.

**Phase 1 — The engineer's daily loop (weeks–months)**
Prime/action notation on record states; `tla_inv`; mutex + 2PC safety;
model-check tactic for finite instances. *Accept:* a TLA+-literate engineer
can write a spec and prove its invariants in one session without reading the
library source; the same examples as Leslie with fewer lines and correct
stuttering.

**Phase 2 — Liveness (months)**
`tla_wf1`/`tla_sf1` with rank functions; leads-to automation; ticket-lock and
mutex liveness; `stutinv`/`StutQuot` refinement layer. *Accept:* textbook
liveness proofs (mutex progress, ticket lock) with rank functions as the only
human input beyond the spec.

**Phase 3 — Composition and refinement (months)**
Refinement over `[A]_v`; `\EE` hiding; 2PC refinement; assume-guarantee.
*Accept:* counter→abstract refinement and 2PC concrete→abstract proved with
`refine_via`-style tactics.

**Phase 4 — Productization**
Tutorials/manual, error-message polish, CI with example regression tests,
optional cslib interop (LTS bridge for trace/bisimulation-based reasoning).

## 5. Non-goals (explicit boundary)

- No `.tla` parser/import, no TLA+2 proof language, no TLAPS interop.
- No untyped values: no `CHOOSE` over classes, no `3 ∪ TRUE`, no
  functions-with-domains; arithmetic is typed and total. Document the
  divergence from TLA+ in a `CONFORMANCE.md` once the DSL stabilizes (the
  intended reading: "typed fragment of TLA+ semantics").
- Meta-theory of the TLA-flavored semantics **is now a priority**
  (2026-08-02 pivot): stuttering equivalence, operator preservation, quotient
  characterization, and proof-rule soundness come first — see
  [`tla-meta-theory.md`](tla-meta-theory.md). This supersedes the earlier
  decision-framework answer; full TLA+ *language* meta-theory (syntax,
  completeness of the calculus) is still out of scope.

## 6. How we will know the UX is good

Concrete, measurable criteria to run against every milestone:

- *Spec expressiveness:* target specs written in near-TLA notation with no
  `fun s s' =>` boilerplate in actions.
- *Proof economy:* invariant proofs are `tla_inv; grind`-shaped; liveness
  proofs are rank-function + tactic shaped; count lines vs Leslie on the same
  examples.
- *Error UX:* a wrong-type state predicate or bad prime produces a readable
  macro/elaborator error, not a metavariable soup.
- *Model-check loop:* finite instances check in seconds via `native_decide`
  before proofs are attempted.
- *Onboarding:* a written tutorial (counter → mutex) executable in one Lean
  file, and a newcomer with TLA+ background can follow it unaided.

## 7. Open design questions to settle by prototyping

1. Prime notation: syntax-category macro vs `StatePair` notation — build both
   on the counter example and choose by feel/robustness.
2. Lifting: explicit `⌜ ⌝` vs coercion-based implicit lifting — measure
   inference stability on the example corpus.
3. `\EE` typed semantics: pick the formulation on 2PC composition, not in the
   abstract.
4. Dependencies: mathlib-only v1; when (if ever) to add cslib — decide when
   the refinement layer needs LTS/bisimulation results.
5. Whether Lentil's proof mode becomes a third UX layer, or task-level
   tactics suffice.

## References

- Leslie (Apache-2.0), Lentil (Apache-2.0), coq-tla (no license; reference
  only) — sources under `docs/research/vendor/`.
- AFP TLA\* (Grov–Merz) for the `stutinv`/`nstutinv` pattern —
  `docs/research/papers/afp-tla-definitional-encoding.pdf`.
- `docs/deep-vs-dsl.md` for why this is a DSL, and `docs/design-space.md` for
  the mathlib/CSLib leverage analysis.
