# Bft: A Lean 4 Verification Pipeline for BFT Consensus

> Project codename **Bft**. This document describes the library as it
> stands: what each layer is, the design decisions that hold it together,
> and the explicit boundaries of what is (and is not) verified.

**Status**: `lake build Bft` green, zero `sorry` across the library.

## 1. Vision and Positioning

A "model → machine-checked proof → executable reference implementation"
pipeline for modern BFT consensus protocols.

Positioning constraints (learned from TLAPS's trajectory):

- Not a general-purpose TLA tool. The target user is a **protocol
  researcher designing a new BFT protocol**.
- Liveness proofs must be a low-cost byproduct of the safety proof, not
  a separate project.
- The executable reference implementation is the adoption hook; the
  proofs are the retention.
- The kernel is designed to be upstreamable into CSLib: no private
  foundational concepts.

## 2. Architecture

```
Bft/Core.lean        semantic kernel (ωSequence, lifts, temporal operators)
Bft/Stutter.lean     stuttering invariance typeclass SI
Bft/Rules.lean       init_invariant_stut, wf1, sf1, leads-to algebra
Bft/RelRank.lean     RelRankCert (Rule 6), LexRankCert (Rule 10), Rule 11
Bft/CslibBridge.lean lossless translation into CSLib ωSequence.Temporal
Bft/Obligation.lean  obligation normalizer + two-state counterexamples
Bft/Tactic.lean      tactic layer
Bft/Exec.lean        executable pipeline (ExecSpec, decidable guards)
Bft/Refine.lean      trace refinement (step simulation, message soup)
Bft/Templates/       certificate templates (FIFO queue)
Bft/Skin/            syntax skin — a replaceable layer (tla_var, brackets)
Bft/Examples/        TicketLock, ObligationDemo, FifoQueue, BoundedCounter,
                     Minimmit, SkinCounter
```

## 3. The Semantic Kernel

### 3.1 Behaviors are `Cslib.ωSequence`

`Behavior σ := Cslib.ωSequence σ` — not `ℕ → σ`. CSLib's
`@[simp] get_drop : (drop m s) n = s (m + n)` (drop-count first, index
last) makes the pointwise form the simp normal form. The kernel only
registers a thin layer on top: `statePred_drop`, `actionPred_drop`,
`eventually_statePred_drop`, `eventually_actionPred_drop`. Descent proofs
contain no suffix-rewrite chains.

### 3.2 Shallow embedding, stuttering invariance by typeclass

`Pred σ := Behavior σ → Prop`, a pure shallow embedding: all of mathlib's
`Prop`-valued machinery composes directly. Stuttering invariance is a
`Prop`-valued typeclass `SI F` with instances for every combinator, so
legality is checked at inference time rather than by discipline. TLA's
syntactic restriction (implication is not stuttering-invariant in
general) is expressed by the *absence* of an `SI (tlaImp F G)` instance;
`leadsTo` has one.

### 3.3 CSLib bridge

`StatePred σ` is literally `Set σ` (mathlib's `Set` is defined as
`α → Prop`), matching `Cslib.ωSequence.Temporal`'s `Step`/`LeadsTo`
signatures. Consequently set notation (`s ∈ p`, `p ∩ q`, `p ∪ q`, `pᶜ`,
`p ⊆ q`) works directly on state predicates, and CSLib's grind-annotated
lemmas (`step_leadsTo`, `leadsTo_trans`, `leadsTo_cases_or`,
`until_frequently_leadsTo_and`, …) apply with no conversion. House style:
declare state predicates as `StatePred σ` or `{s | …}` (never rely on
bare `σ → Prop` literals in `Set` positions — `Set` is semireducible, so
`rw`-family tactics that check at strict transparency reject them; use
`simp [statePred]` there).

The state-level fragment is pointwise-equivalent to
`Cslib.ωSequence.Temporal` (`Step`/`LeadsTo`): certificate conclusions
translate losslessly into CSLib vocabulary via `leadsTo_statePred_iff`.
The bridge also covers `InfOcc` (`∃ᶠ`-machinery for SF-style "infinitely
often enabled") and `FLTS` (the executable step is an FLTS; `run = mtr`).

### 3.4 Finite vs. infinite stuttering: an honest cut

`StutterInvariant` means invariance under single-step stutter
insertion/deletion, generating *finite* stutter equivalence. Full TLA
semantics also requires closure under infinite stuttering (run
compression). That theorem is **not** included: finite stutter invariance
covers every formula of engineering relevance (`□[A]_v`, `WF_v`, `SF_v`,
`↝`), and run compression is mechanical to port when needed. Declared
explicitly, not silently omitted.

## 4. The Liveness Engine

### 4.1 Rules as certificates

`RelRankCert` packages all witnesses of one Rule 6 (McMillan, CAV 2024)
application — justice action, pending predicate, ranking, finite
envelope, and the C1–C3 obligation proofs — into an object that can be
stored, printed, reused across files, and consumed by combinators.
`LexRankCert` does the same for Rule 10 (lexicographic rankings + stable
schedulers), including the full `rel_rank_lex` soundness proof and the
`VecLexLess` well-foundedness theorem.

Combinators: `RelRankCert.trans` (Rule 7 chaining) and
`RelRankCert.forall_fin` + `leadsTo_exists` (Rule 11: a finite family of
certificates sharing `H` and the justice action proves `(∃ i, p i) ↝ q`).

A cautionary data point that justifies the certificate design: the first
draft of the Rule 10 statement was **false** as written — it missed the
S4 premise (at least one scheduler is always on) and had a too-weak
justice antecedent. Both defects were found by the machine-checked proof,
not by review.

### 4.2 The obligation normalizer

`Bft/Obligation.lean`: C1–C3 always unfold to the same shape
(`∀ s s', Next s s' → φ s → q s' ∨ (φ s' ∧ Conserves δ s s')`). The
normalizer uses layered simp sets (`tla_temporal` / `tla_action` /
`tla_state`) with omega/grind finishing, classifies failures by layer,
and never unfolds `Set.ncard` (that stays inside the rule). `#tla_cex`
prints two-state counterexamples by finite enumeration.

### 4.3 Fairness assumptions are explicit

Liveness theorem statements list their fairness dependencies (e.g.
`globalJustice Serve`) instead of pretending to derive them from the
spec. These assumptions translate to deployment premises ("the server
eventually releases every ticket") and are part of the trust-base
documentation.

### 4.4 Certificate templates

`Bft/Templates/Fifo.lean`: FIFO queues rank by queue position
(`List.idxOf`). The template discharges C1 and finiteness automatically
(positions are bounded naturals); the user proves only the two
behavior-level conditions hc2/hc3. Demonstrated in `Examples/FifoQueue`
(per-element liveness, Rule 11 merge, executable smoke run).

## 5. Refinement

`Bft/Refine.lean` — the first layer of message-level refinement:

- `StepSim`/`InitSim`: low-level stuttering steps simulate to high-level
  stuttering steps on the abstract state.
- `specSim_entails`: **arbitrary** high-level properties (safety and
  liveness alike) transfer through the abstraction function.
- `refine_invariant`: invariant transport; `globalJustice_map`: justice
  lifting.
- `Packet`/`NetState`: a message-soup model (plain list, no FIFO
  assumptions).

Demonstrated in `Examples/BoundedCounter`: the abstraction is "served
plus in-flight messages", the bound is proved once at the high level,
and the distributed system inherits it for free. Full Verdi-style
network semantics (faults, duplication) remains a gap.

## 6. The Executable Pipeline

### 6.1 Pattern

Each disjunct of `Next = ∨ᵢ Aᵢ` splits into a guard (reads only the
current state) and a deterministic update; `GuardedAction` packages the
two coherence proofs (`fires`: guard ⇒ relation holds; `det`: the
relation determines the update).

### 6.2 Decidability is first-class

`decGuard : ∀ l s, Decidable (guard l s)` is a field of `ExecSpec`:
an action whose guard is not decidable cannot enter the executable
layer. Guards with existential quantifiers ("some quorum voted") must be
rewritten as bounded checks over finite node sets — that rewrite is part
of the refinement obligation.

### 6.3 Exact content of the correctness theorem

`run_invariant`: the spec's invariant covers every executable run.
Liveness of the executable system is deliberately **not** provided: it
equals the spec's liveness theorem *plus* the deployment environment
satisfying the explicitly listed fairness assumptions — the latter can
never be proved, only declared.

### 6.4 Trust base

Lean kernel + mathlib axioms + this library's zero-sorry theorems +
signature/cryptography FFI (axiomatized) + the deployment environment
satisfying the stated fairness assumptions + the Lean 4 compiler and
runtime.

## 7. The Syntax Skin (Replaceable)

`Bft/Skin/` changes how specs *read*, never what they *mean*. Deleting
it leaves every proof untouched, because all theorems are stated in
kernel vocabulary.

- `tla_var St x y` — declares state functions and the default frame
  `vars`, with global `[simp]` `_apply` lemmas so `simp`/`omega` see
  through `x s` vs. `s.x`.
- `[p| ...]` / `[a| ...]` — type-directed bracket elaborators: `x'` is
  the post-state, bounded `∀/∃ ∈` quantifiers, state-first named
  predicates and named actions lift automatically.
- `[t| ...]` — temporal formulas with invisible lifting of state
  predicates and actions (via `Coe`), `□[A]_v`, `WF_(v)(A)`, `□◇⟨A⟩_v`.
- `[c| Byz, p | body]` — the honest-processor guard sugar.
- Scoped TLA notation (`open scoped Bft`) and delaborators that print
  goals back in bracket form.

Notation-only kernel complements (`tlaIff`, `strongUntil`, `Satisfies`,
`CorrectAct`, function `GetElem`) live inside the layer. Demonstrated in
`Examples/SkinCounter` (bracket spec → safety via `init_invariant_stut`
→ WF1 liveness, all proved on kernel theorems).

## 8. Case Studies

| Example | What is proved |
|---|---|
| `TicketLock` | Full pipeline: invariant, liveness under explicit `globalJustice Serve`, executable `#eval` |
| `FifoQueue` | Per-element liveness via the FIFO template + Rule 11 merge; Nodup invariant reused inside hc2/hc3 |
| `BoundedCounter` | Trace refinement: `served + in-flight ≤ cap` proved once at the high level, inherited by the message-level system |
| `Minimmit` | Voting core of Minimmit (n ≥ 5f+1): monotone message soup, honest single-vote-per-view guard, Byzantine equivocation. One engine lemma (`exists_honest_inter`) drives X0/X1/X2 quorum-intersection theorems, lifted to □-statements via the `HonestUniq` inductive invariant; executable smoke run (double vote rejected, Byzantine vote below quorum) |
| `SkinCounter` | The syntax skin end to end on kernel theorems |

**Minimmit scope (honest declaration)**: only the voting core is
modeled — parent-block dependencies, view progression,
contradiction-based nullification, and liveness (M-notarization guiding
view convergence) are future work.

## 9. Upstreaming to CSLib

The first PR draft packages the Rule 6 engine as
`Cslib/Foundations/Data/OmegaSequence/RankDescent.lean`: a `RankCert`
structure whose conclusion is CSLib's existing pointwise
`ωSequence.LeadsTo` — no formula layer required, minimizing the
acceptance surface. The pointwise descent core (`finite_rank`,
`ncard_decrease`, `rank_persist`, `rank_descent`) is independently
reusable. Ships with a countdown test and follows CSLib CI conventions
(`mk_all` import order, no overlong lines, zero sorry).

Follow-up candidates (already machine-checked here): `trans`/`forall_fin`
combinators, Rule 10 lexicographic rankings, and — if CSLib ever takes a
TLA formula layer — the pointwise simp normal forms.

## 10. Explicit Non-Goals

- TLC-scale model checking (symmetry, partial-order reduction).
- A PTL decision procedure (general-purpose leads-to automation).
- Fully automatic witness inference (δ is template-level semi-automatic
  at best).
- PlusCal-style procedural syntax.

## 11. Relation to lean-tla

The ideas, rule proof structures, and the `rank_descent`/`finite_rank`/
`ncard_decrease` proofs are adapted from lean-tla's machine-checked
versions. Points of divergence: the `SI` typeclass (§3.2), reliance on
CSLib's `drop` simp direction (§3.1), layered simp sets (§4.2),
first-class decidable guards (§6.2), explicit fairness assumptions
(§4.3), and the syntax skin as a replaceable layer rather than part of
the kernel (§7). The best outcome for both projects is a merge along
this roadmap.
