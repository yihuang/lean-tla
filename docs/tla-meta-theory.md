# TLA meta-theory: scope and plan

*Decision (2026-08-02): pivot — start the project with TLA meta-theory,
which supersedes the earlier "meta-theory is not a priority" answer to the
decision framework in [`deep-vs-dsl.md`](deep-vs-dsl.md). The UX-first DSL
remains the long-term product; the meta-theory is its semantic foundation,
and it is the more valuable thing to get right first.*

## 1. What "TLA meta-theory" means here

Not meta-theory of full TLA+ syntax (no parser, no untyped set theory). It
means: **formalize the TLA-flavored semantics and prove the theorems about
it** that every other layer (refinement, tactics, model checking, the DSL
itself) depends on. Concretely, in Lean, over the typed core already built in
`TlaDsl/Basic.lean`:

1. **Stuttering equivalence** `Sim` on behaviors, and **stuttering
   invariance** of every temporal operator. This is the property that makes
   TLA *TLA*: refinement and abstraction only make sense because formulas do
   not distinguish stuttering-equivalent behaviors.
2. **The quotient characterization**: stuttering-invariant formulas are
   exactly the well-defined predicates on `Behavior / ≈`. One theorem, the
   semantic home of TLA.
3. **Soundness of the proof rules**: the invariant rule (box induction),
   leads-to laws, WF1/SF1 — proved from the semantics rather than assumed.
4. **Canonical forms and refinement**: `Init ∧ □[Next]_v ∧ L`, Abadi–Lamport
   refinement mappings, `\EE` (hiding) laws.

This is the "deep where it counts" part of the design: a small, trustworthy
semantic core (the conformance oracle of `deep-vs-dsl.md`), with the typed
DSL as the user-facing layer on top.

## 2. Why it is valuable (and why now)

- **It is the foundation.** Every DSL feature (invariant tactics, liveness
  rules, refinement) is a consequence of these theorems. Getting the
  semantics right first means the DSL stops being "a nice notation" and
  becomes "a logic with theorems".
- **It is self-contained and testable.** Behaviors, `Sim`, and the operators
  are small; each theorem is a checkable milestone that does not need the
  rest of the project.
- **It produces the trust argument.** A stuttering quotient plus
  operator-preservation theorems is the machine-checked version of "our
  formulas mean what TLA means".
- **It is cheap relative to the DSL work** and de-risks it: if stuttering
  semantics turn out to be awkward (e.g., the coinductive case), better to
  learn that now than after building a large tactic layer on a shaky base.

## 3. The theorem list (status as of 2026-08-02)

### Slice 1 — stuttering equivalence and invariance (done, `TlaDsl/Meta.lean`)

| Theorem | Status |
|---|---|
| `Sim` is reflexive/symmetric/transitive (an equivalence) | done |
| `Sim e f → e 0 = f 0` (equal first states) | done |
| suffix matching: `Sim e f → ∀ n, ∃ m, Sim (e.drop n) (f.drop m)` and the right-handed version | done |
| `StutInv` preserved by `⌜p⌝`, `∧`, `∨`, `¬`, `⇒`, `↔` | done |
| `StutInv` preserved by `□`, `◇`, `↝` | done |
| stuttering-invariant formulas lift to `Quot Sim` (`StutInv.lift`) and the iff characterization | done |
| box/eventually basics: `□F ⊢ F`, `□F ⊢ □□F`, `F ⊢ ◇F`, leads-to consequence | done |

### Slice 2 — actions, near-stuttering invariance, fairness (done, `TlaDsl/Meta.lean`)

| Theorem | Notes |
|---|---|
| `NstutInv` for pre-formulas (`⟨A⟩_v`, `Unchanged v`, `[A]_v`) | done — the AFP `stutinv`/`nstutinv` split, plus `sim_step` (step-level suffix matching) |
| `NstutInv A → StutInv (◇⟨A⟩_v)` | done |
| `StutInv (□[A]_v)` given `NstutInv A` | done — the key action theorem |
| `NstutInv A → StutInv (WF_v A)`, same for `SF_v A` | done — added `WF_v`/`SF_v` to the core |
| quotient completeness: `StutInv F` iff `∃! G on Quot, G ⟦e⟧ = F e` | done in slice 1 |

### Slice 3 — proof calculus soundness (done, `TlaDsl/Rules.lean`)

| Theorem | Notes |
|---|---|
| `WF1`: under `□[N]_v ∧ WF_v(A)`, from `p ∧ [N]_v ⇒ ◯(p ∨ q)`, `p ∧ ⟨A⟩_v ⇒ ◯q`, `p ⇒ Enabled ⟨A⟩_v ∨ q` conclude `p ↝ q` | done — semantic proof by contradiction (p persists, A always enabled, fairness forces an A-step) |
| `SF1` (strong fairness analogue) | done — same, with the premise that `p` eventually enables `⟨A⟩_v`; uses infinitely-often enabled |
| leads-to lattice laws (disjunction, transitivity, consequence) | done (`leadsTo_or`, `leadsTo_trans_entails`, `leadsTo_consequence`) |

### Slice 4 — refinement and hiding (done, `TlaDsl/Meta.lean`)

| Theorem | Notes |
|---|---|
| refinement mapping soundness | done — `RefinesVia` + `refinement_mapping` (Abadi–Lamport safety part), transitivity and reflexivity |
| `\EE` (hiding) laws | done — `EEx`/`Extend` with `stutinv_eex` (hiding preserves stuttering invariance via `Sim.map`), monotonicity |
| canonical form: `Spec = Init ∧ □[Next]_v ∧ L` decomposition lemmas | done — `spec_init`, `spec_stutAlways`, `spec_fair`, plus `□`/`∧` and `◇`/`∨` distribution |

**Status: slices 1–4 complete.** The semantic core now covers stuttering
equivalence and the quotient, operator preservation (including fairness),
the liveness rules (`WF1`/`SF1`), and refinement/hiding — all proved from
the semantics, kernel-checked, mathlib-free.

## Examples putting the meta-theory to work

- `TlaDsl/Examples/Refinement.lean`: a two-counter concrete spec refines a
  one-counter abstract spec by projection (`RefinesVia` +
  `refinement_mapping`); the internal variable `y` is invisible to the
  abstract spec.
- `TlaDsl/Examples/TicketLock.lean`: critical-section entry proved with
  `WF1` — the liveness theorem is a one-line application of `wf1` once the
  three standard premises (step, action-to-q, enabled) are discharged by
  `tla_unfold`/`omega`.
- `TlaDsl/Examples/Mutex.lean`: two-process turn-based mutex — mutual
  exclusion via the standard inductive invariant (`init_invariant_stut` with
  six-action case analysis), and two-phase progress `pc = 0 ↝ pc = 2` by
  chaining two `WF1` applications with leads-to transitivity.
- `TlaDsl/Examples/Mutex.lean` (liveness section): the *full chain* — if
  process 0 is trying, she eventually enters the critical section, under
  fairness on `Enter0`, `Req1`, `Enter1`, `Exit1` and the inductive invariant
  (which now also bounds the control variables). Process 1 must request,
  enter, and exit to hand the turn back; the proof chains four `WF1`
  applications and uses the reusable `leads_to_cases` rule (case split under
  an invariant), added to `TlaDsl/Rules.lean`.

Both compile with zero `sorry`s and zero dependencies.

## 4. Honest scope notes

- `Sim` (in `Meta.lean`) is the **finite-stuttering** relation (inductive:
  delete or duplicate finitely many equal-state runs). The full TLA notion
  must also identify behaviors differing in *infinitely many* stuttering
  steps; that is now defined in `SimFull.lean` via run-compression
  (`Compress` — the maximal-run value sequence, computed with `Nat.find`;
  eventually-constant behaviors pad with the final value). `SimFull` has the
  equivalence structure (refl/symm/trans, first-state, quotient) proved; the
  suffix-matching and step-matching lemmas, and migrating the preservation
  theorems to it, are the remaining integration work and should not change
  the shape of the theorems.
- Values are typed (the DSL's choice). Meta-theory here is about the typed
  fragment's semantics; full TLA+ value semantics (ZFC) remains the
  conformance-oracle goal, not this track.
- Mathlib is now a dependency (2026-08-02, toolchain `v4.33.0-rc1` matching
  mathlib's pin); proofs use `grind` (`tla_grind`) alongside `omega`/`simp`.
  The coinductive slice (infinite stuttering) can now use mathlib's
  coinductive streams.

## 5. How this feeds the DSL

- `StutQuot` becomes the type over which specs and properties live; an
  invariant proof is then literally a function between quotient predicates.
- The operator-preservation theorems justify "spec-level" reasoning: if each
  conjunct of a spec is stuttering invariant, so is the whole spec — the
  property that makes refinement (adding/removing stutter steps, internal
  variables) sound.
- The sound rules (slice 3) become the tactic layer (`tla_inv`, `tla_wf1`)
  with their soundness already in the kernel.
