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

### Slice 4 — refinement and hiding (later)

| Theorem | Notes |
|---|---|
| refinement mapping soundness over `StutQuot` | Abadi–Lamport safety part |
| `\EE` (hiding) laws: intro/elim, stuttering closure | the typed formulation from `implementation-strategies.md` |
| canonical form: `Spec = Init ∧ □[Next]_v ∧ L` decomposition lemmas | the engineer-facing normal form |

## 4. Honest scope notes

- `Sim` is currently the **finite-stuttering** relation (inductive: delete or
  duplicate finitely many equal-state runs). The full TLA notion must also
  identify behaviors differing in *infinitely many* stuttering steps; that
  needs a coinductive or block-based definition, likely with mathlib's
  coinductive streams. Slice 1 proves the finite case; the coinductive
  upgrade is tracked as a follow-up and should not change the shape of the
  theorems.
- Values are typed (the DSL's choice). Meta-theory here is about the typed
  fragment's semantics; full TLA+ value semantics (ZFC) remains the
  conformance-oracle goal, not this track.
- No mathlib yet: proofs use core `omega`/`simp`. If the coinductive slice
  needs mathlib, that is the moment to add it as a dependency.

## 5. How this feeds the DSL

- `StutQuot` becomes the type over which specs and properties live; an
  invariant proof is then literally a function between quotient predicates.
- The operator-preservation theorems justify "spec-level" reasoning: if each
  conjunct of a spec is stuttering invariant, so is the whole spec — the
  property that makes refinement (adding/removing stutter steps, internal
  variables) sound.
- The sound rules (slice 3) become the tactic layer (`tla_inv`, `tla_wf1`)
  with their soundness already in the kernel.
