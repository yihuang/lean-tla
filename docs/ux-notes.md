# Prototype UX notes: the first "feel the water" slice

*Status: 2026-08-01. A minimal, mathlib-free vertical slice of the
TLA-flavored DSL is in [`TlaDsl/`](../TlaDsl/) and builds with
`lake build` on Lean 4.32. This document records what the notation and proof
UX actually felt like, what broke, and what to prototype next.*

## 1. What the slice contains

- **Core semantics** (`TlaDsl/Basic.lean`): behaviors `Nat → σ`, temporal
  predicates, lifted connectives, `always`/`eventually`/`later`/`leadsTo`/
  `strongUntil`, `Enabled`, `Unchanged`, `[A]_v` (`StutAction`), `⟨A⟩_v`
  (`AngleAction`), `□[A]_v` (`stutAlways`), `WF`, `SF`, validity/entailment.
- **Notation** (`TlaDsl/Notation.lean`): `□`, `◇`, `◯`, `↝`, `𝑈`, `⇒`, `⊢`,
  `⊨`, `⌜ p ⌝` lifts, and `□[A]_v`.
- **Implicit lifting** (`TlaDsl/Coercion.lean`): one `Coe` instance turns a
  state predicate into a temporal formula automatically.
- **Pseudocode brackets** (`TlaDsl/Prime.lean`): `[p| ...]` (state
  predicates), `[a| ...]` (actions with `x'` primes), `[t| ...]` (temporal
  formulas). `[p|]/[a|]` are a **dedicated elaborator**: it introduces fresh
  pre/post state variables and lifts every identifier of state-function
  type (`σ → α`) to an application `x s` (type-directed, so anything Lean
  elaborates works inside the brackets); `[t| ...]` stays a small macro that
  rewrites propositional connectives to the temporal ones.
- **Rules + tactics** (`TlaDsl/Rules.lean`, `TlaDsl/Tactic.lean`):
  `init_invariant` (plain and stuttering-aware), `leadsTo` transitivity,
  `tla_unfold`, `tla_inv`.
- **Example** (`TlaDsl/Examples/Counter.lean`): a two-counter spec and its
  `x = y` invariant, proved with the tactics.

## 2. The example, as users would write it

```lean
structure St where
  x : Nat
  y : Nat

@[simp] def x : St → Nat := St.x          -- "variables"
@[simp] def y : St → Nat := St.y

@[simp] def Init : Tla.StatePred St := [p| x = 0 ∧ y = 0]
@[simp] def Next : Tla.Action St := [a| x' = x + 1 ∧ y' = y + 1]
@[simp] def Vars : St → Nat × Nat := fun s => (s.x, s.y)

def Spec : Tla.Pred St := [t| Init ∧ □[Next]_Vars]

theorem x_eq_y_invariant : Spec ⊢ □ ⌜ (fun s : St => s.x = s.y) ⌝ := by
  unfold Spec
  tla_inv
  · exact init_ok          -- ∀ s, Init s → s.x = s.y, by tla_unfold; omega
  · exact step_ok          -- step case: rcases stutter; tla_unfold; omega
```

This compiles and the proof is four lines of real work. That is the headline
result: **the pseudocode notation layer works**, including `x'` primes and
`□[Next]_Vars`, and the implicit `Coe` lift means `Init` needs no explicit
`⌜ ⌝` inside `[t| ...]`.

## 3. What felt good

- `[p| ...]`, `[a| ...]`, `[t| ...]` all parse without conflicts (the leading
  `[` does not clash with list literals) and read like pseudocode.
- `x' = x + 1 ∧ y' = y + 1` really works: the macro lifts the body pointwise
  over a pre/post state pair, and the result is a real `Action St`.
- `[t| Init ∧ □[Next]_Vars]` needs zero explicit lifting — the `Coe` covers
  it, and the same spec written with `⌜ ⌝` (`Spec'`) compiles too, so we can
  compare styles.
- The proof ceremony is small: `tla_inv` (apply the stuttering-aware
  invariant theorem) + `omega` (core, no mathlib needed) handles the counter.
- Everything is definitional and kernel-checked; no axioms.

## 4. What felt rough (the honest part)

1. **State functions need a declaration line and `@[simp]`.**
   `@[simp] def x : St → Nat := St.x` per variable. The `@[simp]` was not
   optional: with `abbrev`, `simp`/`omega` treated `x s` and `s.x` as
   different atoms and proofs failed. **Resolved:** the `tla_var St x y`
   command (`TlaDsl/TlaVar.lean`) declares the state functions, the default
   `vars` stuttering frame, and the `[simp]` `_apply` lemmas automatically.
   Note: proofs should use plain `simp`/`tla_unfold`; listing a generated
   variable explicitly (`simp [x]`) is not supported (programmatically
   declared constants are not unfoldable that way).
2. **The bracket macros are a small language.** Only identifiers, numerals,
   and `= + - * < ≤ ∧ ∨ ¬` are supported inside `[p|]/[a|]`. No function
   application (`f x`), no binders (`∃ x ∈ S, ...`), no `→`/`≠`/`if-then-else`.
   Real specs (arrays, records, quantifiers over processes) will hit this
   immediately. **Progress (2026-08-03):** function applications (arguments
   lifted pointwise — `Even x`, `n % 2`), `≠ > ≥ %`, `→` in `[t| ...]`, and
   type ascriptions are now supported; the parity-based SF1 example
   (`StrongFair.lean`) is back in bracket syntax. **More (2026-08-03):**
   bounded quantifiers `∀ x ∈ S, ...` / `∃ x ∈ S, ...` over set-valued state
   functions (bound variables are tracked and treated as plain values, not
   state functions), untyped `∀`/`∃` in `[p|]/[a|]`, temporal `∃`/`∀` in
   `[t| ...]`, `if-then-else`, state/action `→`/`⇒`, and the constants
   `∅ true false`. `Binders.lean` demonstrates the process-quantifier style.
   Remaining gaps: primed functions applied to arguments (`x'[i]`), qualified
   names, and the expected-type heuristic for plain function applications
   (`Even x` works when the state type is known; with no expected type a
   bare `Nat → Prop` could be mistaken for a state function). **Resolved:
   the brackets are now a dedicated elaborator** (type-directed lifting,
   expected-type threading, real binder parsing), which replaced the
   syntax-pattern macro wholesale.
3. **Prime handling is purely syntactic** (strip the trailing `'`), so `x''`
   or qualified names misbehave; documented, acceptable for a prototype.
4. **`tla_unfold` had to be `simp at *` under `try`**: this Lean version
   doesn't expose `location` as a macro category, so `tla_unfold at hnext`
   is unavailable. It works, but "unfold everywhere" is blunt and can
   surprise. A proper `elab`-level tactic should support locations.
5. **Stuttering is now semantically honest, and that costs a little.**
   `[Next]_Vars` produces a disjunct `Vars s' = Vars s`, so step proofs must
   `rcases` the stutter case and `injection` the pair equality. This is the
   price of correct `[A]_v` semantics (vs Leslie's `s = s'`); a `tla_inv`
   tactic should `by_cases` the stutter automatically.
6. **No mathlib**: no `grind`, `linarith`, `Finset`, or decidability
   infrastructure. **Resolved:** mathlib is now a dependency (toolchain
   `v4.33.0-rc1`, matching mathlib's pin; oleans fetched from the cache), and
   the `tla_grind` tactic (`tla_unfold; grind`) discharges action-level
   obligations with SMT-style automation. The whole library and all examples
   build unchanged against mathlib.

## 5. What to prototype next (in rough priority)

- **A `tla_var`-style command** that declares state functions and registers
  the simp lemmas, removing the per-variable boilerplate.
- **Extend the action language**: function application and `∃/∀` binders
  (needed for `{p \in Proc : ...}`-style specs); if the macro grows painful,
  move to a dedicated elaborator.
- **A liveness example** (mutex progress or ticket lock) using `WF`/`SF`,
  `leadsTo`, and a rank function — this is the real test of the proof UX
  (the `wf1` rule from the design docs).
- **A multi-action spec** (Leslie's `ActionSpec` pattern) to test composition
  and named actions in the notation.
- **Add mathlib** (pin a nightly, fetch deps) and switch automation to
  `grind`; re-run the same examples and measure.
- **Delaborators** so goals/hypotheses pretty-print in TLA notation (the
  `[p| ...]`/`[a| ...]` forms) instead of lifted lambdas.

## 6. Bottom line

The "pseudocode DSL" direction is validated: TLA-flavored notation with
primes, stuttering brackets, and implicit lifting compiles and supports
small proofs with near-TLA source text. The main open risk is not notation
but **expressiveness and automation at scale** — the macro language's
limitations and the state-function boilerplate will dominate once specs get
real (processes, data structures, quantifiers). Both are addressable; the
next slice should attack them directly.

---

# UX review after the Streamlet slices (2026-08-06)

The Paxos and Streamlet case studies (safety in `Streamlet.lean`, liveness
in `StreamletLiveness.lean`) are the first at-scale stress tests of the
DSL. This is the honest post-mortem: where the verbosity actually goes,
what a "significantly less verbose" version looks like, and what to
automate first. Numbers below are from the current files.

## 1. Where the lines go (evidence)

`StreamletLiveness.lean` is 1688 lines; `Streamlet.lean` is 697. The
breakdown of the liveness file, roughly:

| Slice | Lines | Character |
|---|---|---|
| model + actions + invariants | ~400 | spec, mostly fine |
| invariant preservation (`vote_inv`, `propose_inv`, `advance_inv`) | ~250 | **mechanical: 4 proofs × 12 fields** |
| safety core re-proved for the extended model | ~200 | reuse of the safety file's lemmas |
| structural liveness (Fact 3, Lemma 5, Theorem 6) | ~250 | real content |
| temporal wrapper (`epoch_step`, `window_progress`, `liveness_spec`) | ~450 | **~40 drop-conversions and 4 × `hInvAll` extractions are plumbing** |

Three concrete smells, each with a count:

1. **The 12-field `Inv` structure forces 12-bullet preservation proofs.**
   `refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` appears four
   times, and most bullets are the same shape:
   `intro ...; exact hInv.votedX ... (by simpa [propose] using hv0)`. The
   *changed* field (the one the action writes) is one or two bullets per
   action; the rest is frame noise.
2. **The leads-to API lives at `e.drop n`, the proofs at `e n`.**
   `simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
   Nat.add_left_comm] using ...` (or one of its 5 variants) appears ~40
   times, every time a leads-to premise is built or a conclusion unpacked.
   The root cause is the `leadsTo` definition
   (`Q (e.drop (n + j))`), which forces manual conversion to and from
   `e n` at every application.
3. **The same "frame extraction" idioms repeat** (`vote_votes_of_ne`,
   `not_and_or.mp`, `sub_le_sub_right`, `drop_at_zero`, ...) 31 times —
   evidence that a few helper lemmas/tactics would have removed a hundred
   lines.

## 2. The five pain points, ranked by (annoyance × frequency)

### P1 — Invariant preservation is dominated by "unchanged field" boilerplate

Before (today):

```lean
refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
· intro i e0 b0 hv0
  exact hInv.votedEpoch i e0 b0 (by simpa [propose] using hv0)
· -- ... 11 more, of which only the `proposed`-group bullets are real
```

After (target):

```lean
theorem propose_inv ... : Inv n s' := by
  tla_inv_step          -- unfold action, ext, split the 12 fields,
                        -- discharge unchanged ones from the frame equations
  · -- only the fields the action writes remain
    ...
```

The tactic knows nothing about `Inv`'s field names: it needs the invariant
to be a structure (it is), the pre-state invariant as a hypothesis (it is),
and the action's frame equations (`proposed' = Function.update ...`,
`cur' = cur`, `votes' = votes`). For each goal field it tries
`simpa [frames] using <corresponding pre field>`; whatever remains is the
genuine proof. Expected saving: ~200 lines of the liveness file, and every
future protocol's `next_inv` becomes a 3–5 line tactic call plus the real
cases.

### P2 — Leads-to should be usable at the state level, not the suffix level

Before (today, in `epoch_step`):

```lean
have hp0 : (Tla.statePred (fun s => s.cur = e' ∧ s.proposed e' = none))
    (e.drop k) := by
  have hnone0 : ((e.drop k) 0).proposed e' = none := by
    simpa [Cslib.ωSequence.drop, Nat.add_comm] using hnone
  change ((e.drop k) 0).cur = e' ∧ ((e.drop k) 0).proposed e' = none
  exact ⟨hcur, hnone0⟩
rcases (hH.2.2.2.1 e') k hp0 with ⟨j1, hj1⟩
refine ⟨j1, ?_⟩
simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
  Nat.add_left_comm] using hj1
```

After (target):

```lean
rcases tla_leads_to_at (hH.2.2.2.1 e') ⟨hcur, hnone⟩ with ⟨j1, hj1⟩
-- hj1 : (e (k + j1)).proposed e' ≠ none ∧ (e (k + j1)).cur = e'
```

A `tla_leads_to_at` tactic (or a state-level reformulation of the rule:
`P (e n) → ∃ j, Q (e (n + j))`) removes the drop conversions entirely.
The existing `drop_at_zero`/`statePred_drop` helpers are the kernel; the
tactic just applies them mechanically. Same for the four
`simpa [Tla.always, Tla.statePred, Cslib.ωSequence.drop, ...]` extractions
of `hInvAll` — one `tla_inv_of_spec` helper would cover them.

Expected saving: ~80–100 lines of the temporal wrapper, and — more
important — the liveness proofs become readable as "from this state,
eventually that state" instead of suffix-index arithmetic.

### P3 — Complex specs leave the bracket language

The `[p| ...]`/`[a| ...]` brackets earn their keep on the action layer
(`Vote`, `Propose` read like pseudocode) but the invariants and derived
predicates (`NotarizedBy`, `ChainNotarizedBy`, quorums, `WindowDone`) are
plain definitions, because the brackets don't lift named relations. The
user noticed this drift ("more and more plain expressions instead of
macros"). The elaborator already auto-lifts state functions whose first
argument is the state; extending the same mechanism to *named predicates*
with the state as first parameter (`ChainNotarizedBy b e` inside
`[p| ...]`, with `s` filled in) would keep complex specs in bracket form.
This is a small, local change to the elaborator (the state-first signature
is already the convention).

### P4 — Goals don't delaborate to TLA

`TlaDsl/Pretty.lean` has unexpanders for the temporal layer
(`□`, `◇`, `⌜ p ⌝`, `□[A]_v`), so `Spec ⊢ □Inv` goals read well. But
state predicates and actions still print as lifted lambdas:
`fun s => ...` instead of `[p| ...]`. The state/action brackets were built
as an elaborator, not a delaborator. A first cut: unexpanders for the
recognizable shapes (conjunctions of lifted equations/inequalities) plus a
`change [p| ...]` fallback in the tactics; the long-term option is stashing
the original syntax in `TermInfo` and recovering it in a custom delaborator
(the same mechanism `simp` uses to display original terms).

### P5 — Lean gotchas that cost real debugging time (document + mitigate)

These came up repeatedly during the Streamlet work; none is a DSL bug, but
all are UX:

- `rcases h with ⟨rfl, rfl⟩` on `j = i ∧ e' = b.epoch` **eliminates `i`**
  (the `rfl` pattern substitutes a variable on the right of the equation),
  so later references to `i` fail with "unknown identifier" — the fix is
  `rcases h with ⟨hji, he'⟩; subst j; subst e'`. A short note in the
  example docs saves this debugging cycle.
- `by omega` in argument position (e.g. `proposal_ne_genesis hInv hp1 (by
  omega)`) fails with "No usable constraints" when the expected type still
  contains a metavariable; the fix is naming the epoch explicitly. Same
  class of issue as the elaborator's primed-identifier heuristic.
- `ωSequence` applications are **not definitionally equal** across
  `drop`/`add` reassociations, so `exact` fails where `simpa` works; the
  `drop_at_zero` family exists but should be applied by a tactic, not by
  hand.
- Namespace/type collisions (the `Block` namespace vs the `Block` type)
  are papercuts; worth a naming convention in the docs.

## 3. Proposed slices, in priority order

| # | Slice | Pain | Expected impact | Effort |
|---|---|---|---|---|
| 1 | `tla_inv_step` — invariant-preservation automation (unfold, ext, field-split, auto-discharge frames) | P1 | `next_inv` for any protocol: 12 bullets → 1 tactic call + real cases; ~200 lines saved here | medium (pure tactic) |
| 2 | State-level leads-to API: `tla_leads_to_at` tactic + `tla_inv_of_spec` helper | P2 | temporal proofs lose all drop-conversion noise; ~100 lines + readability | easy–medium |
| 3 | Bracket lifting of named state-first predicates | P3 | complex invariants stay in `[p| ...]` form; specs read uniformly | easy (elaborator-local) |
| 4 | State/action delaborators (`[p| ...]`-style goal display) | P4 | goals/hyps read like TLA in the middle of proofs | medium–hard |
| 5 | Gotcha documentation + mini-utilities (subst pattern, `by omega` note, naming conventions) | P5 | fewer debugging cycles | easy |

Recommended order: **2 and 3 first** (small, local, immediately felt),
then **1** (the big line win), then 4, then 5. Item 2's helpers
(`drop_at_zero`, `statePred_drop`, the frame-preservation lemmas) already
exist in `StreamletLiveness.lean` and can be promoted into the library
verbatim; item 1 should be prototyped against `StreamletLiveness.lean`'s
four preservation proofs as the regression suite.

## 4. The one-paragraph takeaway

The DSL's notation is not the bottleneck anymore — the *proof plumbing* is:
two thirds of the liveness file is mechanical invariant-preservation and
suffix-index conversion. The highest-leverage work is therefore not more
notation but (a) an invariant-induction tactic that eats the frame cases,
and (b) a leads-to API that works at states instead of suffixes. Both are
pure automation on top of the existing semantics, both have the Streamlet
files as ready-made test cases, and together they would cut the liveness
file's mechanical overhead by roughly half.
