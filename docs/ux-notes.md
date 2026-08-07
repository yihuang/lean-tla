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
| 2 | State-level leads-to API: `leadsTo_at`/`leadsTo_at_suffix` + `inv_all_of_spec` | P2 | temporal proofs lose all drop-conversion noise; ~100 lines + readability | easy–medium — **done (2026-08-06)** |
| 3 | Bracket lifting of named state-first predicates + `∈` over `List` | P3 | complex invariants stay in `[p| ...]` form; specs read uniformly | easy (elaborator-local) — **done (2026-08-06)** |
| 4 | State/action delaborators (`[p| ...]`-style goal display) | P4 | goals/hyps read like TLA in the middle of proofs | medium–hard |
| 5 | Gotcha documentation + mini-utilities (subst pattern, `by omega` note, naming conventions) | P5 | fewer debugging cycles | easy |

Recommended order: **2 and 3 first** (small, local, immediately felt),
then **1** (the big line win), then 4, then 5. Item 2's helpers
(`drop_at_zero`, `statePred_drop`, the frame-preservation lemmas) already
exist in `StreamletLiveness.lean` and can be promoted into the library
verbatim; item 1 should be prototyped against `StreamletLiveness.lean`'s
four preservation proofs as the regression suite.

### Slice 2 done (2026-08-06): state-level leads-to API

`TlaDsl/Rules.lean` now has the state-level leads-to API:

- `leadsTo_at h hp` — apply a leads-to at the current state:
  `P (e n) → ∃ j, Q (e (n + j))`;
- `leadsTo_at_suffix h hp` — same, with the premise already at the suffix
  state `(e.drop n) 0`;
- `inv_all_of_spec spec_entails hspec` — the pointwise invariant
  `∀ m, inv (e m)` from `spec ⊢ □ ⌜inv⌝` and `spec e`.

`StreamletLiveness.lean` was refactored onto the new API. Measured effect:

- file length 1688 → 1604 lines (−84);
- `Cslib.ωSequence.drop` conversions 40 → 16 (the remaining ones are the
  unavoidable suffix-level conclusion of `leadsTo`, the `hStut` extraction,
  and the k=0 base case);
- the `epoch_step` propose/vote/clock chain reads as
  `rcases Tla.leadsTo_at (hH.2.2.2.1 e') ⟨hcur, hnone0⟩ with ⟨j1, hj1⟩`
  — the premise and conclusion are both at the state level, no drop
  arithmetic visible;
- the three `hInvAll` extractions are each one `inv_all_of_spec` call.

The `leadsTo_at_suffix` variant covers the one case (the propose step in
`epoch_step`) where the premise facts arrive from an `rcases` of a
suffix-level state predicate; everything else uses `leadsTo_at`. Item 3
(bracket lifting of named state-first predicates) is next.

### Slice 3 done (2026-08-06): named predicates in brackets — mostly already there

Honest correction: the review's P3 claim ("the brackets don't lift named
relations") was **wrong**. The elaborator's type-directed lifting already
applies any identifier whose first parameter is the state type, so
state-first predicates compose with the pseudocode layer:

```lean
-- state-first signature (the convention), usable inside brackets as:
[p| ∀ i : Node, ∀ e : Epoch, ∀ b : Block,
      votes[i][e] = some b → ChainNotarizedBy n b.pred (e - 1)]

-- primed form inside actions applies to the post state:
[a| ... ∧ (∃ b : Block, NotarizedBy' n b (cur - 1)) ∧ ...]
```

The `Vote`/`Propose` actions in `StreamletLiveness.lean` already use this
in production. What *was* missing:

- **`∈` over `List`** (and `Array`/`Multiset`) in bounded quantifiers:
  `∀ C ∈ b.ancestors, ...` failed with "unsupported set type: List".
  Fixed in `TlaDsl/Prime.lean`'s `elabElemType` — chain-style specs can
  now be written in bracket form.
- **The convention was undocumented.** Added to `Prime.lean`'s header:
  write derived predicates state-first and they compose with the brackets;
  primed forms apply to the post state.

One caveat recorded for future work: the *shared* derived predicates
(`NotarizedBy`, `ChainNotarizedBy`, the `Inv` conjuncts) stay plain
definitional lambdas rather than `[p| ...]` brackets, because the brackets
lift the `tla_var` projections (`votes s`) while proofs operate on the
structure fields (`s.votes`), and the two do not compose definitionally in
`exact`. A future elaborator refinement could emit the field projection
for `tla_var`-generated state functions, making bracket-form definitions
fully proof-compatible; until then the convention is: brackets for the
action/spec layer, plain defs for shared proof-relevant predicates.

Next: item 1 — `tla_inv_step` (invariant-preservation automation), the big
line win, with `StreamletLiveness.lean`'s four preservation proofs as the
regression suite.

### Slice 1 done (2026-08-06): `tla_inv_step` — invariant-preservation automation

`TlaDsl/Tactic.lean` now provides `tla_inv_step`. After a step proof has
established `s' = transformer s ...` and `subst s'`, one call replaces the
whole 12-field bullet list:

```lean
theorem vote_inv ... : Inv n s' := by
  tla_unfold
  rcases hstep with ⟨hcur, hpos, hProp, hNoVote, hSeen, hLongest, hVotes', hProp', hCur'⟩
  have hs' : s' = vote s i b := by ext <;> simp [vote, hVotes', hProp', hCur']
  subst s'
  tla_inv_step
  · -- only the genuinely-changed fields remain, in field order
    exact voteLenMono_vote (Block.epoch_pos_ne_genesis hpos) hLongest hcur hInv
  · -- ProposedSeenParent: votes changed, chain lookup needs the rewrite
    ...
  · -- ProposedLongest
    ...
```

What it does, per field of the invariant structure (in declaration order):

1. **defeq check** (`isDefEq (mkMVar g) ⟨pre-state field projection⟩`, at the
   meta level): closes unchanged fields definitionally — record-update
   projections reduce in the kernel, so an action that only touches `votes`
   is invisible to a `proposed`-only field. This alone discharges the bulk
   of the frame cases with no elaboration at all.
2. **`simpa [transformer] using ⟨pre-state field⟩`**: the transformer is read
   from the goal's state expression (a record update, as in `advance`,
   needs no lemma). Handles arithmetic and simple rewrites.
3. **convention-named preservation lemma** `⟨field⟩_⟨transformer⟩` (e.g.
   `votedEpoch_vote` for `Inv.votedEpoch` under `vote`), via
   `apply ⟨lemma⟩ <;> assumption`: discharges the fields whose proof needs
   the case analysis on a `Function.update`-style state change. This is now
   part of the DSL convention: when an action's preservation proof is not
   pure simplification, write it once as `field_action` and `tla_inv_step`
   picks it up automatically.

Measured effect on `StreamletLiveness.lean`:

- file length 1604 → 1546 (−58 lines, all three preservation proofs);
- 36 invariant bullets (12 per action) → 11 total:
  `vote_inv` 3 (VoteLenMono + ProposedSeenParent + ProposedLongest),
  `propose_inv` 6 (VotedProposed + the four proposed-group cases +
  ProposedLongest), `advance_inv` 2 (VotedCur + ProposedCur);
- every remaining bullet is a real case (a `Function.update` case split, a
  votes-preservation rewrite, or an arithmetic step), so the tactic's
  "what's left is what the action writes" contract holds.

Implementation notes (three Lean API traps worth recording for future
tactic work):

- **`simp` argument nodes must have the right syntax kind.** A
  `TSyntax \`Lean.Parser.Tactic.simpLemma` wrapping a raw `ident` node is
  silently dropped by `elabSimpArg` (it dispatches on the node kind and
  recovers by returning `.none`). Build it with the quotation
  `` `(Parser.Tactic.simpLemma| $(mkIdent n):ident) `` instead.
- **`StructureInfo.fieldInfo` is sorted, not reverse-declaration-order.**
  `fieldInfo` is sorted by `StructureFieldInfo.lt`; `.reverse` only
  accidentally matches declaration order for two-field structures. Use
  `getStructureFields env invName` (declaration order) plus
  `getFieldInfo?` for the projector.
- **A failing `exact` can log error messages and swallow its own failure.**
  `evalTactic (exact ...)` on a type mismatch logs "Application type
  mismatch" and throws an abort exception that `Tactic.run` catches and
  turns into a normal return, so "the tactic ran" does not imply "the goal
  closed" and the leaked message persists. Doing the defeq check directly
  (`isDefEq (mkMVar g) projExpr`, via `Meta.mkProjection` for the field
  projection — which also supplies the structure parameters) avoids both
  problems and is faster.

Remaining per the priority table: slice 4 (state/action delaborators,
medium–hard) and slice 5 (gotcha documentation + mini-utilities, easy) —
the P5 gotchas above (the `rcases ... rfl` subst trap, `by omega` in
argument position, `ωSequence` defeq) are the ones to capture.

### Slice 4 done (2026-08-06): state/action delaborators

`TlaDsl/Pretty.lean` now registers a `@[delab lam]` that inverts the
bracket elaborators: a `σ → Prop` lambda whose state variable only ever
occurs as the first argument of a state function (a `tla_var` abbreviation
or a structure projection) displays as `[p| ...]`, and a `σ → σ → Prop`
lambda as `[a| ...]` with the post-state applications primed. Goals that
used to read

```lean
⊢ (fun s => s.cur = 0 ∧ (∀ e : Epoch, s.proposed e = none) ∧ ...) s
```

now read

```lean
⊢ [p| cur = 0 ∧ (∀ e : Epoch, proposed e = none) ∧ ...] s
```

and action-shaped hypotheses read `[a| cur' = cur + 1 ∧ votes' = votes]`.
It is conservative: it falls through (default lambda display) for value
binders (`∀ C : Block, C ∈ b.ancestors → ...` keeps its `C`), for lambdas
over non-structure domains, for `Enabled`-style shapes where the state is
an argument of a free-variable action, under `pp.all`, and whenever the
elision would leave a stray state-variable occurrence. `TlaDsl/Tactic.lean`
imports `TlaDsl.Pretty`, so every example file that uses the tactics gets
the display for free.

Implementation notes (the delabbed syntax shapes that took the debugging):

- applications delaborate as `app(f, argNode)` where `argNode` is a `null`
  node wrapping *all* explicit arguments, so multi-ary state functions
  (`s.votes i e` = `app(proj(s, votes), #[i, e])`) need two cases: the
  state as the first wrapped argument, and the state as the base of a
  field-notation head;
- never reuse child syntax nodes in the rewritten body — their source
  annotations corrupt the info tree ("failed to pretty print"); rebuild
  idents with `mkIdent`;
- match binder names exactly (`sName.getId`), not by string, to keep macro
  scopes consistent.

Remaining per the priority table: slice 5 (gotcha documentation +
mini-utilities, easy) — the P5 gotchas are the ones to capture.

### Slice 5 done (2026-08-07): gotcha documentation + mini-utilities

`docs/gotchas.md` now documents the P5 papercuts with symptom/cause/fix
and a live example each:

- **`rcases h with ⟨rfl, rfl⟩` eliminates the right-hand-side variables**
  (so `j = i ∧ e' = b.epoch` kills `i` and `b.epoch`) — and, the subtle
  part, `subst h1` on `h1 : j = i` has the same trap. Fix: substitute the
  left-hand-side variables by name. New utility:
  `tla_rcases_subst h` reads the LHS variables from the conjunction type
  and substitutes them, keeping the RHS variables alive.
- **`by omega` in argument position** fails with "No usable constraints"
  when the expected type still has a metavariable — annotate the expected
  type or bind the argument in a named `have` first.
- **`ωSequence` suffix conversions are not definitional** — the
  `simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
  Nat.add_left_comm]` incantation is now `tla_drop_simpa using h` (with or
  without `using`), bundling that exact set plus the spec-layer
  unfoldings. StreamletLiveness's 16 repeated conversion calls collapsed
  to it.
- **`Block` namespace/type collision** — resolution depends on scope; keep
  the type and its lemma namespace apart by convention.

Bonus: the `tla_rcases_subst` elab needed `withMainContext` — a tactic
that reads hypotheses at the top level otherwise sees the *original*
theorem context, not the goal's intro'd variables. Recorded in
`docs/gotchas.md` §5.

All four original slices are now done; the one-paragraph takeaway below is
the current state of the DSL's proof UX.

### Liveness refinement case study (2026-08-07)

`TlaDsl/Examples/RefinementLiveness.lean` runs the Abadi–Lamport
liveness-refinement pattern end to end:

* **Abstract spec** (`Abs`): a counter with `x' = x + 1`, weak fairness on
  the increment. `Abs.step` is one `tla_wf1` application; `Abs.leadsTo`
  chains two WF1 steps through `leads_to_via_nat` (rank `2 - x`) to get
  `x = 0 ↝ x = 2`.
* **Concrete spec** (`Conc`): each increment is a two-phase handshake
  through an internal flag (`flag = 0 → flag = 1` raising, invisible to
  `x`; then `flag ≠ 0 → x + 1`), with weak fairness on the composite
  action.
* **Safety**: `conc_refines_abs` proves the concrete refines the abstract
  by projecting away the flag (`refine_via`); a raise phase is a
  `x`-stutter.
* **Liveness**: `wf_conc_to_abs` proves the concrete fairness implies the
  abstract fairness on the mapped behavior — the substantive part. The
  proof uses `Nat.find` for "the first angle step after a raise" and a
  generic `step_eq_of_all` frame-stability lemma to show the handshake
  steps alternate: after a raise the next angle step is an increment, so
  infinitely many handshake steps yield infinitely many `x`-changes.
* **Transfer**: `conc_leadsTo` derives the concrete `x = 0 ↝ x = 2` from
  the abstract one via the new library theorem `Tla.leadsTo_refines`
  (`Meta.lean`): safety refinement + abstract leads-to ⇒ the refined
  leads-to `P ∘ f ↝ Q ∘ f` on the concrete behaviors.

The library addition (`leadsTo_refines`) is the reusable A-L liveness
transfer: it works for any refinement mapping, so a new case study only
needs the fairness-preservation proof (here the alternation argument) and
the abstract liveness theorem.

### Liveness refinement case study 2 (2026-08-07): prepare–accept consensus

`TlaDsl/Examples/RefinementConsensus.lean` pushes the same pattern to a
Paxos-flavoured protocol, exercising two library pieces the first case
study did not:

* **Abstract spec** (`Abs`): decide the value `1` in one step, guarded by
  `decided = none`; WF proves `decided = none ↝ decided = some 1` (one
  `tla_wf1` application).
* **Concrete spec** (`Conc`): two rounds through a `phase` machine — prepare
  (phase `0 → 1`, sets the value), then accept (phase `1 → 0`, commits
  `some value`) — with WF on the composite action.
* **Invariant-threaded safety**: the step correspondence only holds on
  reachable states (`Inv`: phase ∈ {0, 1}, `decided` ∈ {none, some 1},
  value = 1 when armed), so the refinement uses
  `refinement_mapping_inv` — the case where the mapping's behavior is
  itself a protocol invariant.
* **Liveness**: `wf_conc_to_abs` shows the concrete fairness implies the
  abstract one on the mapped behavior. The first angle step is a prepare,
  the next is an accept (same `Nat.find` + frame-stability argument as
  case study 1), so the concrete eventually decides; after that the
  abstract angle action — guarded by `decided = none` — is disabled
  forever, so the abstract fairness holds vacuously (per-suffix premise
  false).
* **Transfer**: `conc_leadsTo` derives the concrete
  `decided = none ↝ decided = some 1` via `leadsTo_refines`.

The generic frame-stability lemma from case study 1
(`Tla.step_eq_of_all`, "the frame is constant over a run of unchanged
steps") moved to `TlaDsl/Rules.lean` and is shared by both case studies.

### Deep liveness refinement through the LTS layer (2026-08-07)

`TlaDsl/Examples/RefinementLivenessLTS.lean` re-derives the two-phase
counter case study through CSLib's LTS machinery (`TlaDsl/LTSRefine.lean`),
closing the reviewer's "no link to CSLib's `imageFinite`/`finiteState`"
point with a worked protocol pair:

* `conc_refines_abs_lts`: the DSL step correspondence is exactly a forward
  simulation between the spec LTSs (`sim_iff_step`) — the concrete spec's
  ω-executions map to the abstract ones (trace inclusion);
* `conc_refines_abs_sat_lts`: the same correspondence with τ-stutter runs
  absorbed (`sim_saturate_of_step`), the executable-refinement shape;
* `conc_imageFinite`: the concrete LTS is image-finite even though its
  state space is infinite — the action contributes at most two successors
  and the stutter contributes exactly one (`Vars` is injective), so every
  successor set is finite. This is the structural finiteness hypothesis of
  the deep A-L liveness theorem, proved directly (the `[Finite σ]` shortcut
  does not apply to infinite-state specs);
* `conc_refines_abs_wf_lts`: the full canonical-form refinement with
  liveness, re-proved through the LTS layer.

The deep LTS layer is now a **user-facing interface**: `LTSRefine.lean`
gained the invariant-threaded simulation (`sim_inv_of_step`), the generic
image-finiteness lemma for infinite-state specs
(`specLTS_imageFinite_of_step`: injective frame + finitely many action
successors), and the invariant-threaded refinement
(`refinement_mapping_inv_lts`). The consensus case study's deep section
then reads as protocol facts only — the invariant-carrying simulation, the
image-finiteness (injective frame, two action successors), and the
canonical-form refinement are each a few lines re-stating facts proved
above, with the machinery in the library. The counter case study's
image-finiteness proof was likewise shortened onto the generic lemma.

### The spec is runnable: FLTS bridge (2026-08-07)

`RefinementLivenessLTS.lean` gains an "executable step function" section
(the E1 shape from the BFT design notes, and the FLTS item from the
north-star reuse list): the counter's `Next` is a deterministic step
function, so the same spec is CSLib's functional LTS.

* `step` — the transition function (prepare from `flag = 0`, increment
  otherwise) and `next_iff_step` — the action fires exactly to `step s`;
* `stutAction_iff_step_or_self` — `[Next]_Vars`-steps are either the
  deterministic action step or a stutter, which (since `Vars` is
  injective) is the state itself;
* `flts` + `spec_tr_iff_flts_or_stutter` — the spec LTS is the FLTS LTS
  plus the stutter self-loops, so every `foldl` run of `step` is a
  `[Next]_Vars` behavior (`flts_tr_sub_spec`);
* `flts_refines_abs_lts` — the executable runs refine the abstract spec
  too (the FLTS LTS simulates the abstract spec LTS).

This is the pattern a Streamlet-scale `Next` can follow later: give the
step function, prove the action matches it, and the spec is both proved
about and runnable from the same definition.

### The spec-authoring walkthrough (2026-08-07)

`TlaDsl/Examples/Tutorial.lean` runs the whole workflow on one small
protocol — state + `tla_var`, the spec in brackets, an invariant with
`tla_inv_step`, liveness with `tla_wf1`, the safety refinement with
`refine_via`, and the liveness transfer with `Tla.leadsTo_refines` — each
step naming the tool and its real-scale home. `docs/spec-authoring.md` is
the accompanying guide, with the engine table (WF1 / rank / relational
rank), the conventions, and pointers into the library. One real bug found
while writing it: `tla_inv_step` read hypotheses from the term context
instead of the goal context, so it failed on goal-local invariants — fixed
with `withMainContext` (the same lesson as `tla_rcases_subst` in slice 5).

### Streamlet is runnable: the executable step function (2026-08-07)

`TlaDsl/Examples/StreamletExec.lean` brings the FLTS bridge to the flagship
protocol — the roadmap's E1/E3 item. Streamlet's `Next` is a guarded
disjunction, so the executable form is label-indexed: a `Step` is one
protocol action (`Vote i b` or `Notarize b`), the step function applies
the update when the guard holds (`VoteGuard`/`NotarizeGuard`, extracted
from the bracket actions) and is the identity otherwise, and
`step_spec_tr` proves every FLTS transition is a `[Next n]_vars`-step — so
every `foldl` run of the step function is a protocol behavior. The
per-action facts are the two one-liners `vote_step_fires` /
`notarize_step_fires` ("under the guard, the action fires to the step")
and the determinism lemmas.

### Streamlet under Byzantine faults (2026-08-07)

`TlaDsl/Examples/StreamletByz.lean` — the safety core of BFT Streamlet:
quorums of size `> 2n/3` (`QuorumByz`), the Byzantine bound
`3 * Byz.card < n`, and `quorum_overlap_honest` — two notarizing quorums
share a node, and since the intersection is larger than the Byzantine set,
that node is honest. The protocol actions are guarded by `i ∉ Byz`
(`[c| ...]`-style), the invariant is the honest-restricted
`VoteLenMonoByz` (Byzantine votes are unconstrained), and the Byzantine
versions of Lemma 10 (`unique_notarization_byz`), finality-no-conflict and
Theorem 12 (`consistency_byz`) follow the same finality-chain argument as
the honest model, with the honest common voter at every overlap. This is
the BFT item on the north-star roadmap; the liveness half (honest-leader
epochs) and the CSLib FLP vocabulary link remain.

## 4. The one-paragraph takeaway

The DSL's notation is not the bottleneck anymore — the *proof plumbing* is:
two thirds of the liveness file is mechanical invariant-preservation and
suffix-index conversion. The highest-leverage work is therefore not more
notation but (a) an invariant-induction tactic that eats the frame cases,
and (b) a leads-to API that works at states instead of suffixes. Both are
pure automation on top of the existing semantics, both have the Streamlet
files as ready-made test cases, and together they would cut the liveness
file's mechanical overhead by roughly half.

Status: (a) is done — `tla_inv_step` eats the frame cases (36 → 11
bullets, −58 lines); (b) is done — `leadsTo_at`/`leadsTo_at_suffix`/
`inv_all_of_spec` (40 → 16 drop conversions, −84 lines). The remaining
mechanical overhead is the temporal wrapper's suffix-level conclusions,
which slice 5's mini-utilities should attack. Slice 4 is done too: goals
and hypotheses display state predicates and actions in `[p| ...]`/`[a| ...]`
form instead of lifted lambdas. Slice 5 is done: the P5 gotchas are
documented in `docs/gotchas.md` and two of them now have one-call
utilities (`tla_rcases_subst`, `tla_drop_simpa`), so the remaining
mechanical overhead is the temporal wrapper's suffix-level conclusions.
