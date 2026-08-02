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
  formulas), implemented by pointwise-lifting macros.
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
   (`StrongFair.lean`) is back in bracket syntax. Remaining gaps: binders
   (`∃ x ∈ S, ...`), `if-then-else`, qualified names. Options: grow the macro
   further (fragile), or switch to a small custom elaborator / dedicated
   syntax category with real grammar.
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
