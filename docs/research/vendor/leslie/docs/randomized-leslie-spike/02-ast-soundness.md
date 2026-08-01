# M0.3 — AST soundness scaffolding outline

**Status.** Stub builds; outline written.
**Owner.** TBD.
**Budget.** ~2 days planned; ~0.5 day actual (cut by M0.1's
finding that Doob is in Mathlib).
**Blocked by.** M0.1 (resolved). **Blocks.** M3 W1 startup.

---

## The question

Does `ASTCertificate.sound` actually go through against the M0.1
trace-measure type using Mathlib's available martingale convergence?

Round-2 finding 2 (design plan v2.1) flagged that the plan claimed to
defer measure theory but `ASTCertificate.sound` requires Doob, so the
deferral was suspect. M0.1 closed this by showing
`MeasureTheory.Martingale.Convergence` is in Mathlib (arXiv 2212.05578)
and the trace measure is direct from `Kernel.trajMeasure`. M0.3
discharges the remaining sanity check: write the certificate's full
`(V, U, term, …)` shape as a Lean structure plus a soundness
statement, and verify the obligations type-check under the chosen
trace type.

## Stub artifact

`Leslie/Prob/Spike/ASTSanity.lean` (108 lines). Builds green with
exactly one `sorry` (the `ASTCert.sound` body, planned). Key
declarations:

```lean
def AlmostSureTerm (μ : Measure Ω) (term : ℕ → Ω → Prop) : Prop :=
  ∀ᵐ ω ∂μ, ∃ n, term n ω

structure ASTCert (μ : Measure Ω) (ℱ : Filtration ℕ m)
    (V : ℕ → Ω → ℝ) (U : ℕ → Ω → ℕ) (term : ℕ → Ω → Prop) : Prop where
  V_super     : Supermartingale V ℱ μ
  V_nonneg    : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ V n ω
  V_term      : ∀ n, ∀ᵐ ω ∂μ, term n ω → V n ω = 0
  V_bdd       : ∃ R, ∀ n, eLpNorm (V n) 1 μ ≤ R
  U_bdd_subl  : ∀ r : ℝ, ∃ M : ℕ, ∀ n, ∀ᵐ ω ∂μ, V n ω ≤ r → U n ω ≤ M
  U_dec_prob  : ∀ r : ℝ, ∃ ε > 0, ∀ n, ∀ᵐ ω ∂μ, V n ω ≤ r → ¬ term n ω →
                  μ {ω' | U (n + 1) ω' < U n ω} ≥ ENNReal.ofReal ε

theorem ASTCert.sound [IsFiniteMeasure μ] (_ : ASTCert μ ℱ V U term) :
    AlmostSureTerm μ term := sorry
```

Every field's type checks. Mathlib's `Supermartingale`, `Filtration`,
`eLpNorm`, and the `∀ᵐ x ∂μ, _` / `IsFiniteMeasure` / `ENNReal`
machinery compose without surprise.

## Soundness proof outline (for M3 W1)

The soundness proof follows POPL 2025 §3 closely. Below: the four
steps and the specific Mathlib lemmas each one will use.

### Step 1 — Convert supermartingale `V` to L¹-bounded submartingale `-V`

A non-negative supermartingale `V` is bounded below by 0 and bounded
above in expectation by `eLpNorm (V 0) 1 μ` (the `V_bdd` field
provides a uniform bound `R`). Then `-V` is a submartingale, also
L¹-bounded.

Mathlib lemmas to use:
- `Supermartingale.neg : Supermartingale V ℱ μ → Submartingale (-V) ℱ μ`
  (in `Mathlib.Probability.Martingale.Basic`, search for `neg`).
- The L¹ bound transfers: `eLpNorm (-V n) 1 μ = eLpNorm (V n) 1 μ ≤ R`
  via `eLpNorm_neg`.

### Step 2 — Apply Doob's a.e. convergence to `-V`

```lean
theorem Submartingale.ae_tendsto_limitProcess
    [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hbdd : ∀ n, eLpNorm (f n) 1 μ ≤ R) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (ℱ.limitProcess f μ ω))
```

(File: `Mathlib.Probability.Martingale.Convergence`, line 209.)

Applied to `-V`, the conclusion is:

```
∀ᵐ ω ∂μ, Tendsto (fun n => -V n ω) atTop (𝓝 (ℱ.limitProcess (-V) μ ω))
```

Equivalently, `V n ω` converges a.s. to a finite limit `V_∞ ω :=
-ℱ.limitProcess (-V) μ ω`.

### Step 3 — Non-negativity bounds the limit in `[0, R]`

`V_nonneg` gives `0 ≤ V n ω` for almost every `ω`, every `n`. Taking
the limit, `0 ≤ V_∞ ω` a.s. The L¹ bound + Fatou's lemma gives the
upper bound (or directly: limit of bounded sequence is bounded).

Mathlib lemmas:
- `Filter.Tendsto.le_of_lt_eventually` for the lower bound on the
  limit.
- `Submartingale.memLp_limitProcess` (line 234 of Convergence.lean)
  to get the limit's L¹ bound.

### Step 4 — Sublevel-set compatibility forces termination

This is the main argument. On any sublevel set `{V ≤ r}`, `U_bdd_subl`
gives a uniform bound `U ≤ M_r`. On the complement of terminating
trajectories, `U_dec_prob` says `U` strictly decreases at a positive
rate. A finite-state ℕ-valued process that strictly decreases at a
positive rate cannot stay above 0 indefinitely.

Formalized:

(a) Define the event `A_r := {ω | ∀ n, V n ω ≤ r ∧ ¬ term n ω}` —
trajectories that stay bounded by `r` and never terminate.

(b) On `A_r`, `U n ω ≤ M_r` for all `n`. Combined with `U_dec_prob`,
the process `U n` makes a strict decrease at rate `≥ ε > 0` on this
event. By a Borel-Cantelli argument on the events `B_n := {U_{n+1} <
U_n} ∩ A_r`, infinitely many decreases happen a.s. — but `U` is
bounded below by 0 and `M_r`-bounded above, so it can decrease
finitely many times. Contradiction → `μ A_r = 0`.

(c) Take a union over rational `r`: `μ ⋃_{r ∈ ℚ} A_r = 0`. By Step 3,
`V_∞ < ∞` a.s., so a.s. some sublevel `r` contains the trajectory's
tail. Hence a.s. either the trajectory terminates or it lies in some
`A_r` (which has measure 0). Conclusion: `AlmostSureTerm μ term`.

Mathlib lemmas:
- `Probability.Martingale.BorelCantelli` (file
  `Mathlib.Probability.Martingale.BorelCantelli`) for the second
  Borel-Cantelli lemma in martingale form.
- `MeasureTheory.measure_iUnion_null` for the rational-union step.

## What the stub validated

1. **`Supermartingale` is real-valued and adapted to `Filtration`.**
   No surprise; matches the design-plan signatures.
2. **`eLpNorm` (instead of `Lp` or `L1` ascription) is the right
   handle for the boundedness predicate.** Compiles directly from
   `Mathlib.MeasureTheory.Function.LpSeminorm.Basic` (transitively
   imported by `Convergence`).
3. **`∀ᵐ` is `Filter.Eventually` against `μ.ae`** and composes
   trivially with the `→` and `≤` shapes used in the certificate.
4. **`ENNReal.ofReal ε` is the right coercion** for `μ {ω' | …} ≥ ε`,
   since `μ`'s codomain is `ℝ≥0∞`. We do *not* need a separate
   `Probability` pred class for `ε > 0`.
5. **`IsFiniteMeasure μ`** is the typeclass `ASTCert.sound` requires.
   On the M0.1 trace measure `coinTrace μ₀`, the `IsProbabilityMeasure`
   instance from Mathlib subsumes `IsFiniteMeasure`, so the soundness
   theorem applies directly.

## Mathlib gaps (none load-bearing)

- Mathlib has `Submartingale.ae_tendsto_limitProcess` directly. No
  shim needed for the headline convergence step. (M0.1 was already
  optimistic about this; M0.3 confirmed it.)
- Mathlib does not have a dedicated `Supermartingale.ae_tendsto`; the
  paper trail is `Supermartingale.neg → Submartingale` and reuse
  `Submartingale.ae_tendsto_limitProcess`. ~3-5 lines of glue.
- The Borel-Cantelli step in stage 4 uses
  `Mathlib.Probability.Martingale.BorelCantelli` which requires a
  predictable filtration. The natural filtration on the coordinate
  process is predictable, so this is fine; M3 W1 will need the
  `IsPredictable` instance derivation, ~10 lines.

## Implications for the wider plan

- **M3 W1 estimate confirmed.** The "small shim, ~200 lines worst
  case" budget in the design plan was conservative; actual shim work
  is more like ~50 lines (Supermartingale-to-Submartingale conversion,
  predictable-filtration witness, sublevel-set Borel-Cantelli
  application). The non-trivial work is in the case analysis of
  Step 4, not in plumbing Mathlib.
- **Design plan v2.1 §"Risk register" entry "Mathlib martingale-
  convergence gap"** can be marked Resolved with a pointer to this
  outline.
- **Implementation plan v2.1 M3 W1 reading list** stays as-is
  (POPL 2025 §3 + Lemma 3.2 proof structure). Add a pointer to this
  outline.
- **No design-plan signature change needed.** `ASTCertificate` /
  `FairASTCertificate` already operate at the right abstraction; the
  M0.3 stub is a shape-preserving instantiation against the trace
  measure.

## Outstanding for M3 W1

1. Promote `ASTCert` from the spike file to `Leslie/Prob/Liveness.lean`
   with the full POPL 2025 fields (split deterministic-step and
   probabilistic-step variants of `U`'s decrease; that distinction
   is on the design plan but elided here).
2. Replace `Ω, ℱ, μ` with the concrete `coinTrace μ₀, coordFiltration,
   μ` once `coordFiltration` lands (deferred from M0.3 because it
   needs `MetrizableSpace` plumbing on `X n` per `Filtration.natural`).
3. Discharge the soundness `sorry` with the four-step outline above.
4. Layer `FairASTCertificate` on top per POPL 2026.

## References

- [Mathlib.Probability.Martingale.Convergence](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Martingale/Convergence.html)
  — `Submartingale.ae_tendsto_limitProcess` at line 209 in v4.27.0.
- [Mathlib.Probability.Martingale.BorelCantelli](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Martingale/BorelCantelli.html)
  — second Borel-Cantelli for predictable filtrations.
- [Mathlib.Probability.Process.Filtration](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Process/Filtration.html)
  — `Filtration`, `Filtration.natural`, `Filtration.limitProcess`.
- [Mathlib.Probability.Martingale.Basic](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Martingale/Basic.html)
  — `Supermartingale`, `Submartingale`, `.neg` conversion.
- POPL 2025 §3 — Majumdar–Sathiyanarayana, two-function AST rule.
- arXiv:2212.05578 — Pflanzer & Bentkamp, Doob's convergence in Mathlib.
