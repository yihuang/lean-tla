/-
M2.7 — Synchronous BGW-style VSS as a `ProbActionSpec`.

This module models a BGW '88 verifiable secret sharing protocol
(`n` parties, `≤ t` Byzantine faults) over a synchronous broadcast
channel as a `Leslie.Prob.ProbActionSpec`. The protocol is a
3-round share / consistency-check / resolve schedule over a
*single* dealer-sampled bivariate polynomial.

**Note on the threshold `n ≥ 3t + 1`.** The standard BGW security
threshold is needed for liveness and correct reconstruction (so a
corrupt dealer cannot equivocate beyond honest-quorum overlap).
The present module proves four invariants — `roundBounded_AS`,
`correctness_AS`, `outputDeterminedInv_AS`, `secrecy_grid` — none
of which take any `n`/`t` numeric premise. The threshold becomes
load-bearing only once the model wires real dealer-resolution
semantics and almost-sure termination, both of which are M3 work
(see deferred items in §10 and §12). The current statements hold
even with `n = 0`; they constrain the deterministic relationship
between the dealer's `coeffs` and honest outputs, not the
adversary's power to disrupt.

## Design choice: randomness in `μ₀`, coefficient matrix in state

The dealer's only randomness is the bivariate polynomial `F`,
parameterized by its coefficient matrix
`coeffs : Fin (t+1) → Fin (t+1) → F` with `coeffs 0 0 = secret`
(for an honest dealer). For the `AlmostBox_of_pure_inductive`
bridge to apply cleanly, every action's `effect` must be a Dirac
(`PMF.pure`). We achieve this by **pushing the randomness into
the initial measure** `μ₀`:

  * `μ₀` is the pushforward of `PMF.uniform (Fin t → Fin t → F)`
    into a state record where `coeffs` carries the sampled matrix,
    every party's local state is empty, and `round = .init`.
  * Every protocol action is then a deterministic function of the
    state, including reading `coeffs` for share derivation.

This is the same pattern as `BrachaRBC.lean`: the initial measure
carries the entropy, the step kernel is a Dirac everywhere.

**Why coefficient matrix, not `Polynomial (Polynomial F)`.**
`Polynomial F` over a finite field is countable but Mathlib does
not provide the `Countable` instance directly. Storing the
coefficient matrix `Fin (t+1) → Fin (t+1) → F` in state keeps the
state `Fintype` (hence `Countable`), satisfying the prerequisites
of `AlmostBox_of_pure_inductive`. The bivariate evaluation
`F(α_i, α_j) = ∑_{k,l} coeffs k l * α_i^k * α_j^l` is computed
explicitly without invoking the `Polynomial` library.

## Protocol

  * **Round 1 (share).** Dealer broadcasts `f_i(y) := F(α_i, y)`
    and `g_i(x) := F(x, α_i)` to each party `i`, where
    `α_i = partyPoint i`. We model this as the dealer revealing
    `coeffs` to all parties (the dealer's intended share is then
    derivable on demand).
  * **Round 2 (consistency).** Each party `i` "sends" its
    `f_i(α_j)` to each `j`. Party `j` checks
    `g_j(α_i) =? f_i(α_j)`. We model this as each party emitting
    its own row-eval table; mismatches generate complaints.
  * **Round 3 (resolve).** For each complained `(i, j)`, the dealer
    broadcasts `F(α_i, α_j)`. Honest parties cross-check; if the
    dealer's broadcast disagrees with any honest party's polynomial,
    the dealer is *exposed* and the protocol output defaults to `0`.
  * **Reconstruction.** Each party broadcasts its full polynomial
    `f_i`; honest parties Lagrange-interpolate to recover
    `F(0, 0) = coeffs 0 0`.

## Theorems (status)

  * `roundBounded_AS` — round-stage encoding is bounded throughout
    any execution. **Closed.**
  * `correctness_AS` — if the dealer is honest, every honest party's
    reconstruction output equals the dealer's secret. Lifted via
    `AlmostBox_of_pure_inductive` against the inductive invariant
    "every honest party's view is consistent with `coeffs`".
    **Closed.**
  * `outputDeterminedInv_AS` — even with a corrupt dealer, every honest
    party's output is either `0` (on exposure) or
    `bivEval coeffs 0 0`. **Closed.**
  * `secrecy_grid` — grid-view secrecy: the post-share `(C × D)`-grid
    distribution depends only on the coalitions, not on the secret.
    Direct application of `bivariate_shamir_secrecy`.
    **Closed (grid form, option (b) per the M2.7 brief).**

The full row+column view secrecy (a strict generalization of the
grid form) is deferred — see the closing remark in §10 below.

Per implementation plan v2.2 §M2.7 + design plan v2.2 §M2.7.
-/

import Leslie.Examples.Prob.BivariateShamir
import Leslie.Prob.Action
import Leslie.Prob.Adversary
import Leslie.Prob.Trace
import Leslie.Prob.Refinement
import Leslie.Prob.PMF
import Leslie.Prob.Polynomial
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Countable.Defs

namespace Leslie.Examples.Prob.SyncVSS

open Leslie.Prob MeasureTheory

/-! ## §0. Parameters

`n` parties, threshold `t`, finite field `F` with `partyPoint`
embedding `Fin n → F` avoiding 0. The default value emitted on
dealer-exposure is `0`. -/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {n t : ℕ}

/-! ## §1. State machine -/

/-- Protocol round indicator. Drives action gates. -/
inductive Round
  | init        -- before the dealer has sampled / written shares
  | share       -- dealer's row/col polynomials are written; shares delivered
  | consistency -- consistency-check phase active
  | resolve     -- dealer-resolve phase active
  | reconstruct -- reconstruction phase
  | done
  deriving DecidableEq, Repr, Fintype

/-- A complaint records that party `i`'s consistency check against
party `j` failed: party `i` claims `f_i(α_j) = value` but
`g_j(α_i) ≠ value`. Both `i` and `j` broadcast such complaints
during round 2. -/
structure Complaint (n : ℕ) (F : Type*) where
  i     : Fin n
  j     : Fin n
  value : F
  deriving DecidableEq

/-- A dealer-resolution: dealer broadcasts `F(α_i, α_j)` for each
prior complaint `(i, j)`. -/
structure Resolution (n : ℕ) (F : Type*) where
  i     : Fin n
  j     : Fin n
  value : F
  deriving DecidableEq

/-- Per-party local state.

  * `received : Bool` — whether the dealer has dealt this party a
    share (i.e., the dealer has revealed `coeffs`).
  * `complaints : Finset (Complaint n F)` — complaints this party
    has heard or generated.
  * `resolutions : Finset (Resolution n F)` — dealer's resolution
    broadcasts heard.
  * `output : Option F` — the reconstructed secret (or 0 on exposure).
    `none` until reconstruction completes.
  * `dealerExposed : Bool` — true iff this party has seen a dealer
    resolution that contradicts its own polynomial. Always `false`
    in this synchronous-broadcast deterministic model (the dealer's
    resolution is computed from the same `coeffs` the parties see).
-/
structure LocalState (n : ℕ) (F : Type*) [DecidableEq F] where
  received      : Bool
  complaints    : Finset (Complaint n F)
  resolutions   : Finset (Resolution n F)
  output        : Option F
  dealerExposed : Bool

namespace LocalState

/-- The empty per-party state at protocol start. -/
def init (n : ℕ) (F : Type*) [DecidableEq F] : LocalState n F :=
  { received := false
    complaints := ∅
    resolutions := ∅
    output := none
    dealerExposed := false }

end LocalState

/-- The global protocol state.

  * `coeffs : Fin (t+1) → Fin (t+1) → F` — the dealer's bivariate
    polynomial coefficients. Sampled once into `μ₀`; not modified
    after.
  * `secret : F` — the dealer's intended secret (`coeffs 0 0` for
    an honest dealer). **Currently unused in any predicate or
    invariant** — `correctness_AS` reads `coeffs 0 0` directly.
    Retained only for the `initPred` constraint that pins the
    dealer's secret at start-of-execution; downstream proofs all
    project to `coeffs`. Slated for removal once the row+column
    secrecy form lands in M3.
  * `local_ : Fin n → LocalState n F` — per-party state.
  * `round : Round` — current protocol round.
  * `corrupted : Finset (Fin n)` — adversarial parties (static).
  * `dealerHonest : Bool` — whether the dealer is honest. Tracked
    on the state for ease of correctness statements.
  * `pendingComplaints : Finset (Complaint n F)` — complaints
    broadcast in round 2, used to drive round 3 resolution actions.
  * `pendingResolutions : Finset (Resolution n F)` — dealer
    resolutions emitted, broadcast in round 3.
-/
structure State (n t : ℕ) (F : Type*) [DecidableEq F] where
  coeffs             : Fin (t+1) → Fin (t+1) → F
  secret             : F
  local_             : Fin n → LocalState n F
  round              : Round
  corrupted          : Finset (Fin n)
  dealerHonest       : Bool
  pendingComplaints  : Finset (Complaint n F)
  pendingResolutions : Finset (Resolution n F)

namespace State

/-- Whether party `p` is honest in state `s`. -/
def isHonest [DecidableEq F] (s : State n t F) (p : Fin n) : Prop :=
  p ∉ s.corrupted

instance [DecidableEq F] (s : State n t F) (p : Fin n) :
    Decidable (s.isHonest p) :=
  inferInstanceAs (Decidable (p ∉ s.corrupted))

end State

/-! ## §2. Bivariate evaluation

The dealer's bivariate polynomial `F(x, y) := ∑_{k,l} coeffs k l * x^k * y^l`
evaluated at `(α_i, α_j)`. -/

/-- Bivariate evaluation of `coeffs` at `(x, y)` in `F`. -/
def bivEval (coeffs : Fin (t+1) → Fin (t+1) → F) (x y : F) : F :=
  ∑ k : Fin (t+1), ∑ l : Fin (t+1), coeffs k l * x ^ k.val * y ^ l.val

/-- The dealer's `f_i(y) = F(α_i, y)` evaluated at `y`. -/
def rowEval (partyPoint : Fin n → F) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (i : Fin n) (y : F) : F :=
  bivEval coeffs (partyPoint i) y

/-- The dealer's `g_j(x) = F(x, α_j)` evaluated at `x`. -/
def colEval (partyPoint : Fin n → F) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (j : Fin n) (x : F) : F :=
  bivEval coeffs x (partyPoint j)

/-- The dealer's intended `F(α_i, α_j)` value. -/
def crossEval (partyPoint : Fin n → F) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (i j : Fin n) : F :=
  bivEval coeffs (partyPoint i) (partyPoint j)

/-! ## §3. Initial-state predicate -/

/-- The protocol's initial-state predicate (parameterized by the
secret and the corruption set). -/
def initPred (sec : F) (corr : Finset (Fin n))
    (s : State n t F) : Prop :=
  (∀ p, s.local_ p = LocalState.init n F) ∧
  s.round = .init ∧
  s.secret = sec ∧
  s.corrupted = corr ∧
  s.pendingComplaints = ∅ ∧
  s.pendingResolutions = ∅ ∧
  -- If the dealer is honest, `coeffs 0 0 = secret`.
  (s.dealerHonest = true → s.coeffs 0 0 = sec)

/-! ## §4. Actions -/

/-- The protocol's action labels. -/
inductive Action (n : ℕ) (F : Type*) [DecidableEq F]
  | deal
  | consistencyAdvance
  | complain (i j : Fin n) (v : F)
  | resolveOpen
  | dealerResolve (i j : Fin n)
  | partyApplyResolution (p : Fin n) (i j : Fin n)
  | reconstructOpen
  | reconstructAt (p : Fin n)

/-! ## §5. Deterministic next-state function -/

/-- Functional update for `local_`: replace party `p`'s local state. -/
def setLocal (s : State n t F) (p : Fin n) (ls : LocalState n F) :
    State n t F :=
  { s with local_ := fun q => if q = p then ls else s.local_ q }

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_local_self (s : State n t F) (p : Fin n)
    (ls : LocalState n F) :
    (setLocal s p ls).local_ p = ls := by
  simp [setLocal]

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_local_ne (s : State n t F) (p q : Fin n)
    (ls : LocalState n F) (h : q ≠ p) :
    (setLocal s p ls).local_ q = s.local_ q := by
  simp [setLocal, h]

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_round (s : State n t F) (p : Fin n)
    (ls : LocalState n F) :
    (setLocal s p ls).round = s.round := rfl

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_coeffs (s : State n t F) (p : Fin n)
    (ls : LocalState n F) :
    (setLocal s p ls).coeffs = s.coeffs := rfl

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_secret (s : State n t F) (p : Fin n)
    (ls : LocalState n F) :
    (setLocal s p ls).secret = s.secret := rfl

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_corrupted (s : State n t F) (p : Fin n)
    (ls : LocalState n F) :
    (setLocal s p ls).corrupted = s.corrupted := rfl

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_dealerHonest (s : State n t F) (p : Fin n)
    (ls : LocalState n F) :
    (setLocal s p ls).dealerHonest = s.dealerHonest := rfl

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_pendingComplaints (s : State n t F) (p : Fin n)
    (ls : LocalState n F) :
    (setLocal s p ls).pendingComplaints = s.pendingComplaints := rfl

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_pendingResolutions (s : State n t F) (p : Fin n)
    (ls : LocalState n F) :
    (setLocal s p ls).pendingResolutions = s.pendingResolutions := rfl

/-- The deterministic next-state function. Each branch is gated by
`actionGate` (defined below); when the gate fails, this function
is allowed to return arbitrary values (in practice we return `s`
unchanged), hidden by the spec's gate. -/
def vssStep (a : Action n F) (s : State n t F) : State n t F :=
  match a with
  | .deal =>
      { s with
        round := .share
        local_ := fun _ =>
          { received := true
            complaints := ∅
            resolutions := ∅
            output := none
            dealerExposed := false } }
  | .consistencyAdvance =>
      { s with round := .consistency }
  | .complain i j v =>
      { s with
        pendingComplaints := insert ⟨i, j, v⟩ s.pendingComplaints }
  | .resolveOpen =>
      { s with round := .resolve }
  | .dealerResolve _ _ =>
      -- Dealer broadcasts F(α_i, α_j); modeled by leaving
      -- `pendingResolutions` unchanged (the resolution is implicit
      -- via `crossEval`-recomputable). We keep this branch
      -- structurally for proof-shape parity.
      s
  | .partyApplyResolution p _ _ =>
      -- Party `p` adopts the dealer's view; in our deterministic
      -- model with `crossEval` shared via state, the "exposure" check
      -- is identically false, so this is a no-op on `dealerExposed`.
      let ls := s.local_ p
      let ls' : LocalState n F :=
        { ls with resolutions := s.pendingResolutions ∪ ls.resolutions }
      setLocal s p ls'
  | .reconstructOpen =>
      { s with round := .reconstruct }
  | .reconstructAt p =>
      let ls := s.local_ p
      let out : F :=
        if ls.dealerExposed then 0 else s.coeffs 0 0
      let ls' : LocalState n F :=
        { ls with output := some out }
      setLocal s p ls'

/-! ## §6. Action gates and spec -/

/-- Action gate predicates. -/
def actionGate (a : Action n F) (s : State n t F) : Prop :=
  match a with
  | .deal                       => s.round = .init
  | .consistencyAdvance         => s.round = .share
  | .complain _ _ _             => s.round = .consistency
  | .resolveOpen                => s.round = .consistency
  | .dealerResolve _ _          => s.round = .resolve
  | .partyApplyResolution _ _ _ => s.round = .resolve
  | .reconstructOpen            => s.round = .resolve
  | .reconstructAt p            =>
      s.round = .reconstruct ∧ (s.local_ p).output = none

/-- The probabilistic VSS spec.

The randomness lives entirely in `μ₀`: every `effect` is a Dirac
on `vssStep`. -/
noncomputable def vssProb (sec : F) (corr : Finset (Fin n)) :
    ProbActionSpec (State n t F) (Action n F) where
  init := initPred sec corr
  actions := fun a =>
    { gate := actionGate a
      effect := fun s _ => PMF.pure (vssStep a s) }

omit [Fintype F] in
/-- Step is a Dirac on `vssStep`. -/
@[simp] theorem vssProb_step_pure (sec : F) (corr : Finset (Fin n))
    (a : Action n F) (s : State n t F)
    (h : actionGate a s) :
    (vssProb (t := t) sec corr).step a s
      = some (PMF.pure (vssStep a s)) :=
  ProbActionSpec.step_eq_some h

omit [Fintype F] in
theorem vssProb_step_none (sec : F) (corr : Finset (Fin n))
    (a : Action n F) (s : State n t F)
    (h : ¬ actionGate a s) :
    (vssProb (t := t) sec corr).step a s = none :=
  ProbActionSpec.step_eq_none h

/-! ## §7. Typeclasses for `traceDist` lifting

`AlmostBox` requires `Countable σ`, `Countable ι`, plus a
`MeasurableSingletonClass`. With the coefficient-matrix design,
every field of `State` and `Action` has finite components under
`[Fintype F]`, so both types are `Fintype` (hence `Countable`). -/

section Measurable

instance : MeasurableSpace (State n t F) := ⊤
instance : MeasurableSingletonClass (State n t F) := ⟨fun _ => trivial⟩
instance : MeasurableSpace (Action n F) := ⊤
instance : MeasurableSingletonClass (Action n F) := ⟨fun _ => trivial⟩

/-- `Action n F` is `Fintype` under `[Fintype F]`. -/
noncomputable instance : Fintype (Action n F) := by
  classical
  exact Fintype.ofEquiv
    (Unit ⊕ Unit ⊕ (Fin n × Fin n × F) ⊕ Unit ⊕
      (Fin n × Fin n) ⊕ (Fin n × Fin n × Fin n) ⊕ Unit ⊕ Fin n)
    { toFun := fun
        | .inl _ => .deal
        | .inr (.inl _) => .consistencyAdvance
        | .inr (.inr (.inl ⟨i, j, v⟩)) => .complain i j v
        | .inr (.inr (.inr (.inl _))) => .resolveOpen
        | .inr (.inr (.inr (.inr (.inl ⟨i, j⟩)))) => .dealerResolve i j
        | .inr (.inr (.inr (.inr (.inr (.inl ⟨p, i, j⟩))))) =>
            .partyApplyResolution p i j
        | .inr (.inr (.inr (.inr (.inr (.inr (.inl _)))))) =>
            .reconstructOpen
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr p)))))) =>
            .reconstructAt p
      invFun := fun
        | .deal => .inl ()
        | .consistencyAdvance => .inr (.inl ())
        | .complain i j v => .inr (.inr (.inl ⟨i, j, v⟩))
        | .resolveOpen => .inr (.inr (.inr (.inl ())))
        | .dealerResolve i j =>
            .inr (.inr (.inr (.inr (.inl ⟨i, j⟩))))
        | .partyApplyResolution p i j =>
            .inr (.inr (.inr (.inr (.inr (.inl ⟨p, i, j⟩)))))
        | .reconstructOpen =>
            .inr (.inr (.inr (.inr (.inr (.inr (.inl ()))))))
        | .reconstructAt p =>
            .inr (.inr (.inr (.inr (.inr (.inr (.inr p))))))
      left_inv := fun
        | .inl _ => rfl
        | .inr (.inl _) => rfl
        | .inr (.inr (.inl _)) => rfl
        | .inr (.inr (.inr (.inl _))) => rfl
        | .inr (.inr (.inr (.inr (.inl _)))) => rfl
        | .inr (.inr (.inr (.inr (.inr (.inl _))))) => rfl
        | .inr (.inr (.inr (.inr (.inr (.inr (.inl _)))))) => rfl
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr _)))))) => rfl
      right_inv := fun
        | .deal => rfl
        | .consistencyAdvance => rfl
        | .complain _ _ _ => rfl
        | .resolveOpen => rfl
        | .dealerResolve _ _ => rfl
        | .partyApplyResolution _ _ _ => rfl
        | .reconstructOpen => rfl
        | .reconstructAt _ => rfl }

instance : Countable (Action n F) := Finite.to_countable

/-- `Complaint n F` and `Resolution n F` are `Fintype`. -/
noncomputable instance : Fintype (Complaint n F) := by
  classical
  exact Fintype.ofEquiv (Fin n × Fin n × F)
    { toFun := fun ⟨i, j, v⟩ => ⟨i, j, v⟩
      invFun := fun c => ⟨c.i, c.j, c.value⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

noncomputable instance : Fintype (Resolution n F) := by
  classical
  exact Fintype.ofEquiv (Fin n × Fin n × F)
    { toFun := fun ⟨i, j, v⟩ => ⟨i, j, v⟩
      invFun := fun r => ⟨r.i, r.j, r.value⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- `LocalState n F` is `Fintype`. -/
noncomputable instance : Fintype (LocalState n F) := by
  classical
  exact Fintype.ofEquiv
    (Bool × Finset (Complaint n F) × Finset (Resolution n F)
      × Option F × Bool)
    { toFun := fun ⟨r, c, rs, o, e⟩ => ⟨r, c, rs, o, e⟩
      invFun := fun ls =>
        (ls.received, ls.complaints, ls.resolutions, ls.output,
         ls.dealerExposed)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance : Countable (LocalState n F) := Finite.to_countable

/-- `State n t F` is `Fintype` under `[Fintype F]`. -/
noncomputable instance : Fintype (State n t F) := by
  classical
  exact Fintype.ofEquiv
    ((Fin (t+1) → Fin (t+1) → F) × F × (Fin n → LocalState n F)
      × Round × Finset (Fin n) × Bool
      × Finset (Complaint n F) × Finset (Resolution n F))
    { toFun := fun ⟨c, sec, l, r, corr, dh, pc, pr⟩ =>
        ⟨c, sec, l, r, corr, dh, pc, pr⟩
      invFun := fun s =>
        (s.coeffs, s.secret, s.local_, s.round, s.corrupted,
         s.dealerHonest, s.pendingComplaints, s.pendingResolutions)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance : Countable (State n t F) := Finite.to_countable

end Measurable

/-! ## §8. Termination invariant

The protocol's `round` field traces a strict path through
`init → share → consistency → resolve → reconstruct → done`.
Termination as deterministic 3-round bound is captured here as the
trivial `roundBounded` invariant — `round`'s ordinal is bounded by
5. Reaching `.done` is a *liveness* property requiring fairness
(M3 work). -/

/-- Monotone numeric encoding of the round. -/
def roundOrd : Round → ℕ
  | .init => 0
  | .share => 1
  | .consistency => 2
  | .resolve => 3
  | .reconstruct => 4
  | .done => 5

/-- The "round ordering is bounded" invariant: trivially true for
all states, demonstrated as a warmup for the AlmostBox machinery. -/
def roundBounded (s : State n t F) : Prop :=
  roundOrd s.round ≤ 5

omit [Field F] [Fintype F] in
theorem roundBounded_all (s : State n t F) : roundBounded s := by
  cases hr : s.round <;> unfold roundBounded <;> rw [hr] <;> decide

omit [Fintype F] in
theorem vssStep_preserves_roundBounded (a : Action n F) (s : State n t F) :
    roundBounded s → roundBounded (vssStep a s) := by
  intro _; exact roundBounded_all _

omit [Fintype F] in
theorem initPred_roundBounded (sec : F) (corr : Finset (Fin n))
    (s : State n t F) (_h : initPred sec corr s) : roundBounded s :=
  roundBounded_all s

set_option maxHeartbeats 800000 in
/-- The round ordering is bounded throughout any execution. -/
theorem roundBounded_AS
    (sec : F) (corr : Finset (Fin n))
    (μ₀ : Measure (State n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr s)
    (A : Adversary (State n t F) (Action n F)) :
    AlmostBox (vssProb (t := t) sec corr) A μ₀ roundBounded := by
  have h_pure : ∀ (a : Action n F) (s : State n t F)
      (h : ((vssProb (t := t) sec corr).actions a).gate s),
      ((vssProb (t := t) sec corr).actions a).effect s h
        = PMF.pure (vssStep a s) :=
    fun _ _ _ => rfl
  have h_init' : ∀ᵐ s ∂μ₀, roundBounded s := by
    filter_upwards [h_init] with s hs
    exact initPred_roundBounded sec corr s hs
  exact AlmostBox_of_pure_inductive
    roundBounded
    (fun a s => vssStep a s)
    h_pure
    (fun a s _ h => vssStep_preserves_roundBounded a s h)
    μ₀ h_init' A

/-! ## §9. Correctness

If the dealer is honest with secret `sec`, every honest party's
reconstruction output equals `sec`.

Inductive invariant (`honestDealerInv`): under honest dealer,
  1. `coeffs 0 0 = sec`,
  2. every honest party's `dealerExposed` is `false` (the
     deterministic resolve action never sets it),
  3. every honest party's `output`, if set, equals `sec`.
-/

/-- Property: if dealer honest, every set output of an honest party
equals `sec`. -/
def correctness_pred (sec : F) (s : State n t F) : Prop :=
  s.dealerHonest = true →
    s.coeffs 0 0 = sec ∧
    ∀ p, p ∉ s.corrupted → ∀ v, (s.local_ p).output = some v → v = sec

/-- The full honest-dealer invariant. -/
def honestDealerInv (sec : F) (s : State n t F) : Prop :=
  s.dealerHonest = true →
    s.coeffs 0 0 = sec ∧
    (∀ p, p ∉ s.corrupted →
      (s.local_ p).dealerExposed = false ∧
      (∀ v, (s.local_ p).output = some v → v = sec))

omit [Field F] [Fintype F] in
theorem initPred_honestDealerInv (sec : F) (corr : Finset (Fin n))
    (s : State n t F) (h : initPred sec corr s) :
    honestDealerInv sec s := by
  intro hh
  obtain ⟨hloc, _, _, _, _, _, hF⟩ := h
  refine ⟨hF hh, ?_⟩
  intro p _
  rw [hloc p]
  exact ⟨rfl, by intro v hv; simp [LocalState.init] at hv⟩

set_option maxHeartbeats 1200000 in
omit [Fintype F] in
theorem vssStep_preserves_honestDealerInv (sec : F)
    (a : Action n F) (s : State n t F)
    (_hgate : actionGate a s)
    (hinv : honestDealerInv sec s) :
    honestDealerInv sec (vssStep a s) := by
  intro hh
  -- Dealer-honest is preserved by every action (it's not modified).
  have hh_pre : s.dealerHonest = true := by
    cases a <;> simp [vssStep] at hh <;> exact hh
  obtain ⟨hsec, hperp⟩ := hinv hh_pre
  cases a with
  | deal =>
      refine ⟨hsec, ?_⟩
      intro p hp
      refine ⟨?_, ?_⟩
      · -- (vssStep deal s).local_ p .dealerExposed = false
        show false = false
        rfl
      · intro v hv
        -- (vssStep deal s).local_ p .output = some v contradicts output = none
        exfalso
        revert hv
        simp [vssStep]
  | consistencyAdvance | complain _ _ _ | resolveOpen
  | dealerResolve _ _ | reconstructOpen =>
      -- Frame: action doesn't touch `coeffs` or `local_.{dealerExposed, output}`.
      simp only [vssStep] at hh ⊢
      exact ⟨hsec, hperp⟩
  | partyApplyResolution p _ _ =>
      simp only [vssStep] at hh ⊢
      refine ⟨hsec, ?_⟩
      intro q hq
      obtain ⟨hexp_q, hout_q⟩ := hperp q hq
      by_cases hqp : q = p
      · subst hqp; rw [setLocal_local_self]; exact ⟨hexp_q, hout_q⟩
      · rw [setLocal_local_ne _ _ _ _ hqp]; exact ⟨hexp_q, hout_q⟩
  | reconstructAt p =>
      simp only [vssStep] at hh ⊢
      refine ⟨hsec, ?_⟩
      intro q hq
      obtain ⟨hexp_q, hout_q⟩ := hperp q hq
      by_cases hqp : q = p
      · subst hqp
        rw [setLocal_local_self]
        refine ⟨hexp_q, ?_⟩
        intro v hv
        simp at hv
        rw [hexp_q] at hv
        simp at hv
        rw [← hv]; exact hsec
      · rw [setLocal_local_ne _ _ _ _ hqp]; exact ⟨hexp_q, hout_q⟩

set_option maxHeartbeats 800000 in
/-- Correctness as an `AlmostBox`. -/
theorem correctness_AS
    (sec : F) (corr : Finset (Fin n))
    (μ₀ : Measure (State n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr s)
    (A : Adversary (State n t F) (Action n F)) :
    AlmostBox (vssProb (t := t) sec corr) A μ₀
      (correctness_pred sec) := by
  have h_pure : ∀ (a : Action n F) (s : State n t F)
      (h : ((vssProb (t := t) sec corr).actions a).gate s),
      ((vssProb (t := t) sec corr).actions a).effect s h
        = PMF.pure (vssStep a s) :=
    fun _ _ _ => rfl
  have h_init' : ∀ᵐ s ∂μ₀, honestDealerInv sec s := by
    filter_upwards [h_init] with s hs
    exact initPred_honestDealerInv sec corr s hs
  have h_inv : AlmostBox (vssProb (t := t) sec corr) A μ₀
      (honestDealerInv sec) :=
    AlmostBox_of_pure_inductive
      (honestDealerInv sec)
      (fun a s => vssStep a s)
      h_pure
      (fun a s hgate hinv =>
        vssStep_preserves_honestDealerInv sec a s hgate hinv)
      μ₀ h_init' A
  unfold AlmostBox at h_inv ⊢
  filter_upwards [h_inv] with ω hinv k
  intro hh
  obtain ⟨hsec, hperp⟩ := hinv k hh
  refine ⟨hsec, ?_⟩
  intro p hp v hv
  exact (hperp p hp).2 v hv

/-! ## §10. Output-determined invariant (proxy for commitment)

Every honest party's output (after the deterministic reconstruction
step) is uniquely determined by the dealer's `coeffs 0 0` (or `0`
when the dealer is exposed). This is a *weak* invariant form of
commitment: it shows the output is read deterministically from the
dealer's choice of `coeffs`, so no equivocation across honest
parties is possible.

**Strength caveat.** The current deterministic model never actually
sets `dealerExposed = true` (the `dealerResolve` action is a stub
and `partyApplyResolution` only ORs an always-empty resolution
set). So the `vp = 0` disjunct is provably vacuous, and the
invariant collapses to "every honest output is `coeffs 0 0`",
which is the same content as `correctness_AS` modulo the
honest-dealer hypothesis. The full equivocation-resistance content
of standard VSS commitment (with a corrupt dealer that may emit
inconsistent shares) is M3 work — when the model wires real
dealer-resolution semantics, this invariant gains its full force.

The name was changed from `commitmentInv` to `outputDeterminedInv`
to reflect what's actually proved. -/

/-- Output-determined invariant: every honest party's output, if
set, is either `0` (dealer-exposed) or `coeffs 0 0`. -/
def outputDeterminedInv (s : State n t F) : Prop :=
  ∀ p, p ∉ s.corrupted → ∀ vp, (s.local_ p).output = some vp →
    vp = 0 ∨ vp = s.coeffs 0 0

omit [Fintype F] in
theorem initPred_outputDeterminedInv (sec : F) (corr : Finset (Fin n))
    (s : State n t F) (h : initPred sec corr s) :
    outputDeterminedInv s := by
  intro p _ vp hvp
  obtain ⟨hloc, _⟩ := h
  rw [hloc p] at hvp
  simp [LocalState.init] at hvp

omit [Fintype F] in
theorem vssStep_preserves_outputDeterminedInv (a : Action n F) (s : State n t F) :
    outputDeterminedInv s → outputDeterminedInv (vssStep a s) := by
  intro hinv p hp vp hvp
  cases a with
  | deal =>
      simp [vssStep] at hvp
  | consistencyAdvance | complain _ _ _ | resolveOpen
  | dealerResolve _ _ | reconstructOpen =>
      -- Frame: action doesn't touch `local_.output`.
      simp [vssStep] at hvp; exact hinv p hp vp hvp
  | partyApplyResolution q i j =>
      simp only [vssStep] at hvp
      by_cases hqp : p = q
      · subst hqp
        rw [setLocal_local_self] at hvp
        simp at hvp
        exact hinv p hp vp hvp
      · rw [setLocal_local_ne _ _ _ _ hqp] at hvp
        exact hinv p hp vp hvp
  | reconstructAt q =>
      simp only [vssStep] at hvp
      by_cases hqp : p = q
      · subst hqp
        rw [setLocal_local_self] at hvp
        simp at hvp
        rw [show vp = if (s.local_ p).dealerExposed = true then (0 : F)
                       else s.coeffs 0 0 from hvp.symm]
        split
        · left; rfl
        · right; rfl
      · rw [setLocal_local_ne _ _ _ _ hqp] at hvp
        exact hinv p hp vp hvp

set_option maxHeartbeats 800000 in
/-- Commitment invariant `AlmostBox` lift. -/
theorem outputDeterminedInv_AS
    (sec : F) (corr : Finset (Fin n))
    (μ₀ : Measure (State n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr s)
    (A : Adversary (State n t F) (Action n F)) :
    AlmostBox (vssProb (t := t) sec corr) A μ₀ outputDeterminedInv := by
  have h_pure : ∀ (a : Action n F) (s : State n t F)
      (h : ((vssProb (t := t) sec corr).actions a).gate s),
      ((vssProb (t := t) sec corr).actions a).effect s h
        = PMF.pure (vssStep a s) :=
    fun _ _ _ => rfl
  have h_init' : ∀ᵐ s ∂μ₀, outputDeterminedInv s := by
    filter_upwards [h_init] with s hs
    exact initPred_outputDeterminedInv sec corr s hs
  exact AlmostBox_of_pure_inductive
    outputDeterminedInv
    (fun a s => vssStep a s)
    h_pure
    (fun a s _ h => vssStep_preserves_outputDeterminedInv a s h)
    μ₀ h_init' A

/-! ## §11. Secrecy (grid form, option (b))

A `t`-coalition's view of the dealer's grid `(C × D)`-shares is
distributionally independent of the secret. This is **option (b)**
of the M2.7 brief: the grid form rather than the row+column form.

We package this via `bivariate_shamir_secrecy` from
`BivariateShamir.lean`. The grid form's PMF is over
`Polynomial (Polynomial F)` (the dealer's bivariate F); its
coefficient-matrix counterpart is `PMF.uniform (Fin t → Fin t → F)`
modulo the fixed `(0, 0)`-coefficient. The reduction below states
secrecy at the *polynomial* level, which is the form
`bivariate_shamir_secrecy` provides directly. -/

/-- Grid-view secrecy: the post-deal `(C × D)`-grid eval distribution
is independent of the secret. Direct passthrough to
`BivariateShamir.bivariate_shamir_secrecy`. -/
theorem secrecy_grid (partyPoint : Fin n → F)
    (h_nz_pp : ∀ i, partyPoint i ≠ 0)
    (h_F : t + 1 ≤ Fintype.card F)
    (C D : BivariateShamir.Coalition n t) (s s' : F) :
    (Leslie.Prob.Polynomial.uniformBivariateWithFixedZero t t s).map
        (fun f => fun (i : C.val) (j : D.val) =>
          some ((f.eval (Polynomial.C (partyPoint i.val))).eval (partyPoint j.val)))
      =
    (Leslie.Prob.Polynomial.uniformBivariateWithFixedZero t t s').map
        (fun f => fun (i : C.val) (j : D.val) =>
          some ((f.eval (Polynomial.C (partyPoint i.val))).eval (partyPoint j.val))) :=
  BivariateShamir.bivariate_shamir_secrecy partyPoint h_nz_pp h_F C D s s'

/-! ## §12. Closing remarks

**Row+column secrecy (deferred).** The full BGW VSS secrecy theorem
states that a `t`-coalition's view of `(f_i, g_i)_{i ∈ T}` — i.e.,
the *full* row and column polynomials, not just the grid evals — is
independent of the secret. The grid form proved above (option (b))
captures the algebraic core; the full form requires showing that
the joint distribution over `T × Fin n ∪ Fin n × T` evaluations
factors through the grid + an independent uniform on the residual
rows/columns. This factorization is doable from
`bivariate_evals_uniform` but adds another ~200 LOC of polynomial
manipulation; we defer it to M3 AVSS where it is needed for the
real protocol.

**Commitment ⇒ disagreement-freedom.** The pure invariant
`outputDeterminedInv_AS` says every honest output is in `{0, coeffs 0 0}`.
Disagreement (one party outputs `0`, another outputs `coeffs 0 0`)
is ruled out by an additional "global exposure" invariant: in the
synchronous broadcast model, all honest parties see the *same*
resolutions, so either all expose or none do. We have not packaged
this stronger statement here (the deterministic step never sets
`dealerExposed = true`, so the global-exposure invariant is
trivially satisfied; the form *with* exposure logic is M3 work).

**Termination as `AlmostDiamond`.** The eventually-`.done` liveness
statement requires `AlmostDiamond_of_leads_to` machinery (M3). The
*invariant* form `roundBounded_AS` captures the deterministic
3-round bound's structural content. -/

end Leslie.Examples.Prob.SyncVSS
