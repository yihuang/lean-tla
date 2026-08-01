/-
M3 W5–W6 — Canetti–Rabin asynchronous verifiable secret sharing
(**abstracted variant**).

This module models the Canetti–Rabin '93 asynchronous VSS protocol
(`n` parties, `n ≥ 3t + 1`, `t` Byzantine corruptions) at an
*abstraction level* that's sufficient for the termination /
correctness / secrecy proofs to go through but does **not** match
the full protocol structure. Specifically:

  * `partyOutput` writes `s.coeffs 0 0` directly to every honest
    party (no per-party row-poly output).
  * `echoesReceived` / `readyReceived` accumulators are tracked but
    not `n − t`-threshold-checked (no Bracha amplification).

The full Canetti–Rabin protocol with row-poly outputs and Bracha
thresholds is formalized in `Leslie.Examples.Prob.AVSS` (Option B
of the M3 review). This file is preserved for the historical audit
trail and as a reference for the simpler termination certificate.

## Design choice: randomness in `μ₀`, deterministic step

Same template as `SyncVSS.lean` and `BrachaRBC.lean`: every action's
effect is a Dirac (`PMF.pure`); the dealer's bivariate polynomial is
sampled into `μ₀` via the coefficient matrix
`coeffs : Fin (t+1) → Fin (t+1) → F`.  This makes the
`AlmostBox_of_pure_inductive` bridge applicable directly, and lets us
discharge termination through `pi_n_AST_fair_with_progress_det`'s
deterministic-decrease specialisation.

## Protocol — Canetti–Rabin '93 (asynchronous VSS)

  * **Share phase** (dealer → all parties).  Dealer samples
    `F : F[x,y]_{≤t,≤t}` with `F(0,0) = sec`. Sends row poly
    `f_i(y) := F(α_i, y)` and column poly `g_i(x) := F(x, α_i)` to
    party `i`.
  * **Echo/ready phase**.  Bracha-style amplification: each party `i`
    broadcasts `(echo, j, g_i(α_j))` to every party `j`.  Party `j`
    checks `f_j(α_i) =? g_i(α_j)` (i.e., row meets column at the
    `(j,i)` grid point).  Once a party gathers `n − t` consistent
    echoes, it broadcasts `ready`.  Once a party has `n − t` ready
    messages, it outputs its own row poly `f_i` (its share is `f_i(0)
    = F(α_i, 0)`).
  * **Reconstruction.**  To reconstruct `s = F(0,0)`, parties exchange
    their shares; with `t + 1` valid shares Lagrange-interpolation
    recovers the secret.

For modelling purposes we collapse the share/echo/ready exchange into
two coarse-grained per-party actions: **deliver** (party receives its
`(row, col)` from the dealer) and **broadcastReady → output** (party
issues a `ready` once enough echoes accumulate, then snaps `output =
some (rowPoly i 0)` once enough `ready`s arrive).  The
`echoesReceived` / `readyReceived` finsets are tracked but treated
abstractly — the per-Bracha-message bookkeeping that turns a missing
echo into a missing ready is left to a future polish (it does not
affect any of the four headline theorem statements).

## Theorems (status)

  * `avss_termination_AS_fair` — under `TrajectoryFairAdversary` plus
    the trajectory-progress / monotonicity / strict-decrease
    witnesses, every honest party eventually outputs.  Discharged via
    `FairASTCertificate.pi_n_AST_fair_with_progress_det` plus the
    sublevel-set `partition_almostDiamond_fair` argument.
  * `avss_correctness_AS` — if dealer honest with secret `sec`, every
    honest output equals `bivEval coeffs (partyPoint p) 0`. Lifted
    via `AlmostBox_of_pure_inductive` against the inductive invariant
    `honestDealerInv`.
  * `avss_outputDeterminedInv_AS` — output-determined invariant
    (corrupt-dealer-tolerant): every honest output is determined by
    the row polynomial received from the dealer at delivery time.
    Lifted via `AlmostBox_of_pure_inductive`.
  * `avss_secrecy` — `t`-coalition view is independent of the
    dealer's secret. Thin wrapper around
    `BivariateShamir.bivariate_shamir_secrecy`.

## What this file is NOT

  * Not a fully *Bracha-amplification-faithful* AVSS implementation.
    The `echoesReceived` / `readyReceived` accumulators are not
    threshold-checked; we model the protocol at the abstraction level
    where "deliver" and "ready→output" are the load-bearing actions.
    The full thresholded variant is in `AVSS.lean`.
  * Not the per-party-row-poly variant. `partyOutput` here writes
    `coeffs 0 0` directly. The real Canetti–Rabin per-party share
    `s_p = bivEval coeffs (partyPoint p) 0` is formalized in
    `AVSS.lean`.
  * Not the M3 entry gate stub. `AVSSStub.lean` was deleted in the
    M3 cleanup; this file's `avssCert` functionally subsumes the
    stub's shape-verification role.

Per implementation plan v2.2 §M3 W5–W6 + design plan v2.2 §M3 AVSS.
-/

import Leslie.Examples.Prob.BivariateShamir
import Leslie.Prob.Action
import Leslie.Prob.Adversary
import Leslie.Prob.Liveness
import Leslie.Prob.PMF
import Leslie.Prob.Polynomial
import Leslie.Prob.Refinement
import Leslie.Prob.Trace
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Countable.Defs

namespace Leslie.Examples.Prob.AVSSAbstract

open Leslie.Prob MeasureTheory NNReal

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {n t : ℕ}

/-! ## §1. Per-party state -/

/-- Per-party AVSS local state.

  * `delivered : Bool` — whether the dealer's `(row, col)` polys have
    landed at this party.
  * `echoesReceived : Finset (Fin n × Fin n × F)` — `(sender, target,
    value)` tuples seen as echo messages (abstracted; thresholds not
    explicitly checked at the modelling level).
  * `readyReceived : Finset (Fin n)` — set of senders whose `ready`
    has been seen.
  * `readySent : Bool` — has this party broadcast its own ready?
  * `output : Option F` — the final share `f_i(0) = F(α_i, 0)`. `none`
    until enough `ready`s have arrived.
-/
structure AVSSLocalState (n : ℕ) (F : Type*) [DecidableEq F] where
  delivered      : Bool
  echoesReceived : Finset (Fin n × Fin n × F)
  readyReceived  : Finset (Fin n)
  readySent      : Bool
  output         : Option F

namespace AVSSLocalState

/-- The empty per-party state at protocol start. -/
def init (n : ℕ) (F : Type*) [DecidableEq F] : AVSSLocalState n F :=
  { delivered := false
    echoesReceived := ∅
    readyReceived := ∅
    readySent := false
    output := none }

end AVSSLocalState

/-- The global AVSS protocol state.

  * `coeffs` — dealer's bivariate polynomial coefficients. Sampled
    once into `μ₀`; not modified after.
  * `local_` — per-party state.
  * `corrupted` — static corruption set.
  * `dealerHonest` — bookkeeping flag for honest-dealer correctness.
  * `inflightDeliveries` — set of parties whose delivery message has
    not yet been processed.  Drives termination's variant `U`.
  * `inflightReady` — set of parties whose own-ready broadcast has
    not yet been propagated to all peers.
  * `dealerSent` — whether the dealer has emitted shares.
-/
structure AVSSState (n t : ℕ) (F : Type*) [DecidableEq F] where
  coeffs              : Fin (t+1) → Fin (t+1) → F
  secret              : F
  local_              : Fin n → AVSSLocalState n F
  corrupted           : Finset (Fin n)
  dealerHonest        : Bool
  inflightDeliveries  : Finset (Fin n)
  inflightReady       : Finset (Fin n)
  dealerSent          : Bool

namespace AVSSState

/-- A party is honest iff not in the corruption set. -/
def isHonest [DecidableEq F] (s : AVSSState n t F) (p : Fin n) : Prop :=
  p ∉ s.corrupted

instance [DecidableEq F] (s : AVSSState n t F) (p : Fin n) :
    Decidable (s.isHonest p) :=
  inferInstanceAs (Decidable (p ∉ s.corrupted))

end AVSSState

/-! ## §2. Bivariate evaluation (mirrors `SyncVSS.bivEval`) -/

/-- Bivariate evaluation of `coeffs` at `(x, y)` in `F`. -/
def bivEval (coeffs : Fin (t+1) → Fin (t+1) → F) (x y : F) : F :=
  ∑ k : Fin (t+1), ∑ l : Fin (t+1), coeffs k l * x ^ k.val * y ^ l.val

/-- The dealer's row poly `f_i(y) = F(α_i, y)` at `y`. -/
def rowEval (partyPoint : Fin n → F)
    (coeffs : Fin (t+1) → Fin (t+1) → F) (i : Fin n) (y : F) : F :=
  bivEval coeffs (partyPoint i) y

/-- The dealer's column poly `g_j(x) = F(x, α_j)` at `x`. -/
def colEval (partyPoint : Fin n → F)
    (coeffs : Fin (t+1) → Fin (t+1) → F) (j : Fin n) (x : F) : F :=
  bivEval coeffs x (partyPoint j)

/-! ## §3. Initial-state predicate -/

/-- Initial-state predicate. -/
def initPred (sec : F) (corr : Finset (Fin n))
    (s : AVSSState n t F) : Prop :=
  (∀ p, s.local_ p = AVSSLocalState.init n F) ∧
  s.secret = sec ∧
  s.corrupted = corr ∧
  s.inflightDeliveries = ∅ ∧
  s.inflightReady = ∅ ∧
  s.dealerSent = false ∧
  -- If dealer honest, `coeffs 0 0 = sec`.
  (s.dealerHonest = true → s.coeffs 0 0 = sec)

/-! ## §4. Action labels -/

/-- AVSS protocol actions. -/
inductive AVSSAction (n : ℕ) (F : Type*) [DecidableEq F]
  | dealerShare            -- dealer emits all shares (sets `dealerSent`)
  | partyDeliver  (p : Fin n)  -- party `p` receives its row+col
  | partyEcho     (p q : Fin n) (v : F)  -- party `p` records echo from `q` with value `v`
  | partyReady    (p : Fin n)  -- party `p` broadcasts ready
  | partyReceiveReady (p q : Fin n)  -- party `p` records ready from `q`
  | partyOutput   (p : Fin n)  -- party `p` snaps output

/-! ## §5. Functional `setLocal` helper -/

/-- Functional update for `local_`: replace party `p`'s local state. -/
def setLocal (s : AVSSState n t F) (p : Fin n) (ls : AVSSLocalState n F) :
    AVSSState n t F :=
  { s with local_ := fun q => if q = p then ls else s.local_ q }

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_local_self (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n F) :
    (setLocal s p ls).local_ p = ls := by
  simp [setLocal]

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_local_ne (s : AVSSState n t F) (p q : Fin n)
    (ls : AVSSLocalState n F) (h : q ≠ p) :
    (setLocal s p ls).local_ q = s.local_ q := by
  simp [setLocal, h]

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_coeffs (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n F) :
    (setLocal s p ls).coeffs = s.coeffs := rfl

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_secret (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n F) :
    (setLocal s p ls).secret = s.secret := rfl

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_corrupted (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n F) :
    (setLocal s p ls).corrupted = s.corrupted := rfl

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_dealerHonest (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n F) :
    (setLocal s p ls).dealerHonest = s.dealerHonest := rfl

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_inflightDeliveries (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n F) :
    (setLocal s p ls).inflightDeliveries = s.inflightDeliveries := rfl

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_inflightReady (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n F) :
    (setLocal s p ls).inflightReady = s.inflightReady := rfl

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_dealerSent (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n F) :
    (setLocal s p ls).dealerSent = s.dealerSent := rfl

/-! ## §6. Deterministic next-state -/

/-- The deterministic next-state function. Where the gate fails this
returns `s` unchanged; gates are enforced by `actionGate`. -/
def avssStep (a : AVSSAction n F) (s : AVSSState n t F) :
    AVSSState n t F :=
  match a with
  | .dealerShare =>
      -- Dealer emits all shares; populates the inflight-delivery set
      -- with every honest party.
      { s with
        dealerSent := true
        inflightDeliveries :=
          (Finset.univ : Finset (Fin n)).filter (fun p => p ∉ s.corrupted) }
  | .partyDeliver p =>
      let ls := s.local_ p
      let ls' : AVSSLocalState n F := { ls with delivered := true }
      let s' := setLocal s p ls'
      { s' with inflightDeliveries := s.inflightDeliveries.erase p }
  | .partyEcho p q v =>
      let ls := s.local_ p
      let ls' : AVSSLocalState n F :=
        { ls with echoesReceived := insert (q, p, v) ls.echoesReceived }
      setLocal s p ls'
  | .partyReady p =>
      let ls := s.local_ p
      let ls' : AVSSLocalState n F := { ls with readySent := true }
      let s' := setLocal s p ls'
      { s' with inflightReady := insert p s.inflightReady }
  | .partyReceiveReady p q =>
      let ls := s.local_ p
      let ls' : AVSSLocalState n F :=
        { ls with readyReceived := insert q ls.readyReceived }
      let s' := setLocal s p ls'
      { s' with inflightReady := s.inflightReady.erase q }
  | .partyOutput p =>
      let ls := s.local_ p
      -- Output is `coeffs 0 0 = bivEval coeffs 0 0`.  In a fully
      -- Bracha-faithful refinement, this would be the row poly's
      -- evaluation at 0, i.e., `bivEval coeffs (partyPoint p) 0`.
      -- Our abstraction snaps the secret directly; this simplifies
      -- correctness/commitment proofs and is sound at the
      -- algebraic-content level.  See the §13 modeling note.
      let v : F := s.coeffs 0 0
      let ls' : AVSSLocalState n F := { ls with output := some v }
      setLocal s p ls'

/-! ## §7. Action gates -/

/-- Gate predicates.

The fair-required actions (`partyDeliver`, `partyReady`,
`partyReceiveReady`, `partyOutput`) restrict their party arguments to
honest parties — only honest parties follow the protocol script.
This restriction is structurally necessary for the variant analysis:
we count "honest unfinished" / "honest not-yet-ready-sent" cardinals,
and a Byzantine `partyReady`/`partyOutput` would not decrement those
counters.  None of the headline theorems (correctness, commitment,
secrecy) are affected — they already quantify over honest parties. -/
def actionGate (a : AVSSAction n F) (s : AVSSState n t F) : Prop :=
  match a with
  | .dealerShare =>
      s.dealerSent = false
  | .partyDeliver p =>
      s.dealerSent = true ∧ p ∉ s.corrupted ∧
        p ∈ s.inflightDeliveries ∧ (s.local_ p).delivered = false
  | .partyEcho _ _ _ =>
      s.dealerSent = true
  | .partyReady p =>
      p ∉ s.corrupted ∧
        (s.local_ p).delivered = true ∧ (s.local_ p).readySent = false
  | .partyReceiveReady p q =>
      q ∈ s.inflightReady ∧ q ∉ (s.local_ p).readyReceived
  | .partyOutput p =>
      p ∉ s.corrupted ∧
        (s.local_ p).delivered = true ∧ (s.local_ p).readySent = true ∧
        (s.local_ p).output = none

/-! ## §8. Terminated predicate -/

/-- A state is terminated iff every honest party has snapped output
**and** all in-flight queues are drained.  The drainedness condition
makes the termination variant `avssU` equal `0` at terminated states,
which the certificate's `V_term` / `U_term` fields require.

Operationally: an honest party's output requires `delivered = true ∧
output = none` to be true at the firing of `partyOutput`, which by
the gate guarantees a delivery happened; once every honest party has
output, no delivery or ready remains pending (modulo the structural
invariant on `inflightDeliveries`/`inflightReady` capturing
corrupted-party filtering — that invariant is the hidden bookkeeping
mentioned in the §12 design note). -/
def terminated (s : AVSSState n t F) : Prop :=
  (∀ p, p ∉ s.corrupted → (s.local_ p).output.isSome) ∧
  s.inflightDeliveries = ∅ ∧
  s.inflightReady = ∅

/-! ## §9. Spec -/

/-- The probabilistic AVSS spec.  Randomness lives in `μ₀` only. -/
noncomputable def avssSpec (sec : F) (corr : Finset (Fin n)) :
    ProbActionSpec (AVSSState n t F) (AVSSAction n F) where
  init := initPred sec corr
  actions := fun a =>
    { gate := actionGate a
      effect := fun s _ => PMF.pure (avssStep a s) }

omit [Field F] [Fintype F] in
@[simp] theorem avssSpec_step_pure (sec : F) (corr : Finset (Fin n))
    (a : AVSSAction n F) (s : AVSSState n t F) (h : actionGate a s) :
    (avssSpec (t := t) sec corr).step a s
      = some (PMF.pure (avssStep a s)) :=
  ProbActionSpec.step_eq_some h

omit [Field F] [Fintype F] in
theorem avssSpec_step_none (sec : F) (corr : Finset (Fin n))
    (a : AVSSAction n F) (s : AVSSState n t F) (h : ¬ actionGate a s) :
    (avssSpec (t := t) sec corr).step a s = none :=
  ProbActionSpec.step_eq_none h

/-! ## §10. Countable / measurable instances -/

section Measurable

instance : MeasurableSpace (AVSSState n t F) := ⊤
instance : MeasurableSingletonClass (AVSSState n t F) := ⟨fun _ => trivial⟩
instance : MeasurableSpace (AVSSAction n F) := ⊤
instance : MeasurableSingletonClass (AVSSAction n F) := ⟨fun _ => trivial⟩

/-- `AVSSAction n F` is `Fintype` under `[Fintype F]`. -/
noncomputable instance : Fintype (AVSSAction n F) := by
  classical
  exact Fintype.ofEquiv
    (Unit ⊕ Fin n ⊕ (Fin n × Fin n × F) ⊕ Fin n ⊕ (Fin n × Fin n) ⊕ Fin n)
    { toFun := fun
        | .inl _ => .dealerShare
        | .inr (.inl p) => .partyDeliver p
        | .inr (.inr (.inl ⟨p, q, v⟩)) => .partyEcho p q v
        | .inr (.inr (.inr (.inl p))) => .partyReady p
        | .inr (.inr (.inr (.inr (.inl ⟨p, q⟩)))) =>
            .partyReceiveReady p q
        | .inr (.inr (.inr (.inr (.inr p)))) => .partyOutput p
      invFun := fun
        | .dealerShare => .inl ()
        | .partyDeliver p => .inr (.inl p)
        | .partyEcho p q v => .inr (.inr (.inl ⟨p, q, v⟩))
        | .partyReady p => .inr (.inr (.inr (.inl p)))
        | .partyReceiveReady p q =>
            .inr (.inr (.inr (.inr (.inl ⟨p, q⟩))))
        | .partyOutput p => .inr (.inr (.inr (.inr (.inr p))))
      left_inv := fun
        | .inl _ => rfl
        | .inr (.inl _) => rfl
        | .inr (.inr (.inl _)) => rfl
        | .inr (.inr (.inr (.inl _))) => rfl
        | .inr (.inr (.inr (.inr (.inl _)))) => rfl
        | .inr (.inr (.inr (.inr (.inr _)))) => rfl
      right_inv := fun
        | .dealerShare => rfl
        | .partyDeliver _ => rfl
        | .partyEcho _ _ _ => rfl
        | .partyReady _ => rfl
        | .partyReceiveReady _ _ => rfl
        | .partyOutput _ => rfl }

instance : Countable (AVSSAction n F) := Finite.to_countable

/-- `AVSSLocalState n F` is `Fintype`. -/
noncomputable instance : Fintype (AVSSLocalState n F) := by
  classical
  exact Fintype.ofEquiv
    (Bool × Finset (Fin n × Fin n × F) × Finset (Fin n) × Bool × Option F)
    { toFun := fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩
      invFun := fun ls =>
        (ls.delivered, ls.echoesReceived, ls.readyReceived,
         ls.readySent, ls.output)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance : Countable (AVSSLocalState n F) := Finite.to_countable

/-- `AVSSState n t F` is `Fintype`. -/
noncomputable instance : Fintype (AVSSState n t F) := by
  classical
  exact Fintype.ofEquiv
    ((Fin (t+1) → Fin (t+1) → F) × F ×
      (Fin n → AVSSLocalState n F) × Finset (Fin n) × Bool ×
      Finset (Fin n) × Finset (Fin n) × Bool)
    { toFun := fun ⟨c, sec, l, corr, dh, idl, ird, ds⟩ =>
        ⟨c, sec, l, corr, dh, idl, ird, ds⟩
      invFun := fun s =>
        (s.coeffs, s.secret, s.local_, s.corrupted, s.dealerHonest,
         s.inflightDeliveries, s.inflightReady, s.dealerSent)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance : Countable (AVSSState n t F) := Finite.to_countable

end Measurable

/-! ## §11. Fairness assumptions

Honest progress requires that *delivery*, *ready broadcast*, *ready
delivery*, and *output* eventually fire when continuously enabled.
The fair-required action set covers all of these. The
`isWeaklyFair` predicate is left as `True` (placeholder, same
convention as `BrachaRBC.brbFair` and `CommonCoin.ccFair`); concrete
trajectory-progress witnesses are bundled into a
`TrajectoryFairAdversary`. -/

/-- Set of fair-required actions. -/
def avssFairActions : Set (AVSSAction n F) :=
  { a | match a with
        | .partyDeliver _ => True
        | .partyReady _ => True
        | .partyReceiveReady _ _ => True
        | .partyOutput _ => True
        | _ => False }

/-- AVSS fairness assumptions. -/
noncomputable def avssFair :
    FairnessAssumptions (AVSSState n t F) (AVSSAction n F) where
  fair_actions := avssFairActions
  isWeaklyFair := fun _ => True

/-! ## §12. Termination via `FairASTCertificate` (deterministic specialisation)

The variant `U` is a lex-product of pending work counts:

  * `inflightDeliveries.card` — pending dealer deliveries,
  * `inflightReady.card` — pending ready broadcasts,
  * count of honest parties with no `output` set.

Combined linearly via `K := 2 * n + 1` (a uniform upper bound on each
component), so a strict decrease in any component dominates the
others.  Every fair-required action strictly decreases `U` (by the
deterministic-decrease pattern), every non-fair action — at most
`dealerShare` — leaves `U` non-increasing (it adds to
`inflightDeliveries` exactly once, but only when the dealer hasn't
sent yet, which is captured by carrying `dealerSent` in the
invariant).

For the M3 W5–W6 deliverable we discharge termination by handing
`pi_n_AST_fair_with_progress_det` four trajectory-form witnesses: a
fair-progress witness, a `TrajectoryUMono` witness, and a
`TrajectoryFairStrictDecrease` witness, plus the `FairASTCertificate`
itself with all the structural fields. The `TrajectoryUMono` and
`TrajectoryFairStrictDecrease` derivations require ~150 LOC of
trajectory-step kernel analysis (per the `Liveness.lean` design note
on §"Deterministic specialisation"); we package them as hypotheses
the caller supplies, mirroring the shape of
`BrachaRBC.brbProb_totality_AS_fair`. -/

/-- The set of honest parties (those not in `corrupted`). -/
def honestSet (s : AVSSState n t F) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun p => p ∉ s.corrupted)

omit [Field F] [Fintype F] in
@[simp] theorem honestSet_card_le (s : AVSSState n t F) :
    (honestSet s).card ≤ n := by
  simpa [honestSet] using Finset.card_le_univ
    ((Finset.univ : Finset (Fin n)).filter (fun p => p ∉ s.corrupted))

/-- Variant: pending work along the trajectory.

`K = 2 * n + 1` is large enough that strict decrease in any one
component always dominates simultaneous changes elsewhere; the
fair-action analysis uses this directly.

The five lex components, from highest to lowest weight, are:

  * `(if !dealerSent then honestSet.card else 0) * K^4` — the dealer
    hasn't yet emitted shares.  Decreases by `honestCount * K^4` on
    `dealerShare`, dominating that step's `+ honestCount * K^2`
    inflight-deliveries increase.  At terminated states this term
    is `0`: either `dealerSent` (then the multiplier is `0`) or no
    honest party exists (then the cardinality is `0`).
  * `notReadySentCount * K^3` — count of honest parties with
    `readySent = false`.  Decreases by `K^3` on `partyReady`,
    dominating that step's `+ K` inflightReady increase.
  * `inflightDeliveries.card * K^2` — pending dealer deliveries.
  * `inflightReady.card * K` — pending ready broadcasts.
  * `unfinishedCount` — count of honest parties with `output = none`. -/
noncomputable def avssU (s : AVSSState n t F) : ℕ :=
  (if s.dealerSent then 0 else (honestSet s).card) * (2 * n + 1) ^ 4 +
    ((Finset.univ : Finset (Fin n)).filter
        (fun p => p ∉ s.corrupted ∧ (s.local_ p).readySent = false)).card
        * (2 * n + 1) ^ 3 +
    s.inflightDeliveries.card * (2 * n + 1) ^ 2 +
    s.inflightReady.card * (2 * n + 1) +
    ((Finset.univ : Finset (Fin n)).filter
      (fun p => p ∉ s.corrupted ∧ (s.local_ p).output = none)).card

/-- Likelihood `V s = (avssU s : ℝ≥0)`. -/
noncomputable def avssV (s : AVSSState n t F) : ℝ≥0 := (avssU s : ℝ≥0)

/-- Termination inductive invariant.

Two clauses:

  * When the dealer hasn't yet shared, every party is in its initial
    local state and both in-flight queues are empty.  Lets the
    variant analysis reason about `dealerShare`'s state delta
    uniformly.
  * Every honest party with `output = some _` has `readySent = true`.
    The post-share gate of `partyOutput` requires `readySent = true`,
    which makes this implication invariant: nothing else flips
    `output` from `none` to `some _`. -/
def avssTermInv (s : AVSSState n t F) : Prop :=
  (s.dealerSent = false →
    (∀ p, (s.local_ p).delivered = false ∧
          (s.local_ p).readySent = false ∧
          (s.local_ p).output = none) ∧
    s.inflightDeliveries = ∅ ∧
    s.inflightReady = ∅) ∧
  (∀ p, p ∉ s.corrupted →
    (s.local_ p).output.isSome = true → (s.local_ p).readySent = true)

/-! ### Variant bound

Strictly: under `terminated`, every honest party has output set, so
the third component of `avssU` is 0.  The dealer-delivery and
ready-broadcast components depend on adversary scheduling. The
uniform bound below — `(3*n+1) * (2*n+1)^2` — is conservative but
gives the `V_init_bdd` field of the certificate. -/

omit [Field F] [Fintype F] in
/-- The variant `avssU` is bounded by `(5 * n + 5) * (2*n+1)^4`. -/
theorem avssU_le_bound (s : AVSSState n t F) :
    avssU s ≤ (5 * n + 5) * (2 * n + 1) ^ 4 := by
  unfold avssU
  classical
  have h0 : (if s.dealerSent then (0 : ℕ) else (honestSet s).card) ≤ n := by
    split
    · exact Nat.zero_le _
    · exact honestSet_card_le s
  have hNRS : ((Finset.univ : Finset (Fin n)).filter
      (fun p => p ∉ s.corrupted ∧ (s.local_ p).readySent = false)).card ≤ n := by
    have := Finset.card_le_univ
      ((Finset.univ : Finset (Fin n)).filter
        (fun p => p ∉ s.corrupted ∧ (s.local_ p).readySent = false))
    simpa using this
  have h1 : s.inflightDeliveries.card ≤ n := by
    have := Finset.card_le_univ s.inflightDeliveries
    simpa using this
  have h2 : s.inflightReady.card ≤ n := by
    have := Finset.card_le_univ s.inflightReady
    simpa using this
  have h3 : ((Finset.univ : Finset (Fin n)).filter
      (fun p => p ∉ s.corrupted ∧ (s.local_ p).output = none)).card ≤ n := by
    have := Finset.card_le_univ
      ((Finset.univ : Finset (Fin n)).filter
        (fun p => p ∉ s.corrupted ∧ (s.local_ p).output = none))
    simpa using this
  set K := 2 * n + 1 with hK_def
  have hK : 1 ≤ K := by rw [hK_def]; omega
  have hpow1 : K ≤ K ^ 4 := by
    calc K = K ^ 1 := by ring
      _ ≤ K ^ 4 := Nat.pow_le_pow_right hK (by omega)
  have hpow2 : K ^ 2 ≤ K ^ 4 := Nat.pow_le_pow_right hK (by omega)
  have hpow3 : K ^ 3 ≤ K ^ 4 := Nat.pow_le_pow_right hK (by omega)
  have hpow0 : (1 : ℕ) ≤ K ^ 4 := by
    calc (1 : ℕ) = 1 ^ 4 := by ring
      _ ≤ K ^ 4 := by gcongr
  have hA : (if s.dealerSent then (0 : ℕ) else (honestSet s).card) * K ^ 4
              ≤ n * K ^ 4 := by
    have := h0
    nlinarith [Nat.zero_le (K ^ 4)]
  have hB : ((Finset.univ : Finset (Fin n)).filter
        (fun p => p ∉ s.corrupted ∧ (s.local_ p).readySent = false)).card * K ^ 3
        ≤ n * K ^ 4 := by
    calc ((Finset.univ : Finset (Fin n)).filter
            (fun p => p ∉ s.corrupted ∧ (s.local_ p).readySent = false)).card * K ^ 3
        ≤ n * K ^ 3 := by gcongr
      _ ≤ n * K ^ 4 := by gcongr
  have hC : s.inflightDeliveries.card * K ^ 2 ≤ n * K ^ 4 := by
    calc s.inflightDeliveries.card * K ^ 2
        ≤ n * K ^ 2 := by gcongr
      _ ≤ n * K ^ 4 := by gcongr
  have hD : s.inflightReady.card * K ≤ n * K ^ 4 := by
    calc s.inflightReady.card * K
        ≤ n * K := by gcongr
      _ ≤ n * K ^ 4 := by gcongr
  have hE : ((Finset.univ : Finset (Fin n)).filter
        (fun p => p ∉ s.corrupted ∧ (s.local_ p).output = none)).card
        ≤ n * K ^ 4 := by
    calc ((Finset.univ : Finset (Fin n)).filter
            (fun p => p ∉ s.corrupted ∧ (s.local_ p).output = none)).card
        ≤ n := h3
      _ = n * 1 := by ring
      _ ≤ n * K ^ 4 := by nlinarith [hpow0]
  -- Sum: ≤ 5 * n * K^4 ≤ (5*n+5) * K^4.
  have h_total :
      (if s.dealerSent then (0 : ℕ) else (honestSet s).card) * K ^ 4 +
        ((Finset.univ : Finset (Fin n)).filter
          (fun p => p ∉ s.corrupted ∧ (s.local_ p).readySent = false)).card * K ^ 3 +
        s.inflightDeliveries.card * K ^ 2 +
        s.inflightReady.card * K +
        ((Finset.univ : Finset (Fin n)).filter
          (fun p => p ∉ s.corrupted ∧ (s.local_ p).output = none)).card
        ≤ (5 * n + 5) * K ^ 4 := by
    have hgoal : 5 * (n * K ^ 4) ≤ (5 * n + 5) * K ^ 4 := by
      have : (5 * n + 5) * K ^ 4 = 5 * n * K ^ 4 + 5 * K ^ 4 := by ring
      have hKpos : 0 ≤ 5 * K ^ 4 := Nat.zero_le _
      nlinarith
    omega
  exact h_total

/-! ## §13. Honest-dealer correctness invariant

If the dealer is honest with secret `sec`, then `coeffs 0 0 = sec`
(this is part of the initial-state predicate), and every set output
of an honest party equals `sec`. The output-snap step writes
`rowEval _ s.coeffs p 0` which simplifies (since the placeholder
`partyPoint` we use is `fun _ => 0`) to `bivEval s.coeffs 0 0 = s.coeffs 0 0`.

Modeling note: a fully Bracha-faithful AVSS would have the output be
`f_p(0) = bivEval coeffs (partyPoint p) 0`; the dealer's secret is
recovered by Lagrange-interpolating `t + 1` such values. The
abstraction here uses a *uniform* output value `coeffs 0 0` (the
secret itself) for every honest party, mirroring the synchronous-VSS
shape; this is conservative for *correctness* (every honest party's
output equals `sec` directly, no Lagrange interpolation needed) but
means the file does not yet encode the per-party share structure
needed for the *full* commitment story.  See §14. -/

/-- The honest-dealer correctness invariant. -/
def honestDealerInv (sec : F) (s : AVSSState n t F) : Prop :=
  s.dealerHonest = true →
    s.coeffs 0 0 = sec ∧
    ∀ p, p ∉ s.corrupted →
      ∀ v, (s.local_ p).output = some v → v = sec

omit [Field F] [Fintype F] in
theorem initPred_honestDealerInv (sec : F) (corr : Finset (Fin n))
    (s : AVSSState n t F) (h : initPred sec corr s) :
    honestDealerInv sec s := by
  intro hh
  obtain ⟨hloc, _, _, _, _, _, hF⟩ := h
  refine ⟨hF hh, ?_⟩
  intro p _ v hv
  rw [hloc p] at hv
  simp [AVSSLocalState.init] at hv

set_option maxHeartbeats 800000 in
omit [Field F] [Fintype F] in
theorem avssStep_preserves_honestDealerInv (sec : F)
    (a : AVSSAction n F) (s : AVSSState n t F)
    (_hgate : actionGate a s)
    (hinv : honestDealerInv sec s) :
    honestDealerInv sec (avssStep a s) := by
  intro hh
  -- Dealer-honest field is preserved by every action.
  have hh_pre : s.dealerHonest = true := by
    cases a <;> simp [avssStep, setLocal] at hh <;> exact hh
  obtain ⟨hsec, hperp⟩ := hinv hh_pre
  cases a with
  | dealerShare =>
      simp only [avssStep] at hh ⊢
      refine ⟨hsec, ?_⟩
      intro p hp v hv
      exact hperp p hp v hv
  | partyDeliver p =>
      simp only [avssStep] at hh ⊢
      refine ⟨hsec, ?_⟩
      intro q hq v hv
      by_cases hqp : q = p
      · subst hqp
        rw [setLocal_local_self] at hv
        simp at hv
        exact hperp q hq v hv
      · rw [setLocal_local_ne _ _ _ _ hqp] at hv
        exact hperp q hq v hv
  | partyEcho p _ _ =>
      simp only [avssStep] at hh ⊢
      refine ⟨hsec, ?_⟩
      intro q hq v hv
      by_cases hqp : q = p
      · subst hqp
        rw [setLocal_local_self] at hv
        simp at hv
        exact hperp q hq v hv
      · rw [setLocal_local_ne _ _ _ _ hqp] at hv
        exact hperp q hq v hv
  | partyReady p =>
      simp only [avssStep] at hh ⊢
      refine ⟨hsec, ?_⟩
      intro q hq v hv
      by_cases hqp : q = p
      · subst hqp
        rw [setLocal_local_self] at hv
        simp at hv
        exact hperp q hq v hv
      · rw [setLocal_local_ne _ _ _ _ hqp] at hv
        exact hperp q hq v hv
  | partyReceiveReady p _ =>
      simp only [avssStep] at hh ⊢
      refine ⟨hsec, ?_⟩
      intro q hq v hv
      by_cases hqp : q = p
      · subst hqp
        rw [setLocal_local_self] at hv
        simp at hv
        exact hperp q hq v hv
      · rw [setLocal_local_ne _ _ _ _ hqp] at hv
        exact hperp q hq v hv
  | partyOutput p =>
      simp only [avssStep] at hh ⊢
      refine ⟨hsec, ?_⟩
      intro q hq v hv
      by_cases hqp : q = p
      · subst hqp
        rw [setLocal_local_self] at hv
        simp at hv
        -- New output is `s.coeffs 0 0 = sec` by `hsec`.
        rw [← hv]; exact hsec
      · rw [setLocal_local_ne _ _ _ _ hqp] at hv
        exact hperp q hq v hv

/-! ## §14. Output-determined invariant (commitment proxy)

Even with a corrupt dealer, every honest output is the deterministic
function of `coeffs` written by `partyOutput`'s effect. Concretely
`output = some (bivEval coeffs 0 0)` for our abstracted model — no
disjunction needed at this level (the abstraction collapses
"exposure" into the trivial branch). The full commitment statement
disjoining "all honest outputs equal" against "dealer exposed" lives
in the Bracha-faithful refinement of this model; we record the basic
form here. -/

/-- Output-determined invariant: every honest output, if set, equals
`bivEval coeffs 0 0` (= `coeffs 0 0`). -/
def outputDeterminedInv (s : AVSSState n t F) : Prop :=
  ∀ p, p ∉ s.corrupted → ∀ v, (s.local_ p).output = some v →
    v = s.coeffs 0 0

omit [Field F] [Fintype F] in
theorem initPred_outputDeterminedInv (sec : F) (corr : Finset (Fin n))
    (s : AVSSState n t F) (h : initPred sec corr s) :
    outputDeterminedInv s := by
  intro p _ v hv
  obtain ⟨hloc, _⟩ := h
  rw [hloc p] at hv
  simp [AVSSLocalState.init] at hv

omit [Field F] [Fintype F] in
theorem avssStep_preserves_outputDeterminedInv (a : AVSSAction n F)
    (s : AVSSState n t F) :
    outputDeterminedInv s → outputDeterminedInv (avssStep a s) := by
  intro hinv p hp v hv
  cases a with
  | dealerShare =>
      simp only [avssStep] at hv
      exact hinv p hp v hv
  | partyDeliver q =>
      simp only [avssStep] at hv
      by_cases hqp : p = q
      · subst hqp
        rw [setLocal_local_self] at hv
        simp at hv
        exact hinv p hp v hv
      · rw [setLocal_local_ne _ _ _ _ hqp] at hv
        exact hinv p hp v hv
  | partyEcho q _ _ =>
      simp only [avssStep] at hv
      by_cases hqp : p = q
      · subst hqp
        rw [setLocal_local_self] at hv
        simp at hv
        exact hinv p hp v hv
      · rw [setLocal_local_ne _ _ _ _ hqp] at hv
        exact hinv p hp v hv
  | partyReady q =>
      simp only [avssStep] at hv
      by_cases hqp : p = q
      · subst hqp
        rw [setLocal_local_self] at hv
        simp at hv
        exact hinv p hp v hv
      · rw [setLocal_local_ne _ _ _ _ hqp] at hv
        exact hinv p hp v hv
  | partyReceiveReady q _ =>
      simp only [avssStep] at hv
      by_cases hqp : p = q
      · subst hqp
        rw [setLocal_local_self] at hv
        simp at hv
        exact hinv p hp v hv
      · rw [setLocal_local_ne _ _ _ _ hqp] at hv
        exact hinv p hp v hv
  | partyOutput q =>
      simp only [avssStep] at hv
      by_cases hqp : p = q
      · subst hqp
        rw [setLocal_local_self] at hv
        simp at hv
        -- After simp, hv : s.coeffs 0 0 = v.  Goal: v = (avssStep ...).coeffs 0 0.
        -- `avssStep (.partyOutput p)` preserves `coeffs` (frame lemma).
        show v = s.coeffs 0 0
        exact hv.symm
      · rw [setLocal_local_ne _ _ _ _ hqp] at hv
        exact hinv p hp v hv

/-! ## §15. Almost-box lifts -/

set_option maxHeartbeats 800000 in
/-- Honest-dealer correctness as an `AlmostBox`. -/
theorem avss_correctness_AS
    (sec : F) (corr : Finset (Fin n))
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr s)
    (A : Adversary (AVSSState n t F) (AVSSAction n F)) :
    AlmostBox (avssSpec (t := t) sec corr) A μ₀
      (fun s => s.dealerHonest = true →
        ∀ p, p ∉ s.corrupted →
          ∀ v, (s.local_ p).output = some v → v = sec) := by
  have h_pure : ∀ (a : AVSSAction n F) (s : AVSSState n t F)
      (h : ((avssSpec (t := t) sec corr).actions a).gate s),
      ((avssSpec (t := t) sec corr).actions a).effect s h
        = PMF.pure (avssStep a s) :=
    fun _ _ _ => rfl
  have h_init' : ∀ᵐ s ∂μ₀, honestDealerInv sec s := by
    filter_upwards [h_init] with s hs
    exact initPred_honestDealerInv sec corr s hs
  have h_inv : AlmostBox (avssSpec (t := t) sec corr) A μ₀
      (honestDealerInv sec) :=
    AlmostBox_of_pure_inductive
      (honestDealerInv sec)
      (fun a s => avssStep a s)
      h_pure
      (fun a s hgate hinv =>
        avssStep_preserves_honestDealerInv sec a s hgate hinv)
      μ₀ h_init' A
  unfold AlmostBox at h_inv ⊢
  filter_upwards [h_inv] with ω hinv k hh p hp v hv
  exact (hinv k hh).2 p hp v hv

set_option maxHeartbeats 800000 in
/-- Output-determined `AlmostBox` lift. Tolerates corrupt dealer. -/
theorem avss_outputDeterminedInv_AS
    (sec : F) (corr : Finset (Fin n))
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr s)
    (A : Adversary (AVSSState n t F) (AVSSAction n F)) :
    AlmostBox (avssSpec (t := t) sec corr) A μ₀ outputDeterminedInv := by
  have h_pure : ∀ (a : AVSSAction n F) (s : AVSSState n t F)
      (h : ((avssSpec (t := t) sec corr).actions a).gate s),
      ((avssSpec (t := t) sec corr).actions a).effect s h
        = PMF.pure (avssStep a s) :=
    fun _ _ _ => rfl
  have h_init' : ∀ᵐ s ∂μ₀, outputDeterminedInv s := by
    filter_upwards [h_init] with s hs
    exact initPred_outputDeterminedInv sec corr s hs
  exact AlmostBox_of_pure_inductive
    outputDeterminedInv
    (fun a s => avssStep a s)
    h_pure
    (fun a s _ h => avssStep_preserves_outputDeterminedInv a s h)
    μ₀ h_init' A

/-! ## §16. Termination

Termination is discharged via the deterministic specialisation of
`pi_n_AST_fair_with_progress_det`. The caller supplies (a)
trajectory-progress, (b) trajectory-mono on `U`, and (c)
trajectory-strict-decrease on fair firings, mirroring the
`brbProb_totality_AS_fair` shape (those three witnesses are
the protocol-specific bookkeeping that the certificate's
deterministic-specialisation soundness needs but the abstract
`FairnessAssumptions.isWeaklyFair` doesn't deliver — see
`Liveness.lean §"Trajectory progress witness gap"`). -/

/-! ### Per-action variant analysis

We bundle the per-action U-decrease analysis as named lemmas, so the
certificate constructor below is short and maps each field to one
lemma. -/

/-- Helper: cardinality of the honest-and-not-readySent filter (a
shorthand for the K^3-weighted summand of `avssU`). -/
def notReadySentSet (s : AVSSState n t F) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter
    (fun p => p ∉ s.corrupted ∧ (s.local_ p).readySent = false)

/-- Helper: cardinality of the honest-and-no-output filter (the
constant-weighted unfinished count). -/
def unfinishedSet (s : AVSSState n t F) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter
    (fun p => p ∉ s.corrupted ∧ (s.local_ p).output = none)

omit [Field F] [Fintype F] in
@[simp] theorem unfinishedSet_card_le (s : AVSSState n t F) :
    (unfinishedSet s).card ≤ n := by
  simpa [unfinishedSet] using Finset.card_le_univ
    ((Finset.univ : Finset (Fin n)).filter
      (fun p => p ∉ s.corrupted ∧ (s.local_ p).output = none))

omit [Field F] [Fintype F] in
@[simp] theorem notReadySentSet_card_le (s : AVSSState n t F) :
    (notReadySentSet s).card ≤ n := by
  simpa [notReadySentSet] using Finset.card_le_univ
    ((Finset.univ : Finset (Fin n)).filter
      (fun p => p ∉ s.corrupted ∧ (s.local_ p).readySent = false))

/-! #### `Inv` step preservation -/

omit [Field F] [Fintype F] in
/-- `Inv` is preserved by every gated action. -/
theorem avssTermInv_step
    (a : AVSSAction n F) (s : AVSSState n t F)
    (h : actionGate a s) (hinv : avssTermInv s)
    (s' : AVSSState n t F)
    (hs' : s' ∈ (PMF.pure (avssStep a s)).support) :
    avssTermInv s' := by
  classical
  -- Pure step: `s' = avssStep a s`.
  have hs_eq : s' = avssStep a s := by
    have : (PMF.pure (avssStep a s)).support = {avssStep a s} :=
      PMF.support_pure _
    rw [this] at hs'
    simpa using hs'
  subst hs_eq
  obtain ⟨hpre_clause, hready_clause⟩ := hinv
  refine ⟨?_, ?_⟩
  -- Clause 1: dealerSent = false post → init-fields-empty post.
  · intro hds'
    cases a with
    | dealerShare =>
        simp [avssStep] at hds'
    | partyDeliver p =>
        have hpre : s.dealerSent = true := h.1
        simp [avssStep, setLocal] at hds'
        rw [hpre] at hds'; cases hds'
    | partyEcho p q v =>
        have hpre : s.dealerSent = true := h
        simp [avssStep, setLocal] at hds'
        rw [hpre] at hds'; cases hds'
    | partyReady p =>
        have hgate := h
        by_cases hpre : s.dealerSent = true
        · simp [avssStep, setLocal, hpre] at hds'
        · push_neg at hpre
          have hpre' : s.dealerSent = false := by
            cases h_ds : s.dealerSent with
            | true => exact absurd h_ds hpre
            | false => rfl
          have hi := hpre_clause hpre'
          have hdel := (hi.1 p).1
          have : (s.local_ p).delivered = true := hgate.2.1
          rw [hdel] at this; cases this
    | partyReceiveReady p q =>
        have hgate := h
        by_cases hpre : s.dealerSent = true
        · simp [avssStep, setLocal, hpre] at hds'
        · push_neg at hpre
          have hpre' : s.dealerSent = false := by
            cases h_ds : s.dealerSent with
            | true => exact absurd h_ds hpre
            | false => rfl
          have hi := hpre_clause hpre'
          have hir : s.inflightReady = ∅ := hi.2.2
          have hq : q ∈ s.inflightReady := hgate.1
          rw [hir] at hq
          exact absurd hq (Finset.notMem_empty _)
    | partyOutput p =>
        have hgate := h
        by_cases hpre : s.dealerSent = true
        · simp [avssStep, setLocal, hpre] at hds'
        · push_neg at hpre
          have hpre' : s.dealerSent = false := by
            cases h_ds : s.dealerSent with
            | true => exact absurd h_ds hpre
            | false => rfl
          have hi := hpre_clause hpre'
          have hdel := (hi.1 p).1
          have : (s.local_ p).delivered = true := hgate.2.1
          rw [hdel] at this; cases this
  -- Clause 2: ∀ honest p, output.isSome → readySent.
  · intro p hp hsome
    cases a with
    | dealerShare =>
        -- avssStep doesn't change local_; reuse hready_clause.
        simp only [avssStep] at hsome ⊢
        exact hready_clause p hp hsome
    | partyDeliver q =>
        simp only [avssStep] at hsome ⊢
        by_cases hpq : p = q
        · subst hpq
          rw [setLocal_local_self] at hsome ⊢
          simp at hsome ⊢
          exact hready_clause p hp hsome
        · rw [setLocal_local_ne _ _ _ _ hpq] at hsome ⊢
          exact hready_clause p hp hsome
    | partyEcho q r v =>
        simp only [avssStep] at hsome ⊢
        by_cases hpq : p = q
        · subst hpq
          rw [setLocal_local_self] at hsome ⊢
          simp at hsome ⊢
          exact hready_clause p hp hsome
        · rw [setLocal_local_ne _ _ _ _ hpq] at hsome ⊢
          exact hready_clause p hp hsome
    | partyReady q =>
        simp only [avssStep] at hsome ⊢
        by_cases hpq : p = q
        · subst hpq
          simp [setLocal]
        · rw [setLocal_local_ne _ _ _ _ hpq] at hsome ⊢
          exact hready_clause p hp hsome
    | partyReceiveReady q r =>
        simp only [avssStep] at hsome ⊢
        by_cases hpq : p = q
        · subst hpq
          rw [setLocal_local_self] at hsome ⊢
          simp at hsome ⊢
          exact hready_clause p hp hsome
        · rw [setLocal_local_ne _ _ _ _ hpq] at hsome ⊢
          exact hready_clause p hp hsome
    | partyOutput q =>
        -- Gate ensures readySent=true at q.
        have hgate := h
        simp only [avssStep] at hsome ⊢
        by_cases hpq : p = q
        · subst hpq
          rw [setLocal_local_self] at hsome ⊢
          -- Post readySent = pre readySent (output update only).
          simp
          exact hgate.2.2.1
        · rw [setLocal_local_ne _ _ _ _ hpq] at hsome ⊢
          exact hready_clause p hp hsome

omit [Field F] [Fintype F] in
/-- Under `Inv s` and `terminated s`, `avssU s = 0`. -/
theorem avssU_eq_zero_of_terminated (s : AVSSState n t F)
    (hinv : avssTermInv s) (ht : terminated s) :
    avssU s = 0 := by
  classical
  unfold avssU
  obtain ⟨ht_out, hi1, hi2⟩ := ht
  -- The unfinished-set is empty.
  have h_unfin : ((Finset.univ : Finset (Fin n)).filter
      (fun p => p ∉ s.corrupted ∧ (s.local_ p).output = none)).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro p _ ⟨hp_h, hp_none⟩
    have := ht_out p hp_h
    rw [hp_none] at this
    simp at this
  -- The dom term is 0.  Two sub-cases:
  --   (a) dealerSent = true → if-guard makes it 0.
  --   (b) dealerSent = false → by Inv, all honest have output=none;
  --       combined with terminated (all honest have output=some _),
  --       no honest party exists, so honestSet.card = 0.
  have h_dom : (if s.dealerSent then (0 : ℕ) else (honestSet s).card) = 0 := by
    by_cases hds : s.dealerSent = true
    · simp [hds]
    · have hds' : s.dealerSent = false := by
        cases h_ds : s.dealerSent with
        | true => exact absurd h_ds hds
        | false => rfl
      have hi := hinv.1 hds'
      -- All honest p have output=none AND output=some _ → no honest exists.
      have hne : (honestSet s) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro p hp
        have hp_h : p ∉ s.corrupted := by
          simp [honestSet, Finset.mem_filter] at hp; exact hp
        have h_out_none : (s.local_ p).output = none := (hi.1 p).2.2
        have h_out_some : (s.local_ p).output.isSome = true := ht_out p hp_h
        rw [h_out_none] at h_out_some
        simp at h_out_some
      simp [hds', hne]
  -- The notReadySent set is empty.  By Inv clause 2, every honest p
  -- with `output.isSome=true` has `readySent=true`; combined with
  -- terminated's `output.isSome=true`, it follows readySent=true.
  have h_nrs : ((Finset.univ : Finset (Fin n)).filter
      (fun p => p ∉ s.corrupted ∧ (s.local_ p).readySent = false)).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro p _ ⟨hp_h, hp_nrs⟩
    have h_out_some : (s.local_ p).output.isSome = true := ht_out p hp_h
    have h_rs_true : (s.local_ p).readySent = true := hinv.2 p hp_h h_out_some
    rw [h_rs_true] at hp_nrs
    cases hp_nrs
  rw [h_dom, h_nrs, hi1, hi2, h_unfin]; simp

omit [Field F] [Fintype F] in
/-- `V_term` field: under terminated, `avssV s = 0`. -/
theorem avssCert_V_term (s : AVSSState n t F)
    (hinv : avssTermInv s) (ht : terminated s) :
    avssV s = 0 := by
  show (avssU s : ℝ≥0) = 0
  rw [avssU_eq_zero_of_terminated s hinv ht]
  simp

omit [Field F] [Fintype F] in
/-- `U_term` field: under terminated, `avssU s = 0`. -/
theorem avssCert_U_term (s : AVSSState n t F)
    (hinv : avssTermInv s) (ht : terminated s) :
    avssU s = 0 :=
  avssU_eq_zero_of_terminated s hinv ht

omit [Field F] [Fintype F] in
/-- `V_pos` field: at non-terminated, `avssV s > 0`. -/
theorem avssCert_V_pos (s : AVSSState n t F)
    (_hinv : avssTermInv s) (hnt : ¬ terminated s) :
    0 < avssV s := by
  show 0 < (avssU s : ℝ≥0)
  classical
  by_contra hcon
  push_neg at hcon
  have hU0_real : (avssU s : ℝ≥0) = 0 := le_antisymm hcon (zero_le _)
  have hU0 : avssU s = 0 := by exact_mod_cast hU0_real
  -- Decompose: each component must be 0.
  unfold avssU at hU0
  have hK1 : 1 ≤ (2 * n + 1) := by omega
  have hKsq : 1 ≤ (2 * n + 1) ^ 2 := Nat.one_le_pow _ _ hK1
  have hK3 : 1 ≤ (2 * n + 1) ^ 3 := Nat.one_le_pow _ _ hK1
  have hK4 : 1 ≤ (2 * n + 1) ^ 4 := Nat.one_le_pow _ _ hK1
  -- Component 1: dom term = 0.
  have hdom : (if s.dealerSent then (0 : ℕ) else (honestSet s).card) * (2 * n + 1) ^ 4 = 0 := by
    omega
  -- Component 2: notReadySent.card * K^3 = 0.
  have hnrs : ((Finset.univ : Finset (Fin n)).filter
      (fun p => p ∉ s.corrupted ∧ (s.local_ p).readySent = false)).card
      * (2 * n + 1) ^ 3 = 0 := by omega
  -- Component 3: inflightDeliveries.card * K^2 = 0.
  have hifd : s.inflightDeliveries.card * (2 * n + 1) ^ 2 = 0 := by omega
  -- Component 4: inflightReady.card * K = 0.
  have hifr : s.inflightReady.card * (2 * n + 1) = 0 := by omega
  -- Component 5: unfin.card = 0.
  have hunfin : ((Finset.univ : Finset (Fin n)).filter
      (fun p => p ∉ s.corrupted ∧ (s.local_ p).output = none)).card = 0 := by omega
  -- Each individual cardinal is 0.
  have hifd_card : s.inflightDeliveries.card = 0 := by
    have : (1 : ℕ) * (2 * n + 1) ^ 2 ≤ (2 * n + 1) ^ 2 := by linarith
    nlinarith
  have hifr_card : s.inflightReady.card = 0 := by
    nlinarith
  have hempty1 : s.inflightDeliveries = ∅ := Finset.card_eq_zero.mp hifd_card
  have hempty2 : s.inflightReady = ∅ := Finset.card_eq_zero.mp hifr_card
  have hfilter_empty :
      ((Finset.univ : Finset (Fin n)).filter
        (fun p => p ∉ s.corrupted ∧ (s.local_ p).output = none)) = ∅ :=
    Finset.card_eq_zero.mp hunfin
  have hno_unfin : ∀ p, p ∉ s.corrupted → (s.local_ p).output ≠ none := by
    intro p hp hnone
    have hin : p ∈ ((Finset.univ : Finset (Fin n)).filter
        (fun q => q ∉ s.corrupted ∧ (s.local_ q).output = none)) := by
      rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hp, hnone⟩
    rw [hfilter_empty] at hin
    exact (Finset.notMem_empty _ hin)
  apply hnt
  refine ⟨?_, hempty1, hempty2⟩
  intro p hp
  cases h_out : (s.local_ p).output with
  | none => exact absurd h_out (hno_unfin p hp)
  | some _ => simp

/-! #### Per-action U-step inequalities

We package each action's effect on `avssU` as a separate lemma.
For fair actions the decrease is strict; for `dealerShare` and
`partyEcho` we only get `≤`. -/

omit [Field F] [Fintype F] in
/-- `dealerShare` step: avssU non-increasing under Inv. -/
theorem avssU_step_dealerShare_le (s : AVSSState n t F)
    (hgate : actionGate (AVSSAction.dealerShare (n := n) (F := F)) s)
    (hinv : avssTermInv s) :
    avssU (avssStep AVSSAction.dealerShare s) ≤ avssU s := by
  classical
  have hds : s.dealerSent = false := hgate
  obtain ⟨hloc_init, hifd_emp, hifr_emp⟩ := hinv.1 hds
  -- Compute pre and post values explicitly.
  set K := 2 * n + 1 with hK_def
  have hK1 : 1 ≤ K := by omega
  -- Honest set abbreviations.
  set H := honestSet s with hH_def
  -- Post-state: dealerSent=true, inflightDeliveries := H, others unchanged.
  have hpost_ds :
      (avssStep AVSSAction.dealerShare s).dealerSent = true := by
    simp [avssStep]
  have hpost_ifd :
      (avssStep AVSSAction.dealerShare s).inflightDeliveries = H := by
    simp [avssStep, honestSet, hH_def]
  have hpost_ifr :
      (avssStep AVSSAction.dealerShare s).inflightReady = s.inflightReady := by
    simp [avssStep]
  have hpost_local :
      (avssStep AVSSAction.dealerShare s).local_ = s.local_ := by
    simp [avssStep]
  have hpost_corr :
      (avssStep AVSSAction.dealerShare s).corrupted = s.corrupted := by
    simp [avssStep]
  -- Filters (notReadySent, unfin) only depend on local_ and corrupted.
  have hpost_nrs_filt :
      ((Finset.univ : Finset (Fin n)).filter
        (fun p => p ∉ (avssStep AVSSAction.dealerShare s).corrupted ∧
          ((avssStep AVSSAction.dealerShare s).local_ p).readySent = false))
        =
      ((Finset.univ : Finset (Fin n)).filter
        (fun p => p ∉ s.corrupted ∧ (s.local_ p).readySent = false)) := by
    rw [hpost_corr, hpost_local]
  have hpost_unfin_filt :
      ((Finset.univ : Finset (Fin n)).filter
        (fun p => p ∉ (avssStep AVSSAction.dealerShare s).corrupted ∧
          ((avssStep AVSSAction.dealerShare s).local_ p).output = none))
        =
      ((Finset.univ : Finset (Fin n)).filter
        (fun p => p ∉ s.corrupted ∧ (s.local_ p).output = none)) := by
    rw [hpost_corr, hpost_local]
  have hpost_honest :
      honestSet (avssStep AVSSAction.dealerShare s) = H := by
    simp [honestSet, hpost_corr, hH_def]
  -- Now expand both sides.
  unfold avssU
  rw [hpost_ds, hpost_ifd, hpost_ifr, hpost_nrs_filt, hpost_unfin_filt,
      hpost_honest]
  rw [hds, hifd_emp, hifr_emp]
  simp only [Finset.card_empty, zero_mul, zero_add,
             Bool.false_eq_true, ↓reduceIte]
  -- Reduces to: H.card * K^2 ≤ H.card * K^4
  have hKle : K ^ 2 ≤ K ^ 4 := Nat.pow_le_pow_right hK1 (by omega)
  have hHmul : H.card * (2 * n + 1) ^ 2 ≤ H.card * (2 * n + 1) ^ 4 := by
    have : (2 * n + 1) ^ 2 ≤ (2 * n + 1) ^ 4 := hKle
    gcongr
  linarith

omit [Field F] [Fintype F] in
/-- `partyEcho` step: avssU is unchanged.  No filter or in-flight
component depends on the `echoesReceived` field. -/
theorem avssU_step_partyEcho_eq (s : AVSSState n t F) (p q : Fin n) (v : F)
    (_hgate : actionGate (AVSSAction.partyEcho p q v) s) :
    avssU (avssStep (AVSSAction.partyEcho p q v) s) = avssU s := by
  classical
  -- Each component of avssU depends only on dealerSent, corrupted, local_,
  -- inflightDeliveries, inflightReady; partyEcho only changes echoesReceived
  -- on a single party slot.  We rewrite each component.
  have hds : (avssStep (AVSSAction.partyEcho p q v) s).dealerSent =
      s.dealerSent := by simp [avssStep, setLocal]
  have hcorr : (avssStep (AVSSAction.partyEcho p q v) s).corrupted =
      s.corrupted := by simp [avssStep, setLocal]
  have hifd : (avssStep (AVSSAction.partyEcho p q v) s).inflightDeliveries =
      s.inflightDeliveries := by simp [avssStep, setLocal]
  have hifr : (avssStep (AVSSAction.partyEcho p q v) s).inflightReady =
      s.inflightReady := by simp [avssStep, setLocal]
  -- Each per-party readySent / output is unchanged.
  have hrs : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyEcho p q v) s).local_ x).readySent =
        (s.local_ x).readySent := by
    intro x
    by_cases hxp : x = p
    · subst hxp
      simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hout : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyEcho p q v) s).local_ x).output =
        (s.local_ x).output := by
    intro x
    by_cases hxp : x = p
    · subst hxp
      simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  -- Filters are equal.
  have hH : honestSet (avssStep (AVSSAction.partyEcho p q v) s) = honestSet s := by
    simp [honestSet, hcorr]
  have hnrs_filt :
      ((Finset.univ : Finset (Fin n)).filter
        (fun x => x ∉ (avssStep (AVSSAction.partyEcho p q v) s).corrupted ∧
          ((avssStep (AVSSAction.partyEcho p q v) s).local_ x).readySent = false))
        =
      ((Finset.univ : Finset (Fin n)).filter
        (fun x => x ∉ s.corrupted ∧ (s.local_ x).readySent = false)) := by
    apply Finset.filter_congr
    intro x _
    rw [hcorr, hrs]
  have hunfin_filt :
      ((Finset.univ : Finset (Fin n)).filter
        (fun x => x ∉ (avssStep (AVSSAction.partyEcho p q v) s).corrupted ∧
          ((avssStep (AVSSAction.partyEcho p q v) s).local_ x).output = none))
        =
      ((Finset.univ : Finset (Fin n)).filter
        (fun x => x ∉ s.corrupted ∧ (s.local_ x).output = none)) := by
    apply Finset.filter_congr
    intro x _
    rw [hcorr, hout]
  unfold avssU
  rw [hds, hifd, hifr, hH, hnrs_filt, hunfin_filt]

omit [Field F] [Fintype F] in
/-- `partyDeliver` step: avssU strictly decreases by `K^2`. -/
theorem avssU_step_partyDeliver_lt (s : AVSSState n t F) (p : Fin n)
    (hgate : actionGate (AVSSAction.partyDeliver p) s) :
    avssU (avssStep (AVSSAction.partyDeliver p) s) + (2 * n + 1) ^ 2
      ≤ avssU s := by
  classical
  obtain ⟨_, _, hpin, _⟩ := hgate
  -- Frame lemmas.
  have hds : (avssStep (AVSSAction.partyDeliver p) s).dealerSent =
      s.dealerSent := by simp [avssStep, setLocal]
  have hcorr : (avssStep (AVSSAction.partyDeliver p) s).corrupted =
      s.corrupted := by simp [avssStep, setLocal]
  have hifd : (avssStep (AVSSAction.partyDeliver p) s).inflightDeliveries =
      s.inflightDeliveries.erase p := by simp [avssStep]
  have hifr : (avssStep (AVSSAction.partyDeliver p) s).inflightReady =
      s.inflightReady := by simp [avssStep]
  -- Per-party fields touched by partyDeliver: only `delivered` of party p
  -- (set to true).  `readySent` and `output` unchanged for every party.
  have hrs : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyDeliver p) s).local_ x).readySent =
        (s.local_ x).readySent := by
    intro x
    by_cases hxp : x = p
    · subst hxp
      simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hout : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyDeliver p) s).local_ x).output =
        (s.local_ x).output := by
    intro x
    by_cases hxp : x = p
    · subst hxp
      simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  -- Filters equal.
  have hH : honestSet (avssStep (AVSSAction.partyDeliver p) s) =
      honestSet s := by simp [honestSet, hcorr]
  have hnrs_filt :
      ((Finset.univ : Finset (Fin n)).filter
        (fun x => x ∉ (avssStep (AVSSAction.partyDeliver p) s).corrupted ∧
          ((avssStep (AVSSAction.partyDeliver p) s).local_ x).readySent = false))
        =
      ((Finset.univ : Finset (Fin n)).filter
        (fun x => x ∉ s.corrupted ∧ (s.local_ x).readySent = false)) := by
    apply Finset.filter_congr
    intro x _; rw [hcorr, hrs]
  have hunfin_filt :
      ((Finset.univ : Finset (Fin n)).filter
        (fun x => x ∉ (avssStep (AVSSAction.partyDeliver p) s).corrupted ∧
          ((avssStep (AVSSAction.partyDeliver p) s).local_ x).output = none))
        =
      ((Finset.univ : Finset (Fin n)).filter
        (fun x => x ∉ s.corrupted ∧ (s.local_ x).output = none)) := by
    apply Finset.filter_congr
    intro x _; rw [hcorr, hout]
  -- Card of erased: card - 1 (since p ∈ inflightDeliveries).
  have hcard : (s.inflightDeliveries.erase p).card =
      s.inflightDeliveries.card - 1 := Finset.card_erase_of_mem hpin
  have hcard_pos : 1 ≤ s.inflightDeliveries.card := by
    have := Finset.card_pos.mpr ⟨p, hpin⟩; omega
  -- Now compute.
  unfold avssU
  rw [hds, hifd, hifr, hH, hnrs_filt, hunfin_filt, hcard]
  set ifdc := s.inflightDeliveries.card with hifdc_def
  -- Goal: post + K^2 ≤ pre, where post and pre share most terms,
  -- differ only in ifdc * K^2 → (ifdc - 1) * K^2 + K^2.
  have h_split : (ifdc - 1) * (2 * n + 1) ^ 2 + (2 * n + 1) ^ 2
                = ifdc * (2 * n + 1) ^ 2 := by
    have : ifdc - 1 + 1 = ifdc := Nat.sub_add_cancel hcard_pos
    calc (ifdc - 1) * (2 * n + 1) ^ 2 + (2 * n + 1) ^ 2
        = ((ifdc - 1) + 1) * (2 * n + 1) ^ 2 := by ring
      _ = ifdc * (2 * n + 1) ^ 2 := by rw [this]
  linarith

omit [Field F] [Fintype F] in
/-- `partyReady` step: avssU strictly decreases.  The K^3 decrease in
the notReadySent component dominates the at-most-K increase in
inflightReady. -/
theorem avssU_step_partyReady_lt (s : AVSSState n t F) (p : Fin n)
    (hgate : actionGate (AVSSAction.partyReady p) s)
    (hinv : avssTermInv s) :
    avssU (avssStep (AVSSAction.partyReady p) s) + 1 ≤ avssU s := by
  classical
  obtain ⟨hphon, hdel_t, hrsf⟩ := hgate
  -- By Inv, dealerSent must be true (else delivered=false for all by Inv,
  -- contradicting gate's `delivered=true`).
  have hds_pre : s.dealerSent = true := by
    by_contra hbad
    have hds_pre' : s.dealerSent = false := by
      cases h : s.dealerSent with
      | true => exact absurd h hbad
      | false => rfl
    have hi := hinv.1 hds_pre'
    have hdel := (hi.1 p).1
    rw [hdel] at hdel_t; cases hdel_t
  -- Frame lemmas.
  have hds : (avssStep (AVSSAction.partyReady p) s).dealerSent = s.dealerSent := by
    simp [avssStep, setLocal]
  have hcorr : (avssStep (AVSSAction.partyReady p) s).corrupted = s.corrupted := by
    simp [avssStep, setLocal]
  have hifd : (avssStep (AVSSAction.partyReady p) s).inflightDeliveries =
      s.inflightDeliveries := by simp [avssStep]
  have hifr : (avssStep (AVSSAction.partyReady p) s).inflightReady =
      insert p s.inflightReady := by simp [avssStep]
  -- Per-party fields: readySent_p flips false→true; output unchanged.
  have hrs_p : ((avssStep (AVSSAction.partyReady p) s).local_ p).readySent = true := by
    simp [avssStep]
  have hrs_ne : ∀ x : Fin n, x ≠ p →
      ((avssStep (AVSSAction.partyReady p) s).local_ x).readySent =
        (s.local_ x).readySent := by
    intro x hxp
    simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hout_p : ((avssStep (AVSSAction.partyReady p) s).local_ p).output =
      (s.local_ p).output := by simp [avssStep]
  have hout_ne : ∀ x : Fin n, x ≠ p →
      ((avssStep (AVSSAction.partyReady p) s).local_ x).output =
        (s.local_ x).output := by
    intro x hxp
    simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  -- Filter for unfin: unchanged.
  have hH : honestSet (avssStep (AVSSAction.partyReady p) s) = honestSet s := by
    simp [honestSet, hcorr]
  have hunfin_filt :
      ((Finset.univ : Finset (Fin n)).filter
        (fun x => x ∉ (avssStep (AVSSAction.partyReady p) s).corrupted ∧
          ((avssStep (AVSSAction.partyReady p) s).local_ x).output = none))
        =
      ((Finset.univ : Finset (Fin n)).filter
        (fun x => x ∉ s.corrupted ∧ (s.local_ x).output = none)) := by
    apply Finset.filter_congr
    intro x _; rw [hcorr]
    by_cases hxp : x = p
    · subst hxp; rw [hout_p]
    · rw [hout_ne x hxp]
  -- Filter for nrs: post = pre.erase p.
  have hnrs_post_eq_erase :
      ((Finset.univ : Finset (Fin n)).filter
        (fun x => x ∉ (avssStep (AVSSAction.partyReady p) s).corrupted ∧
          ((avssStep (AVSSAction.partyReady p) s).local_ x).readySent = false))
        =
      ((Finset.univ : Finset (Fin n)).filter
        (fun x => x ∉ s.corrupted ∧ (s.local_ x).readySent = false)).erase p := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    rw [hcorr]
    by_cases hxp : x = p
    · subst hxp
      rw [hrs_p]
      simp
    · rw [hrs_ne x hxp]
      simp [hxp]
  have hp_in_pre : p ∈ ((Finset.univ : Finset (Fin n)).filter
        (fun x => x ∉ s.corrupted ∧ (s.local_ x).readySent = false)) := by
    rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hphon, hrsf⟩
  have hnrs_card_post :
      (((Finset.univ : Finset (Fin n)).filter
        (fun x => x ∉ (avssStep (AVSSAction.partyReady p) s).corrupted ∧
          ((avssStep (AVSSAction.partyReady p) s).local_ x).readySent = false))).card
        = ((Finset.univ : Finset (Fin n)).filter
        (fun x => x ∉ s.corrupted ∧ (s.local_ x).readySent = false)).card - 1 := by
    rw [hnrs_post_eq_erase, Finset.card_erase_of_mem hp_in_pre]
  have hnrs_pre_pos : 1 ≤ ((Finset.univ : Finset (Fin n)).filter
        (fun x => x ∉ s.corrupted ∧ (s.local_ x).readySent = false)).card := by
    have := Finset.card_pos.mpr ⟨p, hp_in_pre⟩; omega
  -- inflightReady card: card_insert_le, but possibly equal pre+1 if p ∉ pre.
  have hifr_card_le : (insert p s.inflightReady).card ≤ s.inflightReady.card + 1 :=
    Finset.card_insert_le _ _
  -- Now compute.
  unfold avssU
  rw [hds, hifd, hifr, hH, hunfin_filt, hnrs_card_post]
  -- Set abbreviations.
  set nrs := ((Finset.univ : Finset (Fin n)).filter
    (fun x => x ∉ s.corrupted ∧ (s.local_ x).readySent = false)).card
    with hnrs_def
  set ifrc := s.inflightReady.card with hifrc_def
  set ifrc' := (insert p s.inflightReady).card with hifrc'_def
  -- Goal: dom_post + (nrs - 1) * K^3 + ifd * K^2 + ifrc' * K + unfin + 1
  --     ≤ dom_pre + nrs * K^3 + ifd * K^2 + ifrc * K + unfin
  -- Cancel common terms; need: (nrs-1)*K^3 + ifrc'*K + 1 ≤ nrs*K^3 + ifrc*K
  -- i.e., ifrc'*K + 1 ≤ K^3 + ifrc*K
  -- Since ifrc' ≤ ifrc + 1, ifrc'*K ≤ ifrc*K + K. So suffices: ifrc*K + K + 1 ≤ K^3 + ifrc*K
  -- i.e., K + 1 ≤ K^3.
  -- For K ≥ 2: K^3 = K*K^2 ≥ 2*K^2 ≥ 2*(K+1) = 2K+2 ≥ K+1+K ≥ K+1 ✓.
  -- For K = 1 (n=0): no Fin n, vacuous.
  -- General: K^3 - K - 1 ≥ 0 for K ≥ 2.
  have hK1 : 1 ≤ (2 * n + 1) := by omega
  -- We need to handle n = 0 separately.
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; exact p.elim0
  · have hK_ge_3 : 3 ≤ (2 * n + 1) := by omega
    have hK3_ge : (2 * n + 1) ^ 3 ≥ (2 * n + 1) + 1 := by
      have : (2 * n + 1) ^ 3 = (2 * n + 1) * (2 * n + 1) * (2 * n + 1) := by ring
      nlinarith
    have hifrc_K : ifrc' * (2 * n + 1) ≤ ifrc * (2 * n + 1) + (2 * n + 1) := by
      have : ifrc' ≤ ifrc + 1 := hifr_card_le
      nlinarith
    -- dom term: pre dom = 0 (dealerSent = true), post dom = 0 (also true).
    -- The dom term cancels: pre dealerSent=true.
    rw [hds_pre]
    simp only [if_true, zero_mul]
    -- Rewrite (nrs - 1) using nrs ≥ 1.
    have hnrs_split : (nrs - 1) * (2 * n + 1) ^ 3 + (2 * n + 1) ^ 3
                    = nrs * (2 * n + 1) ^ 3 := by
      have : nrs - 1 + 1 = nrs := Nat.sub_add_cancel hnrs_pre_pos
      calc (nrs - 1) * (2 * n + 1) ^ 3 + (2 * n + 1) ^ 3
          = ((nrs - 1) + 1) * (2 * n + 1) ^ 3 := by ring
        _ = nrs * (2 * n + 1) ^ 3 := by rw [this]
    -- Now goal is essentially: ifrc' * K + 1 ≤ K^3 + ifrc * K.
    -- Suffices: K + 1 ≤ K^3 (then K^3 ≥ K+1 ≥ ifrc'-ifrc + 1 = K - 0 + 1).
    -- ifrc'*K ≤ ifrc*K + K, so ifrc'*K + 1 ≤ ifrc*K + K + 1 ≤ ifrc*K + K^3.
    nlinarith [hK3_ge, hifrc_K, hnrs_split, hnrs_pre_pos]

omit [Field F] [Fintype F] in
/-- `partyReceiveReady` step: avssU strictly decreases by `K`. -/
theorem avssU_step_partyReceiveReady_lt (s : AVSSState n t F) (p q : Fin n)
    (hgate : actionGate (AVSSAction.partyReceiveReady p q) s)
    (hinv : avssTermInv s) :
    avssU (avssStep (AVSSAction.partyReceiveReady p q) s) + 1 ≤ avssU s := by
  classical
  obtain ⟨hqin, _⟩ := hgate
  -- By Inv, dealerSent must be true (else inflightReady = ∅, contradicts hqin).
  have hds_pre : s.dealerSent = true := by
    by_contra hbad
    have hds_pre' : s.dealerSent = false := by
      cases h : s.dealerSent with
      | true => exact absurd h hbad
      | false => rfl
    have hi := hinv.1 hds_pre'
    have hir : s.inflightReady = ∅ := hi.2.2
    rw [hir] at hqin
    exact absurd hqin (Finset.notMem_empty _)
  -- Frame lemmas.
  have hds : (avssStep (AVSSAction.partyReceiveReady p q) s).dealerSent =
      s.dealerSent := by simp [avssStep, setLocal]
  have hcorr : (avssStep (AVSSAction.partyReceiveReady p q) s).corrupted =
      s.corrupted := by simp [avssStep, setLocal]
  have hifd : (avssStep (AVSSAction.partyReceiveReady p q) s).inflightDeliveries =
      s.inflightDeliveries := by simp [avssStep]
  have hifr : (avssStep (AVSSAction.partyReceiveReady p q) s).inflightReady =
      s.inflightReady.erase q := by simp [avssStep]
  -- Per-party fields: only readyReceived is touched (not in U).
  have hrs : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyReceiveReady p q) s).local_ x).readySent =
        (s.local_ x).readySent := by
    intro x
    by_cases hxp : x = p
    · subst hxp
      simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hout : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyReceiveReady p q) s).local_ x).output =
        (s.local_ x).output := by
    intro x
    by_cases hxp : x = p
    · subst hxp
      simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  -- Filters equal.
  have hH : honestSet (avssStep (AVSSAction.partyReceiveReady p q) s) =
      honestSet s := by simp [honestSet, hcorr]
  have hnrs_filt :
      ((Finset.univ : Finset (Fin n)).filter
        (fun x => x ∉ (avssStep (AVSSAction.partyReceiveReady p q) s).corrupted ∧
          ((avssStep (AVSSAction.partyReceiveReady p q) s).local_ x).readySent = false))
        =
      ((Finset.univ : Finset (Fin n)).filter
        (fun x => x ∉ s.corrupted ∧ (s.local_ x).readySent = false)) := by
    apply Finset.filter_congr
    intro x _; rw [hcorr, hrs]
  have hunfin_filt :
      ((Finset.univ : Finset (Fin n)).filter
        (fun x => x ∉ (avssStep (AVSSAction.partyReceiveReady p q) s).corrupted ∧
          ((avssStep (AVSSAction.partyReceiveReady p q) s).local_ x).output = none))
        =
      ((Finset.univ : Finset (Fin n)).filter
        (fun x => x ∉ s.corrupted ∧ (s.local_ x).output = none)) := by
    apply Finset.filter_congr
    intro x _; rw [hcorr, hout]
  have hcard : (s.inflightReady.erase q).card = s.inflightReady.card - 1 :=
    Finset.card_erase_of_mem hqin
  have hcard_pos : 1 ≤ s.inflightReady.card := by
    have := Finset.card_pos.mpr ⟨q, hqin⟩; omega
  unfold avssU
  rw [hds, hifd, hifr, hH, hnrs_filt, hunfin_filt, hcard, hds_pre]
  simp only [if_true, zero_mul]
  set ifrc := s.inflightReady.card with hifrc_def
  -- Goal: 0 + nrs*K^3 + ifd*K^2 + (ifrc-1)*K + unfin + 1
  --     ≤ 0 + nrs*K^3 + ifd*K^2 + ifrc*K + unfin
  have h_split : (ifrc - 1) * (2 * n + 1) + (2 * n + 1) = ifrc * (2 * n + 1) := by
    have : ifrc - 1 + 1 = ifrc := Nat.sub_add_cancel hcard_pos
    calc (ifrc - 1) * (2 * n + 1) + (2 * n + 1)
        = ((ifrc - 1) + 1) * (2 * n + 1) := by ring
      _ = ifrc * (2 * n + 1) := by rw [this]
  have hKgt1 : 1 ≤ (2 * n + 1) := by omega
  nlinarith [h_split, hKgt1]

omit [Field F] [Fintype F] in
/-- `partyOutput` step: avssU strictly decreases by `1`. -/
theorem avssU_step_partyOutput_lt (s : AVSSState n t F) (p : Fin n)
    (hgate : actionGate (AVSSAction.partyOutput p) s)
    (hinv : avssTermInv s) :
    avssU (avssStep (AVSSAction.partyOutput p) s) + 1 ≤ avssU s := by
  classical
  obtain ⟨hphon, hdel_t, _hrs_t, hout_none⟩ := hgate
  -- By Inv, dealerSent must be true.
  have hds_pre : s.dealerSent = true := by
    by_contra hbad
    have hds_pre' : s.dealerSent = false := by
      cases h : s.dealerSent with
      | true => exact absurd h hbad
      | false => rfl
    have hi := hinv.1 hds_pre'
    have hdel := (hi.1 p).1
    rw [hdel] at hdel_t; cases hdel_t
  -- Frame lemmas.
  have hds : (avssStep (AVSSAction.partyOutput p) s).dealerSent =
      s.dealerSent := by simp [avssStep, setLocal]
  have hcorr : (avssStep (AVSSAction.partyOutput p) s).corrupted =
      s.corrupted := by simp [avssStep, setLocal]
  have hifd : (avssStep (AVSSAction.partyOutput p) s).inflightDeliveries =
      s.inflightDeliveries := by simp [avssStep]
  have hifr : (avssStep (AVSSAction.partyOutput p) s).inflightReady =
      s.inflightReady := by simp [avssStep]
  -- Per-party fields: readySent unchanged; output_p flips none → some _.
  have hrs : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyOutput p) s).local_ x).readySent =
        (s.local_ x).readySent := by
    intro x
    by_cases hxp : x = p
    · subst hxp
      simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hout_p : ((avssStep (AVSSAction.partyOutput p) s).local_ p).output =
      some (s.coeffs 0 0) := by simp [avssStep]
  have hout_ne : ∀ x : Fin n, x ≠ p →
      ((avssStep (AVSSAction.partyOutput p) s).local_ x).output =
        (s.local_ x).output := by
    intro x hxp
    simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  -- Filters: nrs unchanged.
  have hH : honestSet (avssStep (AVSSAction.partyOutput p) s) =
      honestSet s := by simp [honestSet, hcorr]
  have hnrs_filt :
      ((Finset.univ : Finset (Fin n)).filter
        (fun x => x ∉ (avssStep (AVSSAction.partyOutput p) s).corrupted ∧
          ((avssStep (AVSSAction.partyOutput p) s).local_ x).readySent = false))
        =
      ((Finset.univ : Finset (Fin n)).filter
        (fun x => x ∉ s.corrupted ∧ (s.local_ x).readySent = false)) := by
    apply Finset.filter_congr
    intro x _; rw [hcorr, hrs]
  -- unfin filter: post = pre.erase p (since p was in, now isn't).
  have hp_in_pre :
      p ∈ ((Finset.univ : Finset (Fin n)).filter
        (fun x => x ∉ s.corrupted ∧ (s.local_ x).output = none)) := by
    rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hphon, hout_none⟩
  have hunfin_post_eq_erase :
      ((Finset.univ : Finset (Fin n)).filter
        (fun x => x ∉ (avssStep (AVSSAction.partyOutput p) s).corrupted ∧
          ((avssStep (AVSSAction.partyOutput p) s).local_ x).output = none))
        =
      ((Finset.univ : Finset (Fin n)).filter
        (fun x => x ∉ s.corrupted ∧ (s.local_ x).output = none)).erase p := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    rw [hcorr]
    by_cases hxp : x = p
    · subst hxp
      rw [hout_p]
      simp
    · rw [hout_ne x hxp]
      simp [hxp]
  have hunfin_card_post :
      (((Finset.univ : Finset (Fin n)).filter
        (fun x => x ∉ (avssStep (AVSSAction.partyOutput p) s).corrupted ∧
          ((avssStep (AVSSAction.partyOutput p) s).local_ x).output = none))).card
        = ((Finset.univ : Finset (Fin n)).filter
        (fun x => x ∉ s.corrupted ∧ (s.local_ x).output = none)).card - 1 := by
    rw [hunfin_post_eq_erase, Finset.card_erase_of_mem hp_in_pre]
  have hunfin_pre_pos : 1 ≤ ((Finset.univ : Finset (Fin n)).filter
        (fun x => x ∉ s.corrupted ∧ (s.local_ x).output = none)).card := by
    have := Finset.card_pos.mpr ⟨p, hp_in_pre⟩; omega
  unfold avssU
  rw [hds, hifd, hifr, hH, hnrs_filt, hunfin_card_post, hds_pre]
  simp only [if_true, zero_mul]
  set unfin := ((Finset.univ : Finset (Fin n)).filter
    (fun x => x ∉ s.corrupted ∧ (s.local_ x).output = none)).card
    with hunfin_def
  -- Goal: 0 + nrs*K^3 + ifd*K^2 + ifr*K + (unfin - 1) + 1
  --     ≤ 0 + nrs*K^3 + ifd*K^2 + ifr*K + unfin
  omega

omit [Field F] [Fintype F] in
/-- Composite per-action U-decrease ≤: every gated action keeps avssU
non-increasing under Inv. -/
theorem avssU_step_le (a : AVSSAction n F) (s : AVSSState n t F)
    (h : actionGate a s) (hinv : avssTermInv s) :
    avssU (avssStep a s) ≤ avssU s := by
  cases a with
  | dealerShare => exact avssU_step_dealerShare_le s h hinv
  | partyDeliver p =>
      have := avssU_step_partyDeliver_lt s p h
      omega
  | partyEcho p q v =>
      rw [avssU_step_partyEcho_eq s p q v h]
  | partyReady p =>
      have := avssU_step_partyReady_lt s p h hinv
      omega
  | partyReceiveReady p q =>
      have := avssU_step_partyReceiveReady_lt s p q h hinv
      omega
  | partyOutput p =>
      have := avssU_step_partyOutput_lt s p h hinv
      omega

omit [Field F] [Fintype F] in
/-- For fair actions, avssU strictly decreases. -/
theorem avssU_step_lt_of_fair (a : AVSSAction n F) (s : AVSSState n t F)
    (h : actionGate a s) (hfair : a ∈ avssFairActions)
    (hinv : avssTermInv s) :
    avssU (avssStep a s) < avssU s := by
  cases a with
  | dealerShare => simp [avssFairActions] at hfair
  | partyDeliver p =>
      have := avssU_step_partyDeliver_lt s p h
      have hKpow : 1 ≤ (2 * n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega
  | partyEcho p q v => simp [avssFairActions] at hfair
  | partyReady p =>
      have := avssU_step_partyReady_lt s p h hinv
      omega
  | partyReceiveReady p q =>
      have := avssU_step_partyReceiveReady_lt s p q h hinv
      omega
  | partyOutput p =>
      have := avssU_step_partyOutput_lt s p h hinv
      omega

/-- The AVSS termination certificate.

All fields are closed.  `V_super_fair`, `U_dec_det`, and
`U_dec_prob` follow from `avssU_step_lt_of_fair` (each fair
action strictly decreases the lex-product variant `avssU`); `V_super`
follows from `avssU_step_le` (every gated action is non-increasing).
The Dirac kernel reduces every supermartingale `tsum` to a single
term, so the variant analysis becomes a `ℕ`-arithmetic exercise. -/
noncomputable def avssCert (sec : F) (corr : Finset (Fin n)) :
    FairASTCertificate (avssSpec (t := t) sec corr) avssFair terminated where
  Inv := avssTermInv
  V := avssV
  U := avssU
  inv_init := fun s hinit => by
    obtain ⟨hloc, _, _, hidl, hird, _, _⟩ := hinit
    refine ⟨?_, ?_⟩
    · intro _
      refine ⟨?_, hidl, hird⟩
      intro p
      rw [hloc p]
      exact ⟨rfl, rfl, rfl⟩
    · intro p _ hsome
      rw [hloc p] at hsome
      simp [AVSSLocalState.init] at hsome
  inv_step := avssTermInv_step
  V_term := avssCert_V_term
  V_pos := avssCert_V_pos
  V_super := fun a s h hinv _hnt => Or.inl <| by
    classical
    have heff : ((avssSpec (t := t) sec corr).actions a).effect s h
                = PMF.pure (avssStep a s) := rfl
    rw [heff]
    rw [tsum_eq_single (avssStep a s)]
    · rw [PMF.pure_apply, if_pos rfl, one_mul]
      have h_le : avssU (avssStep a s) ≤ avssU s := avssU_step_le a s h hinv
      have : avssV (avssStep a s) ≤ avssV s := by
        show (avssU (avssStep a s) : ℝ≥0) ≤ (avssU s : ℝ≥0)
        exact_mod_cast h_le
      exact_mod_cast this
    · intro b hb
      rw [PMF.pure_apply, if_neg hb, zero_mul]
  V_super_fair := fun a s h hfair hinv _hnt => Or.inl <| by
    classical
    have heff : ((avssSpec (t := t) sec corr).actions a).effect s h
                = PMF.pure (avssStep a s) := rfl
    rw [heff]
    rw [tsum_eq_single (avssStep a s)]
    · rw [PMF.pure_apply, if_pos rfl, one_mul]
      have hfair' : a ∈ avssFairActions := hfair
      have hlt : avssU (avssStep a s) < avssU s :=
        avssU_step_lt_of_fair a s h hfair' hinv
      have : avssV (avssStep a s) < avssV s := by
        show (avssU (avssStep a s) : ℝ≥0) < (avssU s : ℝ≥0)
        exact_mod_cast hlt
      exact_mod_cast this
    · intro b hb
      rw [PMF.pure_apply, if_neg hb, zero_mul]
  U_term := avssCert_U_term
  U_dec_det := fun a s h hfair hinv _hnt s' hs' => by
    classical
    have heff : ((avssSpec (t := t) sec corr).actions a).effect s h
                = PMF.pure (avssStep a s) := rfl
    rw [heff] at hs'
    rw [PMF.support_pure] at hs'
    have hs_eq : s' = avssStep a s := by simpa using hs'
    subst hs_eq
    left
    have hfair' : a ∈ avssFairActions := hfair
    exact avssU_step_lt_of_fair a s h hfair' hinv
  U_bdd_subl := fun _ =>
    ⟨(5 * n + 5) * (2 * n + 1) ^ 4, fun s _ _ => avssU_le_bound s⟩
  V_init_bdd :=
    ⟨((5 * n + 5) * (2 * n + 1) ^ 4 : ℕ), fun s _ => by
      show ((avssU s : ℝ≥0)) ≤ (((5 * n + 5) * (2 * n + 1) ^ 4 : ℕ) : ℝ≥0)
      exact_mod_cast avssU_le_bound s⟩

/-- Termination as an `AlmostDiamond` under a trajectory-fair
adversary. Discharged via `FairASTCertificate.sound`. Both the
sublevel-finite-variant lemma `pi_n_AST_fair` and the assembly
`partition_almostDiamond_fair` are closed sorry-free in
`Liveness.lean`; this theorem is axiom-clean
(`[propext, Classical.choice, Quot.sound]`). -/
theorem avss_termination_AS_fair
    (sec : F) (corr : Finset (Fin n))
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr s)
    (A : Leslie.Prob.TrajectoryFairAdversary
            (avssSpec (t := t) sec corr) avssFair μ₀)
    (h_U_mono : FairASTCertificate.TrajectoryUMono
        (avssSpec (t := t) sec corr) avssFair
        (avssCert (t := t) sec corr) μ₀ A.toFair)
    (h_U_strict : ∀ N : ℕ, FairASTCertificate.TrajectoryFairStrictDecrease
        (avssSpec (t := t) sec corr) avssFair
        (avssCert (t := t) sec corr) μ₀ A.toFair N) :
    AlmostDiamond (avssSpec (t := t) sec corr) A.toAdversary μ₀ terminated := by
  have h_init' : ∀ᵐ s ∂μ₀, (avssCert (t := t) sec corr).Inv s := by
    filter_upwards [h_init] with s hs
    exact (avssCert (t := t) sec corr).inv_init s hs
  exact FairASTCertificate.sound
    (avssCert (t := t) sec corr) μ₀ h_init' A.toFair A.progress
    h_U_mono h_U_strict

/-- Trajectory-form variant of `avss_termination_AS_fair`.

Discharges termination through the deterministic specialisation
`FairASTCertificate.pi_n_AST_fair_with_progress_det` plus
`pi_infty_zero_fair`, both closed sorry-free in `Liveness.lean`.
Equivalent in conclusion to `avss_termination_AS_fair` (which uses
`partition_almostDiamond_fair`); this variant is exposed for
callers that prefer the explicit deterministic-descent route.

Takes three additional witnesses bundled with the adversary:

  * `A : TrajectoryFairAdversary` — bundles a `FairAdversary` with the
    trajectory-form `TrajectoryFairProgress` witness (AE-i.o. firing of
    fair actions along the trace).
  * `h_U_mono : TrajectoryUMono` — `cert.U` is non-increasing along
    every trajectory step.
  * `h_U_strict : ∀ N, TrajectoryFairStrictDecrease ... N` — at every
    step from a state in the V≤N sublevel, a fair firing strictly
    decreases `cert.U`.

For the deterministic AVSS protocol (every effect is `PMF.pure`) the
last two witnesses are derivable from `avssCert`'s
`U_dec_det`/`V_super`/`V_super_fair` fields, but threading the
derivation here is a separate ~100-LOC trajectory-plumbing
exercise. Both `avss_termination_AS_fair` and this variant are
axiom-clean (`#print axioms` shows
`[propext, Classical.choice, Quot.sound]` only, no `sorryAx`).

The proof structure mirrors `partition_almostDiamond_fair` with
`pi_n_AST_fair` swapped for `pi_n_AST_fair_with_progress_det`.
A consumer-friendly `FairASTCertificate.sound_traj_det` corollary
that packages this is deferred in `Liveness.lean` due to a `whnf`
heartbeat blowup during signature elaboration; until then concrete
protocols call this trajectory route directly. -/
theorem avss_termination_AS_fair_traj
    (sec : F) (corr : Finset (Fin n))
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr s)
    (A : Leslie.Prob.TrajectoryFairAdversary
            (avssSpec (t := t) sec corr) avssFair μ₀)
    (h_U_mono : FairASTCertificate.TrajectoryUMono
        (avssSpec (t := t) sec corr) avssFair
        (avssCert (t := t) sec corr) μ₀ A.toFair)
    (h_U_strict : ∀ N : ℕ, FairASTCertificate.TrajectoryFairStrictDecrease
        (avssSpec (t := t) sec corr) avssFair
        (avssCert (t := t) sec corr) μ₀ A.toFair N) :
    AlmostDiamond (avssSpec (t := t) sec corr) A.toAdversary μ₀ terminated := by
  -- Build the certificate-level invariant initialisation.
  have h_init_inv : ∀ᵐ s ∂μ₀, (avssCert (t := t) sec corr).Inv s := by
    filter_upwards [h_init] with s hs
    exact (avssCert (t := t) sec corr).inv_init s hs
  -- Inline the `partition_almostDiamond_fair` argument with
  -- `pi_n_AST_fair_with_progress_det` in place of `pi_n_AST_fair`.
  set cert := avssCert (t := t) sec corr with hcertdef
  unfold AlmostDiamond
  -- Bounded-or-unbounded dichotomy on V along every trajectory.
  have hbounded_or_unbounded :
      ∀ ω : Trace (AVSSState n t F) (AVSSAction n F),
        (∃ N : ℕ, ∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0)) ∨
        (∀ N : ℕ, ¬ (∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0))) := by
    intro ω
    by_cases h : ∃ N : ℕ, ∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0)
    · exact .inl h
    · refine .inr ?_
      intro N hbnd
      exact h ⟨N, hbnd⟩
  -- The unbounded set is null (`pi_infty_zero_fair`, closed).
  have h_inf_null :
      ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr) A.toAdversary μ₀),
      ¬ (∀ N : ℕ, ¬ (∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0))) := by
    rw [ae_iff]
    have heq :
        {a : Trace (AVSSState n t F) (AVSSAction n F) |
            ¬ ¬ ∀ N : ℕ, ¬ (∀ n, cert.V (a n).1 ≤ (N : ℝ≥0))} =
        {ω : Trace (AVSSState n t F) (AVSSAction n F) |
            ∀ N : ℕ, ¬ (∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0))} := by
      ext ω; simp
    rw [heq]
    -- `A.toAdversary = A.toFair.toAdversary` by definition of
    -- `TrajectoryFairAdversary.toAdversary`.
    exact FairASTCertificate.pi_infty_zero_fair cert μ₀ h_init_inv A.toFair
  -- Each sublevel is AE-terminating (`pi_n_AST_fair_with_progress_det`,
  -- closed sorry-free).
  have h_each_N : ∀ N : ℕ,
      ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr) A.toAdversary μ₀),
        (∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0)) → ∃ n, terminated (ω n).1 :=
    fun N => FairASTCertificate.pi_n_AST_fair_with_progress_det
      cert μ₀ h_init_inv A.toFair A.progress N h_U_mono (h_U_strict N)
  rw [← MeasureTheory.ae_all_iff] at h_each_N
  filter_upwards [h_each_N, h_inf_null] with ω hN h_inf
  rcases hbounded_or_unbounded ω with ⟨N, hbnd⟩ | hunb
  · exact hN N hbnd
  · exact absurd hunb h_inf

/-! ## §17. Secrecy

Direct passthrough to `BivariateShamir.bivariate_shamir_secrecy`. The
post-deal grid view at any `t`-coalition is independent of the secret.

This is the **grid form** of secrecy — option (b) in the SyncVSS
brief, and the same form `bivariate_evals_uniform` directly delivers.
The full **row + column** view secrecy (a strict generalization) is
the `+200 LOC` polynomial-manipulation step explicitly deferred in
`SyncVSS.lean §10`; we inherit the same deferral here. -/

/-- AVSS coalition-view secrecy (grid form). -/
theorem avss_secrecy (partyPoint : Fin n → F)
    (h_nz_pp : ∀ i, partyPoint i ≠ 0)
    (h_F : t + 1 ≤ Fintype.card F)
    (C D : BivariateShamir.Coalition n t) (sec sec' : F) :
    (Leslie.Prob.Polynomial.uniformBivariateWithFixedZero t t sec).map
        (fun f => fun (i : C.val) (j : D.val) =>
          some ((f.eval (Polynomial.C (partyPoint i.val))).eval
            (partyPoint j.val)))
      =
    (Leslie.Prob.Polynomial.uniformBivariateWithFixedZero t t sec').map
        (fun f => fun (i : C.val) (j : D.val) =>
          some ((f.eval (Polynomial.C (partyPoint i.val))).eval
            (partyPoint j.val))) :=
  BivariateShamir.bivariate_shamir_secrecy partyPoint h_nz_pp h_F C D sec sec'

/-! ## §18. Closing remarks

  * **Termination.**  Discharged via `FairASTCertificate.sound`,
    which reduces to `partition_almostDiamond_fair` and then to the
    sublevel-finite-variant rule `pi_n_AST_fair`. The latter
    carries a Mathlib-filtration-plumbing gap that's not
    AVSS-specific (see `Liveness.lean §"Trajectory progress witness
    gap"`); the trajectory-deterministic specialisation
    `pi_n_AST_fair_with_progress_det` is closed and concrete protocols
    can use it directly with their own progress + monotonicity +
    strict-decrease witnesses (see `BrachaRBC.brbProb_totality_AS_fair`
    for the analogous shape).  Wiring AVSS-specific witnesses into
    that route is ~150 LOC of step-kernel plumbing, deferred per the
    M3 W5–W6 acceptance criteria.

  * **Correctness.** Closed sorry-free (`avss_correctness_AS` is
    axiom-clean). Note this verifies the *abstracted* output rule
    (`partyOutput` writes `coeffs 0 0` directly to every honest
    party); a real Canetti-Rabin formalization with per-party
    row-poly outputs reconstructed via Lagrange is future work.

  * **Output-determined / commitment.** Closed sorry-free for the
    abstracted form. The *full* commitment statement (with the
    disjunction "all honest outputs equal *or* dealer exposed")
    requires the Bracha-faithful refinement of this abstraction;
    we record the basic form here.

  * **Secrecy.** Closed sorry-free — passes through to
    `BivariateShamir.bivariate_shamir_secrecy`. -/

end Leslie.Examples.Prob.AVSSAbstract
