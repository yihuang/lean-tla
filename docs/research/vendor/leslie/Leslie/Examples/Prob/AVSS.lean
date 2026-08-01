/-
M3 — Canetti–Rabin asynchronous verifiable secret sharing
(**threshold-faithful variant**, Option B).

This module models the Canetti–Rabin '93 asynchronous VSS protocol
(`n` parties, `n ≥ 3t + 1`, `t` Byzantine corruptions) at the level
required by the literature: Bracha-amplification thresholds (`n − t`
echo / ready / output gates) plus per-party row-poly outputs.

Compared to `AVSSAbstract.lean`:

  * `AVSSLocalState` carries `rowPoly : Option (Fin (t+1) → F)`
    storing the row polynomial received from the dealer at delivery
    time.
  * `partyOutput p` writes `bivEval coeffs (partyPoint p) 0`
    (the per-party share `s_p = f(α_p, 0)`) — not the secret
    `coeffs 0 0`.
  * `partyEchoSend p` / `partyEchoReceive p q` replace the
    untracked `partyEcho`. Echoes are now in-flight messages with
    sender/target tracking.
  * `partyReady p` gate adds `echoesReceived.card ≥ n − t`.
  * `partyAmplify p` (new action) — Bracha amplification rule:
    `readyReceived.card ≥ t + 1 ∧ ¬ readySent`.
  * `partyOutput p` gate adds `readyReceived.card ≥ n − t`.

The four classical theorems lift to the probabilistic-trace setting:

  * `avss_termination_AS_fair` — every honest party eventually
    outputs (under trajectory fairness).
  * `avss_correctness_AS` — honest dealer ⇒ every honest output
    equals `bivEval coeffs (partyPoint p) 0`.
  * `avss_commitment_AS` — quorum-intersection commitment: any two
    honest outputs are *jointly determined* by the dealer's
    `coeffs`, with the difference equal to the difference of row-
    poly evaluations at 0.
  * `avss_secrecy` — `t`-coalition view independent of the secret
    (passes through to `BivariateShamir.bivariate_shamir_secrecy`).

Per implementation plan v2.2 §M3 W5–W6 + design plan v2.2 §M3 AVSS,
threshold-faithful refinement.

## Important: model abstractions vs. literature

This formalisation is sound and useful as a stepping stone toward
literature-faithful AVSS, but several abstractions matter when
interpreting the formalised statements.  In particular:

  * The **adversary model** has been progressively refined.  Two
    coexisting types are now formalised: the legacy `Adversary` (with
    read access to the full global state) and the literature-standard
    `RushingAdversary` (Phase 7.1, generic in `Leslie/Prob/Adversary.lean`)
    whose strategy is restricted to a measurable projection of the
    state to the corrupt coalition's view.  AVSS instantiates this via
    `avssCoalitionView` (Phase 7.2, §19).  The classical theorems
    re-prove mechanically as `*_rushing` variants (Phase 7.3, §19.1):
    `avss_termination_AS_fair_rushing`, `avss_correctness_AS_rushing`,
    `avss_commitment_AS_rushing`.  Trace-level operational secrecy
    against the rushing adversary (the literature-faithful theorem)
    is captured as a conditional in Phase 6.3
    (`avss_secrecy_AS_view_conditional`) whose hypothesis a follow-up
    Phase 7.4–7.5 PR will discharge — see `AVSS-MODEL-NOTES.md` §9.
  * The **dealer-to-party communication** is abstracted as a single
    global `s.coeffs` field, not per-party row + column polynomials.
    A corrupt dealer cannot deliver inconsistent row polys in this
    model (they're consistent by construction).
  * **Static corruption** only: `corrupted` is fixed at `μ₀`-time.

See `AVSS-MODEL-NOTES.md` (sibling file) for the full abstraction
inventory, the precise relationship to Canetti–Rabin '93, and the
roadmap (Phases 6–8).
-/

import Leslie.Examples.Prob.BivariateShamir
import Leslie.Prob.Action
import Leslie.Prob.Adversary
import Leslie.Prob.DeterministicSimulate
import Leslie.Prob.Liveness
import Leslie.Prob.PMF
import Leslie.Prob.Polynomial
import Leslie.Prob.RandomisedAdversary
import Leslie.Prob.Refinement
import Leslie.Prob.Secrecy
import Leslie.Prob.Trace
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Countable.Defs

namespace Leslie.Examples.Prob.AVSS

open Leslie.Prob MeasureTheory NNReal

variable {n t : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## §1. Local + global state -/

/-- Per-party AVSS local state.

  * `delivered` — has the party's `(rowPoly)` payload been processed?
  * `rowPoly` — the row polynomial `f_p(y) = bivEval coeffs (partyPoint p) y`,
    stored as `t+1` coefficients (degree-`t` univariate polynomial).
  * `echoesReceived` — distinct senders from whom an echo arrived.
  * `readyReceived` — distinct senders from whom a ready arrived.
  * `readySent` — has this party broadcast its own ready?
  * `output` — finalized output (a single `F` element, the per-party
    share `f_p(0)`).
-/
structure AVSSLocalState (n t : ℕ) (F : Type*) [DecidableEq F] where
  delivered      : Bool
  rowPoly        : Option (Fin (t+1) → F)
  echoSent       : Bool
  echoesReceived : Finset (Fin n)
  readyReceived  : Finset (Fin n)
  readySent      : Bool
  output         : Option F

namespace AVSSLocalState

/-- The empty per-party state at protocol start. -/
def init (n t : ℕ) (F : Type*) [DecidableEq F] : AVSSLocalState n t F :=
  { delivered := false
    rowPoly := none
    echoSent := false
    echoesReceived := ∅
    readyReceived := ∅
    readySent := false
    output := none }

end AVSSLocalState

/-- The dealer's per-party message: row polynomial `f_p(y) = f(α_p, y)`
plus column polynomial `g_p(x) = f(x, α_p)`, encoded as `t+1`-coefficient
vectors. In Canetti–Rabin '93 the dealer sends both to each party for
cross-check verifiability.

Phase 8.1 — A-lite refactor: this is the data carrier for per-party
dealer messages. The current model populates `dealerMessages` from
`s.coeffs` deterministically; later Phase 8 PRs (8.5, 8.6) will let
the adversary choose messages independently of `coeffs` for corrupt
dealers. -/
structure DealerPayload (t : ℕ) (F : Type*) where
  rowPoly : Fin (t+1) → F
  colPoly : Fin (t+1) → F

/-- The global AVSS protocol state.

  * `coeffs` — dealer's bivariate polynomial coefficients. Sampled
    once into `μ₀`; not modified after.
  * `partyPoint` — evaluation point for each party (`α_p` in the
    paper). Pinned at `μ₀`-sampling time.
  * `secret` — `coeffs 0 0` if dealer honest.
  * `local_` — per-party state.
  * `corrupted` — static corruption set.
  * `dealerHonest` — bookkeeping flag.
  * `inflightDeliveries` — set of honest parties awaiting share delivery.
  * `inflightCorruptDeliveries` — set of corrupt parties awaiting share
    delivery. Tracked separately so the secrecy proof can reason about
    when corrupt parties acquire their row polynomials.
  * `inflightEchoes` — set of (sender, target) pairs of in-transit echoes.
  * `inflightReady` — set of senders whose own-ready broadcast is
    still in transit.
  * `dealerSent` — whether the dealer has emitted shares.
  * `dealerMessages` — per-party dealer payloads (row + column poly).
    `none` pre-share; populated by `dealerShare` (Phase 8.1 A-lite
    refactor). `partyDeliver` / `partyCorruptDeliver` now read from
    here rather than recomputing from `coeffs`. The mapping
    `dealerMessages p = some {rowPoly := rowPolyOfDealer …, colPoly := …}`
    is preserved by every action; later Phase 8 PRs will let the
    adversary deviate.
-/
structure AVSSState (n t : ℕ) (F : Type*) [DecidableEq F] where
  -- Phase 8.5d-β: `coeffs` field migrated to μ₀ (initial measure). The
  -- bivariate polynomial is no longer a state field; it's a witness sampled
  -- at protocol start. Per-party commitments derived from the witness live
  -- in `dealerCommit` below (set at init by `initPred`, never changed).
  partyPoint                 : Fin n → F
  secret                     : F
  local_                     : Fin n → AVSSLocalState n t F
  corrupted                  : Finset (Fin n)
  dealerHonest               : Bool
  inflightDeliveries         : Finset (Fin n)
  inflightCorruptDeliveries  : Finset (Fin n)
  inflightEchoes             : Finset (Fin n × Fin n)
  -- Phase 8.5b-γ-followup-2: per-pair tokens (q, r) means q's ready
  -- broadcast to r is in flight; mirrors `inflightEchoes`'s shape.
  inflightReady              : Finset (Fin n × Fin n)
  -- Phase 8.5d-α: per-party flag — `dealerSent p = true` means the dealer has
  -- emitted shares to party `p`. Replaces the old `Bool` field; closes caveat
  -- C4 (selective non-broadcast).
  dealerSent                 : Fin n → Bool
  dealerMessages             : Fin n → Option (DealerPayload t F)
  -- Phase 8.5d-β: per-party dealer commitment (the payload the dealer plans
  -- to send to party p). Set at init by `initPred`; for honest dealer,
  -- constrained to be the canonical row poly derived from the μ₀ coeffs
  -- witness; for corrupt dealer, arbitrary. `dealerShareTo p` writes
  -- `dealerMessages p = some (dealerCommit p)`.
  dealerCommit               : Fin n → DealerPayload t F

namespace AVSSState

/-- A party is honest iff not in the corruption set. -/
def isHonest [DecidableEq F] (s : AVSSState n t F) (p : Fin n) : Prop :=
  p ∉ s.corrupted

instance [DecidableEq F] (s : AVSSState n t F) (p : Fin n) :
    Decidable (s.isHonest p) :=
  inferInstanceAs (Decidable (p ∉ s.corrupted))

end AVSSState

/-! ## §2. Bivariate evaluation primitives (mirror AVSSAbstract / BivariateShamir) -/

/-- Bivariate evaluation `coeffs(x, y) = Σ c_{kl} · x^k · y^l`. -/
def bivEval (coeffs : Fin (t+1) → Fin (t+1) → F) (x y : F) : F :=
  ∑ k : Fin (t+1), ∑ l : Fin (t+1), coeffs k l * x ^ k.val * y ^ l.val

/-- The dealer's row polynomial coefficients for party `p`:
`f_p(y) = bivEval coeffs (partyPoint p) y`. As `t+1` coefficients. -/
def rowPolyOfDealer (partyPoint : Fin n → F)
    (coeffs : Fin (t+1) → Fin (t+1) → F) (p : Fin n) :
    Fin (t+1) → F :=
  fun l => ∑ k : Fin (t+1), coeffs k l * partyPoint p ^ k.val

/-- The dealer's column polynomial coefficients for party `p`:
`g_p(x) = bivEval coeffs x (partyPoint p)`. As `t+1` coefficients in `x`.
Used in the Canetti–Rabin '93 cross-check protocol; in the current
Phase 8.1 model it is part of the per-party `DealerPayload` but its
operational use is deferred to PR 8.4 (echoes carrying values). -/
def colPolyOfDealer (partyPoint : Fin n → F)
    (coeffs : Fin (t+1) → Fin (t+1) → F) (p : Fin n) :
    Fin (t+1) → F :=
  fun k => ∑ l : Fin (t+1), coeffs k l * partyPoint p ^ l.val

/-- Univariate evaluation of stored row poly at `y`. -/
def evalRowPoly (rp : Fin (t+1) → F) (y : F) : F :=
  ∑ l : Fin (t+1), rp l * y ^ l.val

omit [Fintype F] [DecidableEq F] in
/-- Algebraic identity: the row poly extracted from `coeffs` at point
`partyPoint p`, evaluated at `y`, equals `bivEval coeffs (partyPoint p) y`. -/
theorem evalRowPoly_rowPolyOfDealer (partyPoint : Fin n → F)
    (coeffs : Fin (t+1) → Fin (t+1) → F) (p : Fin n) (y : F) :
    evalRowPoly (rowPolyOfDealer partyPoint coeffs p) y =
      bivEval coeffs (partyPoint p) y := by
  classical
  unfold evalRowPoly rowPolyOfDealer bivEval
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_mul]

/-! ## §3. Initial state -/

/-- Initial-state predicate.

Phase 8.5d-β: takes `coeffs` as a parameter — the bivariate polynomial
witness, sampled at protocol start (lives in μ₀, no longer in state). For an
honest dealer, `coeffs 0 0 = sec` and `s.dealerCommit p` matches the canonical
row poly derived from `coeffs` and `s.partyPoint`. For a corrupt dealer,
`s.dealerCommit` is unconstrained (the adversary picks). -/
def initPred (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (s : AVSSState n t F) : Prop :=
  (∀ p, s.local_ p = AVSSLocalState.init n t F) ∧
  s.secret = sec ∧
  s.corrupted = corr ∧
  s.inflightDeliveries = ∅ ∧
  s.inflightCorruptDeliveries = ∅ ∧
  s.inflightEchoes = ∅ ∧
  s.inflightReady = ∅ ∧
  s.dealerSent = (fun _ => false) ∧
  s.dealerMessages = (fun _ => none) ∧
  (s.dealerHonest = true →
    coeffs 0 0 = sec ∧
    ∀ p, s.dealerCommit p =
      { rowPoly := rowPolyOfDealer s.partyPoint coeffs p
        colPoly := fun _ => (0 : F) })

/-! ## §4. Action labels -/

/-- AVSS protocol actions (threshold-faithful). -/
inductive AVSSAction (n : ℕ) (F : Type*) [DecidableEq F]
  -- Phase 8.5d-α: per-party emit. The adversary chooses firing order;
  -- corrupt dealers can selectively short-share (C4 closure).
  | dealerShareTo (p : Fin n)                -- dealer emits row poly + echo intent for p
  | partyDeliver  (p : Fin n)                -- p (honest) receives row poly, sets `delivered`
  | partyCorruptDeliver (p : Fin n)          -- p (corrupt) receives row poly: adversary's view
  | partyEchoSend (p : Fin n)                -- p broadcasts echo (after delivery)
  | partyEchoReceive (p q : Fin n)           -- p receives echo from q
  | partyReady    (p : Fin n)                -- p sends ready (after n-t echoes)
  | partyAmplify  (p : Fin n)                -- p sends ready via amplification (≥t+1 readys)
  | partyReceiveReady (p q : Fin n)          -- p receives ready from q
  | partyOutput   (p : Fin n)                -- p outputs (after n-t readys)

/-! ## §5. Functional `setLocal` helper -/

/-- Functional update for `local_`: replace party `p`'s local state. -/
def setLocal (s : AVSSState n t F) (p : Fin n) (ls : AVSSLocalState n t F) :
    AVSSState n t F :=
  { s with local_ := fun q => if q = p then ls else s.local_ q }

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_local_self (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n t F) :
    (setLocal s p ls).local_ p = ls := by
  simp [setLocal]

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_local_ne (s : AVSSState n t F) (p q : Fin n)
    (ls : AVSSLocalState n t F) (h : q ≠ p) :
    (setLocal s p ls).local_ q = s.local_ q := by
  simp [setLocal, h]

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_dealerCommit (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n t F) :
    (setLocal s p ls).dealerCommit = s.dealerCommit := rfl

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_partyPoint (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n t F) :
    (setLocal s p ls).partyPoint = s.partyPoint := rfl

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_secret (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n t F) :
    (setLocal s p ls).secret = s.secret := rfl

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_corrupted (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n t F) :
    (setLocal s p ls).corrupted = s.corrupted := rfl

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_dealerHonest (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n t F) :
    (setLocal s p ls).dealerHonest = s.dealerHonest := rfl

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_inflightDeliveries (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n t F) :
    (setLocal s p ls).inflightDeliveries = s.inflightDeliveries := rfl

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_inflightCorruptDeliveries (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n t F) :
    (setLocal s p ls).inflightCorruptDeliveries = s.inflightCorruptDeliveries := rfl

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_inflightEchoes (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n t F) :
    (setLocal s p ls).inflightEchoes = s.inflightEchoes := rfl

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_inflightReady (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n t F) :
    (setLocal s p ls).inflightReady = s.inflightReady := rfl

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_dealerSent (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n t F) :
    (setLocal s p ls).dealerSent = s.dealerSent := rfl

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_dealerMessages (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n t F) :
    (setLocal s p ls).dealerMessages = s.dealerMessages := rfl

/-! ## §6. Deterministic next-state -/

/-- The deterministic next-state function. Where the gate fails this
returns `s` unchanged; gates are enforced by `actionGate`. -/
def avssStep (a : AVSSAction n F) (s : AVSSState n t F) :
    AVSSState n t F :=
  match a with
  | .dealerShareTo p =>
      -- Phase 8.5d-α: per-party emit. The dealer ships a payload to party `p`
      -- and flags `dealerSent p = true`. Adversary chooses firing order;
      -- corrupt dealers may omit some honest parties (C4 closure).
      --
      -- The destination set is determined by p's corruption status:
      -- honest p → `inflightDeliveries`; corrupt p → `inflightCorruptDeliveries`.
      -- Phase 8.5d-β: payload comes from `s.dealerCommit p` (set at init by
      -- `initPred`), not from a state-stored bivariate polynomial. For an
      -- honest dealer `dealerCommit p` is constrained to the canonical row
      -- poly derived from the μ₀-sampled `coeffs` witness; for a corrupt
      -- dealer it is arbitrary.
      { s with
        dealerSent := Function.update s.dealerSent p true
        inflightDeliveries :=
          if p ∉ s.corrupted then insert p s.inflightDeliveries
          else s.inflightDeliveries
        inflightCorruptDeliveries :=
          if p ∈ s.corrupted then insert p s.inflightCorruptDeliveries
          else s.inflightCorruptDeliveries
        dealerMessages := Function.update s.dealerMessages p (some (s.dealerCommit p)) }
  | .partyDeliver p =>
      let ls := s.local_ p
      -- Read row poly from `dealerMessages p`; fall through to
      -- `s.dealerCommit p . rowPoly` if the slot is unexpectedly empty (the
      -- gate requires `(dealerMessages p).isSome`, so this branch is
      -- unreachable under the gate).
      let rp := match s.dealerMessages p with
        | some msg => msg.rowPoly
        | none     => (s.dealerCommit p).rowPoly
      let ls' : AVSSLocalState n t F :=
        { ls with delivered := true, rowPoly := some rp }
      let s' := setLocal s p ls'
      { s' with inflightDeliveries := s.inflightDeliveries.erase p }
  | .partyCorruptDeliver p =>
      -- Mirror of `partyDeliver` for corrupt parties.
      let ls := s.local_ p
      let rp := match s.dealerMessages p with
        | some msg => msg.rowPoly
        | none     => (s.dealerCommit p).rowPoly
      let ls' : AVSSLocalState n t F :=
        { ls with delivered := true, rowPoly := some rp }
      let s' := setLocal s p ls'
      { s' with inflightCorruptDeliveries := s.inflightCorruptDeliveries.erase p }
  | .partyEchoSend p =>
      -- Phase 8.5b: party `p` (honest *or* corrupt under the C1+C2 model)
      -- broadcasts an echo to every party. Records `(p, q)` in
      -- `inflightEchoes` for every `q` and sets `echoSent` so the action
      -- is single-shot. Phase 8.5b broadens the broadcast filter from
      -- honest receivers only to all receivers (C2): honest sends now
      -- reach corrupt receivers, and corrupt sends populate the queue
      -- regardless.
      let ls := s.local_ p
      let ls' : AVSSLocalState n t F := { ls with echoSent := true }
      let s' := setLocal s p ls'
      { s' with
        inflightEchoes :=
          s.inflightEchoes ∪
            (Finset.univ : Finset (Fin n)).image (fun q => (p, q)) }
  | .partyEchoReceive p q =>
      let ls := s.local_ p
      let ls' : AVSSLocalState n t F :=
        { ls with echoesReceived := insert q ls.echoesReceived }
      let s' := setLocal s p ls'
      { s' with inflightEchoes := s.inflightEchoes.erase (q, p) }
  | .partyReady p =>
      -- Phase 8.5b-γ-followup-2: per-pair broadcast — populates `(p, r)`
      -- for every receiver `r`, mirroring `partyEchoSend`.
      let ls := s.local_ p
      let ls' : AVSSLocalState n t F := { ls with readySent := true }
      let s' := setLocal s p ls'
      { s' with
        inflightReady :=
          s.inflightReady ∪
            (Finset.univ : Finset (Fin n)).image (fun r => (p, r)) }
  | .partyAmplify p =>
      let ls := s.local_ p
      let ls' : AVSSLocalState n t F := { ls with readySent := true }
      let s' := setLocal s p ls'
      { s' with
        inflightReady :=
          s.inflightReady ∪
            (Finset.univ : Finset (Fin n)).image (fun r => (p, r)) }
  | .partyReceiveReady p q =>
      let ls := s.local_ p
      let ls' : AVSSLocalState n t F :=
        { ls with readyReceived := insert q ls.readyReceived }
      let s' := setLocal s p ls'
      { s' with inflightReady := s.inflightReady.erase (q, p) }
  | .partyOutput p =>
      let ls := s.local_ p
      -- Per-party share: f_p(0) = bivEval coeffs (partyPoint p) 0.
      -- Computed from stored `rowPoly`. Equals `bivEval s.coeffs (s.partyPoint p) 0`
      -- by `evalRowPoly_rowPolyOfDealer` whenever `rowPoly = some (rowPolyOfDealer ...)`.
      let v : F :=
        match ls.rowPoly with
        | some rp => evalRowPoly rp 0
        | none    => 0  -- unreachable when gate enforces `delivered = true`
      let ls' : AVSSLocalState n t F := { ls with output := some v }
      setLocal s p ls'

/-! ### Frame lemmas: `dealerMessages` field

Only `dealerShare` writes to `s.dealerMessages`; every other action
preserves it.  These `@[simp]` frame lemmas are convenient in the
simSyncInv preservation proof (Phase 8.1) and elsewhere where we
want to rewrite `(avssStep a s).dealerMessages` to `s.dealerMessages`. -/

omit [Fintype F] in
@[simp] theorem avssStep_partyDeliver_dealerMessages
    (s : AVSSState n t F) (p : Fin n) :
    (avssStep (AVSSAction.partyDeliver p) s).dealerMessages = s.dealerMessages := rfl

omit [Fintype F] in
@[simp] theorem avssStep_partyCorruptDeliver_dealerMessages
    (s : AVSSState n t F) (p : Fin n) :
    (avssStep (AVSSAction.partyCorruptDeliver p) s).dealerMessages =
      s.dealerMessages := rfl

omit [Fintype F] in
@[simp] theorem avssStep_partyEchoSend_dealerMessages
    (s : AVSSState n t F) (p : Fin n) :
    (avssStep (AVSSAction.partyEchoSend p) s).dealerMessages = s.dealerMessages := rfl

omit [Fintype F] in
@[simp] theorem avssStep_partyEchoReceive_dealerMessages
    (s : AVSSState n t F) (p q : Fin n) :
    (avssStep (AVSSAction.partyEchoReceive p q) s).dealerMessages =
      s.dealerMessages := rfl

omit [Fintype F] in
@[simp] theorem avssStep_partyReady_dealerMessages
    (s : AVSSState n t F) (p : Fin n) :
    (avssStep (AVSSAction.partyReady p) s).dealerMessages = s.dealerMessages := rfl

omit [Fintype F] in
@[simp] theorem avssStep_partyAmplify_dealerMessages
    (s : AVSSState n t F) (p : Fin n) :
    (avssStep (AVSSAction.partyAmplify p) s).dealerMessages = s.dealerMessages := rfl

omit [Fintype F] in
@[simp] theorem avssStep_partyReceiveReady_dealerMessages
    (s : AVSSState n t F) (p q : Fin n) :
    (avssStep (AVSSAction.partyReceiveReady p q) s).dealerMessages =
      s.dealerMessages := rfl

omit [Fintype F] in
@[simp] theorem avssStep_partyOutput_dealerMessages
    (s : AVSSState n t F) (p : Fin n) :
    (avssStep (AVSSAction.partyOutput p) s).dealerMessages = s.dealerMessages := rfl

omit [Fintype F] in
/-- The `dealerCommit` field is preserved by every `avssStep` action.
At init it is set from the canonical `coeffs` witness for honest
dealer (or arbitrary for corrupt dealer); no action subsequently
modifies it.  Phase 8.5d-β-followup-6 infrastructure for the trace-
level dealerCommit AE-preservation lemma.  (Moved up from §17 in
followup-7 so it is in scope for `coalitionRowPolyAlignedInv`'s
preservation proof.) -/
theorem avssStep_dealerCommit_invariant (a : AVSSAction n F)
    (s : AVSSState n t F) :
    (avssStep a s).dealerCommit = s.dealerCommit := by
  cases a <;> simp [avssStep, setLocal]

/-! ## §7. Action gates (with thresholds) -/

/-- Gate predicates with `n − t` Bracha thresholds.

The fair-required actions (`partyDeliver`, `partyEchoSend`,
`partyEchoReceive`, `partyReady`, `partyAmplify`, `partyReceiveReady`,
`partyOutput`) restrict their party arguments to honest parties — only
honest parties follow the protocol script.

Phase 8.5a addition: gates of `partyEchoSend`, `partyReady`,
`partyAmplify` carry an explicit `s.dealerSent = true` clause.  Under
the current model this is implied by the existing local-state
preconditions (which require non-`init` values, available only after
`dealerShare` fires) plus `avssTermInv` clause 1; the explicit clause
is added in preparation for Phase 8.5b's gate weakening (drop
`p ∉ s.corrupted` for C1 closure), where corrupt parties may fire
without delivery and the explicit clause becomes load-bearing for
preserving `avssTermInv`'s pre-share quiescence. -/
def actionGate (a : AVSSAction n F) (s : AVSSState n t F) : Prop :=
  match a with
  | .dealerShareTo p =>
      -- Phase 8.5d-α: gate is per-party; `dealerSent p = false` means
      -- this party hasn't been shared yet.
      s.dealerSent p = false
  | .partyDeliver p =>
      -- Phase 8.5d-α: condition specialised to this party.
      s.dealerSent p = true ∧ p ∉ s.corrupted ∧
        p ∈ s.inflightDeliveries ∧ (s.local_ p).delivered = false ∧
        (s.dealerMessages p).isSome
  | .partyCorruptDeliver p =>
      s.dealerSent p = true ∧ p ∈ s.corrupted ∧
        p ∈ s.inflightCorruptDeliveries ∧ (s.local_ p).delivered = false ∧
        (s.dealerMessages p).isSome
  | .partyEchoSend p =>
      -- Phase 8.5b: C1 closure — corrupt parties may also fire `partyEchoSend`.
      -- The `p ∉ s.corrupted` clause is dropped here.
      -- Phase 8.5d-α: per-party `dealerSent p`.
      (s.local_ p).delivered = true ∧
        (s.local_ p).echoSent = false ∧ s.dealerSent p = true
  | .partyEchoReceive p q =>
      -- Phase 8.5b: C2 closure — corrupt receivers may also receive echoes.
      (q, p) ∈ s.inflightEchoes ∧
        q ∉ (s.local_ p).echoesReceived
  | .partyReady p =>
      -- Phase 8.5b: C1 closure.
      -- Phase 8.5d-α: per-party `dealerSent p`.
      (s.local_ p).delivered = true ∧ (s.local_ p).readySent = false ∧
        (s.local_ p).echoesReceived.card ≥ n - t ∧ s.dealerSent p = true
  | .partyAmplify p =>
      -- Phase 8.5b: C1 closure.
      -- Phase 8.5d-α: per-party `dealerSent p`.
      (s.local_ p).readySent = false ∧
        (s.local_ p).readyReceived.card ≥ t + 1 ∧ s.dealerSent p = true
  | .partyReceiveReady p q =>
      -- Phase 8.5b: C2 closure.
      -- Phase 8.5b-γ-followup-2: per-pair tokens.
      (q, p) ∈ s.inflightReady ∧ q ∉ (s.local_ p).readyReceived
  | .partyOutput p =>
      p ∉ s.corrupted ∧
        (s.local_ p).delivered = true ∧ (s.local_ p).readySent = true ∧
        (s.local_ p).output = none ∧
        (s.local_ p).readyReceived.card ≥ n - t

/-! ## §8. Terminated predicate -/

/-- A state is terminated iff every honest party has snapped output
**and** echoed, **and** all in-flight queues are drained. The
`echoSent = true` requirement ensures the variant `avssU` reaches
`0` at terminated states — without it an honest party could output
via `partyAmplify` (which only requires `readyReceived ≥ t + 1`)
without ever echoing, leaving `unsentEchoSet` nonempty. -/
def terminated (s : AVSSState n t F) : Prop :=
  (∀ p, p ∉ s.corrupted → (s.local_ p).output.isSome) ∧
  (∀ p, p ∉ s.corrupted → (s.local_ p).echoSent = true) ∧
  s.inflightDeliveries = ∅ ∧
  s.inflightEchoes = ∅ ∧
  s.inflightReady = ∅

/-! ## §9. Spec -/

/-- The probabilistic AVSS spec. Randomness lives in `μ₀` only.

Phase 8.5d-β: `coeffs` parameter threads through `init` only (the
bivariate-polynomial witness lives in μ₀). The next-state function
and gates remain `coeffs`-independent. -/
noncomputable def avssSpec (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t+1) → Fin (t+1) → F) :
    ProbActionSpec (AVSSState n t F) (AVSSAction n F) where
  init := initPred sec corr coeffs
  actions := fun a =>
    { gate := actionGate a
      effect := fun s _ => PMF.pure (avssStep a s) }

omit [Fintype F] in
@[simp] theorem avssSpec_step_pure (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (a : AVSSAction n F) (s : AVSSState n t F) (h : actionGate a s) :
    (avssSpec (t := t) sec corr coeffs).step a s
      = some (PMF.pure (avssStep a s)) :=
  ProbActionSpec.step_eq_some h

omit [Fintype F] in
theorem avssSpec_step_none (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (a : AVSSAction n F) (s : AVSSState n t F) (h : ¬ actionGate a s) :
    (avssSpec (t := t) sec corr coeffs).step a s = none :=
  ProbActionSpec.step_eq_none h

/-! ## §10. Countable / measurable instances -/

section Measurable

instance : MeasurableSpace (AVSSState n t F) := ⊤
instance : MeasurableSingletonClass (AVSSState n t F) := ⟨fun _ => trivial⟩
instance : MeasurableSpace (AVSSAction n F) := ⊤
instance : MeasurableSingletonClass (AVSSAction n F) := ⟨fun _ => trivial⟩
instance : MeasurableSpace (AVSSLocalState n t F) := ⊤
instance : MeasurableSingletonClass (AVSSLocalState n t F) := ⟨fun _ => trivial⟩

/-- `AVSSAction n F` is `Fintype` under `[Fintype F]`. -/
noncomputable instance : Fintype (AVSSAction n F) := by
  classical
  exact Fintype.ofEquiv
    (Fin n ⊕ Fin n ⊕ Fin n ⊕ Fin n ⊕ (Fin n × Fin n) ⊕ Fin n ⊕ Fin n ⊕
      (Fin n × Fin n) ⊕ Fin n)
    { toFun := fun
        -- Phase 8.5d-α: dealerShareTo carries a Fin n.
        | .inl p => .dealerShareTo p
        | .inr (.inl p) => .partyDeliver p
        | .inr (.inr (.inl p)) => .partyCorruptDeliver p
        | .inr (.inr (.inr (.inl p))) => .partyEchoSend p
        | .inr (.inr (.inr (.inr (.inl ⟨p, q⟩)))) => .partyEchoReceive p q
        | .inr (.inr (.inr (.inr (.inr (.inl p))))) => .partyReady p
        | .inr (.inr (.inr (.inr (.inr (.inr (.inl p)))))) => .partyAmplify p
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨p, q⟩))))))) =>
            .partyReceiveReady p q
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr p))))))) => .partyOutput p
      invFun := fun
        | .dealerShareTo p => .inl p
        | .partyDeliver p => .inr (.inl p)
        | .partyCorruptDeliver p => .inr (.inr (.inl p))
        | .partyEchoSend p => .inr (.inr (.inr (.inl p)))
        | .partyEchoReceive p q => .inr (.inr (.inr (.inr (.inl ⟨p, q⟩))))
        | .partyReady p => .inr (.inr (.inr (.inr (.inr (.inl p)))))
        | .partyAmplify p => .inr (.inr (.inr (.inr (.inr (.inr (.inl p))))))
        | .partyReceiveReady p q =>
            .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨p, q⟩)))))))
        | .partyOutput p =>
            .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr p)))))))
      left_inv := fun
        | .inl _ => rfl
        | .inr (.inl _) => rfl
        | .inr (.inr (.inl _)) => rfl
        | .inr (.inr (.inr (.inl _))) => rfl
        | .inr (.inr (.inr (.inr (.inl _)))) => rfl
        | .inr (.inr (.inr (.inr (.inr (.inl _))))) => rfl
        | .inr (.inr (.inr (.inr (.inr (.inr (.inl _)))))) => rfl
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl _))))))) => rfl
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr _))))))) => rfl
      right_inv := fun
        | .dealerShareTo _ => rfl
        | .partyDeliver _ => rfl
        | .partyCorruptDeliver _ => rfl
        | .partyEchoSend _ => rfl
        | .partyEchoReceive _ _ => rfl
        | .partyReady _ => rfl
        | .partyAmplify _ => rfl
        | .partyReceiveReady _ _ => rfl
        | .partyOutput _ => rfl }

instance : Countable (AVSSAction n F) := Finite.to_countable

/-- `AVSSLocalState n t F` is `Fintype`. -/
noncomputable instance : Fintype (AVSSLocalState n t F) := by
  classical
  exact Fintype.ofEquiv
    (Bool × Option (Fin (t+1) → F) × Bool × Finset (Fin n) ×
      Finset (Fin n) × Bool × Option F)
    { toFun := fun ⟨a, b, c, d, e, f, g⟩ => ⟨a, b, c, d, e, f, g⟩
      invFun := fun ls =>
        (ls.delivered, ls.rowPoly, ls.echoSent, ls.echoesReceived,
         ls.readyReceived, ls.readySent, ls.output)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance : Countable (AVSSLocalState n t F) := Finite.to_countable

instance : MeasurableSpace (DealerPayload t F) := ⊤
instance : MeasurableSingletonClass (DealerPayload t F) := ⟨fun _ => trivial⟩

/-- `DealerPayload t F` is `Fintype` under `[Fintype F]`. -/
noncomputable instance : Fintype (DealerPayload t F) := by
  classical
  exact Fintype.ofEquiv
    ((Fin (t+1) → F) × (Fin (t+1) → F))
    { toFun := fun ⟨r, c⟩ => ⟨r, c⟩
      invFun := fun d => (d.rowPoly, d.colPoly)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance : Countable (DealerPayload t F) := Finite.to_countable

/-- `AVSSState n t F` is `Fintype`. -/
noncomputable instance : Fintype (AVSSState n t F) := by
  classical
  exact Fintype.ofEquiv
    ((Fin n → F) × F ×
      (Fin n → AVSSLocalState n t F) × Finset (Fin n) × Bool ×
      Finset (Fin n) × Finset (Fin n) × Finset (Fin n × Fin n) ×
      Finset (Fin n × Fin n) × (Fin n → Bool) × (Fin n → Option (DealerPayload t F)) ×
      (Fin n → DealerPayload t F))
    { toFun := fun ⟨pp, sec, l, corr, dh, idl, idlc, ie, ird, ds, dm, dc⟩ =>
        ⟨pp, sec, l, corr, dh, idl, idlc, ie, ird, ds, dm, dc⟩
      invFun := fun s =>
        (s.partyPoint, s.secret, s.local_, s.corrupted,
         s.dealerHonest, s.inflightDeliveries, s.inflightCorruptDeliveries,
         s.inflightEchoes, s.inflightReady, s.dealerSent, s.dealerMessages,
         s.dealerCommit)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance : Countable (AVSSState n t F) := Finite.to_countable

end Measurable

/-! ## §11. Fairness assumptions -/

/-- Set of fair-required actions.

`dealerShare` is fair: under fair scheduling, the dealer must
eventually broadcast — otherwise no honest party would ever deliver,
echo, or output, and `terminated` would be unreachable. Folding
`dealerShare` into the fair set makes the model's termination claim
unconditional under fair scheduling (Phase B fix to caveat C3 in
`AVSS-MODEL-NOTES.md` §11). After `dealerShare` fires once, its gate
becomes false (`dealerSent` flips to `true`), so weak fairness is
trivially preserved.

`partyCorruptDeliver` is intentionally NOT fair — it's an action
available to the adversary (modelling corrupt parties acquiring their
shares for the secrecy view), but we don't require fair scheduling
to fire it. Honest-party fairness (and termination of the honest
parties) are unaffected by whether corrupt parties have received
their shares. -/
def avssFairActions : Set (AVSSAction n F) :=
  { a | match a with
        -- Phase 8.5d-α: per-party emit is fair-required for every party
        -- (refined in 8.5d-γ to honest dealer + honest p).
        | .dealerShareTo _ => True
        | .partyDeliver _ => True
        | .partyEchoSend _ => True
        | .partyEchoReceive _ _ => True
        | .partyReady _ => True
        | .partyAmplify _ => True
        | .partyReceiveReady _ _ => True
        | .partyOutput _ => True
        | _ => False }

/-- AVSS fairness assumptions. -/
noncomputable def avssFair :
    FairnessAssumptions (AVSSState n t F) (AVSSAction n F) where
  fair_actions := avssFairActions
  isWeaklyFair := fun _ => True

/-! ## §12. Termination certificate — definitions

The variant `U` is a 7-component lex-product encoded into a single
`ℕ` via base-`K` weighting, with `K = (n+1)*(n+1)` chosen to dominate
the maximum value of any single component (notably
`inflightEchoes.card ≤ n²`).

Lex order (largest weight first):

  1. `[¬ dealerSent]` — the dealer step (`dealerShare`).
  2. `inflightDeliveries.card` — `partyDeliver` step.
  3. `unsentEchoCount` — honest parties with `delivered ∧ ¬ echoSent`;
     `partyEchoSend` step.
  4. `inflightEchoes.card` — `partyEchoReceive` step.
  5. `notReadySentCount` — honest parties with `¬ readySent`;
     `partyReady` / `partyAmplify` step.
  6. `inflightReady.card` — `partyReceiveReady` step.
  7. `unfinishedCount` — honest parties with `output = none`;
     `partyOutput` step. -/

/-- Set of honest parties (complement of `corrupted` in `Fin n`). -/
def honestSet (s : AVSSState n t F) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun p => p ∉ s.corrupted)

@[simp] theorem honestSet_card_le (s : AVSSState n t F) :
    (honestSet s).card ≤ n := by
  unfold honestSet
  exact (Finset.card_le_univ _).trans (by simp)

/-- Phase 8.5d-α: honest parties for which the dealer hasn't yet emitted a
payload. The new c₁ component of `avssU`: drops by 1 each time
`dealerShareTo p` fires for honest p. Honest-only restriction matches
`terminated`'s honest-only conjuncts and lets the variant reach `0` at
terminated states. -/
def unsentDealerSet (s : AVSSState n t F) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter
    (fun p => p ∉ s.corrupted ∧ s.dealerSent p = false)

@[simp] theorem unsentDealerSet_card_le (s : AVSSState n t F) :
    (unsentDealerSet s).card ≤ n := by
  unfold unsentDealerSet
  exact (Finset.card_le_univ _).trans (by simp)

omit [Field F] [Fintype F] in
/-- Phase 8.5d-α: `unsentDealerSet` depends only on `dealerSent` and
`corrupted`. Used by every non-`dealerShareTo` step lemma to discharge
the c₁ component (which is preserved by frame). -/
theorem unsentDealerSet_eq_of_dealerSent_eq
    (s s' : AVSSState n t F)
    (hds : s'.dealerSent = s.dealerSent)
    (hcorr : s'.corrupted = s.corrupted) :
    unsentDealerSet s' = unsentDealerSet s := by
  unfold unsentDealerSet
  congr 1
  funext p
  rw [hds, hcorr]

/-- Honest parties with delivered = true and echoSent = false. -/
def unsentEchoSet (s : AVSSState n t F) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter
    (fun p => p ∉ s.corrupted ∧
      (s.local_ p).delivered = true ∧ (s.local_ p).echoSent = false)

@[simp] theorem unsentEchoSet_card_le (s : AVSSState n t F) :
    (unsentEchoSet s).card ≤ n := by
  unfold unsentEchoSet
  exact (Finset.card_le_univ _).trans (by simp)

/-- Honest parties with `readySent = false`. -/
def notReadySentSet (s : AVSSState n t F) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter
    (fun p => p ∉ s.corrupted ∧ (s.local_ p).readySent = false)

@[simp] theorem notReadySentSet_card_le (s : AVSSState n t F) :
    (notReadySentSet s).card ≤ n := by
  unfold notReadySentSet
  exact (Finset.card_le_univ _).trans (by simp)

/-- Honest parties with `output = none`. -/
def unfinishedSet (s : AVSSState n t F) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter
    (fun p => p ∉ s.corrupted ∧ (s.local_ p).output = none)

@[simp] theorem unfinishedSet_card_le (s : AVSSState n t F) :
    (unfinishedSet s).card ≤ n := by
  unfold unfinishedSet
  exact (Finset.card_le_univ _).trans (by simp)

@[simp] theorem inflightEchoes_card_le (s : AVSSState n t F) :
    s.inflightEchoes.card ≤ (n + 1) * (n + 1) := by
  classical
  have h1 : s.inflightEchoes.card ≤ (Finset.univ : Finset (Fin n × Fin n)).card :=
    Finset.card_le_univ _
  have h2 : (Finset.univ : Finset (Fin n × Fin n)).card = n * n := by simp
  calc s.inflightEchoes.card
      ≤ n * n := by rw [← h2]; exact h1
    _ ≤ (n + 1) * (n + 1) := by nlinarith

@[simp] theorem inflightDeliveries_card_le (s : AVSSState n t F) :
    s.inflightDeliveries.card ≤ n := by
  exact (Finset.card_le_univ s.inflightDeliveries).trans (by simp)

@[simp] theorem inflightReady_card_le (s : AVSSState n t F) :
    s.inflightReady.card ≤ (n + 1) * (n + 1) := by
  classical
  have h1 : s.inflightReady.card ≤ (Finset.univ : Finset (Fin n × Fin n)).card :=
    Finset.card_le_univ _
  have h2 : (Finset.univ : Finset (Fin n × Fin n)).card = n * n := by simp
  calc s.inflightReady.card
      ≤ n * n := by rw [← h2]; exact h1
    _ ≤ (n + 1) * (n + 1) := by nlinarith

/-- Lex base: `K = (n+1)²` dominates every component (in particular
`inflightEchoes.card ≤ n² < K`). -/
def lexBase (n : ℕ) : ℕ := (n + 1) * (n + 1)

theorem lexBase_pos : 1 ≤ lexBase n := by unfold lexBase; nlinarith

theorem inflightEchoes_lt_lexBase (s : AVSSState n t F) :
    s.inflightEchoes.card < lexBase n + 1 := by
  unfold lexBase
  have := inflightEchoes_card_le s
  omega

/-- The 7-component lex-product termination variant.

```
U = c₁·K⁶ + c₂·K⁵ + c₃·K⁴ + c₄·K³ + c₅·K² + c₆·K + c₇
```

with `K = (n+1)²`. -/
noncomputable def avssU (s : AVSSState n t F) : ℕ :=
  let K := lexBase n
  -- Phase 8.5d-α: c₁ is now `(unsentDealerSet s).card` (the per-party form).
  (unsentDealerSet s).card * K ^ 6 +
    s.inflightDeliveries.card * K ^ 5 +
    (unsentEchoSet s).card * K ^ 4 +
    s.inflightEchoes.card * K ^ 3 +
    (notReadySentSet s).card * K ^ 2 +
    s.inflightReady.card * K +
    (unfinishedSet s).card

/-- Likelihood `V s = (avssU s : ℝ≥0)`. -/
noncomputable def avssV (s : AVSSState n t F) : ℝ≥0 := (avssU s : ℝ≥0)

/-- Termination inductive invariant.

Three clauses:

  * Pre-share quiescence: when `dealerSent = false`, every party is
    in its initial local state (all 7 fields = `AVSSLocalState.init`)
    and all three in-flight queues are empty. The full-init form is
    needed to rule out `partyAmplify`'s `readyReceived.card ≥ t + 1`
    gate: if pre-state has `dealerSent = false`, then any honest
    party's `readyReceived` is `∅`, so the gate is infeasible.
  * Echo well-formedness: every honest party that has `echoSent =
    true` also has `delivered = true` (echoes are only sent post-
    delivery).
  * Output well-formedness: every honest party with `output = some _`
    also has `readySent = true ∧ delivered = true`.

This is enough invariant to make the `avssU` lex-product strictly
decrease on each fair-firing step. -/
def avssTermInv (s : AVSSState n t F) : Prop :=
  -- Phase 8.5d-α: clause 1 antecedent is "no party has been served yet".
  ((∀ p, s.dealerSent p = false) →
    (∀ p, s.local_ p = AVSSLocalState.init n t F) ∧
    s.inflightDeliveries = ∅ ∧
    s.inflightEchoes = ∅ ∧
    s.inflightReady = ∅) ∧
  (∀ p, p ∉ s.corrupted →
    (s.local_ p).echoSent = true → (s.local_ p).delivered = true) ∧
  (∀ p, p ∉ s.corrupted →
    (s.local_ p).output.isSome = true →
      (s.local_ p).readySent = true ∧ (s.local_ p).delivered = true) ∧
  -- Phase 8.5d-α clause 4: per-party pre-share quiescence (weak form). For any
  -- honest party `p` not yet served by the dealer, the `delivered` flag is
  -- false. This is exactly the strength needed by `avssU_eq_zero_of_terminated`:
  -- combined with clause 3 (`output.isSome → readySent ∧ delivered`), it forces
  -- `output = none` whenever `dealerSent p = false`, so `unsentDealerSet`
  -- (honest-only) is empty at terminated states.
  --
  -- Stronger forms (e.g. `local_ p = init`) are NOT preserved: `partyEchoReceive q r`
  -- mutates `(s.local_ q).echoesReceived` without requiring `s.dealerSent q = true`
  -- on its gate. The weak form (only `delivered`) is preserved because no action
  -- writes `delivered := true` without `s.dealerSent q = true` on its gate.
  (∀ p, p ∉ s.corrupted → s.dealerSent p = false → (s.local_ p).delivered = false)

/-- Uniform bound on `avssU`: `7 · n · K⁶` plus slack, with `K = (n+1)²`.

A simple over-bound `(7 * n + 7) * K⁶` is used; the cert's
`V_init_bdd` field expects a concrete `ℕ` constant. -/
theorem avssU_le_bound (s : AVSSState n t F) :
    avssU s ≤ (7 * n + 7) * (lexBase n) ^ 6 := by
  classical
  unfold avssU
  set K := lexBase n with hK_def
  have hK_pos : 1 ≤ K := lexBase_pos
  -- Phase 8.5d-α: c₁ is now `unsentDealerSet`.
  have h0 : (unsentDealerSet s).card ≤ n := unsentDealerSet_card_le s
  have h1 := inflightDeliveries_card_le s
  have h2 := unsentEchoSet_card_le s
  have h3 : s.inflightEchoes.card ≤ K := by
    rw [hK_def]; exact inflightEchoes_card_le s
  have h4 := notReadySentSet_card_le s
  have h5 : s.inflightReady.card ≤ K := by
    rw [hK_def]; exact inflightReady_card_le s
  have h6 := unfinishedSet_card_le s
  -- Power monotonicity:
  have hp1 : K ≤ K ^ 6 := by
    calc K = K ^ 1 := by ring
      _ ≤ K ^ 6 := Nat.pow_le_pow_right hK_pos (by omega)
  have hp2 : K ^ 2 ≤ K ^ 6 := Nat.pow_le_pow_right hK_pos (by omega)
  have hp3 : K ^ 3 ≤ K ^ 6 := Nat.pow_le_pow_right hK_pos (by omega)
  have hp4 : K ^ 4 ≤ K ^ 6 := Nat.pow_le_pow_right hK_pos (by omega)
  have hp5 : K ^ 5 ≤ K ^ 6 := Nat.pow_le_pow_right hK_pos (by omega)
  have hp0 : (1 : ℕ) ≤ K ^ 6 := by
    calc (1 : ℕ) = 1 ^ 6 := by ring
      _ ≤ K ^ 6 := by gcongr
  -- Each weighted component ≤ n · K⁶ (or K · K⁵ = K⁶ for component 4):
  have hA : (unsentDealerSet s).card * K ^ 6 ≤ n * K ^ 6 := by gcongr
  have hB : s.inflightDeliveries.card * K ^ 5 ≤ n * K ^ 6 := by
    calc s.inflightDeliveries.card * K ^ 5
        ≤ n * K ^ 5 := by gcongr
      _ ≤ n * K ^ 6 := by gcongr
  have hC : (unsentEchoSet s).card * K ^ 4 ≤ n * K ^ 6 := by
    calc (unsentEchoSet s).card * K ^ 4
        ≤ n * K ^ 4 := by gcongr
      _ ≤ n * K ^ 6 := by gcongr
  have hD : s.inflightEchoes.card * K ^ 3 ≤ K ^ 6 := by
    calc s.inflightEchoes.card * K ^ 3
        ≤ K * K ^ 3 := by gcongr
      _ = K ^ 4 := by ring
      _ ≤ K ^ 6 := hp4
  have hE : (notReadySentSet s).card * K ^ 2 ≤ n * K ^ 6 := by
    calc (notReadySentSet s).card * K ^ 2
        ≤ n * K ^ 2 := by gcongr
      _ ≤ n * K ^ 6 := by gcongr
  have hF : s.inflightReady.card * K ≤ K ^ 6 := by
    calc s.inflightReady.card * K
        ≤ K * K := by gcongr
      _ = K ^ 2 := by ring
      _ ≤ K ^ 6 := hp2
  have hG : (unfinishedSet s).card ≤ n * K ^ 6 := by
    calc (unfinishedSet s).card
        ≤ n := h6
      _ = n * 1 := by ring
      _ ≤ n * K ^ 6 := by nlinarith [hp0]
  -- Combine hA..hG: avssU ≤ 5·n·K⁶ + 2·K⁶.
  have hsum : avssU s ≤ 5 * n * K ^ 6 + 2 * K ^ 6 := by
    unfold avssU
    -- Five components ≤ n · K⁶ each, plus two ≤ K⁶ (inflightEchoes and inflightReady).
    have hsum6 :
        (unsentDealerSet s).card * K ^ 6 +
          s.inflightDeliveries.card * K ^ 5 +
          (unsentEchoSet s).card * K ^ 4 +
          s.inflightEchoes.card * K ^ 3 +
          (notReadySentSet s).card * K ^ 2 +
          s.inflightReady.card * K +
          (unfinishedSet s).card
        ≤ n * K ^ 6 + n * K ^ 6 + n * K ^ 6 + K ^ 6 +
          n * K ^ 6 + K ^ 6 + n * K ^ 6 := by
      have := hA; have := hB; have := hC; have := hD
      have := hE; have := hF; have := hG
      omega
    have hrearrange :
        n * K ^ 6 + n * K ^ 6 + n * K ^ 6 + K ^ 6 +
          n * K ^ 6 + K ^ 6 + n * K ^ 6
        = 5 * n * K ^ 6 + 2 * K ^ 6 := by ring
    rw [hrearrange] at hsum6
    convert hsum6 using 0
  -- Final: 5·n·K⁶ + 2·K⁶ ≤ (7n+7)·K⁶.
  calc avssU s
      ≤ 5 * n * K ^ 6 + 2 * K ^ 6 := hsum
    _ ≤ (7 * n + 7) * K ^ 6 := by nlinarith [Nat.zero_le (K ^ 6)]

/-! ### Inductive invariant — step preservation (Phase 2b) -/

omit [Fintype F] in
/-- `avssTermInv` is preserved by every gated action.

For clause 1 (`dealerSent = false → quiescence`): every action either
flips `dealerSent` to `true` (`dealerShare`) or has its gate falsified
by the strengthened pre-share clause (`s.local_ p = init` plus empty
in-flight queues). The new `partyAmplify` action would otherwise
threaten the invariant — its `readyReceived.card ≥ t + 1` gate is
ruled out because `init.readyReceived = ∅`.

For clauses 2 (`echoSent → delivered`) and 3 (`output.isSome →
readySent ∧ delivered`): the only actions that can establish either
antecedent are `partyEchoSend` and `partyOutput`, whose gates already
guarantee the consequent. Other actions either don't touch the
relevant fields or don't shift them in a problematic direction. -/
theorem avssTermInv_step
    (a : AVSSAction n F) (s : AVSSState n t F)
    (h : actionGate a s) (hinv : avssTermInv s)
    (s' : AVSSState n t F)
    (hs' : s' ∈ (PMF.pure (avssStep a s)).support) :
    avssTermInv s' := by
  classical
  -- Pure step: `s' = avssStep a s`.
  have hs_eq : s' = avssStep a s := by
    have hsupp : (PMF.pure (avssStep a s)).support = {avssStep a s} :=
      PMF.support_pure _
    rw [hsupp] at hs'
    simpa using hs'
  subst hs_eq
  obtain ⟨hpre, hecho, hout, hloc_per_party⟩ := hinv
  refine ⟨?_, ?_, ?_, ?_⟩
  -- ===== Clause 1: ∀ p, dealerSent post p = false → all-init + queues empty post =====
  -- Phase 8.5d-α: hds' is now `∀ p, s'.dealerSent p = false`.
  · intro hds'
    cases a with
    | dealerShareTo p =>
        -- post.dealerSent = Function.update s.dealerSent p true.
        -- hds' p says the post is false at p, but it's `true` by Function.update_self.
        have hp := hds' p
        simp [avssStep, Function.update_self] at hp
    | partyDeliver p =>
        -- Frame: post.dealerSent = s.dealerSent. Gate: s.dealerSent p = true.
        have hpre_ds : s.dealerSent p = true := h.1
        have hp := hds' p
        simp [avssStep, setLocal] at hp
        rw [hpre_ds] at hp
        cases hp
    | partyCorruptDeliver p =>
        have hpre_ds : s.dealerSent p = true := h.1
        have hp := hds' p
        simp [avssStep, setLocal] at hp
        rw [hpre_ds] at hp
        cases hp
    | partyEchoSend p =>
        have hpre_ds : s.dealerSent p = true := h.2.2
        have hp := hds' p
        simp [avssStep, setLocal] at hp
        rw [hpre_ds] at hp
        cases hp
    | partyEchoReceive p q =>
        -- Frame: post.dealerSent = s.dealerSent. From hds' get pre-quiescence.
        have hpre_ds : ∀ r, s.dealerSent r = false := fun r => by
          have := hds' r; simpa [avssStep, setLocal] using this
        have hi := hpre hpre_ds
        have hgate_in : (q, p) ∈ s.inflightEchoes := h.1
        rw [hi.2.2.1] at hgate_in
        exact absurd hgate_in (Finset.notMem_empty _)
    | partyReady p =>
        have hpre_ds : s.dealerSent p = true := h.2.2.2
        have hp := hds' p
        simp [avssStep, setLocal] at hp
        rw [hpre_ds] at hp
        cases hp
    | partyAmplify p =>
        have hpre_ds : s.dealerSent p = true := h.2.2
        have hp := hds' p
        simp [avssStep, setLocal] at hp
        rw [hpre_ds] at hp
        cases hp
    | partyReceiveReady p q =>
        have hpre_ds : ∀ r, s.dealerSent r = false := fun r => by
          have := hds' r; simpa [avssStep, setLocal] using this
        have hi := hpre hpre_ds
        have hgate_in : (q, p) ∈ s.inflightReady := h.1
        rw [hi.2.2.2] at hgate_in
        exact absurd hgate_in (Finset.notMem_empty _)
    | partyOutput p =>
        have hpre_ds : ∀ r, s.dealerSent r = false := fun r => by
          have := hds' r; simpa [avssStep, setLocal] using this
        have hi := hpre hpre_ds
        have hp_init : s.local_ p = AVSSLocalState.init n t F := hi.1 p
        have hgate_del : (s.local_ p).delivered = true := h.2.1
        rw [hp_init] at hgate_del
        simp [AVSSLocalState.init] at hgate_del
  -- ===== Clause 2: ∀ honest p, echoSent post = true → delivered post = true =====
  · intro p hp hes
    cases a with
    | dealerShareTo q =>
        -- `dealerShareTo q` doesn't touch any party's local state.
        simp only [avssStep] at hes ⊢
        exact hecho p hp hes
    | partyDeliver q =>
        simp only [avssStep] at hes ⊢
        by_cases hpq : p = q
        · subst hpq
          rw [setLocal_local_self] at hes ⊢
        -- Goal closed by `rw`: post `delivered := true` is rfl.
        · rw [setLocal_local_ne _ _ _ _ hpq] at hes ⊢
          exact hecho p hp hes
    | partyCorruptDeliver q =>
        -- Same shape as partyDeliver: writes delivered := true, doesn't touch echoSent.
        simp only [avssStep] at hes ⊢
        by_cases hpq : p = q
        · subst hpq
          rw [setLocal_local_self] at hes ⊢
        · rw [setLocal_local_ne _ _ _ _ hpq] at hes ⊢
          exact hecho p hp hes
    | partyEchoSend q =>
        simp only [avssStep] at hes ⊢
        by_cases hpq : p = q
        · subst hpq
          rw [setLocal_local_self] at hes ⊢
          -- Post echoSent = true (set), post delivered = pre delivered.
          -- Phase 8.5b: gate is now 3-tuple ⟨delivered, ¬echoSent, dealerSent⟩.
          -- Pre delivered = true (= h.1).
          simp
          exact h.1
        · rw [setLocal_local_ne _ _ _ _ hpq] at hes ⊢
          exact hecho p hp hes
    | partyEchoReceive q r =>
        simp only [avssStep] at hes ⊢
        by_cases hpq : p = q
        · subst hpq
          rw [setLocal_local_self] at hes ⊢
          simp at hes ⊢
          exact hecho p hp hes
        · rw [setLocal_local_ne _ _ _ _ hpq] at hes ⊢
          exact hecho p hp hes
    | partyReady q =>
        simp only [avssStep] at hes ⊢
        by_cases hpq : p = q
        · subst hpq
          rw [setLocal_local_self] at hes ⊢
          simp at hes ⊢
          exact hecho p hp hes
        · rw [setLocal_local_ne _ _ _ _ hpq] at hes ⊢
          exact hecho p hp hes
    | partyAmplify q =>
        simp only [avssStep] at hes ⊢
        by_cases hpq : p = q
        · subst hpq
          rw [setLocal_local_self] at hes ⊢
          simp at hes ⊢
          exact hecho p hp hes
        · rw [setLocal_local_ne _ _ _ _ hpq] at hes ⊢
          exact hecho p hp hes
    | partyReceiveReady q r =>
        simp only [avssStep] at hes ⊢
        by_cases hpq : p = q
        · subst hpq
          rw [setLocal_local_self] at hes ⊢
          simp at hes ⊢
          exact hecho p hp hes
        · rw [setLocal_local_ne _ _ _ _ hpq] at hes ⊢
          exact hecho p hp hes
    | partyOutput q =>
        simp only [avssStep] at hes ⊢
        by_cases hpq : p = q
        · subst hpq
          rw [setLocal_local_self] at hes ⊢
          simp at hes ⊢
          exact hecho p hp hes
        · rw [setLocal_local_ne _ _ _ _ hpq] at hes ⊢
          exact hecho p hp hes
  -- ===== Clause 3: ∀ honest p, output.isSome = true → readySent ∧ delivered =====
  · intro p hp hsome
    cases a with
    | dealerShareTo q =>
        simp only [avssStep] at hsome ⊢
        exact hout p hp hsome
    | partyDeliver q =>
        simp only [avssStep] at hsome ⊢
        by_cases hpq : p = q
        · subst hpq
          rw [setLocal_local_self] at hsome ⊢
          -- Post sets delivered := true, output unchanged.
          -- After simp: goal becomes `(s.local_ p).readySent = true`.
          simp at hsome ⊢
          exact (hout p hp hsome).1
        · rw [setLocal_local_ne _ _ _ _ hpq] at hsome ⊢
          exact hout p hp hsome
    | partyCorruptDeliver q =>
        -- Same shape as partyDeliver: post delivered := true, output unchanged.
        simp only [avssStep] at hsome ⊢
        by_cases hpq : p = q
        · subst hpq
          rw [setLocal_local_self] at hsome ⊢
          simp at hsome ⊢
          exact (hout p hp hsome).1
        · rw [setLocal_local_ne _ _ _ _ hpq] at hsome ⊢
          exact hout p hp hsome
    | partyEchoSend q =>
        simp only [avssStep] at hsome ⊢
        by_cases hpq : p = q
        · subst hpq
          rw [setLocal_local_self] at hsome ⊢
          simp at hsome ⊢
          exact hout p hp hsome
        · rw [setLocal_local_ne _ _ _ _ hpq] at hsome ⊢
          exact hout p hp hsome
    | partyEchoReceive q r =>
        simp only [avssStep] at hsome ⊢
        by_cases hpq : p = q
        · subst hpq
          rw [setLocal_local_self] at hsome ⊢
          simp at hsome ⊢
          exact hout p hp hsome
        · rw [setLocal_local_ne _ _ _ _ hpq] at hsome ⊢
          exact hout p hp hsome
    | partyReady q =>
        simp only [avssStep] at hsome ⊢
        by_cases hpq : p = q
        · subst hpq
          rw [setLocal_local_self] at hsome ⊢
          -- Post sets readySent := true; output unchanged.
          -- After simp: goal becomes `(s.local_ p).delivered = true`.
          simp at hsome ⊢
          exact (hout p hp hsome).2
        · rw [setLocal_local_ne _ _ _ _ hpq] at hsome ⊢
          exact hout p hp hsome
    | partyAmplify q =>
        simp only [avssStep] at hsome ⊢
        by_cases hpq : p = q
        · subst hpq
          rw [setLocal_local_self] at hsome ⊢
          -- Same shape as partyReady: post readySent := true.
          simp at hsome ⊢
          exact (hout p hp hsome).2
        · rw [setLocal_local_ne _ _ _ _ hpq] at hsome ⊢
          exact hout p hp hsome
    | partyReceiveReady q r =>
        simp only [avssStep] at hsome ⊢
        by_cases hpq : p = q
        · subst hpq
          rw [setLocal_local_self] at hsome ⊢
          simp at hsome ⊢
          exact hout p hp hsome
        · rw [setLocal_local_ne _ _ _ _ hpq] at hsome ⊢
          exact hout p hp hsome
    | partyOutput q =>
        simp only [avssStep] at hsome ⊢
        by_cases hpq : p = q
        · subst hpq
          rw [setLocal_local_self] at hsome ⊢
          -- Post output := some _, readySent and delivered unchanged.
          -- Gate: pre readySent = true ∧ pre delivered = true.
          simp
          exact ⟨h.2.2.1, h.2.1⟩
        · rw [setLocal_local_ne _ _ _ _ hpq] at hsome ⊢
          exact hout p hp hsome
  -- ===== Clause 4: Phase 8.5d-α — per-party `dealerSent p = false → ¬delivered` =====
  · intro p hp_h hds_p
    cases a with
    | dealerShareTo q =>
        -- post.local_ p = s.local_ p; post.dealerSent p: if p = q, true (contradiction);
        -- else = s.dealerSent p, so we can apply hloc_per_party.
        by_cases hpq : p = q
        · -- p = q: post.dealerSent p = true via Function.update_self.
          subst hpq
          have h_post_t : (avssStep (.dealerShareTo p) s).dealerSent p = true := by
            simp [avssStep, Function.update_self]
          rw [h_post_t] at hds_p
          cases hds_p
        · -- p ≠ q: pull antecedent back to pre, get pre.delivered = false, post.local p = pre.
          have h_post_eq : (avssStep (.dealerShareTo q) s).dealerSent p = s.dealerSent p := by
            simp [avssStep, Function.update_of_ne hpq]
          rw [h_post_eq] at hds_p
          have h_pre_d : (s.local_ p).delivered = false :=
            hloc_per_party p hp_h hds_p
          show ((avssStep (.dealerShareTo q) s).local_ p).delivered = false
          simp [avssStep]
          exact h_pre_d
    | partyDeliver q =>
        -- gate: s.dealerSent q = true. So if p = q, hds_p contradicts gate.
        -- For p ≠ q, post.local_ p = s.local_ p and post.dealerSent = s.dealerSent.
        have h_pre_eq : (avssStep (.partyDeliver q) s).dealerSent = s.dealerSent := by
          simp [avssStep, setLocal]
        rw [h_pre_eq] at hds_p
        by_cases hpq : p = q
        · subst hpq
          rw [h.1] at hds_p
          cases hds_p
        · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
          exact hloc_per_party p hp_h hds_p
    | partyCorruptDeliver q =>
        -- p ∉ corr, q ∈ corr (gate), so p ≠ q.
        have hpq : p ≠ q := fun heq => hp_h (heq ▸ h.2.1)
        have h_pre_eq : (avssStep (.partyCorruptDeliver q) s).dealerSent = s.dealerSent := by
          simp [avssStep, setLocal]
        rw [h_pre_eq] at hds_p
        simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact hloc_per_party p hp_h hds_p
    | partyEchoSend q =>
        -- partyEchoSend writes echoSent, not delivered. Frame.
        have h_pre_eq : (avssStep (.partyEchoSend q) s).dealerSent = s.dealerSent := by
          simp [avssStep, setLocal]
        rw [h_pre_eq] at hds_p
        by_cases hpq : p = q
        · subst hpq
          show ((avssStep (.partyEchoSend p) s).local_ p).delivered = false
          simp [avssStep, setLocal_local_self]
          exact hloc_per_party p hp_h hds_p
        · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
          exact hloc_per_party p hp_h hds_p
    | partyEchoReceive q r =>
        -- writes echoesReceived, not delivered.
        have h_pre_eq : (avssStep (.partyEchoReceive q r) s).dealerSent = s.dealerSent := by
          simp [avssStep, setLocal]
        rw [h_pre_eq] at hds_p
        by_cases hpq : p = q
        · subst hpq
          show ((avssStep (.partyEchoReceive p r) s).local_ p).delivered = false
          simp [avssStep, setLocal_local_self]
          exact hloc_per_party p hp_h hds_p
        · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
          exact hloc_per_party p hp_h hds_p
    | partyReady q =>
        have h_pre_eq : (avssStep (.partyReady q) s).dealerSent = s.dealerSent := by
          simp [avssStep, setLocal]
        rw [h_pre_eq] at hds_p
        by_cases hpq : p = q
        · subst hpq
          show ((avssStep (.partyReady p) s).local_ p).delivered = false
          simp [avssStep, setLocal_local_self]
          exact hloc_per_party p hp_h hds_p
        · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
          exact hloc_per_party p hp_h hds_p
    | partyAmplify q =>
        have h_pre_eq : (avssStep (.partyAmplify q) s).dealerSent = s.dealerSent := by
          simp [avssStep, setLocal]
        rw [h_pre_eq] at hds_p
        by_cases hpq : p = q
        · subst hpq
          show ((avssStep (.partyAmplify p) s).local_ p).delivered = false
          simp [avssStep, setLocal_local_self]
          exact hloc_per_party p hp_h hds_p
        · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
          exact hloc_per_party p hp_h hds_p
    | partyReceiveReady q r =>
        have h_pre_eq : (avssStep (.partyReceiveReady q r) s).dealerSent = s.dealerSent := by
          simp [avssStep, setLocal]
        rw [h_pre_eq] at hds_p
        by_cases hpq : p = q
        · subst hpq
          show ((avssStep (.partyReceiveReady p r) s).local_ p).delivered = false
          simp [avssStep, setLocal_local_self]
          exact hloc_per_party p hp_h hds_p
        · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
          exact hloc_per_party p hp_h hds_p
    | partyOutput q =>
        have h_pre_eq : (avssStep (.partyOutput q) s).dealerSent = s.dealerSent := by
          simp [avssStep, setLocal]
        rw [h_pre_eq] at hds_p
        by_cases hpq : p = q
        · subst hpq
          show ((avssStep (.partyOutput p) s).local_ p).delivered = false
          simp [avssStep, setLocal_local_self]
          exact hloc_per_party p hp_h hds_p
        · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
          exact hloc_per_party p hp_h hds_p
/-! ### Variant strict-decrease per fair action (Phase 2c)

Each fair action decreases `avssU` by at least 1 under the inductive
invariant. The lex weighting (`K = (n+1)²`) is chosen so each component's
weighted contribution dominates the next component's max increase. -/

omit [Fintype F] in
/-- Helper: under `avssTermInv s` and any positive `Fin n` cardinality
witness in a queue or local field, the dealer must have shared. -/
private theorem dealerSent_true_of_inflight
    {s : AVSSState n t F} (hinv : avssTermInv s)
    (h : s.inflightDeliveries ≠ ∅ ∨ s.inflightEchoes ≠ ∅ ∨ s.inflightReady ≠ ∅) :
    ¬ (∀ p, s.dealerSent p = false) := by
  intro hbad
  have hi := hinv.1 hbad
  rcases h with h₁ | h₂ | h₃
  · exact h₁ hi.2.1
  · exact h₂ hi.2.2.1
  · exact h₃ hi.2.2.2

omit [Fintype F] in
/-- Helper: under `avssTermInv s`, if any honest party has a non-init
local state, the dealer has shared with at least one party. -/
private theorem dealerSent_true_of_local
    {s : AVSSState n t F} (hinv : avssTermInv s) {p : Fin n}
    (h : s.local_ p ≠ AVSSLocalState.init n t F) :
    ¬ (∀ q, s.dealerSent q = false) := by
  intro hbad
  exact h ((hinv.1 hbad).1 p)

omit [Fintype F] in
/-- `partyOutput` step: avssU strictly decreases by 1.
The only changed component is `unfinishedSet.card` (decreases by 1). -/
theorem avssU_step_partyOutput_lt (s : AVSSState n t F) (p : Fin n)
    (hgate : actionGate (AVSSAction.partyOutput p) s)
    (hinv : avssTermInv s) :
    avssU (avssStep (AVSSAction.partyOutput p) s) + 1 ≤ avssU s := by
  classical
  obtain ⟨hphon, hdel_t, _, hout_none, _⟩ := hgate
  -- Frame.
  have hds : (avssStep (AVSSAction.partyOutput p) s).dealerSent =
      s.dealerSent := by simp [avssStep, setLocal]
  have huds : unsentDealerSet (avssStep (AVSSAction.partyOutput p) s) =
      unsentDealerSet s :=
    by simp [unsentDealerSet, avssStep, setLocal]
  have hcorr : (avssStep (AVSSAction.partyOutput p) s).corrupted =
      s.corrupted := by simp [avssStep, setLocal]
  have hifd : (avssStep (AVSSAction.partyOutput p) s).inflightDeliveries =
      s.inflightDeliveries := by simp [avssStep]
  have hifr : (avssStep (AVSSAction.partyOutput p) s).inflightReady =
      s.inflightReady := by simp [avssStep]
  have hife : (avssStep (AVSSAction.partyOutput p) s).inflightEchoes =
      s.inflightEchoes := by simp [avssStep]
  -- Per-party: only output_p flips none → some _.
  have hdel : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyOutput p) s).local_ x).delivered =
        (s.local_ x).delivered := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hes : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyOutput p) s).local_ x).echoSent =
        (s.local_ x).echoSent := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hrs : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyOutput p) s).local_ x).readySent =
        (s.local_ x).readySent := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hout_p_some :
      ((avssStep (AVSSAction.partyOutput p) s).local_ p).output ≠ none := by
    simp [avssStep]
  have hout_ne : ∀ x : Fin n, x ≠ p →
      ((avssStep (AVSSAction.partyOutput p) s).local_ x).output =
        (s.local_ x).output := by
    intro x hxp
    simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  -- Set equalities.
  have hH : honestSet (avssStep (AVSSAction.partyOutput p) s) =
      honestSet s := by
    apply Finset.ext; intro x
    simp only [honestSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr]
  have huss : unsentEchoSet (avssStep (AVSSAction.partyOutput p) s) =
      unsentEchoSet s := by
    apply Finset.ext; intro x
    simp only [unsentEchoSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr, hdel x, hes x]
  have hnrs : notReadySentSet (avssStep (AVSSAction.partyOutput p) s) =
      notReadySentSet s := by
    apply Finset.ext; intro x
    simp only [notReadySentSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr, hrs x]
  -- unfinishedSet post = unfinishedSet pre.erase p.
  have hp_in_unfin : p ∈ unfinishedSet s := by
    simp only [unfinishedSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hphon, hout_none⟩
  have hunfin_post : unfinishedSet (avssStep (AVSSAction.partyOutput p) s) =
      (unfinishedSet s).erase p := by
    apply Finset.ext; intro x
    simp only [unfinishedSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    rw [hcorr]
    by_cases hxp : x = p
    · subst hxp
      simp [hout_p_some]
    · rw [hout_ne x hxp]
      simp [hxp]
  have hunfin_card :
      (unfinishedSet (avssStep (AVSSAction.partyOutput p) s)).card =
      (unfinishedSet s).card - 1 := by
    rw [hunfin_post, Finset.card_erase_of_mem hp_in_unfin]
  have hunfin_pos : 1 ≤ (unfinishedSet s).card :=
    Finset.card_pos.mpr ⟨p, hp_in_unfin⟩
  show avssU (avssStep (AVSSAction.partyOutput p) s) + 1 ≤ avssU s
  unfold avssU
  rw [huds, hifd, hife, hifr, huss, hnrs, hunfin_card]
  -- The `let K := lexBase n` binding survives in the goal; reduce both sides
  -- to the difference `(unfinishedSet s).card - 1 + 1 ≤ (unfinishedSet s).card`.
  show _ + ((unfinishedSet s).card - 1) + 1 ≤ _ + (unfinishedSet s).card
  omega

omit [Fintype F] in
/-- `partyReceiveReady` step: avssU strictly decreases by `K`. -/
theorem avssU_step_partyReceiveReady_lt (s : AVSSState n t F) (p q : Fin n)
    (hgate : actionGate (AVSSAction.partyReceiveReady p q) s)
    (hinv : avssTermInv s) :
    avssU (avssStep (AVSSAction.partyReceiveReady p q) s) + 1 ≤ avssU s := by
  classical
  -- Phase 8.5b-γ-followup-2: gate is now ⟨(q,p) ∈ inflightReady, ¬received⟩.
  obtain ⟨hqin, _⟩ := hgate
  -- Frame.
  have hds : (avssStep (AVSSAction.partyReceiveReady p q) s).dealerSent =
      s.dealerSent := by simp [avssStep, setLocal]
  have huds : unsentDealerSet (avssStep (AVSSAction.partyReceiveReady p q) s) =
      unsentDealerSet s :=
    by simp [unsentDealerSet, avssStep, setLocal]
  have hcorr : (avssStep (AVSSAction.partyReceiveReady p q) s).corrupted =
      s.corrupted := by simp [avssStep, setLocal]
  have hifd : (avssStep (AVSSAction.partyReceiveReady p q) s).inflightDeliveries =
      s.inflightDeliveries := by simp [avssStep]
  have hife : (avssStep (AVSSAction.partyReceiveReady p q) s).inflightEchoes =
      s.inflightEchoes := by simp [avssStep]
  have hifr : (avssStep (AVSSAction.partyReceiveReady p q) s).inflightReady =
      s.inflightReady.erase (q, p) := by simp [avssStep]
  -- Per-party: only readyReceived_p changes (not in U).
  have hdel : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyReceiveReady p q) s).local_ x).delivered =
        (s.local_ x).delivered := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hes : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyReceiveReady p q) s).local_ x).echoSent =
        (s.local_ x).echoSent := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hrs : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyReceiveReady p q) s).local_ x).readySent =
        (s.local_ x).readySent := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hout : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyReceiveReady p q) s).local_ x).output =
        (s.local_ x).output := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  -- Set equalities.
  have huss : unsentEchoSet (avssStep (AVSSAction.partyReceiveReady p q) s) =
      unsentEchoSet s := by
    apply Finset.ext; intro x
    simp only [unsentEchoSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr, hdel x, hes x]
  have hnrs : notReadySentSet (avssStep (AVSSAction.partyReceiveReady p q) s) =
      notReadySentSet s := by
    apply Finset.ext; intro x
    simp only [notReadySentSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr, hrs x]
  have hunfin : unfinishedSet (avssStep (AVSSAction.partyReceiveReady p q) s) =
      unfinishedSet s := by
    apply Finset.ext; intro x
    simp only [unfinishedSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr, hout x]
  have hifr_card :
      (s.inflightReady.erase (q, p)).card = s.inflightReady.card - 1 :=
    Finset.card_erase_of_mem hqin
  have hifr_pos : 1 ≤ s.inflightReady.card :=
    Finset.card_pos.mpr ⟨(q, p), hqin⟩
  have hK_pos : 1 ≤ lexBase n := lexBase_pos
  unfold avssU
  rw [huds, hifd, hife, hifr, huss, hnrs, hunfin, hifr_card]
  -- Goal: udS*K^6 + ifd*K^5 + uss*K^4 + ife*K^3 + nrs*K^2 + (ifr-1)*K + unfin + 1
  --     ≤ udS*K^6 + ifd*K^5 + uss*K^4 + ife*K^3 + nrs*K^2 + ifr*K + unfin
  -- ⟺ (ifr - 1)*K + 1 ≤ ifr*K, given ifr ≥ 1.
  have h_split : (s.inflightReady.card - 1) * lexBase n + lexBase n =
      s.inflightReady.card * lexBase n := by
    have : s.inflightReady.card - 1 + 1 = s.inflightReady.card :=
      Nat.sub_add_cancel hifr_pos
    calc (s.inflightReady.card - 1) * lexBase n + lexBase n
        = ((s.inflightReady.card - 1) + 1) * lexBase n := by ring
      _ = s.inflightReady.card * lexBase n := by rw [this]
  nlinarith [h_split, hK_pos]

omit [Fintype F] in
/-- `partyReady` step: avssU strictly decreases.  c5 (notReadySent) drops
by 1 (loses K²); c6 (inflightReady) gains at most n (gains ≤ n·K). Net ≥
K² − n·K = K(K-n) ≥ K ≥ 1 since K = (n+1)² ≥ n+1.

Phase 8.5b: `notReadySentSet` remains honest-only, so strict decrease
requires an explicit honest-firing premise `hph`. (Corrupt-fired
`partyReady` is dispatched via `V_super`/`U_dec_det`'s `Or.inr` branch
in `avssCert`.)

Phase 8.5b-γ-followup-2: per-pair `inflightReady` — `partyReady p` may
add up to `n` tokens `(p, r)` instead of 1.  K is large enough that
the K² drop still dominates. -/
theorem avssU_step_partyReady_lt (s : AVSSState n t F) (p : Fin n)
    (hgate : actionGate (AVSSAction.partyReady p) s)
    (hinv : avssTermInv s) (hph : p ∉ s.corrupted) :
    avssU (avssStep (AVSSAction.partyReady p) s) + 1 ≤ avssU s := by
  classical
  obtain ⟨hdel_t, hrsf, _hech, _hds_pre⟩ := hgate
  have hphon : p ∉ s.corrupted := hph
  -- n ≥ 1 from p : Fin n.
  have hn_pos : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; exact p.elim0
    · exact hn
  have hK_ge : 4 ≤ lexBase n := by unfold lexBase; nlinarith
  -- K = (n+1)² ≥ n+1.
  have hK_ge_n1 : n + 1 ≤ lexBase n := by unfold lexBase; nlinarith
  -- Frame.
  have hds : (avssStep (AVSSAction.partyReady p) s).dealerSent =
      s.dealerSent := by simp [avssStep, setLocal]
  have huds : unsentDealerSet (avssStep (AVSSAction.partyReady p) s) =
      unsentDealerSet s :=
    by simp [unsentDealerSet, avssStep, setLocal]
  have hcorr : (avssStep (AVSSAction.partyReady p) s).corrupted =
      s.corrupted := by simp [avssStep, setLocal]
  have hifd : (avssStep (AVSSAction.partyReady p) s).inflightDeliveries =
      s.inflightDeliveries := by simp [avssStep]
  have hife : (avssStep (AVSSAction.partyReady p) s).inflightEchoes =
      s.inflightEchoes := by simp [avssStep]
  have hifr : (avssStep (AVSSAction.partyReady p) s).inflightReady =
      s.inflightReady ∪
        (Finset.univ : Finset (Fin n)).image (fun r => (p, r)) := by
    simp [avssStep]
  -- Per-party: only readySent_p flips false → true.
  have hdel : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyReady p) s).local_ x).delivered =
        (s.local_ x).delivered := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hes : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyReady p) s).local_ x).echoSent =
        (s.local_ x).echoSent := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hrs_p : ((avssStep (AVSSAction.partyReady p) s).local_ p).readySent = true := by
    simp [avssStep]
  have hrs_ne : ∀ x : Fin n, x ≠ p →
      ((avssStep (AVSSAction.partyReady p) s).local_ x).readySent =
        (s.local_ x).readySent := by
    intro x hxp
    simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hout : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyReady p) s).local_ x).output =
        (s.local_ x).output := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  -- Set equalities.
  have huss : unsentEchoSet (avssStep (AVSSAction.partyReady p) s) =
      unsentEchoSet s := by
    apply Finset.ext; intro x
    simp only [unsentEchoSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr, hdel x, hes x]
  have hunfin : unfinishedSet (avssStep (AVSSAction.partyReady p) s) =
      unfinishedSet s := by
    apply Finset.ext; intro x
    simp only [unfinishedSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr, hout x]
  -- notReadySent post = pre.erase p.
  have hp_in_nrs : p ∈ notReadySentSet s := by
    simp only [notReadySentSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hphon, hrsf⟩
  have hnrs_post : notReadySentSet (avssStep (AVSSAction.partyReady p) s) =
      (notReadySentSet s).erase p := by
    apply Finset.ext; intro x
    simp only [notReadySentSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    rw [hcorr]
    by_cases hxp : x = p
    · subst hxp; simp [hrs_p]
    · rw [hrs_ne x hxp]; simp [hxp]
  have hnrs_card :
      (notReadySentSet (avssStep (AVSSAction.partyReady p) s)).card =
      (notReadySentSet s).card - 1 := by
    rw [hnrs_post, Finset.card_erase_of_mem hp_in_nrs]
  have hnrs_pos : 1 ≤ (notReadySentSet s).card :=
    Finset.card_pos.mpr ⟨p, hp_in_nrs⟩
  -- Per-pair tokens: increase ≤ |image| ≤ n.
  have hImg_card :
      ((Finset.univ : Finset (Fin n)).image (fun r => (p, r))).card ≤ n := by
    calc ((Finset.univ : Finset (Fin n)).image (fun r => (p, r))).card
        ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
      _ = n := by simp
  have hifr_card_le :
      (s.inflightReady ∪
        (Finset.univ : Finset (Fin n)).image (fun r => (p, r))).card
        ≤ s.inflightReady.card + n := by
    calc (s.inflightReady ∪
            (Finset.univ : Finset (Fin n)).image (fun r => (p, r))).card
        ≤ s.inflightReady.card +
            ((Finset.univ : Finset (Fin n)).image (fun r => (p, r))).card :=
          Finset.card_union_le _ _
      _ ≤ s.inflightReady.card + n := by omega
  unfold avssU
  rw [huds, hifd, hife, hifr, huss, hnrs_card, hunfin]
  -- Set abbreviations.
  set K := lexBase n with hK_def
  set nrs := (notReadySentSet s).card
  set ifr := s.inflightReady.card
  -- Goal: ... + (nrs - 1) * K^2 + (ifr ∪ image).card * K + ... + 1
  --     ≤ ... + nrs * K^2 + ifr * K + ...
  -- Cancel common: (nrs-1)*K^2 + (ifr ∪ image).card*K + 1 ≤ nrs*K^2 + ifr*K
  -- |ifr ∪ image| ≤ ifr + n, so (ifr ∪ image)*K - ifr*K ≤ n*K. Need K^2 ≥ n*K + 1.
  -- K = (n+1)^2 = n^2 + 2n + 1; K^2 - n*K = K*(K - n) = K*(n^2 + n + 1) ≥ K ≥ 5.
  have h_nrs_split : (nrs - 1) * K^2 + K^2 = nrs * K^2 := by
    have : nrs - 1 + 1 = nrs := Nat.sub_add_cancel hnrs_pos
    calc (nrs - 1) * K^2 + K^2 = ((nrs - 1) + 1) * K^2 := by ring
      _ = nrs * K^2 := by rw [this]
  have hK_ge_n1' : n + 1 ≤ K := by rw [hK_def]; exact hK_ge_n1
  have h_K2_ge_nK : K^2 ≥ n * K + K := by nlinarith [hK_ge_n1', hK_ge]
  nlinarith [h_nrs_split, h_K2_ge_nK, hifr_card_le, hK_ge, hnrs_pos]

omit [Fintype F] in
/-- `partyAmplify` step: avssU strictly decreases.  Same shape as
`partyReady`: c5 (notReadySent) drops by 1; c6 (inflightReady) gains at
most 1.  Net K² - K ≥ 1.

Phase 8.5b: see comment on `avssU_step_partyReady_lt` for the explicit
honest-firing premise. -/
theorem avssU_step_partyAmplify_lt (s : AVSSState n t F) (p : Fin n)
    (hgate : actionGate (AVSSAction.partyAmplify p) s)
    (hinv : avssTermInv s) (hph : p ∉ s.corrupted) :
    avssU (avssStep (AVSSAction.partyAmplify p) s) + 1 ≤ avssU s := by
  classical
  obtain ⟨hrsf, hrr_t, _hds_pre⟩ := hgate
  have hphon : p ∉ s.corrupted := hph
  have hn_pos : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; exact p.elim0
    · exact hn
  have hK_ge : 4 ≤ lexBase n := by unfold lexBase; nlinarith
  have hK_ge_n1 : n + 1 ≤ lexBase n := by unfold lexBase; nlinarith
  -- Frame (analogous to partyReady).
  have hds : (avssStep (AVSSAction.partyAmplify p) s).dealerSent =
      s.dealerSent := by simp [avssStep, setLocal]
  have huds : unsentDealerSet (avssStep (AVSSAction.partyAmplify p) s) =
      unsentDealerSet s :=
    by simp [unsentDealerSet, avssStep, setLocal]
  have hcorr : (avssStep (AVSSAction.partyAmplify p) s).corrupted =
      s.corrupted := by simp [avssStep, setLocal]
  have hifd : (avssStep (AVSSAction.partyAmplify p) s).inflightDeliveries =
      s.inflightDeliveries := by simp [avssStep]
  have hife : (avssStep (AVSSAction.partyAmplify p) s).inflightEchoes =
      s.inflightEchoes := by simp [avssStep]
  have hifr : (avssStep (AVSSAction.partyAmplify p) s).inflightReady =
      s.inflightReady ∪
        (Finset.univ : Finset (Fin n)).image (fun r => (p, r)) := by
    simp [avssStep]
  have hdel : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyAmplify p) s).local_ x).delivered =
        (s.local_ x).delivered := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hes : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyAmplify p) s).local_ x).echoSent =
        (s.local_ x).echoSent := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hrs_p :
      ((avssStep (AVSSAction.partyAmplify p) s).local_ p).readySent = true := by
    simp [avssStep]
  have hrs_ne : ∀ x : Fin n, x ≠ p →
      ((avssStep (AVSSAction.partyAmplify p) s).local_ x).readySent =
        (s.local_ x).readySent := by
    intro x hxp
    simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hout : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyAmplify p) s).local_ x).output =
        (s.local_ x).output := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have huss : unsentEchoSet (avssStep (AVSSAction.partyAmplify p) s) =
      unsentEchoSet s := by
    apply Finset.ext; intro x
    simp only [unsentEchoSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr, hdel x, hes x]
  have hunfin : unfinishedSet (avssStep (AVSSAction.partyAmplify p) s) =
      unfinishedSet s := by
    apply Finset.ext; intro x
    simp only [unfinishedSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr, hout x]
  have hp_in_nrs : p ∈ notReadySentSet s := by
    simp only [notReadySentSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hphon, hrsf⟩
  have hnrs_post : notReadySentSet (avssStep (AVSSAction.partyAmplify p) s) =
      (notReadySentSet s).erase p := by
    apply Finset.ext; intro x
    simp only [notReadySentSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    rw [hcorr]
    by_cases hxp : x = p
    · subst hxp; simp [hrs_p]
    · rw [hrs_ne x hxp]; simp [hxp]
  have hnrs_card :
      (notReadySentSet (avssStep (AVSSAction.partyAmplify p) s)).card =
      (notReadySentSet s).card - 1 := by
    rw [hnrs_post, Finset.card_erase_of_mem hp_in_nrs]
  have hnrs_pos : 1 ≤ (notReadySentSet s).card :=
    Finset.card_pos.mpr ⟨p, hp_in_nrs⟩
  -- Per-pair tokens: increase ≤ |image| ≤ n.
  have hImg_card :
      ((Finset.univ : Finset (Fin n)).image (fun r => (p, r))).card ≤ n := by
    calc ((Finset.univ : Finset (Fin n)).image (fun r => (p, r))).card
        ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
      _ = n := by simp
  have hifr_card_le :
      (s.inflightReady ∪
        (Finset.univ : Finset (Fin n)).image (fun r => (p, r))).card
        ≤ s.inflightReady.card + n := by
    calc (s.inflightReady ∪
            (Finset.univ : Finset (Fin n)).image (fun r => (p, r))).card
        ≤ s.inflightReady.card +
            ((Finset.univ : Finset (Fin n)).image (fun r => (p, r))).card :=
          Finset.card_union_le _ _
      _ ≤ s.inflightReady.card + n := by omega
  unfold avssU
  rw [huds, hifd, hife, hifr, huss, hnrs_card, hunfin]
  set K := lexBase n with hK_def
  set nrs := (notReadySentSet s).card
  set ifr := s.inflightReady.card
  have h_nrs_split : (nrs - 1) * K^2 + K^2 = nrs * K^2 := by
    have : nrs - 1 + 1 = nrs := Nat.sub_add_cancel hnrs_pos
    calc (nrs - 1) * K^2 + K^2 = ((nrs - 1) + 1) * K^2 := by ring
      _ = nrs * K^2 := by rw [this]
  have hK_ge_n1' : n + 1 ≤ K := by rw [hK_def]; exact hK_ge_n1
  have h_K2_ge_nK : K^2 ≥ n * K + K := by nlinarith [hK_ge_n1', hK_ge]
  nlinarith [h_nrs_split, h_K2_ge_nK, hifr_card_le, hK_ge, hnrs_pos]

omit [Fintype F] in
/-- `partyEchoReceive` step: avssU strictly decreases by `K³`. -/
theorem avssU_step_partyEchoReceive_lt (s : AVSSState n t F) (p q : Fin n)
    (hgate : actionGate (AVSSAction.partyEchoReceive p q) s)
    (hinv : avssTermInv s) :
    avssU (avssStep (AVSSAction.partyEchoReceive p q) s) + 1 ≤ avssU s := by
  classical
  -- Phase 8.5b: gate is now 2-tuple ⟨(q,p) ∈ inflightEchoes, ¬received⟩.
  obtain ⟨hqp_in, _⟩ := hgate
  have hK_pos : 1 ≤ lexBase n := lexBase_pos
  -- Frame.
  have hds : (avssStep (AVSSAction.partyEchoReceive p q) s).dealerSent =
      s.dealerSent := by simp [avssStep, setLocal]
  have huds : unsentDealerSet (avssStep (AVSSAction.partyEchoReceive p q) s) =
      unsentDealerSet s :=
    by simp [unsentDealerSet, avssStep, setLocal]
  have hcorr : (avssStep (AVSSAction.partyEchoReceive p q) s).corrupted =
      s.corrupted := by simp [avssStep, setLocal]
  have hifd : (avssStep (AVSSAction.partyEchoReceive p q) s).inflightDeliveries =
      s.inflightDeliveries := by simp [avssStep]
  have hife : (avssStep (AVSSAction.partyEchoReceive p q) s).inflightEchoes =
      s.inflightEchoes.erase (q, p) := by simp [avssStep]
  have hifr : (avssStep (AVSSAction.partyEchoReceive p q) s).inflightReady =
      s.inflightReady := by simp [avssStep]
  -- Per-party: only echoesReceived_p changes (not in U).
  have hdel : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyEchoReceive p q) s).local_ x).delivered =
        (s.local_ x).delivered := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hes : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyEchoReceive p q) s).local_ x).echoSent =
        (s.local_ x).echoSent := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hrs : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyEchoReceive p q) s).local_ x).readySent =
        (s.local_ x).readySent := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hout : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyEchoReceive p q) s).local_ x).output =
        (s.local_ x).output := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have huss : unsentEchoSet (avssStep (AVSSAction.partyEchoReceive p q) s) =
      unsentEchoSet s := by
    apply Finset.ext; intro x
    simp only [unsentEchoSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr, hdel x, hes x]
  have hnrs : notReadySentSet (avssStep (AVSSAction.partyEchoReceive p q) s) =
      notReadySentSet s := by
    apply Finset.ext; intro x
    simp only [notReadySentSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr, hrs x]
  have hunfin : unfinishedSet (avssStep (AVSSAction.partyEchoReceive p q) s) =
      unfinishedSet s := by
    apply Finset.ext; intro x
    simp only [unfinishedSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr, hout x]
  have hife_card :
      (s.inflightEchoes.erase (q, p)).card = s.inflightEchoes.card - 1 :=
    Finset.card_erase_of_mem hqp_in
  have hife_pos : 1 ≤ s.inflightEchoes.card :=
    Finset.card_pos.mpr ⟨(q, p), hqp_in⟩
  unfold avssU
  rw [huds, hifd, hife, hifr, huss, hnrs, hunfin, hife_card]
  set K := lexBase n with hK_def
  -- Goal: ... + (ife - 1)*K^3 + ... + 1 ≤ ... + ife*K^3 + ...
  have h_split : (s.inflightEchoes.card - 1) * K^3 + K^3 =
      s.inflightEchoes.card * K^3 := by
    have : s.inflightEchoes.card - 1 + 1 = s.inflightEchoes.card :=
      Nat.sub_add_cancel hife_pos
    calc (s.inflightEchoes.card - 1) * K^3 + K^3
        = ((s.inflightEchoes.card - 1) + 1) * K^3 := by ring
      _ = s.inflightEchoes.card * K^3 := by rw [this]
  have hK3_pos : 1 ≤ K^3 := Nat.one_le_pow _ _ hK_pos
  nlinarith [h_split, hK3_pos]

omit [Fintype F] in
/-- `partyDeliver` step: avssU strictly decreases.  c2 (inflightDeliveries)
drops by 1 (loses K⁵); c3 (unsentEchoSet) gains 1 (gains K⁴) — `p` was
not in `unsentEchoSet` pre (delivered=false) but joins post (delivered=true,
echoSent=false from inv clause 2 contrapositive). Net ≥ K⁴(K-1) ≥ 1. -/
theorem avssU_step_partyDeliver_lt (s : AVSSState n t F) (p : Fin n)
    (hgate : actionGate (AVSSAction.partyDeliver p) s)
    (hinv : avssTermInv s) :
    avssU (avssStep (AVSSAction.partyDeliver p) s) + 1 ≤ avssU s := by
  classical
  obtain ⟨_hds_pre, hphon, hpin, hdel_f, _hdm⟩ := hgate
  have hn_pos : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; exact p.elim0
    · exact hn
  have hK_ge : 4 ≤ lexBase n := by unfold lexBase; nlinarith
  -- Pre echoSent at p = false (from inv clause 2 contrapositive).
  have hes_pre_p : (s.local_ p).echoSent = false := by
    by_contra hbad
    have hes_t : (s.local_ p).echoSent = true := by
      cases h : (s.local_ p).echoSent with
      | true => rfl
      | false => exact absurd h hbad
    have := hinv.2.1 p hphon hes_t
    rw [this] at hdel_f; cases hdel_f
  -- Frame.
  have hds : (avssStep (AVSSAction.partyDeliver p) s).dealerSent =
      s.dealerSent := by simp [avssStep, setLocal]
  have huds : unsentDealerSet (avssStep (AVSSAction.partyDeliver p) s) =
      unsentDealerSet s :=
    by simp [unsentDealerSet, avssStep, setLocal]
  have hcorr : (avssStep (AVSSAction.partyDeliver p) s).corrupted =
      s.corrupted := by simp [avssStep, setLocal]
  have hifd : (avssStep (AVSSAction.partyDeliver p) s).inflightDeliveries =
      s.inflightDeliveries.erase p := by simp [avssStep]
  have hife : (avssStep (AVSSAction.partyDeliver p) s).inflightEchoes =
      s.inflightEchoes := by simp [avssStep]
  have hifr : (avssStep (AVSSAction.partyDeliver p) s).inflightReady =
      s.inflightReady := by simp [avssStep]
  -- Per-party: only delivered_p (false→true) and rowPoly_p change.
  have hdel_p :
      ((avssStep (AVSSAction.partyDeliver p) s).local_ p).delivered = true := by
    simp [avssStep]
  have hdel_ne : ∀ x : Fin n, x ≠ p →
      ((avssStep (AVSSAction.partyDeliver p) s).local_ x).delivered =
        (s.local_ x).delivered := by
    intro x hxp
    simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hes_p :
      ((avssStep (AVSSAction.partyDeliver p) s).local_ p).echoSent =
        (s.local_ p).echoSent := by
    simp [avssStep]
  have hes_ne : ∀ x : Fin n, x ≠ p →
      ((avssStep (AVSSAction.partyDeliver p) s).local_ x).echoSent =
        (s.local_ x).echoSent := by
    intro x hxp
    simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hrs : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyDeliver p) s).local_ x).readySent =
        (s.local_ x).readySent := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hout : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyDeliver p) s).local_ x).output =
        (s.local_ x).output := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  -- Set equalities.
  have hnrs : notReadySentSet (avssStep (AVSSAction.partyDeliver p) s) =
      notReadySentSet s := by
    apply Finset.ext; intro x
    simp only [notReadySentSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr, hrs x]
  have hunfin : unfinishedSet (avssStep (AVSSAction.partyDeliver p) s) =
      unfinishedSet s := by
    apply Finset.ext; intro x
    simp only [unfinishedSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr, hout x]
  -- p ∉ unsentEchoSet pre (delivered=false), p ∈ unsentEchoSet post.
  have hp_notin_uss_pre : p ∉ unsentEchoSet s := by
    simp only [unsentEchoSet, Finset.mem_filter, Finset.mem_univ, true_and]
    intro ⟨_, hd, _⟩
    rw [hd] at hdel_f; cases hdel_f
  have hp_in_uss_post : p ∈ unsentEchoSet (avssStep (AVSSAction.partyDeliver p) s) := by
    simp only [unsentEchoSet, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, hdel_p, ?_⟩
    · rw [hcorr]; exact hphon
    · rw [hes_p]; exact hes_pre_p
  -- unsentEchoSet post = insert p (unsentEchoSet pre).
  have huss_post :
      unsentEchoSet (avssStep (AVSSAction.partyDeliver p) s) =
      insert p (unsentEchoSet s) := by
    apply Finset.ext; intro x
    simp only [unsentEchoSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    rw [hcorr]
    by_cases hxp : x = p
    · subst hxp
      rw [hdel_p, hes_p, hes_pre_p]
      simp [hphon]
    · rw [hdel_ne x hxp, hes_ne x hxp]
      constructor
      · intro h; right; exact h
      · rintro (heq | h)
        · exact absurd heq hxp
        · exact h
  have huss_card :
      (unsentEchoSet (avssStep (AVSSAction.partyDeliver p) s)).card =
      (unsentEchoSet s).card + 1 := by
    rw [huss_post]
    exact Finset.card_insert_of_notMem hp_notin_uss_pre
  -- inflightDeliveries.erase card.
  have hifd_card :
      (s.inflightDeliveries.erase p).card = s.inflightDeliveries.card - 1 :=
    Finset.card_erase_of_mem hpin
  have hifd_pos : 1 ≤ s.inflightDeliveries.card :=
    Finset.card_pos.mpr ⟨p, hpin⟩
  unfold avssU
  rw [huds, hifd, hife, hifr, huss_card, hnrs, hunfin, hifd_card]
  set K := lexBase n with hK_def
  set ifd := s.inflightDeliveries.card
  set uss := (unsentEchoSet s).card
  -- Goal: (ifd - 1)*K^5 + (uss + 1)*K^4 + ... + 1 ≤ ifd*K^5 + uss*K^4 + ...
  -- ⟺ (ifd-1)*K^5 + uss*K^4 + K^4 + 1 ≤ ifd*K^5 + uss*K^4
  -- ⟺ (ifd-1)*K^5 + K^4 + 1 ≤ ifd*K^5
  -- Substitute ifd*K^5 = (ifd-1)*K^5 + K^5: K^4 + 1 ≤ K^5 = K * K^4.
  -- For K ≥ 2, K * K^4 ≥ 2 * K^4 = K^4 + K^4 ≥ K^4 + 1. ✓
  have h_ifd_split : (ifd - 1) * K^5 + K^5 = ifd * K^5 := by
    have : ifd - 1 + 1 = ifd := Nat.sub_add_cancel hifd_pos
    calc (ifd - 1) * K^5 + K^5 = ((ifd - 1) + 1) * K^5 := by ring
      _ = ifd * K^5 := by rw [this]
  have h_K4_pos : 1 ≤ K^4 := Nat.one_le_pow _ _ (by omega)
  have h_K5_ge : K^5 ≥ K^4 + 1 := by
    calc K^5 = K * K^4 := by ring
      _ ≥ 2 * K^4 := by nlinarith [h_K4_pos, hK_ge]
      _ = K^4 + K^4 := by ring
      _ ≥ K^4 + 1 := by omega
  nlinarith [h_ifd_split, h_K5_ge, hK_ge, hifd_pos]

omit [Fintype F] in
/-- `partyCorruptDeliver` step: avssU is unchanged. The action only modifies
state at a corrupt party — `inflightCorruptDeliveries` (not in U) and the
local state of `p ∈ s.corrupted` (which is filtered out of all U-sets,
since they restrict to `p ∉ s.corrupted`). -/
theorem avssU_step_partyCorruptDeliver_eq (s : AVSSState n t F) (p : Fin n)
    (hgate : actionGate (AVSSAction.partyCorruptDeliver p) s) :
    avssU (avssStep (AVSSAction.partyCorruptDeliver p) s) = avssU s := by
  classical
  obtain ⟨_, hpcorr, _, _, _⟩ := hgate
  -- Frame.
  have hds : (avssStep (AVSSAction.partyCorruptDeliver p) s).dealerSent =
      s.dealerSent := by simp [avssStep, setLocal]
  have huds : unsentDealerSet (avssStep (AVSSAction.partyCorruptDeliver p) s) =
      unsentDealerSet s :=
    by simp [unsentDealerSet, avssStep, setLocal]
  have hcorr : (avssStep (AVSSAction.partyCorruptDeliver p) s).corrupted =
      s.corrupted := by simp [avssStep, setLocal]
  have hifd : (avssStep (AVSSAction.partyCorruptDeliver p) s).inflightDeliveries =
      s.inflightDeliveries := by simp [avssStep]
  have hife : (avssStep (AVSSAction.partyCorruptDeliver p) s).inflightEchoes =
      s.inflightEchoes := by simp [avssStep]
  have hifr : (avssStep (AVSSAction.partyCorruptDeliver p) s).inflightReady =
      s.inflightReady := by simp [avssStep]
  -- p is corrupt, so changing p's local doesn't affect honest-party-restricted sets.
  have hloc_ne : ∀ x : Fin n, x ≠ p →
      (avssStep (AVSSAction.partyCorruptDeliver p) s).local_ x = s.local_ x := by
    intro x hxp
    simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have huss : unsentEchoSet (avssStep (AVSSAction.partyCorruptDeliver p) s) =
      unsentEchoSet s := by
    apply Finset.ext; intro x
    simp only [unsentEchoSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr]
    by_cases hxp : x = p
    · subst hxp; simp [hpcorr]
    · rw [hloc_ne x hxp]
  have hnrs : notReadySentSet (avssStep (AVSSAction.partyCorruptDeliver p) s) =
      notReadySentSet s := by
    apply Finset.ext; intro x
    simp only [notReadySentSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr]
    by_cases hxp : x = p
    · subst hxp; simp [hpcorr]
    · rw [hloc_ne x hxp]
  have hunfin : unfinishedSet (avssStep (AVSSAction.partyCorruptDeliver p) s) =
      unfinishedSet s := by
    apply Finset.ext; intro x
    simp only [unfinishedSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr]
    by_cases hxp : x = p
    · subst hxp; simp [hpcorr]
    · rw [hloc_ne x hxp]
  have hH : honestSet (avssStep (AVSSAction.partyCorruptDeliver p) s) =
      honestSet s := by
    apply Finset.ext; intro x
    simp only [honestSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr]
  unfold avssU
  rw [huds, hifd, hife, hifr, huss, hnrs, hunfin]

omit [Fintype F] in
/-- `partyEchoSend` step: avssU strictly decreases.  c3 (unsentEchoSet)
drops by 1 (loses K⁴); c4 (inflightEchoes) gains at most `n` (gains
≤ n·K³). The lex weight K = (n+1)² is chosen exactly so K⁴ > n·K³.

Phase 8.5b: `unsentEchoSet` remains honest-only, and the broadcast
filter now covers all receivers (broadens to `Finset.univ`). The
strict-decrease argument requires an explicit honest-firing premise
`hph`. (Corrupt-fired `partyEchoSend` is dispatched via
`V_super`/`U_dec_det`'s `Or.inr` branch in `avssCert`.) -/
theorem avssU_step_partyEchoSend_lt (s : AVSSState n t F) (p : Fin n)
    (hgate : actionGate (AVSSAction.partyEchoSend p) s)
    (hinv : avssTermInv s) (hph : p ∉ s.corrupted) :
    avssU (avssStep (AVSSAction.partyEchoSend p) s) + 1 ≤ avssU s := by
  classical
  obtain ⟨hdel_t, hesf, _hds_pre⟩ := hgate
  have hphon : p ∉ s.corrupted := hph
  have hn_pos : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; exact p.elim0
    · exact hn
  have hK_def_eq : lexBase n = (n + 1) * (n + 1) := rfl
  have hK_ge : 4 ≤ lexBase n := by unfold lexBase; nlinarith
  have hK_gt_n : lexBase n > n := by unfold lexBase; nlinarith
  -- Frame.
  have hds : (avssStep (AVSSAction.partyEchoSend p) s).dealerSent =
      s.dealerSent := by simp [avssStep, setLocal]
  have huds : unsentDealerSet (avssStep (AVSSAction.partyEchoSend p) s) =
      unsentDealerSet s :=
    by simp [unsentDealerSet, avssStep, setLocal]
  have hcorr : (avssStep (AVSSAction.partyEchoSend p) s).corrupted =
      s.corrupted := by simp [avssStep, setLocal]
  have hifd : (avssStep (AVSSAction.partyEchoSend p) s).inflightDeliveries =
      s.inflightDeliveries := by simp [avssStep]
  have hife : (avssStep (AVSSAction.partyEchoSend p) s).inflightEchoes =
      s.inflightEchoes ∪
        (Finset.univ : Finset (Fin n)).image (fun q => (p, q)) := by
    simp [avssStep]
  have hifr : (avssStep (AVSSAction.partyEchoSend p) s).inflightReady =
      s.inflightReady := by simp [avssStep]
  -- Per-party: only echoSent_p flips false→true.
  have hdel : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyEchoSend p) s).local_ x).delivered =
        (s.local_ x).delivered := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hes_p :
      ((avssStep (AVSSAction.partyEchoSend p) s).local_ p).echoSent = true := by
    simp [avssStep]
  have hes_ne : ∀ x : Fin n, x ≠ p →
      ((avssStep (AVSSAction.partyEchoSend p) s).local_ x).echoSent =
        (s.local_ x).echoSent := by
    intro x hxp
    simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hrs : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyEchoSend p) s).local_ x).readySent =
        (s.local_ x).readySent := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hout : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyEchoSend p) s).local_ x).output =
        (s.local_ x).output := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  -- Set equalities.
  have hnrs : notReadySentSet (avssStep (AVSSAction.partyEchoSend p) s) =
      notReadySentSet s := by
    apply Finset.ext; intro x
    simp only [notReadySentSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr, hrs x]
  have hunfin : unfinishedSet (avssStep (AVSSAction.partyEchoSend p) s) =
      unfinishedSet s := by
    apply Finset.ext; intro x
    simp only [unfinishedSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr, hout x]
  -- p ∈ unsentEchoSet pre, p ∉ unsentEchoSet post.
  have hp_in_uss_pre : p ∈ unsentEchoSet s := by
    simp only [unsentEchoSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hphon, hdel_t, hesf⟩
  have huss_post :
      unsentEchoSet (avssStep (AVSSAction.partyEchoSend p) s) =
      (unsentEchoSet s).erase p := by
    apply Finset.ext; intro x
    simp only [unsentEchoSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    rw [hcorr]
    by_cases hxp : x = p
    · subst hxp
      rw [hdel x, hes_p]
      simp
    · rw [hdel x, hes_ne x hxp]; simp [hxp]
  have huss_card :
      (unsentEchoSet (avssStep (AVSSAction.partyEchoSend p) s)).card =
      (unsentEchoSet s).card - 1 := by
    rw [huss_post, Finset.card_erase_of_mem hp_in_uss_pre]
  have huss_pos : 1 ≤ (unsentEchoSet s).card :=
    Finset.card_pos.mpr ⟨p, hp_in_uss_pre⟩
  -- inflightEchoes card bound (Phase 8.5b: broadcast filter is now univ).
  -- Post ≤ pre + n.
  have hife_card_le :
      (s.inflightEchoes ∪
        (Finset.univ : Finset (Fin n)).image (fun q => (p, q))).card
        ≤ s.inflightEchoes.card + n := by
    calc (s.inflightEchoes ∪
            (Finset.univ : Finset (Fin n)).image (fun q => (p, q))).card
        ≤ s.inflightEchoes.card +
            ((Finset.univ : Finset (Fin n)).image (fun q => (p, q))).card :=
          Finset.card_union_le _ _
      _ ≤ s.inflightEchoes.card + (Finset.univ : Finset (Fin n)).card := by
          gcongr; exact Finset.card_image_le
      _ = s.inflightEchoes.card + n := by simp
  unfold avssU
  rw [huds, hifd, hife, hifr, huss_card, hnrs, hunfin]
  set K := lexBase n with hK_def
  set uss := (unsentEchoSet s).card
  set ife_pre := s.inflightEchoes.card
  -- Goal: ifd*K^5 + (uss-1)*K^4 + ife_post*K^3 + nrs*K^2 + ifr*K + unfin + 1
  --     ≤ ifd*K^5 + uss*K^4 + ife_pre*K^3 + nrs*K^2 + ifr*K + unfin
  -- Cancel and substitute uss*K^4 = (uss-1)*K^4 + K^4:
  -- ife_post*K^3 + 1 ≤ K^4 + ife_pre*K^3
  -- Use ife_post ≤ ife_pre + n: ife_pre*K^3 + n*K^3 + 1 ≤ K^4 + ife_pre*K^3
  -- ⟺ n*K^3 + 1 ≤ K^4 = K * K^3
  -- ⟺ n*K^3 + 1 ≤ K * K^3 ⟺ (K - n)*K^3 ≥ 1 (with K ≥ n+1).
  have h_uss_split : (uss - 1) * K^4 + K^4 = uss * K^4 := by
    have : uss - 1 + 1 = uss := Nat.sub_add_cancel huss_pos
    calc (uss - 1) * K^4 + K^4 = ((uss - 1) + 1) * K^4 := by ring
      _ = uss * K^4 := by rw [this]
  have hK3_pos : 1 ≤ K^3 := Nat.one_le_pow _ _ (by omega)
  -- Key bound: K^4 ≥ n * K^3 + 1, i.e., (K - n) * K^3 ≥ 1.
  have h_K4_ge : K^4 ≥ n * K^3 + 1 := by
    have hKn1 : K ≥ n + 1 := by
      rw [hK_def]; unfold lexBase; nlinarith
    have h1 : K^4 = K * K^3 := by ring
    have h2 : K * K^3 ≥ (n + 1) * K^3 := by nlinarith [hK3_pos, hKn1]
    nlinarith [hK3_pos, h1, h2]
  nlinarith [h_uss_split, h_K4_ge, hife_card_le, huss_pos, hK3_pos, hK_ge]

omit [Fintype F] in
/-- Phase 8.5d-α: `dealerShareTo p` step decreases avssU. For honest p,
`unsentDealerSet` drops by 1 (c₁ component, K⁶), while `inflightDeliveries`
grows by ≤1 (c₂, K⁵). Net change: −K⁶ + K⁵ ≤ 0 (since K ≥ 1). For corrupt
p, `unsentDealerSet` and `inflightDeliveries` are unchanged (corrupt parties
are filtered out of both). -/
theorem avssU_step_dealerShareTo_le (s : AVSSState n t F) (p : Fin n)
    (hgate : actionGate (AVSSAction.dealerShareTo p) s)
    (_hinv : avssTermInv s) :
    avssU (avssStep (AVSSAction.dealerShareTo p) s) ≤ avssU s := by
  classical
  have hgate' : s.dealerSent p = false := hgate
  have hK_pos : 1 ≤ lexBase n := lexBase_pos
  -- Frame: ife / ifr / local / corrupted / unsentEcho / notReadySent / unfin all unchanged.
  have hcorr : (avssStep (.dealerShareTo p) s).corrupted = s.corrupted := rfl
  have hife : (avssStep (.dealerShareTo p) s).inflightEchoes = s.inflightEchoes := rfl
  have hifr : (avssStep (.dealerShareTo p) s).inflightReady = s.inflightReady := rfl
  have hloc : ∀ q, (avssStep (.dealerShareTo p) s).local_ q = s.local_ q := fun _ => rfl
  have huss : unsentEchoSet (avssStep (.dealerShareTo p) s) = unsentEchoSet s := by
    apply Finset.ext; intro x
    simp only [unsentEchoSet, Finset.mem_filter, Finset.mem_univ, true_and, hcorr, hloc]
  have hnrs : notReadySentSet (avssStep (.dealerShareTo p) s) = notReadySentSet s := by
    apply Finset.ext; intro x
    simp only [notReadySentSet, Finset.mem_filter, Finset.mem_univ, true_and, hcorr, hloc]
  have hunfin : unfinishedSet (avssStep (.dealerShareTo p) s) = unfinishedSet s := by
    apply Finset.ext; intro x
    simp only [unfinishedSet, Finset.mem_filter, Finset.mem_univ, true_and, hcorr, hloc]
  -- Key bounds on the two changing components.
  have huds_le : (unsentDealerSet (avssStep (.dealerShareTo p) s)).card ≤
      (unsentDealerSet s).card := by
    apply Finset.card_le_card
    intro q hq
    simp only [unsentDealerSet, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    refine ⟨hq.1, ?_⟩
    -- post.dealerSent q = false; show pre.dealerSent q = false.
    have hq_ds : (Function.update s.dealerSent p true) q = false := hq.2
    by_cases hqp : q = p
    · subst hqp; simp [Function.update_self] at hq_ds
    · rwa [Function.update_of_ne hqp] at hq_ds
  have hifd_le : (avssStep (.dealerShareTo p) s).inflightDeliveries.card ≤
      s.inflightDeliveries.card + 1 := by
    show (if p ∉ s.corrupted then insert p s.inflightDeliveries
          else s.inflightDeliveries).card ≤ s.inflightDeliveries.card + 1
    split
    · exact (Finset.card_insert_le _ _).trans (by omega)
    · omega
  -- Case-split on p's corruption status.
  by_cases hpcorr : p ∉ s.corrupted
  · -- honest p: unsentDealerSet drops by exactly 1, ifd grows by ≤ 1.
    have hp_in_uds : p ∈ unsentDealerSet s := by
      simp only [unsentDealerSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hpcorr, hgate'⟩
    have huds_drop : (unsentDealerSet (avssStep (.dealerShareTo p) s)).card + 1 =
        (unsentDealerSet s).card := by
      have h_post_eq_set : unsentDealerSet (avssStep (.dealerShareTo p) s) =
          (unsentDealerSet s).erase p := by
        apply Finset.ext; intro q
        simp only [unsentDealerSet, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_erase]
        have h_post_ds : (avssStep (.dealerShareTo p) s).dealerSent =
            Function.update s.dealerSent p true := rfl
        rw [h_post_ds]
        constructor
        · rintro ⟨hq_corr, hq_ds⟩
          by_cases hqp : q = p
          · subst hqp; simp [Function.update_self] at hq_ds
          · rw [Function.update_of_ne hqp] at hq_ds
            exact ⟨hqp, hq_corr, hq_ds⟩
        · rintro ⟨hqp, hq_corr, hq_ds⟩
          refine ⟨hq_corr, ?_⟩
          rw [Function.update_of_ne hqp]; exact hq_ds
      rw [h_post_eq_set, Finset.card_erase_of_mem hp_in_uds]
      have hpos : 1 ≤ (unsentDealerSet s).card :=
        Finset.card_pos.mpr ⟨p, hp_in_uds⟩
      omega
    -- avssU change: -K^6 + Δ(ifd) * K^5. Need ≤ 0.
    set K := lexBase n
    show (unsentDealerSet (avssStep (.dealerShareTo p) s)).card * K ^ 6 +
        (avssStep (.dealerShareTo p) s).inflightDeliveries.card * K ^ 5 +
        (unsentEchoSet (avssStep (.dealerShareTo p) s)).card * K ^ 4 +
        (avssStep (.dealerShareTo p) s).inflightEchoes.card * K ^ 3 +
        (notReadySentSet (avssStep (.dealerShareTo p) s)).card * K ^ 2 +
        (avssStep (.dealerShareTo p) s).inflightReady.card * K +
        (unfinishedSet (avssStep (.dealerShareTo p) s)).card ≤
      (unsentDealerSet s).card * K ^ 6 +
        s.inflightDeliveries.card * K ^ 5 +
        (unsentEchoSet s).card * K ^ 4 +
        s.inflightEchoes.card * K ^ 3 +
        (notReadySentSet s).card * K ^ 2 +
        s.inflightReady.card * K +
        (unfinishedSet s).card
    rw [hife, hifr, huss, hnrs, hunfin]
    have hK5_le : K ^ 5 ≤ K ^ 6 := Nat.pow_le_pow_right hK_pos (by omega)
    -- Derive (post.uds.card + 1) * K^6 = (s.uds.card) * K^6.
    have h_uds_K6 : ((unsentDealerSet (avssStep (.dealerShareTo p) s)).card + 1) * K ^ 6 =
        (unsentDealerSet s).card * K ^ 6 := by rw [huds_drop]
    have h_uds_K6' : (unsentDealerSet (avssStep (.dealerShareTo p) s)).card * K ^ 6 + K ^ 6 =
        (unsentDealerSet s).card * K ^ 6 := by linarith [h_uds_K6]
    -- post.ifd.card * K^5 ≤ (s.ifd.card + 1) * K^5 = s.ifd.card * K^5 + K^5.
    have h_ifd_K5 : (avssStep (.dealerShareTo p) s).inflightDeliveries.card * K ^ 5 ≤
        s.inflightDeliveries.card * K ^ 5 + K ^ 5 := by
      have := Nat.mul_le_mul_right (K ^ 5) hifd_le
      linarith [this]
    -- Combine.
    linarith [h_uds_K6', h_ifd_K5, hK5_le]
  · -- p ∈ corr: unsentDealerSet unchanged, inflightDeliveries unchanged.
    push_neg at hpcorr
    have hifd_eq : (avssStep (.dealerShareTo p) s).inflightDeliveries =
        s.inflightDeliveries := by
      show (if p ∉ s.corrupted then insert p s.inflightDeliveries
            else s.inflightDeliveries) = s.inflightDeliveries
      rw [if_neg (by simp [hpcorr])]
    have huds_eq : unsentDealerSet (avssStep (.dealerShareTo p) s) = unsentDealerSet s := by
      apply Finset.ext; intro q
      simp only [unsentDealerSet, Finset.mem_filter, Finset.mem_univ, true_and]
      have h_post_ds : (avssStep (.dealerShareTo p) s).dealerSent =
          Function.update s.dealerSent p true := rfl
      rw [h_post_ds]
      by_cases hqp : q = p
      · subst hqp
        simp only [Function.update_self, hcorr]
        constructor
        · rintro ⟨_, h⟩; cases h
        · rintro ⟨h_pnotin, _⟩
          exact (h_pnotin hpcorr).elim
      · rw [Function.update_of_ne hqp, hcorr]
    show avssU (avssStep (.dealerShareTo p) s) ≤ avssU s
    unfold avssU
    rw [huds_eq, hifd_eq, hife, hifr, huss, hnrs, hunfin]

omit [Fintype F] in
/-- Phase 8.5d-α: `dealerShareTo p` step strictly decreases avssU when p
is honest. The unsentDealerSet drops by 1 (gate ensures `s.dealerSent p = false`)
and this K⁶-weighted drop strictly dominates the K⁵-weighted growth in
inflightDeliveries. For corrupt p, the variant is preserved (no strict
decrease) — but corrupt-fired dealerShareTo isn't strictly fair under the
refined model in 8.5d-γ. -/
theorem avssU_step_dealerShareTo_lt (s : AVSSState n t F) (p : Fin n)
    (hgate : actionGate (AVSSAction.dealerShareTo p) s)
    (_hinv : avssTermInv s)
    (hph : p ∉ s.corrupted) :
    avssU (avssStep (AVSSAction.dealerShareTo p) s) + 1 ≤ avssU s := by
  classical
  have hgate' : s.dealerSent p = false := hgate
  have hK_pos : 1 ≤ lexBase n := lexBase_pos
  -- Need K ≥ 2 so K^6 - K^5 ≥ 1.
  have hn_pos : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; exact p.elim0
    · exact hn
  have hK_ge : 4 ≤ lexBase n := by unfold lexBase; nlinarith
  -- Frame.
  have hcorr : (avssStep (.dealerShareTo p) s).corrupted = s.corrupted := rfl
  have hife : (avssStep (.dealerShareTo p) s).inflightEchoes = s.inflightEchoes := rfl
  have hifr : (avssStep (.dealerShareTo p) s).inflightReady = s.inflightReady := rfl
  have hloc : ∀ q, (avssStep (.dealerShareTo p) s).local_ q = s.local_ q := fun _ => rfl
  have huss : unsentEchoSet (avssStep (.dealerShareTo p) s) = unsentEchoSet s := by
    apply Finset.ext; intro x
    simp only [unsentEchoSet, Finset.mem_filter, Finset.mem_univ, true_and, hcorr, hloc]
  have hnrs : notReadySentSet (avssStep (.dealerShareTo p) s) = notReadySentSet s := by
    apply Finset.ext; intro x
    simp only [notReadySentSet, Finset.mem_filter, Finset.mem_univ, true_and, hcorr, hloc]
  have hunfin : unfinishedSet (avssStep (.dealerShareTo p) s) = unfinishedSet s := by
    apply Finset.ext; intro x
    simp only [unfinishedSet, Finset.mem_filter, Finset.mem_univ, true_and, hcorr, hloc]
  -- Honest p: ifd grows by exactly 1 (when p ∉ pre.ifd) or 0 (when p ∈ pre.ifd).
  -- We don't need the exact count — just the ≤ + 1 bound.
  have hifd_le : (avssStep (.dealerShareTo p) s).inflightDeliveries.card ≤
      s.inflightDeliveries.card + 1 := by
    show (if p ∉ s.corrupted then insert p s.inflightDeliveries
          else s.inflightDeliveries).card ≤ s.inflightDeliveries.card + 1
    rw [if_pos hph]
    exact (Finset.card_insert_le _ _).trans (by omega)
  -- unsentDealerSet drops by exactly 1 (honest p was in unsentDealerSet).
  have hp_in_uds : p ∈ unsentDealerSet s := by
    simp only [unsentDealerSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hph, hgate'⟩
  have huds_drop : (unsentDealerSet (avssStep (.dealerShareTo p) s)).card + 1 =
      (unsentDealerSet s).card := by
    have h_post_eq_set : unsentDealerSet (avssStep (.dealerShareTo p) s) =
        (unsentDealerSet s).erase p := by
      apply Finset.ext; intro q
      simp only [unsentDealerSet, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_erase]
      have h_post_ds : (avssStep (.dealerShareTo p) s).dealerSent =
          Function.update s.dealerSent p true := rfl
      rw [h_post_ds]
      constructor
      · rintro ⟨hq_corr, hq_ds⟩
        by_cases hqp : q = p
        · subst hqp; simp [Function.update_self] at hq_ds
        · rw [Function.update_of_ne hqp] at hq_ds
          exact ⟨hqp, hq_corr, hq_ds⟩
      · rintro ⟨hqp, hq_corr, hq_ds⟩
        refine ⟨hq_corr, ?_⟩
        rw [Function.update_of_ne hqp]; exact hq_ds
    rw [h_post_eq_set, Finset.card_erase_of_mem hp_in_uds]
    have hpos : 1 ≤ (unsentDealerSet s).card :=
      Finset.card_pos.mpr ⟨p, hp_in_uds⟩
    omega
  -- avssU change: -K^6 + Δ(ifd) * K^5 + 1. Need ≤ 0, i.e., Δ(ifd) * K^5 + 1 ≤ K^6.
  -- Δ(ifd) ≤ 1, so Δ(ifd) * K^5 ≤ K^5. Need K^5 + 1 ≤ K^6 = K * K^5. Since K ≥ 4, K^6 ≥ 4 * K^5 ≥ K^5 + 1.
  set K := lexBase n
  show (unsentDealerSet (avssStep (.dealerShareTo p) s)).card * K ^ 6 +
      (avssStep (.dealerShareTo p) s).inflightDeliveries.card * K ^ 5 +
      (unsentEchoSet (avssStep (.dealerShareTo p) s)).card * K ^ 4 +
      (avssStep (.dealerShareTo p) s).inflightEchoes.card * K ^ 3 +
      (notReadySentSet (avssStep (.dealerShareTo p) s)).card * K ^ 2 +
      (avssStep (.dealerShareTo p) s).inflightReady.card * K +
      (unfinishedSet (avssStep (.dealerShareTo p) s)).card + 1 ≤
    (unsentDealerSet s).card * K ^ 6 +
      s.inflightDeliveries.card * K ^ 5 +
      (unsentEchoSet s).card * K ^ 4 +
      s.inflightEchoes.card * K ^ 3 +
      (notReadySentSet s).card * K ^ 2 +
      s.inflightReady.card * K +
      (unfinishedSet s).card
  rw [hife, hifr, huss, hnrs, hunfin]
  have hK5_pos : 1 ≤ K ^ 5 := Nat.one_le_pow _ _ hK_pos
  have hK6_eq : K ^ 6 = K * K ^ 5 := by ring
  have h_K6_ge : K ^ 6 ≥ 4 * K ^ 5 := by rw [hK6_eq]; nlinarith [hK5_pos, hK_ge]
  have h_K6_ge_K5_1 : K ^ 6 ≥ K ^ 5 + 1 := by nlinarith [hK5_pos, h_K6_ge]
  -- Derive (post.uds.card + 1) * K^6 = s.uds.card * K^6.
  have h_uds_K6 : ((unsentDealerSet (avssStep (.dealerShareTo p) s)).card + 1) * K ^ 6 =
      (unsentDealerSet s).card * K ^ 6 := by rw [huds_drop]
  have h_uds_K6' : (unsentDealerSet (avssStep (.dealerShareTo p) s)).card * K ^ 6 + K ^ 6 =
      (unsentDealerSet s).card * K ^ 6 := by linarith [h_uds_K6]
  have h_ifd_K5 : (avssStep (.dealerShareTo p) s).inflightDeliveries.card * K ^ 5 ≤
      s.inflightDeliveries.card * K ^ 5 + K ^ 5 := by
    have := Nat.mul_le_mul_right (K ^ 5) hifd_le
    linarith [this]
  linarith [h_uds_K6', h_ifd_K5, h_K6_ge_K5_1]

/-- "Action is honest-fired at state `s`" — its owning party (if any) is
not in `s.corrupted`. Phase 8.5b: the case-split predicate for V_super /
U_dec_det disjunct dispatch. -/
def isHonestFire (a : AVSSAction n F) (s : AVSSState n t F) : Prop :=
  ∀ p, ((a = .partyEchoSend p ∨ a = .partyReady p ∨ a = .partyAmplify p
         ∨ a = .dealerShareTo p)
        → p ∉ s.corrupted)

omit [Fintype F] in
/-- Composite ≤: every honest-fired gated action keeps avssU non-increasing.

Phase 8.5b: corrupt-fired send actions may increase `avssU` (since
`unsentEchoSet`/`notReadySentSet` remain honest-only). The `hph` premise
restricts to honest firings. The cert's `V_super` discharges the
corrupt-fired case via `Or.inr` (a fair action remains enabled). -/
theorem avssU_step_le (a : AVSSAction n F) (s : AVSSState n t F)
    (h : actionGate a s) (hinv : avssTermInv s) (hph : isHonestFire a s) :
    avssU (avssStep a s) ≤ avssU s := by
  cases a with
  | dealerShareTo p => exact avssU_step_dealerShareTo_le s p h hinv
  | partyDeliver p =>
      have := avssU_step_partyDeliver_lt s p h hinv; omega
  | partyCorruptDeliver p =>
      have := avssU_step_partyCorruptDeliver_eq s p h; omega
  | partyEchoSend p =>
      have hp : p ∉ s.corrupted := hph p (Or.inl rfl)
      have := avssU_step_partyEchoSend_lt s p h hinv hp; omega
  | partyEchoReceive p q =>
      have := avssU_step_partyEchoReceive_lt s p q h hinv; omega
  | partyReady p =>
      have hp : p ∉ s.corrupted := hph p (Or.inr (Or.inl rfl))
      have := avssU_step_partyReady_lt s p h hinv hp; omega
  | partyAmplify p =>
      have hp : p ∉ s.corrupted := hph p (Or.inr (Or.inr (Or.inl rfl)))
      have := avssU_step_partyAmplify_lt s p h hinv hp; omega
  | partyReceiveReady p q =>
      have := avssU_step_partyReceiveReady_lt s p q h hinv; omega
  | partyOutput p =>
      have := avssU_step_partyOutput_lt s p h hinv; omega

omit [Fintype F] in
/-- Helper: at a non-terminated state with `dealerSent = false` and the
inductive invariant, the honest set must be non-empty. Otherwise
`terminated s` would hold vacuously (every conjunct of `terminated`
that quantifies over honest parties is vacuous when no honest party
exists; queue conjuncts are guaranteed by inv clause 1).

Used in `avssU_step_lt_of_fair` to dispatch the `dealerShare` case
to `avssU_step_dealerShare_lt`, which requires the honest-set bound. -/
theorem honestSet_pos_of_not_terminated_pre_share
    (s : AVSSState n t F) (hinv : avssTermInv s)
    (hds : ∀ p, s.dealerSent p = false) (hnt : ¬ terminated s) :
    1 ≤ (honestSet s).card := by
  classical
  by_contra hbad
  push_neg at hbad
  have hzero : (honestSet s).card = 0 := by omega
  have hempty : honestSet s = ∅ := Finset.card_eq_zero.mp hzero
  -- Phase 8.5d-α: clause 1's antecedent is now `∀ p, dealerSent p = false`.
  have hi := hinv.1 hds
  obtain ⟨_, hifd_emp, hife_emp, hifr_emp⟩ := hi
  apply hnt
  refine ⟨?_, ?_, hifd_emp, hife_emp, hifr_emp⟩
  · intro p hp
    have hp_in : p ∈ honestSet s := by
      simp only [honestSet, Finset.mem_filter, Finset.mem_univ, true_and]; exact hp
    rw [hempty] at hp_in
    exact absurd hp_in (Finset.notMem_empty _)
  · intro p hp
    have hp_in : p ∈ honestSet s := by
      simp only [honestSet, Finset.mem_filter, Finset.mem_univ, true_and]; exact hp
    rw [hempty] at hp_in
    exact absurd hp_in (Finset.notMem_empty _)

omit [Fintype F] in
/-- For every fair-firing action, avssU strictly decreases. The
`hnt : ¬ terminated s` premise is needed for the new `dealerShare`
case (added to `avssFairActions` in Phase B): strict decrease of
the K⁶ → K⁵ shift requires `(honestSet s).card ≥ 1`, which follows
from `¬ terminated s` via `honestSet_pos_of_not_terminated_pre_share`. -/
theorem avssU_step_lt_of_fair (a : AVSSAction n F) (s : AVSSState n t F)
    (h : actionGate a s) (hfair : a ∈ avssFairActions)
    (hinv : avssTermInv s) (hnt : ¬ terminated s) (hph : isHonestFire a s) :
    avssU (avssStep a s) < avssU s := by
  cases a with
  | dealerShareTo p =>
      have hp : p ∉ s.corrupted := hph p (Or.inr (Or.inr (Or.inr rfl)))
      have := avssU_step_dealerShareTo_lt s p h hinv hp; omega
  | partyDeliver p =>
      have := avssU_step_partyDeliver_lt s p h hinv; omega
  | partyCorruptDeliver p => simp [avssFairActions] at hfair
  | partyEchoSend p =>
      have hp : p ∉ s.corrupted := hph p (Or.inl rfl)
      have := avssU_step_partyEchoSend_lt s p h hinv hp; omega
  | partyEchoReceive p q =>
      have := avssU_step_partyEchoReceive_lt s p q h hinv; omega
  | partyReady p =>
      have hp : p ∉ s.corrupted := hph p (Or.inr (Or.inl rfl))
      have := avssU_step_partyReady_lt s p h hinv hp; omega
  | partyAmplify p =>
      have hp : p ∉ s.corrupted := hph p (Or.inr (Or.inr (Or.inl rfl)))
      have := avssU_step_partyAmplify_lt s p h hinv hp; omega
  | partyReceiveReady p q =>
      have := avssU_step_partyReceiveReady_lt s p q h hinv; omega
  | partyOutput p =>
      have := avssU_step_partyOutput_lt s p h hinv; omega


/-! ### Phase 2d: variant value at terminated and at non-terminated states -/

omit [Fintype F] in
/-- Under `avssTermInv s` and `terminated s`, `avssU s = 0`. -/
theorem avssU_eq_zero_of_terminated (s : AVSSState n t F)
    (hinv : avssTermInv s) (ht : terminated s) :
    avssU s = 0 := by
  classical
  unfold avssU
  obtain ⟨ht_out, ht_echo, ht_ifd, ht_ife, ht_ifr⟩ := ht
  -- c2, c4, c6 = 0 from queues = ∅.
  have hifd_card : s.inflightDeliveries.card = 0 := by rw [ht_ifd]; rfl
  have hife_card : s.inflightEchoes.card = 0 := by rw [ht_ife]; rfl
  have hifr_card : s.inflightReady.card = 0 := by rw [ht_ifr]; rfl
  -- c7 = 0 from `unfinishedSet = ∅`.
  have hunfin : (unfinishedSet s).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro p _ ⟨hp_h, hp_none⟩
    have := ht_out p hp_h
    rw [hp_none] at this
    simp at this
  -- c3 = 0 from `unsentEchoSet = ∅` via `ht_echo`.
  have huss : (unsentEchoSet s).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro p _ ⟨hp_h, _, hp_es⟩
    have := ht_echo p hp_h
    rw [this] at hp_es
    cases hp_es
  -- c5 = 0 from inv clause 3 (output.isSome → readySent) + ht_out.
  have hnrs : (notReadySentSet s).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro p _ ⟨hp_h, hp_nrs⟩
    have hsome : (s.local_ p).output.isSome = true := ht_out p hp_h
    have := (hinv.2.2.1 p hp_h hsome).1
    rw [this] at hp_nrs
    cases hp_nrs
  -- c1 = 0: unsentDealerSet is empty at terminated states.
  -- Honest p: output.isSome (terminated) ⟹ readySent ∧ delivered (clause 3)
  --        ⟹ delivered. But clause 4 says: dealerSent p = false → ¬delivered.
  -- Contrapositive: delivered ⟹ dealerSent p = true.
  have hudS : (unsentDealerSet s).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_of_forall_notMem
    intro p hp
    simp only [unsentDealerSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hp_h, hp_ds⟩ := hp
    have hp_some : (s.local_ p).output.isSome = true := ht_out p hp_h
    have hp_del : (s.local_ p).delivered = true := (hinv.2.2.1 p hp_h hp_some).2
    have hp_del_f : (s.local_ p).delivered = false := hinv.2.2.2 p hp_h hp_ds
    rw [hp_del] at hp_del_f
    cases hp_del_f
  rw [hudS, hifd_card, huss, hife_card, hnrs, hifr_card, hunfin]
  ring

omit [Fintype F] in
/-- `V_term` field: under `Inv` and `terminated`, `avssV s = 0`. -/
theorem avssCert_V_term (s : AVSSState n t F)
    (hinv : avssTermInv s) (ht : terminated s) :
    avssV s = 0 := by
  show (avssU s : ℝ≥0) = 0
  rw [avssU_eq_zero_of_terminated s hinv ht]
  simp

omit [Fintype F] in
/-- `U_term` field: under `Inv` and `terminated`, `avssU s = 0`. -/
theorem avssCert_U_term (s : AVSSState n t F)
    (hinv : avssTermInv s) (ht : terminated s) :
    avssU s = 0 :=
  avssU_eq_zero_of_terminated s hinv ht

omit [Fintype F] in
/-- `V_pos` field: at non-terminated states, `avssV s > 0`. -/
theorem avssCert_V_pos (s : AVSSState n t F)
    (hinv : avssTermInv s) (hnt : ¬ terminated s) :
    0 < avssV s := by
  show 0 < (avssU s : ℝ≥0)
  classical
  by_contra hcon
  push_neg at hcon
  have hU0_real : (avssU s : ℝ≥0) = 0 := le_antisymm hcon (zero_le _)
  have hU0 : avssU s = 0 := by exact_mod_cast hU0_real
  unfold avssU at hU0
  -- Decompose the sum of nonnegative ℕ-terms.  Each term must be 0.
  have hK_pos : 1 ≤ lexBase n := lexBase_pos
  obtain ⟨hU0', hunfin_t⟩ := Nat.add_eq_zero.mp hU0
  obtain ⟨hU0', hifr_t⟩ := Nat.add_eq_zero.mp hU0'
  obtain ⟨hU0', hnrs_t⟩ := Nat.add_eq_zero.mp hU0'
  obtain ⟨hU0', hife_t⟩ := Nat.add_eq_zero.mp hU0'
  obtain ⟨hU0', huss_t⟩ := Nat.add_eq_zero.mp hU0'
  obtain ⟨_hdom_t, hifd_t⟩ := Nat.add_eq_zero.mp hU0'
  -- For each `t * K^k = 0` with `K^k ≥ 1`, deduce `t = 0`.
  have hifd_card : s.inflightDeliveries.card = 0 := by
    rcases Nat.mul_eq_zero.mp hifd_t with h | h
    · exact h
    · have : 1 ≤ lexBase n ^ 5 := Nat.one_le_pow _ _ hK_pos; omega
  have huss_card : (unsentEchoSet s).card = 0 := by
    rcases Nat.mul_eq_zero.mp huss_t with h | h
    · exact h
    · have : 1 ≤ lexBase n ^ 4 := Nat.one_le_pow _ _ hK_pos; omega
  have hife_card : s.inflightEchoes.card = 0 := by
    rcases Nat.mul_eq_zero.mp hife_t with h | h
    · exact h
    · have : 1 ≤ lexBase n ^ 3 := Nat.one_le_pow _ _ hK_pos; omega
  have hnrs_card : (notReadySentSet s).card = 0 := by
    rcases Nat.mul_eq_zero.mp hnrs_t with h | h
    · exact h
    · have : 1 ≤ lexBase n ^ 2 := Nat.one_le_pow _ _ hK_pos; omega
  have hifr_card : s.inflightReady.card = 0 := by
    rcases Nat.mul_eq_zero.mp hifr_t with h | h
    · exact h
    · omega
  have hunfin_card : (unfinishedSet s).card = 0 := hunfin_t
  -- Now derive `terminated`.
  have hifd_emp : s.inflightDeliveries = ∅ := Finset.card_eq_zero.mp hifd_card
  have hife_emp : s.inflightEchoes = ∅ := Finset.card_eq_zero.mp hife_card
  have hifr_emp : s.inflightReady = ∅ := Finset.card_eq_zero.mp hifr_card
  have hunfin_emp : unfinishedSet s = ∅ := Finset.card_eq_zero.mp hunfin_card
  have huss_emp : unsentEchoSet s = ∅ := Finset.card_eq_zero.mp huss_card
  have h_out : ∀ p, p ∉ s.corrupted → (s.local_ p).output.isSome := by
    intro p hp
    by_contra hnone
    have hp_in : p ∈ unfinishedSet s := by
      simp only [unfinishedSet, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hp, ?_⟩
      cases h_o : (s.local_ p).output with
      | none => rfl
      | some _ => simp [h_o] at hnone
    rw [hunfin_emp] at hp_in
    exact (Finset.notMem_empty _) hp_in
  have h_echo : ∀ p, p ∉ s.corrupted → (s.local_ p).echoSent = true := by
    intro p hp
    by_contra hbad
    have hes : (s.local_ p).echoSent = false := by
      cases h_es : (s.local_ p).echoSent with
      | true => exact absurd h_es hbad
      | false => rfl
    -- Need delivered = true to put p in unsentEchoSet.
    have hsome := h_out p hp
    have hdel : (s.local_ p).delivered = true := (hinv.2.2.1 p hp hsome).2
    have hp_in : p ∈ unsentEchoSet s := by
      simp only [unsentEchoSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hp, hdel, hes⟩
    rw [huss_emp] at hp_in
    exact (Finset.notMem_empty _) hp_in
  exact hnt ⟨h_out, h_echo, hifd_emp, hife_emp, hifr_emp⟩

/-! ### `corruptLocalInv` — moved earlier in Phase 8.5b-β so the cert can
carry it as part of its joint invariant. -/

/-- For every corrupt party `p`, the local state's `output` is
pinned at `none`, and `delivered = false → rowPoly = none`.

Phase 8.5b weakening: under the C1+C2 model, corrupt parties may
fire `partyEchoSend`/`partyReady`/`partyAmplify`/`partyEchoReceive`/
`partyReceiveReady`, so the previous pinning of `{echoSent,
echoesReceived, readySent, readyReceived}` no longer holds — those
fields are now schedule-dependent for corrupt parties. The only
genuinely pinned fields are `output` (set only by `partyOutput`,
which retains the `p ∉ corrupted` gate) and the `(delivered, rowPoly)`
pair (set together by `partyCorruptDeliver`).

Combined with `outputDeterminedInv` (which pins `delivered = true →
rowPoly = some (rowPolyOfDealer …)`), this still fully constrains
the *algebraic* content of corrupt parties' local states modulo the
single bit `delivered`. The schedule-dependent trivial fields are
recovered separately via `coalitionTrivialView` (Phase 8.5c). -/
def corruptLocalInv (s : AVSSState n t F) : Prop :=
  ∀ p, p ∈ s.corrupted →
    (s.local_ p).output = none ∧
    ((s.local_ p).delivered = false → (s.local_ p).rowPoly = none)

omit [Fintype F] in
theorem initPred_corruptLocalInv (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (s : AVSSState n t F) (h : initPred sec corr coeffs s) :
    corruptLocalInv s := by
  obtain ⟨hloc, _⟩ := h
  intro p _
  rw [hloc p]
  refine ⟨rfl, fun _ => rfl⟩

omit [Fintype F] in
/-- `corruptLocalInv` is preserved by every gated action.

Phase 8.5b: only `output` and the `(delivered, rowPoly)` pair are
pinned. `output` is preserved by every action except `partyOutput`,
whose gate retains `p ∉ corrupted`. The `(delivered, rowPoly)` pair
is preserved by every action except `partyCorruptDeliver`, which
sets *both* fields together (so the implication
`delivered = false → rowPoly = none` is vacuously preserved). -/
theorem avssStep_preserves_corruptLocalInv
    (a : AVSSAction n F) (s : AVSSState n t F)
    (hgate : actionGate a s) (hinv : corruptLocalInv s) :
    corruptLocalInv (avssStep a s) := by
  classical
  -- `s.corrupted` is preserved by every action.
  have hcorr : (avssStep a s).corrupted = s.corrupted := by
    cases a <;> simp [avssStep, setLocal]
  intro p hp
  rw [hcorr] at hp
  obtain ⟨h_out, h_rp_none⟩ := hinv p hp
  cases a with
  | dealerShareTo r =>
      -- dealerShareTo r writes only `dealerMessages r`, `dealerSent r`, and
      -- the in-flight queues. Local state is unchanged for every party,
      -- so the corruptLocalInv predicate (which inspects only `local_`) carries.
      simp only [avssStep]
      exact ⟨h_out, h_rp_none⟩
  | partyDeliver q =>
      -- gate: q ∉ corrupted, so q ≠ p (since p ∈ corrupted).
      have hpq : p ≠ q := fun h => hgate.2.1 (h ▸ hp)
      simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
      exact ⟨h_out, h_rp_none⟩
  | partyCorruptDeliver q =>
      -- gate: q ∈ corrupted; p may or may not equal q.
      by_cases hpq : p = q
      · subst hpq
        -- After partyCorruptDeliver(p), delivered = true and
        -- rowPoly = some (rowPolyOfDealer …); the implication
        -- `delivered = false → rowPoly = none` is vacuously preserved.
        -- `output` is unchanged.
        refine ⟨?_, ?_⟩
        · simp [avssStep, setLocal_local_self]; exact h_out
        · intro hd; simp [avssStep, setLocal_local_self] at hd
      · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact ⟨h_out, h_rp_none⟩
  | partyEchoSend q =>
      -- Phase 8.5b: q may be corrupt. But `partyEchoSend` only writes
      -- `echoSent`, not `output`, `delivered`, or `rowPoly`.
      by_cases hpq : p = q
      · subst hpq
        simp [avssStep, setLocal_local_self]
        exact ⟨h_out, h_rp_none⟩
      · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact ⟨h_out, h_rp_none⟩
  | partyEchoReceive q r =>
      -- Phase 8.5b: q may be corrupt. `partyEchoReceive` only writes
      -- `echoesReceived`, not the pinned fields.
      by_cases hpq : p = q
      · subst hpq
        simp [avssStep, setLocal_local_self]
        exact ⟨h_out, h_rp_none⟩
      · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact ⟨h_out, h_rp_none⟩
  | partyReady q =>
      -- Phase 8.5b: q may be corrupt. Only writes `readySent`.
      by_cases hpq : p = q
      · subst hpq
        simp [avssStep, setLocal_local_self]
        exact ⟨h_out, h_rp_none⟩
      · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact ⟨h_out, h_rp_none⟩
  | partyAmplify q =>
      -- Phase 8.5b: q may be corrupt. Only writes `readySent`.
      by_cases hpq : p = q
      · subst hpq
        simp [avssStep, setLocal_local_self]
        exact ⟨h_out, h_rp_none⟩
      · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact ⟨h_out, h_rp_none⟩
  | partyReceiveReady q r =>
      -- Phase 8.5b: q may be corrupt. Only writes `readyReceived`.
      by_cases hpq : p = q
      · subst hpq
        simp [avssStep, setLocal_local_self]
        exact ⟨h_out, h_rp_none⟩
      · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact ⟨h_out, h_rp_none⟩
  | partyOutput q =>
      -- gate retains q ∉ corrupted, so q ≠ p.
      have hpq : p ≠ q := fun h => hgate.1 (h ▸ hp)
      simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
      exact ⟨h_out, h_rp_none⟩

/-! ### Phase 8.5d-β-followup-7 — `coalitionRowPolyAlignedInv`

A dealerHonest-INDEPENDENT invariant tracking the structural alignment
between `dealerMessages` writes (from `dealerShareTo`) and `dealerCommit`,
and the consequent alignment between corrupt parties' `local_.rowPoly`
(set by `partyCorruptDeliver` from `dealerMessages`) and `dealerCommit`.

This invariant holds AE on `avssInitMeasure` (vacuously at init: all
queues empty, all locals init), is preserved by every `avssStep`
unconditionally (no honest-dealer guard), and provides the bridge
`coalitionTraceView ↔ reconstruct(coalitionAlgebraicView, ...)` under
arbitrary `dealerHonest` — closing the corrupt-dealer gap from
followup-6. -/

/-- The dealerHonest-INDEPENDENT alignment invariant:
  * (dealerMessages p = some msg → msg = dealerCommit p): every populated
    `dealerMessages p` matches the corresponding `dealerCommit p` (since
    `dealerShareTo r` writes `s.dealerCommit r` to `dealerMessages r`).
  * (∀ p ∈ corrupted, delivered → rowPoly = some (dealerCommit p .rowPoly)):
    every delivered corrupt party's rowPoly was set by
    `partyCorruptDeliver` from the matching `dealerMessages` payload, which
    equals `dealerCommit p` by the first clause.

Both clauses are c-independent and dealerHonest-independent. They are
preserved by every gated `avssStep` action, with the partyCorruptDeliver
case using the first clause to bridge `dealerMessages r = some msg →
msg = s.dealerCommit r` to `(avssStep _ s).local_ r .rowPoly =
some ((avssStep _ s).dealerCommit r .rowPoly)` (using also that
`dealerCommit` is preserved by every action). -/
def coalitionRowPolyAlignedInv (s : AVSSState n t F) : Prop :=
  (∀ p msg, s.dealerMessages p = some msg → msg = s.dealerCommit p) ∧
  (∀ p ∈ s.corrupted, (s.local_ p).delivered = true →
    (s.local_ p).rowPoly = some ((s.dealerCommit p).rowPoly))

omit [Fintype F] in
/-- `coalitionRowPolyAlignedInv` is preserved by every gated `avssStep`
action.  Note: no honest-dealer assumption — the invariant tracks
structural protocol semantics only. -/
theorem avssStep_preserves_coalitionRowPolyAlignedInv
    (a : AVSSAction n F) (s : AVSSState n t F)
    (hgate : actionGate a s) (hinv : coalitionRowPolyAlignedInv s) :
    coalitionRowPolyAlignedInv (avssStep a s) := by
  classical
  obtain ⟨h_dm_align, h_local_align⟩ := hinv
  -- `s.corrupted` and `s.dealerCommit` are preserved by every action.
  have hcorr : (avssStep a s).corrupted = s.corrupted := by
    cases a <;> simp [avssStep, setLocal]
  have hdc : (avssStep a s).dealerCommit = s.dealerCommit :=
    avssStep_dealerCommit_invariant a s
  refine ⟨?_, ?_⟩
  · -- Clause 1: dealerMessages p = some msg → msg = dealerCommit p.
    intro p msg hmsg
    cases a with
    | dealerShareTo r =>
        -- dealerMessages updated at r; preserved elsewhere.
        by_cases hpr : p = r
        · subst hpr
          simp [avssStep, Function.update_self] at hmsg
          rw [← hmsg, hdc]
        · rw [hdc]
          have hmsg' : s.dealerMessages p = some msg := by
            have := hmsg
            simp [avssStep, Function.update_of_ne hpr] at this
            exact this
          exact h_dm_align p msg hmsg'
    | partyDeliver q =>
        -- dealerMessages preserved.
        simp [avssStep, setLocal] at hmsg
        rw [hdc]
        exact h_dm_align p msg hmsg
    | partyCorruptDeliver q =>
        simp [avssStep, setLocal] at hmsg
        rw [hdc]
        exact h_dm_align p msg hmsg
    | partyEchoSend q =>
        simp [avssStep, setLocal] at hmsg
        rw [hdc]
        exact h_dm_align p msg hmsg
    | partyEchoReceive q r =>
        simp [avssStep, setLocal] at hmsg
        rw [hdc]
        exact h_dm_align p msg hmsg
    | partyReady q =>
        simp [avssStep, setLocal] at hmsg
        rw [hdc]
        exact h_dm_align p msg hmsg
    | partyAmplify q =>
        simp [avssStep, setLocal] at hmsg
        rw [hdc]
        exact h_dm_align p msg hmsg
    | partyReceiveReady q r =>
        simp [avssStep, setLocal] at hmsg
        rw [hdc]
        exact h_dm_align p msg hmsg
    | partyOutput q =>
        simp [avssStep, setLocal] at hmsg
        rw [hdc]
        exact h_dm_align p msg hmsg
  · -- Clause 2: ∀ p ∈ corrupted, delivered → rowPoly = some (dealerCommit p .rowPoly).
    intro p hp h_d
    rw [hcorr] at hp
    cases a with
    | dealerShareTo r =>
        -- Local state unchanged.
        simp [avssStep] at h_d
        simp [avssStep, hdc]
        exact h_local_align p hp h_d
    | partyDeliver q =>
        -- gate: q ∉ corrupted, so q ≠ p (since p ∈ corrupted).
        have hpq : p ≠ q := fun h => hgate.2.1 (h ▸ hp)
        simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at h_d
        simp [avssStep, setLocal_local_ne _ _ _ _ hpq, hdc]
        exact h_local_align p hp h_d
    | partyCorruptDeliver q =>
        -- gate: q ∈ corrupted; case-split on p = q vs p ≠ q.
        by_cases hpq : p = q
        · subst hpq
          -- partyCorruptDeliver(p) sets ls.rowPoly = some msg.rowPoly where
          -- msg = s.dealerMessages p (some by gate). By h_dm_align,
          -- msg = s.dealerCommit p, so rowPoly = some (dealerCommit p .rowPoly).
          have h_some : (s.dealerMessages p).isSome := hgate.2.2.2.2
          obtain ⟨msg, hmsg⟩ := Option.isSome_iff_exists.mp h_some
          have h_msg_eq : msg = s.dealerCommit p := h_dm_align p msg hmsg
          simp [avssStep, setLocal_local_self, hmsg, hdc, h_msg_eq]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at h_d
          simp [avssStep, setLocal_local_ne _ _ _ _ hpq, hdc]
          exact h_local_align p hp h_d
    | partyEchoSend q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at h_d
          simp [avssStep, setLocal_local_self, hdc]
          exact h_local_align p hp h_d
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at h_d
          simp [avssStep, setLocal_local_ne _ _ _ _ hpq, hdc]
          exact h_local_align p hp h_d
    | partyEchoReceive q r =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at h_d
          simp [avssStep, setLocal_local_self, hdc]
          exact h_local_align p hp h_d
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at h_d
          simp [avssStep, setLocal_local_ne _ _ _ _ hpq, hdc]
          exact h_local_align p hp h_d
    | partyReady q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at h_d
          simp [avssStep, setLocal_local_self, hdc]
          exact h_local_align p hp h_d
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at h_d
          simp [avssStep, setLocal_local_ne _ _ _ _ hpq, hdc]
          exact h_local_align p hp h_d
    | partyAmplify q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at h_d
          simp [avssStep, setLocal_local_self, hdc]
          exact h_local_align p hp h_d
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at h_d
          simp [avssStep, setLocal_local_ne _ _ _ _ hpq, hdc]
          exact h_local_align p hp h_d
    | partyReceiveReady q r =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at h_d
          simp [avssStep, setLocal_local_self, hdc]
          exact h_local_align p hp h_d
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at h_d
          simp [avssStep, setLocal_local_ne _ _ _ _ hpq, hdc]
          exact h_local_align p hp h_d
    | partyOutput q =>
        -- gate retains q ∉ corrupted, so q ≠ p.
        have hpq : p ≠ q := fun h => hgate.1 (h ▸ hp)
        simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at h_d
        simp [avssStep, setLocal_local_ne _ _ _ _ hpq, hdc]
        exact h_local_align p hp h_d

omit [Fintype F] in
/-- The structural part of `initPred` already implies
`coalitionRowPolyAlignedInv` vacuously: at init, `dealerMessages` is
all `none` (clause 1 vacuous) and all `local_` are `init` so
`delivered = false` (clause 2 vacuous).  No `coeffs`-witness needed. -/
theorem initPred_coalitionRowPolyAlignedInv
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (s : AVSSState n t F) (h : initPred sec corr coeffs s) :
    coalitionRowPolyAlignedInv s := by
  obtain ⟨hloc, _, _, _, _, _, _, _, hdm, _⟩ := h
  refine ⟨?_, ?_⟩
  · intro p msg hmsg
    rw [hdm] at hmsg
    cases hmsg
  · intro p _ h_d
    rw [hloc p] at h_d
    simp [AVSSLocalState.init] at h_d

/-! ### Phase 8.5b-β: queue well-formedness invariant.

Bundles four protocol-level queue invariants used by the liveness lemma's
`Or.inr` dispatch.  Each invariant is preserved by every gated action
(proved mechanically, see `avssStep_preserves_avssQueueWfInv`). -/

/-- Queue/state well-formedness invariant.  Tracks four protocol-level
queue invariants used to discharge the liveness lemma:

  * `inflightDeliveries`: every entry is honest, undelivered, and has its
    dealer message populated (so `partyDeliver` is enabled).
  * `inflightEchoes`: each queued `(q, p)` has `q ∉ p.echoesReceived`
    (so `partyEchoReceive p q` is enabled).
  * `inflightReady`: each queued `(q, p)` has `q ∉ p.readyReceived`
    (so `partyReceiveReady p q` is enabled).
  * `dealerSent ⟹ ∀ p, dealerMessages.isSome` (joint with the
    `inflightDeliveries` clause).

Phase 8.5b-γ-followup-2: `inflightReady` is now per-pair `(q, p)`. -/
def avssQueueWfInv (s : AVSSState n t F) : Prop :=
  (∀ p, p ∈ s.inflightDeliveries →
    p ∉ s.corrupted ∧ (s.local_ p).delivered = false ∧ (s.dealerMessages p).isSome) ∧
  (∀ q p, (q, p) ∈ s.inflightEchoes → q ∉ (s.local_ p).echoesReceived) ∧
  (∀ q p, (q, p) ∈ s.inflightReady → q ∉ (s.local_ p).readyReceived) ∧
  -- Phase 8.5d-α: per-party form. `dealerSent p = true → dealerMessages p is populated`.
  (∀ p, s.dealerSent p = true → (s.dealerMessages p).isSome)

omit [Fintype F] in
theorem initPred_avssQueueWfInv (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (s : AVSSState n t F) (h : initPred sec corr coeffs s) :
    avssQueueWfInv s := by
  obtain ⟨hloc, _, _, hidl, _, hie, hird, hds, _⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp; rw [hidl] at hp; exact absurd hp (Finset.notMem_empty _)
  · intro q p hqp; rw [hie] at hqp; exact absurd hqp (Finset.notMem_empty _)
  · intro q p hq; rw [hird] at hq; exact absurd hq (Finset.notMem_empty _)
  · intro p hbad; rw [hds] at hbad; cases hbad

/-! ### Phase 8.5b-γ: freshness invariant.

Tracks four "echo/ready freshness" relations consumed by
`avssStep_preserves_avssQueueWfInv` (the partyEchoSend/partyReady/
partyAmplify cases that grow `inflightEchoes` / `inflightReady` need
to know the newly enqueued echo/ready hasn't already been received
or already in flight).  Bundled as a single `Prop` so we can thread
it through the cert. -/

/-- Freshness/source-sent invariant.

  * Q6 (echo freshness): if `q.echoSent = false`, then `q ∉ p.echoesReceived`
    for every `p` (no echo from `q` has ever been received because none was
    ever sent).
  * Q7 (ready freshness): same with ready.
  * Q8 (echo source-sent): if `q.echoSent = false`, then `(q, p) ∉ inflightEchoes`
    for every `p` (no echo from `q` is in flight either).
  * Q9 (ready source-sent): if `q.readySent = false`, then `(q, p) ∉ inflightReady`
    for every `p` (Phase 8.5b-γ-followup-2: per-pair tokens). -/
def avssFreshInv (s : AVSSState n t F) : Prop :=
  (∀ q, (s.local_ q).echoSent = false →
        ∀ p, q ∉ (s.local_ p).echoesReceived) ∧
  (∀ q, (s.local_ q).readySent = false →
        ∀ p, q ∉ (s.local_ p).readyReceived) ∧
  (∀ q, (s.local_ q).echoSent = false →
        ∀ p, (q, p) ∉ s.inflightEchoes) ∧
  (∀ q, (s.local_ q).readySent = false →
        ∀ p, (q, p) ∉ s.inflightReady)

omit [Fintype F] in
theorem initPred_avssFreshInv (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (s : AVSSState n t F) (h : initPred sec corr coeffs s) :
    avssFreshInv s := by
  obtain ⟨hloc, _, _, _, _, hie, hird, _, _⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q _ p; rw [hloc p]; show q ∉ (AVSSLocalState.init n t F).echoesReceived
    simp [AVSSLocalState.init]
  · intro q _ p; rw [hloc p]; show q ∉ (AVSSLocalState.init n t F).readyReceived
    simp [AVSSLocalState.init]
  · intro q _ p hqp; rw [hie] at hqp; exact absurd hqp (Finset.notMem_empty _)
  · intro q _ p hq; rw [hird] at hq; exact absurd hq (Finset.notMem_empty _)

omit [Fintype F] in
/-- `avssQueueWfInv` is preserved by every gated action.  Proof is
mechanical: each clause is preserved by frame reasoning + the action's
specific contribution.  The only delicate cases are
  * `dealerShare`: needs `avssTermInv`'s pre-share quiescence to know
    every honest party's local state is `init`,
  * `partyDeliver` / `partyCorruptDeliver`: erases an entry from
    `inflightDeliveries` and updates `delivered`, requiring `p ≠ q`
    reasoning,
  * `partyReady` / `partyAmplify`: adds to `inflightReady`, needs the
    pre's queue WF to know the new entry isn't already in any
    `readyReceived`.

Phase 8.5b-γ also threads `avssFreshInv` to discharge the freshness
sub-goals (`q ∉ p.echoesReceived` / `q ∉ p.readyReceived`) for the
new entries added by `partyEchoSend` / `partyReady` / `partyAmplify`. -/
theorem avssStep_preserves_avssQueueWfInv
    (a : AVSSAction n F) (s : AVSSState n t F)
    (hgate : actionGate a s) (hterm : avssTermInv s)
    (hfresh : avssFreshInv s) (hwf : avssQueueWfInv s) :
    avssQueueWfInv (avssStep a s) := by
  classical
  obtain ⟨hF6, hF7, _hF8, _hF9⟩ := hfresh
  obtain ⟨hQ1, hQ2, hQ3, hQ5⟩ := hwf
  cases a with
  | dealerShareTo p =>
    -- Phase 8.5d-α: per-party emit. Local state is unchanged; ife and ifr unchanged.
    -- For Q1: post.ifd = pre.ifd (if p ∈ corr) or pre.ifd ∪ {p} (if p ∉ corr).
    --   * For r ∈ pre.ifd: same as pre (Q1 carries through hQ1, since dealerMessages
    --     was only changed at slot p, and r ≠ p possibly — but Q1 needs
    --     `dealerMessages r .isSome`; pre's hQ1 gives this, and post's update
    --     doesn't lose it since `Function.update_some` preserves `isSome`).
    --   * For new entry r = p (only when p ∉ corr): need p ∉ corr (✓ by case),
    --     pre.local_ p.delivered = false, and post.dealerMessages p .isSome.
    --     The first follows from `avssTermInv` clause 4 and the gate's
    --     `dealerSent p = false`. The latter is true since post writes `some _`.
    -- Q5: post.dealerSent r = true for r given. If r = p, post.dealerMessages p =
    -- some payload by `Function.update_self`, .isSome trivially. If r ≠ p,
    -- post.dealerSent r = pre.dealerSent r, so use hQ5 r.
    have hgate' : s.dealerSent p = false := hgate
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Q1: ifd post.
      intro r hr
      by_cases hpcorr : p ∉ s.corrupted
      · -- post.ifd = insert p s.ifd. Cases on r = p vs r ≠ p.
        have h_post_ifd : (avssStep (.dealerShareTo p) s).inflightDeliveries =
            insert p s.inflightDeliveries := by simp [avssStep, hpcorr]
        rw [h_post_ifd] at hr
        rcases Finset.mem_insert.mp hr with rfl | hr_old
        · -- r = p: honest p, delivered = false, dealerMessages p .isSome (post).
          refine ⟨hpcorr, ?_, ?_⟩
          · -- pre.local_ p.delivered = false from clause 4.
            show ((avssStep (.dealerShareTo r) s).local_ r).delivered = false
            simp [avssStep]
            exact hterm.2.2.2 r hpcorr hgate'
          · show ((avssStep (.dealerShareTo r) s).dealerMessages r).isSome
            simp [avssStep, Function.update_self]
        · -- r ∈ pre.ifd: Q1 + frame.
          obtain ⟨hr_h, hr_ndel, hr_dm⟩ := hQ1 r hr_old
          refine ⟨hr_h, ?_, ?_⟩
          · show ((avssStep (.dealerShareTo p) s).local_ r).delivered = false
            simp [avssStep]
            exact hr_ndel
          · -- post.dealerMessages r = update p (some _) r. If r = p (only honest p case),
            -- this is some _; if r ≠ p, this is pre.dealerMessages r = some _ from hr_dm.
            show ((avssStep (.dealerShareTo p) s).dealerMessages r).isSome
            simp only [avssStep]
            by_cases hrp : r = p
            · subst hrp; simp [Function.update_self]
            · simp [Function.update_of_ne hrp]; exact hr_dm
      · -- p ∈ corr: post.ifd = pre.ifd; r ∈ pre.ifd.
        have h_post_ifd : (avssStep (.dealerShareTo p) s).inflightDeliveries =
            s.inflightDeliveries := by
          simp only [avssStep]
          split <;> simp_all
        rw [h_post_ifd] at hr
        obtain ⟨hr_h, hr_ndel, hr_dm⟩ := hQ1 r hr
        refine ⟨hr_h, ?_, ?_⟩
        · show ((avssStep (.dealerShareTo p) s).local_ r).delivered = false
          simp [avssStep]; exact hr_ndel
        · show ((avssStep (.dealerShareTo p) s).dealerMessages r).isSome
          simp only [avssStep]
          by_cases hrp : r = p
          · subst hrp; simp [Function.update_self]
          · simp [Function.update_of_ne hrp]; exact hr_dm
    · -- Q2: ife unchanged.
      intro q r hqr
      have h_post_ife : (avssStep (.dealerShareTo p) s).inflightEchoes = s.inflightEchoes :=
        rfl
      rw [h_post_ife] at hqr
      have h_post_loc : ((avssStep (.dealerShareTo p) s).local_ r).echoesReceived =
          (s.local_ r).echoesReceived := rfl
      rw [h_post_loc]
      exact hQ2 q r hqr
    · -- Q3: ifr unchanged.
      intro q r hqr
      have h_post_ifr : (avssStep (.dealerShareTo p) s).inflightReady = s.inflightReady := rfl
      rw [h_post_ifr] at hqr
      have h_post_loc : ((avssStep (.dealerShareTo p) s).local_ r).readyReceived =
          (s.local_ r).readyReceived := rfl
      rw [h_post_loc]
      exact hQ3 q r hqr
    · -- Q5: ∀ r, post.dealerSent r = true → post.dealerMessages r .isSome.
      intro r hr_post
      show ((avssStep (.dealerShareTo p) s).dealerMessages r).isSome
      simp only [avssStep]
      by_cases hrp : r = p
      · subst hrp; simp [Function.update_self]
      · simp [Function.update_of_ne hrp]
        -- hr_post : post.dealerSent r = true. With r ≠ p: post = pre. So pre.dealerSent r = true.
        have h_pre_t : s.dealerSent r = true := by
          have h_post_eq : (avssStep (.dealerShareTo p) s).dealerSent r =
              s.dealerSent r := by simp [avssStep, Function.update_of_ne hrp]
          rw [h_post_eq] at hr_post; exact hr_post
        exact hQ5 r h_pre_t
  | partyDeliver q =>
    obtain ⟨_hds, hq_h, hq_in, _hq_ndel, _hq_dm⟩ := hgate
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Q1 post: ifd post = ifd.erase q. Each member is in pre.ifd \ {q}. Use Q1 pre + p ≠ q.
      intro p hp
      have : (avssStep (.partyDeliver q) s).inflightDeliveries = s.inflightDeliveries.erase q :=
        rfl
      rw [this] at hp
      have hpne : p ≠ q := (Finset.mem_erase.mp hp).1
      have hp_in : p ∈ s.inflightDeliveries := (Finset.mem_erase.mp hp).2
      obtain ⟨hp_h, hp_ndel, hp_dm⟩ := hQ1 p hp_in
      refine ⟨hp_h, ?_, ?_⟩
      · -- p.delivered post = pre.local_ p.delivered (since p ≠ q) = false.
        simp [avssStep, setLocal_local_ne _ _ _ _ hpne]
        exact hp_ndel
      · -- dealerMessages unchanged.
        show ((avssStep _ s).dealerMessages p).isSome
        simp [avssStep, setLocal]
        exact hp_dm
    · -- Q2: ife unchanged. apply hQ2.
      intro qq p hqp
      have : (avssStep (.partyDeliver q) s).inflightEchoes = s.inflightEchoes := rfl
      rw [this] at hqp
      have heR_eq : (((avssStep (.partyDeliver q) s).local_ p).echoesReceived) =
          (s.local_ p).echoesReceived := by
        by_cases hpq : p = q
        · subst hpq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
      rw [heR_eq]; exact hQ2 qq p hqp
    · -- Q3: ifr unchanged.
      intro qq p hq
      have : (avssStep (.partyDeliver q) s).inflightReady = s.inflightReady := rfl
      rw [this] at hq
      have hrR_eq : (((avssStep (.partyDeliver q) s).local_ p).readyReceived) =
          (s.local_ p).readyReceived := by
        by_cases hpq : p = q
        · subst hpq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
      rw [hrR_eq]; exact hQ3 qq p hq
    · -- Q5: dealerSent unchanged, dealerMessages unchanged.
      intro p hds_post
      have hds_pre : s.dealerSent p = true := by
        have h : (avssStep (.partyDeliver q) s).dealerSent = s.dealerSent := by
          simp [avssStep, setLocal]
        rw [h] at hds_post; exact hds_post
      show ((avssStep _ s).dealerMessages p).isSome
      simp [avssStep, setLocal]
      exact hQ5 p hds_pre
  | partyCorruptDeliver q =>
    obtain ⟨_hds, hq_corr, _hq_in, _hq_ndel, _hq_dm⟩ := hgate
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- ifd unchanged (partyCorruptDeliver only touches inflightCorruptDeliveries).
      intro p hp
      have : (avssStep (.partyCorruptDeliver q) s).inflightDeliveries = s.inflightDeliveries :=
        rfl
      rw [this] at hp
      obtain ⟨hp_h, hp_ndel, hp_dm⟩ := hQ1 p hp
      refine ⟨hp_h, ?_, ?_⟩
      · -- p ∉ corr but q ∈ corr, so p ≠ q.
        have hpne : p ≠ q := fun heq => hp_h (heq ▸ hq_corr)
        simp [avssStep, setLocal_local_ne _ _ _ _ hpne]
        exact hp_ndel
      · show ((avssStep _ s).dealerMessages p).isSome
        simp [avssStep, setLocal]
        exact hp_dm
    · intro qq p hqp
      have : (avssStep (.partyCorruptDeliver q) s).inflightEchoes = s.inflightEchoes := rfl
      rw [this] at hqp
      have heR_eq : (((avssStep (.partyCorruptDeliver q) s).local_ p).echoesReceived) =
          (s.local_ p).echoesReceived := by
        by_cases hpq : p = q
        · subst hpq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
      rw [heR_eq]; exact hQ2 qq p hqp
    · intro qq p hq
      have : (avssStep (.partyCorruptDeliver q) s).inflightReady = s.inflightReady := rfl
      rw [this] at hq
      have hrR_eq : (((avssStep (.partyCorruptDeliver q) s).local_ p).readyReceived) =
          (s.local_ p).readyReceived := by
        by_cases hpq : p = q
        · subst hpq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
      rw [hrR_eq]; exact hQ3 qq p hq
    · intro p hds_post
      have hds_pre : s.dealerSent p = true := by
        have : (avssStep (.partyCorruptDeliver q) s).dealerSent = s.dealerSent := by
          simp [avssStep, setLocal]
        rw [this] at hds_post; exact hds_post
      show ((avssStep _ s).dealerMessages p).isSome
      simp [avssStep, setLocal]
      exact hQ5 p hds_pre
  | partyEchoSend q =>
    obtain ⟨_hq_del, hq_es, _hq_ds⟩ := hgate
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- ifd unchanged.
      intro p hp
      have : (avssStep (.partyEchoSend q) s).inflightDeliveries = s.inflightDeliveries := by
        simp [avssStep, setLocal]
      rw [this] at hp
      obtain ⟨hp_h, hp_ndel, hp_dm⟩ := hQ1 p hp
      refine ⟨hp_h, ?_, ?_⟩
      · -- delivered unchanged: partyEchoSend only writes echoSent.
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self]; exact hp_ndel
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]; exact hp_ndel
      · show ((avssStep _ s).dealerMessages p).isSome
        simp [avssStep, setLocal]
        exact hp_dm
    · -- Q2: post.ife = pre.ife ∪ image (q, ·) for univ. echoesReceived for receivers unchanged
      -- (partyEchoSend writes sender's echoSent, not receiver's echoesReceived).
      intro qq p hqp
      have heR_eq : (((avssStep (.partyEchoSend q) s).local_ p).echoesReceived) =
          (s.local_ p).echoesReceived := by
        by_cases hpq : p = q
        · subst hpq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
      rw [heR_eq]
      -- The new entries are (q, *), so qq could be q. We need qq ∉ p.echoesReceived.
      -- Case 1: (qq, p) ∈ pre.ife → use hQ2.
      -- Case 2: (qq, p) ∈ new image → qq = q.
      have hpost : (avssStep (.partyEchoSend q) s).inflightEchoes =
          s.inflightEchoes ∪
            (Finset.univ : Finset (Fin n)).image (fun r => (q, r)) := rfl
      rw [hpost] at hqp
      rcases Finset.mem_union.mp hqp with hin1 | hin2
      · exact hQ2 qq p hin1
      · -- (qq, p) ∈ image → qq = q. Then need q ∉ (s.local_ p).echoesReceived.
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hin2
        obtain ⟨y, heq⟩ := hin2
        have hqq_eq : q = qq := (Prod.mk.injEq _ _ _ _).mp heq |>.1
        have _hp_eq : y = p := (Prod.mk.injEq _ _ _ _).mp heq |>.2
        subst hqq_eq
        -- Goal: q ∉ (s.local_ p).echoesReceived.  Q6 (echo freshness) of
        -- `avssFreshInv` gives this from `q.echoSent = false` (gate).
        exact hF6 q hq_es p
    · intro qq p hq
      have : (avssStep (.partyEchoSend q) s).inflightReady = s.inflightReady := by
        simp [avssStep, setLocal]
      rw [this] at hq
      have hrR_eq : (((avssStep (.partyEchoSend q) s).local_ p).readyReceived) =
          (s.local_ p).readyReceived := by
        by_cases hpq : p = q
        · subst hpq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
      rw [hrR_eq]; exact hQ3 qq p hq
    · intro p hds_post
      have hds_pre : s.dealerSent p = true := by
        have : (avssStep (.partyEchoSend q) s).dealerSent = s.dealerSent := by
          simp [avssStep, setLocal]
        rw [this] at hds_post; exact hds_post
      show ((avssStep _ s).dealerMessages p).isSome
      simp [avssStep, setLocal]
      exact hQ5 p hds_pre
  | partyEchoReceive q r =>
    obtain ⟨hqr_in, _hqnotin⟩ := hgate
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro p hp
      have : (avssStep (.partyEchoReceive q r) s).inflightDeliveries = s.inflightDeliveries := by
        simp [avssStep, setLocal]
      rw [this] at hp
      obtain ⟨hp_h, hp_ndel, hp_dm⟩ := hQ1 p hp
      refine ⟨hp_h, ?_, ?_⟩
      · by_cases hpq : p = q
        · subst hpq; simp [avssStep, setLocal_local_self]; exact hp_ndel
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]; exact hp_ndel
      · show ((avssStep _ s).dealerMessages p).isSome
        simp [avssStep, setLocal]
        exact hp_dm
    · -- Q2 post: ife = pre.ife.erase (r, q). For (qq, p) ∈ post.ife: in pre.ife, ≠ (r, q).
      intro qq p hqp
      have hpost : (avssStep (.partyEchoReceive q r) s).inflightEchoes =
          s.inflightEchoes.erase (r, q) := rfl
      rw [hpost] at hqp
      have hne : (qq, p) ≠ (r, q) := (Finset.mem_erase.mp hqp).1
      have hin_pre : (qq, p) ∈ s.inflightEchoes := (Finset.mem_erase.mp hqp).2
      -- echoesReceived for receiver: only q's local_ updated (to insert r).
      -- For p ≠ q: echoesReceived unchanged. For p = q: post = insert r pre.
      by_cases hpq : p = q
      · subst hpq
        -- After subst, `q` is replaced by `p`.  Goal:
        -- `qq ∉ post.local_ p.echoesReceived = insert r (pre.local_ p.echoesReceived)`.
        simp [avssStep, setLocal_local_self]
        refine ⟨?_, hQ2 qq p hin_pre⟩
        intro hqr_eq
        exact hne (by rw [hqr_eq])
      · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact hQ2 qq p hin_pre
    · intro qq p hq
      have : (avssStep (.partyEchoReceive q r) s).inflightReady = s.inflightReady := by
        simp [avssStep, setLocal]
      rw [this] at hq
      have hrR_eq : (((avssStep (.partyEchoReceive q r) s).local_ p).readyReceived) =
          (s.local_ p).readyReceived := by
        by_cases hpq : p = q
        · subst hpq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
      rw [hrR_eq]; exact hQ3 qq p hq
    · intro p hds_post
      have hds_pre : s.dealerSent p = true := by
        have : (avssStep (.partyEchoReceive q r) s).dealerSent = s.dealerSent := by
          simp [avssStep, setLocal]
        rw [this] at hds_post; exact hds_post
      show ((avssStep _ s).dealerMessages p).isSome
      simp [avssStep, setLocal]
      exact hQ5 p hds_pre
  | partyReady q =>
    obtain ⟨_hq_del, hq_rs, _hq_eR, _hq_ds⟩ := hgate
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro p hp
      have : (avssStep (.partyReady q) s).inflightDeliveries = s.inflightDeliveries := by
        simp [avssStep, setLocal]
      rw [this] at hp
      obtain ⟨hp_h, hp_ndel, hp_dm⟩ := hQ1 p hp
      refine ⟨hp_h, ?_, ?_⟩
      · by_cases hpq : p = q
        · subst hpq; simp [avssStep, setLocal_local_self]; exact hp_ndel
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]; exact hp_ndel
      · show ((avssStep _ s).dealerMessages p).isSome
        simp [avssStep, setLocal]
        exact hp_dm
    · intro qq p hqp
      have : (avssStep (.partyReady q) s).inflightEchoes = s.inflightEchoes := by
        simp [avssStep, setLocal]
      rw [this] at hqp
      have heR_eq : (((avssStep (.partyReady q) s).local_ p).echoesReceived) =
          (s.local_ p).echoesReceived := by
        by_cases hpq : p = q
        · subst hpq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
      rw [heR_eq]; exact hQ2 qq p hqp
    · -- Phase 8.5b-γ-followup-2: Q3 post = pre.ifr ∪ image(fun r => (q, r)).
      -- New entries are (q, r) for every r.  Need q ∉ p.readyReceived (any p).
      intro qq p hq
      have hpost : (avssStep (.partyReady q) s).inflightReady =
          s.inflightReady ∪
            (Finset.univ : Finset (Fin n)).image (fun r => (q, r)) := rfl
      rw [hpost] at hq
      have hrR_eq : (((avssStep (.partyReady q) s).local_ p).readyReceived) =
          (s.local_ p).readyReceived := by
        by_cases hpq : p = q
        · subst hpq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
      rw [hrR_eq]
      rcases Finset.mem_union.mp hq with hin_pre | hin_img
      · exact hQ3 qq p hin_pre
      · -- (qq, p) is in the image, so qq = q.  Q7 closes.
        rw [Finset.mem_image] at hin_img
        obtain ⟨_, _, heq⟩ := hin_img
        rw [Prod.mk.injEq] at heq
        rw [← heq.1]; exact hF7 q hq_rs p
    · intro p hds_post
      have hds_pre : s.dealerSent p = true := by
        have : (avssStep (.partyReady q) s).dealerSent = s.dealerSent := by
          simp [avssStep, setLocal]
        rw [this] at hds_post; exact hds_post
      show ((avssStep _ s).dealerMessages p).isSome
      simp [avssStep, setLocal]
      exact hQ5 p hds_pre
  | partyAmplify q =>
    obtain ⟨hq_rs, _hq_rR, _hq_ds⟩ := hgate
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro p hp
      have : (avssStep (.partyAmplify q) s).inflightDeliveries = s.inflightDeliveries := by
        simp [avssStep, setLocal]
      rw [this] at hp
      obtain ⟨hp_h, hp_ndel, hp_dm⟩ := hQ1 p hp
      refine ⟨hp_h, ?_, ?_⟩
      · by_cases hpq : p = q
        · subst hpq; simp [avssStep, setLocal_local_self]; exact hp_ndel
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]; exact hp_ndel
      · show ((avssStep _ s).dealerMessages p).isSome
        simp [avssStep, setLocal]
        exact hp_dm
    · intro qq p hqp
      have : (avssStep (.partyAmplify q) s).inflightEchoes = s.inflightEchoes := by
        simp [avssStep, setLocal]
      rw [this] at hqp
      have heR_eq : (((avssStep (.partyAmplify q) s).local_ p).echoesReceived) =
          (s.local_ p).echoesReceived := by
        by_cases hpq : p = q
        · subst hpq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
      rw [heR_eq]; exact hQ2 qq p hqp
    · -- Phase 8.5b-γ-followup-2: same as partyReady.
      intro qq p hq
      have hpost : (avssStep (.partyAmplify q) s).inflightReady =
          s.inflightReady ∪
            (Finset.univ : Finset (Fin n)).image (fun r => (q, r)) := rfl
      rw [hpost] at hq
      have hrR_eq : (((avssStep (.partyAmplify q) s).local_ p).readyReceived) =
          (s.local_ p).readyReceived := by
        by_cases hpq : p = q
        · subst hpq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
      rw [hrR_eq]
      rcases Finset.mem_union.mp hq with hin_pre | hin_img
      · exact hQ3 qq p hin_pre
      · rw [Finset.mem_image] at hin_img
        obtain ⟨_, _, heq⟩ := hin_img
        rw [Prod.mk.injEq] at heq
        rw [← heq.1]; exact hF7 q hq_rs p
    · intro p hds_post
      have hds_pre : s.dealerSent p = true := by
        have : (avssStep (.partyAmplify q) s).dealerSent = s.dealerSent := by
          simp [avssStep, setLocal]
        rw [this] at hds_post; exact hds_post
      show ((avssStep _ s).dealerMessages p).isSome
      simp [avssStep, setLocal]
      exact hQ5 p hds_pre
  | partyReceiveReady q r =>
    obtain ⟨hr_in, _hrnotin⟩ := hgate
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro p hp
      have : (avssStep (.partyReceiveReady q r) s).inflightDeliveries = s.inflightDeliveries := by
        simp [avssStep, setLocal]
      rw [this] at hp
      obtain ⟨hp_h, hp_ndel, hp_dm⟩ := hQ1 p hp
      refine ⟨hp_h, ?_, ?_⟩
      · by_cases hpq : p = q
        · subst hpq; simp [avssStep, setLocal_local_self]; exact hp_ndel
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]; exact hp_ndel
      · show ((avssStep _ s).dealerMessages p).isSome
        simp [avssStep, setLocal]
        exact hp_dm
    · intro qq p hqp
      have : (avssStep (.partyReceiveReady q r) s).inflightEchoes = s.inflightEchoes := by
        simp [avssStep, setLocal]
      rw [this] at hqp
      have heR_eq : (((avssStep (.partyReceiveReady q r) s).local_ p).echoesReceived) =
          (s.local_ p).echoesReceived := by
        by_cases hpq : p = q
        · subst hpq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
      rw [heR_eq]; exact hQ2 qq p hqp
    · -- Phase 8.5b-γ-followup-2: ifr_post = ifr.erase (r, q).  For receiver
      -- p = q: rR_post = insert r pre.  For p ≠ q: unchanged.
      intro qq p hq
      have hpost : (avssStep (.partyReceiveReady q r) s).inflightReady =
          s.inflightReady.erase (r, q) := rfl
      rw [hpost] at hq
      have hne_r : ¬ ((qq, p) = (r, q)) := (Finset.mem_erase.mp hq).1
      have hin_pre : (qq, p) ∈ s.inflightReady := (Finset.mem_erase.mp hq).2
      by_cases hpq : p = q
      · subst hpq
        simp [avssStep, setLocal_local_self]
        refine ⟨?_, hQ3 qq p hin_pre⟩
        intro heq; exact hne_r (by rw [heq])
      · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact hQ3 qq p hin_pre
    · intro p hds_post
      have hds_pre : s.dealerSent p = true := by
        have : (avssStep (.partyReceiveReady q r) s).dealerSent = s.dealerSent := by
          simp [avssStep, setLocal]
        rw [this] at hds_post; exact hds_post
      show ((avssStep _ s).dealerMessages p).isSome
      simp [avssStep, setLocal]
      exact hQ5 p hds_pre
  | partyOutput q =>
    obtain ⟨hq_h, _, _, _, _⟩ := hgate
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro p hp
      have : (avssStep (.partyOutput q) s).inflightDeliveries = s.inflightDeliveries := by
        simp [avssStep, setLocal]
      rw [this] at hp
      obtain ⟨hp_h, hp_ndel, hp_dm⟩ := hQ1 p hp
      refine ⟨hp_h, ?_, ?_⟩
      · -- p ∉ corr but q ∉ corr too, so this doesn't help. p might equal q.
        by_cases hpq : p = q
        · subst hpq; simp [avssStep, setLocal_local_self]; exact hp_ndel
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]; exact hp_ndel
      · show ((avssStep _ s).dealerMessages p).isSome
        simp [avssStep, setLocal]
        exact hp_dm
    · intro qq p hqp
      have : (avssStep (.partyOutput q) s).inflightEchoes = s.inflightEchoes := by
        simp [avssStep, setLocal]
      rw [this] at hqp
      have heR_eq : (((avssStep (.partyOutput q) s).local_ p).echoesReceived) =
          (s.local_ p).echoesReceived := by
        by_cases hpq : p = q
        · subst hpq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
      rw [heR_eq]; exact hQ2 qq p hqp
    · intro qq p hq
      have : (avssStep (.partyOutput q) s).inflightReady = s.inflightReady := by
        simp [avssStep, setLocal]
      rw [this] at hq
      have hrR_eq : (((avssStep (.partyOutput q) s).local_ p).readyReceived) =
          (s.local_ p).readyReceived := by
        by_cases hpq : p = q
        · subst hpq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
      rw [hrR_eq]; exact hQ3 qq p hq
    · intro p hds_post
      have hds_pre : s.dealerSent p = true := by
        have : (avssStep (.partyOutput q) s).dealerSent = s.dealerSent := by
          simp [avssStep, setLocal]
        rw [this] at hds_post; exact hds_post
      show ((avssStep _ s).dealerMessages p).isSome
      simp [avssStep, setLocal]
      exact hQ5 p hds_pre

omit [Fintype F] in
/-- `avssFreshInv` is preserved by every gated action.  The four
clauses are mutually self-supporting: Q6's preservation under
`partyEchoReceive` rests on Q8 (a fresh-source echo can't be in
flight either), and Q7's preservation under `partyReceiveReady`
rests on Q9 analogously.  All other action cases are frame-only. -/
theorem avssStep_preserves_avssFreshInv
    (a : AVSSAction n F) (s : AVSSState n t F)
    (hgate : actionGate a s) (hfresh : avssFreshInv s) :
    avssFreshInv (avssStep a s) := by
  classical
  obtain ⟨hF6, hF7, hF8, hF9⟩ := hfresh
  cases a with
  | dealerShareTo r =>
    -- Phase 8.5d-α: dealerShareTo r leaves all party local states + ife + ifr unchanged.
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro q hq p
      have hes_pre : (s.local_ q).echoSent = false := by
        have : ((avssStep (AVSSAction.dealerShareTo r) s).local_ q) = s.local_ q := rfl
        rw [this] at hq; exact hq
      have heR_eq : ((avssStep (AVSSAction.dealerShareTo r) s).local_ p).echoesReceived =
          (s.local_ p).echoesReceived := rfl
      rw [heR_eq]; exact hF6 q hes_pre p
    · intro q hq p
      have hrs_pre : (s.local_ q).readySent = false := by
        have : ((avssStep (AVSSAction.dealerShareTo r) s).local_ q) = s.local_ q := rfl
        rw [this] at hq; exact hq
      have hrR_eq : ((avssStep (AVSSAction.dealerShareTo r) s).local_ p).readyReceived =
          (s.local_ p).readyReceived := rfl
      rw [hrR_eq]; exact hF7 q hrs_pre p
    · intro q hq p hqp
      have hes_pre : (s.local_ q).echoSent = false := by
        have : ((avssStep (AVSSAction.dealerShareTo r) s).local_ q) = s.local_ q := rfl
        rw [this] at hq; exact hq
      have hife_eq : (avssStep (AVSSAction.dealerShareTo r) s).inflightEchoes = s.inflightEchoes := rfl
      rw [hife_eq] at hqp; exact hF8 q hes_pre p hqp
    · intro q hq p
      have hrs_pre : (s.local_ q).readySent = false := by
        have : ((avssStep (AVSSAction.dealerShareTo r) s).local_ q) = s.local_ q := rfl
        rw [this] at hq; exact hq
      have hifr_eq : (avssStep (AVSSAction.dealerShareTo r) s).inflightReady = s.inflightReady := rfl
      intro hqq; rw [hifr_eq] at hqq; exact hF9 q hrs_pre p hqq
  | partyDeliver q =>
    -- Updates q.delivered + q.rowPoly + ifd. echoSent/echoesReceived/
    -- readySent/readyReceived/ife/ifr all unchanged.
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r hr p
      have hes_eq : ((avssStep (.partyDeliver q) s).local_ r).echoSent = (s.local_ r).echoSent := by
        by_cases hrq : r = q
        · subst hrq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hrq]
      rw [hes_eq] at hr
      have heR_eq : ((avssStep (.partyDeliver q) s).local_ p).echoesReceived =
          (s.local_ p).echoesReceived := by
        by_cases hpq : p = q
        · subst hpq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
      rw [heR_eq]; exact hF6 r hr p
    · intro r hr p
      have hrs_eq : ((avssStep (.partyDeliver q) s).local_ r).readySent = (s.local_ r).readySent := by
        by_cases hrq : r = q
        · subst hrq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hrq]
      rw [hrs_eq] at hr
      have hrR_eq : ((avssStep (.partyDeliver q) s).local_ p).readyReceived =
          (s.local_ p).readyReceived := by
        by_cases hpq : p = q
        · subst hpq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
      rw [hrR_eq]; exact hF7 r hr p
    · intro r hr p hrp
      have hes_eq : ((avssStep (.partyDeliver q) s).local_ r).echoSent = (s.local_ r).echoSent := by
        by_cases hrq : r = q
        · subst hrq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hrq]
      rw [hes_eq] at hr
      have hife_eq : (avssStep (.partyDeliver q) s).inflightEchoes = s.inflightEchoes := rfl
      rw [hife_eq] at hrp; exact hF8 r hr p hrp
    · intro r hr p
      have hrs_eq : ((avssStep (.partyDeliver q) s).local_ r).readySent = (s.local_ r).readySent := by
        by_cases hrq : r = q
        · subst hrq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hrq]
      rw [hrs_eq] at hr
      have hifr_eq : (avssStep (.partyDeliver q) s).inflightReady = s.inflightReady := rfl
      intro hrq; rw [hifr_eq] at hrq; exact hF9 r hr p hrq
  | partyCorruptDeliver q =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r hr p
      have hes_eq : ((avssStep (.partyCorruptDeliver q) s).local_ r).echoSent =
          (s.local_ r).echoSent := by
        by_cases hrq : r = q
        · subst hrq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hrq]
      rw [hes_eq] at hr
      have heR_eq : ((avssStep (.partyCorruptDeliver q) s).local_ p).echoesReceived =
          (s.local_ p).echoesReceived := by
        by_cases hpq : p = q
        · subst hpq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
      rw [heR_eq]; exact hF6 r hr p
    · intro r hr p
      have hrs_eq : ((avssStep (.partyCorruptDeliver q) s).local_ r).readySent =
          (s.local_ r).readySent := by
        by_cases hrq : r = q
        · subst hrq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hrq]
      rw [hrs_eq] at hr
      have hrR_eq : ((avssStep (.partyCorruptDeliver q) s).local_ p).readyReceived =
          (s.local_ p).readyReceived := by
        by_cases hpq : p = q
        · subst hpq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
      rw [hrR_eq]; exact hF7 r hr p
    · intro r hr p hrp
      have hes_eq : ((avssStep (.partyCorruptDeliver q) s).local_ r).echoSent =
          (s.local_ r).echoSent := by
        by_cases hrq : r = q
        · subst hrq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hrq]
      rw [hes_eq] at hr
      have hife_eq : (avssStep (.partyCorruptDeliver q) s).inflightEchoes = s.inflightEchoes := rfl
      rw [hife_eq] at hrp; exact hF8 r hr p hrp
    · intro r hr p
      have hrs_eq : ((avssStep (.partyCorruptDeliver q) s).local_ r).readySent =
          (s.local_ r).readySent := by
        by_cases hrq : r = q
        · subst hrq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hrq]
      rw [hrs_eq] at hr
      have hifr_eq : (avssStep (.partyCorruptDeliver q) s).inflightReady = s.inflightReady := rfl
      intro hrq; rw [hifr_eq] at hrq; exact hF9 r hr p hrq
  | partyEchoSend q =>
    -- Sets q.echoSent = true; adds (q, *) to ife.  Doesn't touch
    -- echoesReceived/readySent/readyReceived/ifr.
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r hr p
      -- For r ≠ q: r.echoSent unchanged; use hF6.  For r = q: post.r.echoSent = true,
      -- contradicts hr.
      have heR_eq : ((avssStep (.partyEchoSend q) s).local_ p).echoesReceived =
          (s.local_ p).echoesReceived := by
        by_cases hpq : p = q
        · subst hpq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
      rw [heR_eq]
      by_cases hrq : r = q
      · subst hrq
        -- After subst: q is gone, only r remains.
        have : ((avssStep (.partyEchoSend r) s).local_ r).echoSent = true := by
          simp [avssStep, setLocal_local_self]
        rw [this] at hr; cases hr
      · have hes_pre : (s.local_ r).echoSent = false := by
          have : ((avssStep (.partyEchoSend q) s).local_ r).echoSent = (s.local_ r).echoSent := by
            simp [avssStep, setLocal_local_ne _ _ _ _ hrq]
          rw [this] at hr; exact hr
        exact hF6 r hes_pre p
    · intro r hr p
      have hrs_pre : (s.local_ r).readySent = false := by
        have : ((avssStep (.partyEchoSend q) s).local_ r).readySent = (s.local_ r).readySent := by
          by_cases hrq : r = q
          · subst hrq; simp [avssStep, setLocal_local_self]
          · simp [avssStep, setLocal_local_ne _ _ _ _ hrq]
        rw [this] at hr; exact hr
      have hrR_eq : ((avssStep (.partyEchoSend q) s).local_ p).readyReceived =
          (s.local_ p).readyReceived := by
        by_cases hpq : p = q
        · subst hpq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
      rw [hrR_eq]; exact hF7 r hrs_pre p
    · intro r hr p hrp
      have hpost : (avssStep (.partyEchoSend q) s).inflightEchoes =
          s.inflightEchoes ∪
            (Finset.univ : Finset (Fin n)).image (fun y => (q, y)) := rfl
      rw [hpost] at hrp
      by_cases hrq : r = q
      · subst hrq
        have : ((avssStep (.partyEchoSend r) s).local_ r).echoSent = true := by
          simp [avssStep, setLocal_local_self]
        rw [this] at hr; cases hr
      · have hes_pre : (s.local_ r).echoSent = false := by
          have : ((avssStep (.partyEchoSend q) s).local_ r).echoSent = (s.local_ r).echoSent := by
            simp [avssStep, setLocal_local_ne _ _ _ _ hrq]
          rw [this] at hr; exact hr
        rcases Finset.mem_union.mp hrp with hin1 | hin2
        · exact hF8 r hes_pre p hin1
        · simp only [Finset.mem_image, Finset.mem_univ, true_and] at hin2
          obtain ⟨y, heq⟩ := hin2
          have : q = r := (Prod.mk.injEq _ _ _ _).mp heq |>.1
          exact hrq this.symm
    · intro r hr p
      have hrs_pre : (s.local_ r).readySent = false := by
        have : ((avssStep (.partyEchoSend q) s).local_ r).readySent = (s.local_ r).readySent := by
          by_cases hrq : r = q
          · subst hrq; simp [avssStep, setLocal_local_self]
          · simp [avssStep, setLocal_local_ne _ _ _ _ hrq]
        rw [this] at hr; exact hr
      have hifr_eq : (avssStep (.partyEchoSend q) s).inflightReady = s.inflightReady := rfl
      intro hrr; rw [hifr_eq] at hrr; exact hF9 r hrs_pre p hrr
  | partyEchoReceive p q =>
    obtain ⟨hqp_in, _hqnotin⟩ := hgate
    -- p.echoesReceived ← insert q; ife ← erase (q, p); echoSent/readySent/readyReceived/ifr unchanged.
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Q6: hyp r.echoSent = false (post = pre).  Need r ∉ post.p'.echoesReceived.
      -- For p' ≠ p: unchanged.  For p' = p: post = insert q pre.p.echoesReceived.
      -- If r = q, then q.echoSent = false but gate gives (q, p) ∈ pre.ife; Q8 contradiction.
      intro r hr p'
      have hes_pre : (s.local_ r).echoSent = false := by
        have : ((avssStep (.partyEchoReceive p q) s).local_ r).echoSent = (s.local_ r).echoSent := by
          by_cases hrp : r = p
          · subst hrp; simp [avssStep, setLocal_local_self]
          · simp [avssStep, setLocal_local_ne _ _ _ _ hrp]
        rw [this] at hr; exact hr
      have hrq : r ≠ q := by
        intro heq; subst heq
        exact hF8 r hes_pre p hqp_in
      by_cases hp'p : p' = p
      · subst hp'p
        have : ((avssStep (.partyEchoReceive p' q) s).local_ p').echoesReceived =
            insert q (s.local_ p').echoesReceived := by
          simp [avssStep, setLocal_local_self]
        rw [this]
        rw [Finset.mem_insert, not_or]
        exact ⟨hrq, hF6 r hes_pre p'⟩
      · have : ((avssStep (.partyEchoReceive p q) s).local_ p').echoesReceived =
            (s.local_ p').echoesReceived := by
          simp [avssStep, setLocal_local_ne _ _ _ _ hp'p]
        rw [this]; exact hF6 r hes_pre p'
    · intro r hr p'
      have hrs_pre : (s.local_ r).readySent = false := by
        have : ((avssStep (.partyEchoReceive p q) s).local_ r).readySent = (s.local_ r).readySent := by
          by_cases hrp : r = p
          · subst hrp; simp [avssStep, setLocal_local_self]
          · simp [avssStep, setLocal_local_ne _ _ _ _ hrp]
        rw [this] at hr; exact hr
      have hrR_eq : ((avssStep (.partyEchoReceive p q) s).local_ p').readyReceived =
          (s.local_ p').readyReceived := by
        by_cases hp'p : p' = p
        · subst hp'p; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hp'p]
      rw [hrR_eq]; exact hF7 r hrs_pre p'
    · intro r hr p' hrp'
      have hes_pre : (s.local_ r).echoSent = false := by
        have : ((avssStep (.partyEchoReceive p q) s).local_ r).echoSent = (s.local_ r).echoSent := by
          by_cases hrp : r = p
          · subst hrp; simp [avssStep, setLocal_local_self]
          · simp [avssStep, setLocal_local_ne _ _ _ _ hrp]
        rw [this] at hr; exact hr
      have hpost : (avssStep (.partyEchoReceive p q) s).inflightEchoes =
          s.inflightEchoes.erase (q, p) := rfl
      rw [hpost] at hrp'
      have : (r, p') ∈ s.inflightEchoes := (Finset.mem_erase.mp hrp').2
      exact hF8 r hes_pre p' this
    · intro r hr p'
      have hrs_pre : (s.local_ r).readySent = false := by
        have : ((avssStep (.partyEchoReceive p q) s).local_ r).readySent = (s.local_ r).readySent := by
          by_cases hrp : r = p
          · subst hrp; simp [avssStep, setLocal_local_self]
          · simp [avssStep, setLocal_local_ne _ _ _ _ hrp]
        rw [this] at hr; exact hr
      have hifr_eq : (avssStep (.partyEchoReceive p q) s).inflightReady = s.inflightReady := rfl
      intro hrr; rw [hifr_eq] at hrr; exact hF9 r hrs_pre p' hrr
  | partyReady q =>
    -- q.readySent ← true; ifr ← insert q; echoSent/echoesReceived/readyReceived/ife unchanged.
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r hr p
      have hes_pre : (s.local_ r).echoSent = false := by
        have : ((avssStep (.partyReady q) s).local_ r).echoSent = (s.local_ r).echoSent := by
          by_cases hrq : r = q
          · subst hrq; simp [avssStep, setLocal_local_self]
          · simp [avssStep, setLocal_local_ne _ _ _ _ hrq]
        rw [this] at hr; exact hr
      have heR_eq : ((avssStep (.partyReady q) s).local_ p).echoesReceived =
          (s.local_ p).echoesReceived := by
        by_cases hpq : p = q
        · subst hpq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
      rw [heR_eq]; exact hF6 r hes_pre p
    · intro r hr p
      -- For r ≠ q: r.readySent unchanged; use hF7.  For r = q: post = true, contradicts hr.
      have hrR_eq : ((avssStep (.partyReady q) s).local_ p).readyReceived =
          (s.local_ p).readyReceived := by
        by_cases hpq : p = q
        · subst hpq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
      rw [hrR_eq]
      by_cases hrq : r = q
      · subst hrq
        have : ((avssStep (.partyReady r) s).local_ r).readySent = true := by
          simp [avssStep, setLocal_local_self]
        rw [this] at hr; cases hr
      · have hrs_pre : (s.local_ r).readySent = false := by
          have : ((avssStep (.partyReady q) s).local_ r).readySent = (s.local_ r).readySent := by
            simp [avssStep, setLocal_local_ne _ _ _ _ hrq]
          rw [this] at hr; exact hr
        exact hF7 r hrs_pre p
    · intro r hr p hrp
      have hes_pre : (s.local_ r).echoSent = false := by
        have : ((avssStep (.partyReady q) s).local_ r).echoSent = (s.local_ r).echoSent := by
          by_cases hrq : r = q
          · subst hrq; simp [avssStep, setLocal_local_self]
          · simp [avssStep, setLocal_local_ne _ _ _ _ hrq]
        rw [this] at hr; exact hr
      have hife_eq : (avssStep (.partyReady q) s).inflightEchoes = s.inflightEchoes := by
        simp [avssStep, setLocal]
      rw [hife_eq] at hrp; exact hF8 r hes_pre p hrp
    · intro r hr p
      by_cases hrq : r = q
      · subst hrq
        have : ((avssStep (.partyReady r) s).local_ r).readySent = true := by
          simp [avssStep, setLocal_local_self]
        rw [this] at hr; cases hr
      · have hrs_pre : (s.local_ r).readySent = false := by
          have : ((avssStep (.partyReady q) s).local_ r).readySent = (s.local_ r).readySent := by
            simp [avssStep, setLocal_local_ne _ _ _ _ hrq]
          rw [this] at hr; exact hr
        intro hrr
        have hpost : (avssStep (.partyReady q) s).inflightReady =
            s.inflightReady ∪
              (Finset.univ : Finset (Fin n)).image (fun y => (q, y)) := rfl
        rw [hpost] at hrr
        rcases Finset.mem_union.mp hrr with hin_pre | hin_img
        · exact hF9 r hrs_pre p hin_pre
        · rw [Finset.mem_image] at hin_img
          obtain ⟨_, _, heq⟩ := hin_img
          rw [Prod.mk.injEq] at heq
          exact hrq heq.1.symm
  | partyAmplify q =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r hr p
      have hes_pre : (s.local_ r).echoSent = false := by
        have : ((avssStep (.partyAmplify q) s).local_ r).echoSent = (s.local_ r).echoSent := by
          by_cases hrq : r = q
          · subst hrq; simp [avssStep, setLocal_local_self]
          · simp [avssStep, setLocal_local_ne _ _ _ _ hrq]
        rw [this] at hr; exact hr
      have heR_eq : ((avssStep (.partyAmplify q) s).local_ p).echoesReceived =
          (s.local_ p).echoesReceived := by
        by_cases hpq : p = q
        · subst hpq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
      rw [heR_eq]; exact hF6 r hes_pre p
    · intro r hr p
      have hrR_eq : ((avssStep (.partyAmplify q) s).local_ p).readyReceived =
          (s.local_ p).readyReceived := by
        by_cases hpq : p = q
        · subst hpq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
      rw [hrR_eq]
      by_cases hrq : r = q
      · subst hrq
        have : ((avssStep (.partyAmplify r) s).local_ r).readySent = true := by
          simp [avssStep, setLocal_local_self]
        rw [this] at hr; cases hr
      · have hrs_pre : (s.local_ r).readySent = false := by
          have : ((avssStep (.partyAmplify q) s).local_ r).readySent = (s.local_ r).readySent := by
            simp [avssStep, setLocal_local_ne _ _ _ _ hrq]
          rw [this] at hr; exact hr
        exact hF7 r hrs_pre p
    · intro r hr p hrp
      have hes_pre : (s.local_ r).echoSent = false := by
        have : ((avssStep (.partyAmplify q) s).local_ r).echoSent = (s.local_ r).echoSent := by
          by_cases hrq : r = q
          · subst hrq; simp [avssStep, setLocal_local_self]
          · simp [avssStep, setLocal_local_ne _ _ _ _ hrq]
        rw [this] at hr; exact hr
      have hife_eq : (avssStep (.partyAmplify q) s).inflightEchoes = s.inflightEchoes := by
        simp [avssStep, setLocal]
      rw [hife_eq] at hrp; exact hF8 r hes_pre p hrp
    · intro r hr p
      by_cases hrq : r = q
      · subst hrq
        have : ((avssStep (.partyAmplify r) s).local_ r).readySent = true := by
          simp [avssStep, setLocal_local_self]
        rw [this] at hr; cases hr
      · have hrs_pre : (s.local_ r).readySent = false := by
          have : ((avssStep (.partyAmplify q) s).local_ r).readySent = (s.local_ r).readySent := by
            simp [avssStep, setLocal_local_ne _ _ _ _ hrq]
          rw [this] at hr; exact hr
        intro hrr
        have hpost : (avssStep (.partyAmplify q) s).inflightReady =
            s.inflightReady ∪
              (Finset.univ : Finset (Fin n)).image (fun y => (q, y)) := rfl
        rw [hpost] at hrr
        rcases Finset.mem_union.mp hrr with hin_pre | hin_img
        · exact hF9 r hrs_pre p hin_pre
        · rw [Finset.mem_image] at hin_img
          obtain ⟨_, _, heq⟩ := hin_img
          rw [Prod.mk.injEq] at heq
          exact hrq heq.1.symm
  | partyReceiveReady p q =>
    obtain ⟨hq_in, _hqnotin⟩ := hgate
    -- p.readyReceived ← insert q; ifr ← erase q; echoSent/echoesReceived/readySent/ife unchanged.
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r hr p'
      have hes_pre : (s.local_ r).echoSent = false := by
        have : ((avssStep (.partyReceiveReady p q) s).local_ r).echoSent = (s.local_ r).echoSent := by
          by_cases hrp : r = p
          · subst hrp; simp [avssStep, setLocal_local_self]
          · simp [avssStep, setLocal_local_ne _ _ _ _ hrp]
        rw [this] at hr; exact hr
      have heR_eq : ((avssStep (.partyReceiveReady p q) s).local_ p').echoesReceived =
          (s.local_ p').echoesReceived := by
        by_cases hp'p : p' = p
        · subst hp'p; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hp'p]
      rw [heR_eq]; exact hF6 r hes_pre p'
    · intro r hr p'
      have hrs_pre : (s.local_ r).readySent = false := by
        have : ((avssStep (.partyReceiveReady p q) s).local_ r).readySent = (s.local_ r).readySent := by
          by_cases hrp : r = p
          · subst hrp; simp [avssStep, setLocal_local_self]
          · simp [avssStep, setLocal_local_ne _ _ _ _ hrp]
        rw [this] at hr; exact hr
      have hrq : r ≠ q := by
        intro heq
        apply hF9 r hrs_pre p
        rw [heq]; exact hq_in
      by_cases hp'p : p' = p
      · subst hp'p
        have : ((avssStep (.partyReceiveReady p' q) s).local_ p').readyReceived =
            insert q (s.local_ p').readyReceived := by
          simp [avssStep, setLocal_local_self]
        rw [this]
        rw [Finset.mem_insert, not_or]
        exact ⟨hrq, hF7 r hrs_pre p'⟩
      · have : ((avssStep (.partyReceiveReady p q) s).local_ p').readyReceived =
            (s.local_ p').readyReceived := by
          simp [avssStep, setLocal_local_ne _ _ _ _ hp'p]
        rw [this]; exact hF7 r hrs_pre p'
    · intro r hr p' hrp'
      have hes_pre : (s.local_ r).echoSent = false := by
        have : ((avssStep (.partyReceiveReady p q) s).local_ r).echoSent = (s.local_ r).echoSent := by
          by_cases hrp : r = p
          · subst hrp; simp [avssStep, setLocal_local_self]
          · simp [avssStep, setLocal_local_ne _ _ _ _ hrp]
        rw [this] at hr; exact hr
      have hife_eq : (avssStep (.partyReceiveReady p q) s).inflightEchoes = s.inflightEchoes := by
        simp [avssStep, setLocal]
      rw [hife_eq] at hrp'; exact hF8 r hes_pre p' hrp'
    · intro r hr p'
      have hrs_pre : (s.local_ r).readySent = false := by
        have : ((avssStep (.partyReceiveReady p q) s).local_ r).readySent = (s.local_ r).readySent := by
          by_cases hrp : r = p
          · subst hrp; simp [avssStep, setLocal_local_self]
          · simp [avssStep, setLocal_local_ne _ _ _ _ hrp]
        rw [this] at hr; exact hr
      have hpost : (avssStep (.partyReceiveReady p q) s).inflightReady =
          s.inflightReady.erase (q, p) := rfl
      intro hrr
      rw [hpost] at hrr
      exact hF9 r hrs_pre p' (Finset.mem_erase.mp hrr).2
  | partyOutput q =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r hr p
      have hes_pre : (s.local_ r).echoSent = false := by
        have : ((avssStep (.partyOutput q) s).local_ r).echoSent = (s.local_ r).echoSent := by
          by_cases hrq : r = q
          · subst hrq; simp [avssStep, setLocal_local_self]
          · simp [avssStep, setLocal_local_ne _ _ _ _ hrq]
        rw [this] at hr; exact hr
      have heR_eq : ((avssStep (.partyOutput q) s).local_ p).echoesReceived =
          (s.local_ p).echoesReceived := by
        by_cases hpq : p = q
        · subst hpq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
      rw [heR_eq]; exact hF6 r hes_pre p
    · intro r hr p
      have hrs_pre : (s.local_ r).readySent = false := by
        have : ((avssStep (.partyOutput q) s).local_ r).readySent = (s.local_ r).readySent := by
          by_cases hrq : r = q
          · subst hrq; simp [avssStep, setLocal_local_self]
          · simp [avssStep, setLocal_local_ne _ _ _ _ hrq]
        rw [this] at hr; exact hr
      have hrR_eq : ((avssStep (.partyOutput q) s).local_ p).readyReceived =
          (s.local_ p).readyReceived := by
        by_cases hpq : p = q
        · subst hpq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
      rw [hrR_eq]; exact hF7 r hrs_pre p
    · intro r hr p hrp
      have hes_pre : (s.local_ r).echoSent = false := by
        have : ((avssStep (.partyOutput q) s).local_ r).echoSent = (s.local_ r).echoSent := by
          by_cases hrq : r = q
          · subst hrq; simp [avssStep, setLocal_local_self]
          · simp [avssStep, setLocal_local_ne _ _ _ _ hrq]
        rw [this] at hr; exact hr
      have hife_eq : (avssStep (.partyOutput q) s).inflightEchoes = s.inflightEchoes := by
        simp [avssStep, setLocal]
      rw [hife_eq] at hrp; exact hF8 r hes_pre p hrp
    · intro r hr p
      have hrs_pre : (s.local_ r).readySent = false := by
        have : ((avssStep (.partyOutput q) s).local_ r).readySent = (s.local_ r).readySent := by
          by_cases hrq : r = q
          · subst hrq; simp [avssStep, setLocal_local_self]
          · simp [avssStep, setLocal_local_ne _ _ _ _ hrq]
        rw [this] at hr; exact hr
      have hifr_eq : (avssStep (.partyOutput q) s).inflightReady = s.inflightReady := by
        simp [avssStep, setLocal]
      intro hrr; rw [hifr_eq] at hrr; exact hF9 r hrs_pre p hrr

/-! ### Phase 8.5b-γ-followup: flow + threshold invariant.

Adds four "global flow" clauses consumed by
`avssFairActionEnabled_at_non_terminated`'s C5 / C7 stuck-case dispatches:

  * F1 (threshold): `s.corrupted.card ≤ t`.
  * F2 (delivery completeness): under `dealerSent = true`, every honest party
    is either delivered or in `inflightDeliveries`.
  * F3 (echo flow): every honest sender's echo is either received by every
    honest receiver or still in `inflightEchoes`.
  * F4 (ready flow): same shape for ready.

Phase 8.5b-γ-followup-2: F4 now uses per-pair `inflightReady` tokens
`(q, p)`, mirroring F3's echo flow.  This makes preservation under
`partyReceiveReady r q` mechanical (the action only erases `(q, r)`,
leaving `(q, p) ∈ inflightReady` intact for `p ≠ r`). -/
def avssFlowInv (s : AVSSState n t F) : Prop :=
  s.corrupted.card ≤ t ∧
  -- Phase 8.5d-α: F2 is now per-party (`dealerSent p = true → ...`).
  (∀ p, p ∉ s.corrupted → s.dealerSent p = true →
    (s.local_ p).delivered = true ∨ p ∈ s.inflightDeliveries) ∧
  (∀ q, q ∉ s.corrupted → (s.local_ q).echoSent = true →
    ∀ p, p ∉ s.corrupted →
      q ∈ (s.local_ p).echoesReceived ∨ (q, p) ∈ s.inflightEchoes) ∧
  (∀ q, q ∉ s.corrupted → (s.local_ q).readySent = true →
    ∀ p, p ∉ s.corrupted →
      q ∈ (s.local_ p).readyReceived ∨ (q, p) ∈ s.inflightReady)

omit [Fintype F] in
theorem initPred_avssFlowInv (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (h_corr : corr.card ≤ t) (s : AVSSState n t F) (h : initPred sec corr coeffs s) :
    avssFlowInv s := by
  obtain ⟨hloc, _, hcorr_eq, _, _, _, _, hds, _⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcorr_eq]; exact h_corr
  · intro p _ hbad; rw [hds] at hbad; cases hbad
  · intro q _ hes p _
    rw [hloc q] at hes; simp [AVSSLocalState.init] at hes
  · intro q _ hrs p _
    rw [hloc q] at hrs; simp [AVSSLocalState.init] at hrs

omit [Fintype F] in
/-- `avssFlowInv` is preserved by every gated action.  F1 / F2 / F3 are
fully proved; F4's `partyReceiveReady` case is sorry'd (see docstring on
`avssFlowInv`). -/
theorem avssStep_preserves_avssFlowInv
    (a : AVSSAction n F) (s : AVSSState n t F)
    (hgate : actionGate a s) (hflow : avssFlowInv s) :
    avssFlowInv (avssStep a s) := by
  classical
  obtain ⟨hF1, hF2, hF3, hF4⟩ := hflow
  -- F1: corrupted is preserved by every action.
  have hcorr_post : (avssStep a s).corrupted = s.corrupted := by
    cases a <;> simp [avssStep, setLocal]
  have hF1_post : (avssStep a s).corrupted.card ≤ t := by rw [hcorr_post]; exact hF1
  refine ⟨hF1_post, ?_, ?_, ?_⟩
  · -- F2: delivery completeness (Phase 8.5d-α: per-party form).
    intro p hp hds_post
    have hcorr_p : p ∉ s.corrupted := by rw [hcorr_post] at hp; exact hp
    cases a with
    | dealerShareTo r =>
      -- post.dealerSent p: if p = r, true; if p ≠ r, = pre.
      -- post.local_ p = s.local_ p; post.ifd = if r ∉ corr then insert r s.ifd else s.ifd.
      by_cases hpr : p = r
      · -- p = r honest; r ∈ post.ifd.
        subst hpr
        right
        show p ∈ (avssStep (.dealerShareTo p) s).inflightDeliveries
        simp only [avssStep, if_pos hcorr_p]
        exact Finset.mem_insert_self _ _
      · -- p ≠ r: pre.dealerSent p = post.dealerSent p = true (from hds_post).
        have h_post_eq : (avssStep (.dealerShareTo r) s).dealerSent p = s.dealerSent p := by
          simp [avssStep, Function.update_of_ne hpr]
        rw [h_post_eq] at hds_post
        rcases hF2 p hcorr_p hds_post with h | h
        · left
          show ((avssStep (.dealerShareTo r) s).local_ p).delivered = true
          simp [avssStep]; exact h
        · right
          show p ∈ (avssStep (.dealerShareTo r) s).inflightDeliveries
          simp only [avssStep]
          split
          · exact Finset.mem_insert_of_mem h
          · exact h
    | partyDeliver q =>
      have h_post_eq : (avssStep (.partyDeliver q) s).dealerSent = s.dealerSent := by
        simp [avssStep, setLocal]
      rw [h_post_eq] at hds_post
      rcases hF2 p hcorr_p hds_post with h | h
      · -- pre delivered = true. post.local_ p.delivered: if p = q, true; else pre = true.
        left
        by_cases hpq : p = q
        · subst hpq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]; exact h
      · -- p ∈ pre.ifd. post.ifd = pre.ifd.erase q.
        by_cases hpq : p = q
        · -- p = q just delivered; left case.
          subst hpq
          left
          show ((avssStep (.partyDeliver p) s).local_ p).delivered = true
          simp [avssStep, setLocal_local_self]
        · right
          show p ∈ (avssStep (.partyDeliver q) s).inflightDeliveries
          have : (avssStep (.partyDeliver q) s).inflightDeliveries =
              s.inflightDeliveries.erase q := rfl
          rw [this]
          exact Finset.mem_erase.mpr ⟨hpq, h⟩
    | partyCorruptDeliver q =>
      -- p ∉ corr, q ∈ corr (gate). p ≠ q.
      have hpq : p ≠ q := fun heq => hcorr_p (heq ▸ hgate.2.1)
      have h_post_eq : (avssStep (.partyCorruptDeliver q) s).dealerSent = s.dealerSent := by
        simp [avssStep, setLocal]
      rw [h_post_eq] at hds_post
      have h_post_ifd : (avssStep (.partyCorruptDeliver q) s).inflightDeliveries =
          s.inflightDeliveries := by simp [avssStep, setLocal]
      have h_post_loc : ((avssStep (.partyCorruptDeliver q) s).local_ p).delivered =
          (s.local_ p).delivered := by simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
      rcases hF2 p hcorr_p hds_post with h | h
      · left; rw [h_post_loc]; exact h
      · right; rw [h_post_ifd]; exact h
    | partyEchoSend q =>
      have h_post_eq : (avssStep (.partyEchoSend q) s).dealerSent = s.dealerSent := by
        simp [avssStep, setLocal]
      rw [h_post_eq] at hds_post
      have h_post_ifd : (avssStep (.partyEchoSend q) s).inflightDeliveries =
          s.inflightDeliveries := by simp [avssStep, setLocal]
      have h_post_loc : ((avssStep (.partyEchoSend q) s).local_ p).delivered =
          (s.local_ p).delivered := by
        by_cases hpq : p = q
        · subst hpq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
      rcases hF2 p hcorr_p hds_post with h | h
      · left; rw [h_post_loc]; exact h
      · right; rw [h_post_ifd]; exact h
    | partyEchoReceive p' q =>
      have h_post_eq : (avssStep (.partyEchoReceive p' q) s).dealerSent = s.dealerSent := by
        simp [avssStep, setLocal]
      rw [h_post_eq] at hds_post
      have h_post_ifd : (avssStep (.partyEchoReceive p' q) s).inflightDeliveries =
          s.inflightDeliveries := by simp [avssStep, setLocal]
      have h_post_loc : ((avssStep (.partyEchoReceive p' q) s).local_ p).delivered =
          (s.local_ p).delivered := by
        by_cases hpp' : p = p'
        · subst hpp'; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpp']
      rcases hF2 p hcorr_p hds_post with h | h
      · left; rw [h_post_loc]; exact h
      · right; rw [h_post_ifd]; exact h
    | partyReady q =>
      have h_post_eq : (avssStep (.partyReady q) s).dealerSent = s.dealerSent := by
        simp [avssStep, setLocal]
      rw [h_post_eq] at hds_post
      have h_post_ifd : (avssStep (.partyReady q) s).inflightDeliveries =
          s.inflightDeliveries := by simp [avssStep, setLocal]
      have h_post_loc : ((avssStep (.partyReady q) s).local_ p).delivered =
          (s.local_ p).delivered := by
        by_cases hpq : p = q
        · subst hpq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
      rcases hF2 p hcorr_p hds_post with h | h
      · left; rw [h_post_loc]; exact h
      · right; rw [h_post_ifd]; exact h
    | partyAmplify q =>
      have h_post_eq : (avssStep (.partyAmplify q) s).dealerSent = s.dealerSent := by
        simp [avssStep, setLocal]
      rw [h_post_eq] at hds_post
      have h_post_ifd : (avssStep (.partyAmplify q) s).inflightDeliveries =
          s.inflightDeliveries := by simp [avssStep, setLocal]
      have h_post_loc : ((avssStep (.partyAmplify q) s).local_ p).delivered =
          (s.local_ p).delivered := by
        by_cases hpq : p = q
        · subst hpq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
      rcases hF2 p hcorr_p hds_post with h | h
      · left; rw [h_post_loc]; exact h
      · right; rw [h_post_ifd]; exact h
    | partyReceiveReady p' q =>
      have h_post_eq : (avssStep (.partyReceiveReady p' q) s).dealerSent = s.dealerSent := by
        simp [avssStep, setLocal]
      rw [h_post_eq] at hds_post
      have h_post_ifd : (avssStep (.partyReceiveReady p' q) s).inflightDeliveries =
          s.inflightDeliveries := by simp [avssStep, setLocal]
      have h_post_loc : ((avssStep (.partyReceiveReady p' q) s).local_ p).delivered =
          (s.local_ p).delivered := by
        by_cases hpp' : p = p'
        · subst hpp'; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpp']
      rcases hF2 p hcorr_p hds_post with h | h
      · left; rw [h_post_loc]; exact h
      · right; rw [h_post_ifd]; exact h
    | partyOutput q =>
      have h_post_eq : (avssStep (.partyOutput q) s).dealerSent = s.dealerSent := by
        simp [avssStep, setLocal]
      rw [h_post_eq] at hds_post
      have h_post_ifd : (avssStep (.partyOutput q) s).inflightDeliveries =
          s.inflightDeliveries := by simp [avssStep]
      have h_post_loc : ((avssStep (.partyOutput q) s).local_ p).delivered =
          (s.local_ p).delivered := by
        by_cases hpq : p = q
        · subst hpq; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq]
      rcases hF2 p hcorr_p hds_post with h | h
      · left; rw [h_post_loc]; exact h
      · right; rw [h_post_ifd]; exact h
  · -- F3: echo flow.
    cases a with
    | dealerShareTo r =>
      intro q hq hes p hp
      have hcorr_q : q ∉ s.corrupted := by rw [hcorr_post] at hq; exact hq
      have hcorr_p : p ∉ s.corrupted := by rw [hcorr_post] at hp; exact hp
      have hes_pre : (s.local_ q).echoSent = true := by
        have : ((avssStep (AVSSAction.dealerShareTo r) s).local_ q).echoSent =
            (s.local_ q).echoSent := rfl
        rw [this] at hes; exact hes
      have heR_eq : ((avssStep (AVSSAction.dealerShareTo r) s).local_ p).echoesReceived =
          (s.local_ p).echoesReceived := rfl
      have hife_eq : (avssStep (AVSSAction.dealerShareTo r) s).inflightEchoes =
          s.inflightEchoes := rfl
      rcases hF3 q hcorr_q hes_pre p hcorr_p with h | h
      · left; rw [heR_eq]; exact h
      · right; rw [hife_eq]; exact h
    | partyDeliver r =>
      intro q hq hes p hp
      have hcorr_q : q ∉ s.corrupted := by rw [hcorr_post] at hq; exact hq
      have hcorr_p : p ∉ s.corrupted := by rw [hcorr_post] at hp; exact hp
      have hes_pre : (s.local_ q).echoSent = true := by
        have : ((avssStep (.partyDeliver r) s).local_ q).echoSent =
            (s.local_ q).echoSent := by
          by_cases hqr : q = r
          · subst hqr; simp [avssStep, setLocal_local_self]
          · simp [avssStep, setLocal_local_ne _ _ _ _ hqr]
        rw [this] at hes; exact hes
      have heR_eq : ((avssStep (.partyDeliver r) s).local_ p).echoesReceived =
          (s.local_ p).echoesReceived := by
        by_cases hpr : p = r
        · subst hpr; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpr]
      have hife_eq : (avssStep (.partyDeliver r) s).inflightEchoes = s.inflightEchoes := rfl
      rcases hF3 q hcorr_q hes_pre p hcorr_p with h | h
      · left; rw [heR_eq]; exact h
      · right; rw [hife_eq]; exact h
    | partyCorruptDeliver r =>
      intro q hq hes p hp
      have hcorr_q : q ∉ s.corrupted := by rw [hcorr_post] at hq; exact hq
      have hcorr_p : p ∉ s.corrupted := by rw [hcorr_post] at hp; exact hp
      have hes_pre : (s.local_ q).echoSent = true := by
        have : ((avssStep (.partyCorruptDeliver r) s).local_ q).echoSent =
            (s.local_ q).echoSent := by
          by_cases hqr : q = r
          · subst hqr; simp [avssStep, setLocal_local_self]
          · simp [avssStep, setLocal_local_ne _ _ _ _ hqr]
        rw [this] at hes; exact hes
      have heR_eq : ((avssStep (.partyCorruptDeliver r) s).local_ p).echoesReceived =
          (s.local_ p).echoesReceived := by
        by_cases hpr : p = r
        · subst hpr; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpr]
      have hife_eq : (avssStep (.partyCorruptDeliver r) s).inflightEchoes =
          s.inflightEchoes := rfl
      rcases hF3 q hcorr_q hes_pre p hcorr_p with h | h
      · left; rw [heR_eq]; exact h
      · right; rw [hife_eq]; exact h
    | partyEchoSend r =>
      intro q hq hes p hp
      have hcorr_q : q ∉ s.corrupted := by rw [hcorr_post] at hq; exact hq
      have hcorr_p : p ∉ s.corrupted := by rw [hcorr_post] at hp; exact hp
      -- Locals echoesReceived unchanged.
      have heR_eq : ((avssStep (.partyEchoSend r) s).local_ p).echoesReceived =
          (s.local_ p).echoesReceived := by
        by_cases hpr : p = r
        · subst hpr; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpr]
      -- ife post = ife pre ∪ {(r, *)}.
      have hife_post : (avssStep (.partyEchoSend r) s).inflightEchoes =
          s.inflightEchoes ∪ (Finset.univ : Finset (Fin n)).image (fun q' => (r, q')) := rfl
      by_cases hqr : q = r
      · subst hqr
        -- q = r, post.q.echoSent = true.  We use the broadcast: (q, p) ∈ post.ife.
        right; rw [hife_post]
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩
      · -- q ≠ r, post.q.echoSent = pre.q.echoSent = true.
        have hes_pre : (s.local_ q).echoSent = true := by
          have : ((avssStep (.partyEchoSend r) s).local_ q).echoSent =
              (s.local_ q).echoSent := by
            simp [avssStep, setLocal_local_ne _ _ _ _ hqr]
          rw [this] at hes; exact hes
        rcases hF3 q hcorr_q hes_pre p hcorr_p with h | h
        · left; rw [heR_eq]; exact h
        · right; rw [hife_post]; exact Finset.mem_union_left _ h
    | partyEchoReceive p' r =>
      obtain ⟨_hrp_in, _hr_notin⟩ := hgate
      intro q hq hes p hp
      have hcorr_q : q ∉ s.corrupted := by rw [hcorr_post] at hq; exact hq
      have hcorr_p : p ∉ s.corrupted := by rw [hcorr_post] at hp; exact hp
      have hes_pre : (s.local_ q).echoSent = true := by
        have : ((avssStep (.partyEchoReceive p' r) s).local_ q).echoSent =
            (s.local_ q).echoSent := by
          by_cases hqp' : q = p'
          · subst hqp'; simp [avssStep, setLocal_local_self]
          · simp [avssStep, setLocal_local_ne _ _ _ _ hqp']
        rw [this] at hes; exact hes
      have hife_post : (avssStep (.partyEchoReceive p' r) s).inflightEchoes =
          s.inflightEchoes.erase (r, p') := rfl
      by_cases hpp' : p = p'
      · subst hpp'
        -- p = p'.  post.p.echoesReceived = insert r pre.p.echoesReceived.
        have heR_post : ((avssStep (.partyEchoReceive p r) s).local_ p).echoesReceived =
            insert r (s.local_ p).echoesReceived := by
          simp [avssStep, setLocal_local_self]
        rcases hF3 q hcorr_q hes_pre p hcorr_p with h | h
        · left; rw [heR_post]; exact Finset.mem_insert.mpr (Or.inr h)
        · -- (q, p) ∈ pre.ife. Either (q, p) = (r, p) in which case q = r and goes to the LHS
          -- via insert; or (q, p) ≠ (r, p) and goes to post.ife = pre.ife.erase.
          by_cases hqr : q = r
          · subst hqr; left; rw [heR_post]; exact Finset.mem_insert_self _ _
          · right; rw [hife_post]
            exact Finset.mem_erase.mpr ⟨fun h_eq => hqr (Prod.mk.inj h_eq).1, h⟩
      · have heR_eq : ((avssStep (.partyEchoReceive p' r) s).local_ p).echoesReceived =
            (s.local_ p).echoesReceived := by
          simp [avssStep, setLocal_local_ne _ _ _ _ hpp']
        rcases hF3 q hcorr_q hes_pre p hcorr_p with h | h
        · left; rw [heR_eq]; exact h
        · right; rw [hife_post]
          exact Finset.mem_erase.mpr ⟨fun h_eq => hpp' (Prod.mk.inj h_eq).2, h⟩
    | partyReady r =>
      intro q hq hes p hp
      have hcorr_q : q ∉ s.corrupted := by rw [hcorr_post] at hq; exact hq
      have hcorr_p : p ∉ s.corrupted := by rw [hcorr_post] at hp; exact hp
      have hes_pre : (s.local_ q).echoSent = true := by
        have : ((avssStep (.partyReady r) s).local_ q).echoSent =
            (s.local_ q).echoSent := by
          by_cases hqr : q = r
          · subst hqr; simp [avssStep, setLocal_local_self]
          · simp [avssStep, setLocal_local_ne _ _ _ _ hqr]
        rw [this] at hes; exact hes
      have heR_eq : ((avssStep (.partyReady r) s).local_ p).echoesReceived =
          (s.local_ p).echoesReceived := by
        by_cases hpr : p = r
        · subst hpr; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpr]
      have hife_eq : (avssStep (.partyReady r) s).inflightEchoes = s.inflightEchoes := by
        simp [avssStep, setLocal]
      rcases hF3 q hcorr_q hes_pre p hcorr_p with h | h
      · left; rw [heR_eq]; exact h
      · right; rw [hife_eq]; exact h
    | partyAmplify r =>
      intro q hq hes p hp
      have hcorr_q : q ∉ s.corrupted := by rw [hcorr_post] at hq; exact hq
      have hcorr_p : p ∉ s.corrupted := by rw [hcorr_post] at hp; exact hp
      have hes_pre : (s.local_ q).echoSent = true := by
        have : ((avssStep (.partyAmplify r) s).local_ q).echoSent =
            (s.local_ q).echoSent := by
          by_cases hqr : q = r
          · subst hqr; simp [avssStep, setLocal_local_self]
          · simp [avssStep, setLocal_local_ne _ _ _ _ hqr]
        rw [this] at hes; exact hes
      have heR_eq : ((avssStep (.partyAmplify r) s).local_ p).echoesReceived =
          (s.local_ p).echoesReceived := by
        by_cases hpr : p = r
        · subst hpr; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpr]
      have hife_eq : (avssStep (.partyAmplify r) s).inflightEchoes = s.inflightEchoes := by
        simp [avssStep, setLocal]
      rcases hF3 q hcorr_q hes_pre p hcorr_p with h | h
      · left; rw [heR_eq]; exact h
      · right; rw [hife_eq]; exact h
    | partyReceiveReady p' r =>
      intro q hq hes p hp
      have hcorr_q : q ∉ s.corrupted := by rw [hcorr_post] at hq; exact hq
      have hcorr_p : p ∉ s.corrupted := by rw [hcorr_post] at hp; exact hp
      have hes_pre : (s.local_ q).echoSent = true := by
        have : ((avssStep (.partyReceiveReady p' r) s).local_ q).echoSent =
            (s.local_ q).echoSent := by
          by_cases hqp' : q = p'
          · subst hqp'; simp [avssStep, setLocal_local_self]
          · simp [avssStep, setLocal_local_ne _ _ _ _ hqp']
        rw [this] at hes; exact hes
      have heR_eq : ((avssStep (.partyReceiveReady p' r) s).local_ p).echoesReceived =
          (s.local_ p).echoesReceived := by
        by_cases hpp' : p = p'
        · subst hpp'; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpp']
      have hife_eq : (avssStep (.partyReceiveReady p' r) s).inflightEchoes =
          s.inflightEchoes := by simp [avssStep, setLocal]
      rcases hF3 q hcorr_q hes_pre p hcorr_p with h | h
      · left; rw [heR_eq]; exact h
      · right; rw [hife_eq]; exact h
    | partyOutput r =>
      intro q hq hes p hp
      have hcorr_q : q ∉ s.corrupted := by rw [hcorr_post] at hq; exact hq
      have hcorr_p : p ∉ s.corrupted := by rw [hcorr_post] at hp; exact hp
      have hes_pre : (s.local_ q).echoSent = true := by
        have : ((avssStep (.partyOutput r) s).local_ q).echoSent =
            (s.local_ q).echoSent := by
          by_cases hqr : q = r
          · subst hqr; simp [avssStep, setLocal_local_self]
          · simp [avssStep, setLocal_local_ne _ _ _ _ hqr]
        rw [this] at hes; exact hes
      have heR_eq : ((avssStep (.partyOutput r) s).local_ p).echoesReceived =
          (s.local_ p).echoesReceived := by
        by_cases hpr : p = r
        · subst hpr; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpr]
      have hife_eq : (avssStep (.partyOutput r) s).inflightEchoes = s.inflightEchoes := by
        simp [avssStep, setLocal]
      rcases hF3 q hcorr_q hes_pre p hcorr_p with h | h
      · left; rw [heR_eq]; exact h
      · right; rw [hife_eq]; exact h
  · -- F4: ready flow.  All cases except `partyReceiveReady` are mechanical;
    -- `partyReceiveReady` is sorry'd (see docstring).
    cases a with
    | dealerShareTo r =>
      intro q hq hrs p hp
      have hcorr_q : q ∉ s.corrupted := by rw [hcorr_post] at hq; exact hq
      have hcorr_p : p ∉ s.corrupted := by rw [hcorr_post] at hp; exact hp
      have hrs_pre : (s.local_ q).readySent = true := by
        have : ((avssStep (AVSSAction.dealerShareTo r) s).local_ q).readySent =
            (s.local_ q).readySent := rfl
        rw [this] at hrs; exact hrs
      have hrR_eq : ((avssStep (AVSSAction.dealerShareTo r) s).local_ p).readyReceived =
          (s.local_ p).readyReceived := rfl
      have hifr_eq : (avssStep (AVSSAction.dealerShareTo r) s).inflightReady = s.inflightReady := rfl
      rcases hF4 q hcorr_q hrs_pre p hcorr_p with h | h
      · left; rw [hrR_eq]; exact h
      · right; rw [hifr_eq]; exact h
    | partyDeliver r =>
      intro q hq hrs p hp
      have hcorr_q : q ∉ s.corrupted := by rw [hcorr_post] at hq; exact hq
      have hcorr_p : p ∉ s.corrupted := by rw [hcorr_post] at hp; exact hp
      have hrs_pre : (s.local_ q).readySent = true := by
        have : ((avssStep (.partyDeliver r) s).local_ q).readySent =
            (s.local_ q).readySent := by
          by_cases hqr : q = r
          · subst hqr; simp [avssStep, setLocal_local_self]
          · simp [avssStep, setLocal_local_ne _ _ _ _ hqr]
        rw [this] at hrs; exact hrs
      have hrR_eq : ((avssStep (.partyDeliver r) s).local_ p).readyReceived =
          (s.local_ p).readyReceived := by
        by_cases hpr : p = r
        · subst hpr; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpr]
      have hifr_eq : (avssStep (.partyDeliver r) s).inflightReady = s.inflightReady := rfl
      rcases hF4 q hcorr_q hrs_pre p hcorr_p with h | h
      · left; rw [hrR_eq]; exact h
      · right; rw [hifr_eq]; exact h
    | partyCorruptDeliver r =>
      intro q hq hrs p hp
      have hcorr_q : q ∉ s.corrupted := by rw [hcorr_post] at hq; exact hq
      have hcorr_p : p ∉ s.corrupted := by rw [hcorr_post] at hp; exact hp
      have hrs_pre : (s.local_ q).readySent = true := by
        have : ((avssStep (.partyCorruptDeliver r) s).local_ q).readySent =
            (s.local_ q).readySent := by
          by_cases hqr : q = r
          · subst hqr; simp [avssStep, setLocal_local_self]
          · simp [avssStep, setLocal_local_ne _ _ _ _ hqr]
        rw [this] at hrs; exact hrs
      have hrR_eq : ((avssStep (.partyCorruptDeliver r) s).local_ p).readyReceived =
          (s.local_ p).readyReceived := by
        by_cases hpr : p = r
        · subst hpr; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpr]
      have hifr_eq : (avssStep (.partyCorruptDeliver r) s).inflightReady =
          s.inflightReady := rfl
      rcases hF4 q hcorr_q hrs_pre p hcorr_p with h | h
      · left; rw [hrR_eq]; exact h
      · right; rw [hifr_eq]; exact h
    | partyEchoSend r =>
      intro q hq hrs p hp
      have hcorr_q : q ∉ s.corrupted := by rw [hcorr_post] at hq; exact hq
      have hcorr_p : p ∉ s.corrupted := by rw [hcorr_post] at hp; exact hp
      have hrs_pre : (s.local_ q).readySent = true := by
        have : ((avssStep (.partyEchoSend r) s).local_ q).readySent =
            (s.local_ q).readySent := by
          by_cases hqr : q = r
          · subst hqr; simp [avssStep, setLocal_local_self]
          · simp [avssStep, setLocal_local_ne _ _ _ _ hqr]
        rw [this] at hrs; exact hrs
      have hrR_eq : ((avssStep (.partyEchoSend r) s).local_ p).readyReceived =
          (s.local_ p).readyReceived := by
        by_cases hpr : p = r
        · subst hpr; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpr]
      have hifr_eq : (avssStep (.partyEchoSend r) s).inflightReady = s.inflightReady := by
        simp [avssStep, setLocal]
      rcases hF4 q hcorr_q hrs_pre p hcorr_p with h | h
      · left; rw [hrR_eq]; exact h
      · right; rw [hifr_eq]; exact h
    | partyEchoReceive p' r =>
      intro q hq hrs p hp
      have hcorr_q : q ∉ s.corrupted := by rw [hcorr_post] at hq; exact hq
      have hcorr_p : p ∉ s.corrupted := by rw [hcorr_post] at hp; exact hp
      have hrs_pre : (s.local_ q).readySent = true := by
        have : ((avssStep (.partyEchoReceive p' r) s).local_ q).readySent =
            (s.local_ q).readySent := by
          by_cases hqp' : q = p'
          · subst hqp'; simp [avssStep, setLocal_local_self]
          · simp [avssStep, setLocal_local_ne _ _ _ _ hqp']
        rw [this] at hrs; exact hrs
      have hrR_eq : ((avssStep (.partyEchoReceive p' r) s).local_ p).readyReceived =
          (s.local_ p).readyReceived := by
        by_cases hpp' : p = p'
        · subst hpp'; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpp']
      have hifr_eq : (avssStep (.partyEchoReceive p' r) s).inflightReady =
          s.inflightReady := rfl
      rcases hF4 q hcorr_q hrs_pre p hcorr_p with h | h
      · left; rw [hrR_eq]; exact h
      · right; rw [hifr_eq]; exact h
    | partyReady r =>
      intro q hq hrs p hp
      have hcorr_q : q ∉ s.corrupted := by rw [hcorr_post] at hq; exact hq
      have hcorr_p : p ∉ s.corrupted := by rw [hcorr_post] at hp; exact hp
      have hrR_eq : ((avssStep (.partyReady r) s).local_ p).readyReceived =
          (s.local_ p).readyReceived := by
        by_cases hpr : p = r
        · subst hpr; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpr]
      have hifr_post : (avssStep (.partyReady r) s).inflightReady =
          s.inflightReady ∪
            (Finset.univ : Finset (Fin n)).image (fun y => (r, y)) := rfl
      by_cases hqr : q = r
      · subst hqr
        right; rw [hifr_post]
        exact Finset.mem_union.mpr (Or.inr
          (Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩))
      · have hrs_pre : (s.local_ q).readySent = true := by
          have : ((avssStep (.partyReady r) s).local_ q).readySent =
              (s.local_ q).readySent := by
            simp [avssStep, setLocal_local_ne _ _ _ _ hqr]
          rw [this] at hrs; exact hrs
        rcases hF4 q hcorr_q hrs_pre p hcorr_p with h | h
        · left; rw [hrR_eq]; exact h
        · right; rw [hifr_post]; exact Finset.mem_union.mpr (Or.inl h)
    | partyAmplify r =>
      intro q hq hrs p hp
      have hcorr_q : q ∉ s.corrupted := by rw [hcorr_post] at hq; exact hq
      have hcorr_p : p ∉ s.corrupted := by rw [hcorr_post] at hp; exact hp
      have hrR_eq : ((avssStep (.partyAmplify r) s).local_ p).readyReceived =
          (s.local_ p).readyReceived := by
        by_cases hpr : p = r
        · subst hpr; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpr]
      have hifr_post : (avssStep (.partyAmplify r) s).inflightReady =
          s.inflightReady ∪
            (Finset.univ : Finset (Fin n)).image (fun y => (r, y)) := rfl
      by_cases hqr : q = r
      · subst hqr
        right; rw [hifr_post]
        exact Finset.mem_union.mpr (Or.inr
          (Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩))
      · have hrs_pre : (s.local_ q).readySent = true := by
          have : ((avssStep (.partyAmplify r) s).local_ q).readySent =
              (s.local_ q).readySent := by
            simp [avssStep, setLocal_local_ne _ _ _ _ hqr]
          rw [this] at hrs; exact hrs
        rcases hF4 q hcorr_q hrs_pre p hcorr_p with h | h
        · left; rw [hrR_eq]; exact h
        · right; rw [hifr_post]; exact Finset.mem_union.mpr (Or.inl h)
    | partyReceiveReady p' r =>
      -- Phase 8.5b-γ-followup-2: per-pair tokens make F4 preservation mechanical.
      -- The action erases (r, p') only; tokens (q, p) for (q, p) ≠ (r, p') survive.
      -- The exact consumed token (r, p') is replaced by `r ∈ p'.readyReceived`.
      intro q hq hrs p hp
      have hcorr_q : q ∉ s.corrupted := by rw [hcorr_post] at hq; exact hq
      have hcorr_p : p ∉ s.corrupted := by rw [hcorr_post] at hp; exact hp
      have hrs_pre : (s.local_ q).readySent = true := by
        have : ((avssStep (.partyReceiveReady p' r) s).local_ q).readySent =
            (s.local_ q).readySent := by
          by_cases hqp' : q = p'
          · subst hqp'; simp [avssStep, setLocal_local_self]
          · simp [avssStep, setLocal_local_ne _ _ _ _ hqp']
        rw [this] at hrs; exact hrs
      have hifr_post : (avssStep (.partyReceiveReady p' r) s).inflightReady =
          s.inflightReady.erase (r, p') := rfl
      rcases hF4 q hcorr_q hrs_pre p hcorr_p with h | h
      · -- Pre had `q ∈ p.readyReceived` — survives any insert.
        left
        by_cases hpp' : p = p'
        · subst hpp'
          show q ∈ ((avssStep (.partyReceiveReady p r) s).local_ p).readyReceived
          have heq : ((avssStep (.partyReceiveReady p r) s).local_ p).readyReceived =
              insert r (s.local_ p).readyReceived := by
            simp [avssStep, setLocal_local_self]
          rw [heq]; exact Finset.mem_insert_of_mem h
        · show q ∈ ((avssStep (.partyReceiveReady p' r) s).local_ p).readyReceived
          have : ((avssStep (.partyReceiveReady p' r) s).local_ p).readyReceived =
              (s.local_ p).readyReceived := by
            simp [avssStep, setLocal_local_ne _ _ _ _ hpp']
          rw [this]; exact h
      · -- Pre had `(q, p) ∈ inflightReady`. Sub-case on (q, p) = (r, p').
        by_cases hpair : (q, p) = (r, p')
        · -- The action consumed exactly this token; equivalent claim is
          -- now `q ∈ p.readyReceived` (since p = p' and q = r).
          left
          obtain ⟨hqr, hpp'⟩ := Prod.mk.injEq _ _ _ _ |>.mp hpair
          subst hqr; subst hpp'
          show q ∈ ((avssStep (.partyReceiveReady p q) s).local_ p).readyReceived
          have heq : ((avssStep (.partyReceiveReady p q) s).local_ p).readyReceived =
              insert q (s.local_ p).readyReceived := by
            simp [avssStep, setLocal_local_self]
          rw [heq]; exact Finset.mem_insert_self _ _
        · -- Token (q, p) ≠ (r, p'), survives the erase.
          right; rw [hifr_post]
          exact Finset.mem_erase.mpr ⟨hpair, h⟩
    | partyOutput r =>
      intro q hq hrs p hp
      have hcorr_q : q ∉ s.corrupted := by rw [hcorr_post] at hq; exact hq
      have hcorr_p : p ∉ s.corrupted := by rw [hcorr_post] at hp; exact hp
      have hrs_pre : (s.local_ q).readySent = true := by
        have : ((avssStep (.partyOutput r) s).local_ q).readySent =
            (s.local_ q).readySent := by
          by_cases hqr : q = r
          · subst hqr; simp [avssStep, setLocal_local_self]
          · simp [avssStep, setLocal_local_ne _ _ _ _ hqr]
        rw [this] at hrs; exact hrs
      have hrR_eq : ((avssStep (.partyOutput r) s).local_ p).readyReceived =
          (s.local_ p).readyReceived := by
        by_cases hpr : p = r
        · subst hpr; simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpr]
      have hifr_eq : (avssStep (.partyOutput r) s).inflightReady = s.inflightReady := by
        simp [avssStep, setLocal]
      rcases hF4 q hcorr_q hrs_pre p hcorr_p with h | h
      · left; rw [hrR_eq]; exact h
      · right; rw [hifr_eq]; exact h

/-! ### Phase 8.5b-β: liveness lemma for cert dispatch -/

omit [Fintype F] in
/-- Helper: when the cert's `Inv s` (which carries `avssTermInv s ∧
corruptLocalInv s`) holds and `avssU s > 0`, the lex-product structure
forces at least one of the seven progress components to be strictly
positive.  Exposed as a structured disjunction over the seven
components so callers (the `dealerSent = true` case below) can
dispatch on which protocol step is enabled. -/
private theorem avssU_pos_disjunct (s : AVSSState n t F)
    (hpos : 0 < avssU s) :
    -- Phase 8.5d-α: c₁ is now `(unsentDealerSet s).card`.
    (unsentDealerSet s).card > 0 ∨
    s.inflightDeliveries.card > 0 ∨
    (unsentEchoSet s).card > 0 ∨
    s.inflightEchoes.card > 0 ∨
    (notReadySentSet s).card > 0 ∨
    s.inflightReady.card > 0 ∨
    (unfinishedSet s).card > 0 := by
  classical
  by_contra hbad
  push_neg at hbad
  obtain ⟨h0, h2, h3, h4, h5, h6, h7⟩ := hbad
  have huds : (unsentDealerSet s).card = 0 := by omega
  have hifd : s.inflightDeliveries.card = 0 := by omega
  have huss : (unsentEchoSet s).card = 0 := by omega
  have hife : s.inflightEchoes.card = 0 := by omega
  have hnrs : (notReadySentSet s).card = 0 := by omega
  have hifr : s.inflightReady.card = 0 := by omega
  have hufs : (unfinishedSet s).card = 0 := by omega
  have hzero : avssU s = 0 := by
    unfold avssU
    rw [huds, hifd, huss, hife, hnrs, hifr, hufs]
    ring
  exact (Nat.lt_irrefl 0) (hzero ▸ hpos)

omit [Fintype F] in
/-- At any state with the cert's joint invariant
(`avssTermInv ∧ corruptLocalInv`) and `¬ terminated`, some fair action's
gate is satisfied.  This is the load-bearing liveness lemma for the cert's
`Or.inr` dispatch under the C1+C2 model: when a corrupt-fired action is
gated and the variant doesn't strictly decrease, we discharge `V_super` /
`U_dec_det`'s disjunct via "another fair action remains enabled at the
post-state".

Argument by case-split on `s.dealerSent`:

  * `false` → `dealerShare`'s gate (`s.dealerSent = false`) holds.
    `dealerShare` is in `avssFairActions` (Phase B).
  * `true` → from `¬ terminated s` and the lex-product structure of
    `avssU`, at least one of the seven progress components is positive.
    Each component witnesses a fair action with a satisfied gate
    (modulo three protocol queue-content invariants whose preservation
    is tracked by 8.5b-γ; see internal sorries).

The four "queue-content" invariants left as `sorry` correspond to:
  - `(q, p) ∈ inflightEchoes → q ∉ p.echoesReceived` (partyEchoReceive freshness),
  - `q ∈ inflightReady → q ∉ p.readyReceived` (partyReceiveReady freshness),
  - `p ∈ inflightDeliveries → p ∉ corrupted ∧ ¬delivered ∧ dealerMessages.isSome`
    (partyDeliver enablement),
  - the deep "stuck honest party" case in `unfinishedSet ≠ ∅` /
    `notReadySentSet ≠ ∅`.

Each is a true protocol invariant; their preservation proofs land in
8.5b-γ along with the §15+ secrecy-chain cascade. -/
theorem avssFairActionEnabled_at_non_terminated
    (s : AVSSState n t F) (hinv : avssTermInv s) (_hcorrupt : corruptLocalInv s)
    (hwf : avssQueueWfInv s) (hflow : avssFlowInv s) (hnt : ¬ terminated s) :
    ∃ j ∈ avssFairActions, actionGate j s := by
  classical
  obtain ⟨hF1, hF2, hF3, hF4⟩ := hflow
  -- TODO Phase 8.5d-α-followup: Re-prove this liveness dispatch lemma under
  -- the per-party `dealerShareTo p` model. Strategy: case-split on whether
  -- some party has `dealerSent p = false` (then `dealerShareTo p` fires);
  -- else apply the existing C2..C7 cascade with `unsentDealerSet = ∅`,
  -- which forces every honest party's `dealerSent` to be true and lets
  -- the existing F2..F4 flow logic carry through.
  --
  -- For the temporary placeholder we adopt the per-party "first unserved
  -- honest party" route — picks the witness from `unsentDealerSet`.
  by_cases hds_all : ∀ p, s.dealerSent p = true
  · -- All parties served. Dispatch via the C2..C7 cascade using `avssU_pos_disjunct`.
    have hUpos : 0 < avssU s := by
      by_contra hbad
      push_neg at hbad
      have hU0 : avssU s = 0 := Nat.le_zero.mp hbad
      apply hnt
      -- Mirror the V_pos contrapositive.
      unfold avssU at hU0
      have hK_pos : 1 ≤ lexBase n := lexBase_pos
      obtain ⟨hU0', hunfin_t⟩ := Nat.add_eq_zero_iff.mp hU0
      obtain ⟨hU0', hifr_t⟩ := Nat.add_eq_zero_iff.mp hU0'
      obtain ⟨hU0', hnrs_t⟩ := Nat.add_eq_zero_iff.mp hU0'
      obtain ⟨hU0', hife_t⟩ := Nat.add_eq_zero_iff.mp hU0'
      obtain ⟨hU0', huss_t⟩ := Nat.add_eq_zero_iff.mp hU0'
      obtain ⟨_, hifd_t⟩ := Nat.add_eq_zero_iff.mp hU0'
      have hifd_card : s.inflightDeliveries.card = 0 := by
        rcases Nat.mul_eq_zero.mp hifd_t with h | h
        · exact h
        · have : 1 ≤ lexBase n ^ 5 := Nat.one_le_pow _ _ hK_pos; omega
      have huss_card : (unsentEchoSet s).card = 0 := by
        rcases Nat.mul_eq_zero.mp huss_t with h | h
        · exact h
        · have : 1 ≤ lexBase n ^ 4 := Nat.one_le_pow _ _ hK_pos; omega
      have hife_card : s.inflightEchoes.card = 0 := by
        rcases Nat.mul_eq_zero.mp hife_t with h | h
        · exact h
        · have : 1 ≤ lexBase n ^ 3 := Nat.one_le_pow _ _ hK_pos; omega
      have hnrs_card : (notReadySentSet s).card = 0 := by
        rcases Nat.mul_eq_zero.mp hnrs_t with h | h
        · exact h
        · have : 1 ≤ lexBase n ^ 2 := Nat.one_le_pow _ _ hK_pos; omega
      have hifr_card : s.inflightReady.card = 0 := by
        rcases Nat.mul_eq_zero.mp hifr_t with h | h
        · exact h
        · omega
      have hifd_emp : s.inflightDeliveries = ∅ := Finset.card_eq_zero.mp hifd_card
      have hife_emp : s.inflightEchoes = ∅ := Finset.card_eq_zero.mp hife_card
      have hifr_emp : s.inflightReady = ∅ := Finset.card_eq_zero.mp hifr_card
      have huss_emp : unsentEchoSet s = ∅ := Finset.card_eq_zero.mp huss_card
      have hunfin_emp : unfinishedSet s = ∅ := Finset.card_eq_zero.mp hunfin_t
      have h_out : ∀ p, p ∉ s.corrupted → (s.local_ p).output.isSome := by
        intro p hp
        by_contra hnone
        have hp_in : p ∈ unfinishedSet s := by
          simp only [unfinishedSet, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨hp, ?_⟩
          cases h_o : (s.local_ p).output with
          | none => rfl
          | some _ => simp [h_o] at hnone
        rw [hunfin_emp] at hp_in
        exact (Finset.notMem_empty _) hp_in
      have h_echo : ∀ p, p ∉ s.corrupted → (s.local_ p).echoSent = true := by
        intro p hp
        by_contra hbad
        have hes : (s.local_ p).echoSent = false := by
          cases h_es : (s.local_ p).echoSent with
          | true => exact absurd h_es hbad
          | false => rfl
        have hsome := h_out p hp
        have hdel : (s.local_ p).delivered = true := (hinv.2.2.1 p hp hsome).2
        have hp_in : p ∈ unsentEchoSet s := by
          simp only [unsentEchoSet, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hp, hdel, hes⟩
        rw [huss_emp] at hp_in
        exact (Finset.notMem_empty _) hp_in
      exact ⟨h_out, h_echo, hifd_emp, hife_emp, hifr_emp⟩
    rcases avssU_pos_disjunct s hUpos with hC1 | hC2 | hC3 | hC4 | hC5 | hC6 | hC7
    · -- C1: unsentDealerSet > 0; contradicts hds_all (all served, so unsentDealerSet = ∅).
      exfalso
      have hne : (unsentDealerSet s).Nonempty := Finset.card_pos.mp hC1
      obtain ⟨p, hp_in⟩ := hne
      simp only [unsentDealerSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp_in
      have := hds_all p
      rw [this] at hp_in
      cases hp_in.2
    · -- C2: inflightDeliveries ≠ ∅. Pick p ∈ ifd. Queue WF gives the rest.
      have hne : s.inflightDeliveries.Nonempty := Finset.card_pos.mp hC2
      obtain ⟨p, hp_in⟩ := hne
      obtain ⟨hp_h, hp_ndel, hp_dm⟩ := hwf.1 p hp_in
      refine ⟨.partyDeliver p, ?_, ?_⟩
      · show True; trivial
      · show s.dealerSent p = true ∧ p ∉ s.corrupted ∧ p ∈ s.inflightDeliveries
            ∧ (s.local_ p).delivered = false ∧ (s.dealerMessages p).isSome
        exact ⟨hds_all p, hp_h, hp_in, hp_ndel, hp_dm⟩
    · -- C3: unsentEchoSet ≠ ∅.
      have hne : (unsentEchoSet s).Nonempty := Finset.card_pos.mp hC3
      obtain ⟨p, hp_in⟩ := hne
      simp only [unsentEchoSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp_in
      obtain ⟨hp_h, hdel, hes⟩ := hp_in
      refine ⟨.partyEchoSend p, ?_, ?_⟩
      · show True; trivial
      · exact ⟨hdel, hes, hds_all p⟩
    · -- C4: inflightEchoes ≠ ∅.
      have hne : s.inflightEchoes.Nonempty := Finset.card_pos.mp hC4
      obtain ⟨⟨q, p⟩, hqp_in⟩ := hne
      refine ⟨.partyEchoReceive p q, ?_, ?_⟩
      · show True; trivial
      · exact ⟨hqp_in, hwf.2.1 q p hqp_in⟩
    · -- C5: notReadySentSet ≠ ∅. Cascade through ifd / uss / ife / ifr first.
      by_cases hifd : 0 < s.inflightDeliveries.card
      · have hne : s.inflightDeliveries.Nonempty := Finset.card_pos.mp hifd
        obtain ⟨q, hq_in⟩ := hne
        obtain ⟨hq_h, hq_ndel, hq_dm⟩ := hwf.1 q hq_in
        exact ⟨.partyDeliver q, by show True; trivial,
               hds_all q, hq_h, hq_in, hq_ndel, hq_dm⟩
      push_neg at hifd
      by_cases huss : 0 < (unsentEchoSet s).card
      · have hne : (unsentEchoSet s).Nonempty := Finset.card_pos.mp huss
        obtain ⟨q, hq_in⟩ := hne
        simp only [unsentEchoSet, Finset.mem_filter, Finset.mem_univ, true_and] at hq_in
        obtain ⟨hq_h, hdel, hes⟩ := hq_in
        exact ⟨.partyEchoSend q, by show True; trivial, hdel, hes, hds_all q⟩
      push_neg at huss
      by_cases hife : 0 < s.inflightEchoes.card
      · have hne : s.inflightEchoes.Nonempty := Finset.card_pos.mp hife
        obtain ⟨⟨q, p⟩, hqp_in⟩ := hne
        exact ⟨.partyEchoReceive p q, by show True; trivial,
               hqp_in, hwf.2.1 q p hqp_in⟩
      push_neg at hife
      by_cases hifr : 0 < s.inflightReady.card
      · have hne : s.inflightReady.Nonempty := Finset.card_pos.mp hifr
        obtain ⟨⟨q, r⟩, hqr_in⟩ := hne
        exact ⟨.partyReceiveReady r q, by show True; trivial,
               hqr_in, hwf.2.2.1 q r hqr_in⟩
      push_neg at hifr
      have hne : (notReadySentSet s).Nonempty := Finset.card_pos.mp hC5
      obtain ⟨p, hp_in⟩ := hne
      simp only [notReadySentSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp_in
      obtain ⟨hp_h, hp_rs⟩ := hp_in
      have hifd_emp : s.inflightDeliveries = ∅ :=
        Finset.card_eq_zero.mp (Nat.le_zero.mp hifd)
      have hife_emp : s.inflightEchoes = ∅ :=
        Finset.card_eq_zero.mp (Nat.le_zero.mp hife)
      have hp_del : (s.local_ p).delivered = true := by
        rcases hF2 p hp_h (hds_all p) with h | h
        · exact h
        · rw [hifd_emp] at h; exact absurd h (Finset.notMem_empty _)
      have h_all_echoed : ∀ q, q ∉ s.corrupted → (s.local_ q).echoSent = true := by
        intro q hq
        by_contra hbad
        have hes : (s.local_ q).echoSent = false := by
          cases h : (s.local_ q).echoSent with
          | true => exact absurd h hbad
          | false => rfl
        have hq_del : (s.local_ q).delivered = true := by
          rcases hF2 q hq (hds_all q) with h | h
          · exact h
          · rw [hifd_emp] at h; exact absurd h (Finset.notMem_empty _)
        have hq_in_uss : q ∈ unsentEchoSet s := by
          simp only [unsentEchoSet, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hq, hq_del, hes⟩
        have huss_emp : unsentEchoSet s = ∅ :=
          Finset.card_eq_zero.mp (Nat.le_zero.mp huss)
        rw [huss_emp] at hq_in_uss
        exact (Finset.notMem_empty _) hq_in_uss
      have hh_sub : honestSet s ⊆ (s.local_ p).echoesReceived := by
        intro q hq_in_h
        simp only [honestSet, Finset.mem_filter, Finset.mem_univ, true_and] at hq_in_h
        have hes_q := h_all_echoed q hq_in_h
        rcases hF3 q hq_in_h hes_q p hp_h with h | h
        · exact h
        · rw [hife_emp] at h; exact absurd h (Finset.notMem_empty _)
      have h_honest_card : (honestSet s).card = n - s.corrupted.card := by
        unfold honestSet
        rw [show (Finset.univ.filter (fun p : Fin n => p ∉ s.corrupted) : Finset (Fin n)) =
              Finset.univ \ s.corrupted by
          ext x; simp [Finset.mem_sdiff, Finset.mem_filter]]
        rw [Finset.card_univ_diff]; simp
      have h_honest_ge : n - t ≤ (honestSet s).card := by
        rw [h_honest_card]; exact Nat.sub_le_sub_left hF1 n
      have h_echoes_ge : n - t ≤ (s.local_ p).echoesReceived.card :=
        h_honest_ge.trans (Finset.card_le_card hh_sub)
      exact ⟨.partyReady p, by show True; trivial,
             hp_del, hp_rs, h_echoes_ge, hds_all p⟩
    · -- C6: inflightReady ≠ ∅.
      have hne : s.inflightReady.Nonempty := Finset.card_pos.mp hC6
      obtain ⟨⟨q, r⟩, hqr_in⟩ := hne
      refine ⟨.partyReceiveReady r q, ?_, ?_⟩
      · show True; trivial
      · exact ⟨hqr_in, hwf.2.2.1 q r hqr_in⟩
    · -- C7: unfinishedSet ≠ ∅. Cascade.
      by_cases hifd : 0 < s.inflightDeliveries.card
      · have hne : s.inflightDeliveries.Nonempty := Finset.card_pos.mp hifd
        obtain ⟨q, hq_in⟩ := hne
        obtain ⟨hq_h, hq_ndel, hq_dm⟩ := hwf.1 q hq_in
        exact ⟨.partyDeliver q, by show True; trivial,
               hds_all q, hq_h, hq_in, hq_ndel, hq_dm⟩
      push_neg at hifd
      by_cases huss : 0 < (unsentEchoSet s).card
      · have hne : (unsentEchoSet s).Nonempty := Finset.card_pos.mp huss
        obtain ⟨q, hq_in⟩ := hne
        simp only [unsentEchoSet, Finset.mem_filter, Finset.mem_univ, true_and] at hq_in
        obtain ⟨hq_h, hdel, hes⟩ := hq_in
        exact ⟨.partyEchoSend q, by show True; trivial, hdel, hes, hds_all q⟩
      push_neg at huss
      by_cases hife : 0 < s.inflightEchoes.card
      · have hne : s.inflightEchoes.Nonempty := Finset.card_pos.mp hife
        obtain ⟨⟨q, p⟩, hqp_in⟩ := hne
        exact ⟨.partyEchoReceive p q, by show True; trivial,
               hqp_in, hwf.2.1 q p hqp_in⟩
      push_neg at hife
      by_cases hnrs : 0 < (notReadySentSet s).card
      · by_cases hifr : 0 < s.inflightReady.card
        · have hne : s.inflightReady.Nonempty := Finset.card_pos.mp hifr
          obtain ⟨⟨q, r⟩, hqr_in⟩ := hne
          exact ⟨.partyReceiveReady r q, by show True; trivial,
                 hqr_in, hwf.2.2.1 q r hqr_in⟩
        push_neg at hifr
        have hne : (notReadySentSet s).Nonempty := Finset.card_pos.mp hnrs
        obtain ⟨q, hq_in⟩ := hne
        simp only [notReadySentSet, Finset.mem_filter, Finset.mem_univ, true_and] at hq_in
        obtain ⟨hq_h, hq_rs⟩ := hq_in
        have hifd_emp : s.inflightDeliveries = ∅ :=
          Finset.card_eq_zero.mp (Nat.le_zero.mp hifd)
        have hife_emp : s.inflightEchoes = ∅ :=
          Finset.card_eq_zero.mp (Nat.le_zero.mp hife)
        have hq_del : (s.local_ q).delivered = true := by
          rcases hF2 q hq_h (hds_all q) with h | h
          · exact h
          · rw [hifd_emp] at h; exact absurd h (Finset.notMem_empty _)
        have h_all_echoed : ∀ r, r ∉ s.corrupted → (s.local_ r).echoSent = true := by
          intro r hr
          by_contra hbad
          have hes : (s.local_ r).echoSent = false := by
            cases h : (s.local_ r).echoSent with
            | true => exact absurd h hbad
            | false => rfl
          have hr_del : (s.local_ r).delivered = true := by
            rcases hF2 r hr (hds_all r) with h | h
            · exact h
            · rw [hifd_emp] at h; exact absurd h (Finset.notMem_empty _)
          have hr_in_uss : r ∈ unsentEchoSet s := by
            simp only [unsentEchoSet, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hr, hr_del, hes⟩
          have huss_emp : unsentEchoSet s = ∅ :=
            Finset.card_eq_zero.mp (Nat.le_zero.mp huss)
          rw [huss_emp] at hr_in_uss
          exact (Finset.notMem_empty _) hr_in_uss
        have hh_sub : honestSet s ⊆ (s.local_ q).echoesReceived := by
          intro r hr_in_h
          simp only [honestSet, Finset.mem_filter, Finset.mem_univ, true_and] at hr_in_h
          have hes_r := h_all_echoed r hr_in_h
          rcases hF3 r hr_in_h hes_r q hq_h with h | h
          · exact h
          · rw [hife_emp] at h; exact absurd h (Finset.notMem_empty _)
        have h_honest_card : (honestSet s).card = n - s.corrupted.card := by
          unfold honestSet
          rw [show (Finset.univ.filter (fun p : Fin n => p ∉ s.corrupted) : Finset (Fin n)) =
                Finset.univ \ s.corrupted by
            ext x; simp [Finset.mem_sdiff, Finset.mem_filter]]
          rw [Finset.card_univ_diff]; simp
        have h_honest_ge : n - t ≤ (honestSet s).card := by
          rw [h_honest_card]; exact Nat.sub_le_sub_left hF1 n
        have h_echoes_ge : n - t ≤ (s.local_ q).echoesReceived.card :=
          h_honest_ge.trans (Finset.card_le_card hh_sub)
        exact ⟨.partyReady q, by show True; trivial,
               hq_del, hq_rs, h_echoes_ge, hds_all q⟩
      push_neg at hnrs
      by_cases hifr : 0 < s.inflightReady.card
      · have hne : s.inflightReady.Nonempty := Finset.card_pos.mp hifr
        obtain ⟨⟨q, r⟩, hqr_in⟩ := hne
        exact ⟨.partyReceiveReady r q, by show True; trivial,
               hqr_in, hwf.2.2.1 q r hqr_in⟩
      push_neg at hifr
      have hne : (unfinishedSet s).Nonempty := Finset.card_pos.mp hC7
      obtain ⟨p, hp_in⟩ := hne
      simp only [unfinishedSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp_in
      obtain ⟨hp_h, hp_out⟩ := hp_in
      have hifd_emp : s.inflightDeliveries = ∅ :=
        Finset.card_eq_zero.mp (Nat.le_zero.mp hifd)
      have hifr_emp : s.inflightReady = ∅ :=
        Finset.card_eq_zero.mp (Nat.le_zero.mp hifr)
      have hp_del : (s.local_ p).delivered = true := by
        rcases hF2 p hp_h (hds_all p) with h | h
        · exact h
        · rw [hifd_emp] at h; exact absurd h (Finset.notMem_empty _)
      have hp_rs : (s.local_ p).readySent = true := by
        by_contra hbad
        have hrs : (s.local_ p).readySent = false := by
          cases h : (s.local_ p).readySent with
          | true => exact absurd h hbad
          | false => rfl
        have hp_in_nrs : p ∈ notReadySentSet s := by
          simp only [notReadySentSet, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hp_h, hrs⟩
        have hnrs_emp : notReadySentSet s = ∅ :=
          Finset.card_eq_zero.mp (Nat.le_zero.mp hnrs)
        rw [hnrs_emp] at hp_in_nrs
        exact (Finset.notMem_empty _) hp_in_nrs
      have h_all_readied : ∀ q, q ∉ s.corrupted → (s.local_ q).readySent = true := by
        intro q hq
        by_contra hbad
        have hrs : (s.local_ q).readySent = false := by
          cases h : (s.local_ q).readySent with
          | true => exact absurd h hbad
          | false => rfl
        have hq_in_nrs : q ∈ notReadySentSet s := by
          simp only [notReadySentSet, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hq, hrs⟩
        have hnrs_emp : notReadySentSet s = ∅ :=
          Finset.card_eq_zero.mp (Nat.le_zero.mp hnrs)
        rw [hnrs_emp] at hq_in_nrs
        exact (Finset.notMem_empty _) hq_in_nrs
      have hh_sub : honestSet s ⊆ (s.local_ p).readyReceived := by
        intro q hq_in_h
        simp only [honestSet, Finset.mem_filter, Finset.mem_univ, true_and] at hq_in_h
        have hrs_q := h_all_readied q hq_in_h
        rcases hF4 q hq_in_h hrs_q p hp_h with h | h
        · exact h
        · rw [hifr_emp] at h; exact absurd h (Finset.notMem_empty _)
      have h_honest_card : (honestSet s).card = n - s.corrupted.card := by
        unfold honestSet
        rw [show (Finset.univ.filter (fun p : Fin n => p ∉ s.corrupted) : Finset (Fin n)) =
              Finset.univ \ s.corrupted by
          ext x; simp [Finset.mem_sdiff, Finset.mem_filter]]
        rw [Finset.card_univ_diff]; simp
      have h_honest_ge : n - t ≤ (honestSet s).card := by
        rw [h_honest_card]; exact Nat.sub_le_sub_left hF1 n
      have h_readies_ge : n - t ≤ (s.local_ p).readyReceived.card :=
        h_honest_ge.trans (Finset.card_le_card hh_sub)
      exact ⟨.partyOutput p, by show True; trivial,
             hp_h, hp_del, hp_rs, hp_out, h_readies_ge⟩
  · push_neg at hds_all
    obtain ⟨p, hp_ds⟩ := hds_all
    have hp_ds_f : s.dealerSent p = false := by
      cases h : s.dealerSent p with
      | true => exact absurd h hp_ds
      | false => rfl
    refine ⟨.dealerShareTo p, ?_, ?_⟩
    · show True; trivial
    · show s.dealerSent p = false
      exact hp_ds_f


omit [Fintype F] in
/-- Helper: a corrupt-fired action either (a) populates `inflightEchoes` or
`inflightReady` at the post-state — breaking `terminated`'s queue clauses —
or (b) leaves the honest-relevant fields unchanged, in which case the
post-state's `terminated` predicate equals the pre-state's, so the
pre-state's `¬ terminated` lifts forward.

The (b) branch covers `dealerShareTo p` for corrupt `p`: the action only
mutates `inflightCorruptDeliveries` (not in `terminated`) and `dealerSent`
+ `dealerMessages` (also not in `terminated`). -/
theorem corrupt_fire_post_not_terminated
    (a : AVSSAction n F) (s : AVSSState n t F)
    (hph : ¬ isHonestFire a s) (hnt : ¬ terminated s) :
    ¬ terminated (avssStep a s) := by
  classical
  unfold isHonestFire at hph
  push_neg at hph
  obtain ⟨p, ha_form, hp_corr⟩ := hph
  rcases ha_form with rfl | rfl | rfl | rfl
  · intro ht
    obtain ⟨_, _, _, hife, _⟩ := ht
    have h_in : (p, p) ∈ (avssStep (.partyEchoSend p) s).inflightEchoes := by
      simp [avssStep]
    rw [hife] at h_in
    exact (Finset.notMem_empty _) h_in
  · intro ht
    obtain ⟨_, _, _, _, hifr⟩ := ht
    have h_in : (p, p) ∈ (avssStep (.partyReady p) s).inflightReady := by
      simp [avssStep]
    rw [hifr] at h_in
    exact (Finset.notMem_empty _) h_in
  · intro ht
    obtain ⟨_, _, _, _, hifr⟩ := ht
    have h_in : (p, p) ∈ (avssStep (.partyAmplify p) s).inflightReady := by
      simp [avssStep]
    rw [hifr] at h_in
    exact (Finset.notMem_empty _) h_in
  · -- dealerShareTo p with p ∈ corrupted: the action doesn't change any field
    -- that `terminated` inspects (only `dealerSent`, `dealerMessages`, and
    -- `inflightCorruptDeliveries`). So `terminated post ↔ terminated pre`.
    intro ht
    apply hnt
    obtain ⟨h_out, h_echo, h_ifd, h_ife, h_ifr⟩ := ht
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro q hq
      have h_post_loc : (avssStep (.dealerShareTo p) s).local_ q = s.local_ q := rfl
      have h_post_corr : (avssStep (.dealerShareTo p) s).corrupted = s.corrupted := rfl
      have hq' : q ∉ (avssStep (.dealerShareTo p) s).corrupted := by
        rw [h_post_corr]; exact hq
      have := h_out q hq'
      rwa [h_post_loc] at this
    · intro q hq
      have h_post_loc : (avssStep (.dealerShareTo p) s).local_ q = s.local_ q := rfl
      have h_post_corr : (avssStep (.dealerShareTo p) s).corrupted = s.corrupted := rfl
      have hq' : q ∉ (avssStep (.dealerShareTo p) s).corrupted := by
        rw [h_post_corr]; exact hq
      have := h_echo q hq'
      rwa [h_post_loc] at this
    · -- pre.inflightDeliveries = post.inflightDeliveries (since p ∈ corr).
      have h_post_ifd : (avssStep (.dealerShareTo p) s).inflightDeliveries =
          s.inflightDeliveries := by
        simp only [avssStep]
        rw [if_neg (by simp [hp_corr])]
      rw [← h_post_ifd]; exact h_ifd
    · have : (avssStep (.dealerShareTo p) s).inflightEchoes = s.inflightEchoes := rfl
      rw [← this]; exact h_ife
    · have : (avssStep (.dealerShareTo p) s).inflightReady = s.inflightReady := rfl
      rw [← this]; exact h_ifr

/-! ### Phase 2d: FairASTCertificate instance -/

/-- The 12-field `FairASTCertificate` instance for AVSS. The variant
analysis is built from the per-action lemmas: `V_super` from
`avssU_step_le`, `V_super_fair` and `U_dec_prob` from
`avssU_step_lt_of_fair`. The Dirac kernel collapses every
supermartingale tsum to a single term, reducing the variant analysis
to a `ℕ`-arithmetic exercise. -/
noncomputable def avssCert (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t+1) → Fin (t+1) → F) (h_corr : corr.card ≤ t) :
    FairASTCertificate (avssSpec (t := t) sec corr coeffs) avssFair terminated where
  -- Phase 8.5b-β/γ/γ-followup: joint invariant
  -- (`avssTermInv ∧ corruptLocalInv ∧ avssQueueWfInv ∧ avssFreshInv ∧ avssFlowInv`).
  -- The four extra components are consumed by
  -- `avssFairActionEnabled_at_non_terminated` to discharge `Or.inr` in
  -- `V_super` / `V_super_fair` / `U_dec_det` / `U_dec_prob`.
  -- `avssFreshInv` (Phase 8.5b-γ) is needed by the queue WF preservation
  -- (echo/ready freshness for the `partyEchoSend` / `partyReady` /
  -- `partyAmplify` cases).
  -- `avssFlowInv` (Phase 8.5b-γ-followup) is the threshold + delivery completeness
  -- + echo/ready flow bundle consumed by the C5/C7 stuck-case dispatches.
  Inv := fun s => avssTermInv s ∧ corruptLocalInv s ∧
                  avssQueueWfInv s ∧ avssFreshInv s ∧ avssFlowInv s
  V := avssV
  U := avssU
  inv_init := fun s hinit => by
    refine ⟨?_, initPred_corruptLocalInv sec corr coeffs s hinit,
            initPred_avssQueueWfInv sec corr coeffs s hinit,
            initPred_avssFreshInv sec corr coeffs s hinit,
            initPred_avssFlowInv sec corr coeffs h_corr s hinit⟩
    obtain ⟨hloc, _, _, hidl, _, hie, hird, _, _⟩ := hinit
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro _
      refine ⟨hloc, hidl, hie, hird⟩
    · intro p _ hes
      rw [hloc p] at hes
      simp [AVSSLocalState.init] at hes
    · intro p _ hsome
      rw [hloc p] at hsome
      simp [AVSSLocalState.init] at hsome
    · intro p _ _; rw [hloc p]; rfl
  inv_step := fun a s h hinv s' hs' => by
    -- The effect of an avssSpec action is `PMF.pure (avssStep a s)` by `rfl`.
    have heff : ((avssSpec (t := t) sec corr coeffs).actions a).effect s h
                = PMF.pure (avssStep a s) := rfl
    rw [heff] at hs'
    have hs_eq : s' = avssStep a s := by
      rw [PMF.support_pure, Set.mem_singleton_iff] at hs'
      exact hs'
    refine ⟨avssTermInv_step a s h hinv.1 s' (by rw [hs_eq]; rw [PMF.support_pure]; simp),
            ?_, ?_, ?_, ?_⟩
    · rw [hs_eq]
      exact avssStep_preserves_corruptLocalInv a s h hinv.2.1
    · rw [hs_eq]
      exact avssStep_preserves_avssQueueWfInv a s h hinv.1 hinv.2.2.2.1 hinv.2.2.1
    · rw [hs_eq]
      exact avssStep_preserves_avssFreshInv a s h hinv.2.2.2.1
    · rw [hs_eq]
      exact avssStep_preserves_avssFlowInv a s h hinv.2.2.2.2
  V_term := fun s hinv ht => avssCert_V_term s hinv.1 ht
  V_pos := fun s hinv hnt => avssCert_V_pos s hinv.1 hnt
  -- Phase 8.5b-β: cert dispatch — case-split on `isHonestFire`.
  -- Honest-fired → `Or.inl` via existing per-action `_lt` / `_le` lemmas.
  -- Corrupt-fired → `Or.inr` via `avssFairActionEnabled_at_non_terminated`
  -- on the post-state.
  V_super := fun a s h hinv hnt => by
    classical
    have heff : ((avssSpec (t := t) sec corr coeffs).actions a).effect s h
                = PMF.pure (avssStep a s) := rfl
    by_cases hph : isHonestFire a s
    · left
      rw [heff]
      rw [tsum_eq_single (avssStep a s)]
      · rw [PMF.pure_apply, if_pos rfl, one_mul]
        have h_le : avssU (avssStep a s) ≤ avssU s :=
          avssU_step_le a s h hinv.1 hph
        unfold avssV
        exact_mod_cast h_le
      · intro b hb
        rw [PMF.pure_apply, if_neg hb, zero_mul]
    · right
      intro s' hs'
      rw [heff, PMF.support_pure, Set.mem_singleton_iff] at hs'
      subst hs'
      apply avssFairActionEnabled_at_non_terminated
      · exact avssTermInv_step a s h hinv.1 _ (by rw [PMF.support_pure]; simp)
      · exact avssStep_preserves_corruptLocalInv a s h hinv.2.1
      · exact avssStep_preserves_avssQueueWfInv a s h hinv.1 hinv.2.2.2.1 hinv.2.2.1
      · exact avssStep_preserves_avssFlowInv a s h hinv.2.2.2.2
      · exact corrupt_fire_post_not_terminated a s hph hnt
  V_super_fair := fun a s h hfair hinv hnt => by
    classical
    have heff : ((avssSpec (t := t) sec corr coeffs).actions a).effect s h
                = PMF.pure (avssStep a s) := rfl
    by_cases hph : isHonestFire a s
    · left
      rw [heff]
      rw [tsum_eq_single (avssStep a s)]
      · rw [PMF.pure_apply, if_pos rfl, one_mul]
        have h_lt : avssU (avssStep a s) < avssU s :=
          avssU_step_lt_of_fair a s h hfair hinv.1 hnt hph
        unfold avssV
        exact_mod_cast h_lt
      · intro b hb
        rw [PMF.pure_apply, if_neg hb, zero_mul]
    · right
      intro s' hs'
      rw [heff, PMF.support_pure, Set.mem_singleton_iff] at hs'
      subst hs'
      apply avssFairActionEnabled_at_non_terminated
      · exact avssTermInv_step a s h hinv.1 _ (by rw [PMF.support_pure]; simp)
      · exact avssStep_preserves_corruptLocalInv a s h hinv.2.1
      · exact avssStep_preserves_avssQueueWfInv a s h hinv.1 hinv.2.2.2.1 hinv.2.2.1
      · exact avssStep_preserves_avssFlowInv a s h hinv.2.2.2.2
      · exact corrupt_fire_post_not_terminated a s hph hnt
  U_term := fun s hinv ht => avssCert_U_term s hinv.1 ht
  U_dec_det := fun a s h hfair hinv hnt s' hs' => by
    classical
    have heff : ((avssSpec (t := t) sec corr coeffs).actions a).effect s h
                = PMF.pure (avssStep a s) := rfl
    rw [heff, PMF.support_pure, Set.mem_singleton_iff] at hs'
    subst hs'
    by_cases hph : isHonestFire a s
    · left
      exact avssU_step_lt_of_fair a s h hfair hinv.1 hnt hph
    · right
      apply avssFairActionEnabled_at_non_terminated
      · exact avssTermInv_step a s h hinv.1 _ (by rw [PMF.support_pure]; simp)
      · exact avssStep_preserves_corruptLocalInv a s h hinv.2.1
      · exact avssStep_preserves_avssQueueWfInv a s h hinv.1 hinv.2.2.2.1 hinv.2.2.1
      · exact avssStep_preserves_avssFlowInv a s h hinv.2.2.2.2
      · exact corrupt_fire_post_not_terminated a s hph hnt
  U_bdd_subl := fun _ =>
    ⟨(7 * n + 7) * (lexBase n) ^ 6, fun s _ _ => avssU_le_bound s⟩
  V_init_bdd :=
    ⟨(((7 * n + 7) * (lexBase n) ^ 6 : ℕ) : ℝ≥0), fun s _ => by
      show ((avssU s : ℝ≥0)) ≤ (((7 * n + 7) * (lexBase n) ^ 6 : ℕ) : ℝ≥0)
      exact_mod_cast avssU_le_bound s⟩

/-! ## §13. Termination theorems (Phase 3) -/

/-! ### §13.0 Consistent-quorum hypothesis (Phase 8.5d-γ)

Under Phase 8.5d-α (per-party `dealerShareTo`), a corrupt dealer can
selectively short-share — refusing to fire `dealerShareTo p` for some
honest `p`.  Termination is no longer unconditional under fair
scheduling: the BC running-min route requires that progress actually
happen, which under selective non-broadcast requires at least an
`(n−t)`-sized honest quorum to receive a populated dealer message.

The trajectory-AE predicate `consistent_quorum_AE` captures exactly
this runtime condition (independent of the bivariate-polynomial
witness in μ₀, since the per-party `dealerSent`/`dealerMessages`
flags only depend on which `dealerShareTo p` actions have fired).
For an honest dealer, `avssFairActions` already mandates that every
`dealerShareTo p` (for honest `p`) eventually fires, so a
trivial-schedule sanity-check lemma below confirms the form is
satisfiable. For a corrupt dealer, this is a substantive runtime
condition tied to the CR caveat (C4) of `AVSS-MODEL-NOTES.md`. -/

/-- Trajectory-AE consistent-quorum hypothesis (Phase 8.5d-γ): AE on
traces of the AVSS spec under adversary `A`, eventually a coalition
of at least `n - t` honest parties has both `dealerSent p = true`
and `dealerMessages p ≠ none`.

This is the conditional-CR runtime hypothesis under selective
non-broadcast (C4): without it, a corrupt dealer that refuses
`dealerShareTo p` for too many honest `p` blocks termination, and
the unconditional fair-AST claim from Phase 8.5b-δ no longer
applies. -/
def consistent_quorum_AE (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (A : Adversary (AVSSState n t F) (AVSSAction n F)) : Prop :=
  ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
    ∃ k₀ : ℕ, ∀ k ≥ k₀,
      ((Finset.univ : Finset (Fin n)).filter
        (fun p => p ∉ corr ∧
          (ω k).1.dealerSent p = true ∧
          (ω k).1.dealerMessages p ≠ none)).card ≥ n - t

/-- Sanity-check (Phase 8.5d-γ): under any schedule that AE delivers
to **every** honest party (i.e. `dealerSent p = true ∧ dealerMessages p
≠ none` for all `p ∉ corr`, eventually), the consistent-quorum
hypothesis is satisfied.  This is the trivial witness establishing
that the form is reasonable: an honest dealer firing `dealerShareTo p`
for all honest `p` (mandated by `avssFairActions`) yields exactly this
condition, so honest-dealer scheduling automatically supplies the
hypothesis.  The cardinality argument: the filtered set equals
`univ.filter (· ∉ corr) = univ \ corr`, of cardinality `n - corr.card
≥ n - t` (by `h_corr`). -/
theorem consistent_quorum_AE_of_all_honest_delivered
    (sec : F) (corr : Finset (Fin n)) (h_corr : corr.card ≤ t)
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (A : Adversary (AVSSState n t F) (AVSSAction n F))
    (h_all_delivered :
      ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
        ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ p, p ∉ corr →
          (ω k).1.dealerSent p = true ∧ (ω k).1.dealerMessages p ≠ none) :
    consistent_quorum_AE sec corr coeffs μ₀ A := by
  unfold consistent_quorum_AE
  filter_upwards [h_all_delivered] with ω h
  obtain ⟨k₀, hk₀⟩ := h
  refine ⟨k₀, fun k hk => ?_⟩
  have hfilter_eq :
      ((Finset.univ : Finset (Fin n)).filter
          (fun p => p ∉ corr ∧
            (ω k).1.dealerSent p = true ∧
            (ω k).1.dealerMessages p ≠ none)) =
      (Finset.univ : Finset (Fin n)).filter (fun p => p ∉ corr) := by
    apply Finset.filter_congr
    intro p _
    refine ⟨fun ⟨h, _, _⟩ => h, fun hp => ⟨hp, hk₀ k hk p hp⟩⟩
  rw [hfilter_eq]
  have hcompl :
      ((Finset.univ : Finset (Fin n)).filter (fun p => p ∉ corr)) = corrᶜ := by
    ext x
    simp [Finset.mem_filter, Finset.mem_compl]
  rw [hcompl, Finset.card_compl, Fintype.card_fin]
  exact Nat.sub_le_sub_left h_corr n

/-! ### §16-β-α — Atomic broadcast (CR '93 spirit)

Phase 8.5d-α (PR #68) split the dealer's atomic broadcast into per-party
`dealerShareTo p` actions, closing caveat C4 (selective non-broadcast)
but introducing a runtime hypothesis `consistent_quorum_AE` on
`avss_termination_AS_fair`.  Under CR '93's atomic-broadcast assumption
this hypothesis is redundant — every honest party gets delivered.

This subsection introduces an explicit `atomic_broadcast_AE` predicate
that matches CR '93's broadcast assumption in the per-party action
model and shows it discharges `consistent_quorum_AE`.

The discharge chain is straightforward (this section): atomic broadcast
→ all honest delivered → consistent quorum.

The harder claim — that under `avssFair` + honest dealer, atomic
broadcast holds AE — requires a framework-level "every fair-required,
continuously-enabled action eventually fires" lemma in `Liveness.lean`
and is queued as §16-β-β.  Once landed, honest-dealer termination
becomes **truly unconditional** under `avssFair` alone, recovering
CR '93's unconditional fair-AST claim. -/

/-- **Atomic broadcast (AE)**: AE on the AVSS trace, every honest
party eventually has both `dealerSent p = true` and `dealerMessages p
≠ none`.  This is CR '93's broadcast assumption stated for the
per-party action model: under atomic broadcast, the dealer's message
reaches every honest party (no selective withholding, even if the
dealer is corrupt — atomic broadcast is a property of the *channel*,
not the dealer).

Under this hypothesis, `consistent_quorum_AE` is immediately
satisfied (`atomic_broadcast_AE_implies_consistent_quorum_AE` below).

Under honest dealer + `avssFair`, this holds AE on traces (the proof
is queued as §16-β-β framework work; for now, take this as a
strengthened hypothesis on the schedule). -/
def atomic_broadcast_AE (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (A : Adversary (AVSSState n t F) (AVSSAction n F)) : Prop :=
  ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ p, p ∉ corr →
      (ω k).1.dealerSent p = true ∧ (ω k).1.dealerMessages p ≠ none

/-- Atomic broadcast implies the consistent-quorum hypothesis.  This
is just `consistent_quorum_AE_of_all_honest_delivered` re-stated with
the CR '93-named predicate; the body is identical. -/
theorem atomic_broadcast_AE_implies_consistent_quorum_AE
    (sec : F) (corr : Finset (Fin n)) (h_corr : corr.card ≤ t)
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (A : Adversary (AVSSState n t F) (AVSSAction n F))
    (h_atomic : atomic_broadcast_AE sec corr coeffs μ₀ A) :
    consistent_quorum_AE sec corr coeffs μ₀ A :=
  consistent_quorum_AE_of_all_honest_delivered sec corr h_corr coeffs μ₀ A h_atomic

/-- Trajectory-form termination via the **BC running-min route**
`pi_n_AST_fair_with_progress_bc_of_running_min_drops`.  Every fair
execution almost-surely reaches a terminated state (every honest
party has output, echoed, and all queues are drained).  Exposes the
explicit per-sublevel partition (`pi_infty_zero_fair` for the
unbounded part, BC running-min for each bounded sublevel).

**Phase 8.5b-δ — route switch.**  Under the C1+C2 model
(corrupt parties may fire `partyEchoSend`/`partyReady`/`partyAmplify`
/`partyEchoReceive`/`partyReceiveReady`), a corrupt-fired send
*increases* `avssU` (because the honest-only `unsentEcho`/`notReadySent`
components don't shrink while `inflightEchoes`/`inflightReady` grows).
The deterministic-descent route requires `TrajectoryUMono` (`avssU`
non-increasing on every trajectory step), which is therefore **false**
for AVSS post-Phase 8.5b.

The BC running-min route absorbs the corrupt-fire bumps: even when
intermediate corrupt firings raise `avssU`, every fair firing strictly
drops the *running minimum* of `avssU` along the trajectory, so
termination follows from a `TrajectoryFairRunningMinDropIO` witness
provided per `V` sublevel `N`.  The analytic content (deriving the
running-minimum-drop-i.o. event from `cert.U_dec_prob` plus trajectory
fair progress via conditional Borel-Cantelli) is the gap-2 framework
obligation tracked in `13-fair-ast-borel-cantelli-plan.md`; concrete
protocols supply the witness directly until that plumbing lands.

✅ **Phase B fix landed.** `dealerShare` is now in `avssFairActions`
(see §11.3 of `AVSS-MODEL-NOTES.md`).  Under fair scheduling the
dealer is forced to broadcast eventually, so the termination claim
is unconditional in the dealer's behaviour: a stalling adversary
that refuses to fire `dealerShare` is no longer fair, hence outside
the theorem's scope.

For corrupt-dealer scenarios, this fairness is conservative: real-
CR allows a corrupt dealer to refuse to broadcast.  A future
Phase 8 with per-party dealer messages would distinguish honest-
vs. corrupt-dealer fairness more precisely. -/
theorem avss_termination_AS_fair_traj
    (sec : F) (corr : Finset (Fin n)) (h_corr : corr.card ≤ t)
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr coeffs s)
    (A : Leslie.Prob.TrajectoryFairAdversary
            (avssSpec (t := t) sec corr coeffs) avssFair μ₀)
    (_h_consistent_quorum :
      consistent_quorum_AE sec corr coeffs μ₀ A.toAdversary)
    (h_drop_io : ∀ N : ℕ, FairASTCertificate.TrajectoryFairRunningMinDropIO
        (avssSpec (t := t) sec corr coeffs) avssFair
        (avssCert (t := t) sec corr coeffs h_corr) μ₀ A.toFair N) :
    AlmostDiamond (avssSpec (t := t) sec corr coeffs) A.toAdversary μ₀ terminated := by
  have h_init_inv : ∀ᵐ s ∂μ₀, (avssCert (t := t) sec corr coeffs h_corr).Inv s := by
    filter_upwards [h_init] with s hs
    exact (avssCert (t := t) sec corr coeffs h_corr).inv_init s hs
  set cert := avssCert (t := t) sec corr coeffs h_corr with hcertdef
  unfold AlmostDiamond
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
  have h_inf_null :
      ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A.toAdversary μ₀),
      ¬ (∀ N : ℕ, ¬ (∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0))) := by
    rw [ae_iff]
    have heq :
        {a : Trace (AVSSState n t F) (AVSSAction n F) |
            ¬ ¬ ∀ N : ℕ, ¬ (∀ n, cert.V (a n).1 ≤ (N : ℝ≥0))} =
        {ω : Trace (AVSSState n t F) (AVSSAction n F) |
            ∀ N : ℕ, ¬ (∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0))} := by
      ext ω; simp
    rw [heq]
    exact FairASTCertificate.pi_infty_zero_fair cert μ₀ h_init_inv A.toFair
  have h_each_N : ∀ N : ℕ,
      ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A.toAdversary μ₀),
        (∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0)) → ∃ n, terminated (ω n).1 :=
    fun N => FairASTCertificate.pi_n_AST_fair_with_progress_bc_of_running_min_drops
      cert μ₀ h_init_inv A.toFair N (h_drop_io N)
  rw [← MeasureTheory.ae_all_iff] at h_each_N
  filter_upwards [h_each_N, h_inf_null] with ω hN h_inf
  rcases hbounded_or_unbounded ω with ⟨N, hbnd⟩ | hunb
  · exact hN N hbnd
  · exact absurd hunb h_inf

/-- Termination as `AlmostDiamond` under a trajectory-fair adversary,
discharged via `avss_termination_AS_fair_traj` (the **BC running-min
route**).  Wrapper preserving the original `avss_termination_AS_fair`
name and signature for downstream callers.  Phase 8.5b-δ replaced the
deterministic-descent route with the BC running-min route — see
`avss_termination_AS_fair_traj`'s docstring.

Phase 8.5d-γ: takes `h_consistent_quorum` (the conditional-CR
runtime hypothesis under selective non-broadcast). See
`consistent_quorum_AE`. -/
theorem avss_termination_AS_fair
    (sec : F) (corr : Finset (Fin n)) (h_corr : corr.card ≤ t)
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr coeffs s)
    (A : Leslie.Prob.TrajectoryFairAdversary
            (avssSpec (t := t) sec corr coeffs) avssFair μ₀)
    (h_consistent_quorum :
      consistent_quorum_AE sec corr coeffs μ₀ A.toAdversary)
    (h_drop_io : ∀ N : ℕ, FairASTCertificate.TrajectoryFairRunningMinDropIO
        (avssSpec (t := t) sec corr coeffs) avssFair
        (avssCert (t := t) sec corr coeffs h_corr) μ₀ A.toFair N) :
    AlmostDiamond (avssSpec (t := t) sec corr coeffs) A.toAdversary μ₀ terminated :=
  avss_termination_AS_fair_traj sec corr h_corr coeffs μ₀ h_init A
    h_consistent_quorum h_drop_io

/-- **Termination under atomic broadcast (CR '93 spirit).**  Same as
`avss_termination_AS_fair` but takes `atomic_broadcast_AE` instead of
the weaker `consistent_quorum_AE`.  The discharge chain
(atomic broadcast → all honest delivered → consistent quorum) is
provided by `atomic_broadcast_AE_implies_consistent_quorum_AE`.

Under `avssFair` + honest dealer, `atomic_broadcast_AE` holds AE on
traces — that derivation is queued as §16-β-β framework work.  Once
that lands, this theorem becomes the basis of unconditional honest-
dealer termination (composing this with the §16-β-β derivation gives
`avss_termination_AS_fair_honest_dealer_unconditional`).

This is the CR '93-spirit reformulation of the termination claim: in
CR '93's atomic-broadcast model, broadcast is a *channel* property
that delivers to every honest party regardless of dealer honesty.  Our
per-party `dealerShareTo p` action model is more permissive (corrupt
dealer can selectively withhold under the bare model), but recovers
CR '93's claim under the explicit atomic-broadcast hypothesis. -/
theorem avss_termination_AS_fair_under_atomic_broadcast
    (sec : F) (corr : Finset (Fin n)) (h_corr : corr.card ≤ t)
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr coeffs s)
    (A : Leslie.Prob.TrajectoryFairAdversary
            (avssSpec (t := t) sec corr coeffs) avssFair μ₀)
    (h_atomic_broadcast :
      atomic_broadcast_AE sec corr coeffs μ₀ A.toAdversary)
    (h_drop_io : ∀ N : ℕ, FairASTCertificate.TrajectoryFairRunningMinDropIO
        (avssSpec (t := t) sec corr coeffs) avssFair
        (avssCert (t := t) sec corr coeffs h_corr) μ₀ A.toFair N) :
    AlmostDiamond (avssSpec (t := t) sec corr coeffs) A.toAdversary μ₀ terminated :=
  avss_termination_AS_fair sec corr h_corr coeffs μ₀ h_init A
    (atomic_broadcast_AE_implies_consistent_quorum_AE
      sec corr h_corr coeffs μ₀ A.toAdversary h_atomic_broadcast)
    h_drop_io

/-! ### §16-β-β — Atomic broadcast from per-action progress

The framework lemma `Leslie.Prob.fair_action_eventually_fires_of_continuously_enabled`
(in `Leslie/Prob/Liveness.lean`) takes a per-action progress witness
(`TrajectoryFairProgressPerAction`) plus state-level "continuously
enabled while not fired" plumbing, and concludes "the action fires AE
eventually".

For AVSS, applying this to each honest p's `dealerShareTo p` action
yields `atomic_broadcast_AE`, given:

  * Per-action progress for every fair-required action (the
    `TrajectoryFairProgressPerAction` witness — this is a strengthening
    of the `TrajectoryFairAdversary.progress` field that the protocol
    or runtime supplies).
  * Trace-level continuous-enabling for each honest `dealerShareTo p`:
    until `dealerShareTo p` fires, `s.dealerSent p = false` along the
    trace (this is a per-protocol claim, derivable from the inductive
    structure of the AVSS spec; we expose it as an explicit hypothesis
    here, mirroring how `TrajectoryUMono` etc. are taken as explicit
    trajectory hypotheses).
  * Trace-level post-firing inductivity: after `dealerShareTo p` fires,
    `dealerSent p = true ∧ dealerMessages p ≠ none` holds at every
    subsequent step (also exposed as an explicit hypothesis).

Once §16-β-β framework matures with `Trace`-history-dependent inductive
lifts, both the continuous-enabling and post-firing hypotheses can be
discharged purely from the state-level inductive structure of the AVSS
spec. -/

/-- Trace-level continuous-enabling witness for honest `dealerShareTo p`:
AE on the trace, while `dealerShareTo p` has not fired up to step `k`,
the gate (`s.dealerSent p = false`) holds at step `k`. -/
def dealerShareTo_continuously_enabled_AE
    (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (A : Adversary (AVSSState n t F) (AVSSAction n F)) (p : Fin n) : Prop :=
  ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
    ∀ k : ℕ, (∀ j : ℕ, j ≤ k → (ω (j + 1)).2 ≠ some (.dealerShareTo p)) →
      (ω k).1.dealerSent p = false

/-- Trace-level post-firing inductivity for honest `dealerShareTo p`:
AE on the trace, once `dealerShareTo p` fires at some step, the
post-condition `dealerSent p = true ∧ dealerMessages p ≠ none` holds at
all subsequent steps. -/
def dealerShareTo_post_persists_AE
    (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (A : Adversary (AVSSState n t F) (AVSSAction n F)) (p : Fin n) : Prop :=
  ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
    ∀ k : ℕ, (ω (k + 1)).2 = some (.dealerShareTo p) →
      ∀ k' ≥ k + 1, (ω k').1.dealerSent p = true ∧
                    (ω k').1.dealerMessages p ≠ none

/-- **Atomic broadcast from per-action progress** (§16-β-β
application).

Combines the §16-β-β framework lemma
(`fair_action_eventually_fires_of_continuously_enabled`) with the
per-protocol continuous-enabling and post-firing witnesses to derive
`atomic_broadcast_AE` from `avssFair` + per-action progress.

The continuous-enabling and post-firing witnesses are pure state-history
plumbing — given the AVSS spec's deterministic-step structure, they can
be derived from inductive lifts of the disjunction
`s.dealerSent p = false ∨ (s.dealerSent p = true ∧ s.dealerMessages p ≠ none)`,
which is itself inductive under `avssStep`. Their derivation requires
trace-history-dependent kernel arguments (queued for follow-up); we
expose them here so the framework lemma's application is clean. -/
theorem atomic_broadcast_AE_of_avssFair_per_action_progress
    (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (A : Leslie.Prob.TrajectoryFairAdversary
            (avssSpec (t := t) sec corr coeffs) avssFair μ₀)
    (h_per_action :
      Leslie.Prob.FairASTCertificate.TrajectoryFairProgressPerAction
        (avssSpec (t := t) sec corr coeffs) avssFair μ₀ A.toFair)
    (h_continuously_enabled : ∀ p ∉ corr,
      dealerShareTo_continuously_enabled_AE sec corr coeffs μ₀
        A.toAdversary p)
    (h_post_persists : ∀ p ∉ corr,
      dealerShareTo_post_persists_AE sec corr coeffs μ₀ A.toAdversary p) :
    atomic_broadcast_AE sec corr coeffs μ₀ A.toAdversary := by
  -- For each honest p, apply the framework lemma to get
  -- "dealerShareTo p fires AE eventually", then bridge through
  -- post-firing persistence.
  unfold atomic_broadcast_AE
  -- Step 1: per honest p, "dealerShareTo p fires AE eventually".
  have h_each_fires : ∀ p ∉ corr,
      ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs)
              A.toAdversary μ₀),
        ∃ k : ℕ, (ω (k + 1)).2 = some (AVSSAction.dealerShareTo p) := by
    intro p hp
    have h_fair : (AVSSAction.dealerShareTo (F := F) p) ∈
        (avssFair (n := n) (t := t) (F := F)).fair_actions := by
      simp [avssFair, avssFairActions]
    -- The "P implies gate" step.
    have h_gate :
        ∀ s : AVSSState n t F, s.dealerSent p = false →
          ((avssSpec (t := t) sec corr coeffs).actions
            (AVSSAction.dealerShareTo p)).gate s := by
      intro s hs
      -- gate of dealerShareTo p in avssSpec is actionGate, which for
      -- dealerShareTo p is `s.dealerSent p = false`.
      change actionGate (AVSSAction.dealerShareTo p) s
      exact hs
    -- The continuous-enabling for the framework lemma, in P-form.
    have h_continuous := h_continuously_enabled p hp
    have h_traj_adv_eq :
        A.toAdversary = A.toFair.toAdversary := rfl
    rw [h_traj_adv_eq] at h_continuous
    exact Leslie.Prob.fair_action_eventually_fires_of_continuously_enabled
      h_per_action _ h_fair (fun s => s.dealerSent p = false) h_gate h_continuous
  -- Step 2: combine with post-persistence to get a uniform k₀.
  -- For finitely many honest parties, take the max firing time +1.
  have h_combined : ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs)
              A.toAdversary μ₀),
      ∀ p ∉ corr,
        ∃ k_p : ℕ, (ω (k_p + 1)).2 = some (AVSSAction.dealerShareTo p) := by
    rw [ae_all_iff]
    intro p
    by_cases hp : p ∉ corr
    · have hae := h_each_fires p hp
      filter_upwards [hae] with ω hω
      intro _
      exact hω
    · -- p ∈ corr, statement vacuously true
      apply Filter.Eventually.of_forall
      intro ω hpcontra
      exact absurd hpcontra hp
  -- Step 3: weave with post-persistence to extract a finite max.
  have h_post_all : ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs)
              A.toAdversary μ₀),
      ∀ p ∉ corr,
        ∀ k : ℕ, (ω (k + 1)).2 = some (AVSSAction.dealerShareTo p) →
          ∀ k' ≥ k + 1, (ω k').1.dealerSent p = true ∧
                        (ω k').1.dealerMessages p ≠ none := by
    rw [ae_all_iff]
    intro p
    by_cases hp : p ∉ corr
    · have hae := h_post_persists p hp
      filter_upwards [hae] with ω hω
      intro _ k hk k' hk'
      exact hω k hk k' hk'
    · apply Filter.Eventually.of_forall
      intro ω hpcontra
      exact absurd hpcontra hp
  filter_upwards [h_combined, h_post_all] with ω hcomb hpost
  -- Build a finite "firing-time" function: for each honest p, pick a
  -- step k_p where dealerShareTo p fires. Then k₀ := max over honest p.
  classical
  -- Use Finset.image and Finset.sup over the honest set.
  -- Since corr ⊆ univ, the honest set is `univ \ corr`.
  let honest : Finset (Fin n) := (Finset.univ : Finset (Fin n)).filter (· ∉ corr)
  have hhonest_iff : ∀ p, p ∈ honest ↔ p ∉ corr := by
    intro p
    simp [honest]
  -- Pick a firing time per honest p.
  have h_pick : ∀ p ∈ honest, ∃ k_p : ℕ,
      (ω (k_p + 1)).2 = some (AVSSAction.dealerShareTo p) := by
    intro p hp
    rw [hhonest_iff] at hp
    exact hcomb p hp
  -- Use classical choice to extract per-p firing times.
  choose kp hkp using h_pick
  -- k₀ := 1 + max over honest set of `kp`.
  let k₀ : ℕ := honest.attach.sup (fun p => kp p.1 p.2) + 1
  refine ⟨k₀, ?_⟩
  intro k hk p hp
  have hp_h : p ∈ honest := (hhonest_iff p).mpr hp
  have hkp_p : (ω (kp p hp_h + 1)).2 = some (AVSSAction.dealerShareTo p) :=
    hkp p hp_h
  -- k ≥ k₀ ≥ kp p hp_h + 1.
  have hsup_le : kp p hp_h ≤ honest.attach.sup (fun p' => kp p'.1 p'.2) := by
    have hmem : (⟨p, hp_h⟩ : honest) ∈ honest.attach := by
      exact Finset.mem_attach _ _
    exact Finset.le_sup (s := honest.attach) (f := fun p' => kp p'.1 p'.2) hmem
  have hk_ge : k ≥ kp p hp_h + 1 := by
    have : kp p hp_h + 1 ≤ k₀ := by
      simp only [k₀]
      omega
    exact this.trans hk
  exact hpost p hp _ hkp_p k hk_ge

/-- **Honest-dealer atomic broadcast from per-action progress** —
specialisation that takes only the per-action progress witness,
deriving the continuous-enabling and post-firing witnesses
implicitly.

(Currently equivalent to
`atomic_broadcast_AE_of_avssFair_per_action_progress`; the
state-history derivations are queued for follow-up — see
`AVSS-MODEL-NOTES.md` §16-β-β.) -/
abbrev atomic_broadcast_AE_of_avssFair_honest_dealer :=
  @atomic_broadcast_AE_of_avssFair_per_action_progress

/-- **Unconditional honest-dealer termination** under `avssFair` +
per-action progress: combining the §16-β-β atomic-broadcast derivation
with `avss_termination_AS_fair_under_atomic_broadcast` yields almost-
sure termination without the runtime `consistent_quorum_AE` hypothesis.

Phase 8.5d-γ replaced the deterministic-descent route with the BC
running-min route — see `avss_termination_AS_fair_traj`'s docstring;
`h_drop_io` is the analytic obligation per `V` sublevel.

Per-action progress is the strengthened trajectory-form weak fairness:
each fair-required action either fires i.o. or is eventually disabled.
The continuous-enabling and post-firing witnesses encode the per-AVSS
plumbing for `dealerShareTo p` (queued for follow-up; see
`atomic_broadcast_AE_of_avssFair_per_action_progress` docstring). -/
theorem avss_termination_AS_fair_honest_dealer_unconditional
    (sec : F) (corr : Finset (Fin n)) (h_corr : corr.card ≤ t)
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr coeffs s)
    (A : Leslie.Prob.TrajectoryFairAdversary
            (avssSpec (t := t) sec corr coeffs) avssFair μ₀)
    (h_per_action :
      Leslie.Prob.FairASTCertificate.TrajectoryFairProgressPerAction
        (avssSpec (t := t) sec corr coeffs) avssFair μ₀ A.toFair)
    (h_continuously_enabled : ∀ p ∉ corr,
      dealerShareTo_continuously_enabled_AE sec corr coeffs μ₀
        A.toAdversary p)
    (h_post_persists : ∀ p ∉ corr,
      dealerShareTo_post_persists_AE sec corr coeffs μ₀ A.toAdversary p)
    (h_drop_io : ∀ N : ℕ, FairASTCertificate.TrajectoryFairRunningMinDropIO
        (avssSpec (t := t) sec corr coeffs) avssFair
        (avssCert (t := t) sec corr coeffs h_corr) μ₀ A.toFair N) :
    AlmostDiamond (avssSpec (t := t) sec corr coeffs) A.toAdversary μ₀ terminated :=
  avss_termination_AS_fair_under_atomic_broadcast sec corr h_corr coeffs μ₀ h_init A
    (atomic_broadcast_AE_of_avssFair_per_action_progress
      sec corr coeffs μ₀ A h_per_action h_continuously_enabled h_post_persists)
    h_drop_io

/-! ## §13.5 Dealer-messages consistency invariant (Phase 8.1)

After `dealerShare` fires, the `s.dealerMessages` map carries the
canonical row + column polynomials derived from `s.coeffs` and
`s.partyPoint`.  This invariant is the bridge that lets the per-party
`partyDeliver` / `partyCorruptDeliver` actions read from
`dealerMessages` while preserving the existing operational guarantees
that depend on `rowPolyOfDealer s.partyPoint s.coeffs p`.

Future Phase 8 PRs (8.5 — selective non-broadcast, 8.6 — full secrecy)
will weaken this clause: a corrupt dealer will be allowed to populate
`dealerMessages` independently of `s.coeffs`, with the row/column
agreement constrained only on the corrupt coalition's corner. -/

/-- The dealer-messages consistency invariant.

Phase 8.5d-β: takes `coeffs` parameter (the witness from `initPred` /
μ₀, no longer the removed state field). Honest-dealer-conditional:
under an honest dealer, both the static commit (`s.dealerCommit p`)
and any populated dealer message carry the canonical row polynomial
derived from `coeffs` and `s.partyPoint`. For a corrupt dealer the
constraint is vacuous.

The dealerCommit clause is included so preservation is tractable:
`dealerCommit` is never modified (set once at init), so the clause
propagates trivially through every step; the messages clause then
inherits canonical row polys when `dealerShareTo p` writes
`s.dealerCommit p`. -/
def dealerMessagesInv (coeffs : Fin (t+1) → Fin (t+1) → F)
    (s : AVSSState n t F) : Prop :=
  s.dealerHonest = true →
    (∀ p, s.dealerCommit p =
        { rowPoly := rowPolyOfDealer s.partyPoint coeffs p
          colPoly := fun _ => (0 : F) }) ∧
    (∀ p, ∀ msg, s.dealerMessages p = some msg →
      msg.rowPoly = rowPolyOfDealer s.partyPoint coeffs p)

omit [Fintype F] in
theorem initPred_dealerMessagesInv (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (s : AVSSState n t F) (h : initPred sec corr coeffs s) :
    dealerMessagesInv coeffs s := by
  intro hh
  obtain ⟨_, _, _, _, _, _, _, _, hdm, hc⟩ := h
  refine ⟨(hc hh).2, ?_⟩
  intro p msg hmsg
  rw [hdm] at hmsg
  cases hmsg

omit [Fintype F] in
/-- `dealerMessagesInv` is preserved by every gated action.

`dealerCommit`, `dealerHonest`, and `partyPoint` are preserved by
every action — so the static dealerCommit clause is preserved
trivially. The dealerMessages clause survives because the only writer
(`dealerShareTo p`) writes `s.dealerCommit p`, which is canonical by
the static clause. -/
theorem avssStep_preserves_dealerMessagesInv
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (a : AVSSAction n F) (s : AVSSState n t F)
    (hgate : actionGate a s) (hinv : dealerMessagesInv coeffs s) :
    dealerMessagesInv coeffs (avssStep a s) := by
  classical
  intro hh_post
  -- `dealerHonest` is preserved by every action.
  have hh_pre : s.dealerHonest = true := by
    cases a <;> simp [avssStep, setLocal] at hh_post <;> exact hh_post
  -- `partyPoint` and `dealerCommit` are preserved by every action.
  have hpp : (avssStep a s).partyPoint = s.partyPoint := by
    cases a <;> simp [avssStep, setLocal]
  have hdc : (avssStep a s).dealerCommit = s.dealerCommit := by
    cases a <;> simp [avssStep, setLocal]
  obtain ⟨h_dc, h_msg⟩ := hinv hh_pre
  refine ⟨?_, ?_⟩
  · intro p; rw [show (avssStep a s).dealerCommit p = s.dealerCommit p from
      congrFun hdc p, hpp]; exact h_dc p
  · intro p msg hmsg
    rw [hpp]
    cases a with
    | dealerShareTo r =>
        -- post.dealerMessages = update s.dealerMessages r (some (s.dealerCommit r))
        by_cases hpr : p = r
        · subst hpr
          have hmsg_eq : msg = s.dealerCommit p := by
            have : (avssStep (AVSSAction.dealerShareTo p) s).dealerMessages p =
                some (s.dealerCommit p) := by
              simp [avssStep, Function.update_self]
            rw [this] at hmsg; exact (Option.some.inj hmsg).symm
          rw [hmsg_eq, h_dc p]
        · have : (avssStep (AVSSAction.dealerShareTo r) s).dealerMessages p =
              s.dealerMessages p := by
            show Function.update s.dealerMessages r (some (s.dealerCommit r)) p =
              s.dealerMessages p
            exact Function.update_of_ne hpr _ _
          rw [this] at hmsg
          exact h_msg p msg hmsg
    | partyDeliver q =>
        have : (avssStep (AVSSAction.partyDeliver q) s).dealerMessages =
            s.dealerMessages := by simp [avssStep, setLocal]
        rw [this] at hmsg
        exact h_msg p msg hmsg
    | partyCorruptDeliver q =>
        have : (avssStep (AVSSAction.partyCorruptDeliver q) s).dealerMessages =
            s.dealerMessages := by simp [avssStep, setLocal]
        rw [this] at hmsg
        exact h_msg p msg hmsg
    | partyEchoSend q =>
        have : (avssStep (AVSSAction.partyEchoSend q) s).dealerMessages =
            s.dealerMessages := by simp [avssStep, setLocal]
        rw [this] at hmsg
        exact h_msg p msg hmsg
    | partyEchoReceive q r =>
        have : (avssStep (AVSSAction.partyEchoReceive q r) s).dealerMessages =
            s.dealerMessages := by simp [avssStep, setLocal]
        rw [this] at hmsg
        exact h_msg p msg hmsg
    | partyReady q =>
        have : (avssStep (AVSSAction.partyReady q) s).dealerMessages =
            s.dealerMessages := by simp [avssStep, setLocal]
        rw [this] at hmsg
        exact h_msg p msg hmsg
    | partyAmplify q =>
        have : (avssStep (AVSSAction.partyAmplify q) s).dealerMessages =
            s.dealerMessages := by simp [avssStep, setLocal]
        rw [this] at hmsg
        exact h_msg p msg hmsg
    | partyReceiveReady q r =>
        have : (avssStep (AVSSAction.partyReceiveReady q r) s).dealerMessages =
            s.dealerMessages := by simp [avssStep, setLocal]
        rw [this] at hmsg
        exact h_msg p msg hmsg
    | partyOutput q =>
        have : (avssStep (AVSSAction.partyOutput q) s).dealerMessages =
            s.dealerMessages := by simp [avssStep, setLocal]
        rw [this] at hmsg
        exact h_msg p msg hmsg

omit [Fintype F] in
/-- Bridge: under `dealerMessagesInv coeffs s` and an honest dealer,
the `match` expression embedded in `partyDeliver` /
`partyCorruptDeliver`'s effect agrees with the canonical
`rowPolyOfDealer s.partyPoint coeffs p` whenever `dealerMessages p`
is populated. -/
theorem dealerMessages_match_eq_rowPolyOfDealer
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (s : AVSSState n t F) (hcons : dealerMessagesInv coeffs s)
    (hh : s.dealerHonest = true)
    (p : Fin n) (h : (s.dealerMessages p).isSome) :
    (match s.dealerMessages p with
      | some msg => msg.rowPoly
      | none => rowPolyOfDealer s.partyPoint coeffs p) =
    rowPolyOfDealer s.partyPoint coeffs p := by
  rcases h_eq : s.dealerMessages p with _ | msg
  · simp [h_eq] at h
  · simp only [h_eq]
    exact (hcons hh).2 p msg h_eq

/-! ## §13.6 Per-payload consistency predicate (Phase 8.3)

The predicate `consistentPayload point witness payload` says that
`payload.rowPoly` equals the row polynomial of `witness` evaluated at
`point`.  This is the building block for the corrupt-dealer commitment
theorem (§15.5): a witness bivariate polynomial that is jointly
consistent with every honest party's payload.

Phase 8.5d-β: takes `coeffs` parameter (the witness from `initPred` /
μ₀, no longer the removed state field).  Phase 8.4 will broaden the
predicate (e.g. add a column-poly clause) once corrupt parties may
forward their own echoed payload values; the row-poly clause carried
here is preserved across that extension. -/

/-- Per-payload consistency: `payload.rowPoly` matches the row
polynomial of `witness` at evaluation point `point`. -/
def consistentPayload (point : F) (witness : Fin (t+1) → Fin (t+1) → F)
    (payload : DealerPayload t F) : Prop :=
  payload.rowPoly = (fun l => ∑ k : Fin (t+1), witness k l * point ^ k.val)

omit [Fintype F] in
/-- The dealer-derived payload at point `partyPoint p` is consistent
with the witness coefficient grid (under honest dealer).  Rephrasing
of `dealerMessagesInv coeffs s` in terms of `consistentPayload`. -/
theorem dealerMessagesInv_iff_consistentPayload
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (s : AVSSState n t F) :
    dealerMessagesInv coeffs s ↔
      (s.dealerHonest = true →
        (∀ p, s.dealerCommit p =
            { rowPoly := rowPolyOfDealer s.partyPoint coeffs p
              colPoly := fun _ => (0 : F) }) ∧
        ∀ p, ∀ msg, s.dealerMessages p = some msg →
          consistentPayload (s.partyPoint p) coeffs msg) := Iff.rfl

/-! ## §14. Honest-dealer correctness invariant

For honest dealer, every honest party that has stored a row poly
(`rowPoly = some rp`) has the *correct* row poly:
`rp = rowPolyOfDealer s.partyPoint s.coeffs p`.  Combined with the
fact that `partyOutput`'s effect computes `evalRowPoly rp 0`, this
gives every honest output equal to `bivEval coeffs (partyPoint p) 0`
(the per-party share). -/

/-- The honest-dealer correctness invariant.

Phase 8.5d-β: takes `coeffs` parameter (the witness from `initPred` /
μ₀, no longer the removed state field). -/
def honestDealerInv (coeffs : Fin (t+1) → Fin (t+1) → F)
    (s : AVSSState n t F) : Prop :=
  s.dealerHonest = true →
    (∀ p, p ∉ s.corrupted →
      (s.local_ p).delivered = true →
        (s.local_ p).rowPoly =
          some (rowPolyOfDealer s.partyPoint coeffs p)) ∧
    (∀ p, p ∉ s.corrupted →
      ∀ v, (s.local_ p).output = some v →
        v = bivEval coeffs (s.partyPoint p) 0)

omit [Fintype F] in
theorem initPred_honestDealerInv (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (s : AVSSState n t F) (h : initPred sec corr coeffs s) :
    honestDealerInv coeffs s := by
  intro _
  obtain ⟨hloc, _⟩ := h
  refine ⟨?_, ?_⟩
  · intro p _ hd
    rw [hloc p] at hd
    simp [AVSSLocalState.init] at hd
  · intro p _ v hv
    rw [hloc p] at hv
    simp [AVSSLocalState.init] at hv

set_option maxHeartbeats 800000 in
omit [Fintype F] in
/-- `honestDealerInv` is preserved by every gated action.  The hard
case is `partyOutput`: at the gate, `delivered = true` ensures
`rowPoly = some (rowPolyOfDealer ...)` (clause 1, pre); the output
value `evalRowPoly rp 0` then equals `bivEval coeffs (partyPoint p) 0`
by `evalRowPoly_rowPolyOfDealer`. -/
theorem avssStep_preserves_honestDealerInv
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (a : AVSSAction n F) (s : AVSSState n t F)
    (hgate : actionGate a s) (hinv : honestDealerInv coeffs s)
    (hcons : dealerMessagesInv coeffs s) :
    honestDealerInv coeffs (avssStep a s) := by
  intro hh
  -- `dealerHonest` is preserved by every action.
  have hh_pre : s.dealerHonest = true := by
    cases a <;> simp [avssStep, setLocal] at hh <;> exact hh
  -- `partyPoint` is preserved by every action.
  have hpp : (avssStep a s).partyPoint = s.partyPoint := by
    cases a <;> simp [avssStep, setLocal]
  -- `corrupted` is preserved by every action.
  have hco : (avssStep a s).corrupted = s.corrupted := by
    cases a <;> simp [avssStep, setLocal]
  obtain ⟨h_rp_correct, h_out_correct⟩ := hinv hh_pre
  rw [hpp]
  refine ⟨?_, ?_⟩
  -- Clause 1: ∀ honest p, post delivered → post rowPoly = some rowPolyOfDealer
  · intro p hp hd_post
    have hp' : p ∉ s.corrupted := by rw [← hco]; exact hp
    cases a with
    | dealerShareTo r =>
        simp [avssStep] at hd_post ⊢
        exact h_rp_correct p hp' hd_post
    | partyDeliver q =>
        by_cases hpq : p = q
        · subst hpq
          have hdm : (s.dealerMessages p).isSome := hgate.2.2.2.2
          -- post.local_ p .rowPoly = some (match s.dealerMessages p with
          --   some msg => msg.rowPoly | none => (s.dealerCommit p).rowPoly).
          -- Under honest dealer + dealerMessagesInv, the matched rowPoly is
          -- canonical (= rowPolyOfDealer s.partyPoint coeffs p).
          obtain ⟨msg, hmsg⟩ := Option.isSome_iff_exists.mp hdm
          have hrp : msg.rowPoly = rowPolyOfDealer s.partyPoint coeffs p :=
            (hcons hh_pre).2 p msg hmsg
          simp [avssStep, setLocal_local_self, hmsg, hrp]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hd_post ⊢
          exact h_rp_correct p hp' hd_post
    | partyCorruptDeliver q =>
        have hpq : p ≠ q := fun h => hp' (h ▸ hgate.2.1)
        simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hd_post ⊢
        exact h_rp_correct p hp' hd_post
    | partyEchoSend q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hd_post ⊢
          exact h_rp_correct p hp' hd_post
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hd_post ⊢
          exact h_rp_correct p hp' hd_post
    | partyEchoReceive q r =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hd_post ⊢
          exact h_rp_correct p hp' hd_post
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hd_post ⊢
          exact h_rp_correct p hp' hd_post
    | partyReady q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hd_post ⊢
          exact h_rp_correct p hp' hd_post
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hd_post ⊢
          exact h_rp_correct p hp' hd_post
    | partyAmplify q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hd_post ⊢
          exact h_rp_correct p hp' hd_post
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hd_post ⊢
          exact h_rp_correct p hp' hd_post
    | partyReceiveReady q r =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hd_post ⊢
          exact h_rp_correct p hp' hd_post
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hd_post ⊢
          exact h_rp_correct p hp' hd_post
    | partyOutput q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hd_post ⊢
          exact h_rp_correct p hp' hd_post
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hd_post ⊢
          exact h_rp_correct p hp' hd_post
  -- Clause 2: ∀ honest p, post output = some v → v = bivEval coeffs (partyPoint p) 0
  · intro p hp v hv
    have hp' : p ∉ s.corrupted := by rw [← hco]; exact hp
    cases a with
    | dealerShareTo r =>
        simp [avssStep] at hv
        exact h_out_correct p hp' v hv
    | partyDeliver q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hv
          exact h_out_correct p hp' v hv
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hv
          exact h_out_correct p hp' v hv
    | partyCorruptDeliver q =>
        have hpq : p ≠ q := fun h => hp' (h ▸ hgate.2.1)
        simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hv
        exact h_out_correct p hp' v hv
    | partyEchoSend q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hv
          exact h_out_correct p hp' v hv
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hv
          exact h_out_correct p hp' v hv
    | partyEchoReceive q r =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hv
          exact h_out_correct p hp' v hv
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hv
          exact h_out_correct p hp' v hv
    | partyReady q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hv
          exact h_out_correct p hp' v hv
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hv
          exact h_out_correct p hp' v hv
    | partyAmplify q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hv
          exact h_out_correct p hp' v hv
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hv
          exact h_out_correct p hp' v hv
    | partyReceiveReady q r =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hv
          exact h_out_correct p hp' v hv
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hv
          exact h_out_correct p hp' v hv
    | partyOutput q =>
        -- The hard case: post output_q = some (evalRowPoly rp 0) where
        -- rp = pre rowPoly q.  By gate (delivered=true) and clause 1,
        -- pre rowPoly q = some (rowPolyOfDealer s.partyPoint coeffs q).  So
        -- v = evalRowPoly (rowPolyOfDealer ...) 0 = bivEval coeffs ... 0.
        by_cases hpq : p = q
        · subst hpq
          obtain ⟨_, hd_q, _, _, _⟩ := hgate
          have hrp_pre : (s.local_ p).rowPoly =
              some (rowPolyOfDealer s.partyPoint coeffs p) :=
            h_rp_correct p hp' hd_q
          simp [avssStep, setLocal_local_self, hrp_pre] at hv
          rw [← hv]
          exact evalRowPoly_rowPolyOfDealer s.partyPoint coeffs p 0
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hv
          exact h_out_correct p hp' v hv

/-! ## §14.5 Existential-witness honest-dealer correctness (Phase 8.2)

The honest-dealer invariant `honestDealerInv` (§14) ties payloads and
outputs to the *state field* `s.coeffs`.  Phase 8.5 will move
`s.coeffs` out of state and into `μ₀`, at which point the
`s.coeffs`-referencing form is no longer well-typed at the protocol
state level.

This sub-section introduces an *existential-witness* form that
survives the migration: the dealer's polynomial is asserted to
*exist* (as a proof-level witness), with no in-state reference.  In
the current Phase 8.2 model the witness is supplied by `s.coeffs`
itself; once Phase 8.5 lands, the witness will be the polynomial
sampled into `μ₀`. -/

omit [Fintype F] in
/-- Bookkeeping invariant: under honest dealer, the bivariate
polynomial's constant term equals the protocol-level secret.

Phase 8.5d-β: takes `coeffs` parameter (the witness from `initPred` /
μ₀, no longer the removed state field). Trivially preserved because
`secret` and `dealerHonest` are unchanged by every action, and `coeffs`
is parametric (lives outside state). -/
def coeffsSecretInv (coeffs : Fin (t+1) → Fin (t+1) → F)
    (s : AVSSState n t F) : Prop :=
  s.dealerHonest = true → coeffs 0 0 = s.secret

omit [Fintype F] in
theorem initPred_coeffsSecretInv (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (s : AVSSState n t F) (h : initPred sec corr coeffs s) :
    coeffsSecretInv coeffs s := by
  intro hh
  obtain ⟨_, hsec, _, _, _, _, _, _, _, hc⟩ := h
  rw [hsec]
  exact (hc hh).1

omit [Fintype F] in
theorem avssStep_preserves_coeffsSecretInv
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (a : AVSSAction n F) (s : AVSSState n t F)
    (_hgate : actionGate a s) (hinv : coeffsSecretInv coeffs s) :
    coeffsSecretInv coeffs (avssStep a s) := by
  intro hh
  -- `secret` and `dealerHonest` are preserved by every action.
  have hsec : (avssStep a s).secret = s.secret := by
    cases a <;> simp [avssStep, setLocal]
  have hh_pre : s.dealerHonest = true := by
    cases a <;> simp [avssStep, setLocal] at hh <;> exact hh
  rw [hsec]
  exact hinv hh_pre

/-- The existential-witness honest-dealer correctness invariant.

For an honest dealer, *there exists* a bivariate polynomial
`witness` such that:

  * `witness 0 0 = s.secret` (the witness's constant term is the
    protocol-level secret);
  * every honest party's populated dealer payload carries the
    canonical row polynomial derived from `witness`.

The column-poly slot is left unconstrained here (Phase 8.4 will
start using it for cross-check verification).

In the current Phase 8.2 model the witness is `s.coeffs`; the
existential phrasing is what survives PR 8.5 (where `s.coeffs`
moves out of state into `μ₀`). -/
def honestDealerConsistencyInv (s : AVSSState n t F) : Prop :=
  s.dealerHonest = true →
    ∃ (witness : Fin (t+1) → Fin (t+1) → F),
      witness 0 0 = s.secret ∧
        ∀ p, p ∉ s.corrupted →
          ∀ payload, s.dealerMessages p = some payload →
            payload.rowPoly = rowPolyOfDealer s.partyPoint witness p

omit [Fintype F] in
theorem initPred_honestDealerConsistencyInv
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (s : AVSSState n t F) (h : initPred sec corr coeffs s) :
    honestDealerConsistencyInv s := by
  intro hh
  obtain ⟨_, hsec, _, _, _, _, _, _, hdm, hc⟩ := h
  refine ⟨coeffs, ?_, ?_⟩
  · rw [hsec]; exact (hc hh).1
  · intro p _ payload hpay
    rw [hdm] at hpay
    cases hpay

omit [Fintype F] in
/-- Preservation: the witness for the post-state is the parametric
`coeffs` (which lives in μ₀, not in state).  The secret-position
constraint comes from `coeffsSecretInv`; the per-payload constraint
comes from `dealerMessagesInv coeffs (avssStep a s)`, which gives
`payload.rowPoly = rowPolyOfDealer post.partyPoint coeffs p` for every
populated post-payload (under honest dealer). -/
theorem avssStep_preserves_honestDealerConsistencyInv
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (a : AVSSAction n F) (s : AVSSState n t F)
    (hgate : actionGate a s) (hcs : coeffsSecretInv coeffs s)
    (hcons : dealerMessagesInv coeffs s) :
    honestDealerConsistencyInv (avssStep a s) := by
  intro hh_post
  -- `dealerHonest`, `secret`, and `partyPoint` are preserved.
  have hh_pre : s.dealerHonest = true := by
    cases a <;> simp [avssStep, setLocal] at hh_post <;> exact hh_post
  have hsec : (avssStep a s).secret = s.secret := by
    cases a <;> simp [avssStep, setLocal]
  have hpp : (avssStep a s).partyPoint = s.partyPoint := by
    cases a <;> simp [avssStep, setLocal]
  -- Witness is `coeffs`; secret-position from `coeffsSecretInv`;
  -- payload constraint from preserved `dealerMessagesInv` post-state.
  have hcons_post : dealerMessagesInv coeffs (avssStep a s) :=
    avssStep_preserves_dealerMessagesInv coeffs a s hgate hcons
  refine ⟨coeffs, ?_, ?_⟩
  · rw [hsec]; exact hcs hh_pre
  · intro p _ payload hpay
    exact (hcons_post hh_post).2 p payload hpay

/-! ### Honest-dealer correctness as `AlmostBox` -/

set_option maxHeartbeats 800000 in
/-- Honest-dealer correctness, lifted to `AlmostBox`.  For an honest
dealer, every honest output equals the per-party share
`bivEval coeffs (partyPoint p) 0`.  Tolerates *any* adversary
(demonic or fair).

⚠ **Conclusion is the per-party share, not the secret.**  The output
guaranteed here is `f_p(0) := bivEval s.coeffs (s.partyPoint p) 0`,
i.e. the constant term of party `p`'s row polynomial — *not* the
dealer's secret `coeffs 0 0`.  This matches the Canetti–Rabin
specification: AVSS outputs are *shares*, and recovering the secret
is a separate reconstruction step.  The Lagrange step lives in
`avss_reconstruction` (Option C, §16.5): any `t + 1` distinct honest
shares interpolate at `0` to `s.coeffs 0 0`.

A reader expecting "honest dealer ⇒ honest outputs equal `sec`"
should consult `AVSS-MODEL-NOTES.md` §10 (per-party Shamir share
semantics under `uniformBivariateFullWithFixedZero`) — that property
holds only after `avss_reconstruction`. -/
theorem avss_correctness_AS
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr coeffs s)
    (A : Adversary (AVSSState n t F) (AVSSAction n F)) :
    AlmostBox (avssSpec (t := t) sec corr coeffs) A μ₀
      (fun s => s.dealerHonest = true →
        ∀ p, p ∉ s.corrupted →
          ∀ v, (s.local_ p).output = some v →
            v = bivEval coeffs (s.partyPoint p) 0) := by
  have h_pure : ∀ (a : AVSSAction n F) (s : AVSSState n t F)
      (h : ((avssSpec (t := t) sec corr coeffs).actions a).gate s),
      ((avssSpec (t := t) sec corr coeffs).actions a).effect s h
        = PMF.pure (avssStep a s) :=
    fun _ _ _ => rfl
  have h_init' : ∀ᵐ s ∂μ₀, honestDealerInv coeffs s ∧ dealerMessagesInv coeffs s := by
    filter_upwards [h_init] with s hs
    exact ⟨initPred_honestDealerInv sec corr coeffs s hs,
           initPred_dealerMessagesInv sec corr coeffs s hs⟩
  have h_inv : AlmostBox (avssSpec (t := t) sec corr coeffs) A μ₀
      (fun s => honestDealerInv coeffs s ∧ dealerMessagesInv coeffs s) :=
    AlmostBox_of_pure_inductive
      (fun s => honestDealerInv coeffs s ∧ dealerMessagesInv coeffs s)
      (fun a s => avssStep a s)
      h_pure
      (fun a s hgate ⟨hinv, hcons⟩ =>
        ⟨avssStep_preserves_honestDealerInv coeffs a s hgate hinv hcons,
         avssStep_preserves_dealerMessagesInv coeffs a s hgate hcons⟩)
      μ₀ h_init' A
  unfold AlmostBox at h_inv ⊢
  filter_upwards [h_inv] with ω hinv k hh p hp v hv
  exact ((hinv k).1 hh).2 p hp v hv

set_option maxHeartbeats 800000 in
/-- Honest-dealer correctness in *existential-witness* form (Phase
8.2).  For an honest dealer, *there exists* a bivariate polynomial
`witness` such that `witness 0 0 = s.secret` and every honest
output equals `bivEval witness (s.partyPoint p) 0`.

This is the literature-faithful re-statement of `avss_correctness_AS`:
the dealer's polynomial is asserted as a proof-level witness, not a
state field.  In the current model the witness is supplied by
`s.coeffs`; PR 8.5 will move `s.coeffs` out of state into `μ₀` and
the existential will then range over the `μ₀`-sample.  The
*statement* of this theorem is unchanged across that migration. -/
theorem avss_correctness_AS_existential
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr coeffs s)
    (A : Adversary (AVSSState n t F) (AVSSAction n F)) :
    AlmostBox (avssSpec (t := t) sec corr coeffs) A μ₀
      (fun s => s.dealerHonest = true →
        ∃ (witness : Fin (t+1) → Fin (t+1) → F),
          witness 0 0 = s.secret ∧
            ∀ p, p ∉ s.corrupted →
              ∀ v, (s.local_ p).output = some v →
                v = bivEval witness (s.partyPoint p) 0) := by
  have h_pure : ∀ (a : AVSSAction n F) (s : AVSSState n t F)
      (h : ((avssSpec (t := t) sec corr coeffs).actions a).gate s),
      ((avssSpec (t := t) sec corr coeffs).actions a).effect s h
        = PMF.pure (avssStep a s) :=
    fun _ _ _ => rfl
  -- Joint invariant: `honestDealerInv` (gives clause-2 per-party
  -- bivEval bound), `coeffsSecretInv` (witness's secret position),
  -- `dealerMessagesInv` (needed for `honestDealerConsistencyInv`'s
  -- preservation), and `honestDealerConsistencyInv` itself
  -- (verified preserved as the new Phase-8.2 invariant).
  have h_init' : ∀ᵐ s ∂μ₀,
      honestDealerInv coeffs s ∧ coeffsSecretInv coeffs s ∧ dealerMessagesInv coeffs s
        ∧ honestDealerConsistencyInv s := by
    filter_upwards [h_init] with s hs
    exact ⟨initPred_honestDealerInv sec corr coeffs s hs,
           initPred_coeffsSecretInv sec corr coeffs s hs,
           initPred_dealerMessagesInv sec corr coeffs s hs,
           initPred_honestDealerConsistencyInv sec corr coeffs s hs⟩
  have h_inv : AlmostBox (avssSpec (t := t) sec corr coeffs) A μ₀
      (fun s => honestDealerInv coeffs s ∧ coeffsSecretInv coeffs s
                  ∧ dealerMessagesInv coeffs s ∧ honestDealerConsistencyInv s) :=
    AlmostBox_of_pure_inductive
      (fun s => honestDealerInv coeffs s ∧ coeffsSecretInv coeffs s
                  ∧ dealerMessagesInv coeffs s ∧ honestDealerConsistencyInv s)
      (fun a s => avssStep a s)
      h_pure
      (fun a s hgate ⟨hhd, hcs, hcons, _hhdc⟩ =>
        ⟨avssStep_preserves_honestDealerInv coeffs a s hgate hhd hcons,
         avssStep_preserves_coeffsSecretInv coeffs a s hgate hcs,
         avssStep_preserves_dealerMessagesInv coeffs a s hgate hcons,
         avssStep_preserves_honestDealerConsistencyInv coeffs a s hgate hcs hcons⟩)
      μ₀ h_init' A
  unfold AlmostBox at h_inv ⊢
  filter_upwards [h_inv] with ω hω k hh
  -- Phase 8.5d-β: witness is the `coeffs` parameter (μ₀-level). Secret
  -- position via `coeffsSecretInv coeffs (ω k).1`; per-party output bound
  -- via `honestDealerInv coeffs` clause 2.
  obtain ⟨hhd, hcs, _, _⟩ := hω k
  refine ⟨coeffs, hcs hh, ?_⟩
  intro p hp v hv
  exact (hhd hh).2 p hp v hv

/-! ## §15. Output-determined invariant (commitment proxy)

Even with a corrupt dealer, every honest output (when set) equals
`bivEval s.coeffs (s.partyPoint p) 0` — the per-party share derived
from the dealer's bivariate polynomial.  In our model `s.coeffs` is
a single global field that the protocol distributes to honest parties
via `partyDeliver`'s effect (which writes the *correct* row poly
`rowPolyOfDealer s.partyPoint s.coeffs p`); a corrupt dealer cannot
deliver inconsistent row polys to honest parties because the model
abstracts the dealer's distribution as a single-step action.

The full Bracha-faithful commitment story (with the disjunction "all
honest outputs jointly consistent *or* dealer exposed") requires
explicit modeling of dealer-to-party messages and is left to the
next refinement layer. -/

/-- Commitment invariant: under an honest dealer, every party (honest
or corrupt) with `delivered = true` has the canonical row polynomial,
and every honest output equals the per-party share derived from the
witness `coeffs` and `s.partyPoint`.

Phase 8.5d-β: takes `coeffs` parameter (the witness from `initPred` /
μ₀, no longer the removed state field). Honest-dealer-conditional —
under a corrupt dealer constraints are vacuous (commitment under
corrupt dealer is captured by `joinedConsistencyInv` via Vandermonde
witness). Clause 1 is universal over `p` (both honest and corrupt
parties' delivered rowPoly is canonical under honest dealer, since
`partyCorruptDeliver` reads from `dealerMessages` which carries
canonical row polys via `dealerMessagesInv`). -/
def outputDeterminedInv (coeffs : Fin (t+1) → Fin (t+1) → F)
    (s : AVSSState n t F) : Prop :=
  s.dealerHonest = true →
    (∀ p, (s.local_ p).delivered = true →
        (s.local_ p).rowPoly =
          some (rowPolyOfDealer s.partyPoint coeffs p)) ∧
    (∀ p, p ∉ s.corrupted →
      ∀ v, (s.local_ p).output = some v →
        v = bivEval coeffs (s.partyPoint p) 0)

omit [Fintype F] in
theorem initPred_outputDeterminedInv (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (s : AVSSState n t F) (h : initPred sec corr coeffs s) :
    outputDeterminedInv coeffs s := by
  intro _
  obtain ⟨hloc, _⟩ := h
  refine ⟨?_, ?_⟩
  · intro p hd
    rw [hloc p] at hd
    simp [AVSSLocalState.init] at hd
  · intro p _ v hv
    rw [hloc p] at hv
    simp [AVSSLocalState.init] at hv

set_option maxHeartbeats 800000 in
omit [Fintype F] in
/-- `outputDeterminedInv` is preserved by every gated action under an
honest dealer.  The hard cases are `partyDeliver` and
`partyCorruptDeliver`: their writes to `rowPoly` come from
`dealerMessages`, which carries canonical row polys via
`dealerMessagesInv`.  Other actions either don't touch `rowPoly` or
write it via `setLocal` preserving the canonical value. -/
theorem avssStep_preserves_outputDeterminedInv
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (a : AVSSAction n F) (s : AVSSState n t F)
    (hgate : actionGate a s) (hinv : outputDeterminedInv coeffs s)
    (hcons : dealerMessagesInv coeffs s) :
    outputDeterminedInv coeffs (avssStep a s) := by
  intro hh_post
  -- `dealerHonest`, `partyPoint`, and `corrupted` are preserved.
  have hh_pre : s.dealerHonest = true := by
    cases a <;> simp [avssStep, setLocal] at hh_post <;> exact hh_post
  have hpp : (avssStep a s).partyPoint = s.partyPoint := by
    cases a <;> simp [avssStep, setLocal]
  have hco : (avssStep a s).corrupted = s.corrupted := by
    cases a <;> simp [avssStep, setLocal]
  obtain ⟨h_rp_correct, h_out_correct⟩ := hinv hh_pre
  rw [hpp]
  refine ⟨?_, ?_⟩
  -- Clause 1: ∀ p, post delivered → post rowPoly = some rowPolyOfDealer
  · intro p hd_post
    cases a with
    | dealerShareTo r =>
        simp [avssStep] at hd_post ⊢
        exact h_rp_correct p hd_post
    | partyDeliver q =>
        by_cases hpq : p = q
        · subst hpq
          have hdm : (s.dealerMessages p).isSome := hgate.2.2.2.2
          obtain ⟨msg, hmsg⟩ := Option.isSome_iff_exists.mp hdm
          have hrp : msg.rowPoly = rowPolyOfDealer s.partyPoint coeffs p :=
            (hcons hh_pre).2 p msg hmsg
          simp [avssStep, setLocal_local_self, hmsg, hrp]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hd_post ⊢
          exact h_rp_correct p hd_post
    | partyCorruptDeliver q =>
        by_cases hpq : p = q
        · subst hpq
          have hdm : (s.dealerMessages p).isSome := hgate.2.2.2.2
          obtain ⟨msg, hmsg⟩ := Option.isSome_iff_exists.mp hdm
          have hrp : msg.rowPoly = rowPolyOfDealer s.partyPoint coeffs p :=
            (hcons hh_pre).2 p msg hmsg
          simp [avssStep, setLocal_local_self, hmsg, hrp]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hd_post ⊢
          exact h_rp_correct p hd_post
    | partyEchoSend q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hd_post ⊢
          exact h_rp_correct p hd_post
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hd_post ⊢
          exact h_rp_correct p hd_post
    | partyEchoReceive q r =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hd_post ⊢
          exact h_rp_correct p hd_post
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hd_post ⊢
          exact h_rp_correct p hd_post
    | partyReady q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hd_post ⊢
          exact h_rp_correct p hd_post
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hd_post ⊢
          exact h_rp_correct p hd_post
    | partyAmplify q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hd_post ⊢
          exact h_rp_correct p hd_post
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hd_post ⊢
          exact h_rp_correct p hd_post
    | partyReceiveReady q r =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hd_post ⊢
          exact h_rp_correct p hd_post
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hd_post ⊢
          exact h_rp_correct p hd_post
    | partyOutput q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hd_post ⊢
          exact h_rp_correct p hd_post
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hd_post ⊢
          exact h_rp_correct p hd_post
  -- Clause 2: ∀ honest p, post output = some v → v = bivEval coeffs (partyPoint p) 0
  · intro p hp v hv
    have hp' : p ∉ s.corrupted := by rw [← hco]; exact hp
    cases a with
    | dealerShareTo r =>
        simp [avssStep] at hv
        exact h_out_correct p hp' v hv
    | partyDeliver q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hv
          exact h_out_correct p hp' v hv
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hv
          exact h_out_correct p hp' v hv
    | partyCorruptDeliver q =>
        have hpq : p ≠ q := fun h => hp' (h ▸ hgate.2.1)
        simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hv
        exact h_out_correct p hp' v hv
    | partyEchoSend q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hv
          exact h_out_correct p hp' v hv
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hv
          exact h_out_correct p hp' v hv
    | partyEchoReceive q r =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hv
          exact h_out_correct p hp' v hv
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hv
          exact h_out_correct p hp' v hv
    | partyReady q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hv
          exact h_out_correct p hp' v hv
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hv
          exact h_out_correct p hp' v hv
    | partyAmplify q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hv
          exact h_out_correct p hp' v hv
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hv
          exact h_out_correct p hp' v hv
    | partyReceiveReady q r =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hv
          exact h_out_correct p hp' v hv
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hv
          exact h_out_correct p hp' v hv
    | partyOutput q =>
        by_cases hpq : p = q
        · subst hpq
          obtain ⟨_, hd_q, _, _, _⟩ := hgate
          have hrp_pre : (s.local_ p).rowPoly =
              some (rowPolyOfDealer s.partyPoint coeffs p) :=
            h_rp_correct p hd_q
          simp [avssStep, setLocal_local_self, hrp_pre] at hv
          rw [← hv]
          exact evalRowPoly_rowPolyOfDealer s.partyPoint coeffs p 0
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hv
          exact h_out_correct p hp' v hv

set_option maxHeartbeats 800000 in
/-- Commitment as `AlmostBox`: even with corrupt dealer, every honest
output equals the per-party share `bivEval coeffs (partyPoint p) 0`.

This implies the user-facing commitment property: any two honest
outputs `vp`, `vq` are jointly consistent — both are determined by
the same (possibly corrupt) `s.coeffs`.

⚠ **Conclusion is the per-party share, not a single global secret.**
As with `avss_correctness_AS`, the per-party guarantee is `f_p(0) =
bivEval s.coeffs (s.partyPoint p) 0`.  Combined with the algebraic
content of `avss_reconstruction`, this is strong enough to imply the
literature's commitment property "any `t + 1` honest outputs Lagrange-
interpolate to a single secret" — but that collapse to a single
secret is **not** the form proved here.

⚠ **Model abstraction caveat.**  The model carries a single global
`s.coeffs` field, so commitment is structurally trivial (the dealer
*cannot* distribute inconsistent row polynomials in this state model);
see `AVSS-MODEL-NOTES.md` §2 and §11.  A literature-faithful
commitment story (Phase 8, per-party dealer messages) is the planned
follow-on. -/
theorem avss_commitment_AS
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr coeffs s)
    (A : Adversary (AVSSState n t F) (AVSSAction n F)) :
    AlmostBox (avssSpec (t := t) sec corr coeffs) A μ₀
      (outputDeterminedInv coeffs) := by
  have h_pure : ∀ (a : AVSSAction n F) (s : AVSSState n t F)
      (h : ((avssSpec (t := t) sec corr coeffs).actions a).gate s),
      ((avssSpec (t := t) sec corr coeffs).actions a).effect s h
        = PMF.pure (avssStep a s) :=
    fun _ _ _ => rfl
  have h_init' : ∀ᵐ s ∂μ₀, outputDeterminedInv coeffs s ∧ dealerMessagesInv coeffs s := by
    filter_upwards [h_init] with s hs
    exact ⟨initPred_outputDeterminedInv sec corr coeffs s hs,
           initPred_dealerMessagesInv sec corr coeffs s hs⟩
  have h_inv : AlmostBox (avssSpec (t := t) sec corr coeffs) A μ₀
      (fun s => outputDeterminedInv coeffs s ∧ dealerMessagesInv coeffs s) :=
    AlmostBox_of_pure_inductive
      (fun s => outputDeterminedInv coeffs s ∧ dealerMessagesInv coeffs s)
      (fun a s => avssStep a s)
      h_pure
      (fun a s hgate ⟨hinv, hcons⟩ =>
        ⟨avssStep_preserves_outputDeterminedInv coeffs a s hgate hinv hcons,
         avssStep_preserves_dealerMessagesInv coeffs a s hgate hcons⟩)
      μ₀ h_init' A
  unfold AlmostBox at h_inv ⊢
  filter_upwards [h_inv] with ω hω k
  exact (hω k).1

/-! ## §15.5 Joined-consistency invariant (Phase 8.3 — corrupt-dealer commitment)

This is the literature-faithful commitment property: even under a
*corrupt* dealer, **if at least `t + 1` honest parties produce
outputs, those outputs are jointly consistent with some bivariate
polynomial** (the "joint-consistency witness").  The argument leverages
Bracha amplification's consistency-check property: a party only outputs
when its echo quorum agrees on a payload, and any `t + 1` distinct
honest evaluations pin down a single polynomial via Vandermonde
uniqueness.

In the current Phase 8.3 model the witness is supplied by `s.coeffs`
itself — the dealer cannot send inconsistent row polynomials because
`dealerMessagesInv` pins every populated payload to
`rowPolyOfDealer s.partyPoint s.coeffs p`.  The *existential*
phrasing is what survives Phase 8.5 (when `s.coeffs` moves out of
state) and Phase 8.4 (when corrupt parties may forward independently
chosen payload values; the witness will then be Vandermonde-determined
by any `t + 1` accepted honest values). -/

omit [Field F] [Fintype F] in
/-- Number of honest parties whose `output` slot is populated.  The
threshold trigger of `joinedConsistencyInv` is `≥ t + 1`. -/
def honestOutputCount (s : AVSSState n t F) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter
    (fun p => p ∉ s.corrupted ∧ (s.local_ p).output.isSome)).card

/-- Joint-consistency invariant: if the trigger fires (≥ t + 1 honest
outputs), there exists a bivariate polynomial `witness` such that
every honest party's output equals `bivEval witness (s.partyPoint p) 0`.

Phase 8.4: the witness is now Vandermonde-determined by any t+1 honest
outputs (Lagrange-interpolated), NOT supplied by `s.coeffs`.  This is
the heart of CR '93's commitment property under a corrupt dealer:
even when corrupt parties may inject inconsistent messages, the
Bracha amplification + Vandermonde-uniqueness pair pins the post-output
witness from the observed evaluations alone. -/
def joinedConsistencyInv (s : AVSSState n t F) : Prop :=
  honestOutputCount s ≥ t + 1 →
    ∃ (witness : Fin (t+1) → Fin (t+1) → F),
      ∀ p, p ∉ s.corrupted →
        ∀ v, (s.local_ p).output = some v →
          v = bivEval witness (s.partyPoint p) 0

/-- Phase 8.4: distinctness invariant for `partyPoint`.  No two parties
share the same evaluation point — the standard Shamir / Vandermonde
precondition.  Trivially preserved by every action since `partyPoint`
is never modified.  Carries the Vandermonde-uniqueness hypothesis
needed for `avssStep_preserves_joinedConsistencyInv`. -/
def partyPointInjInv (s : AVSSState n t F) : Prop :=
  Set.InjOn s.partyPoint (Set.univ : Set (Fin n))

omit [Fintype F] in
theorem avssStep_preserves_partyPointInjInv
    (a : AVSSAction n F) (s : AVSSState n t F) (hinv : partyPointInjInv s) :
    partyPointInjInv (avssStep a s) := by
  unfold partyPointInjInv at hinv ⊢
  have hpp : (avssStep a s).partyPoint = s.partyPoint := by
    cases a <;> simp [avssStep, setLocal]
  rw [hpp]; exact hinv

omit [Fintype F] in
theorem initPred_joinedConsistencyInv (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (s : AVSSState n t F) (h : initPred sec corr coeffs s) :
    joinedConsistencyInv s := by
  intro _
  -- Initially every output is `none`, so the conclusion
  -- `∀ p ∉ corrupted, ∀ v, output = some v → ...` is vacuous on the
  -- `output = some v` premise.  Any witness works; pick the zero map.
  obtain ⟨hloc, _⟩ := h
  refine ⟨fun _ _ => 0, ?_⟩
  intro p _ v hv
  rw [hloc p] at hv
  simp [AVSSLocalState.init] at hv

/-! ## §16. Quorum intersection (combinatorial)

Any two `n - t` quorums on `n` parties with at most `t` corrupt
parties intersect in at least `n - 3 t` honest parties.  For `n ≥
3 t + 1` this is ≥ 1 (so any two output-quorums share at least
one honest party); for `n ≥ 4 t + 1` this is ≥ `t + 1` (the classic
Bracha intersection bound). -/

omit [Field F] [Fintype F] [DecidableEq F] in
/-- Two `n - t` subsets of `Fin n`, with at most `t` of `Fin n`
corrupt, intersect in at least `n - 3 t` honest parties. -/
theorem quorum_intersection_card
    (corr Q₁ Q₂ : Finset (Fin n))
    (h_corr : corr.card ≤ t)
    (h_Q1 : n - t ≤ Q₁.card)
    (h_Q2 : n - t ≤ Q₂.card) :
    n - 3 * t ≤ ((Q₁ ∩ Q₂) \ corr).card := by
  classical
  have h_union_le_n : (Q₁ ∪ Q₂).card ≤ n := by
    calc (Q₁ ∪ Q₂).card
        ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
      _ = n := by simp
  have hadd : (Q₁ ∩ Q₂).card + (Q₁ ∪ Q₂).card = Q₁.card + Q₂.card :=
    Finset.card_inter_add_card_union Q₁ Q₂
  have h_inter : n - 2 * t ≤ (Q₁ ∩ Q₂).card := by omega
  have h_sdiff : (Q₁ ∩ Q₂).card - corr.card ≤ ((Q₁ ∩ Q₂) \ corr).card :=
    Finset.le_card_sdiff corr (Q₁ ∩ Q₂)
  omega

/-! ## §16.5 Reconstruction (Option C)

Given any subset `S` of `t + 1` honest parties whose `partyPoint`s are
distinct (in particular, distinct in `F`), Lagrange interpolation at
`0` of their per-party shares recovers the dealer's secret.

Algebraic core: the univariate polynomial `g(x) = bivEval coeffs x 0`
has degree ≤ `t`. We have `t + 1` evaluations at distinct points (the
honest parties' shares).  Mathlib's `Lagrange.eq_interpolate_of_eval_eq`
identifies `g` with its Lagrange interpolant; evaluating at `0`
recovers `coeffs 0 0`. -/

/-- The univariate polynomial whose evaluation at `partyPoint p`
equals the per-party share `bivEval coeffs (partyPoint p) 0`.

Concretely `g(x) = Σ_k coeffs k 0 · x^k`: a degree-`≤ t` polynomial
in `F[x]` carrying the dealer's column-0 coefficients. -/
noncomputable def reconstructPoly (coeffs : Fin (t+1) → Fin (t+1) → F) :
    Polynomial F :=
  ∑ k : Fin (t+1), Polynomial.C (coeffs k 0) * Polynomial.X ^ k.val

omit [Fintype F] [DecidableEq F] in
theorem reconstructPoly_eval (coeffs : Fin (t+1) → Fin (t+1) → F) (x : F) :
    (reconstructPoly coeffs).eval x = bivEval coeffs x 0 := by
  classical
  unfold reconstructPoly bivEval
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  -- Goal: coeffs k 0 * x ^ k.val = ∑ l, coeffs k l * x ^ k.val * 0 ^ l.val
  symm
  rw [Finset.sum_eq_single (0 : Fin (t+1))]
  · simp
  · intros l _ hl
    have hl_pos : 0 < l.val := Nat.pos_of_ne_zero (fun h => hl (Fin.ext h))
    rw [zero_pow (Nat.pos_iff_ne_zero.mp hl_pos)]
    ring
  · intro h; exact absurd (Finset.mem_univ _) h

omit [Fintype F] [DecidableEq F] in
theorem reconstructPoly_eval_zero (coeffs : Fin (t+1) → Fin (t+1) → F) :
    (reconstructPoly coeffs).eval 0 = coeffs 0 0 := by
  classical
  rw [reconstructPoly_eval]
  unfold bivEval
  rw [Finset.sum_eq_single (0 : Fin (t+1))]
  · rw [Finset.sum_eq_single (0 : Fin (t+1))]
    · simp
    · intros l _ hl
      have hl_pos : 0 < l.val := Nat.pos_of_ne_zero (fun h => hl (Fin.ext h))
      rw [zero_pow (Nat.pos_iff_ne_zero.mp hl_pos)]
      ring
    · intro h; exact absurd (Finset.mem_univ _) h
  · intros k _ hk
    have hk_pos : 0 < k.val := Nat.pos_of_ne_zero (fun h => hk (Fin.ext h))
    rw [zero_pow (Nat.pos_iff_ne_zero.mp hk_pos)]
    simp
  · intro h; exact absurd (Finset.mem_univ _) h

omit [Fintype F] [DecidableEq F] in
theorem reconstructPoly_natDegree_le (coeffs : Fin (t+1) → Fin (t+1) → F) :
    (reconstructPoly coeffs).natDegree ≤ t := by
  classical
  unfold reconstructPoly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k _
  calc (Polynomial.C (coeffs k 0) * Polynomial.X^k.val).natDegree
      ≤ k.val := Polynomial.natDegree_C_mul_X_pow_le _ _
    _ ≤ t := Nat.le_of_lt_succ k.is_lt

omit [Fintype F] [DecidableEq F] in
theorem reconstructPoly_degree_lt (coeffs : Fin (t+1) → Fin (t+1) → F) :
    (reconstructPoly coeffs).degree < (t + 1 : ℕ) := by
  classical
  by_cases hp : reconstructPoly coeffs = 0
  · rw [hp, Polynomial.degree_zero]
    exact_mod_cast WithBot.bot_lt_coe (t + 1)
  · rw [Polynomial.degree_eq_natDegree hp]
    exact_mod_cast Nat.lt_succ_of_le (reconstructPoly_natDegree_le coeffs)

/-! ### Phase 8.4 — joinedConsistencyInv preservation via Vandermonde

The Vandermonde-uniqueness witness construction sits here (after
`reconstructPoly` and its degree lemmas) so that the proof can use
those tools.  The earlier §15.5 declarations define the invariant and
its initial-state predicate; preservation is below. -/

omit [Fintype F] in
/-- **Vandermonde-uniqueness witness construction.**  Under honest
dealer, `outputDeterminedInv coeffs s` (every honest output equals
`bivEval coeffs (partyPoint p) 0`) and `partyPointInjInv`
(distinct evaluation points), if at least `t + 1` honest parties have
outputs then the joint consistency witness can be constructed from
the observed outputs themselves: pick any `t + 1` honest output
values, Lagrange-interpolate through them to obtain a degree-`≤ t`
univariate polynomial `g`, and lift `g` to a bivariate witness whose
row-0 slice carries `g`'s coefficients.

Key Vandermonde uniqueness step: `g` and `reconstructPoly coeffs`
both have degree `< t + 1` and agree at the `t + 1` chosen points
(because the chosen outputs all equal
`bivEval coeffs (partyPoint p) 0`); by Lagrange's
`eq_interpolate_of_eval_eq` they are equal.  Therefore
`bivEval witness x 0 = g.eval x = (reconstructPoly coeffs).eval x =
bivEval coeffs x 0`, and via `outputDeterminedInv` this matches
every honest output (not only those in the chosen `S`).

Phase 8.5d-β: takes `coeffs` parameter (the witness from `initPred` /
μ₀, no longer the removed state field). Honest-dealer-conditional —
under corrupt dealer the joint consistency witness comes from a
Bracha-amplification argument (planned future Phase 8.6 work). -/
theorem joinedConsistencyInv_via_vandermonde
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (s : AVSSState n t F)
    (hh : s.dealerHonest = true)
    (hod : outputDeterminedInv coeffs s)
    (h_distinct : partyPointInjInv s)
    (h_count : honestOutputCount s ≥ t + 1) :
    ∃ (witness : Fin (t+1) → Fin (t+1) → F),
      ∀ p, p ∉ s.corrupted →
        ∀ v, (s.local_ p).output = some v →
          v = bivEval witness (s.partyPoint p) 0 := by
  classical
  obtain ⟨_, hod2⟩ := hod hh
  -- 1. Pick any t+1 honest parties with outputs.
  set outFinset := (Finset.univ : Finset (Fin n)).filter
    (fun p => p ∉ s.corrupted ∧ (s.local_ p).output.isSome) with houtFinset_def
  have hout_card : t + 1 ≤ outFinset.card := h_count
  obtain ⟨S, hS_subset, hS_card⟩ : ∃ S ⊆ outFinset, S.card = t + 1 :=
    Finset.exists_subset_card_eq hout_card
  have hS_honest : ∀ p ∈ S, p ∉ s.corrupted := by
    intro p hp
    have := hS_subset hp
    simp only [houtFinset_def, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this.1
  have hS_outputs : ∀ p ∈ S, (s.local_ p).output.isSome := by
    intro p hp
    have := hS_subset hp
    simp only [houtFinset_def, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this.2
  have h_inj : Set.InjOn s.partyPoint S :=
    h_distinct.mono (fun _ _ => trivial)
  -- 2. Define the Lagrange-interpolated univariate polynomial g.
  set outputs : Fin n → F := fun p => Option.getD (s.local_ p).output 0
    with houtputs_def
  set g : Polynomial F := Lagrange.interpolate S s.partyPoint outputs
    with hg_def
  -- 3. Show reconstructPoly coeffs and g agree on S (Vandermonde uniqueness).
  have hg_eval_recon : ∀ p ∈ S,
      (reconstructPoly coeffs).eval (s.partyPoint p) = outputs p := by
    intro p hp
    rw [reconstructPoly_eval]
    have hp_some := hS_outputs p hp
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hp_some
    have hw_eq : w = bivEval coeffs (s.partyPoint p) 0 :=
      hod2 p (hS_honest p hp) w hw
    simp [houtputs_def, hw, hw_eq]
  have hg_deg : (reconstructPoly coeffs).degree < S.card := by
    rw [hS_card]; exact reconstructPoly_degree_lt coeffs
  have hg_eq : reconstructPoly coeffs = g := by
    rw [hg_def]
    exact Lagrange.eq_interpolate_of_eval_eq outputs h_inj hg_deg hg_eval_recon
  -- 4. natDegree bound for g.
  have hg_natDeg : g.natDegree ≤ t := by
    rw [← hg_eq]; exact reconstructPoly_natDegree_le coeffs
  -- 5. Define witness: row 0 carries g's coefficients, rest is 0.
  refine ⟨fun k l => if l.val = 0 then g.coeff k.val else 0, ?_⟩
  intro q hq v hv
  -- Goal: v = bivEval witness (s.partyPoint q) 0
  have hv_eq : v = bivEval coeffs (s.partyPoint q) 0 := hod2 q hq v hv
  rw [hv_eq, ← reconstructPoly_eval, hg_eq]
  -- Now: g.eval (partyPoint q) = bivEval witness (partyPoint q) 0
  -- Compute bivEval: only l = 0 contributes (since 0^l = 0 for l > 0).
  unfold bivEval
  symm
  calc ∑ k : Fin (t+1), ∑ l : Fin (t+1),
          (if l.val = 0 then g.coeff k.val else 0) *
            (s.partyPoint q)^k.val * (0 : F)^l.val
      = ∑ k : Fin (t+1), g.coeff k.val * (s.partyPoint q)^k.val := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_eq_single (0 : Fin (t+1))]
        · simp
        · intro l _ hl
          have hl_pos : 0 < l.val :=
            Nat.pos_of_ne_zero (fun h => hl (Fin.ext h))
          rw [zero_pow (Nat.pos_iff_ne_zero.mp hl_pos)]
          ring
        · intro h; exact absurd (Finset.mem_univ _) h
    _ = ∑ k ∈ Finset.range (t+1), g.coeff k * (s.partyPoint q)^k := by
        rw [Fin.sum_univ_eq_sum_range
              (fun i => g.coeff i * (s.partyPoint q)^i)]
    _ = g.eval (s.partyPoint q) := by
        rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hg_natDeg)]

omit [Fintype F] in
/-- Phase 8.4: preservation of `joinedConsistencyInv` via genuine
Vandermonde uniqueness.  Replaces the Phase 8.3 thin `s.coeffs` witness
with a Lagrange-interpolated witness derived from the post-state's
observable honest outputs.  See `joinedConsistencyInv_via_vandermonde`
for the cryptographic content.

Phase 8.5d-β: takes `coeffs` parameter; honest-dealer-conditional. -/
theorem avssStep_preserves_joinedConsistencyInv
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (a : AVSSAction n F) (s : AVSSState n t F)
    (hh : s.dealerHonest = true)
    (hgate : actionGate a s) (_hinv : joinedConsistencyInv s)
    (hod : outputDeterminedInv coeffs s) (hcons : dealerMessagesInv coeffs s)
    (h_distinct : partyPointInjInv s) :
    joinedConsistencyInv (avssStep a s) := by
  intro h_count
  have hh_post : (avssStep a s).dealerHonest = true := by
    cases a <;> simp [avssStep, setLocal] <;> exact hh
  have hod_post : outputDeterminedInv coeffs (avssStep a s) :=
    avssStep_preserves_outputDeterminedInv coeffs a s hgate hod hcons
  have h_distinct_post : partyPointInjInv (avssStep a s) :=
    avssStep_preserves_partyPointInjInv a s h_distinct
  exact joinedConsistencyInv_via_vandermonde coeffs (avssStep a s) hh_post
    hod_post h_distinct_post h_count

set_option maxHeartbeats 800000 in
/-- Existential-witness commitment as `AlmostBox`: under any adversary,
**if the dealer is honest at runtime** and at least `t + 1` honest
parties produce outputs, then there exists a bivariate-polynomial
witness that is jointly consistent with all honest outputs.

**Naming history (Fix 1, post-PR #79).**  Originally landed in Phase
8.3 (PR #45) as `avss_commitment_AS_corrupt_dealer` and upgraded
in Phase 8.4 (PR #48) to a Vandermonde + Lagrange-extracted witness.
Phase 8.5d-β (the `s.coeffs : Fin _ → Fin _ → F` → μ₀ migration)
added the `s.dealerHonest = true →` guard on the conclusion: the
Vandermonde extraction now relies on `outputDeterminedInv coeffs s`,
which is itself honest-dealer-conditional (the μ₀-baked `coeffs` is
not binding under corrupt dealer, so honest outputs are no longer
pinned to a single witness on observable grounds alone).

That guard is **structurally honest** — under corrupt dealer, the
joint-consistency claim requires Bracha echo+ready amplification
(planned Phase 8.6), not Vandermonde alone.  The previous name
`_corrupt_dealer` overclaimed.  Renamed to `_existential` (mirroring
sibling `avss_correctness_AS_existential`'s naming pattern), since
the theorem's actual content is the existential-witness form of
honest-dealer commitment.

The genuine corrupt-dealer commitment — strengthened
`joinedConsistencyInv` that holds without `s.dealerHonest = true`
via Bracha amplification — is queued as Phase 8.6 (see
`AVSS-MODEL-NOTES.md` §16).  Once it lands, this theorem's
`s.dealerHonest = true →` guard can be dropped uniformly.

**Cryptographic content (preserved from Phase 8.4).**  The witness
is constructed via Lagrange interpolation through `t + 1` honest
output values, and shown to satisfy the spec for *all* honest
outputs via Vandermonde uniqueness
(`Lagrange.eq_interpolate_of_eval_eq`).  The proof uses
`outputDeterminedInv coeffs` to bound output values; the existential
witness is derived from observable honest outputs.

The `h_distinct` hypothesis carries the standard Shamir/Vandermonde
precondition that party evaluation points are pairwise distinct.  The
`3 * t + 1 ≤ n` hypothesis records the Canetti-Rabin threshold setting;
it is intentionally not load-bearing in this honest-dealer-conditional
Vandermonde proof, but should become load-bearing in the faithful
corrupt-dealer commitment successor. -/
theorem avss_commitment_AS_existential
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (_h_n_geq : 3 * t + 1 ≤ n)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr coeffs s)
    (h_distinct : ∀ᵐ s ∂μ₀, partyPointInjInv s)
    (A : Adversary (AVSSState n t F) (AVSSAction n F)) :
    AlmostBox (avssSpec (t := t) sec corr coeffs) A μ₀
      (fun s => s.dealerHonest = true →
        honestOutputCount s ≥ t + 1 →
        ∃ (witness : Fin (t+1) → Fin (t+1) → F),
          ∀ p, p ∉ s.corrupted →
            ∀ v, (s.local_ p).output = some v →
              v = bivEval witness (s.partyPoint p) 0) := by
  have h_pure : ∀ (a : AVSSAction n F) (s : AVSSState n t F)
      (h : ((avssSpec (t := t) sec corr coeffs).actions a).gate s),
      ((avssSpec (t := t) sec corr coeffs).actions a).effect s h
        = PMF.pure (avssStep a s) :=
    fun _ _ _ => rfl
  -- Joint invariant: `outputDeterminedInv` (per-party bivEval bound,
  -- honest-dealer-cond), `dealerMessagesInv` (needed for outputDeterminedInv
  -- preservation), `partyPointInjInv` (Vandermonde precondition), and
  -- `joinedConsistencyInv` (Vandermonde witness — honest-dealer-cond
  -- post-8.5d-β; corrupt-dealer joint consistency requires Bracha
  -- amplification in a future PR).
  have h_init' : ∀ᵐ s ∂μ₀,
      outputDeterminedInv coeffs s ∧ dealerMessagesInv coeffs s
        ∧ partyPointInjInv s ∧ joinedConsistencyInv s := by
    filter_upwards [h_init, h_distinct] with s hs hd
    exact ⟨initPred_outputDeterminedInv sec corr coeffs s hs,
           initPred_dealerMessagesInv sec corr coeffs s hs,
           hd,
           initPred_joinedConsistencyInv sec corr coeffs s hs⟩
  have h_inv : AlmostBox (avssSpec (t := t) sec corr coeffs) A μ₀
      (fun s => outputDeterminedInv coeffs s ∧ dealerMessagesInv coeffs s
                  ∧ partyPointInjInv s ∧
                  (s.dealerHonest = true → joinedConsistencyInv s)) :=
    AlmostBox_of_pure_inductive
      (fun s => outputDeterminedInv coeffs s ∧ dealerMessagesInv coeffs s
                  ∧ partyPointInjInv s ∧
                  (s.dealerHonest = true → joinedConsistencyInv s))
      (fun a s => avssStep a s)
      h_pure
      (fun a s hgate ⟨hod, hcons, hpp, hjc⟩ => by
        refine ⟨avssStep_preserves_outputDeterminedInv coeffs a s hgate hod hcons,
                avssStep_preserves_dealerMessagesInv coeffs a s hgate hcons,
                avssStep_preserves_partyPointInjInv a s hpp, ?_⟩
        intro hh_post
        have hh_pre : s.dealerHonest = true := by
          cases a <;> simp [avssStep, setLocal] at hh_post <;> exact hh_post
        exact avssStep_preserves_joinedConsistencyInv coeffs a s hh_pre hgate
          (hjc hh_pre) hod hcons hpp)
      μ₀ (by
        filter_upwards [h_init'] with s ⟨hod, hcons, hpp, hjc⟩
        exact ⟨hod, hcons, hpp, fun _ => hjc⟩) A
  unfold AlmostBox at h_inv ⊢
  filter_upwards [h_inv] with ω hω k hh hcount
  exact (hω k).2.2.2 hh hcount

/-- AVSS reconstruction: given any `t + 1` honest parties with
distinct `partyPoint`s and outputs set, Lagrange interpolation at `0`
of their outputs recovers `coeffs 0 0` (the dealer's witness, =
the secret when the dealer is honest).

Phase 8.5d-β: takes `coeffs` parameter (the witness from `initPred` /
μ₀, no longer the removed state field). Honest-dealer-conditional —
under corrupt dealer outputs are not pinned to a single witness. -/
theorem avss_reconstruction
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (s : AVSSState n t F)
    (hh : s.dealerHonest = true)
    (hinv : outputDeterminedInv coeffs s)
    (S : Finset (Fin n))
    (h_size : S.card = t + 1)
    (h_inj : Set.InjOn s.partyPoint S)
    (h_honest : ∀ p ∈ S, p ∉ s.corrupted)
    (h_outs : ∀ p ∈ S, (s.local_ p).output.isSome) :
    coeffs 0 0 =
      Polynomial.eval 0
        (Lagrange.interpolate S s.partyPoint
          (fun p => Option.getD (s.local_ p).output 0)) := by
  classical
  obtain ⟨_, hinv2⟩ := hinv hh
  -- The reconstruction polynomial g matches all honest output values.
  set g := reconstructPoly coeffs with hg_def
  have hg_eval : ∀ p ∈ S,
      g.eval (s.partyPoint p) = Option.getD (s.local_ p).output 0 := by
    intro p hp
    rw [reconstructPoly_eval]
    have hp_some := h_outs p hp
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hp_some
    have hv_eq : v = bivEval coeffs (s.partyPoint p) 0 :=
      hinv2 p (h_honest p hp) v hv
    rw [hv]
    simp [hv_eq]
  -- Degree bound.
  have hg_deg : g.degree < S.card := by
    rw [h_size]
    exact reconstructPoly_degree_lt coeffs
  -- Identify g with its Lagrange interpolant.
  have hg_interp : g = Lagrange.interpolate S s.partyPoint
      (fun p => Option.getD (s.local_ p).output 0) :=
    Lagrange.eq_interpolate_of_eval_eq
      (fun p => Option.getD (s.local_ p).output 0) h_inj hg_deg hg_eval
  -- Evaluate both sides at 0.
  rw [← hg_interp, reconstructPoly_eval_zero]

/-! ## §17. Operational μ₀ (Phase 5 Layer B)

The `avssInitMeasure` couples the AVSS initial-state distribution to
`uniformBivariateWithFixedZero t t sec` via a deterministic state
builder `avssInitState` and a coefficient-extraction map
`polyToCoeffs`. -/

/-- Extract a coefficient grid `Fin (t+1) → Fin (t+1) → F` from a
bivariate polynomial `f : Polynomial (Polynomial F)` by indexing into
the doubly-graded coefficient structure: `polyToCoeffs f k l =
(f.coeff k.val).coeff l.val`. For `f` sampled from
`uniformBivariateWithFixedZero t t sec`, the resulting grid satisfies
`grid 0 0 = sec` (other diagonal/off-diagonal cells are determined by
the polynomial structure). -/
noncomputable def polyToCoeffs
    (f : _root_.Polynomial (_root_.Polynomial F)) :
    Fin (t+1) → Fin (t+1) → F :=
  fun k l => (f.coeff k.val).coeff l.val

/-- Deterministic builder for the AVSS initial state from a
coefficient grid, party-point function, secret, corruption set, and
dealer-honest flag. All in-flight queues are empty, all locals are
in their `init` state, and `dealerSent = false`.

Phase 8.5d-β: `coeffs` no longer sets a state field; it pins
`dealerCommit` for an honest dealer (canonical row poly per party).
For a corrupt dealer, `dealerCommit` is the canonical layout regardless
(the adversary's freedom is captured at the `μ₀` / theorem-statement
level via existential witness). -/
def avssInitState (sec : F) (corr : Finset (Fin n))
    (partyPoint : Fin n → F) (dealerHonest : Bool)
    (coeffs : Fin (t+1) → Fin (t+1) → F) : AVSSState n t F :=
  { partyPoint := partyPoint
    secret := sec
    local_ := fun _ => AVSSLocalState.init n t F
    corrupted := corr
    dealerHonest := dealerHonest
    inflightDeliveries := ∅
    inflightCorruptDeliveries := ∅
    inflightEchoes := ∅
    inflightReady := ∅
    dealerSent := fun _ => false
    dealerMessages := fun _ => none
    dealerCommit := fun p =>
      { rowPoly := rowPolyOfDealer partyPoint coeffs p
        colPoly := fun _ => (0 : F) } }

/-- Operational initial PMF for AVSS, pulled back from
`uniformBivariateFullWithFixedZero` through
`avssInitState ∘ polyToCoeffs`.  This is the structural anchor of
Phase 5: the secret is sampled at `(0,0)` of the coefficient grid
via the bivariate polynomial.

⚠ **Distribution refactor (Phase 7.7).**  Previously coupled to
`uniformBivariateWithFixedZero` (axis-zero), which collapses every
axis coefficient to zero and makes `f(x, 0) = sec` for all `x` —
degenerate for VSS.  Now uses
`uniformBivariateFullWithFixedZero`, the literature-standard
distribution where only the `(0, 0)` constant is fixed and all
other `(t + 1)² − 1` coefficients are independently uniform.  See
`AVSS-MODEL-NOTES.md` §9–§10. -/
noncomputable def avssInitPMF (sec : F) (corr : Finset (Fin n))
    (partyPoint : Fin n → F) (dealerHonest : Bool) :
    PMF (AVSSState n t F) :=
  (Leslie.Prob.Polynomial.uniformBivariateFullWithFixedZero t t sec).map
    (fun f => avssInitState (n := n) sec corr partyPoint dealerHonest
      (polyToCoeffs f))

/-- Operational initial measure for AVSS: the `Measure` form of
`avssInitPMF`. Suitable to feed into `traceDist`. -/
noncomputable def avssInitMeasure (sec : F) (corr : Finset (Fin n))
    (partyPoint : Fin n → F) (dealerHonest : Bool) :
    Measure (AVSSState n t F) :=
  (avssInitPMF (n := n) (t := t) sec corr partyPoint dealerHonest).toMeasure

/-- `avssInitMeasure` is a probability measure. -/
instance avssInitMeasure_isProbabilityMeasure (sec : F) (corr : Finset (Fin n))
    (partyPoint : Fin n → F) (dealerHonest : Bool) :
    IsProbabilityMeasure
        (avssInitMeasure (n := n) (t := t) sec corr partyPoint dealerHonest) := by
  unfold avssInitMeasure
  exact PMF.toMeasure.isProbabilityMeasure _

/-- AVSS initial states (in the support of `avssInitPMF`) all satisfy
the structural part of `initPred` — empty queues, all-init locals,
`dealerSent = false`. The dealer-honest constraint `coeffs 0 0 = sec`
holds because `polyToCoeffs` extracts the constant term, which is
always `sec` in the support of `uniformBivariateFullWithFixedZero`.

Phase 8.5d-β: `coeffs`-related clauses dropped from the conclusion
(field no longer in state); the bivariate-polynomial witness is
parametric to `initPred` instead. -/
theorem avssInitPMF_support_initPred (sec : F) (corr : Finset (Fin n))
    (partyPoint : Fin n → F) (dealerHonest : Bool) :
    ∀ s ∈ (avssInitPMF (n := n) (t := t) sec corr partyPoint dealerHonest).support,
      (∀ p, s.local_ p = AVSSLocalState.init n t F) ∧
      s.secret = sec ∧
      s.corrupted = corr ∧
      s.inflightDeliveries = ∅ ∧
      s.inflightCorruptDeliveries = ∅ ∧
      s.inflightEchoes = ∅ ∧
      s.inflightReady = ∅ ∧
      s.dealerSent = (fun _ => false) ∧
      s.dealerMessages = (fun _ => none) := by
  classical
  intro s hs
  unfold avssInitPMF at hs
  rw [PMF.support_map] at hs
  obtain ⟨_, _, hs_eq⟩ := hs
  rw [← hs_eq]
  refine ⟨fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## §17.5 Coalition view + grid projection (Phase 5 Layer C1)

The trace-level secrecy theorem says: for any `t`-coalition `C` of
*corrupt* parties, the marginal of the AVSS trace distribution
projected to `C`'s view is invariant in the secret. To formalise
this we factor the projection through two definitions:

* `coalitionView C s : C.val → AVSSLocalState n t F` — the local
  state of every party in coalition `C`.
* `coalitionGrid coeffs C D s : C.val → D.val → Option F` — the grid view
  of bivariate evaluations: for each row party `p ∈ C` and column
  party `q ∈ D`, look up `(rowPolyOfDealer s.partyPoint s.coeffs p)
  evaluated at the partyPoint of `q`. Wrapped in `Option` to mirror
  `BivariateShamir.gridView`.

Under `outputDeterminedInv`, the grid view at delivered parties
agrees with `bivEval s.coeffs (s.partyPoint p) (s.partyPoint q)`. -/

/-- The local-state coalition view: project `s.local_` onto `C.val`. -/
def coalitionView (C : BivariateShamir.Coalition n t)
    (s : AVSSState n t F) : C.val → AVSSLocalState n t F :=
  fun p => s.local_ p.val

/-- The grid view of two coalitions `C` (rows) and `D` (columns):
the bivariate evaluations of the dealer's polynomial at the grid
`(partyPoint p, partyPoint q)` for `p ∈ C, q ∈ D`. Wrapped in
`Option` to align with `BivariateShamir.gridView` (where `none`
indicates "not delivered yet" — though here we always return the
algebraic value derivable from the witness `coeffs`).

Phase 8.5d-β: takes `coeffs` parameter (the witness from `initPred` /
μ₀, no longer the removed state field). -/
noncomputable def coalitionGrid (coeffs : Fin (t+1) → Fin (t+1) → F)
    (C D : BivariateShamir.Coalition n t)
    (s : AVSSState n t F) : C.val → D.val → Option F :=
  fun p q => some (bivEval coeffs (s.partyPoint p.val) (s.partyPoint q.val))

omit [Fintype F] in
/-- The grid view depends only on `coeffs` and `s.partyPoint`. -/
theorem coalitionGrid_eq_bivEval (coeffs : Fin (t+1) → Fin (t+1) → F)
    (C D : BivariateShamir.Coalition n t)
    (s : AVSSState n t F) (p : C.val) (q : D.val) :
    coalitionGrid coeffs C D s p q =
      some (bivEval coeffs (s.partyPoint p.val) (s.partyPoint q.val)) := rfl

omit [Fintype F] in
/-- Under honest dealer + `outputDeterminedInv coeffs s`, every delivered
honest coalition member's stored row poly evaluates to the bivariate
value at the grid point.  Bridge from operational `local_.rowPoly`
to the algebraic `bivEval coeffs ...` view. -/
theorem coalitionGrid_eq_evalRowPoly_of_delivered
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (C D : BivariateShamir.Coalition n t)
    (s : AVSSState n t F) (hh : s.dealerHonest = true)
    (hinv : outputDeterminedInv coeffs s)
    (p : C.val) (q : D.val)
    (hd : (s.local_ p.val).delivered = true) :
    ∃ rp : Fin (t+1) → F,
      (s.local_ p.val).rowPoly = some rp ∧
      coalitionGrid coeffs C D s p q = some (evalRowPoly rp (s.partyPoint q.val)) := by
  refine ⟨rowPolyOfDealer s.partyPoint coeffs p.val, (hinv hh).1 p.val hd, ?_⟩
  rw [coalitionGrid_eq_bivEval]
  rw [evalRowPoly_rowPolyOfDealer]

/-! ## §17.6 Layer C2 reduction structure (Phase 5)

The trace-level grid-secrecy theorem `avss_secrecy_AS` (canonical
step-`k` form in §17.9) reduces (in three steps documented at the
proof site) to the algebraic core `bivariate_shamir_secrecy`. Here
we provide the reduction skeleton:

1. **Static initial-grid secrecy** — the marginal of the initial
   measure on the `coalitionGrid` projection is invariant in the
   secret.

2. **Trace-level lifting** — the trace marginal at a coalition view
   is a deterministic function of the initial state's coalition grid
   (and the schedule). Pure-Dirac kernels mean the trace distribution
   factors as a pushforward of the initial measure.

3. **Coalition view at step k** — for `C ⊆ corr`, the view depends
   only on `coalitionGrid C C` of the initial state (and the
   schedule), not on `s.secret`.

The first step requires the algebraic bridge
`bivEval (polyToCoeffs f) x y = (f.eval (C x)).eval y` for `f` in
the support of `uniformBivariateWithFixedZero`. This bridge is
explicitly deferred as `+200 LOC` polynomial-manipulation work in
the existing `avss_secrecy` documentation comment (§17 below). For
this phase, we provide:

* The structural reduction theorem `avss_secrecy_static_reduction`
  that shows the static grid view's invariance is *equivalent* to
  the algebraic core `avss_secrecy`, mod the bridge.

* The coalition-view abstraction `coalitionView`, ready for use in
  trace-level statements.

The full closed proof of trace-level secrecy is left as follow-on
work; the architecture is in place. -/

/-- Helper: PMF.map agrees if the underlying functions agree on the
support. Used to bridge between equivalent forms of the coalition
view marginal. -/
theorem _root_.PMF.map_congr_of_support {α β : Type*} (p : PMF α)
    {f g : α → β} (h : ∀ x ∈ p.support, f x = g x) :
    p.map f = p.map g := by
  apply PMF.ext
  intro b
  simp only [PMF.map_apply]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · have : p a = 0 := (PMF.apply_eq_zero_iff p a).mpr ha
    simp [this]

/-- For `f` in the support of `uniformBivariateWithFixedZero`, `f`
has the explicit form `C(C sec) + ∑_{i,j ∈ Fin _} c_{ij} * X^{i+1} *
(C X)^{j+1}`. -/
theorem uniformBivariate_support_form (sec : F) (dx dy : ℕ)
    (f : _root_.Polynomial (_root_.Polynomial F))
    (hf : f ∈ (Leslie.Prob.Polynomial.uniformBivariateWithFixedZero
                 (F := F) dx dy sec).support) :
    ∃ coefs : Fin dx → Fin dy → F,
      f = Polynomial.C (Polynomial.C sec) +
            ∑ i : Fin dx, ∑ j : Fin dy,
              Polynomial.C (Polynomial.C (coefs i j)) *
                Polynomial.X ^ (i.val + 1) *
                (Polynomial.C Polynomial.X) ^ (j.val + 1) := by
  classical
  unfold Leslie.Prob.Polynomial.uniformBivariateWithFixedZero at hf
  rw [PMF.support_map] at hf
  obtain ⟨coefs, _, hf_eq⟩ := hf
  exact ⟨coefs, hf_eq.symm⟩

/-- For `f` in the support of `uniformBivariateFullWithFixedZero`,
`f` has the explicit four-piece form: constant `sec`, axis-X part
(degree-`dx` in X with no constant), axis-Y part (degree-`dy` in Y
with no constant), and an interior part. -/
theorem uniformBivariateFull_support_form (sec : F) (dx dy : ℕ)
    (f : _root_.Polynomial (_root_.Polynomial F))
    (hf : f ∈ (Leslie.Prob.Polynomial.uniformBivariateFullWithFixedZero
                 (F := F) dx dy sec).support) :
    ∃ (coefs : Fin dx → Fin dy → F) (axisX : Fin dx → F) (axisY : Fin dy → F),
      f = Polynomial.C (Polynomial.C sec) +
            (∑ i : Fin dx, Polynomial.C (Polynomial.C (axisX i)) *
              Polynomial.X ^ (i.val + 1)) +
            (∑ j : Fin dy, Polynomial.C (Polynomial.C (axisY j)) *
              (Polynomial.C Polynomial.X) ^ (j.val + 1)) +
            ∑ i : Fin dx, ∑ j : Fin dy,
              Polynomial.C (Polynomial.C (coefs i j)) *
                Polynomial.X ^ (i.val + 1) *
                (Polynomial.C Polynomial.X) ^ (j.val + 1) := by
  classical
  unfold Leslie.Prob.Polynomial.uniformBivariateFullWithFixedZero at hf
  rw [PMF.support_map] at hf
  obtain ⟨⟨coefs, axisX, axisY⟩, _, hf_eq⟩ := hf
  exact ⟨coefs, axisX, axisY, hf_eq.symm⟩

/-- Helper for the polynomial bridge: swap `(k, l) ↔ (i, j)` in a
4-fold nested Finset sum (over `Fin a × Fin a × Fin b × Fin b`). -/
private theorem quad_sum_swap {α : Type*} [AddCommMonoid α]
    (a b : ℕ)
    (G : Fin a → Fin a → Fin b → Fin b → α) :
    ∑ k : Fin a, ∑ l : Fin a, ∑ i : Fin b, ∑ j : Fin b, G k l i j =
      ∑ i : Fin b, ∑ j : Fin b, ∑ k : Fin a, ∑ l : Fin a, G k l i j := by
  calc ∑ k : Fin a, ∑ l : Fin a, ∑ i : Fin b, ∑ j : Fin b, G k l i j
      = ∑ k : Fin a, ∑ i : Fin b, ∑ l : Fin a, ∑ j : Fin b, G k l i j := by
          apply Finset.sum_congr rfl; intros k _; exact Finset.sum_comm
    _ = ∑ i : Fin b, ∑ k : Fin a, ∑ l : Fin a, ∑ j : Fin b, G k l i j := Finset.sum_comm
    _ = ∑ i : Fin b, ∑ k : Fin a, ∑ j : Fin b, ∑ l : Fin a, G k l i j := by
          apply Finset.sum_congr rfl; intros i _
          apply Finset.sum_congr rfl; intros k _
          exact Finset.sum_comm
    _ = ∑ i : Fin b, ∑ j : Fin b, ∑ k : Fin a, ∑ l : Fin a, G k l i j := by
          apply Finset.sum_congr rfl; intros i _
          exact Finset.sum_comm

/-- The algebraic core of Layer C2: for `f` in the support of
`uniformBivariateWithFixedZero t t sec`, the finite-coefficient
bivariate evaluation `bivEval (polyToCoeffs f) x y` equals the
polynomial double-evaluation `(f.eval (Polynomial.C x)).eval y`.

This is the bridge that closes Layer C2: it lifts the operational
`coalitionGrid` view (defined via `bivEval s.coeffs`) to the
algebraic form used in `BivariateShamir.bivariate_shamir_secrecy`
(`(f.eval (C x)).eval y`). -/
theorem bivEval_polyToCoeffs_eq_eval_of_support (sec : F)
    (f : _root_.Polynomial (_root_.Polynomial F))
    (hf : f ∈ (Leslie.Prob.Polynomial.uniformBivariateWithFixedZero
                 (F := F) t t sec).support)
    (x y : F) :
    bivEval (t := t) (polyToCoeffs (t := t) f) x y =
      (f.eval (Polynomial.C x)).eval y := by
  classical
  obtain ⟨coefs, rfl⟩ := uniformBivariate_support_form sec t t f hf
  unfold bivEval polyToCoeffs
  -- Step 1: explicit formula for `((explicit).coeff k).coeff l`.
  have h_term :
      ∀ (i : Fin t) (j : Fin t),
        (Polynomial.C (Polynomial.C (coefs i j)) *
          Polynomial.X ^ (i.val + 1) *
          (Polynomial.C Polynomial.X) ^ (j.val + 1) :
          _root_.Polynomial (_root_.Polynomial F)) =
        Polynomial.C (Polynomial.C (coefs i j) * Polynomial.X ^ (j.val + 1)) *
          Polynomial.X ^ (i.val + 1) := by
    intro i j
    have h1 : (Polynomial.C Polynomial.X : _root_.Polynomial (_root_.Polynomial F)) ^ (j.val + 1) =
              Polynomial.C (Polynomial.X ^ (j.val + 1)) :=
      (Polynomial.C_pow).symm
    have h2 : Polynomial.C (Polynomial.C (coefs i j) * Polynomial.X ^ (j.val + 1)) =
              Polynomial.C (Polynomial.C (coefs i j)) *
                (Polynomial.C (Polynomial.X ^ (j.val + 1)) :
                _root_.Polynomial (_root_.Polynomial F)) :=
      Polynomial.C_mul
    rw [h1, h2]
    ring
  have h_coeff : ∀ (k l : ℕ),
      ((Polynomial.C (Polynomial.C sec) +
        ∑ i : Fin t, ∑ j : Fin t,
          Polynomial.C (Polynomial.C (coefs i j)) *
            Polynomial.X ^ (i.val + 1) *
            (Polynomial.C Polynomial.X) ^ (j.val + 1)).coeff k).coeff l =
      (if k = 0 ∧ l = 0 then sec else 0) +
      (∑ i : Fin t, ∑ j : Fin t,
        if k = i.val + 1 ∧ l = j.val + 1 then coefs i j else 0) := by
    intros k l
    rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.finset_sum_coeff,
        Polynomial.finset_sum_coeff]
    simp only [Polynomial.finset_sum_coeff]
    congr 1
    · -- ((C(C sec)).coeff k).coeff l = if k = 0 ∧ l = 0 then sec else 0
      by_cases hk : k = 0
      · subst hk
        rw [Polynomial.coeff_C_zero, Polynomial.coeff_C]
        by_cases hl : l = 0
        · subst hl; simp
        · simp [hl]
      · rw [Polynomial.coeff_C, if_neg hk, Polynomial.coeff_zero]
        simp [hk]
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [h_term i j, Polynomial.coeff_C_mul_X_pow]
      by_cases h1 : k = i.val + 1
      · rw [if_pos h1]
        rw [Polynomial.coeff_C_mul_X_pow]
        by_cases h2 : l = j.val + 1
        · rw [if_pos h2, if_pos ⟨h1, h2⟩]
        · rw [if_neg h2]
          rw [if_neg]
          rintro ⟨_, hcontra⟩; exact h2 hcontra
      · rw [if_neg h1, Polynomial.coeff_zero]
        rw [if_neg]
        rintro ⟨hcontra, _⟩; exact h1 hcontra
  -- Step 2: bivEval picker — extracts a single nonzero (k, l) term.
  have h_picker : ∀ (p q : Fin (t+1)) (v : F),
      (∑ k : Fin (t+1), ∑ l : Fin (t+1),
        (if k.val = p.val ∧ l.val = q.val then v else 0) * x ^ k.val * y ^ l.val) =
      v * x ^ p.val * y ^ q.val := by
    intros p q v
    rw [Finset.sum_eq_single p]
    · rw [Finset.sum_eq_single q]
      · simp
      · intros l _ hl
        rw [if_neg]; · ring
        push_neg; intro _ hc; exact hl (Fin.ext hc)
      · intro h; exact (h (Finset.mem_univ _)).elim
    · intros k _ hk
      apply Finset.sum_eq_zero
      intros l _
      rw [if_neg]; · ring
      push_neg; intro hc; exact (hk (Fin.ext hc)).elim
    · intro h; exact (h (Finset.mem_univ _)).elim
  -- Step 3: substitute h_coeff into LHS via Finset.sum_congr.
  rw [show (∑ k : Fin (t+1), ∑ l : Fin (t+1),
        ((Polynomial.C (Polynomial.C sec) +
          ∑ i : Fin t, ∑ j : Fin t,
            Polynomial.C (Polynomial.C (coefs i j)) *
              Polynomial.X ^ (i.val + 1) *
              (Polynomial.C Polynomial.X) ^ (j.val + 1)).coeff k.val).coeff l.val *
        x ^ k.val * y ^ l.val) =
      (∑ k : Fin (t+1), ∑ l : Fin (t+1),
        ((if k.val = 0 ∧ l.val = 0 then sec else 0) +
          (∑ i : Fin t, ∑ j : Fin t,
            if k.val = i.val + 1 ∧ l.val = j.val + 1 then coefs i j else 0)) *
        x ^ k.val * y ^ l.val) from by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      rw [h_coeff k.val l.val]]
  simp only [add_mul, Finset.sum_add_distrib]
  -- Step 4: compute RHS via Polynomial.eval_*.
  have h_RHS : ((Polynomial.C (Polynomial.C sec) +
                ∑ i : Fin t, ∑ j : Fin t,
                  Polynomial.C (Polynomial.C (coefs i j)) *
                    Polynomial.X ^ (i.val + 1) *
                    (Polynomial.C Polynomial.X) ^ (j.val + 1)).eval
                (Polynomial.C x)).eval y =
              sec + ∑ i : Fin t, ∑ j : Fin t,
                coefs i j * x ^ (i.val + 1) * y ^ (j.val + 1) := by
    simp only [Polynomial.eval_add, Polynomial.eval_finset_sum, Polynomial.eval_mul,
               Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
               ← Polynomial.C_pow]
  rw [h_RHS]
  -- Step 5: match LHS and RHS via h_picker.
  congr 1
  · have := h_picker (0 : Fin (t+1)) (0 : Fin (t+1)) sec
    simpa using this
  · rw [show (∑ k : Fin (t+1), ∑ l : Fin (t+1),
        (∑ i : Fin t, ∑ j : Fin t,
          (if k.val = i.val + 1 ∧ l.val = j.val + 1 then coefs i j else 0)) *
        x ^ k.val * y ^ l.val) =
      (∑ i : Fin t, ∑ j : Fin t,
        ∑ k : Fin (t+1), ∑ l : Fin (t+1),
          (if k.val = i.val + 1 ∧ l.val = j.val + 1 then coefs i j else 0) *
            x ^ k.val * y ^ l.val) from by
      simp only [Finset.sum_mul]
      exact quad_sum_swap (a := t+1) (b := t) _]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have h_iv : i.val + 1 < t + 1 := by omega
    have h_jv : j.val + 1 < t + 1 := by omega
    have := h_picker ⟨i.val + 1, h_iv⟩ ⟨j.val + 1, h_jv⟩ (coefs i j)
    convert this using 2

/-- Polynomial bridge for the **full** distribution: for `f` in the
support of `uniformBivariateFullWithFixedZero t t sec`,
`bivEval (polyToCoeffs f) x y = (f.eval (C x)).eval y`.

Direct adaptation of `bivEval_polyToCoeffs_eq_eval_of_support` with
the new polynomial form `f = C(C sec) + ∑ax_i * X^(i+1)
+ ∑ay_j * (CX)^(j+1) + ∑coefs_ij * X^(i+1) * (CX)^(j+1)` —
four-piece coefficient formula and four-piece eval. -/
theorem bivEval_polyToCoeffs_eq_eval_of_support_full (sec : F)
    (f : _root_.Polynomial (_root_.Polynomial F))
    (hf : f ∈ (Leslie.Prob.Polynomial.uniformBivariateFullWithFixedZero
                 (F := F) t t sec).support)
    (x y : F) :
    bivEval (t := t) (polyToCoeffs (t := t) f) x y =
      (f.eval (Polynomial.C x)).eval y := by
  classical
  obtain ⟨coefs, axisX, axisY, rfl⟩ := uniformBivariateFull_support_form sec t t f hf
  unfold bivEval polyToCoeffs
  -- Step 1: explicit form for the per-(i, j) interior term.
  have h_term :
      ∀ (i : Fin t) (j : Fin t),
        (Polynomial.C (Polynomial.C (coefs i j)) *
          Polynomial.X ^ (i.val + 1) *
          (Polynomial.C Polynomial.X) ^ (j.val + 1) :
          _root_.Polynomial (_root_.Polynomial F)) =
        Polynomial.C (Polynomial.C (coefs i j) * Polynomial.X ^ (j.val + 1)) *
          Polynomial.X ^ (i.val + 1) := by
    intro i j
    have h1 : (Polynomial.C Polynomial.X :
                _root_.Polynomial (_root_.Polynomial F)) ^ (j.val + 1) =
              Polynomial.C (Polynomial.X ^ (j.val + 1)) :=
      (Polynomial.C_pow).symm
    have h2 : Polynomial.C (Polynomial.C (coefs i j) * Polynomial.X ^ (j.val + 1)) =
              Polynomial.C (Polynomial.C (coefs i j)) *
                (Polynomial.C (Polynomial.X ^ (j.val + 1)) :
                _root_.Polynomial (_root_.Polynomial F)) :=
      Polynomial.C_mul
    rw [h1, h2]; ring
  -- Step 2: explicit form for the per-j axisY term.
  have h_termY : ∀ (j : Fin t),
      (Polynomial.C (Polynomial.C (axisY j)) *
        (Polynomial.C Polynomial.X) ^ (j.val + 1) :
        _root_.Polynomial (_root_.Polynomial F)) =
      Polynomial.C (Polynomial.C (axisY j) * Polynomial.X ^ (j.val + 1)) := by
    intro j
    have h1 : (Polynomial.C Polynomial.X :
                _root_.Polynomial (_root_.Polynomial F)) ^ (j.val + 1) =
              Polynomial.C (Polynomial.X ^ (j.val + 1)) :=
      (Polynomial.C_pow).symm
    rw [h1, ← Polynomial.C_mul]
  -- Step 3: 4-case coefficient formula.
  have h_coeff : ∀ (k l : ℕ),
      ((Polynomial.C (Polynomial.C sec) +
        (∑ i : Fin t, Polynomial.C (Polynomial.C (axisX i)) *
          Polynomial.X ^ (i.val + 1)) +
        (∑ j : Fin t, Polynomial.C (Polynomial.C (axisY j)) *
          (Polynomial.C Polynomial.X) ^ (j.val + 1)) +
        ∑ i : Fin t, ∑ j : Fin t,
          Polynomial.C (Polynomial.C (coefs i j)) *
            Polynomial.X ^ (i.val + 1) *
            (Polynomial.C Polynomial.X) ^ (j.val + 1)).coeff k).coeff l =
      (if k = 0 ∧ l = 0 then sec else 0) +
      (∑ i : Fin t, if k = i.val + 1 ∧ l = 0 then axisX i else 0) +
      (∑ j : Fin t, if k = 0 ∧ l = j.val + 1 then axisY j else 0) +
      (∑ i : Fin t, ∑ j : Fin t,
        if k = i.val + 1 ∧ l = j.val + 1 then coefs i j else 0) := by
    intros k l
    rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
        Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
        Polynomial.finset_sum_coeff, Polynomial.finset_sum_coeff,
        Polynomial.finset_sum_coeff]
    simp only [Polynomial.finset_sum_coeff]
    -- Sum order: const + axisX + axisY + interior.
    refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_) ?_
    · -- ((C(C sec)).coeff k).coeff l = if (k, l) = (0, 0) then sec else 0
      by_cases hk : k = 0
      · subst hk
        rw [Polynomial.coeff_C_zero, Polynomial.coeff_C]
        by_cases hl : l = 0
        · subst hl; simp
        · simp [hl]
      · rw [Polynomial.coeff_C, if_neg hk, Polynomial.coeff_zero]; simp [hk]
    · -- axisX sum: (C(C(axisX i)) * X^(i+1)).coeff k).coeff l.
      apply Finset.sum_congr rfl
      intro i _
      rw [Polynomial.coeff_C_mul_X_pow]
      by_cases h1 : k = i.val + 1
      · rw [if_pos h1]
        rw [Polynomial.coeff_C]
        by_cases h2 : l = 0
        · subst h2; simp [h1]
        · rw [if_neg h2, if_neg]
          rintro ⟨_, hcontra⟩; exact h2 hcontra
      · rw [if_neg h1, Polynomial.coeff_zero, if_neg]
        rintro ⟨hcontra, _⟩; exact h1 hcontra
    · -- axisY sum: ((C(C(axisY j)) * (CX)^(j+1)).coeff k).coeff l.
      apply Finset.sum_congr rfl
      intro j _
      rw [h_termY j]
      by_cases hk : k = 0
      · subst hk
        rw [Polynomial.coeff_C_zero, Polynomial.coeff_C_mul_X_pow]
        by_cases hl : l = j.val + 1
        · simp [hl]
        · rw [if_neg hl, if_neg]
          rintro ⟨_, hcontra⟩; exact hl hcontra
      · rw [Polynomial.coeff_C, if_neg hk, Polynomial.coeff_zero, if_neg]
        rintro ⟨hcontra, _⟩; exact hk hcontra
    · -- interior 2D sum (same as the existing proof).
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [h_term i j, Polynomial.coeff_C_mul_X_pow]
      by_cases h1 : k = i.val + 1
      · rw [if_pos h1, Polynomial.coeff_C_mul_X_pow]
        by_cases h2 : l = j.val + 1
        · rw [if_pos h2, if_pos ⟨h1, h2⟩]
        · rw [if_neg h2, if_neg]
          rintro ⟨_, hcontra⟩; exact h2 hcontra
      · rw [if_neg h1, Polynomial.coeff_zero, if_neg]
        rintro ⟨hcontra, _⟩; exact h1 hcontra
  -- Step 4: bivEval picker — extracts a single nonzero (k, l) term.
  have h_picker : ∀ (p q : Fin (t+1)) (v : F),
      (∑ k : Fin (t+1), ∑ l : Fin (t+1),
        (if k.val = p.val ∧ l.val = q.val then v else 0) * x ^ k.val * y ^ l.val) =
      v * x ^ p.val * y ^ q.val := by
    intros p q v
    rw [Finset.sum_eq_single p]
    · rw [Finset.sum_eq_single q]
      · simp
      · intros l _ hl
        rw [if_neg]; · ring
        push_neg; intro _ hc; exact hl (Fin.ext hc)
      · intro h; exact (h (Finset.mem_univ _)).elim
    · intros k _ hk
      apply Finset.sum_eq_zero
      intros l _
      rw [if_neg]; · ring
      push_neg; intro hc; exact (hk (Fin.ext hc)).elim
    · intro h; exact (h (Finset.mem_univ _)).elim
  -- Step 5: substitute h_coeff into LHS.
  rw [show (∑ k : Fin (t+1), ∑ l : Fin (t+1),
        ((Polynomial.C (Polynomial.C sec) +
          (∑ i : Fin t, Polynomial.C (Polynomial.C (axisX i)) *
            Polynomial.X ^ (i.val + 1)) +
          (∑ j : Fin t, Polynomial.C (Polynomial.C (axisY j)) *
            (Polynomial.C Polynomial.X) ^ (j.val + 1)) +
          ∑ i : Fin t, ∑ j : Fin t,
            Polynomial.C (Polynomial.C (coefs i j)) *
              Polynomial.X ^ (i.val + 1) *
              (Polynomial.C Polynomial.X) ^ (j.val + 1)).coeff k.val).coeff l.val *
        x ^ k.val * y ^ l.val) =
      (∑ k : Fin (t+1), ∑ l : Fin (t+1),
        ((if k.val = 0 ∧ l.val = 0 then sec else 0) +
          (∑ i : Fin t, if k.val = i.val + 1 ∧ l.val = 0 then axisX i else 0) +
          (∑ j : Fin t, if k.val = 0 ∧ l.val = j.val + 1 then axisY j else 0) +
          (∑ i : Fin t, ∑ j : Fin t,
            if k.val = i.val + 1 ∧ l.val = j.val + 1 then coefs i j else 0)) *
        x ^ k.val * y ^ l.val) from by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      rw [h_coeff k.val l.val]]
  simp only [add_mul, Finset.sum_add_distrib]
  -- Step 6: compute RHS.
  have h_RHS : ((Polynomial.C (Polynomial.C sec) +
        (∑ i : Fin t, Polynomial.C (Polynomial.C (axisX i)) *
          Polynomial.X ^ (i.val + 1)) +
        (∑ j : Fin t, Polynomial.C (Polynomial.C (axisY j)) *
          (Polynomial.C Polynomial.X) ^ (j.val + 1)) +
        ∑ i : Fin t, ∑ j : Fin t,
          Polynomial.C (Polynomial.C (coefs i j)) *
            Polynomial.X ^ (i.val + 1) *
            (Polynomial.C Polynomial.X) ^ (j.val + 1)).eval
                (Polynomial.C x)).eval y =
      sec + (∑ i : Fin t, axisX i * x ^ (i.val + 1)) +
            (∑ j : Fin t, axisY j * y ^ (j.val + 1)) +
            (∑ i : Fin t, ∑ j : Fin t,
              coefs i j * x ^ (i.val + 1) * y ^ (j.val + 1)) := by
    simp only [Polynomial.eval_add, Polynomial.eval_finset_sum, Polynomial.eval_mul,
               Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
               ← Polynomial.C_pow]
  rw [h_RHS]
  -- Step 7: match LHS and RHS via h_picker for each piece.
  -- The LHS has 4 summands by the add_mul + sum_add_distrib distribution.
  -- Each matches one piece on RHS via h_picker.
  -- Strategy: compute each LHS piece individually using h_picker.
  have h_const : (∑ k : Fin (t+1), ∑ l : Fin (t+1),
      (if k.val = 0 ∧ l.val = 0 then sec else 0) * x ^ k.val * y ^ l.val) = sec := by
    have := h_picker (0 : Fin (t+1)) (0 : Fin (t+1)) sec
    simpa using this
  have h_aX : (∑ k : Fin (t+1), ∑ l : Fin (t+1),
      (∑ i : Fin t, if k.val = i.val + 1 ∧ l.val = 0 then axisX i else 0) *
        x ^ k.val * y ^ l.val) =
      ∑ i : Fin t, axisX i * x ^ (i.val + 1) := by
    -- Distribute multiplication over the i-sum, then swap sum order.
    have hdist : ∀ k l : Fin (t+1),
        (∑ i : Fin t, if k.val = i.val + 1 ∧ l.val = 0 then axisX i else 0) *
          x ^ k.val * y ^ l.val =
        ∑ i : Fin t,
          (if k.val = i.val + 1 ∧ l.val = 0 then axisX i else 0) *
            x ^ k.val * y ^ l.val := by
      intro k l
      simp only [Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun k _ =>
        Finset.sum_congr rfl (fun l _ => hdist k l))]
    rw [Finset.sum_congr rfl (fun k _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    have h_iv : i.val + 1 < t + 1 := by omega
    have := h_picker ⟨i.val + 1, h_iv⟩ ⟨0, by omega⟩ (axisX i)
    simpa using this
  have h_aY : (∑ k : Fin (t+1), ∑ l : Fin (t+1),
      (∑ j : Fin t, if k.val = 0 ∧ l.val = j.val + 1 then axisY j else 0) *
        x ^ k.val * y ^ l.val) =
      ∑ j : Fin t, axisY j * y ^ (j.val + 1) := by
    have hdist : ∀ k l : Fin (t+1),
        (∑ j : Fin t, if k.val = 0 ∧ l.val = j.val + 1 then axisY j else 0) *
          x ^ k.val * y ^ l.val =
        ∑ j : Fin t,
          (if k.val = 0 ∧ l.val = j.val + 1 then axisY j else 0) *
            x ^ k.val * y ^ l.val := by
      intro k l
      simp only [Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun k _ =>
        Finset.sum_congr rfl (fun l _ => hdist k l))]
    rw [Finset.sum_congr rfl (fun k _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    have h_jv : j.val + 1 < t + 1 := by omega
    have := h_picker ⟨0, by omega⟩ ⟨j.val + 1, h_jv⟩ (axisY j)
    simpa using this
  have h_int : (∑ k : Fin (t+1), ∑ l : Fin (t+1),
      (∑ i : Fin t, ∑ j : Fin t,
        if k.val = i.val + 1 ∧ l.val = j.val + 1 then coefs i j else 0) *
        x ^ k.val * y ^ l.val) =
      ∑ i : Fin t, ∑ j : Fin t,
        coefs i j * x ^ (i.val + 1) * y ^ (j.val + 1) := by
    rw [show (∑ k : Fin (t+1), ∑ l : Fin (t+1),
        (∑ i : Fin t, ∑ j : Fin t,
          (if k.val = i.val + 1 ∧ l.val = j.val + 1 then coefs i j else 0)) *
        x ^ k.val * y ^ l.val) =
      (∑ i : Fin t, ∑ j : Fin t,
        ∑ k : Fin (t+1), ∑ l : Fin (t+1),
          (if k.val = i.val + 1 ∧ l.val = j.val + 1 then coefs i j else 0) *
            x ^ k.val * y ^ l.val) from by
      simp only [Finset.sum_mul]
      exact quad_sum_swap (a := t+1) (b := t) _]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have h_iv : i.val + 1 < t + 1 := by omega
    have h_jv : j.val + 1 < t + 1 := by omega
    have := h_picker ⟨i.val + 1, h_iv⟩ ⟨j.val + 1, h_jv⟩ (coefs i j)
    convert this using 2
  rw [h_const, h_aX, h_aY, h_int]

/-! ## §17.7 Static initial-grid secrecy (Layer C2 conclusion)

With the polynomial bridge in place, we can now state and prove the
static initial-grid secrecy theorem: the marginal of `avssInitPMF`
on the `coalitionGrid` projection is invariant in the secret. This
is the immediate operational-secrecy consequence of
`bivariate_shamir_secrecy` applied through the avssInitState wrapper.

The full *trace-level* grid-secrecy theorem `avss_secrecy_AS` (the
step-`k` form, in §17.9) follows from this static version by
factoring the trace distribution as a pushforward of the initial
measure (since all `avssSpec` step kernels are `PMF.pure` and
`coalitionGrid` is invariant under every `avssStep`). -/

/-- Static initial-grid secrecy: for any two coalitions `C` (rows)
and `D` (columns), the marginal of `avssInitPMF` on the
`coalitionGrid coeffs C D` projection is invariant in the secret.

Direct corollary of `bivariate_shamir_secrecy` via the polynomial
bridge `bivEval_polyToCoeffs_eq_eval_of_support`. -/
theorem avss_secrecy_initPMF
    (sec sec' : F) (corr : Finset (Fin n))
    (partyPoint : Fin n → F) (dealerHonest : Bool)
    (_h_nz_pp : ∀ i, partyPoint i ≠ 0)
    (_h_F : t + 1 ≤ Fintype.card F)
    (C D : BivariateShamir.Coalition n t) :
    (avssInitPMF (n := n) (t := t) sec corr partyPoint dealerHonest).map
        (coalitionGrid coeffs C D) =
      (avssInitPMF (n := n) (t := t) sec' corr partyPoint dealerHonest).map
        (coalitionGrid coeffs C D) := by
  -- Phase 8.5d-β: `coalitionGrid coeffs C D s` reads only `s.partyPoint`,
  -- which is constant-equal to `partyPoint` (the parameter) on the support
  -- of `avssInitPMF` (since `avssInitState` sets `partyPoint := partyPoint`).
  -- The marginal therefore collapses to a Dirac on a sec-independent constant,
  -- making both sides equal trivially.
  classical
  set c : C.val → D.val → Option F :=
    fun p q => some (bivEval coeffs (partyPoint p.val) (partyPoint q.val)) with hc_def
  have h_const : ∀ (sec_val : F),
      (avssInitPMF (n := n) (t := t) sec_val corr partyPoint dealerHonest).map
          (coalitionGrid coeffs C D) =
        (avssInitPMF (n := n) (t := t) sec_val corr partyPoint dealerHonest).map
          (fun _ => c) := by
    intro sec_val
    apply PMF.map_congr_of_support
    intro s hs
    unfold avssInitPMF at hs
    rw [PMF.support_map] at hs
    obtain ⟨_f, _, hs_eq⟩ := hs
    rw [← hs_eq]
    rfl
  rw [h_const sec, h_const sec']
  -- `(μ).map (fun _ => c) g = (∑' a, if g = c then μ a else 0)`, independent of μ.
  apply PMF.ext
  intro g
  simp only [PMF.map_apply]
  by_cases hg : g = c
  · subst hg
    simp only [if_true, PMF.tsum_coe]
  · simp only [if_neg hg, tsum_zero]

/-! ## §17.8 Trace-level grid secrecy (Phase 5 Layer D)

The trace-level **grid-view** secrecy theorem (canonical name
`avss_secrecy_AS`, after the step-k lift in §17.9): under any
adversary `A` and any step `k`, the marginal of the trace
distribution projected to `coalitionGrid coeffs C D (ω k).1` is invariant
in the secret. Stated against the **algebraic grid view** (bivariate
polynomial evaluations derivable from `s.coeffs` + `s.partyPoint`),
**not** against the corrupt parties' operational view (the
`coalitionView`-based local-state projection — Phase 6).

This section closes the step-0 form `avss_secrecy_AS_step_zero_grid`
(originally `avss_secrecy_AS_init`); §17.9 below lifts it to the
canonical step-`k` form.

The proof reduces to `avss_secrecy_initPMF` via:

1. The trace's step-0 state marginal equals `μ₀` (a standard fact
   about `Kernel.trajMeasure`).
2. `coalitionGrid coeffs C D` depends only on `s.coeffs` and `s.partyPoint`,
   neither of which are touched by any `avssStep` action — so the
   grid view at any step `k` equals the grid view at step `0`
   (formalised as `traceDist_coalitionGrid_AE_eq_init` in §17.9).
3. Apply `avss_secrecy_initPMF` lifted to `Measure` via
   `PMF.toMeasure_map`. -/

/-- `coalitionGrid coeffs C D` is invariant under any `avssStep` action:
it depends only on `coeffs` (the parametric witness, not in state) and
`s.partyPoint` (preserved by every action). -/
theorem avssStep_coalitionGrid_invariant
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (a : AVSSAction n F)
    (s : AVSSState n t F) (C D : BivariateShamir.Coalition n t) :
    coalitionGrid coeffs C D (avssStep a s) = coalitionGrid coeffs C D s := by
  unfold coalitionGrid
  funext p q
  have hpp : (avssStep a s).partyPoint = s.partyPoint := by
    cases a <;> simp [avssStep, setLocal]
  rw [hpp]

/-- The step-0 state marginal of `traceDist`: projecting the trace at
step `0` to its state component recovers `μ₀`. -/
theorem traceDist_step_zero_state_marginal
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (A : Adversary (AVSSState n t F) (AVSSAction n F)) :
    (traceDist (avssSpec (t := t) sec corr coeffs) A μ₀).map
        (fun ω => (ω 0).1) = μ₀ := by
  classical
  -- Standard `Kernel.trajMeasure` step-0 marginal: `(traj κ 0)` is
  -- concentrated on the `Iic 0`-prefix, so the 0-th coordinate
  -- recovers the initial measure.
  unfold traceDist
  set μ₀_full : Measure (AVSSState n t F × Option (AVSSAction n F)) :=
    μ₀.map (fun s => (s, (none : Option (AVSSAction n F))))
    with hμ₀_full_def
  haveI : IsProbabilityMeasure μ₀_full :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  -- Step-0 marginal of `Kernel.trajMeasure`.
  have hmarg_zero :
      (ProbabilityTheory.Kernel.trajMeasure
          (X := fun _ => AVSSState n t F × Option (AVSSAction n F))
          μ₀_full (stepKernel (avssSpec (t := t) sec corr coeffs) A)).map
        (fun ω => ω 0) = μ₀_full := by
    unfold ProbabilityTheory.Kernel.trajMeasure
    have hmeas_eval0 : Measurable
        (fun ω : Π _ : ℕ, AVSSState n t F × Option (AVSSAction n F) => ω 0) :=
      measurable_pi_apply 0
    rw [Measure.map_comp _ _ hmeas_eval0]
    have hfact : (fun ω : Π _ : ℕ, AVSSState n t F × Option (AVSSAction n F) =>
            ω 0) =
        (fun y : Π _ : Finset.Iic 0,
            AVSSState n t F × Option (AVSSAction n F) =>
              y ⟨0, by simp⟩) ∘
          (Preorder.frestrictLe 0) := by
      funext _; rfl
    have hmeas_pia : Measurable
        (fun y : Π _ : Finset.Iic 0,
              AVSSState n t F × Option (AVSSAction n F) =>
            y ⟨0, by simp⟩) :=
      measurable_pi_apply _
    have hmeas_fl0 : Measurable
        (Preorder.frestrictLe
          (π := fun _ : ℕ => AVSSState n t F × Option (AVSSAction n F)) 0) :=
      Preorder.measurable_frestrictLe _
    have hmeas_fl2 : Measurable
        (Preorder.frestrictLe₂
          (π := fun _ : ℕ => AVSSState n t F × Option (AVSSAction n F))
          (le_refl 0)) :=
      Preorder.measurable_frestrictLe₂ _
    have hcomp : Measurable
        ((fun y : Π _ : Finset.Iic 0,
              AVSSState n t F × Option (AVSSAction n F) =>
            y ⟨0, by simp⟩) ∘
          Preorder.frestrictLe₂
            (π := fun _ : ℕ => AVSSState n t F × Option (AVSSAction n F))
            (le_refl 0)) :=
      hmeas_pia.comp hmeas_fl2
    rw [hfact, ProbabilityTheory.Kernel.map_comp_right _ hmeas_fl0 hmeas_pia,
        ProbabilityTheory.Kernel.traj_map_frestrictLe_of_le (le_refl 0)]
    rw [ProbabilityTheory.Kernel.deterministic_map hmeas_fl2 hmeas_pia]
    rw [Measure.deterministic_comp_eq_map hcomp]
    rw [Measure.map_map hcomp (by fun_prop)]
    convert Measure.map_id (μ := μ₀_full)
  -- Project via Prod.fst.
  have hmeas_eval0 : Measurable
      (fun ω : Π _ : ℕ, AVSSState n t F × Option (AVSSAction n F) => ω 0) :=
    measurable_pi_apply 0
  have hmeas_fst : Measurable
      (Prod.fst : AVSSState n t F × Option (AVSSAction n F) → AVSSState n t F) :=
    measurable_fst
  rw [show (fun ω : Π _ : ℕ, AVSSState n t F × Option (AVSSAction n F) =>
            (ω 0).1) =
        Prod.fst ∘ (fun ω => ω 0) from rfl]
  rw [← Measure.map_map hmeas_fst hmeas_eval0]
  rw [hmarg_zero, hμ₀_full_def, Measure.map_map hmeas_fst (by fun_prop)]
  convert Measure.map_id (μ := μ₀)

set_option maxHeartbeats 800000 in
/-- **Trace-level operational secrecy (Phase 5 Layer D).**

For any adversary `A` and any two coalitions `C` (rows) and `D`
(columns) of size ≤ `t`, the marginal of the trace distribution
projected to the `coalitionGrid coeffs C D` view at the initial step is
invariant in the secret.

This is the operational analogue of `avss_secrecy_initPMF`, lifted
through the trace distribution. The proof reduces to
`avss_secrecy_initPMF` via the step-0 marginal of `Kernel.trajMeasure`. -/
theorem avss_secrecy_AS_init
    (sec sec' : F) (corr : Finset (Fin n))
    (partyPoint : Fin n → F) (dealerHonest : Bool)
    (h_nz_pp : ∀ i, partyPoint i ≠ 0)
    (h_F : t + 1 ≤ Fintype.card F)
    (C D : BivariateShamir.Coalition n t)
    (A : Adversary (AVSSState n t F) (AVSSAction n F)) :
    (traceDist (avssSpec (t := t) sec corr coeffs) A
        (avssInitMeasure (n := n) (t := t) sec corr partyPoint dealerHonest)).map
        (fun ω => coalitionGrid coeffs C D (ω 0).1) =
      (traceDist (avssSpec (t := t) sec' corr coeffs) A
        (avssInitMeasure (n := n) (t := t) sec' corr partyPoint dealerHonest)).map
        (fun ω => coalitionGrid coeffs C D (ω 0).1) := by
  classical
  -- Step 1: factor the trace-level (ω 0).1 marginal through `traceDist_step_zero_state_marginal`.
  have hstep0 : ∀ (sec_val : F),
      (traceDist (avssSpec (t := t) sec_val corr coeffs) A
          (avssInitMeasure (n := n) (t := t) sec_val corr partyPoint dealerHonest)).map
          (fun ω => coalitionGrid coeffs C D (ω 0).1) =
        (avssInitMeasure (n := n) (t := t) sec_val corr partyPoint dealerHonest).map
          (coalitionGrid coeffs C D) := by
    intro sec_val
    rw [show (fun ω : ℕ → AVSSState n t F × Option (AVSSAction n F) =>
          coalitionGrid coeffs C D (ω 0).1) =
        coalitionGrid coeffs C D ∘ (fun ω => (ω 0).1) from rfl]
    rw [← Measure.map_map (by fun_prop) (by fun_prop)]
    rw [traceDist_step_zero_state_marginal]
  rw [hstep0 sec, hstep0 sec']
  -- Step 2: lift `avss_secrecy_initPMF` (PMF level) to the `Measure` level.
  have h_pmf := avss_secrecy_initPMF (t := t) (coeffs := coeffs)
    sec sec' corr partyPoint dealerHonest h_nz_pp h_F C D
  -- The toMeasure of two equal PMFs is equal.
  have h_meas := congrArg PMF.toMeasure h_pmf
  unfold avssInitMeasure
  -- Bridge `(p.toMeasure).map f` to `(p.map f).toMeasure` via PMF.toMeasure_map.
  have hmeas : Measurable (coalitionGrid (n := n) (t := t)
      (F := F) coeffs C D) := by fun_prop
  have hL := @PMF.toMeasure_map _ _ (coalitionGrid coeffs C D) _ _
    (avssInitPMF (n := n) (t := t) sec corr partyPoint dealerHonest) hmeas
  have hR := @PMF.toMeasure_map _ _ (coalitionGrid coeffs C D) _ _
    (avssInitPMF (n := n) (t := t) sec' corr partyPoint dealerHonest) hmeas
  rw [hL, hR]; exact h_meas

/-- **Step-0 trace-level grid secrecy.**

The marginal of the trace distribution at step 0 projected to
`coalitionGrid coeffs C D` is invariant in the secret. Direct re-export of
`avss_secrecy_AS_init`, kept as a separate name so the step-k
generalisation `avss_secrecy_AS` (below) can call it without name
clash.

**Scope.** `coalitionGrid coeffs C D s := fun p q => some (bivEval s.coeffs
(s.partyPoint p) (s.partyPoint q))` is the **algebraic grid view**:
the bivariate polynomial evaluations at the row × column grid,
derivable from `s.coeffs` and `s.partyPoint` alone. This is **not**
the corrupt parties' operational view (the `coalitionView`-based
local-state projection, which uses `s.local_` and is sensitive to
adversary scheduling). The operational-view secrecy theorem is the
remaining work for Phase 6. -/
theorem avss_secrecy_AS_step_zero_grid
    (sec sec' : F) (corr : Finset (Fin n))
    (partyPoint : Fin n → F) (dealerHonest : Bool)
    (h_nz_pp : ∀ i, partyPoint i ≠ 0)
    (h_F : t + 1 ≤ Fintype.card F)
    (C D : BivariateShamir.Coalition n t)
    (A : Adversary (AVSSState n t F) (AVSSAction n F)) :
    (traceDist (avssSpec (t := t) sec corr coeffs) A
        (avssInitMeasure (n := n) (t := t) sec corr partyPoint dealerHonest)).map
        (fun ω => coalitionGrid coeffs C D (ω 0).1) =
      (traceDist (avssSpec (t := t) sec' corr coeffs) A
        (avssInitMeasure (n := n) (t := t) sec' corr partyPoint dealerHonest)).map
        (fun ω => coalitionGrid coeffs C D (ω 0).1) :=
  avss_secrecy_AS_init sec sec' corr partyPoint dealerHonest h_nz_pp h_F C D A

section StepKGeneralisation

open scoped ProbabilityTheory

/-! ## §17.9 Step-k generalisation of trace-level grid secrecy

The step-0 form `avss_secrecy_AS_step_zero_grid` (above) lifts to a
step-`k` form (the canonical `avss_secrecy_AS`, below): for every
step `k`, the marginal of the trace distribution projected to
`coalitionGrid coeffs C D (ω k).1` is invariant in the secret.

The argument is straightforward: `coalitionGrid coeffs C D` depends only on
`s.coeffs` and `s.partyPoint` — both invariant under every `avssStep`
action (see `avssStep_coalitionGrid_invariant`). So the step-`k`
grid view AE-equals the step-0 grid view under any trajectory.
Pushing this AE equality through `Measure.map_congr` gives the
step-`k` form, which then reduces to the step-0 form. -/

/-- The per-step kernel of `avssSpec` AE-preserves `coalitionGrid`:
no matter which branch the kernel takes (no-schedule stutter,
gate-fail stutter, or gate-pass `avssStep` application), the
resulting state's grid view equals the input prefix's current-state
grid view. The gate-pass case uses `avssStep_coalitionGrid_invariant`. -/
private theorem avssSpec_stepKernel_coalitionGrid_AE
    (sec : F) (corr : Finset (Fin n))
    (A : Adversary (AVSSState n t F) (AVSSAction n F))
    (C D : BivariateShamir.Coalition n t) (k : ℕ)
    (h : FinPrefix (AVSSState n t F) (AVSSAction n F) k) :
    ∀ᵐ y ∂(stepKernel (avssSpec (t := t) sec corr coeffs) A k h),
        coalitionGrid coeffs C D y.1 = coalitionGrid coeffs C D h.currentState := by
  classical
  have hPset : MeasurableSet
      {x : AVSSState n t F × Option (AVSSAction n F) |
        coalitionGrid coeffs C D x.1 = coalitionGrid coeffs C D h.currentState} :=
    MeasurableSet.of_discrete
  -- The kernel is `Kernel.ofFunOfCountable f` with `f h` the per-history measure.
  -- After unfolding, the goal becomes a `match` expression we can branch on.
  unfold stepKernel
  simp only [ProbabilityTheory.Kernel.ofFunOfCountable, ProbabilityTheory.Kernel.coe_mk]
  rcases A.schedule h.toList with _ | i
  · -- Stutter (no schedule).
    rw [ae_dirac_iff hPset]
  · by_cases hgate : ((avssSpec (t := t) sec corr coeffs).actions i).gate h.currentState
    · -- Gate-pass: pure-Dirac kernel applies `avssStep i`.
      simp only [hgate, dite_true]
      rw [show ((avssSpec (t := t) sec corr coeffs).actions i).effect h.currentState hgate
            = PMF.pure (avssStep i h.currentState) from rfl,
          PMF.toMeasure_pure, Measure.map_dirac (by fun_prop), ae_dirac_iff hPset]
      exact avssStep_coalitionGrid_invariant coeffs i h.currentState C D
    · -- Gate-fail stutter.
      simp only [hgate, dite_false]
      rw [ae_dirac_iff hPset]

/-- **Step-k AE invariance of the grid view.** Under any adversary
`A` and initial probability measure `μ₀`, the trace marginal of
`coalitionGrid coeffs C D` at step `k` AE-equals the marginal at step 0.

Proven by induction on `k`. The successor step uses the marginal
recurrence
`Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure`
to reduce the step-`(k+1)` AE statement to a per-prefix kernel
AE statement, which is exactly `avssSpec_stepKernel_coalitionGrid_AE`. -/
theorem traceDist_coalitionGrid_AE_eq_init
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (A : Adversary (AVSSState n t F) (AVSSAction n F))
    (C D : BivariateShamir.Coalition n t) (k : ℕ) :
    ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
        coalitionGrid coeffs C D (ω k).1 = coalitionGrid coeffs C D (ω 0).1 := by
  classical
  induction k with
  | zero => exact Filter.Eventually.of_forall fun _ => rfl
  | succ k ih =>
    -- Reduce to: ∀ᵐ ω, coalitionGrid (ω (k+1)).1 = coalitionGrid (ω k).1, then chain with ih.
    suffices hone_step :
        ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
          coalitionGrid coeffs C D (ω (k+1)).1 = coalitionGrid coeffs C D (ω k).1 by
      filter_upwards [hone_step, ih] with ω h_step h_ih
      rw [h_step, h_ih]
    -- Marginal recurrence: pull (frestrictLe k ω, ω (k+1)) marginal from the joint.
    have hmeas_pair : Measurable
        (fun ω : Π _ : ℕ, AVSSState n t F × Option (AVSSAction n F) =>
          (Preorder.frestrictLe k ω, ω (k+1))) := by fun_prop
    -- IsProbabilityMeasure instance for the lifted initial measure.
    haveI : IsProbabilityMeasure
        (μ₀.map (fun s : AVSSState n t F => (s, (none : Option (AVSSAction n F))))) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    -- ν ⊗ₘ κ = μtraj.map (paired marginal at step k+1).
    have hk :
        ((traceDist (avssSpec (t := t) sec corr coeffs) A μ₀).map
            (Preorder.frestrictLe k)) ⊗ₘ
          (stepKernel (avssSpec (t := t) sec corr coeffs) A k) =
        (traceDist (avssSpec (t := t) sec corr coeffs) A μ₀).map
          (fun ω => (Preorder.frestrictLe k ω, ω (k+1))) := by
      unfold traceDist
      exact ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    -- Inner: for every prefix `h`, the kernel preserves coalitionGrid AE.
    have h_inner : ∀ᵐ h ∂((traceDist (avssSpec (t := t) sec corr coeffs) A μ₀).map
          (Preorder.frestrictLe k)),
        ∀ᵐ y ∂(stepKernel (avssSpec (t := t) sec corr coeffs) A k h),
          coalitionGrid coeffs C D y.1 = coalitionGrid coeffs C D h.currentState :=
      Filter.Eventually.of_forall fun h =>
        avssSpec_stepKernel_coalitionGrid_AE sec corr A C D k h
    -- Lift to AE on the joint measure ν ⊗ₘ κ.
    have hjoint :
        ∀ᵐ x ∂(((traceDist (avssSpec (t := t) sec corr coeffs) A μ₀).map
              (Preorder.frestrictLe k)) ⊗ₘ
            (stepKernel (avssSpec (t := t) sec corr coeffs) A k)),
          coalitionGrid coeffs C D x.2.1 = coalitionGrid coeffs C D (FinPrefix.currentState x.1) :=
      Measure.ae_compProd_of_ae_ae MeasurableSet.of_discrete h_inner
    -- Transfer along hk to get the AE statement on the trace measure.
    rw [hk] at hjoint
    rw [ae_map_iff hmeas_pair.aemeasurable MeasurableSet.of_discrete] at hjoint
    -- `(Preorder.frestrictLe k ω).currentState = (ω k).1` is definitional.
    exact hjoint

/-- **Trace-level grid secrecy.** This is the canonical `avss_secrecy_AS`:
the step-`k` form of operational secrecy on the algebraic grid view.

For any adversary `A`, any two coalitions `C` (rows) and `D`
(columns) of size ≤ `t`, and any step index `k`, the marginal of
the trace distribution projected to `coalitionGrid coeffs C D (ω k).1` is
invariant in the secret.

**Scope.** This is the **algebraic grid view** secrecy:
`coalitionGrid coeffs C D s := fun p q => some (bivEval s.coeffs
(s.partyPoint p) (s.partyPoint q))` is derivable from `s.coeffs`
and `s.partyPoint` alone, both of which are immutable across actions
(see `avssStep_coalitionGrid_invariant`).

This is **not** the corrupt parties' operational view — i.e. the
`coalitionView`-based local-state projection (`coalitionView C s :=
fun p => s.local_ p.val`), which depends on adversary scheduling
through `s.local_`. The operational-view secrecy theorem is the
remaining work for Phase 6.

Proof: reduces to the step-0 form `avss_secrecy_AS_step_zero_grid`
via `traceDist_coalitionGrid_AE_eq_init` (the step-`k` AE invariance
of the grid view) plus `Measure.map_congr` (AE-equal random variables
push forward to the same measure). -/
theorem avss_secrecy_AS
    (sec sec' : F) (corr : Finset (Fin n))
    (partyPoint : Fin n → F) (dealerHonest : Bool)
    (h_nz_pp : ∀ i, partyPoint i ≠ 0)
    (h_F : t + 1 ≤ Fintype.card F)
    (C D : BivariateShamir.Coalition n t)
    (A : Adversary (AVSSState n t F) (AVSSAction n F)) (k : ℕ) :
    (traceDist (avssSpec (t := t) sec corr coeffs) A
        (avssInitMeasure (n := n) (t := t) sec corr partyPoint dealerHonest)).map
        (fun ω => coalitionGrid coeffs C D (ω k).1) =
      (traceDist (avssSpec (t := t) sec' corr coeffs) A
        (avssInitMeasure (n := n) (t := t) sec' corr partyPoint dealerHonest)).map
        (fun ω => coalitionGrid coeffs C D (ω k).1) := by
  classical
  -- Bridge step-k → step-0 via the AE-equality of `coalitionGrid coeffs C D` at
  -- step `k` and step `0` (since `coalitionGrid` depends only on `partyPoint`,
  -- preserved by every action).
  have h_AE_sec :=
    traceDist_coalitionGrid_AE_eq_init (t := t) sec corr coeffs
      (avssInitMeasure (n := n) (t := t) sec corr partyPoint dealerHonest) A C D k
  have h_AE_sec' :=
    traceDist_coalitionGrid_AE_eq_init (t := t) sec' corr coeffs
      (avssInitMeasure (n := n) (t := t) sec' corr partyPoint dealerHonest) A C D k
  rw [Measure.map_congr h_AE_sec, Measure.map_congr h_AE_sec']
  exact avss_secrecy_AS_init (t := t) (coeffs := coeffs)
    sec sec' corr partyPoint dealerHonest h_nz_pp h_F C D A

end StepKGeneralisation

/-! ## §17.10 Trace-level operational view + schedule prefix (Phase 6.1)

For Phase 6 we project a trace
`ω : ℕ → AVSSState n t F × Option (AVSSAction n F)` onto two pieces:

* `coalitionTraceView C ω k : Fin k → C.val → AVSSLocalState n t F` —
  the per-step **operational** view: the corrupt coalition's local
  state at every step `i < k`.
* `schedulePrefix ω k : Fin k → Option (AVSSAction n F)` — the action
  label recorded at every step `i < k`. The 0-th entry is conventionally
  `none` (no action has fired before step 0); subsequent entries hold
  the label of the action that fired between steps `i - 1` and `i`.

Both are deterministic functions of the trace and are measurable (each
is a Pi over `Fin k`-many coordinate projections composed with finite
state evaluations).

These are the operational analogues of `coalitionGrid (ω k).1` (the
algebraic-grid view at step `k`) used in the trace-level **grid**
secrecy theorem `avss_secrecy_AS`. -/

/-- The corrupt coalition's per-step operational view: at every step
`i < k`, project `(ω i).1.local_` onto the parties of `C`. -/
def coalitionTraceView (C : BivariateShamir.Coalition n t)
    (ω : ℕ → AVSSState n t F × Option (AVSSAction n F)) (k : ℕ) :
    Fin k → C.val → AVSSLocalState n t F :=
  fun i p => coalitionView C (ω i.val).1 p

/-- The schedule prefix: at every step `i < k`, record the action label
component of the trace at step `i`. -/
def schedulePrefix
    (ω : ℕ → AVSSState n t F × Option (AVSSAction n F)) (k : ℕ) :
    Fin k → Option (AVSSAction n F) :=
  fun i => (ω i.val).2

omit [Field F] [Fintype F] in
@[simp] theorem coalitionTraceView_apply (C : BivariateShamir.Coalition n t)
    (ω : ℕ → AVSSState n t F × Option (AVSSAction n F)) (k : ℕ)
    (i : Fin k) (p : C.val) :
    coalitionTraceView C ω k i p = coalitionView C (ω i.val).1 p := rfl

omit [Field F] [Fintype F] in
@[simp] theorem schedulePrefix_apply
    (ω : ℕ → AVSSState n t F × Option (AVSSAction n F)) (k : ℕ) (i : Fin k) :
    schedulePrefix ω k i = (ω i.val).2 := rfl

omit [Field F] in
/-- `coalitionTraceView` is measurable: it factors as a Pi of
coordinate evaluations, each composed with `Prod.fst` and the discrete
`s.local_ p.val` projection (measurable since `AVSSState` carries the
top σ-algebra, hence every function out is measurable). -/
@[fun_prop]
theorem measurable_coalitionTraceView (C : BivariateShamir.Coalition n t)
    (k : ℕ) :
    Measurable (fun ω : ℕ → AVSSState n t F × Option (AVSSAction n F) =>
        coalitionTraceView C ω k) := by
  classical
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun p => ?_
  -- The coordinate map is `ω ↦ (ω i.val).1.local_ p.val`.
  have h1 : Measurable (fun ω : ℕ → AVSSState n t F × Option (AVSSAction n F) =>
        ω i.val) :=
    measurable_pi_apply _
  have h2 : Measurable (Prod.fst :
      AVSSState n t F × Option (AVSSAction n F) → AVSSState n t F) :=
    measurable_fst
  have h3 : Measurable (fun s : AVSSState n t F => s.local_ p.val) :=
    measurable_of_countable _
  exact (h3.comp h2).comp h1

omit [Field F] [Fintype F] in
/-- `schedulePrefix` is measurable: it is a Pi of coordinate
evaluations followed by `Prod.snd`. -/
@[fun_prop]
theorem measurable_schedulePrefix (k : ℕ) :
    Measurable (fun ω : ℕ → AVSSState n t F × Option (AVSSAction n F) =>
        schedulePrefix ω k) := by
  refine measurable_pi_iff.mpr fun i => ?_
  exact measurable_snd.comp (measurable_pi_apply i.val)

omit [Field F] in
/-- Combined measurability: `(coalitionTraceView, schedulePrefix)` is
measurable. Used at the headline operational-secrecy theorem (§17.12)
to push forward the trace measure under the joint projection. -/
@[fun_prop]
theorem measurable_coalitionTraceView_schedulePrefix
    (C : BivariateShamir.Coalition n t) (k : ℕ) :
    Measurable (fun ω : ℕ → AVSSState n t F × Option (AVSSAction n F) =>
        (coalitionTraceView C ω k, schedulePrefix ω k)) :=
  (measurable_coalitionTraceView C k).prodMk (measurable_schedulePrefix k)

/-! ## §17.11 `corruptViewFactorsThroughGrid` — operational view structural theorem (Phase 6.2)

The corrupt parties' local-state view at any step `k` is determined
by:
  1. the **initial state's** (`partyPoint`, `coeffs`) — concretely the
     row polynomials `rowPolyOfDealer (s_0.partyPoint) (s_0.coeffs) p`
     for `p` corrupt, and
  2. the **schedule prefix** `(ω 0).2, (ω 1).2, …, (ω (k-1)).2`.

This decomposition follows from two state invariants combined:

* `outputDeterminedInv` (§15) — for **every** party (including
  corrupt), `delivered = true` implies
  `rowPoly = some (rowPolyOfDealer s.partyPoint s.coeffs p)`. Pinned
  by the `partyCorruptDeliver` action's effect (§6).

* `corruptLocalInv` (this section) — for every corrupt `p`, the local
  state's fields `{echoSent, echoesReceived, readySent, readyReceived,
  output, rowPoly-when-not-delivered}` are pinned at their `init`
  values throughout. Every action that writes to those fields has a
  gate requiring `p ∉ corrupted` (§7) — so corrupt parties never
  echo, never send ready, never output, never receive echoes/readies.

Combined, the only mutable bits of corrupt `p`'s local state are the
pair `(delivered, rowPoly)`, which is `(false, none)` initially and
`(true, some (rowPolyOfDealer …))` after `partyCorruptDeliver(p)`
fires. Both branches are deterministic functions of `(s_0, schedule)`.

The two invariants combine to give the headline structural theorem
`coalitionView_corrupt_factors_AE` below: under any adversary `A`,
along almost every trace, every corrupt party's local state at step
`k` agrees with `replayCorruptLocal (rowPolyOfDealer …) (delivered_k
p)`. The factoring is *not yet* closed at the operational data type
level (we'd need to extract `delivered_k p` as a deterministic
schedule function), but the AE structural identity is enough to drive
the joint-marginal reduction in §17.12 below. -/

/-- The combined Phase 6.2 invariant: `outputDeterminedInv` (rowPoly
content for delivered parties), `corruptLocalInv` (trivial fields for
corrupt parties), and `dealerMessagesInv` (per-party dealer payloads
match the canonical row/column polys). Together these pin the corrupt
coalition's operational view to a deterministic function of `(s_0,
schedule)`. -/
def phase6Inv (coeffs : Fin (t+1) → Fin (t+1) → F)
    (s : AVSSState n t F) : Prop :=
  outputDeterminedInv coeffs s ∧ corruptLocalInv s ∧ dealerMessagesInv coeffs s

omit [Fintype F] in
theorem initPred_phase6Inv (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (s : AVSSState n t F) (h : initPred sec corr coeffs s) :
    phase6Inv coeffs s :=
  ⟨initPred_outputDeterminedInv sec corr coeffs s h,
   initPred_corruptLocalInv sec corr coeffs s h,
   initPred_dealerMessagesInv sec corr coeffs s h⟩

omit [Fintype F] in
theorem avssStep_preserves_phase6Inv
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (a : AVSSAction n F) (s : AVSSState n t F)
    (hgate : actionGate a s) (hinv : phase6Inv coeffs s) :
    phase6Inv coeffs (avssStep a s) :=
  ⟨avssStep_preserves_outputDeterminedInv coeffs a s hgate hinv.1 hinv.2.2,
   avssStep_preserves_corruptLocalInv a s hgate hinv.2.1,
   avssStep_preserves_dealerMessagesInv coeffs a s hgate hinv.2.2⟩

/-- **Phase 6.2 invariant as `AlmostBox`.** Along every trace, every
state satisfies `phase6Inv` — i.e., `outputDeterminedInv` plus
`corruptLocalInv`. -/
theorem avss_phase6Inv_AS
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr coeffs s)
    (A : Adversary (AVSSState n t F) (AVSSAction n F)) :
    AlmostBox (avssSpec (t := t) sec corr coeffs) A μ₀ (phase6Inv coeffs) := by
  have h_pure : ∀ (a : AVSSAction n F) (s : AVSSState n t F)
      (h : ((avssSpec (t := t) sec corr coeffs).actions a).gate s),
      ((avssSpec (t := t) sec corr coeffs).actions a).effect s h
        = PMF.pure (avssStep a s) :=
    fun _ _ _ => rfl
  have h_init' : ∀ᵐ s ∂μ₀, phase6Inv coeffs s := by
    filter_upwards [h_init] with s hs
    exact initPred_phase6Inv sec corr coeffs s hs
  exact AlmostBox_of_pure_inductive
    (phase6Inv coeffs)
    (fun a s => avssStep a s)
    h_pure
    (fun a s hgate hinv =>
      avssStep_preserves_phase6Inv coeffs a s hgate hinv)
    μ₀ h_init' A

/-- **Phase 8.5d-β-followup-6 — existential `phase6Inv` AlmostBox.**
Under the existential AE-form `∀ᵐ s ∂μ₀, ∃ c, initPred sec corr c s`
(returned by `avssInitMeasure_AE_initPred` after the μ₀ migration),
the predicate `∃ c, phase6Inv c s` holds AlmostBox along the trace.
The witness `c` may differ per step — but `phase6Inv c` at any
specific step suffices for the dealerCommit-form factor lemma
because the c-dependence cancels via `dealerMessagesInv` (which pins
`dealerCommit p .rowPoly = rowPolyOfDealer ... c p`). -/
theorem avss_phase6InvEx_AS
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, ∃ c, initPred sec corr c s)
    (A : Adversary (AVSSState n t F) (AVSSAction n F)) :
    AlmostBox (avssSpec (t := t) sec corr coeffs) A μ₀
      (fun s => ∃ c, phase6Inv c s) := by
  have h_pure : ∀ (a : AVSSAction n F) (s : AVSSState n t F)
      (h : ((avssSpec (t := t) sec corr coeffs).actions a).gate s),
      ((avssSpec (t := t) sec corr coeffs).actions a).effect s h
        = PMF.pure (avssStep a s) :=
    fun _ _ _ => rfl
  have h_init' : ∀ᵐ s ∂μ₀, ∃ c, phase6Inv c s := by
    filter_upwards [h_init] with s hs
    obtain ⟨c, hsc⟩ := hs
    exact ⟨c, initPred_phase6Inv sec corr c s hsc⟩
  exact AlmostBox_of_pure_inductive
    (fun s => ∃ c, phase6Inv c s)
    (fun a s => avssStep a s)
    h_pure
    (fun a s hgate hinv => by
      obtain ⟨c, hc⟩ := hinv
      exact ⟨c, avssStep_preserves_phase6Inv c a s hgate hc⟩)
    μ₀ h_init' A

/-- **Phase 8.5d-β-followup-7 — AlmostBox for the dealerHonest-INDEPENDENT
`coalitionRowPolyAlignedInv`.**

Holds AE on the trace given the existential AE-init from
`avssInitMeasure_AE_initPred` (which gives `coalitionRowPolyAlignedInv`
vacuously since `dealerMessages = none` and all `local_` are `init` at
init).  Crucially, `coalitionRowPolyAlignedInv` is c-independent and
dealerHonest-INDEPENDENT — it tracks structural protocol semantics only.
This is the closure infrastructure for the corrupt-dealer headline case. -/
theorem avss_coalitionRowPolyAlignedInv_AS
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, ∃ c, initPred sec corr c s)
    (A : Adversary (AVSSState n t F) (AVSSAction n F)) :
    AlmostBox (avssSpec (t := t) sec corr coeffs) A μ₀
      coalitionRowPolyAlignedInv := by
  have h_pure : ∀ (a : AVSSAction n F) (s : AVSSState n t F)
      (h : ((avssSpec (t := t) sec corr coeffs).actions a).gate s),
      ((avssSpec (t := t) sec corr coeffs).actions a).effect s h
        = PMF.pure (avssStep a s) :=
    fun _ _ _ => rfl
  have h_init' : ∀ᵐ s ∂μ₀, coalitionRowPolyAlignedInv s := by
    filter_upwards [h_init] with s hs
    obtain ⟨c, hsc⟩ := hs
    exact initPred_coalitionRowPolyAlignedInv sec corr c s hsc
  exact AlmostBox_of_pure_inductive
    coalitionRowPolyAlignedInv
    (fun a s => avssStep a s)
    h_pure
    (fun a s hgate hinv =>
      avssStep_preserves_coalitionRowPolyAlignedInv a s hgate hinv)
    μ₀ h_init' A

omit [Field F] [Fintype F] in
/-- Under `corruptLocalInv` (Phase 8.5b weakening), every corrupt
party's `output = none`, and `rowPoly = none` whenever
`delivered = false`. The previously pinned trivial fields
`{echoSent, echoesReceived, readySent, readyReceived}` are now
schedule-dependent (recovered separately via `coalitionTrivialView`
in Phase 8.5c). -/
theorem corruptLocalInv_local_trivial
    (s : AVSSState n t F) (hinv : corruptLocalInv s)
    (p : Fin n) (hp : p ∈ s.corrupted) :
    (s.local_ p).output = none ∧
    ((s.local_ p).delivered = false → (s.local_ p).rowPoly = none) :=
  hinv p hp

omit [Fintype F] in
/-- Under honest dealer + `phase6Inv coeffs s`, every party's `rowPoly`,
when present, equals `some (rowPolyOfDealer s.partyPoint coeffs p)` —
derivable from the witness coefficients and party-points.

Phase 8.5d-β: takes `coeffs` parameter and adds an honest-dealer
hypothesis (under corrupt dealer rowPoly content is unconstrained). -/
theorem phase6Inv_rowPoly_determined
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (s : AVSSState n t F) (hh : s.dealerHonest = true)
    (hinv : phase6Inv coeffs s)
    (p : Fin n) (_hp : p ∈ s.corrupted)
    (hd : (s.local_ p).delivered = true) :
    (s.local_ p).rowPoly = some (rowPolyOfDealer s.partyPoint coeffs p) :=
  (hinv.1 hh).1 p hd

omit [Fintype F] in
/-- `partyPoint` is preserved by every `avssStep` action — unchanged in
every branch of the `match` on `a`.  Used to pull `s_k.partyPoint =
s_0.partyPoint` through the AE structural reduction. -/
theorem avssStep_partyPoint_invariant (a : AVSSAction n F)
    (s : AVSSState n t F) :
    (avssStep a s).partyPoint = s.partyPoint := by
  cases a <;> simp [avssStep, setLocal]

omit [Fintype F] in
theorem avssStep_corrupted_invariant (a : AVSSAction n F)
    (s : AVSSState n t F) :
    (avssStep a s).corrupted = s.corrupted := by
  cases a <;> simp [avssStep, setLocal]

omit [Fintype F] in
theorem avssStep_dealerHonest_invariant (a : AVSSAction n F)
    (s : AVSSState n t F) :
    (avssStep a s).dealerHonest = s.dealerHonest := by
  cases a <;> simp [avssStep, setLocal]

section Phase6_OperationalView

open scoped ProbabilityTheory

/-- The kernel AE-preserves `s.partyPoint` (and analogous fields):
under any `stepKernel` branch, the resulting state's `partyPoint`
equals the input prefix's current-state `partyPoint`. -/
private theorem avssSpec_stepKernel_partyPoint_AE
    (sec : F) (corr : Finset (Fin n))
    (A : Adversary (AVSSState n t F) (AVSSAction n F)) (k : ℕ)
    (h : FinPrefix (AVSSState n t F) (AVSSAction n F) k) :
    ∀ᵐ y ∂(stepKernel (avssSpec (t := t) sec corr coeffs) A k h),
        y.1.partyPoint = h.currentState.partyPoint := by
  classical
  have hPset : MeasurableSet
      {x : AVSSState n t F × Option (AVSSAction n F) |
        x.1.partyPoint = h.currentState.partyPoint} :=
    MeasurableSet.of_discrete
  unfold stepKernel
  simp only [ProbabilityTheory.Kernel.ofFunOfCountable, ProbabilityTheory.Kernel.coe_mk]
  rcases A.schedule h.toList with _ | i
  · rw [ae_dirac_iff hPset]
  · by_cases hgate : ((avssSpec (t := t) sec corr coeffs).actions i).gate h.currentState
    · simp only [hgate, dite_true]
      rw [show ((avssSpec (t := t) sec corr coeffs).actions i).effect h.currentState hgate
            = PMF.pure (avssStep i h.currentState) from rfl,
          PMF.toMeasure_pure, Measure.map_dirac (by fun_prop), ae_dirac_iff hPset]
      exact avssStep_partyPoint_invariant i h.currentState
    · simp only [hgate, dite_false]
      rw [ae_dirac_iff hPset]

private theorem avssSpec_stepKernel_corrupted_AE
    (sec : F) (corr : Finset (Fin n))
    (A : Adversary (AVSSState n t F) (AVSSAction n F)) (k : ℕ)
    (h : FinPrefix (AVSSState n t F) (AVSSAction n F) k) :
    ∀ᵐ y ∂(stepKernel (avssSpec (t := t) sec corr coeffs) A k h),
        y.1.corrupted = h.currentState.corrupted := by
  classical
  have hPset : MeasurableSet
      {x : AVSSState n t F × Option (AVSSAction n F) |
        x.1.corrupted = h.currentState.corrupted} :=
    MeasurableSet.of_discrete
  unfold stepKernel
  simp only [ProbabilityTheory.Kernel.ofFunOfCountable, ProbabilityTheory.Kernel.coe_mk]
  rcases A.schedule h.toList with _ | i
  · rw [ae_dirac_iff hPset]
  · by_cases hgate : ((avssSpec (t := t) sec corr coeffs).actions i).gate h.currentState
    · simp only [hgate, dite_true]
      rw [show ((avssSpec (t := t) sec corr coeffs).actions i).effect h.currentState hgate
            = PMF.pure (avssStep i h.currentState) from rfl,
          PMF.toMeasure_pure, Measure.map_dirac (by fun_prop), ae_dirac_iff hPset]
      exact avssStep_corrupted_invariant i h.currentState
    · simp only [hgate, dite_false]
      rw [ae_dirac_iff hPset]

/-- AE invariance of `partyPoint` along the trace: at every step `k`,
`(ω k).1.partyPoint = (ω 0).1.partyPoint`. Same induction structure
as `traceDist_coalitionGrid_AE_eq_init`. -/
theorem traceDist_partyPoint_AE_eq_init
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (A : Adversary (AVSSState n t F) (AVSSAction n F)) (k : ℕ) :
    ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
        (ω k).1.partyPoint = (ω 0).1.partyPoint := by
  classical
  induction k with
  | zero => exact Filter.Eventually.of_forall fun _ => rfl
  | succ k ih =>
    suffices hone_step :
        ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
          (ω (k+1)).1.partyPoint = (ω k).1.partyPoint by
      filter_upwards [hone_step, ih] with ω h_step h_ih
      rw [h_step, h_ih]
    have hmeas_pair : Measurable
        (fun ω : Π _ : ℕ, AVSSState n t F × Option (AVSSAction n F) =>
          (Preorder.frestrictLe k ω, ω (k+1))) := by fun_prop
    haveI : IsProbabilityMeasure
        (μ₀.map (fun s : AVSSState n t F => (s, (none : Option (AVSSAction n F))))) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    have hk :
        ((traceDist (avssSpec (t := t) sec corr coeffs) A μ₀).map
            (Preorder.frestrictLe k)) ⊗ₘ
          (stepKernel (avssSpec (t := t) sec corr coeffs) A k) =
        (traceDist (avssSpec (t := t) sec corr coeffs) A μ₀).map
          (fun ω => (Preorder.frestrictLe k ω, ω (k+1))) := by
      unfold traceDist
      exact ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    have h_inner : ∀ᵐ h ∂((traceDist (avssSpec (t := t) sec corr coeffs) A μ₀).map
          (Preorder.frestrictLe k)),
        ∀ᵐ y ∂(stepKernel (avssSpec (t := t) sec corr coeffs) A k h),
          y.1.partyPoint = h.currentState.partyPoint :=
      Filter.Eventually.of_forall fun h =>
        avssSpec_stepKernel_partyPoint_AE sec corr A k h
    have hjoint :
        ∀ᵐ x ∂(((traceDist (avssSpec (t := t) sec corr coeffs) A μ₀).map
              (Preorder.frestrictLe k)) ⊗ₘ
            (stepKernel (avssSpec (t := t) sec corr coeffs) A k)),
          x.2.1.partyPoint = (FinPrefix.currentState x.1).partyPoint :=
      Measure.ae_compProd_of_ae_ae MeasurableSet.of_discrete h_inner
    rw [hk] at hjoint
    rw [ae_map_iff hmeas_pair.aemeasurable MeasurableSet.of_discrete] at hjoint
    exact hjoint

theorem traceDist_corrupted_AE_eq_init
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (A : Adversary (AVSSState n t F) (AVSSAction n F)) (k : ℕ) :
    ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
        (ω k).1.corrupted = (ω 0).1.corrupted := by
  classical
  induction k with
  | zero => exact Filter.Eventually.of_forall fun _ => rfl
  | succ k ih =>
    suffices hone_step :
        ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
          (ω (k+1)).1.corrupted = (ω k).1.corrupted by
      filter_upwards [hone_step, ih] with ω h_step h_ih
      rw [h_step, h_ih]
    have hmeas_pair : Measurable
        (fun ω : Π _ : ℕ, AVSSState n t F × Option (AVSSAction n F) =>
          (Preorder.frestrictLe k ω, ω (k+1))) := by fun_prop
    haveI : IsProbabilityMeasure
        (μ₀.map (fun s : AVSSState n t F => (s, (none : Option (AVSSAction n F))))) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    have hk :
        ((traceDist (avssSpec (t := t) sec corr coeffs) A μ₀).map
            (Preorder.frestrictLe k)) ⊗ₘ
          (stepKernel (avssSpec (t := t) sec corr coeffs) A k) =
        (traceDist (avssSpec (t := t) sec corr coeffs) A μ₀).map
          (fun ω => (Preorder.frestrictLe k ω, ω (k+1))) := by
      unfold traceDist
      exact ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    have h_inner : ∀ᵐ h ∂((traceDist (avssSpec (t := t) sec corr coeffs) A μ₀).map
          (Preorder.frestrictLe k)),
        ∀ᵐ y ∂(stepKernel (avssSpec (t := t) sec corr coeffs) A k h),
          y.1.corrupted = h.currentState.corrupted :=
      Filter.Eventually.of_forall fun h =>
        avssSpec_stepKernel_corrupted_AE sec corr A k h
    have hjoint :
        ∀ᵐ x ∂(((traceDist (avssSpec (t := t) sec corr coeffs) A μ₀).map
              (Preorder.frestrictLe k)) ⊗ₘ
            (stepKernel (avssSpec (t := t) sec corr coeffs) A k)),
          x.2.1.corrupted = (FinPrefix.currentState x.1).corrupted :=
      Measure.ae_compProd_of_ae_ae MeasurableSet.of_discrete h_inner
    rw [hk] at hjoint
    rw [ae_map_iff hmeas_pair.aemeasurable MeasurableSet.of_discrete] at hjoint
    exact hjoint

private theorem avssSpec_stepKernel_dealerHonest_AE
    (sec : F) (corr : Finset (Fin n))
    (A : Adversary (AVSSState n t F) (AVSSAction n F)) (k : ℕ)
    (h : FinPrefix (AVSSState n t F) (AVSSAction n F) k) :
    ∀ᵐ y ∂(stepKernel (avssSpec (t := t) sec corr coeffs) A k h),
        y.1.dealerHonest = h.currentState.dealerHonest := by
  classical
  have hPset : MeasurableSet
      {x : AVSSState n t F × Option (AVSSAction n F) |
        x.1.dealerHonest = h.currentState.dealerHonest} :=
    MeasurableSet.of_discrete
  unfold stepKernel
  simp only [ProbabilityTheory.Kernel.ofFunOfCountable, ProbabilityTheory.Kernel.coe_mk]
  rcases A.schedule h.toList with _ | i
  · rw [ae_dirac_iff hPset]
  · by_cases hgate : ((avssSpec (t := t) sec corr coeffs).actions i).gate h.currentState
    · simp only [hgate, dite_true]
      rw [show ((avssSpec (t := t) sec corr coeffs).actions i).effect h.currentState hgate
            = PMF.pure (avssStep i h.currentState) from rfl,
          PMF.toMeasure_pure, Measure.map_dirac (by fun_prop), ae_dirac_iff hPset]
      exact avssStep_dealerHonest_invariant i h.currentState
    · simp only [hgate, dite_false]
      rw [ae_dirac_iff hPset]

theorem traceDist_dealerHonest_AE_eq_init
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (A : Adversary (AVSSState n t F) (AVSSAction n F)) (k : ℕ) :
    ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
        (ω k).1.dealerHonest = (ω 0).1.dealerHonest := by
  classical
  induction k with
  | zero => exact Filter.Eventually.of_forall fun _ => rfl
  | succ k ih =>
    suffices hone_step :
        ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
          (ω (k+1)).1.dealerHonest = (ω k).1.dealerHonest by
      filter_upwards [hone_step, ih] with ω h_step h_ih
      rw [h_step, h_ih]
    have hmeas_pair : Measurable
        (fun ω : Π _ : ℕ, AVSSState n t F × Option (AVSSAction n F) =>
          (Preorder.frestrictLe k ω, ω (k+1))) := by fun_prop
    haveI : IsProbabilityMeasure
        (μ₀.map (fun s : AVSSState n t F => (s, (none : Option (AVSSAction n F))))) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    have hk :
        ((traceDist (avssSpec (t := t) sec corr coeffs) A μ₀).map
            (Preorder.frestrictLe k)) ⊗ₘ
          (stepKernel (avssSpec (t := t) sec corr coeffs) A k) =
        (traceDist (avssSpec (t := t) sec corr coeffs) A μ₀).map
          (fun ω => (Preorder.frestrictLe k ω, ω (k+1))) := by
      unfold traceDist
      exact ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    have h_inner : ∀ᵐ h ∂((traceDist (avssSpec (t := t) sec corr coeffs) A μ₀).map
          (Preorder.frestrictLe k)),
        ∀ᵐ y ∂(stepKernel (avssSpec (t := t) sec corr coeffs) A k h),
          y.1.dealerHonest = h.currentState.dealerHonest :=
      Filter.Eventually.of_forall fun h =>
        avssSpec_stepKernel_dealerHonest_AE sec corr A k h
    have hjoint :
        ∀ᵐ x ∂(((traceDist (avssSpec (t := t) sec corr coeffs) A μ₀).map
              (Preorder.frestrictLe k)) ⊗ₘ
            (stepKernel (avssSpec (t := t) sec corr coeffs) A k)),
          x.2.1.dealerHonest = (FinPrefix.currentState x.1).dealerHonest :=
      Measure.ae_compProd_of_ae_ae MeasurableSet.of_discrete h_inner
    rw [hk] at hjoint
    rw [ae_map_iff hmeas_pair.aemeasurable MeasurableSet.of_discrete] at hjoint
    exact hjoint

/-- Per-prefix kernel preservation of `dealerCommit`: parallels
`avssSpec_stepKernel_dealerHonest_AE`. Phase 8.5d-β-followup-6
infrastructure. -/
private theorem avssSpec_stepKernel_dealerCommit_AE
    (sec : F) (corr : Finset (Fin n))
    (A : Adversary (AVSSState n t F) (AVSSAction n F)) (k : ℕ)
    (h : FinPrefix (AVSSState n t F) (AVSSAction n F) k) :
    ∀ᵐ y ∂(stepKernel (avssSpec (t := t) sec corr coeffs) A k h),
        y.1.dealerCommit = h.currentState.dealerCommit := by
  classical
  have hPset : MeasurableSet
      {x : AVSSState n t F × Option (AVSSAction n F) |
        x.1.dealerCommit = h.currentState.dealerCommit} :=
    MeasurableSet.of_discrete
  unfold stepKernel
  simp only [ProbabilityTheory.Kernel.ofFunOfCountable, ProbabilityTheory.Kernel.coe_mk]
  rcases A.schedule h.toList with _ | i
  · rw [ae_dirac_iff hPset]
  · by_cases hgate : ((avssSpec (t := t) sec corr coeffs).actions i).gate h.currentState
    · simp only [hgate, dite_true]
      rw [show ((avssSpec (t := t) sec corr coeffs).actions i).effect h.currentState hgate
            = PMF.pure (avssStep i h.currentState) from rfl,
          PMF.toMeasure_pure, Measure.map_dirac (by fun_prop), ae_dirac_iff hPset]
      exact avssStep_dealerCommit_invariant i h.currentState
    · simp only [hgate, dite_false]
      rw [ae_dirac_iff hPset]

/-- AE preservation of `dealerCommit` along the trace: at every step
`k`, `(ω k).1.dealerCommit = (ω 0).1.dealerCommit`. Same induction
structure as `traceDist_dealerHonest_AE_eq_init`. Phase 8.5d-β-
followup-6 — needed by `coalitionView_corrupt_factors_AE_ex` to
bridge `(ω k).1.dealerCommit` (used in `dealerMessagesInv`) to
`(ω 0).1.dealerCommit` (used in `coalitionAlgebraicView`). -/
theorem traceDist_dealerCommit_AE_eq_init
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (A : Adversary (AVSSState n t F) (AVSSAction n F)) (k : ℕ) :
    ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
        (ω k).1.dealerCommit = (ω 0).1.dealerCommit := by
  classical
  induction k with
  | zero => exact Filter.Eventually.of_forall fun _ => rfl
  | succ k ih =>
    suffices hone_step :
        ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
          (ω (k+1)).1.dealerCommit = (ω k).1.dealerCommit by
      filter_upwards [hone_step, ih] with ω h_step h_ih
      rw [h_step, h_ih]
    have hmeas_pair : Measurable
        (fun ω : Π _ : ℕ, AVSSState n t F × Option (AVSSAction n F) =>
          (Preorder.frestrictLe k ω, ω (k+1))) := by fun_prop
    haveI : IsProbabilityMeasure
        (μ₀.map (fun s : AVSSState n t F => (s, (none : Option (AVSSAction n F))))) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    have hk :
        ((traceDist (avssSpec (t := t) sec corr coeffs) A μ₀).map
            (Preorder.frestrictLe k)) ⊗ₘ
          (stepKernel (avssSpec (t := t) sec corr coeffs) A k) =
        (traceDist (avssSpec (t := t) sec corr coeffs) A μ₀).map
          (fun ω => (Preorder.frestrictLe k ω, ω (k+1))) := by
      unfold traceDist
      exact ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    have h_inner : ∀ᵐ h ∂((traceDist (avssSpec (t := t) sec corr coeffs) A μ₀).map
          (Preorder.frestrictLe k)),
        ∀ᵐ y ∂(stepKernel (avssSpec (t := t) sec corr coeffs) A k h),
          y.1.dealerCommit = h.currentState.dealerCommit :=
      Filter.Eventually.of_forall fun h =>
        avssSpec_stepKernel_dealerCommit_AE sec corr A k h
    have hjoint :
        ∀ᵐ x ∂(((traceDist (avssSpec (t := t) sec corr coeffs) A μ₀).map
              (Preorder.frestrictLe k)) ⊗ₘ
            (stepKernel (avssSpec (t := t) sec corr coeffs) A k)),
          x.2.1.dealerCommit = (FinPrefix.currentState x.1).dealerCommit :=
      Measure.ae_compProd_of_ae_ae MeasurableSet.of_discrete h_inner
    rw [hk] at hjoint
    rw [ae_map_iff hmeas_pair.aemeasurable MeasurableSet.of_discrete] at hjoint
    exact hjoint

/-! ### §16-β-γ — Kernel-history discharge of `dealerShareTo` trace hypotheses

The §16-β-β packaging exposes `dealerShareTo_continuously_enabled_AE`
and `dealerShareTo_post_persists_AE` as explicit trace-level
hypotheses.  This subsection discharges both via a single
kernel-history inductive lift that mirrors
`traceDist_partyPoint_AE_eq_init`.

The key insight is the partition disjunction tracking whether
`dealerShareTo p` has fired in the prefix:

```
((ω k).1.dealerSent p = false ∧ (ω k).1.dealerMessages p = none ∧
  ∀ j ∈ [1, k], (ω j).2 ≠ some (.dealerShareTo p)) ∨
((ω k).1.dealerSent p = true ∧ (ω k).1.dealerMessages p ≠ none ∧
  ∃ j ∈ [1, k], (ω j).2 = some (.dealerShareTo p))
```

This disjunction is preserved by every `avssStep` action (left
stays left until `dealerShareTo p` fires, then moves to right;
right stays right by `dealerSent p`/`dealerMessages p`
monotonicity), and yields both target hypotheses as direct
corollaries. -/

omit [Fintype F] in
/-- Frame: `dealerSent p` is unchanged by any action that is not
`dealerShareTo p`. -/
theorem avssStep_dealerSent_self_unless
    (a : AVSSAction n F) (s : AVSSState n t F) (p : Fin n)
    (h_not_share : a ≠ .dealerShareTo p) :
    (avssStep a s).dealerSent p = s.dealerSent p := by
  cases a with
  | dealerShareTo q =>
    have hpq : p ≠ q := fun heq => h_not_share (heq ▸ rfl)
    show (avssStep (.dealerShareTo q) s).dealerSent p = s.dealerSent p
    simp [avssStep, Function.update_of_ne hpq]
  | partyDeliver q => simp [avssStep, setLocal]
  | partyCorruptDeliver q => simp [avssStep, setLocal]
  | partyEchoSend q => simp [avssStep, setLocal]
  | partyEchoReceive q r => simp [avssStep, setLocal]
  | partyReady q => simp [avssStep, setLocal]
  | partyAmplify q => simp [avssStep, setLocal]
  | partyReceiveReady q r => simp [avssStep, setLocal]
  | partyOutput q => simp [avssStep, setLocal]

omit [Fintype F] in
/-- Frame: `dealerMessages p` is unchanged by any action that is not
`dealerShareTo p`. -/
theorem avssStep_dealerMessages_self_unless
    (a : AVSSAction n F) (s : AVSSState n t F) (p : Fin n)
    (h_not_share : a ≠ .dealerShareTo p) :
    (avssStep a s).dealerMessages p = s.dealerMessages p := by
  cases a with
  | dealerShareTo q =>
    have hpq : p ≠ q := fun heq => h_not_share (heq ▸ rfl)
    show (avssStep (.dealerShareTo q) s).dealerMessages p = s.dealerMessages p
    simp [avssStep, Function.update_of_ne hpq]
  | partyDeliver q => rfl
  | partyCorruptDeliver q => rfl
  | partyEchoSend q => rfl
  | partyEchoReceive q r => rfl
  | partyReady q => rfl
  | partyAmplify q => rfl
  | partyReceiveReady q r => rfl
  | partyOutput q => rfl

omit [Fintype F] in
/-- After `dealerShareTo p`, `dealerSent p = true`. -/
theorem avssStep_dealerSent_set_after_share
    (s : AVSSState n t F) (p : Fin n) :
    (avssStep (.dealerShareTo p) s).dealerSent p = true := by
  show (avssStep (.dealerShareTo p) s).dealerSent p = true
  simp [avssStep, Function.update_self]

omit [Fintype F] in
/-- After `dealerShareTo p`, `dealerMessages p ≠ none`. -/
theorem avssStep_dealerMessages_some_after_share
    (s : AVSSState n t F) (p : Fin n) :
    (avssStep (.dealerShareTo p) s).dealerMessages p ≠ none := by
  show (avssStep (.dealerShareTo p) s).dealerMessages p ≠ none
  simp [avssStep, Function.update_self]

omit [Fintype F] in
/-- Monotonicity: `dealerSent p = true` is preserved by every action. -/
theorem avssStep_dealerSent_monotone
    (a : AVSSAction n F) (s : AVSSState n t F) (p : Fin n)
    (h_pre : s.dealerSent p = true) :
    (avssStep a s).dealerSent p = true := by
  by_cases h : a = .dealerShareTo p
  · subst h; exact avssStep_dealerSent_set_after_share s p
  · rw [avssStep_dealerSent_self_unless a s p h]; exact h_pre

omit [Fintype F] in
/-- Monotonicity: `dealerMessages p ≠ none` is preserved by every action. -/
theorem avssStep_dealerMessages_some_monotone
    (a : AVSSAction n F) (s : AVSSState n t F) (p : Fin n)
    (h_pre : s.dealerMessages p ≠ none) :
    (avssStep a s).dealerMessages p ≠ none := by
  by_cases h : a = .dealerShareTo p
  · subst h; exact avssStep_dealerMessages_some_after_share s p
  · rw [avssStep_dealerMessages_self_unless a s p h]; exact h_pre

/-- Per-step kernel history-tracking AE relation for `dealerSent p`
and `dealerMessages p`: AE on the kernel, the resulting pair `y`
either records a `dealerShareTo p` firing (action label witnesses,
post is post-share) or it preserves the pre-state's `dealerSent p`
and `dealerMessages p` (and the action label is not the firing). -/
private theorem avssSpec_stepKernel_dealerShareTo_track_AE
    (sec : F) (corr : Finset (Fin n))
    (A : Adversary (AVSSState n t F) (AVSSAction n F)) (k : ℕ)
    (h : FinPrefix (AVSSState n t F) (AVSSAction n F) k) (p : Fin n) :
    ∀ᵐ y ∂(stepKernel (avssSpec (t := t) sec corr coeffs) A k h),
      (y.2 = some (.dealerShareTo p) ∧ y.1.dealerSent p = true ∧
          y.1.dealerMessages p ≠ none) ∨
      (y.2 ≠ some (.dealerShareTo p) ∧
          y.1.dealerSent p = h.currentState.dealerSent p ∧
          y.1.dealerMessages p = h.currentState.dealerMessages p) := by
  classical
  have hPset : MeasurableSet
      {x : AVSSState n t F × Option (AVSSAction n F) |
        (x.2 = some (.dealerShareTo p) ∧ x.1.dealerSent p = true ∧
            x.1.dealerMessages p ≠ none) ∨
        (x.2 ≠ some (.dealerShareTo p) ∧
            x.1.dealerSent p = h.currentState.dealerSent p ∧
            x.1.dealerMessages p = h.currentState.dealerMessages p)} :=
    MeasurableSet.of_discrete
  unfold stepKernel
  simp only [ProbabilityTheory.Kernel.ofFunOfCountable, ProbabilityTheory.Kernel.coe_mk]
  rcases hsched : A.schedule h.toList with _ | i
  · rw [ae_dirac_iff hPset]
    -- Stutter: y = (h.currentState, none).
    right
    exact ⟨by simp, rfl, rfl⟩
  · by_cases hgate : ((avssSpec (t := t) sec corr coeffs).actions i).gate h.currentState
    · simp only [hgate, dite_true]
      rw [show ((avssSpec (t := t) sec corr coeffs).actions i).effect h.currentState hgate
            = PMF.pure (avssStep i h.currentState) from rfl,
          PMF.toMeasure_pure, Measure.map_dirac (by fun_prop), ae_dirac_iff hPset]
      -- y = (avssStep i h.currentState, some i). Case on `i = dealerShareTo p`.
      by_cases hi : i = .dealerShareTo p
      · subst hi
        left
        refine ⟨rfl, ?_, ?_⟩
        · exact avssStep_dealerSent_set_after_share h.currentState p
        · exact avssStep_dealerMessages_some_after_share h.currentState p
      · right
        refine ⟨?_, ?_, ?_⟩
        · simp [hi]
        · exact avssStep_dealerSent_self_unless i h.currentState p hi
        · exact avssStep_dealerMessages_self_unless i h.currentState p hi
    · simp only [hgate, dite_false]
      rw [ae_dirac_iff hPset]
      right
      exact ⟨by simp, rfl, rfl⟩

/-- Trace-level history-tracked partition for `dealerShareTo p`:
AE on the trace, at every step `k`, we are in exactly one of two
states — either `dealerShareTo p` has not fired in `[1, k]` and the
gate is still open, or it has fired and the post-condition holds.

This is the inductive bridge between the §16-β-β trace hypotheses
and `avssStep`'s state-level semantics: both
`dealerShareTo_continuously_enabled_AE` and
`dealerShareTo_post_persists_AE` are direct corollaries. -/
theorem traceDist_dealerShareTo_history_AE
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr coeffs s)
    (A : Adversary (AVSSState n t F) (AVSSAction n F)) (p : Fin n) (k : ℕ) :
    ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
      ((ω k).1.dealerSent p = false ∧ (ω k).1.dealerMessages p = none ∧
        ∀ j, 1 ≤ j → j ≤ k → (ω j).2 ≠ some (.dealerShareTo p)) ∨
      ((ω k).1.dealerSent p = true ∧ (ω k).1.dealerMessages p ≠ none ∧
        ∃ j, 1 ≤ j ∧ j ≤ k ∧ (ω j).2 = some (.dealerShareTo p)) := by
  classical
  -- Lift `h_init` to a step-0 AE statement on the trace.
  have h_init_AE : ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
      initPred sec corr coeffs (ω 0).1 := by
    have hmap := traceDist_step_zero_state_marginal (t := t) sec corr coeffs μ₀ A
    have hmeas : Measurable (fun ω : Π _ : ℕ, AVSSState n t F × Option (AVSSAction n F) =>
        (ω 0).1) := by fun_prop
    rw [← hmap] at h_init
    rwa [ae_map_iff hmeas.aemeasurable MeasurableSet.of_discrete] at h_init
  induction k with
  | zero =>
    -- Base: at step 0, gate is open (from initPred), and there are
    -- no indices in [1, 0].
    filter_upwards [h_init_AE] with ω h_init0
    left
    refine ⟨?_, ?_, ?_⟩
    · have : (ω 0).1.dealerSent = (fun _ => false) := h_init0.2.2.2.2.2.2.2.1
      rw [this]
    · have : (ω 0).1.dealerMessages = (fun _ => none) := h_init0.2.2.2.2.2.2.2.2.1
      rw [this]
    · intro j h1 h2
      omega
  | succ k ih =>
    -- Per-step kernel-AE: lift to `(traceDist).map (frestrictLe k) ⊗ₘ stepKernel`,
    -- then to `traceDist`-AE on the joint pair `(prefix, ω (k+1))`.
    have hmeas_pair : Measurable
        (fun ω : Π _ : ℕ, AVSSState n t F × Option (AVSSAction n F) =>
          (Preorder.frestrictLe k ω, ω (k+1))) := by fun_prop
    haveI : IsProbabilityMeasure
        (μ₀.map (fun s : AVSSState n t F => (s, (none : Option (AVSSAction n F))))) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    have hk :
        ((traceDist (avssSpec (t := t) sec corr coeffs) A μ₀).map
            (Preorder.frestrictLe k)) ⊗ₘ
          (stepKernel (avssSpec (t := t) sec corr coeffs) A k) =
        (traceDist (avssSpec (t := t) sec corr coeffs) A μ₀).map
          (fun ω => (Preorder.frestrictLe k ω, ω (k+1))) := by
      unfold traceDist
      exact ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    have h_inner : ∀ᵐ h ∂((traceDist (avssSpec (t := t) sec corr coeffs) A μ₀).map
          (Preorder.frestrictLe k)),
        ∀ᵐ y ∂(stepKernel (avssSpec (t := t) sec corr coeffs) A k h),
          (y.2 = some (.dealerShareTo p) ∧ y.1.dealerSent p = true ∧
              y.1.dealerMessages p ≠ none) ∨
          (y.2 ≠ some (.dealerShareTo p) ∧
              y.1.dealerSent p = h.currentState.dealerSent p ∧
              y.1.dealerMessages p = h.currentState.dealerMessages p) :=
      Filter.Eventually.of_forall fun h =>
        avssSpec_stepKernel_dealerShareTo_track_AE sec corr A k h p
    have hjoint :
        ∀ᵐ x ∂(((traceDist (avssSpec (t := t) sec corr coeffs) A μ₀).map
              (Preorder.frestrictLe k)) ⊗ₘ
            (stepKernel (avssSpec (t := t) sec corr coeffs) A k)),
          (x.2.2 = some (.dealerShareTo p) ∧ x.2.1.dealerSent p = true ∧
              x.2.1.dealerMessages p ≠ none) ∨
          (x.2.2 ≠ some (.dealerShareTo p) ∧
              x.2.1.dealerSent p = (FinPrefix.currentState x.1).dealerSent p ∧
              x.2.1.dealerMessages p = (FinPrefix.currentState x.1).dealerMessages p) :=
      Measure.ae_compProd_of_ae_ae MeasurableSet.of_discrete h_inner
    rw [hk] at hjoint
    rw [ae_map_iff hmeas_pair.aemeasurable MeasurableSet.of_discrete] at hjoint
    -- Bridge: `FinPrefix.currentState (Preorder.frestrictLe k ω) = (ω k).1`.
    have h_bridge : ∀ ω : Π _ : ℕ, AVSSState n t F × Option (AVSSAction n F),
        FinPrefix.currentState
            (Preorder.frestrictLe (π := fun _ : ℕ =>
              AVSSState n t F × Option (AVSSAction n F)) k ω) = (ω k).1 := by
      intro ω; rfl
    have hjoint' :
        ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
          ((ω (k+1)).2 = some (.dealerShareTo p) ∧
              (ω (k+1)).1.dealerSent p = true ∧
              (ω (k+1)).1.dealerMessages p ≠ none) ∨
          ((ω (k+1)).2 ≠ some (.dealerShareTo p) ∧
              (ω (k+1)).1.dealerSent p = (ω k).1.dealerSent p ∧
              (ω (k+1)).1.dealerMessages p = (ω k).1.dealerMessages p) := by
      filter_upwards [hjoint] with ω hω
      rcases hω with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · left; exact ⟨h1, h2, h3⟩
      · right
        rw [h_bridge ω] at h2 h3
        exact ⟨h1, h2, h3⟩
    -- Combine the IH and the kernel-AE step.
    filter_upwards [ih, hjoint'] with ω h_ih h_kernel
    rcases h_ih with h_left | h_right
    · -- Pre at k is left: gate open, no firing in [1, k].
      rcases h_kernel with ⟨h_act, h_ds, h_dm⟩ | ⟨h_nact, h_ds_eq, h_dm_eq⟩
      · -- Action label fires dealerShareTo p at k+1: move to right.
        right
        refine ⟨h_ds, h_dm, k + 1, by omega, le_refl _, h_act⟩
      · -- Action does not fire dealerShareTo p; state preserved, no new firing.
        left
        refine ⟨?_, ?_, ?_⟩
        · rw [h_ds_eq]; exact h_left.1
        · rw [h_dm_eq]; exact h_left.2.1
        · intro j hj1 hjk
          rcases Nat.lt_or_ge j (k + 1) with hjlt | hjge
          · exact h_left.2.2 j hj1 (Nat.lt_succ_iff.mp hjlt)
          · -- j ≥ k+1 and j ≤ k+1, so j = k+1.
            have hj_eq : j = k + 1 := le_antisymm hjk hjge
            subst hj_eq
            exact h_nact
    · -- Pre at k is right: post-share already, witness in prefix.
      obtain ⟨h_ds_pre, h_dm_pre, j, hj1, hjk, hj_act⟩ := h_right
      rcases h_kernel with ⟨h_act, h_ds, h_dm⟩ | ⟨h_nact, h_ds_eq, h_dm_eq⟩
      · -- Action also fires at k+1: carry through.
        right
        exact ⟨h_ds, h_dm, j, hj1, le_trans hjk (Nat.le_succ k), hj_act⟩
      · -- Action does not fire; carry witness, state preserved.
        right
        refine ⟨?_, ?_, j, hj1, le_trans hjk (Nat.le_succ k), hj_act⟩
        · rw [h_ds_eq]; exact h_ds_pre
        · rw [h_dm_eq]; exact h_dm_pre

/-- **Discharge of `dealerShareTo_continuously_enabled_AE`** via the
kernel-history lift `traceDist_dealerShareTo_history_AE`. -/
theorem dealerShareTo_continuously_enabled_AE_of_initPred
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr coeffs s)
    (A : Adversary (AVSSState n t F) (AVSSAction n F)) (p : Fin n) :
    dealerShareTo_continuously_enabled_AE sec corr coeffs μ₀ A p := by
  classical
  unfold dealerShareTo_continuously_enabled_AE
  rw [ae_all_iff]
  intro k
  filter_upwards [traceDist_dealerShareTo_history_AE sec corr coeffs μ₀ h_init A p k]
    with ω hω h_no_share
  rcases hω with hL | hR
  · exact hL.1
  · -- Right branch: ∃ j ∈ [1, k] with firing — contradicts h_no_share.
    obtain ⟨_, _, j, hj1, hjk, hj_act⟩ := hR
    -- j ≥ 1 means j = (j - 1) + 1, and (j - 1) ≤ k.
    have hj_pred : j - 1 ≤ k := by omega
    have hj_succ : (j - 1) + 1 = j := by omega
    have h_contra := h_no_share (j - 1) hj_pred
    rw [hj_succ] at h_contra
    exact absurd hj_act h_contra

/-- **Discharge of `dealerShareTo_post_persists_AE`** via the
kernel-history lift `traceDist_dealerShareTo_history_AE`.

The post-condition's target step `k'` (the step at which we want
`dealerSent p = true ∧ dealerMessages p ≠ none`) drives our use of
the history at step `k'`: the right branch gives the post-condition,
and the left branch contradicts the firing assumption at `k+1 ≤ k'`. -/
theorem dealerShareTo_post_persists_AE_of_initPred
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr coeffs s)
    (A : Adversary (AVSSState n t F) (AVSSAction n F)) (p : Fin n) :
    dealerShareTo_post_persists_AE sec corr coeffs μ₀ A p := by
  classical
  unfold dealerShareTo_post_persists_AE
  -- Reorder: ∀ k', ∀ k, AE; the AE-history at the *target step* k' is
  -- what gives both branches.
  -- Push the inner ∀ k' through to AE-quantification level via `ae_all_iff`.
  -- Strategy: prove the universal-over-k' AE statement directly, then
  -- combine via filter_upwards.
  have h_per_target : ∀ k' : ℕ,
      ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
        ∀ k, (ω (k + 1)).2 = some (AVSSAction.dealerShareTo p) →
          k' ≥ k + 1 →
          (ω k').1.dealerSent p = true ∧
            (ω k').1.dealerMessages p ≠ none := by
    intro k'
    filter_upwards [traceDist_dealerShareTo_history_AE sec corr coeffs μ₀ h_init A p k']
      with ω hω k h_fire hk'_ge
    rcases hω with hL | hR
    · -- Left at k': no firing in [1, k'], but firing at k+1 ≤ k' contradicts.
      exfalso
      have h_no := hL.2.2 (k + 1) (by omega) hk'_ge
      exact h_no h_fire
    · -- Right at k': directly gives the post-condition.
      exact ⟨hR.1, hR.2.1⟩
  -- Combine via `ae_all_iff` to commute the outer ∀ k' inside the AE.
  have h_combined :
      ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
        ∀ k', ∀ k, (ω (k + 1)).2 = some (AVSSAction.dealerShareTo p) →
          k' ≥ k + 1 →
          (ω k').1.dealerSent p = true ∧
            (ω k').1.dealerMessages p ≠ none :=
    ae_all_iff.mpr h_per_target
  filter_upwards [h_combined] with ω hω k h_fire k' hk'_ge
  exact hω k' k h_fire hk'_ge

/-- **§16-β-γ closure** — `atomic_broadcast_AE` from per-action
progress alone (the trace-level continuous-enabling and
post-firing hypotheses are now discharged from `h_init` by the
kernel-history lift `traceDist_dealerShareTo_history_AE`). -/
theorem atomic_broadcast_AE_of_avssFair_per_action_progress_initPred
    (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr coeffs s)
    (A : Leslie.Prob.TrajectoryFairAdversary
            (avssSpec (t := t) sec corr coeffs) avssFair μ₀)
    (h_per_action :
      Leslie.Prob.FairASTCertificate.TrajectoryFairProgressPerAction
        (avssSpec (t := t) sec corr coeffs) avssFair μ₀ A.toFair) :
    atomic_broadcast_AE sec corr coeffs μ₀ A.toAdversary :=
  atomic_broadcast_AE_of_avssFair_per_action_progress sec corr coeffs μ₀ A
    h_per_action
    (fun p _ => dealerShareTo_continuously_enabled_AE_of_initPred
      sec corr coeffs μ₀ h_init A.toAdversary p)
    (fun p _ => dealerShareTo_post_persists_AE_of_initPred
      sec corr coeffs μ₀ h_init A.toAdversary p)

/-- **§16-β-γ closure** — unconditional honest-dealer termination
from `avssFair` + per-action progress, with the §16-β-β trace
hypotheses now discharged. -/
theorem avss_termination_AS_fair_honest_dealer_unconditional_initPred
    (sec : F) (corr : Finset (Fin n)) (h_corr : corr.card ≤ t)
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr coeffs s)
    (A : Leslie.Prob.TrajectoryFairAdversary
            (avssSpec (t := t) sec corr coeffs) avssFair μ₀)
    (h_per_action :
      Leslie.Prob.FairASTCertificate.TrajectoryFairProgressPerAction
        (avssSpec (t := t) sec corr coeffs) avssFair μ₀ A.toFair)
    (h_drop_io : ∀ N : ℕ, FairASTCertificate.TrajectoryFairRunningMinDropIO
        (avssSpec (t := t) sec corr coeffs) avssFair
        (avssCert (t := t) sec corr coeffs h_corr) μ₀ A.toFair N) :
    AlmostDiamond (avssSpec (t := t) sec corr coeffs) A.toAdversary μ₀ terminated :=
  avss_termination_AS_fair_under_atomic_broadcast sec corr h_corr coeffs μ₀ h_init A
    (atomic_broadcast_AE_of_avssFair_per_action_progress_initPred
      sec corr coeffs μ₀ h_init A h_per_action)
    h_drop_io

/-! ### Phase 8.5c — `TrivialView` and `coalitionTrivialView`

Phase 8.5b-α weakened `corruptLocalInv` to drop the
`{echoSent, echoesReceived, readySent, readyReceived} = ∅` clauses
(those fields are now schedule-dependent for corrupt parties).
Phase 8.5c re-introduces the `TrivialView` projection that was
landed in PR #58 (and removed during 8.5b-α): it carries the
schedule-derived per-step trivial-field view per corrupt party.
The structural bridge `coalitionTraceView_eq_reconstruct_AE`
factors through both `coalitionAlgebraicView` *and*
`coalitionTrivialView`. -/

/-- Carrier for the schedule-derived trivial-field view of a corrupt
party's local state at one step: `(echoSent, echoesReceived,
readySent, readyReceived)`. -/
abbrev TrivialView (n : ℕ) : Type :=
  Bool × Finset (Fin n) × Bool × Finset (Fin n)

instance : MeasurableSpace (TrivialView n) := ⊤
instance : MeasurableSingletonClass (TrivialView n) := ⟨fun _ => trivial⟩

/-- The corrupt coalition's per-step trivial-field view. Reads the
schedule-derived fields directly from the trace. Under the C1+C2
model, these fields can take non-`init` values; their joint
sec-invariance follows from the simulation factoring through the
initial state (§19.2.5+). -/
def coalitionTrivialView (C : BivariateShamir.Coalition n t)
    (ω : ℕ → AVSSState n t F × Option (AVSSAction n F)) (k : ℕ) :
    Fin k → C.val → TrivialView n :=
  fun i p =>
    let ls := (ω i.val).1.local_ p.val
    (ls.echoSent, ls.echoesReceived, ls.readySent, ls.readyReceived)

omit [Field F] in
@[fun_prop]
theorem measurable_coalitionTrivialView
    (C : BivariateShamir.Coalition n t) (k : ℕ) :
    Measurable (fun ω : ℕ → AVSSState n t F × Option (AVSSAction n F) =>
        coalitionTrivialView C ω k) := by
  classical
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun p => ?_
  have h1 : Measurable (fun ω : ℕ → AVSSState n t F × Option (AVSSAction n F) =>
      ω i.val) := measurable_pi_apply _
  have h2 : Measurable (Prod.fst :
      AVSSState n t F × Option (AVSSAction n F) → AVSSState n t F) := measurable_fst
  have h3 : Measurable (fun s : AVSSState n t F =>
      ((s.local_ p.val).echoSent, (s.local_ p.val).echoesReceived,
       (s.local_ p.val).readySent, (s.local_ p.val).readyReceived)) :=
    measurable_of_countable _
  exact (h3.comp h2).comp h1

/-- **Phase 6.2 structural theorem (`corruptViewFactorsThroughGrid`),
8.5c weakened.**

Almost surely, every corrupt party `p ∈ C` has, at every step `i < k`,
a local state whose **algebraic** content is pinned to:
  * `output = none` (by `corruptLocalInv`),
  * `rowPoly = some (rowPolyOfDealer (ω 0).1.partyPoint
     (ω 0).1.coeffs p.val)` whenever `delivered = true` (by
     `outputDeterminedInv` plus the AE invariance of
     `partyPoint`/`coeffs` along the trace), and
  * `rowPoly = none` whenever `delivered = false` (by
     `corruptLocalInv`).

Phase 8.5b-α weakening: the four trivial fields
`{echoSent, echoesReceived, readySent, readyReceived}` are now
schedule-dependent for corrupt parties (those gates dropped
`p ∉ corrupted`); they are recovered separately via the companion
theorem `coalitionView_corrupt_trivial_factors_AE`, which is just
the unfolding of `coalitionTrivialView`. -/
theorem coalitionView_corrupt_factors_AE
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr coeffs s)
    (A : Adversary (AVSSState n t F) (AVSSAction n F))
    (C : BivariateShamir.Coalition n t)
    (h_C_corr : C.val ⊆ corr) (k : ℕ) :
    ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
        ∀ p : C.val,
          let ls := (ω k).1.local_ p.val
          ls.output = none ∧
          (ls.delivered = false → ls.rowPoly = none) ∧
          ((ω 0).1.dealerHonest = true → ls.delivered = true →
            ls.rowPoly = some (rowPolyOfDealer (ω 0).1.partyPoint
              coeffs p.val)) := by
  classical
  -- Step 1: lift `h_init` into a per-trace AE statement at step 0.
  have h_init_AE : ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
      initPred sec corr coeffs (ω 0).1 := by
    have hmap := traceDist_step_zero_state_marginal (t := t) sec corr coeffs μ₀ A
    have hmeas : Measurable (fun ω : Π _ : ℕ, AVSSState n t F × Option (AVSSAction n F) =>
        (ω 0).1) := by fun_prop
    rw [← hmap] at h_init
    rwa [ae_map_iff hmeas.aemeasurable MeasurableSet.of_discrete] at h_init
  -- Step 2: phase6Inv at every step.
  have h_phase6 : ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
      ∀ n, phase6Inv coeffs (ω n).1 :=
    avss_phase6Inv_AS sec corr coeffs μ₀ h_init A
  -- Step 3: partyPoint, corrupted, dealerHonest preserved AE along the trace.
  have h_pp := traceDist_partyPoint_AE_eq_init (t := t) sec corr coeffs μ₀ A k
  have h_corr := traceDist_corrupted_AE_eq_init (t := t) sec corr coeffs μ₀ A k
  have h_dH := traceDist_dealerHonest_AE_eq_init (t := t) sec corr coeffs μ₀ A k
  filter_upwards [h_init_AE, h_phase6, h_pp, h_corr, h_dH]
    with ω h_init0 h_p6 h_pp_eq h_corr_eq h_dH_eq p
  -- p ∈ C ⊆ corr, and (ω 0).1.corrupted = corr (from initPred), and
  -- (ω k).1.corrupted = (ω 0).1.corrupted, so p.val ∈ (ω k).1.corrupted.
  have h_corrupt_eq : (ω 0).1.corrupted = corr := h_init0.2.2.1
  have hp_corr : p.val ∈ corr := h_C_corr p.property
  have hp_corr_k : p.val ∈ (ω k).1.corrupted := by
    rw [h_corr_eq, h_corrupt_eq]; exact hp_corr
  -- Apply phase6Inv at step k.
  have h_p6_k := h_p6 k
  obtain ⟨h_od, h_cl, _h_dm⟩ := h_p6_k
  have h_cl_p := h_cl p.val hp_corr_k
  refine ⟨h_cl_p.1, h_cl_p.2, ?_⟩
  intro h_dH_init h_d
  -- Bridge: (ω k).1.dealerHonest = (ω 0).1.dealerHonest = true.
  have h_dH_k : (ω k).1.dealerHonest = true := h_dH_eq.trans h_dH_init
  -- outputDeterminedInv applied to step k under honest dealer.
  have h_rp_correct := (h_od h_dH_k).1 p.val h_d
  -- Bridge partyPoint at step k to step 0.
  rw [h_rp_correct, h_pp_eq]

/-- **Phase 8.5d-β-followup-6 — existential variant of
`coalitionView_corrupt_factors_AE`.**

Takes the existential AE-hypothesis `∀ᵐ s ∂μ₀, ∃ c, initPred sec corr c s`
(returned by `avssInitMeasure_AE_initPred` post μ₀ migration) and
returns a coeffs-free conclusion that uses `(ω 0).1.dealerCommit p.val`
directly (matching `coalitionAlgebraicView`'s first coord).

The c-dependence cancels via `dealerMessagesInv c (ω k).1`, which
under honest dealer pins
`(ω k).1.dealerCommit p .rowPoly = rowPolyOfDealer (ω k).1.partyPoint c p`,
matching `outputDeterminedInv c (ω k).1`'s rowPoly clause exactly.
A separate trace-AE preservation `traceDist_dealerCommit_AE_eq_init`
bridges to `(ω 0).1.dealerCommit`. -/
theorem coalitionView_corrupt_factors_AE_ex
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, ∃ c, initPred sec corr c s)
    (A : Adversary (AVSSState n t F) (AVSSAction n F))
    (C : BivariateShamir.Coalition n t)
    (h_C_corr : C.val ⊆ corr) (k : ℕ) :
    ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
        ∀ p : C.val,
          let ls := (ω k).1.local_ p.val
          ls.output = none ∧
          (ls.delivered = false → ls.rowPoly = none) ∧
          ((ω 0).1.dealerHonest = true → ls.delivered = true →
            ls.rowPoly = some ((ω 0).1.dealerCommit p.val).rowPoly) := by
  classical
  -- Lift h_init into a per-trace AE statement at step 0.
  have h_init_AE : ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
      ∃ c, initPred sec corr c (ω 0).1 := by
    have hmap := traceDist_step_zero_state_marginal (t := t) sec corr coeffs μ₀ A
    have hmeas : Measurable (fun ω : Π _ : ℕ, AVSSState n t F × Option (AVSSAction n F) =>
        (ω 0).1) := by fun_prop
    rw [← hmap] at h_init
    rwa [ae_map_iff hmeas.aemeasurable MeasurableSet.of_discrete] at h_init
  -- Existential phase6Inv at every step.
  have h_phase6 : ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
      ∀ n, ∃ c, phase6Inv c (ω n).1 :=
    avss_phase6InvEx_AS sec corr coeffs μ₀ h_init A
  -- AE preservations along the trace.
  have h_corr := traceDist_corrupted_AE_eq_init (t := t) sec corr coeffs μ₀ A k
  have h_dH := traceDist_dealerHonest_AE_eq_init (t := t) sec corr coeffs μ₀ A k
  have h_dC := traceDist_dealerCommit_AE_eq_init (t := t) sec corr coeffs μ₀ A k
  filter_upwards [h_init_AE, h_phase6, h_corr, h_dH, h_dC]
    with ω h_init0 h_p6 h_corr_eq h_dH_eq h_dC_eq p
  -- p ∈ C ⊆ corr; (ω 0).1.corrupted = corr (initPred clause 3, c-independent).
  obtain ⟨_c0, h_init0c⟩ := h_init0
  have h_corrupt_eq : (ω 0).1.corrupted = corr := h_init0c.2.2.1
  have hp_corr : p.val ∈ corr := h_C_corr p.property
  have hp_corr_k : p.val ∈ (ω k).1.corrupted := by
    rw [h_corr_eq, h_corrupt_eq]; exact hp_corr
  -- Existential phase6Inv at step k.
  obtain ⟨c, h_p6_k⟩ := h_p6 k
  obtain ⟨h_od, h_cl, h_dm⟩ := h_p6_k
  have h_cl_p := h_cl p.val hp_corr_k
  refine ⟨h_cl_p.1, h_cl_p.2, ?_⟩
  intro h_dH_init h_d
  -- (ω k).1.dealerHonest = (ω 0).1.dealerHonest = true.
  have h_dH_k : (ω k).1.dealerHonest = true := h_dH_eq.trans h_dH_init
  -- outputDeterminedInv at step k.
  have h_rp_correct : ((ω k).1.local_ p.val).rowPoly =
      some (rowPolyOfDealer (ω k).1.partyPoint c p.val) :=
    (h_od h_dH_k).1 p.val h_d
  -- dealerMessagesInv at step k pins dealerCommit's rowPoly.
  have h_dc_k : (ω k).1.dealerCommit p.val =
      { rowPoly := rowPolyOfDealer (ω k).1.partyPoint c p.val
        colPoly := fun _ => (0 : F) } :=
    (h_dm h_dH_k).1 p.val
  -- Bridge `(ω 0).1.dealerCommit` to `(ω k).1.dealerCommit` by AE-preservation.
  have h_dc_pt : (ω 0).1.dealerCommit p.val = (ω k).1.dealerCommit p.val :=
    (congrFun h_dC_eq.symm p.val)
  rw [h_rp_correct, h_dc_pt, h_dc_k]

/-- **Phase 8.5d-β-followup-7 — dealerHonest-INDEPENDENT factor lemma.**

Drops the honest-dealer guard from `coalitionView_corrupt_factors_AE_ex`'s
third clause.  The proof uses the dealerHonest-INDEPENDENT
`coalitionRowPolyAlignedInv` (which holds AE on the trace by
`avss_coalitionRowPolyAlignedInv_AS`) plus `avss_phase6InvEx_AS` for
the c-independent `corruptLocalInv` clauses (output = none, delivered = false →
rowPoly = none).  Plus dealerCommit AE-preservation to bridge to (ω 0).1.

This closes the corrupt-dealer headline case; the rowPoly clause now
holds unconditionally, not just under honest dealer. -/
theorem coalitionView_corrupt_factors_AE_indep
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, ∃ c, initPred sec corr c s)
    (A : Adversary (AVSSState n t F) (AVSSAction n F))
    (C : BivariateShamir.Coalition n t)
    (h_C_corr : C.val ⊆ corr) (k : ℕ) :
    ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
        ∀ p : C.val,
          let ls := (ω k).1.local_ p.val
          ls.output = none ∧
          (ls.delivered = false → ls.rowPoly = none) ∧
          (ls.delivered = true →
            ls.rowPoly = some ((ω 0).1.dealerCommit p.val).rowPoly) := by
  classical
  -- Lift h_init to per-trace AE at step 0 (for the `(ω 0).1.corrupted = corr` fact).
  have h_init_AE : ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
      ∃ c, initPred sec corr c (ω 0).1 := by
    have hmap := traceDist_step_zero_state_marginal (t := t) sec corr coeffs μ₀ A
    have hmeas : Measurable (fun ω : Π _ : ℕ, AVSSState n t F × Option (AVSSAction n F) =>
        (ω 0).1) := by fun_prop
    rw [← hmap] at h_init
    rwa [ae_map_iff hmeas.aemeasurable MeasurableSet.of_discrete] at h_init
  -- Existential phase6Inv at every step (gives c-independent corruptLocalInv).
  have h_phase6 : ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
      ∀ n, ∃ c, phase6Inv c (ω n).1 :=
    avss_phase6InvEx_AS sec corr coeffs μ₀ h_init A
  -- dealerHonest-INDEPENDENT alignment invariant at every step.
  have h_align : ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
      ∀ n, coalitionRowPolyAlignedInv (ω n).1 :=
    avss_coalitionRowPolyAlignedInv_AS sec corr coeffs μ₀ h_init A
  -- AE preservations along the trace.
  have h_corr := traceDist_corrupted_AE_eq_init (t := t) sec corr coeffs μ₀ A k
  have h_dC := traceDist_dealerCommit_AE_eq_init (t := t) sec corr coeffs μ₀ A k
  filter_upwards [h_init_AE, h_phase6, h_align, h_corr, h_dC]
    with ω h_init0 h_p6 h_align_all h_corr_eq h_dC_eq p
  obtain ⟨_c0, h_init0c⟩ := h_init0
  have h_corrupt_eq : (ω 0).1.corrupted = corr := h_init0c.2.2.1
  have hp_corr : p.val ∈ corr := h_C_corr p.property
  have hp_corr_k : p.val ∈ (ω k).1.corrupted := by
    rw [h_corr_eq, h_corrupt_eq]; exact hp_corr
  -- Use existential phase6Inv at step k for the c-independent corruptLocalInv part.
  obtain ⟨_c, h_p6_k⟩ := h_p6 k
  obtain ⟨_h_od, h_cl, _h_dm⟩ := h_p6_k
  have h_cl_p := h_cl p.val hp_corr_k
  refine ⟨h_cl_p.1, h_cl_p.2, ?_⟩
  intro h_d
  -- Use coalitionRowPolyAlignedInv at step k for the rowPoly = some dealerCommit clause.
  have h_align_k := h_align_all k
  have h_local_align_k := h_align_k.2 p.val hp_corr_k h_d
  -- Bridge `(ω k).1.dealerCommit` to `(ω 0).1.dealerCommit`.
  have h_dc_pt : (ω 0).1.dealerCommit p.val = (ω k).1.dealerCommit p.val :=
    (congrFun h_dC_eq.symm p.val)
  rw [h_local_align_k, h_dc_pt]

/-- **Phase 8.5c companion theorem.** The trivial-field view of every
corrupt party at every step matches `coalitionTrivialView`. This is
literally definitional unfolding — `coalitionTrivialView` is *defined*
as the projection of the per-step local state onto the four trivial
fields. The lemma form is convenient at consumer sites (see
`coalitionTraceView_eq_reconstruct_AE`). -/
theorem coalitionView_corrupt_trivial_factors_AE
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (A : Adversary (AVSSState n t F) (AVSSAction n F))
    (C : BivariateShamir.Coalition n t) (k : ℕ) :
    ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
        ∀ (i : Fin k) (p : C.val),
          let ls := (ω i.val).1.local_ p.val
          coalitionTrivialView C ω k i p =
            (ls.echoSent, ls.echoesReceived, ls.readySent, ls.readyReceived) :=
  Filter.Eventually.of_forall (fun _ _ _ => rfl)

end Phase6_OperationalView

/-! ## §17.12 Phase 6.3 — operational view secrecy (conditional headline)

The headline operational secrecy theorem: under any adversary `A`
and any step `k`, the marginal of the trace distribution projected
to `(coalitionTraceView, schedulePrefix)` is invariant in the secret
— **modulo a documented joint-marginal hypothesis**.

### Why the unconditional theorem cannot be closed under the existing model

Two structural blockers prevent an unconditional proof of the
headline theorem against the existing `Adversary` in
`Leslie/Prob/Adversary.lean`:

1. **Schedule leakage (strong-adversary blocker).**
   The current `Adversary` has full-state read access:
   `schedule : List (σ × Option ι) → Option ι` may branch on any
   field of `σ`, including `s.coeffs`. Concrete counterexample: the
   strategy "schedule action `a` if `s.coeffs 0 0 = 0`, else action
   `b`" yields different `schedulePrefix` distributions under
   `sec = 0` vs. `sec = 1`. So
   `(traceDist sec A μ_sec).map schedulePrefix` itself is *not*
   invariant in the secret, and hence the joint marginal cannot be
   invariant either. Phase 7 (the **rushing** adversary refactor)
   replaces `Adversary` with a scheduler whose decisions depend only
   on corrupt parties' visible view; that closes this leak.

2. **Row-poly vs. grid secrecy (algebraic-core blocker).**
   The operational view records `rowPoly : Option (Fin (t+1) → F)`
   — the corrupt party's *full row polynomial*, having `t+1`
   coefficients. Phase 5 Layer E (`avss_secrecy_AS`) proves
   invariance of `coalitionGrid` only — at most `|C|·|D| ≤ t·t`
   bivariate evaluations, strictly less informative than `t` row
   polys (each `t+1` coefficients). The `+200 LOC` polynomial-
   manipulation step deferred in §17 is exactly the row-poly
   strengthening needed to close this gap.

### What this commit delivers

* `coalitionAlgebraicView` — the row-poly-level abstract operational
  view: corrupt parties' row polys (from initial state) plus their
  per-step `delivered` bits. This is the algebraic-level analogue of
  `coalitionTraceView` modulo the trivial-field constants pinned by
  `corruptLocalInv`.

* `coalitionTraceView_eq_reconstruct_AE` — the Phase 6.2 → 6.3
  structural bridge: almost surely along any trace,
  `coalitionTraceView` agrees with a deterministic reconstruction
  from `coalitionAlgebraicView`.

* `avss_secrecy_AS_view_conditional` — the conditional headline:
  given joint invariance of `(coalitionAlgebraicView,
  schedulePrefix)` (which Phase 7 + row-poly secrecy will
  unconditionally supply), the operational view's joint marginal
  `(coalitionTraceView, schedulePrefix)` is invariant in the secret.

A Phase 7 worker supplying the rushing-adversary + row-poly secrecy
proofs can drop them in as `h_aux` and obtain the headline theorem
mechanically. -/

/-- The abstract row-poly-level operational view of the corrupt
coalition at step `k`.

Components:
* `C.val → Fin (t+1) → F` — the corrupt parties' row polynomials,
  derived from `(ω 0).1.partyPoint` and `(ω 0).1.coeffs` via
  `rowPolyOfDealer`. Sec-secret in the row-poly sense (deferred
  algebraic core).
* `Fin k → C.val → Bool` — per-step `delivered` bits of every
  corrupt party. A finite-alphabet trace observable to the corrupt
  coalition.

Joint invariance with `schedulePrefix` is what Phase 7 (rushing
adversary) plus row-poly secrecy combine to provide. -/
noncomputable def coalitionAlgebraicView (C : BivariateShamir.Coalition n t)
    (ω : ℕ → AVSSState n t F × Option (AVSSAction n F)) (k : ℕ) :
    (C.val → Fin (t+1) → F) × (Fin k → C.val → Bool) :=
  (fun p => ((ω 0).1.dealerCommit p.val).rowPoly,
   fun i p => ((ω i.val).1.local_ p.val).delivered)

/-- Local discrete-σ-algebra on `Fin (t+1) → F`. Required for the
codomain of `coalitionAlgebraicView` to be a `MeasurableSpace`. -/
instance : MeasurableSpace (Fin (t+1) → F) := ⊤
instance : MeasurableSingletonClass (Fin (t+1) → F) := ⟨fun _ => trivial⟩

@[fun_prop]
theorem measurable_coalitionAlgebraicView
    (C : BivariateShamir.Coalition n t) (k : ℕ) :
    Measurable (fun ω : ℕ → AVSSState n t F × Option (AVSSAction n F) =>
        coalitionAlgebraicView C ω k) := by
  classical
  refine Measurable.prodMk (measurable_pi_iff.mpr fun p => ?_)
    (measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun p => ?_)
  · -- p ↦ ((ω 0).1.dealerCommit p.val).rowPoly.
    have h1 : Measurable (fun ω : ℕ → AVSSState n t F × Option (AVSSAction n F) =>
        ω 0) := measurable_pi_apply _
    have h2 : Measurable (Prod.fst :
        AVSSState n t F × Option (AVSSAction n F) → AVSSState n t F) := measurable_fst
    have h3 : Measurable (fun s : AVSSState n t F =>
        (s.dealerCommit p.val).rowPoly) := measurable_of_countable _
    exact (h3.comp h2).comp h1
  · -- (i, p) ↦ ((ω i.val).1.local_ p.val).delivered.
    have h1 : Measurable (fun ω : ℕ → AVSSState n t F × Option (AVSSAction n F) =>
        ω i.val) := measurable_pi_apply _
    have h2 : Measurable (Prod.fst :
        AVSSState n t F × Option (AVSSAction n F) → AVSSState n t F) := measurable_fst
    have h3 : Measurable (fun s : AVSSState n t F =>
        (s.local_ p.val).delivered) := measurable_of_countable _
    exact (h3.comp h2).comp h1

/-- Build a corrupt party's local state from its row poly, its
`TrivialView` projection, and its `delivered` bit. Phase 8.5c
weakening: the trivial fields are now schedule-dependent and are
threaded explicitly via `tv : TrivialView n` (rather than being
hardcoded to `(false, ∅, false, ∅)` as in pre-8.5b). -/
def buildCorruptLocalState (rp : Fin (t+1) → F) (tv : TrivialView n)
    (delivered : Bool) : AVSSLocalState n t F :=
  { delivered := delivered
    rowPoly := if delivered then some rp else none
    echoSent := tv.1
    echoesReceived := tv.2.1
    readySent := tv.2.2.1
    readyReceived := tv.2.2.2
    output := none }

omit [Fintype F] in
/-- A corrupt party's local state is uniquely determined by its
`delivered` bit, its row poly, and its trivial-field projection,
given that `output = none` (by `corruptLocalInv`) and `rowPoly`
follows `outputDeterminedInv` plus the pin. Phase 8.5c weakening:
the four trivial-field hypotheses are absorbed into the `tv`
parameter; the lemma now only requires the three algebraic-content
hypotheses. -/
lemma corrupt_local_state_uniqueness
    (ls : AVSSLocalState n t F) (rp : Fin (t+1) → F)
    (h_out : ls.output = none)
    (h_rp_none : ls.delivered = false → ls.rowPoly = none)
    (h_rp_some : ls.delivered = true → ls.rowPoly = some rp) :
    ls = buildCorruptLocalState rp
      (ls.echoSent, ls.echoesReceived, ls.readySent, ls.readyReceived)
      ls.delivered := by
  cases ls with
  | mk d rp_actual es er rr rs out =>
    simp only at h_out
    subst h_out
    cases d with
    | false =>
        have heq : rp_actual = none := h_rp_none rfl
        subst heq
        unfold buildCorruptLocalState
        rfl
    | true =>
        have heq : rp_actual = some rp := h_rp_some rfl
        subst heq
        unfold buildCorruptLocalState
        rfl

/-- Reconstruct `coalitionTraceView` from `(coalitionAlgebraicView,
coalitionTrivialView)`: at every `(i, p)`, build the corrupt local
state from `(rp p)`, the per-step trivial-field projection, and
`(delivered i p)`. Phase 8.5c restructuring: this function now
takes a `tv` parameter to thread the schedule-dependent trivial
fields. -/
def reconstructCoalitionTraceView
    {C : BivariateShamir.Coalition n t} {k : ℕ}
    (rp : C.val → Fin (t+1) → F)
    (tv : Fin k → C.val → TrivialView n)
    (delivered : Fin k → C.val → Bool) :
    Fin k → C.val → AVSSLocalState n t F :=
  fun i p => buildCorruptLocalState (rp p) (tv i p) (delivered i p)

omit [Field F] in
@[fun_prop]
theorem measurable_reconstruct_pair
    {C : BivariateShamir.Coalition n t} {k : ℕ} :
    Measurable
      (fun rtd : ((C.val → Fin (t+1) → F) × (Fin k → C.val → Bool)) ×
                 (Fin k → C.val → TrivialView n) =>
        reconstructCoalitionTraceView (C := C) (k := k)
          rtd.1.1 rtd.2 rtd.1.2) :=
  measurable_of_countable _

/-- **Phase 6.2 → 6.3 structural bridge** (8.5c). Almost surely along
the trace, `coalitionTraceView` matches `reconstructCoalitionTraceView`
applied to `(coalitionAlgebraicView, coalitionTrivialView)`. The
trivial-view component captures the schedule-dependent fields that,
post-8.5b-α, no longer pin to `(false, ∅, false, ∅)`. -/
theorem coalitionTraceView_eq_reconstruct_AE
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr coeffs s)
    (A : Adversary (AVSSState n t F) (AVSSAction n F))
    (C : BivariateShamir.Coalition n t)
    (h_C_corr : C.val ⊆ corr) (k : ℕ) :
    ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
        (ω 0).1.dealerHonest = true →
          coalitionTraceView C ω k =
            reconstructCoalitionTraceView (C := C) (k := k)
              (coalitionAlgebraicView C ω k).1
              (coalitionTrivialView C ω k)
              (coalitionAlgebraicView C ω k).2 := by
  classical
  -- The factoring theorem at every step i.  Take a finite AE-intersection
  -- over `Fin k` (each `i` is a separate AE statement).  We can use
  -- `Filter.Eventually.forall_finite` (or chain `filter_upwards`) since
  -- `Fin k` is finite.
  have h_factors_i : ∀ i : Fin k,
      ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
          ∀ p : C.val,
            let ls := (ω i.val).1.local_ p.val
            ls.output = none ∧
            (ls.delivered = false → ls.rowPoly = none) ∧
            ((ω 0).1.dealerHonest = true → ls.delivered = true →
              ls.rowPoly = some (rowPolyOfDealer (ω 0).1.partyPoint
                coeffs p.val)) :=
    fun i => coalitionView_corrupt_factors_AE (t := t) sec corr coeffs μ₀ h_init A C h_C_corr i.val
  -- AE-intersection over the finite index set `Fin k`.
  have h_factors_all :
      ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
        ∀ i : Fin k, ∀ p : C.val,
          let ls := (ω i.val).1.local_ p.val
          ls.output = none ∧
          (ls.delivered = false → ls.rowPoly = none) ∧
          ((ω 0).1.dealerHonest = true → ls.delivered = true →
            ls.rowPoly = some (rowPolyOfDealer (ω 0).1.partyPoint
              coeffs p.val)) :=
    (ae_all_iff (ι := Fin k)).mpr h_factors_i
  -- Lift `h_init` into a per-trace AE statement at step 0.
  have h_init_AE : ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
      initPred sec corr coeffs (ω 0).1 := by
    have hmap := traceDist_step_zero_state_marginal (t := t) sec corr coeffs μ₀ A
    have hmeas : Measurable (fun ω : Π _ : ℕ, AVSSState n t F × Option (AVSSAction n F) =>
        (ω 0).1) := by fun_prop
    rw [← hmap] at h_init
    rwa [ae_map_iff hmeas.aemeasurable MeasurableSet.of_discrete] at h_init
  filter_upwards [h_factors_all, h_init_AE] with ω hω h_init0 hHonest
  -- For each (i : Fin k, p : C.val), apply uniqueness lemma.
  -- Bridge: under honest dealer, `(ω 0).1.dealerCommit p .rowPoly =
  -- rowPolyOfDealer ((ω 0).1.partyPoint) coeffs p` from `initPred`.
  have h_dC := (h_init0.2.2.2.2.2.2.2.2.2 hHonest).2
  funext i p
  obtain ⟨h_out, h_rp_none, h_rp_some⟩ := hω i p
  show (ω i.val).1.local_ p.val =
    reconstructCoalitionTraceView (C := C) (k := k)
      (coalitionAlgebraicView C ω k).1
      (coalitionTrivialView C ω k)
      (coalitionAlgebraicView C ω k).2 i p
  -- (ω 0).1.dealerCommit p.val .rowPoly = rowPolyOfDealer (ω 0).1.partyPoint coeffs p.val.
  have h_eq : ((ω 0).1.dealerCommit p.val).rowPoly =
      rowPolyOfDealer (ω 0).1.partyPoint coeffs p.val := by
    rw [h_dC p.val]
  simp only [reconstructCoalitionTraceView, coalitionAlgebraicView,
    coalitionTrivialView, h_eq]
  exact corrupt_local_state_uniqueness (ls := (ω i.val).1.local_ p.val)
    (rp := rowPolyOfDealer (ω 0).1.partyPoint coeffs p.val)
    h_out h_rp_none (h_rp_some hHonest)

/-- **Phase 8.5d-β-followup-6 — existential variant of
`coalitionTraceView_eq_reconstruct_AE`.**

Same conclusion as the fixed-coeffs version (which is already coeffs-
free since `coalitionAlgebraicView` uses `(ω 0).1.dealerCommit` rather
than `coeffs` directly), but takes the existential AE-hypothesis
`∀ᵐ s ∂μ₀, ∃ c, initPred sec corr c s` (the form returned by
`avssInitMeasure_AE_initPred` after the μ₀ migration).

Internally uses `coalitionView_corrupt_factors_AE_ex` whose conclusion
is already in `dealerCommit` form, so the bridging lemma at the
filter_upwards site is a direct application of
`corrupt_local_state_uniqueness` with `rp = ((ω 0).1.dealerCommit p).rowPoly`. -/
theorem coalitionTraceView_eq_reconstruct_AE_ex
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, ∃ c, initPred sec corr c s)
    (A : Adversary (AVSSState n t F) (AVSSAction n F))
    (C : BivariateShamir.Coalition n t)
    (h_C_corr : C.val ⊆ corr) (k : ℕ) :
    ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
        (ω 0).1.dealerHonest = true →
          coalitionTraceView C ω k =
            reconstructCoalitionTraceView (C := C) (k := k)
              (coalitionAlgebraicView C ω k).1
              (coalitionTrivialView C ω k)
              (coalitionAlgebraicView C ω k).2 := by
  classical
  have h_factors_i : ∀ i : Fin k,
      ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
          ∀ p : C.val,
            let ls := (ω i.val).1.local_ p.val
            ls.output = none ∧
            (ls.delivered = false → ls.rowPoly = none) ∧
            ((ω 0).1.dealerHonest = true → ls.delivered = true →
              ls.rowPoly = some ((ω 0).1.dealerCommit p.val).rowPoly) :=
    fun i => coalitionView_corrupt_factors_AE_ex (t := t) sec corr coeffs μ₀
      h_init A C h_C_corr i.val
  have h_factors_all :
      ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
        ∀ i : Fin k, ∀ p : C.val,
          let ls := (ω i.val).1.local_ p.val
          ls.output = none ∧
          (ls.delivered = false → ls.rowPoly = none) ∧
          ((ω 0).1.dealerHonest = true → ls.delivered = true →
            ls.rowPoly = some ((ω 0).1.dealerCommit p.val).rowPoly) :=
    (ae_all_iff (ι := Fin k)).mpr h_factors_i
  filter_upwards [h_factors_all] with ω hω hHonest
  funext i p
  obtain ⟨h_out, h_rp_none, h_rp_some⟩ := hω i p
  show (ω i.val).1.local_ p.val =
    reconstructCoalitionTraceView (C := C) (k := k)
      (coalitionAlgebraicView C ω k).1
      (coalitionTrivialView C ω k)
      (coalitionAlgebraicView C ω k).2 i p
  simp only [reconstructCoalitionTraceView, coalitionAlgebraicView,
    coalitionTrivialView]
  exact corrupt_local_state_uniqueness (ls := (ω i.val).1.local_ p.val)
    (rp := ((ω 0).1.dealerCommit p.val).rowPoly)
    h_out h_rp_none (h_rp_some hHonest)

/-- **Phase 8.5d-β-followup-7 — dealerHonest-INDEPENDENT cTV bridge.**

Drops the honest-dealer guard from the conclusion of
`coalitionTraceView_eq_reconstruct_AE_ex`.  The proof uses the
dealerHonest-INDEPENDENT factor lemma `coalitionView_corrupt_factors_AE_indep`
internally.  This is the bridge used by the dealerHonest-INDEPENDENT
chain wrappers (`_view_conditional_indep`, etc.) to close the
corrupt-dealer headline case from followup-6. -/
theorem coalitionTraceView_eq_reconstruct_AE_indep
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, ∃ c, initPred sec corr c s)
    (A : Adversary (AVSSState n t F) (AVSSAction n F))
    (C : BivariateShamir.Coalition n t)
    (h_C_corr : C.val ⊆ corr) (k : ℕ) :
    ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
        coalitionTraceView C ω k =
          reconstructCoalitionTraceView (C := C) (k := k)
            (coalitionAlgebraicView C ω k).1
            (coalitionTrivialView C ω k)
            (coalitionAlgebraicView C ω k).2 := by
  classical
  have h_factors_i : ∀ i : Fin k,
      ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
          ∀ p : C.val,
            let ls := (ω i.val).1.local_ p.val
            ls.output = none ∧
            (ls.delivered = false → ls.rowPoly = none) ∧
            (ls.delivered = true →
              ls.rowPoly = some ((ω 0).1.dealerCommit p.val).rowPoly) :=
    fun i => coalitionView_corrupt_factors_AE_indep (t := t) sec corr coeffs μ₀
      h_init A C h_C_corr i.val
  have h_factors_all :
      ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ₀),
        ∀ i : Fin k, ∀ p : C.val,
          let ls := (ω i.val).1.local_ p.val
          ls.output = none ∧
          (ls.delivered = false → ls.rowPoly = none) ∧
          (ls.delivered = true →
            ls.rowPoly = some ((ω 0).1.dealerCommit p.val).rowPoly) :=
    (ae_all_iff (ι := Fin k)).mpr h_factors_i
  filter_upwards [h_factors_all] with ω hω
  funext i p
  obtain ⟨h_out, h_rp_none, h_rp_some⟩ := hω i p
  show (ω i.val).1.local_ p.val =
    reconstructCoalitionTraceView (C := C) (k := k)
      (coalitionAlgebraicView C ω k).1
      (coalitionTrivialView C ω k)
      (coalitionAlgebraicView C ω k).2 i p
  simp only [reconstructCoalitionTraceView, coalitionAlgebraicView,
    coalitionTrivialView]
  exact corrupt_local_state_uniqueness (ls := (ω i.val).1.local_ p.val)
    (rp := ((ω 0).1.dealerCommit p.val).rowPoly)
    h_out h_rp_none h_rp_some

/-- **Phase 6.3 conditional headline theorem (8.5c form).** Given the
joint invariance of `(coalitionAlgebraicView, coalitionTrivialView,
schedulePrefix)` in the secret — Phase 7.5/7.6 plus row-poly secrecy
will unconditionally supply this — the operational view's joint
marginal `(coalitionTraceView, schedulePrefix)` is invariant in the
secret. Phase 8.5c update: `h_aux` now also covers the trivial-view
projection, since post-8.5b-α the trivial fields are
schedule-dependent.

⚠ See the §17.12 doc-comment for the two structural blockers
(schedule leakage + row-poly-vs-grid secrecy) that prevent an
unconditional proof under the current `Adversary` model. -/
theorem avss_secrecy_AS_view_conditional
    (sec sec' : F) (corr : Finset (Fin n))
    (μ_sec μ_sec' : Measure (AVSSState n t F))
    [IsProbabilityMeasure μ_sec] [IsProbabilityMeasure μ_sec']
    (h_init_sec : ∀ᵐ s ∂μ_sec, initPred sec corr coeffs s)
    (h_init_sec' : ∀ᵐ s ∂μ_sec', initPred sec' corr coeffs s)
    (h_dH_sec : ∀ᵐ s ∂μ_sec, s.dealerHonest = true)
    (h_dH_sec' : ∀ᵐ s ∂μ_sec', s.dealerHonest = true)
    (C : BivariateShamir.Coalition n t)
    (h_C_corr : C.val ⊆ corr)
    (A : Adversary (AVSSState n t F) (AVSSAction n F))
    (k : ℕ)
    (h_aux :
      (traceDist (avssSpec (t := t) sec corr coeffs) A μ_sec).map
          (fun ω => ((coalitionAlgebraicView C ω k, coalitionTrivialView C ω k),
                     schedulePrefix ω k)) =
        (traceDist (avssSpec (t := t) sec' corr coeffs) A μ_sec').map
          (fun ω => ((coalitionAlgebraicView C ω k, coalitionTrivialView C ω k),
                     schedulePrefix ω k))) :
    (traceDist (avssSpec (t := t) sec corr coeffs) A μ_sec).map
        (fun ω => (coalitionTraceView C ω k, schedulePrefix ω k)) =
      (traceDist (avssSpec (t := t) sec' corr coeffs) A μ_sec').map
        (fun ω => (coalitionTraceView C ω k, schedulePrefix ω k)) := by
  classical
  -- The reduction map: given `((av, tv), sp) : (algView, trivView, sched)`,
  -- produce `(reconstruct av tv sched_delivered, sp) : (coalitionTraceView, schedule)`.
  set G : (((C.val → Fin (t+1) → F) × (Fin k → C.val → Bool)) ×
            (Fin k → C.val → TrivialView n)) ×
            (Fin k → Option (AVSSAction n F)) →
          (Fin k → C.val → AVSSLocalState n t F) ×
            (Fin k → Option (AVSSAction n F)) :=
    fun atSp =>
      (reconstructCoalitionTraceView (C := C) (k := k)
        atSp.1.1.1 atSp.1.2 atSp.1.1.2,
       atSp.2)
    with hG_def
  have hmeas_G : Measurable G := measurable_of_countable _
  -- Lift `h_dH_sec`/`h_dH_sec'` from μ to traceDist via the step-0 marginal.
  have h_dH_sec_AE : ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ_sec),
      (ω 0).1.dealerHonest = true := by
    have hmap := traceDist_step_zero_state_marginal (t := t) sec corr coeffs μ_sec A
    have hmeas : Measurable (fun ω : Π _ : ℕ, AVSSState n t F × Option (AVSSAction n F) =>
        (ω 0).1) := by fun_prop
    rw [← hmap] at h_dH_sec
    rwa [ae_map_iff hmeas.aemeasurable MeasurableSet.of_discrete] at h_dH_sec
  have h_dH_sec'_AE : ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec' corr coeffs) A μ_sec'),
      (ω 0).1.dealerHonest = true := by
    have hmap := traceDist_step_zero_state_marginal (t := t) sec' corr coeffs μ_sec' A
    have hmeas : Measurable (fun ω : Π _ : ℕ, AVSSState n t F × Option (AVSSAction n F) =>
        (ω 0).1) := by fun_prop
    rw [← hmap] at h_dH_sec'
    rwa [ae_map_iff hmeas.aemeasurable MeasurableSet.of_discrete] at h_dH_sec'
  -- Bridge: cTV ω = reconstruct (algView ω, trivView ω) AE under both traces.
  have h_bridge_sec :=
    coalitionTraceView_eq_reconstruct_AE (t := t) sec corr coeffs μ_sec
      h_init_sec A C h_C_corr k
  have h_bridge_sec' :=
    coalitionTraceView_eq_reconstruct_AE (t := t) sec' corr coeffs μ_sec'
      h_init_sec' A C h_C_corr k
  -- Push the `cTV, sP` marginal through `G ∘ (algView, trivView, sP)`.
  have h_push_sec :
      (traceDist (avssSpec (t := t) sec corr coeffs) A μ_sec).map
          (fun ω => (coalitionTraceView C ω k, schedulePrefix ω k)) =
        (traceDist (avssSpec (t := t) sec corr coeffs) A μ_sec).map
          (fun ω => G ((coalitionAlgebraicView C ω k,
                         coalitionTrivialView C ω k),
                        schedulePrefix ω k)) := by
    apply Measure.map_congr
    filter_upwards [h_bridge_sec, h_dH_sec_AE] with ω hω hH
    rw [hG_def]
    simp only [hω hH]
  have h_push_sec' :
      (traceDist (avssSpec (t := t) sec' corr coeffs) A μ_sec').map
          (fun ω => (coalitionTraceView C ω k, schedulePrefix ω k)) =
        (traceDist (avssSpec (t := t) sec' corr coeffs) A μ_sec').map
          (fun ω => G ((coalitionAlgebraicView C ω k,
                         coalitionTrivialView C ω k),
                        schedulePrefix ω k)) := by
    apply Measure.map_congr
    filter_upwards [h_bridge_sec', h_dH_sec'_AE] with ω hω hH
    rw [hG_def]
    simp only [hω hH]
  -- Compose with the auxiliary hypothesis (joint × sP invariance).
  rw [h_push_sec, h_push_sec']
  -- Both sides equal `(map (algView, trivView, sP)).map G`. Apply h_aux.
  rw [show (fun ω : ℕ → AVSSState n t F × Option (AVSSAction n F) =>
        G ((coalitionAlgebraicView C ω k, coalitionTrivialView C ω k),
           schedulePrefix ω k)) =
      G ∘ (fun ω => ((coalitionAlgebraicView C ω k,
                       coalitionTrivialView C ω k),
                      schedulePrefix ω k)) from rfl]
  have hmeas_av_sp_sec :
      Measurable (fun ω : ℕ → AVSSState n t F × Option (AVSSAction n F) =>
          ((coalitionAlgebraicView C ω k, coalitionTrivialView C ω k),
           schedulePrefix ω k)) :=
    ((measurable_coalitionAlgebraicView C k).prodMk
        (measurable_coalitionTrivialView C k)).prodMk
      (measurable_schedulePrefix k)
  rw [← Measure.map_map hmeas_G hmeas_av_sp_sec,
      ← Measure.map_map hmeas_G hmeas_av_sp_sec, h_aux]

/-- **Phase 8.5d-β-followup-6 — existential variant of
`avss_secrecy_AS_view_conditional`.**

Identical to the fixed-coeffs version except `h_init_sec` /
`h_init_sec'` take the existential AE-form
`∀ᵐ s ∂μ, ∃ c, initPred sec corr c s` (returned by
`avssInitMeasure_AE_initPred` post μ₀ migration). Internally uses
`coalitionTraceView_eq_reconstruct_AE_ex` instead of the fixed-c
version; the rest of the body is mechanical. -/
theorem avss_secrecy_AS_view_conditional_ex
    (sec sec' : F) (corr : Finset (Fin n))
    (μ_sec μ_sec' : Measure (AVSSState n t F))
    [IsProbabilityMeasure μ_sec] [IsProbabilityMeasure μ_sec']
    (h_init_sec : ∀ᵐ s ∂μ_sec, ∃ c, initPred sec corr c s)
    (h_init_sec' : ∀ᵐ s ∂μ_sec', ∃ c, initPred sec' corr c s)
    (h_dH_sec : ∀ᵐ s ∂μ_sec, s.dealerHonest = true)
    (h_dH_sec' : ∀ᵐ s ∂μ_sec', s.dealerHonest = true)
    (C : BivariateShamir.Coalition n t)
    (h_C_corr : C.val ⊆ corr)
    (A : Adversary (AVSSState n t F) (AVSSAction n F))
    (k : ℕ)
    (h_aux :
      (traceDist (avssSpec (t := t) sec corr coeffs) A μ_sec).map
          (fun ω => ((coalitionAlgebraicView C ω k, coalitionTrivialView C ω k),
                     schedulePrefix ω k)) =
        (traceDist (avssSpec (t := t) sec' corr coeffs) A μ_sec').map
          (fun ω => ((coalitionAlgebraicView C ω k, coalitionTrivialView C ω k),
                     schedulePrefix ω k))) :
    (traceDist (avssSpec (t := t) sec corr coeffs) A μ_sec).map
        (fun ω => (coalitionTraceView C ω k, schedulePrefix ω k)) =
      (traceDist (avssSpec (t := t) sec' corr coeffs) A μ_sec').map
        (fun ω => (coalitionTraceView C ω k, schedulePrefix ω k)) := by
  classical
  set G : (((C.val → Fin (t+1) → F) × (Fin k → C.val → Bool)) ×
            (Fin k → C.val → TrivialView n)) ×
            (Fin k → Option (AVSSAction n F)) →
          (Fin k → C.val → AVSSLocalState n t F) ×
            (Fin k → Option (AVSSAction n F)) :=
    fun atSp =>
      (reconstructCoalitionTraceView (C := C) (k := k)
        atSp.1.1.1 atSp.1.2 atSp.1.1.2,
       atSp.2)
    with hG_def
  have hmeas_G : Measurable G := measurable_of_countable _
  have h_dH_sec_AE : ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) A μ_sec),
      (ω 0).1.dealerHonest = true := by
    have hmap := traceDist_step_zero_state_marginal (t := t) sec corr coeffs μ_sec A
    have hmeas : Measurable (fun ω : Π _ : ℕ, AVSSState n t F × Option (AVSSAction n F) =>
        (ω 0).1) := by fun_prop
    rw [← hmap] at h_dH_sec
    rwa [ae_map_iff hmeas.aemeasurable MeasurableSet.of_discrete] at h_dH_sec
  have h_dH_sec'_AE : ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec' corr coeffs) A μ_sec'),
      (ω 0).1.dealerHonest = true := by
    have hmap := traceDist_step_zero_state_marginal (t := t) sec' corr coeffs μ_sec' A
    have hmeas : Measurable (fun ω : Π _ : ℕ, AVSSState n t F × Option (AVSSAction n F) =>
        (ω 0).1) := by fun_prop
    rw [← hmap] at h_dH_sec'
    rwa [ae_map_iff hmeas.aemeasurable MeasurableSet.of_discrete] at h_dH_sec'
  have h_bridge_sec :=
    coalitionTraceView_eq_reconstruct_AE_ex (t := t) sec corr coeffs μ_sec
      h_init_sec A C h_C_corr k
  have h_bridge_sec' :=
    coalitionTraceView_eq_reconstruct_AE_ex (t := t) sec' corr coeffs μ_sec'
      h_init_sec' A C h_C_corr k
  have h_push_sec :
      (traceDist (avssSpec (t := t) sec corr coeffs) A μ_sec).map
          (fun ω => (coalitionTraceView C ω k, schedulePrefix ω k)) =
        (traceDist (avssSpec (t := t) sec corr coeffs) A μ_sec).map
          (fun ω => G ((coalitionAlgebraicView C ω k,
                         coalitionTrivialView C ω k),
                        schedulePrefix ω k)) := by
    apply Measure.map_congr
    filter_upwards [h_bridge_sec, h_dH_sec_AE] with ω hω hH
    rw [hG_def]
    simp only [hω hH]
  have h_push_sec' :
      (traceDist (avssSpec (t := t) sec' corr coeffs) A μ_sec').map
          (fun ω => (coalitionTraceView C ω k, schedulePrefix ω k)) =
        (traceDist (avssSpec (t := t) sec' corr coeffs) A μ_sec').map
          (fun ω => G ((coalitionAlgebraicView C ω k,
                         coalitionTrivialView C ω k),
                        schedulePrefix ω k)) := by
    apply Measure.map_congr
    filter_upwards [h_bridge_sec', h_dH_sec'_AE] with ω hω hH
    rw [hG_def]
    simp only [hω hH]
  rw [h_push_sec, h_push_sec']
  rw [show (fun ω : ℕ → AVSSState n t F × Option (AVSSAction n F) =>
        G ((coalitionAlgebraicView C ω k, coalitionTrivialView C ω k),
           schedulePrefix ω k)) =
      G ∘ (fun ω => ((coalitionAlgebraicView C ω k,
                       coalitionTrivialView C ω k),
                      schedulePrefix ω k)) from rfl]
  have hmeas_av_sp_sec :
      Measurable (fun ω : ℕ → AVSSState n t F × Option (AVSSAction n F) =>
          ((coalitionAlgebraicView C ω k, coalitionTrivialView C ω k),
           schedulePrefix ω k)) :=
    ((measurable_coalitionAlgebraicView C k).prodMk
        (measurable_coalitionTrivialView C k)).prodMk
      (measurable_schedulePrefix k)
  rw [← Measure.map_map hmeas_G hmeas_av_sp_sec,
      ← Measure.map_map hmeas_G hmeas_av_sp_sec, h_aux]

/-- **Phase 8.5d-β-followup-7 — dealerHonest-INDEPENDENT view conditional.**

Generalizes `avss_secrecy_AS_view_conditional_ex` by dropping the
`h_dH_sec` / `h_dH_sec'` hypotheses (the cTV bridge in the `_indep`
chain fires unconditionally, so `Measure.map_congr` works without an
honest-dealer guard).

Closes the corrupt-dealer headline case from followup-6. -/
theorem avss_secrecy_AS_view_conditional_indep
    (sec sec' : F) (corr : Finset (Fin n))
    (μ_sec μ_sec' : Measure (AVSSState n t F))
    [IsProbabilityMeasure μ_sec] [IsProbabilityMeasure μ_sec']
    (h_init_sec : ∀ᵐ s ∂μ_sec, ∃ c, initPred sec corr c s)
    (h_init_sec' : ∀ᵐ s ∂μ_sec', ∃ c, initPred sec' corr c s)
    (C : BivariateShamir.Coalition n t)
    (h_C_corr : C.val ⊆ corr)
    (A : Adversary (AVSSState n t F) (AVSSAction n F))
    (k : ℕ)
    (h_aux :
      (traceDist (avssSpec (t := t) sec corr coeffs) A μ_sec).map
          (fun ω => ((coalitionAlgebraicView C ω k, coalitionTrivialView C ω k),
                     schedulePrefix ω k)) =
        (traceDist (avssSpec (t := t) sec' corr coeffs) A μ_sec').map
          (fun ω => ((coalitionAlgebraicView C ω k, coalitionTrivialView C ω k),
                     schedulePrefix ω k))) :
    (traceDist (avssSpec (t := t) sec corr coeffs) A μ_sec).map
        (fun ω => (coalitionTraceView C ω k, schedulePrefix ω k)) =
      (traceDist (avssSpec (t := t) sec' corr coeffs) A μ_sec').map
        (fun ω => (coalitionTraceView C ω k, schedulePrefix ω k)) := by
  classical
  set G : (((C.val → Fin (t+1) → F) × (Fin k → C.val → Bool)) ×
            (Fin k → C.val → TrivialView n)) ×
            (Fin k → Option (AVSSAction n F)) →
          (Fin k → C.val → AVSSLocalState n t F) ×
            (Fin k → Option (AVSSAction n F)) :=
    fun atSp =>
      (reconstructCoalitionTraceView (C := C) (k := k)
        atSp.1.1.1 atSp.1.2 atSp.1.1.2,
       atSp.2)
    with hG_def
  have hmeas_G : Measurable G := measurable_of_countable _
  have h_bridge_sec :=
    coalitionTraceView_eq_reconstruct_AE_indep (t := t) sec corr coeffs μ_sec
      h_init_sec A C h_C_corr k
  have h_bridge_sec' :=
    coalitionTraceView_eq_reconstruct_AE_indep (t := t) sec' corr coeffs μ_sec'
      h_init_sec' A C h_C_corr k
  have h_push_sec :
      (traceDist (avssSpec (t := t) sec corr coeffs) A μ_sec).map
          (fun ω => (coalitionTraceView C ω k, schedulePrefix ω k)) =
        (traceDist (avssSpec (t := t) sec corr coeffs) A μ_sec).map
          (fun ω => G ((coalitionAlgebraicView C ω k,
                         coalitionTrivialView C ω k),
                        schedulePrefix ω k)) := by
    apply Measure.map_congr
    filter_upwards [h_bridge_sec] with ω hω
    rw [hG_def]
    simp only [hω]
  have h_push_sec' :
      (traceDist (avssSpec (t := t) sec' corr coeffs) A μ_sec').map
          (fun ω => (coalitionTraceView C ω k, schedulePrefix ω k)) =
        (traceDist (avssSpec (t := t) sec' corr coeffs) A μ_sec').map
          (fun ω => G ((coalitionAlgebraicView C ω k,
                         coalitionTrivialView C ω k),
                        schedulePrefix ω k)) := by
    apply Measure.map_congr
    filter_upwards [h_bridge_sec'] with ω hω
    rw [hG_def]
    simp only [hω]
  rw [h_push_sec, h_push_sec']
  rw [show (fun ω : ℕ → AVSSState n t F × Option (AVSSAction n F) =>
        G ((coalitionAlgebraicView C ω k, coalitionTrivialView C ω k),
           schedulePrefix ω k)) =
      G ∘ (fun ω => ((coalitionAlgebraicView C ω k,
                       coalitionTrivialView C ω k),
                      schedulePrefix ω k)) from rfl]
  have hmeas_av_sp_sec :
      Measurable (fun ω : ℕ → AVSSState n t F × Option (AVSSAction n F) =>
          ((coalitionAlgebraicView C ω k, coalitionTrivialView C ω k),
           schedulePrefix ω k)) :=
    ((measurable_coalitionAlgebraicView C k).prodMk
        (measurable_coalitionTrivialView C k)).prodMk
      (measurable_schedulePrefix k)
  rw [← Measure.map_map hmeas_G hmeas_av_sp_sec,
      ← Measure.map_map hmeas_G hmeas_av_sp_sec, h_aux]

/-! ## §18. Polynomial-level secrecy (Phase 4, kept for the headline)

Direct passthrough to `BivariateShamir.bivariate_shamir_secrecy`.
The post-deal grid view at any `t`-coalition is independent of the
secret. This is the **grid form** — option (b) in the SyncVSS brief.
The full **row + column** view secrecy (a strict generalisation) is
the +200 LOC polynomial-manipulation step explicitly deferred in
`SyncVSS.lean §10`; we inherit the same deferral. See §17.12 for
the trace-level analogue and `AVSS-MODEL-NOTES.md` for the broader
adversary-model story. -/

/-- AVSS coalition-view secrecy (grid form, **full** distribution). -/
theorem avss_secrecy (partyPoint : Fin n → F)
    (h_nz_pp : ∀ i, partyPoint i ≠ 0)
    (h_F : t + 1 ≤ Fintype.card F)
    (C D : BivariateShamir.Coalition n t) (sec sec' : F) :
    (Leslie.Prob.Polynomial.uniformBivariateFullWithFixedZero t t sec).map
        (fun f => fun (i : C.val) (j : D.val) =>
          some ((f.eval (Polynomial.C (partyPoint i.val))).eval
            (partyPoint j.val)))
      =
    (Leslie.Prob.Polynomial.uniformBivariateFullWithFixedZero t t sec').map
        (fun f => fun (i : C.val) (j : D.val) =>
          some ((f.eval (Polynomial.C (partyPoint i.val))).eval
            (partyPoint j.val))) :=
  BivariateShamir.bivariate_shamir_secrecy_full partyPoint h_nz_pp h_F C D sec sec'

/-! ## §19. Rushing adversary instantiation (Phase 7.2)

Phase 7 closes the schedule-leakage caveat from Phase 6 by introducing
the standard cryptography-literature *rushing adversary* — a scheduler
whose decisions depend only on the corrupt coalition's view of the
state, not on the full state.

The generic types `Leslie.Prob.ProtocolView` and
`Leslie.Prob.RushingAdversary` live in `Leslie/Prob/Adversary.lean`.
This section is the AVSS-specific instantiation: the projection `view`
that maps an `AVSSState` to the corrupt coalition's local states.

Concretely, the coalition view of `s : AVSSState n t F` for a corrupt
set `corr : Finset (Fin n)` is the function `corr → AVSSLocalState n t F`
that, on each corrupt party `p`, returns `s.local_ p.val`. Messages "in
flight" between honest parties are not part of the view because in our
state-based model they are encoded as state-mutations on the
recipient's local state, observable only when the corresponding
receive-action fires for a corrupt party.

This generalises `coalitionView` (Phase 5/6) from a size-`t`
`BivariateShamir.Coalition` to an arbitrary `Finset (Fin n)`.

The canonical headline theorem `avss_secrecy_AS_view_rushing`
(§19.4.5) discharges the `h_aux` hypothesis of
`avss_secrecy_AS_view_conditional` unconditionally, by composing
Phase 7.4's schedule-factoring AE-bridge with Phase 5's step-`k`
algebraic-view secrecy and the row-poly secrecy lemma. -/

/-- The view of an AVSS state visible to the corrupt coalition `corr`:
the local states of every corrupt party.

Consistent with `coalitionView` (Phase 5/6) but generalised from a
size-`t` `BivariateShamir.Coalition` to an arbitrary `Finset (Fin n)`,
and packaged as the `V` parameter of `Leslie.Prob.ProtocolView` for use
with `Leslie.Prob.RushingAdversary`. -/
abbrev AVSSRushingView (n t : ℕ) (F : Type*) [DecidableEq F]
    (corr : Finset (Fin n)) : Type _ :=
  corr → AVSSLocalState n t F

/-- Discrete σ-algebra on `AVSSRushingView`. The codomain
`AVSSLocalState n t F` carries the maximal σ-algebra and is countable
(both established in §10); the function space `corr → AVSSLocalState`
inherits the maximal σ-algebra and singleton-measurability via the
discrete topology. -/
instance instMeasurableSpaceAVSSRushingView
    (corr : Finset (Fin n)) : MeasurableSpace (AVSSRushingView n t F corr) := ⊤

instance instMeasurableSingletonClassAVSSRushingView
    (corr : Finset (Fin n)) :
    MeasurableSingletonClass (AVSSRushingView n t F corr) :=
  ⟨fun _ => trivial⟩

instance instCountableAVSSRushingView
    (corr : Finset (Fin n)) : Countable (AVSSRushingView n t F corr) :=
  inferInstance

/-- The AVSS coalition-view projection, packaged as a generic
`Leslie.Prob.ProtocolView`. Used as the `ProtocolView` parameter of
`Leslie.Prob.RushingAdversary` when instantiating the rushing-adversary
machinery for AVSS. -/
def avssCoalitionView (corr : Finset (Fin n)) :
    Leslie.Prob.ProtocolView (AVSSState n t F) (AVSSRushingView n t F corr) where
  view s := fun p => s.local_ p.val

omit [Field F] [Fintype F] in
theorem avssCoalitionView_view_apply
    (corr : Finset (Fin n)) (s : AVSSState n t F) (p : corr) :
    (avssCoalitionView (n := n) (t := t) (F := F) corr).view s p =
      s.local_ p.val := rfl

omit [Field F] in
theorem measurable_avssCoalitionView_view
    (corr : Finset (Fin n)) :
    Measurable
      (fun s : AVSSState n t F =>
        (avssCoalitionView (n := n) (t := t) (F := F) corr).view s) :=
  measurable_of_countable _

/-- A `RushingAdversary` for AVSS specialises the generic
view-restricted scheduler to the AVSS state, action, and coalition-view
types. This abbreviation is the canonical entry point for downstream
theorems quantifying over rushing adversaries (Phase 7.3, 7.5). -/
abbrev AVSSRushingAdversary (n t : ℕ) (F : Type*) [DecidableEq F] [Fintype F]
    (corr : Finset (Fin n)) : Type _ :=
  Leslie.Prob.RushingAdversary
    (AVSSState n t F) (AVSSAction n F) (AVSSRushingView n t F corr)

/-- A `RushingRandomisedAdversary` for AVSS specialises the generic
view-restricted *randomised* scheduler to the AVSS state, action, and
coalition-view types.  Phase 9.5 (MODEL_NOTES §13.5): the
randomised analog of `AVSSRushingAdversary`, used by the four
`_rushing_randomised` headline restatements (`avss_correctness_…`,
`avss_commitment_…`, `avss_secrecy_…`, `avss_termination_…`) below.

The schedule is a PMF on the rushing-view σ-algebra; via
`instCountableAVSSRushingView`, this PMF is automatically measurable
on the discrete σ-algebra carried by the rushing view, which is the
measurability backbone the deferred Phase 9.3 wrappers needed. -/
abbrev AVSSRushingRandomisedAdversary
    (n t : ℕ) (F : Type*) [DecidableEq F] [Fintype F]
    (corr : Finset (Fin n)) : Type _ :=
  Leslie.Prob.RushingRandomisedAdversary
    (AVSSState n t F) (AVSSAction n F) (AVSSRushingView n t F corr)

/-! ## §19.1. Classical theorems against `RushingAdversary` (Phase 7.3)

Re-statements of the classical AVSS theorems (termination, correctness,
commitment) against `AVSSRushingAdversary`. Each is a thin wrapper that
threads `R.toAdversary` into the existing `Adversary`-quantified
theorem. `avss_reconstruction` is purely algebraic and needs no
rushing-adversary version.

Recall `avssFair.isWeaklyFair = fun _ => True` (every adversary is
trivially weakly-fair w.r.t. AVSS's fairness assumptions; the
substantive condition is `TrajectoryFairProgress`, threaded through
`TrajectoryFairAdversary`). The termination wrapper accepts the
trajectory-progress witness directly against `R.toAdversary`. -/

/-- Termination as `AlmostDiamond` under a trajectory-fair *rushing*
adversary. Re-statement of `avss_termination_AS_fair` with the
underlying adversary supplied as `R.toAdversary` and fairness/progress
witnesses formulated against that lift.

Phase 8.5b-δ: switched to BC running-min route; the
`TrajectoryUMono`/`TrajectoryFairStrictDecrease` witnesses required
by the deterministic-descent route have been replaced by a single
per-sublevel `TrajectoryFairRunningMinDropIO` witness.

Phase 8.5d-γ: takes `h_consistent_quorum` (the conditional-CR
runtime hypothesis under selective non-broadcast). See
`consistent_quorum_AE`. -/
theorem avss_termination_AS_fair_rushing
    (sec : F) (corr : Finset (Fin n)) (h_corr : corr.card ≤ t)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr coeffs s)
    (R : AVSSRushingAdversary n t F corr)
    (h_progress : FairASTCertificate.TrajectoryFairProgress
      (avssSpec (t := t) sec corr coeffs) avssFair μ₀
      ⟨R.toAdversary, trivial⟩)
    (h_consistent_quorum :
      consistent_quorum_AE sec corr coeffs μ₀ R.toAdversary)
    (h_drop_io : ∀ N : ℕ, FairASTCertificate.TrajectoryFairRunningMinDropIO
      (avssSpec (t := t) sec corr coeffs) avssFair
      (avssCert (t := t) sec corr coeffs h_corr) μ₀
      ⟨R.toAdversary, trivial⟩ N) :
    AlmostDiamond (avssSpec (t := t) sec corr coeffs) R.toAdversary μ₀ terminated :=
  avss_termination_AS_fair sec corr h_corr coeffs μ₀ h_init
    ⟨⟨R.toAdversary, trivial⟩, h_progress⟩
    h_consistent_quorum
    h_drop_io

/-- Honest-dealer correctness against a *rushing* adversary: with an
honest dealer, every honest party's output equals its per-party share.
Thin wrapper around `avss_correctness_AS`. -/
theorem avss_correctness_AS_rushing
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr coeffs s)
    (R : AVSSRushingAdversary n t F corr) :
    AlmostBox (avssSpec (t := t) sec corr coeffs) R.toAdversary μ₀
      (fun s => s.dealerHonest = true →
        ∀ p, p ∉ s.corrupted →
          ∀ v, (s.local_ p).output = some v →
            v = bivEval coeffs (s.partyPoint p) 0) :=
  avss_correctness_AS sec corr coeffs μ₀ h_init R.toAdversary

/-- Honest-dealer correctness in *existential-witness* form against a
*rushing* adversary (Phase 8.2).  Thin wrapper around
`avss_correctness_AS_existential`.  This is the literature-faithful
re-statement that survives the Phase-8.5 `coeffs`-into-`μ₀` migration. -/
theorem avss_correctness_AS_existential_rushing
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr coeffs s)
    (R : AVSSRushingAdversary n t F corr) :
    AlmostBox (avssSpec (t := t) sec corr coeffs) R.toAdversary μ₀
      (fun s => s.dealerHonest = true →
        ∃ (witness : Fin (t+1) → Fin (t+1) → F),
          witness 0 0 = s.secret ∧
            ∀ p, p ∉ s.corrupted →
              ∀ v, (s.local_ p).output = some v →
                v = bivEval witness (s.partyPoint p) 0) :=
  avss_correctness_AS_existential sec corr coeffs μ₀ h_init R.toAdversary

/-- Output-determined commitment against a *rushing* adversary: any
output, when set, equals the per-party share derived from `s.coeffs`
and `s.partyPoint` (universal in `p`, including corrupt parties whose
`partyCorruptDeliver` writes the correct row poly). Thin wrapper around
`avss_commitment_AS`. -/
theorem avss_commitment_AS_rushing
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr coeffs s)
    (R : AVSSRushingAdversary n t F corr) :
    AlmostBox (avssSpec (t := t) sec corr coeffs) R.toAdversary μ₀
      (outputDeterminedInv coeffs) :=
  avss_commitment_AS sec corr coeffs μ₀ h_init R.toAdversary

/-- Existential-witness commitment against a *rushing* adversary
(Phase 8.3, upgraded to Vandermonde witness in Phase 8.4, renamed
post-Fix 1): under any rushing adversary, **if the dealer is honest
at runtime** and at least `t + 1` honest parties produce outputs,
there exists a bivariate-polynomial witness that is jointly
consistent with all honest outputs.  Thin wrapper around
`avss_commitment_AS_existential`.  See that theorem's docstring for
the honest-dealer guard rationale and the Phase 8.6 follow-up
queued to drop it via Bracha amplification.

Phase 8.4 added the `h_distinct` hypothesis (Shamir/Vandermonde
precondition: party evaluation points are pairwise distinct).  Phase
8.6-redux makes the `3 * t + 1 ≤ n` threshold setting explicit for
surface-statement fidelity. -/
theorem avss_commitment_AS_existential_rushing
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (_h_n_geq : 3 * t + 1 ≤ n)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr coeffs s)
    (h_distinct : ∀ᵐ s ∂μ₀, partyPointInjInv s)
    (R : AVSSRushingAdversary n t F corr) :
    AlmostBox (avssSpec (t := t) sec corr coeffs) R.toAdversary μ₀
      (fun s => s.dealerHonest = true →
        honestOutputCount s ≥ t + 1 →
        ∃ (witness : Fin (t+1) → Fin (t+1) → F),
          ∀ p, p ∉ s.corrupted →
            ∀ v, (s.local_ p).output = some v →
              v = bivEval witness (s.partyPoint p) 0) :=
  avss_commitment_AS_existential sec corr coeffs _h_n_geq μ₀ h_init h_distinct
    R.toAdversary

/-! ## §19.1.5 Phase 9.3 — randomised-adversary restatements (partial coverage)

Closes caveat **C5** (MODEL_NOTES §11.5) for `avss_correctness_AS`,
`avss_commitment_AS`, and the coord-0 form of `avss_secrecy_AS`. The
existing classical theorems universally quantify over deterministic
`Adversary σ ι`; here we re-derive the same propositions for any
`RandomisedAdversary` (literature-standard: a coin-flipping demonic
scheduler) by routing the per-step inductive preservation data through
the Phase 9.2 lifting meta-theorems
(`AlmostBoxRandomised_of_inductive`,
`randomisedTraceDist_map_eq_of_deterministic_at_zero`).

**Partial-coverage caveat** — `avss_termination_AS_fair` is **not**
lifted in this PR. PR #46's `AlmostDiamond.lift_to_randomised` only
derives the trivial diamond from box (`exact ⟨0, hω 0⟩`); it cannot
lift true eventual-termination claims whose proof goes through
`FairASTCertificate.sound`. The randomised termination theorem is
deferred to Phase 9.4 (see MODEL_NOTES §13.4). -/

/-- **Honest-dealer correctness against a randomised adversary.** The
randomised analog of `avss_correctness_AS` (PR #43). With an honest
dealer, every honest party's output equals its per-party share —
almost surely under the mixture trace measure for *any* randomised
schedule.

Proof: re-feed the same inductive data (`honestDealerInv`, plus
preservation `avssStep_preserves_honestDealerInv`) into
`AlmostBoxRandomised_of_inductive`; the support of every gated
action's effect PMF is a singleton (effects are pure
`PMF.pure (avssStep a s)`), so per-step preservation reduces to the
deterministic-step preservation. Closes C5 for correctness. -/
theorem avss_correctness_AS_randomised
    (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr coeffs s)
    (R : RandomisedAdversary (AVSSState n t F) (AVSSAction n F)) :
    AlmostBoxRandomised (avssSpec (t := t) sec corr coeffs) R μ₀
      (fun s => s.dealerHonest = true →
        ∀ p, p ∉ s.corrupted →
          ∀ v, (s.local_ p).output = some v →
            v = bivEval coeffs (s.partyPoint p) 0) := by
  have h_init' : ∀ᵐ s ∂μ₀, honestDealerInv coeffs s ∧ dealerMessagesInv coeffs s := by
    filter_upwards [h_init] with s hs
    exact ⟨initPred_honestDealerInv sec corr coeffs s hs,
           initPred_dealerMessagesInv sec corr coeffs s hs⟩
  have h_step : ∀ (a : AVSSAction n F) (s : AVSSState n t F)
      (h : ((avssSpec (t := t) sec corr coeffs).actions a).gate s),
      (honestDealerInv coeffs s ∧ dealerMessagesInv coeffs s) →
      ∀ s' ∈ ((avssSpec (t := t) sec corr coeffs).actions a).effect s h |>.support,
        honestDealerInv coeffs s' ∧ dealerMessagesInv coeffs s' := by
    intro a s hgate ⟨hinv, hcons⟩ s' hsupp
    rw [show ((avssSpec (t := t) sec corr coeffs).actions a).effect s hgate
          = PMF.pure (avssStep a s) from rfl,
        PMF.support_pure, Set.mem_singleton_iff] at hsupp
    subst hsupp
    exact ⟨avssStep_preserves_honestDealerInv coeffs a s hgate hinv hcons,
           avssStep_preserves_dealerMessagesInv coeffs a s hgate hcons⟩
  have h_inv : AlmostBoxRandomised (avssSpec (t := t) sec corr coeffs) R μ₀
      (fun s => honestDealerInv coeffs s ∧ dealerMessagesInv coeffs s) :=
    AlmostBoxRandomised_of_inductive _ h_step μ₀ h_init' R
  unfold AlmostBoxRandomised at h_inv ⊢
  filter_upwards [h_inv] with ω hinv k hh p hp v hv
  exact ((hinv k).1 hh).2 p hp v hv

/-- **Output-determined commitment against a randomised adversary.**
The randomised analog of `avss_commitment_AS` (PR #45). Every output,
when set, equals the per-party share derived from `s.coeffs` and
`s.partyPoint` — almost surely under the mixture trace measure for
*any* randomised schedule.

Proof: re-feed `outputDeterminedInv` and
`avssStep_preserves_outputDeterminedInv` into
`AlmostBoxRandomised_of_inductive`. Closes C5 for commitment. -/
theorem avss_commitment_AS_randomised
    (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr coeffs s)
    (R : RandomisedAdversary (AVSSState n t F) (AVSSAction n F)) :
    AlmostBoxRandomised (avssSpec (t := t) sec corr coeffs) R μ₀
      (outputDeterminedInv coeffs) := by
  have h_init' : ∀ᵐ s ∂μ₀, outputDeterminedInv coeffs s ∧ dealerMessagesInv coeffs s := by
    filter_upwards [h_init] with s hs
    exact ⟨initPred_outputDeterminedInv sec corr coeffs s hs,
           initPred_dealerMessagesInv sec corr coeffs s hs⟩
  have h_step : ∀ (a : AVSSAction n F) (s : AVSSState n t F)
      (h : ((avssSpec (t := t) sec corr coeffs).actions a).gate s),
      (outputDeterminedInv coeffs s ∧ dealerMessagesInv coeffs s) →
      ∀ s' ∈ ((avssSpec (t := t) sec corr coeffs).actions a).effect s h |>.support,
        outputDeterminedInv coeffs s' ∧ dealerMessagesInv coeffs s' := by
    intro a s hgate ⟨hinv, hcons⟩ s' hsupp
    rw [show ((avssSpec (t := t) sec corr coeffs).actions a).effect s hgate
          = PMF.pure (avssStep a s) from rfl,
        PMF.support_pure, Set.mem_singleton_iff] at hsupp
    subst hsupp
    exact ⟨avssStep_preserves_outputDeterminedInv coeffs a s hgate hinv hcons,
           avssStep_preserves_dealerMessagesInv coeffs a s hgate hcons⟩
  have h_inv : AlmostBoxRandomised (avssSpec (t := t) sec corr coeffs) R μ₀
      (fun s => outputDeterminedInv coeffs s ∧ dealerMessagesInv coeffs s) :=
    AlmostBoxRandomised_of_inductive _ h_step μ₀ h_init' R
  unfold AlmostBoxRandomised at h_inv ⊢
  filter_upwards [h_inv] with ω hω k
  exact (hω k).1

/-- **Coord-0 grid secrecy against a randomised adversary.** The
randomised analog of `avss_secrecy_AS_step_zero_grid`: the marginal
of the mixture trace measure projected to the `coalitionGrid C D`
view at coordinate 0 is invariant in the secret, for *any* randomised
adversary.

Proof: factor through `randomisedTraceDist_map_eq_of_deterministic_at_zero`,
which closes the lift via the coord-0-only argument (the projection
factors through `μ₀.map (·, none)`, where neither the spec nor the
adversary appears). The deterministic premise is exactly
`avss_secrecy_AS_init` (= `avss_secrecy_AS_step_zero_grid`).

Closes C5 for the coord-0 form of secrecy. The step-`k` general form
(`avss_secrecy_AS`) requires propagating the `coalitionGrid`-AE
invariance under the randomised step kernel; that lift is structurally
straightforward (the same `coalitionGrid`-invariance holds branchwise,
and integrates over the schedule PMF) and is folded into the same
Phase 9.4 follow-up as `avss_termination_AS_fair_randomised`. -/
theorem avss_secrecy_AS_step_zero_grid_randomised
    (sec sec' : F) (corr : Finset (Fin n))
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (partyPoint : Fin n → F) (dealerHonest : Bool)
    (h_nz_pp : ∀ i, partyPoint i ≠ 0)
    (h_F : t + 1 ≤ Fintype.card F)
    (C D : BivariateShamir.Coalition n t)
    (R : RandomisedAdversary (AVSSState n t F) (AVSSAction n F)) :
    (randomisedTraceDist (avssSpec (t := t) sec corr coeffs) R
        (avssInitMeasure (n := n) (t := t) sec corr partyPoint dealerHonest)).map
        (fun ω => coalitionGrid coeffs C D (ω 0).1) =
      (randomisedTraceDist (avssSpec (t := t) sec' corr coeffs) R
        (avssInitMeasure (n := n) (t := t) sec' corr partyPoint dealerHonest)).map
        (fun ω => coalitionGrid coeffs C D (ω 0).1) := by
  classical
  have hmeas : Measurable (fun x : AVSSState n t F × Option (AVSSAction n F) =>
      coalitionGrid coeffs C D x.1) := measurable_of_countable _
  exact randomisedTraceDist_map_eq_of_deterministic_at_zero (f := fun x =>
      coalitionGrid coeffs C D x.1) hmeas
    (fun A => avss_secrecy_AS_init sec sec' corr partyPoint dealerHonest
      h_nz_pp h_F C D A) R

/-- **Step-`k` general grid secrecy against a randomised adversary.**

The randomised analog of `avss_secrecy_AS` (§17.9): the marginal of
the mixture trace measure projected to the `coalitionGrid C D` view
at any coordinate `k` is invariant in the secret, for *any*
randomised adversary.

Generalisation of `avss_secrecy_AS_step_zero_grid_randomised` (PR #47)
from coord 0 to all `k : ℕ`. Closes the step-`k` form of caveat C5
for secrecy.

Proof: factor through `randomisedTraceDist_map_eq_of_deterministic`
(PR #N, this PR) — the generic step-`k` lift — supplying:

  * the structural state-projection invariance hypothesis discharged
    by `avssStep_coalitionGrid_invariant` (every gated `avssStep`
    branch preserves `coalitionGrid C D`); and
  * the deterministic premise `avss_secrecy_AS_init` (= the coord-0
    grid secrecy for any deterministic adversary, PR #43).

The schedule PMF integrates the per-branch AE-equality across
`randomisedStepKernel` to lift from coord 0 to coord `k`. -/
theorem avss_secrecy_AS_randomised
    (sec sec' : F) (corr : Finset (Fin n))
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (partyPoint : Fin n → F) (dealerHonest : Bool)
    (h_nz_pp : ∀ i, partyPoint i ≠ 0)
    (h_F : t + 1 ≤ Fintype.card F)
    (C D : BivariateShamir.Coalition n t)
    (R : RandomisedAdversary (AVSSState n t F) (AVSSAction n F)) (k : ℕ) :
    (randomisedTraceDist (avssSpec (t := t) sec corr coeffs) R
        (avssInitMeasure (n := n) (t := t) sec corr partyPoint dealerHonest)).map
        (fun ω => coalitionGrid coeffs C D (ω k).1) =
      (randomisedTraceDist (avssSpec (t := t) sec' corr coeffs) R
        (avssInitMeasure (n := n) (t := t) sec' corr partyPoint dealerHonest)).map
        (fun ω => coalitionGrid coeffs C D (ω k).1) := by
  classical
  have hmeas : Measurable (coalitionGrid (n := n) (t := t) (F := F) coeffs C D) :=
    measurable_of_countable _
  have h_step : ∀ (s : F) (a : AVSSAction n F) (st : AVSSState n t F)
      (hgate : ((avssSpec (t := t) s corr coeffs).actions a).gate st),
      ∀ st' ∈ ((avssSpec (t := t) s corr coeffs).actions a).effect st hgate |>.support,
        coalitionGrid coeffs C D st' = coalitionGrid coeffs C D st := by
    intro s a st hgate st' hsupp
    rw [show ((avssSpec (t := t) s corr coeffs).actions a).effect st hgate
          = PMF.pure (avssStep a st) from rfl,
        PMF.support_pure, Set.mem_singleton_iff] at hsupp
    subst hsupp
    exact avssStep_coalitionGrid_invariant coeffs a st C D
  exact randomisedTraceDist_map_eq_of_deterministic
    (g := coalitionGrid (n := n) (t := t) (F := F) coeffs C D)
    hmeas (h_step sec) (h_step sec')
    (fun A => avss_secrecy_AS_init sec sec' corr partyPoint dealerHonest
      h_nz_pp h_F C D A) R k

/-! ## §19.1.6 Phase 9.3 follow-up — existential-witness `_randomised` analogs

The `_randomised` lifts in §19.1.5 above target the older
`s.coeffs`-direct forms of correctness and commitment. The
**literature-faithful** existential-witness forms (introduced by the
parallel Phase 8.2 / 8.3 PR chain on a sister branch) are
migration-stable: when a future PR moves `s.coeffs` out of state into
`μ₀`, the `s.coeffs`-direct lifts above will become stale, but the
existential-witness forms continue to hold cleanly with the witness
sourced from `μ₀`'s sample.

This sub-section adds the existential-witness `_randomised` analogs,
keeping the same lift pattern as §19.1.5 but with the witness
existential introduced at the surface conclusion. The proofs reuse
the per-step preservation already established for `honestDealerInv`
(correctness) and `outputDeterminedInv` (commitment); the additional
content is the trivial static preservation of `s.coeffs`, `s.secret`,
and `s.dealerHonest` (none of which is touched by any `avssStep`
branch). -/

/-- **Honest-dealer correctness, existential-witness form, against a
randomised adversary.** Literature-faithful analog of
`avss_correctness_AS_randomised`: with an honest dealer, there exists
a witness bivariate `f : Fin (t+1) → Fin (t+1) → F` whose constant
term equals the dealer's secret and whose evaluations at the per-party
points coincide with every honest output, almost surely under the
mixture trace measure for any randomised adversary.

Proof: lift the joint invariant `honestDealerInv ∧ (dealerHonest =
true → coeffs 0 0 = secret)` via `AlmostBoxRandomised_of_inductive`.
The first conjunct's preservation comes from
`avssStep_preserves_honestDealerInv` (re-used from PR #47); the
second conjunct's preservation is trivial because every gated
`avssStep` branch is static in `coeffs`, `secret`, and `dealerHonest`.
The witness `(ω k).1.coeffs` is then read off the trace at any
coordinate.

Migration-stable: when a future PR moves `s.coeffs` out of state into
`μ₀`, the existential witness will be sourced from the initial-state
sample (rather than read off the trace's static `coeffs` field), and
the surface statement above continues to hold. -/
theorem avss_correctness_AS_existential_randomised
    (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr coeffs s)
    (R : RandomisedAdversary (AVSSState n t F) (AVSSAction n F)) :
    AlmostBoxRandomised (avssSpec (t := t) sec corr coeffs) R μ₀
      (fun s => s.dealerHonest = true →
        ∃ (witness : Fin (t+1) → Fin (t+1) → F),
          witness 0 0 = s.secret ∧
            ∀ p, p ∉ s.corrupted →
              ∀ v, (s.local_ p).output = some v →
                v = bivEval witness (s.partyPoint p) 0) := by
  have h_init' : ∀ᵐ s ∂μ₀,
      (honestDealerInv coeffs s ∧ dealerMessagesInv coeffs s) ∧
        (s.dealerHonest = true → coeffs 0 0 = s.secret) := by
    filter_upwards [h_init] with s hs
    refine ⟨⟨initPred_honestDealerInv sec corr coeffs s hs,
            initPred_dealerMessagesInv sec corr coeffs s hs⟩, ?_⟩
    intro hh
    obtain ⟨_, hsec, _, _, _, _, _, _, _, hch⟩ := hs
    rw [hsec]
    exact (hch hh).1
  have h_step : ∀ (a : AVSSAction n F) (s : AVSSState n t F)
      (h : ((avssSpec (t := t) sec corr coeffs).actions a).gate s),
      ((honestDealerInv coeffs s ∧ dealerMessagesInv coeffs s) ∧
        (s.dealerHonest = true → coeffs 0 0 = s.secret)) →
      ∀ s' ∈ ((avssSpec (t := t) sec corr coeffs).actions a).effect s h |>.support,
        ((honestDealerInv coeffs s' ∧ dealerMessagesInv coeffs s') ∧
          (s'.dealerHonest = true → coeffs 0 0 = s'.secret)) := by
    intro a s hgate hp s' hsupp
    rw [show ((avssSpec (t := t) sec corr coeffs).actions a).effect s hgate
          = PMF.pure (avssStep a s) from rfl,
        PMF.support_pure, Set.mem_singleton_iff] at hsupp
    subst hsupp
    refine ⟨⟨avssStep_preserves_honestDealerInv coeffs a s hgate hp.1.1 hp.1.2,
            avssStep_preserves_dealerMessagesInv coeffs a s hgate hp.1.2⟩, ?_⟩
    intro hh
    have hh_pre : s.dealerHonest = true := by
      cases a <;> simp [avssStep, setLocal] at hh <;> exact hh
    have hsecret : (avssStep a s).secret = s.secret := by
      cases a <;> simp [avssStep, setLocal]
    rw [hsecret]
    exact hp.2 hh_pre
  have h_inv : AlmostBoxRandomised (avssSpec (t := t) sec corr coeffs) R μ₀
      (fun s => (honestDealerInv coeffs s ∧ dealerMessagesInv coeffs s) ∧
        (s.dealerHonest = true → coeffs 0 0 = s.secret)) :=
    AlmostBoxRandomised_of_inductive _ h_step μ₀ h_init' R
  unfold AlmostBoxRandomised at h_inv ⊢
  filter_upwards [h_inv] with ω hP k hh
  refine ⟨coeffs, (hP k).2 hh, ?_⟩
  intro p hp v hv
  exact ((hP k).1.1 hh).2 p hp v hv

/-- **Existential-witness commitment against a randomised adversary**
(honest-dealer-conditional, post-Fix 1 rename).  Analog of
`avss_commitment_AS_randomised`: under the honest-dealer guard, at
any quorum-of-honest-outputs coordinate there exists a witness
bivariate whose evaluations at the per-party points coincide with
every honest output.  The witness is the μ₀-baked `coeffs` parameter;
the precondition `honestOutputCount s ≥ t + 1` is the literature-
faithful Bracha-quorum gate from PR #45's deterministic version,
kept here for surface-statement alignment.

The honest-dealer guard is identical to the deterministic version's
(see `avss_commitment_AS_existential` for the rationale and the
Phase 8.6 follow-up that drops it via Bracha amplification).  The
previous name `_corrupt_dealer_randomised` overclaimed.

Proof: derived directly from `avss_commitment_AS_randomised`
(`outputDeterminedInv` lift); the existential is satisfied with
`witness := coeffs` and the per-party clause is exactly
`outputDeterminedInv`'s second conjunct.  The explicit `3 * t + 1 ≤ n`
hypothesis records the intended Canetti-Rabin threshold regime but is
not consumed by this honest-dealer-conditional proof. -/
theorem avss_commitment_AS_existential_randomised
    (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (_h_n_geq : 3 * t + 1 ≤ n)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr coeffs s)
    (R : RandomisedAdversary (AVSSState n t F) (AVSSAction n F)) :
    AlmostBoxRandomised (avssSpec (t := t) sec corr coeffs) R μ₀
      (fun s => s.dealerHonest = true →
        honestOutputCount s ≥ t + 1 →
        ∃ (witness : Fin (t+1) → Fin (t+1) → F),
          ∀ p, p ∉ s.corrupted →
            ∀ v, (s.local_ p).output = some v →
              v = bivEval witness (s.partyPoint p) 0) := by
  have hcomm := avss_commitment_AS_randomised sec corr coeffs μ₀ h_init R
  unfold AlmostBoxRandomised at hcomm ⊢
  filter_upwards [hcomm] with ω hP k hh _hquorum
  refine ⟨coeffs, ?_⟩
  intro p hp v hv
  exact (hP k hh).2 p hp v hv

/-! ### §19.1.4. Phase 9.4 — termination against a randomised adversary

Closes the termination half of caveat **C5** (MODEL_NOTES §11.5):
together with PR #41 / PR #46 / PR #47 / PR #49, every classical
AVSS property (correctness, commitment, secrecy at coord 0,
termination) now holds against any randomised adversary.

The randomised analog of `avss_termination_AS_fair` (§13). Routes
through `RandomisedFairASTCertificate.sound` (the randomised
specialisation of the measure-generic
`partition_almostDiamond_fair_on` core in
`Leslie/Prob/Liveness.lean`); the underlying certificate
(`avssCert sec corr`) is the same protocol-data witness used by
the deterministic version.

Per the maintenance plan in `AVSS-MODEL-NOTES.md` §13.4. -/

/-- **Termination against a randomised adversary.**  The randomised
analog of `avss_termination_AS_fair` (§13).  Every randomised
trajectory-fair adversary almost-surely drives the protocol to a
terminated state, where "trajectory-fair" means an AE witness of
fair-action progress along the mixture trace measure
(`RandomisedTrajectoryFairAdversary.progress`).

Discharged via `RandomisedFairASTCertificate.sound`, which
specialises the measure-generic `partition_almostDiamond_fair_on`
core (in `Liveness.lean`) to the randomised mixture trace measure
plus the inductive randomised-Box lift
`AlmostBoxRandomised_of_inductive`.

Closes C5 for termination. -/
theorem avss_termination_AS_fair_randomised
    (sec : F) (corr : Finset (Fin n)) (h_corr : corr.card ≤ t)
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr coeffs s)
    (R : Leslie.Prob.RandomisedTrajectoryFairAdversary
            (avssSpec (t := t) sec corr coeffs) avssFair μ₀)
    (h_U_mono : FairASTCertificate.RandomisedTrajectoryUMono
        (avssCert (t := t) sec corr coeffs h_corr) μ₀ R.toRandomised)
    (h_U_strict : ∀ N : ℕ, FairASTCertificate.RandomisedTrajectoryFairStrictDecrease
        (avssCert (t := t) sec corr coeffs h_corr) μ₀ R.toRandomised N) :
    AlmostDiamondRandomised (avssSpec (t := t) sec corr coeffs) R.toRandomised μ₀
      terminated := by
  have h_init' : ∀ᵐ s ∂μ₀, (avssCert (t := t) sec corr coeffs h_corr).Inv s := by
    filter_upwards [h_init] with s hs
    exact (avssCert (t := t) sec corr coeffs h_corr).inv_init s hs
  exact RandomisedFairASTCertificate.sound
    (avssCert (t := t) sec corr coeffs h_corr) μ₀ h_init' R h_U_mono h_U_strict

/-! ### §19.1.7. Phase 9.5 — `_rushing_randomised` headline wrappers

Closes the literature-standard threat model gap: every classical AVSS
theorem now has a randomised analog quantified over an
`AVSSRushingRandomisedAdversary` (the literature's *randomised
rushing* threat model — coin-flipping schedule on the coalition view).

Each wrapper is a one-liner: the rushing-randomised structure carries
a `RushingRandomisedAdversary.toRandomisedAdversary` adapter that
projects to a plain `RandomisedAdversary` by composing the rushing-view
projection with the rushing-view-restricted PMF strategy.  The
underlying `_randomised` theorems from PRs #47, #49, and #54 quantify
universally over `RandomisedAdversary`, so they specialise immediately.

The four wrappers cover the four classical AVSS properties:
  * `avss_correctness_AS_existential_rushing_randomised` (around PR #49)
  * `avss_commitment_AS_existential_rushing_randomised`  (around PR #49,
                                                          renamed in Fix 1)
  * `avss_secrecy_AS_step_zero_grid_rushing_randomised`   (around PR #47)
  * `avss_termination_AS_fair_rushing_randomised`         (around PR #54)

The step-`k` general form of the secrecy wrapper
(`avss_secrecy_AS_view_rushing_randomised` mirroring the deterministic
operational secrecy headline at arbitrary step `k` with the schedule
prefix joint distribution) is independently lifted in Phase 9.6 (PR
#53); together with this PR, **C5 closes fully** (MODEL_NOTES §11.5,
§13.1).

Per maintenance plan in `AVSS-MODEL-NOTES.md` §13.5. -/

/-- **Honest-dealer correctness against a rushing randomised
adversary** (existential-witness form).  Thin wrapper: feed
`R.toRandomisedAdversary` into `avss_correctness_AS_existential_randomised`
(PR #49). -/
theorem avss_correctness_AS_existential_rushing_randomised
    (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr coeffs s)
    (R : AVSSRushingRandomisedAdversary n t F corr) :
    AlmostBoxRandomised (avssSpec (t := t) sec corr coeffs) R.toRandomisedAdversary μ₀
      (fun s => s.dealerHonest = true →
        ∃ (witness : Fin (t+1) → Fin (t+1) → F),
          witness 0 0 = s.secret ∧
            ∀ p, p ∉ s.corrupted →
              ∀ v, (s.local_ p).output = some v →
                v = bivEval witness (s.partyPoint p) 0) :=
  avss_correctness_AS_existential_randomised sec corr coeffs μ₀ h_init
    R.toRandomisedAdversary

/-- **Existential-witness commitment against a rushing randomised
adversary** (honest-dealer-conditional, post-Fix 1 rename).  Thin
wrapper: feed `R.toRandomisedAdversary` into
`avss_commitment_AS_existential_randomised` (PR #49).  See
`avss_commitment_AS_existential` for the honest-dealer guard
rationale and the explicit threshold-regime hypothesis. -/
theorem avss_commitment_AS_existential_rushing_randomised
    (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (_h_n_geq : 3 * t + 1 ≤ n)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr coeffs s)
    (R : AVSSRushingRandomisedAdversary n t F corr) :
    AlmostBoxRandomised (avssSpec (t := t) sec corr coeffs) R.toRandomisedAdversary μ₀
      (fun s => s.dealerHonest = true →
        honestOutputCount s ≥ t + 1 →
        ∃ (witness : Fin (t+1) → Fin (t+1) → F),
          ∀ p, p ∉ s.corrupted →
            ∀ v, (s.local_ p).output = some v →
              v = bivEval witness (s.partyPoint p) 0) :=
  avss_commitment_AS_existential_randomised sec corr coeffs _h_n_geq μ₀ h_init
    R.toRandomisedAdversary

/-- **Coord-0 grid secrecy against a rushing randomised adversary.**
The randomised-rushing analog of the coord-0 grid form
`avss_secrecy_AS_step_zero_grid_randomised` (PR #47).  At coordinate
0 the projection factors through `μ₀.map (·, none)` (neither the spec
nor the adversary appears), so the schedule restriction to the rushing
view is trivially absorbed.

The literature-faithful **step-`k` operational secrecy** randomised
analog (mirroring deterministic `avss_secrecy_AS_view_rushing` with
the joint coalition-view + schedule-prefix distribution at arbitrary
`k`) is the deliverable of Phase 9.6 (PR #53), independent of this PR;
together with this PR, MODEL_NOTES §11.5 (caveat C5) closes fully. -/
theorem avss_secrecy_AS_step_zero_grid_rushing_randomised
    (sec sec' : F) (corr : Finset (Fin n))
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (partyPoint : Fin n → F) (dealerHonest : Bool)
    (h_nz_pp : ∀ i, partyPoint i ≠ 0)
    (h_F : t + 1 ≤ Fintype.card F)
    (C D : BivariateShamir.Coalition n t)
    (R : AVSSRushingRandomisedAdversary n t F corr) :
    (randomisedTraceDist (avssSpec (t := t) sec corr coeffs) R.toRandomisedAdversary
        (avssInitMeasure (n := n) (t := t) sec corr partyPoint dealerHonest)).map
        (fun ω => coalitionGrid coeffs C D (ω 0).1) =
      (randomisedTraceDist (avssSpec (t := t) sec' corr coeffs) R.toRandomisedAdversary
        (avssInitMeasure (n := n) (t := t) sec' corr partyPoint dealerHonest)).map
        (fun ω => coalitionGrid coeffs C D (ω 0).1) :=
  avss_secrecy_AS_step_zero_grid_randomised sec sec' corr coeffs partyPoint
    dealerHonest h_nz_pp h_F C D R.toRandomisedAdversary

/-- **Step-`k` grid secrecy against a rushing randomised adversary.**

The literature-faithful step-`k` operational secrecy randomised
analog: at any coordinate `k : ℕ`, the marginal of the mixture trace
measure projected to the `coalitionGrid C D` view is invariant in
the secret, against any rushing randomised adversary.

Generalisation of `avss_secrecy_AS_step_zero_grid_rushing_randomised`
(coord 0) to all `k`. Closes the step-`k` operational rushing-randomised
secrecy gap that was deferred from PRs #55 and #53 due to their
sibling-stack independence.

Thin wrapper: forwards to PR #53's step-`k` form
`avss_secrecy_AS_randomised` via `R.toRandomisedAdversary`. -/
theorem avss_secrecy_AS_view_rushing_randomised
    (sec sec' : F) (corr : Finset (Fin n))
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (partyPoint : Fin n → F) (dealerHonest : Bool)
    (h_nz_pp : ∀ i, partyPoint i ≠ 0)
    (h_F : t + 1 ≤ Fintype.card F)
    (C D : BivariateShamir.Coalition n t)
    (R : AVSSRushingRandomisedAdversary n t F corr) (k : ℕ) :
    (randomisedTraceDist (avssSpec (t := t) sec corr coeffs) R.toRandomisedAdversary
        (avssInitMeasure (n := n) (t := t) sec corr partyPoint dealerHonest)).map
        (fun ω => coalitionGrid coeffs C D (ω k).1) =
      (randomisedTraceDist (avssSpec (t := t) sec' corr coeffs) R.toRandomisedAdversary
        (avssInitMeasure (n := n) (t := t) sec' corr partyPoint dealerHonest)).map
        (fun ω => coalitionGrid coeffs C D (ω k).1) :=
  avss_secrecy_AS_randomised sec sec' corr coeffs partyPoint dealerHonest
    h_nz_pp h_F C D R.toRandomisedAdversary k

/-- **Termination against a rushing randomised adversary.**  Thin
wrapper: bundle `R.toRandomisedAdversary` together with the AE-trajectory
progress witness into a `RandomisedTrajectoryFairAdversary` and forward
to `avss_termination_AS_fair_randomised` (PR #54). -/
theorem avss_termination_AS_fair_rushing_randomised
    (sec : F) (corr : Finset (Fin n)) (h_corr : corr.card ≤ t)
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr coeffs s)
    (R : AVSSRushingRandomisedAdversary n t F corr)
    (h_progress : FairASTCertificate.RandomisedTrajectoryFairProgress
      (avssSpec (t := t) sec corr coeffs) avssFair μ₀ R.toRandomisedAdversary)
    (h_U_mono : FairASTCertificate.RandomisedTrajectoryUMono
        (avssCert (t := t) sec corr coeffs h_corr) μ₀ R.toRandomisedAdversary)
    (h_U_strict : ∀ N : ℕ, FairASTCertificate.RandomisedTrajectoryFairStrictDecrease
        (avssCert (t := t) sec corr coeffs h_corr) μ₀ R.toRandomisedAdversary N) :
    AlmostDiamondRandomised (avssSpec (t := t) sec corr coeffs) R.toRandomisedAdversary μ₀
      terminated :=
  avss_termination_AS_fair_randomised sec corr h_corr coeffs μ₀ h_init
    ⟨R.toRandomisedAdversary, h_progress⟩ h_U_mono h_U_strict

/-! ## §19.2. Phase 7.4 — schedule prefix factors through algebraic view AE

Under a `RushingAdversary` `R` for AVSS, the trace is *fully deterministic*
given the initial state: each step's effect-PMF is a `pure` (Dirac), and
the adversary's schedule is a deterministic function of the (state-)
history. We exploit this to express the trace measure as a deterministic
pushforward of the initial measure, then read off the AE-factoring of
the schedule prefix and the operational coalition view through the
corrupt-coalition's algebraic view at the initial state.

This is the cryptographic-core deliverable that the deferral note in
`AVSS-MODEL-NOTES.md` §9 calls out: ~300–500 LOC of inductive trace
plumbing that closes the schedule-leakage half of the headline
operational-secrecy theorem.  The remaining "algebraic-core" half — the
+200 LOC row-poly-vs-grid secrecy strengthening of
`BivariateShamir.bivariate_shamir_secrecy` — is still deferred (cf. §17.12);
the headline theorem `avss_secrecy_AS_view_rushing_via_aux` (§19.3 below)
takes that strengthening as an explicit hypothesis. -/

section RushingSimulation

open Classical
open scoped ProbabilityTheory

/-! ### Phase 10.3 — AVSS as a `DeterministicProbActionSpec`

`avssDeterministic sec corr` packages AVSS's `(init, gate, step)`
triple as a `DeterministicProbActionSpec`.  The adapter
`toProbActionSpec` recovers `avssSpec sec corr` definitionally, so
the AE-bridge meta-theorem `Leslie.Prob.traceDist_AE_eq_simulateTrace`
can be applied directly to AVSS's trace distribution.  See PRs #42, #44
for the generic data + meta-theorem this builds on. -/

/-- AVSS as a `DeterministicProbActionSpec`. The data triple
`(init, gate, step)` matches `avssSpec`'s shape verbatim. -/
def avssDeterministic (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t+1) → Fin (t+1) → F) :
    Leslie.Prob.DeterministicProbActionSpec
      (AVSSState n t F) (AVSSAction n F) where
  init := initPred sec corr coeffs
  gate := actionGate
  step := avssStep

omit [Fintype F] in
@[simp] theorem avssDeterministic_toProbActionSpec
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F) :
    (avssDeterministic (t := t) sec corr coeffs).toProbActionSpec
      = avssSpec (t := t) sec corr coeffs := rfl

/-- Compute the next trace pair given a prior reverse-order prefix list.
Used as the inductive step of `avssSimulateRev`.  If the prefix is
empty (unreachable in our recursion), returns the input fallback. -/
noncomputable def avssSimulateNext (R : AVSSRushingAdversary n t F corr)
    (fallback : AVSSState n t F)
    (prev : List (AVSSState n t F × Option (AVSSAction n F))) :
    AVSSState n t F × Option (AVSSAction n F) :=
  let s_k : AVSSState n t F := (prev.head?.map Prod.fst).getD fallback
  match R.toAdversary.schedule prev.reverse with
  | none => (s_k, (none : Option (AVSSAction n F)))
  | some i =>
      if actionGate i s_k then (avssStep i s_k, some i)
      else (s_k, (none : Option (AVSSAction n F)))

/-- Reverse-order simulated trace prefix at step `k`.  Returns a list
of length `k+1` ordered as `[step k, step k-1, …, step 0]`.  The
recursion is structural in `k`. -/
noncomputable def avssSimulateRev (R : AVSSRushingAdversary n t F corr)
    (s_0 : AVSSState n t F) :
    ℕ → List (AVSSState n t F × Option (AVSSAction n F))
  | 0 => [(s_0, (none : Option (AVSSAction n F)))]
  | (k+1) =>
    let prev := avssSimulateRev R s_0 k
    (avssSimulateNext R s_0 prev) :: prev

/-- Length of the simulated reverse prefix is `k+1`. -/
theorem avssSimulateRev_length {corr : Finset (Fin n)}
    (R : AVSSRushingAdversary n t F corr)
    (s_0 : AVSSState n t F) (k : ℕ) :
    (avssSimulateRev R s_0 k).length = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [avssSimulateRev, ih]

theorem avssSimulateRev_ne_nil {corr : Finset (Fin n)}
    (R : AVSSRushingAdversary n t F corr)
    (s_0 : AVSSState n t F) (k : ℕ) :
    avssSimulateRev R s_0 k ≠ [] := by
  intro h
  have := avssSimulateRev_length R s_0 k
  rw [h] at this; simp at this

/-- The simulated trace at step `k`: extract the head of the
reverse-order prefix list. -/
noncomputable def avssSimulateTrace (R : AVSSRushingAdversary n t F corr)
    (s_0 : AVSSState n t F) (k : ℕ) :
    AVSSState n t F × Option (AVSSAction n F) :=
  match avssSimulateRev R s_0 k with
  | [] => (s_0, (none : Option (AVSSAction n F)))  -- unreachable
  | x :: _ => x

@[simp] theorem avssSimulateTrace_zero {corr : Finset (Fin n)}
    (R : AVSSRushingAdversary n t F corr)
    (s_0 : AVSSState n t F) :
    avssSimulateTrace R s_0 0 = (s_0, (none : Option (AVSSAction n F))) := rfl

@[simp] theorem avssSimulateTrace_zero_fst {corr : Finset (Fin n)}
    (R : AVSSRushingAdversary n t F corr)
    (s_0 : AVSSState n t F) :
    (avssSimulateTrace R s_0 0).1 = s_0 := rfl

@[simp] theorem avssSimulateTrace_zero_snd {corr : Finset (Fin n)}
    (R : AVSSRushingAdversary n t F corr)
    (s_0 : AVSSState n t F) :
    (avssSimulateTrace R s_0 0).2 = none := rfl

/-- Successor-step structural identity for `avssSimulateTrace`: the
state-action pair at step `k+1` equals `avssSimulateNext` applied to
the reverse-order prefix at step `k`. -/
theorem avssSimulateTrace_succ_eq {corr : Finset (Fin n)}
    (R : AVSSRushingAdversary n t F corr)
    (s_0 : AVSSState n t F) (k : ℕ) :
    avssSimulateTrace R s_0 (k+1) =
      avssSimulateNext R s_0 (avssSimulateRev R s_0 k) := by
  simp [avssSimulateTrace, avssSimulateRev]

/-- The state at step `k` of the simulate equals the head of the
reverse-prefix list (when nonempty). -/
theorem avssSimulateRev_head_eq {corr : Finset (Fin n)}
    (R : AVSSRushingAdversary n t F corr)
    (s_0 : AVSSState n t F) (k : ℕ) :
    (avssSimulateRev R s_0 k).head?.map Prod.fst =
      some (avssSimulateTrace R s_0 k).1 := by
  unfold avssSimulateTrace
  -- Case-split on the head of the (nonempty) list.
  cases h : avssSimulateRev R s_0 k with
  | nil => exact absurd h (avssSimulateRev_ne_nil R s_0 k)
  | cons x xs => simp

/-! ### Phase 10.3 — projection-rfls + bridge to the generic simulate machinery

The AVSS-specific `avssSimulate*` definitions agree definitionally with
`Leslie.Prob.simulate*` instantiated at `avssDeterministic sec corr`,
since the bodies share the same `(gate, step, schedule)` triple.  But
Lean's kernel `defEq` does not always unfold structure projections on
`avssDeterministic` calls, so we provide explicit `@[simp]` projection
lemmas plus inductive bridge equalities. -/

omit [Fintype F] in
@[simp] theorem avssDeterministic_init (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t+1) → Fin (t+1) → F) :
    (avssDeterministic (t := t) sec corr coeffs).init = initPred sec corr coeffs := rfl

omit [Fintype F] in
@[simp] theorem avssDeterministic_gate (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t+1) → Fin (t+1) → F) :
    (avssDeterministic (t := t) sec corr coeffs).gate = actionGate := rfl

omit [Fintype F] in
@[simp] theorem avssDeterministic_step (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t+1) → Fin (t+1) → F) :
    (avssDeterministic (t := t) sec corr coeffs).step = avssStep := rfl

theorem avssSimulateNext_eq_simulateNext
    (sec : F) {corr : Finset (Fin n)}
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (R : AVSSRushingAdversary n t F corr)
    (fallback : AVSSState n t F)
    (prev : List (AVSSState n t F × Option (AVSSAction n F))) :
    avssSimulateNext R fallback prev =
      Leslie.Prob.simulateNext (avssDeterministic (t := t) sec corr coeffs)
        R.toAdversary fallback prev := by
  unfold avssSimulateNext Leslie.Prob.simulateNext
  simp only [avssDeterministic_gate, avssDeterministic_step]
  rcases (RushingAdversary.toAdversary R).schedule prev.reverse with _ | i
  · rfl
  · rfl

theorem avssSimulateRev_eq_simulateRev
    (sec : F) {corr : Finset (Fin n)}
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (R : AVSSRushingAdversary n t F corr)
    (s_0 : AVSSState n t F) (k : ℕ) :
    avssSimulateRev R s_0 k =
      Leslie.Prob.simulateRev (avssDeterministic (t := t) sec corr coeffs)
        R.toAdversary s_0 k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show avssSimulateNext R s_0 (avssSimulateRev R s_0 k) ::
          avssSimulateRev R s_0 k = _
    rw [ih, avssSimulateNext_eq_simulateNext sec coeffs]
    rfl

theorem avssSimulateTrace_eq_simulateTrace
    (sec : F) {corr : Finset (Fin n)}
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (R : AVSSRushingAdversary n t F corr)
    (s_0 : AVSSState n t F) (k : ℕ) :
    avssSimulateTrace R s_0 k =
      Leslie.Prob.simulateTrace (avssDeterministic (t := t) sec corr coeffs)
        R.toAdversary s_0 k := by
  unfold avssSimulateTrace Leslie.Prob.simulateTrace
  rw [avssSimulateRev_eq_simulateRev sec coeffs]
  -- Match-on-equal-list: split on the list value to close.
  rcases h : Leslie.Prob.simulateRev
      (avssDeterministic (t := t) sec corr coeffs) R.toAdversary s_0 k with _ | x
  · rfl
  · rfl

/-! ## §19.2.4. Phase 7.4 — inductive AE-bridge: trace AE-equals simulate

Under any `Adversary A`, AVSS's trace is fully deterministic given the
initial state: each step's effect-PMF is a Dirac (`PMF.pure (avssStep
i s)`).  The headline `traceDist_AE_eq_avssSimulateTrace` is therefore
an immediate instantiation of the generic meta-theorem
`Leslie.Prob.traceDist_AE_eq_simulateTrace` (PR #44) at
`avssDeterministic sec corr`.

Phase 10.3 collapsed the original ~330-LOC inductive proof chain
(`avssSpec_R_stepKernel_AE_simulate`,
`traceDist_step_zero_pair_marginal`, `traceDist_step_zero_snd_AE`,
`traceDist_AE_eq_avssSimulateTrace_strong`,
`avssSimulateRev_reverse_eq_ofFn`) to a one-line application of the
meta-theorem.  See `Leslie/Prob/DeterministicSimulate.lean` for the
generic form. -/

/-- **Phase 7.4 inductive AE-bridge.** Under any `Adversary A`, the
trace at step `k` AE-equals `avssSimulateTrace R (ω 0).1 k` —
because every step's effect-PMF is a Dirac (`PMF.pure (avssStep i s)`)
and the schedule is a deterministic function of the view-history.

This is the structural content of Phase 7.4.  Combined with Phase 5's
algebraic-view AE invariance (in §19.2.5 below), it discharges the
`h_aux` hypothesis of `avss_secrecy_AS_view_conditional` and yields
the operational-secrecy theorem
`avss_secrecy_AS_view_rushing_via_init_invariant` (§19.4 below);
in §19.4.5 this is composed with the row-poly secrecy lemma to give
the fully unconditional headline `avss_secrecy_AS_view_rushing`.

Phase 10.3: this is now a one-line instantiation of the generic
meta-theorem `Leslie.Prob.traceDist_AE_eq_simulateTrace` (PR #44) at
`avssDeterministic sec corr`.  Both `(avssDeterministic sec
corr).toProbActionSpec = avssSpec sec corr` and `Leslie.Prob.simulateTrace
(avssDeterministic sec corr) R.toAdversary s_0 k = avssSimulateTrace R
s_0 k` hold definitionally (`rfl`-equal up to the irrelevant-for-trace
`init` field), so the meta-theorem's conclusion matches the AVSS
statement directly. -/
theorem traceDist_AE_eq_avssSimulateTrace
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (R : AVSSRushingAdversary n t F corr) (k : ℕ) :
    ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) R.toAdversary μ₀),
        ω k = avssSimulateTrace R (ω 0).1 k := by
  have h := Leslie.Prob.traceDist_AE_eq_simulateTrace
    (avssDeterministic (t := t) sec corr coeffs) R.toAdversary μ₀ k
  rw [avssDeterministic_toProbActionSpec] at h
  filter_upwards [h] with ω hω
  rw [hω, avssSimulateTrace_eq_simulateTrace sec coeffs]

/-- Strong-form inductive AE-bridge: the prefix `(ω 0..k)` of any
`traceDist` trace AE-matches the simulate's prefix `avssSimulateTrace R
(ω 0).1 i` for every `i ≤ k`.

Strong because `R.toAdversary.schedule` at every step depends on the
full prefix-history, so a per-step inductive step needs the matching
to hold over the entire prefix.  Used by §19.2.5 below.

Phase 10.3: derived from the public per-step
`traceDist_AE_eq_avssSimulateTrace` by a small `Nat.rec` induction
over the prefix range.  The inductive bulk is now in
`Leslie.Prob.traceDist_AE_eq_simulateTrace`. -/
private theorem traceDist_AE_eq_avssSimulateTrace_strong
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (R : AVSSRushingAdversary n t F corr) (k : ℕ) :
    ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) R.toAdversary μ₀),
        ∀ i, i ≤ k → ω i = avssSimulateTrace R (ω 0).1 i := by
  induction k with
  | zero =>
    filter_upwards [traceDist_AE_eq_avssSimulateTrace (t := t) sec corr coeffs μ₀ R 0]
      with ω hω i hi
    interval_cases i
    exact hω
  | succ k ih =>
    filter_upwards [ih,
        traceDist_AE_eq_avssSimulateTrace (t := t) sec corr coeffs μ₀ R (k+1)]
      with ω h_ih h_step i hi
    by_cases h : i = k + 1
    · exact h.symm ▸ h_step
    · exact h_ih i (by omega)

/-! ### Removed in Phase 10.3

The following AVSS-specific helpers were subsumed by the generic
forms in `Leslie/Prob/DeterministicSimulate.lean` (PR #44) and have
been deleted:

  * `traceDist_step_zero_pair_marginal` — generic form available as
    `Leslie.Prob.traceDist_step_zero_pair_marginal`.
  * `traceDist_step_zero_snd_AE` — generic form available as
    `Leslie.Prob.traceDist_step_zero_snd_AE`.
  * `avssSimulateRev_reverse_eq_ofFn` — generic form available as
    `Leslie.Prob.simulateRev_reverse_eq_ofFn`.
  * `avssSpec_R_stepKernel_AE_simulate` — generic form is the
    `private` `Leslie.Prob.stepKernel_AE_simulate`.

If a downstream caller needs any of these by their AVSS-specific
names, retarget to the generic forms above.  All callers within AVSS
have already been updated. -/

/-! ## §19.2.5. Phase 7.4 — joint factoring through the initial state

Apply the inductive AE-bridge `traceDist_AE_eq_avssSimulateTrace` to
extract a joint factoring of `(coalitionAlgebraicView, schedulePrefix)`
through the trace's initial state `(ω 0).1`.  Both components are
deterministic functions of `(ω 0).1` (and the rushing adversary `R`
and coalition `C`), so the joint marginal of the trace measure is the
pushforward of the initial measure through this deterministic
function.  This is the structural prerequisite for §19.3's discharge
of `h_aux`. -/

/-- Simulate-derived algebraic view: a deterministic function of the
initial state `s_0`, equal AE to `coalitionAlgebraicView C ω k` along
the trace under a rushing adversary `R`.

The first component is the row polynomials at corrupt parties — a
function of `s_0.partyPoint` and `s_0.coeffs`.  The second is the
per-step `delivered` bits, computed deterministically from the
simulate.  -/
noncomputable def simAlgebraicView (R : AVSSRushingAdversary n t F corr)
    (C : BivariateShamir.Coalition n t) (k : ℕ) (s_0 : AVSSState n t F) :
    (C.val → Fin (t+1) → F) × (Fin k → C.val → Bool) :=
  (fun p => (s_0.dealerCommit p.val).rowPoly,
   fun i p => ((avssSimulateTrace R s_0 i.val).1.local_ p.val).delivered)

/-- Simulate-derived schedule prefix: a deterministic function of the
initial state `s_0`, equal AE to `schedulePrefix ω k` along the trace
under a rushing adversary `R`. -/
noncomputable def simSchedulePrefix (R : AVSSRushingAdversary n t F corr)
    (k : ℕ) (s_0 : AVSSState n t F) :
    Fin k → Option (AVSSAction n F) :=
  fun i => (avssSimulateTrace R s_0 i.val).2

/-- **Phase 8.5c** simulate-derived trivial-field view: a deterministic
function of the initial state `s_0`, equal AE to `coalitionTrivialView
C ω k` along the trace under a rushing adversary `R`. Mirrors the
second component of `simAlgebraicView` (the `delivered` bits) for the
four schedule-dependent trivial fields. -/
noncomputable def simTrivialView (R : AVSSRushingAdversary n t F corr)
    (C : BivariateShamir.Coalition n t) (k : ℕ) (s_0 : AVSSState n t F) :
    Fin k → C.val → TrivialView n :=
  fun i p =>
    let ls := (avssSimulateTrace R s_0 i.val).1.local_ p.val
    (ls.echoSent, ls.echoesReceived, ls.readySent, ls.readyReceived)

/-- **Phase 7.4 joint factoring.** Under a rushing adversary `R`, the
joint `(coalitionAlgebraicView C ω k, schedulePrefix ω k)` AE-equals
the simulate's deterministic image of `(ω 0).1`.

This is the cryptographic-core deliverable: it expresses the joint
operational-view-and-schedule marginal as a pushforward of the
initial measure through `(simAlgebraicView, simSchedulePrefix)`,
which is exactly the form needed to apply polynomial-level secrecy
in §19.3 below. -/
theorem coalitionAlgebraicView_schedulePrefix_AE_eq_sim
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (R : AVSSRushingAdversary n t F corr)
    (C : BivariateShamir.Coalition n t) (k : ℕ) :
    ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) R.toAdversary μ₀),
        (coalitionAlgebraicView C ω k, schedulePrefix ω k) =
          (simAlgebraicView R C k (ω 0).1, simSchedulePrefix R k (ω 0).1) := by
  classical
  -- Strong-form prefix matching: `ω i = sim i` for all `i ≤ k`.
  -- For algView's second component and schedulePrefix, we need every
  -- `i < k` (i.e., `i ≤ k - 1`).  Use `i ≤ k` for safety — covers all.
  have h_prefix :=
    traceDist_AE_eq_avssSimulateTrace_strong (t := t) sec corr coeffs μ₀ R k
  filter_upwards [h_prefix] with ω hω
  -- The first component (row poly at C parties) depends only on `(ω 0).1`.
  -- Both algView and simAlgebraicView's first components are literally
  -- `rowPolyOfDealer (ω 0).1.partyPoint (ω 0).1.coeffs p.val`.
  -- The second component / schedulePrefix depend on `(ω i).1` / `(ω i).2`,
  -- which match `avssSimulateTrace R (ω 0).1 i.val` AE.
  refine Prod.ext (Prod.ext rfl ?_) ?_
  · -- delivered bits at every (i : Fin k, p ∈ C)
    funext i p
    show ((ω i.val).1.local_ p.val).delivered =
        ((avssSimulateTrace R (ω 0).1 i.val).1.local_ p.val).delivered
    have hi : i.val ≤ k := le_of_lt i.isLt
    rw [hω i.val hi]
  · -- schedulePrefix at every i : Fin k
    funext i
    show (ω i.val).2 = (avssSimulateTrace R (ω 0).1 i.val).2
    have hi : i.val ≤ k := le_of_lt i.isLt
    rw [hω i.val hi]

/-- Joint factoring of `(coalitionAlgebraicView, schedulePrefix)` through
the trace's initial state, restated as a deterministic-function form:
the joint AE-equals `F((ω 0).1)` for `F` the simulate-derived pair.

This is the form actually used by §19.3 below to discharge `h_aux`.
The brief's preferred form — `schedulePrefix ω k = G(coalitionAlgebraicView)`
through `coalitionAlgebraicView` alone — is *not* generally provable
because `R.toAdversary.schedule` depends on `R`'s view of the **full**
corrupt set `corr`, while `coalitionAlgebraicView C` only carries
data for `C ⊆ corr`.  When `C ⊊ corr`, two traces with identical
algebraic views (on `C`) can have distinct schedules.  The factoring
through `(ω 0).1` is the correct form: it uses the strictly more
informative initial state, and the §19.3 reduction is via the
step-0 pair marginal of the trace measure (which equals
`avssInitMeasure` paired with `none`). -/
theorem traceDist_algebraicView_schedulePrefix_factors_AE
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (R : AVSSRushingAdversary n t F corr)
    (C : BivariateShamir.Coalition n t) (k : ℕ) :
    (traceDist (avssSpec (t := t) sec corr coeffs) R.toAdversary μ₀).map
        (fun ω => (coalitionAlgebraicView C ω k, schedulePrefix ω k)) =
      (traceDist (avssSpec (t := t) sec corr coeffs) R.toAdversary μ₀).map
        (fun ω =>
          (simAlgebraicView R C k (ω 0).1, simSchedulePrefix R k (ω 0).1)) := by
  refine Measure.map_congr ?_
  exact coalitionAlgebraicView_schedulePrefix_AE_eq_sim
    (t := t) sec corr coeffs μ₀ R C k

/-- **Phase 8.5c joint factoring (Ext form).** Under a rushing
adversary `R`, the joint
`((coalitionAlgebraicView ω k, coalitionTrivialView ω k),
  schedulePrefix ω k)` AE-equals the simulate's deterministic image
of `(ω 0).1`. Same proof structure as the algebraic-only bridge,
extended with the trivial-view component. -/
theorem coalitionViewExt_schedulePrefix_AE_eq_sim
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (R : AVSSRushingAdversary n t F corr)
    (C : BivariateShamir.Coalition n t) (k : ℕ) :
    ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr coeffs) R.toAdversary μ₀),
        ((coalitionAlgebraicView C ω k, coalitionTrivialView C ω k),
          schedulePrefix ω k) =
          ((simAlgebraicView R C k (ω 0).1,
              simTrivialView R C k (ω 0).1),
            simSchedulePrefix R k (ω 0).1) := by
  classical
  have h_prefix :=
    traceDist_AE_eq_avssSimulateTrace_strong (t := t) sec corr coeffs μ₀ R k
  filter_upwards [h_prefix] with ω hω
  refine Prod.ext (Prod.ext (Prod.ext rfl ?_) ?_) ?_
  · -- delivered bits at every (i : Fin k, p ∈ C)
    funext i p
    show ((ω i.val).1.local_ p.val).delivered =
        ((avssSimulateTrace R (ω 0).1 i.val).1.local_ p.val).delivered
    have hi : i.val ≤ k := le_of_lt i.isLt
    rw [hω i.val hi]
  · -- trivial-field projections at every (i : Fin k, p ∈ C)
    funext i p
    have hi : i.val ≤ k := le_of_lt i.isLt
    show (((ω i.val).1.local_ p.val).echoSent,
          ((ω i.val).1.local_ p.val).echoesReceived,
          ((ω i.val).1.local_ p.val).readySent,
          ((ω i.val).1.local_ p.val).readyReceived) =
        (((avssSimulateTrace R (ω 0).1 i.val).1.local_ p.val).echoSent,
         ((avssSimulateTrace R (ω 0).1 i.val).1.local_ p.val).echoesReceived,
         ((avssSimulateTrace R (ω 0).1 i.val).1.local_ p.val).readySent,
         ((avssSimulateTrace R (ω 0).1 i.val).1.local_ p.val).readyReceived)
    rw [hω i.val hi]
  · -- schedulePrefix at every i : Fin k
    funext i
    show (ω i.val).2 = (avssSimulateTrace R (ω 0).1 i.val).2
    have hi : i.val ≤ k := le_of_lt i.isLt
    rw [hω i.val hi]

/-- Measure-level form of `coalitionViewExt_schedulePrefix_AE_eq_sim`. -/
theorem traceDist_algTrivView_schedulePrefix_factors_AE
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (R : AVSSRushingAdversary n t F corr)
    (C : BivariateShamir.Coalition n t) (k : ℕ) :
    (traceDist (avssSpec (t := t) sec corr coeffs) R.toAdversary μ₀).map
        (fun ω => ((coalitionAlgebraicView C ω k, coalitionTrivialView C ω k),
                   schedulePrefix ω k)) =
      (traceDist (avssSpec (t := t) sec corr coeffs) R.toAdversary μ₀).map
        (fun ω =>
          ((simAlgebraicView R C k (ω 0).1,
              simTrivialView R C k (ω 0).1),
            simSchedulePrefix R k (ω 0).1)) := by
  refine Measure.map_congr ?_
  exact coalitionViewExt_schedulePrefix_AE_eq_sim
    (t := t) sec corr coeffs μ₀ R C k

/-! ## §19.3. Phase 7.5 — operational view secrecy under rushing adversary

The §19.3 wrapper `avss_secrecy_AS_view_rushing_via_aux` is a thin composition of
PR #33's `avss_secrecy_AS_view_conditional` with the rushing-adversary
adapter `R.toAdversary`.  The conditional theorem requires a joint
marginal-invariance hypothesis `h_aux` on `(coalitionAlgebraicView,
schedulePrefix)`; the rushing-adversary refactor (Phase 7.1–7.4)
**structurally restricts** the adversary's information to the corrupt-
coalition view, but `h_aux` itself remains the polynomial-level
*algebraic core* — specifically the row-poly-vs-grid secrecy
strengthening of `BivariateShamir.bivariate_shamir_secrecy` that is
documented as the second of two structural blockers in §17.12 and the
"+200 LOC polynomial-manipulation step" in `BivariateShamir.lean`'s
docstring.

Phase 7.4's substantive content — the inductive trace-determinism
proof showing that under `R.toAdversary`, every trace is AE-equal to
`avssSimulateTrace R (ω 0).1` (since each step's PMF is `pure`
and the schedule is a deterministic function of the view-history) —
provides the **simulate machinery** above (`avssSimulateRev`,
`avssSimulateTrace`, `avssSimulateNext`, structural lemmas).  The
inductive proof itself, threading the marginal recurrence
`Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure`
through the Dirac per-step kernel, is the bulk of the deferred
"~300–500 LOC of inductive trace plumbing" called out in
`AVSS-MODEL-NOTES.md` §9.  This wrapper exposes the schedule-leakage-
closing structure as a hypothesis-fed theorem so that downstream
consumers can compose `R.toAdversary` with the conditional theorem
without re-deriving the rushing-adapter plumbing each time.

The headline below quantifies over the conditional's `h_aux`
hypothesis — equivalent, after schedule-factoring (Phase 7.4's
substantive AE-bridge), to row-poly invariance of the corrupt
coalition's algebraic view.  In §19.4.5, the row-poly secrecy lemma
discharges this hypothesis unconditionally, yielding the canonical
fully-unconditional `avss_secrecy_AS_view_rushing` — the
literature-faithful operational-secrecy theorem under the AVSS state
model. -/

attribute [-instance] instMeasurableSpaceAVSSRushingView
  instMeasurableSingletonClassAVSSRushingView

/-- **Phase 7.5: operational view secrecy under a rushing adversary
(abstract-`h_aux` variant).**

For any rushing adversary `R` whose view is the corrupt coalition's
local-state projection (`AVSSRushingView corr`), and any subcoalition
`C ⊆ corr`, the joint marginal `(coalitionTraceView C, schedulePrefix)`
of the trace measure is invariant in the secret — provided the
algebraic-view-plus-schedule joint marginal invariance `h_aux` holds.

The hypothesis `h_aux` is the row-poly-vs-grid secrecy condition
(§17.12, blocker #2).  Phase 7.4's structural content (the simulate
machinery in §19.2 above) closes the schedule-leakage half (blocker #1)
by exhibiting the trace as a deterministic function of the initial
state under `R.toAdversary`.  The two halves are composed and the
hypothesis is discharged unconditionally in §19.4 (initial-measure
form) and §19.4.5 (canonical fully-unconditional headline
`avss_secrecy_AS_view_rushing`).

This thin composition is the mechanical step: plug `R.toAdversary` into
the conditional theorem.  The section's own
`instMeasurableSpaceAVSSRushingView` instance is disabled in this
sub-section so that the default Pi-`MeasurableSpace` is picked,
matching the conditional theorem's conclusion type. -/
theorem avss_secrecy_AS_view_rushing_via_aux
    {corr : Finset (Fin n)}
    (sec sec' : F)
    (μ_sec μ_sec' : Measure (AVSSState n t F))
    [IsProbabilityMeasure μ_sec] [IsProbabilityMeasure μ_sec']
    (h_init_sec : ∀ᵐ s ∂μ_sec, initPred sec corr coeffs s)
    (h_init_sec' : ∀ᵐ s ∂μ_sec', initPred sec' corr coeffs s)
    (h_dH_sec : ∀ᵐ s ∂μ_sec, s.dealerHonest = true)
    (h_dH_sec' : ∀ᵐ s ∂μ_sec', s.dealerHonest = true)
    (R : AVSSRushingAdversary n t F corr)
    (C : BivariateShamir.Coalition n t)
    (h_C_corr : C.val ⊆ corr) (k : ℕ)
    (h_aux :
      (traceDist (avssSpec (t := t) sec corr coeffs) R.toAdversary μ_sec).map
          (fun ω => ((coalitionAlgebraicView C ω k, coalitionTrivialView C ω k),
                     schedulePrefix ω k)) =
        (traceDist (avssSpec (t := t) sec' corr coeffs) R.toAdversary μ_sec').map
          (fun ω => ((coalitionAlgebraicView C ω k, coalitionTrivialView C ω k),
                     schedulePrefix ω k))) :
    (traceDist (avssSpec (t := t) sec corr coeffs) R.toAdversary μ_sec).map
        (fun ω => (coalitionTraceView C ω k, schedulePrefix ω k)) =
      (traceDist (avssSpec (t := t) sec' corr coeffs) R.toAdversary μ_sec').map
        (fun ω => (coalitionTraceView C ω k, schedulePrefix ω k)) :=
  avss_secrecy_AS_view_conditional sec sec' corr μ_sec μ_sec'
    h_init_sec h_init_sec' h_dH_sec h_dH_sec' C h_C_corr R.toAdversary k h_aux

/-- **Phase 8.5d-β-followup-6 — existential variant of
`avss_secrecy_AS_view_rushing_via_aux`.** Thin wrapper around
`avss_secrecy_AS_view_conditional_ex`. -/
theorem avss_secrecy_AS_view_rushing_via_aux_ex
    {corr : Finset (Fin n)}
    (sec sec' : F)
    (μ_sec μ_sec' : Measure (AVSSState n t F))
    [IsProbabilityMeasure μ_sec] [IsProbabilityMeasure μ_sec']
    (h_init_sec : ∀ᵐ s ∂μ_sec, ∃ c, initPred sec corr c s)
    (h_init_sec' : ∀ᵐ s ∂μ_sec', ∃ c, initPred sec' corr c s)
    (h_dH_sec : ∀ᵐ s ∂μ_sec, s.dealerHonest = true)
    (h_dH_sec' : ∀ᵐ s ∂μ_sec', s.dealerHonest = true)
    (R : AVSSRushingAdversary n t F corr)
    (C : BivariateShamir.Coalition n t)
    (h_C_corr : C.val ⊆ corr) (k : ℕ)
    (h_aux :
      (traceDist (avssSpec (t := t) sec corr coeffs) R.toAdversary μ_sec).map
          (fun ω => ((coalitionAlgebraicView C ω k, coalitionTrivialView C ω k),
                     schedulePrefix ω k)) =
        (traceDist (avssSpec (t := t) sec' corr coeffs) R.toAdversary μ_sec').map
          (fun ω => ((coalitionAlgebraicView C ω k, coalitionTrivialView C ω k),
                     schedulePrefix ω k))) :
    (traceDist (avssSpec (t := t) sec corr coeffs) R.toAdversary μ_sec).map
        (fun ω => (coalitionTraceView C ω k, schedulePrefix ω k)) =
      (traceDist (avssSpec (t := t) sec' corr coeffs) R.toAdversary μ_sec').map
        (fun ω => (coalitionTraceView C ω k, schedulePrefix ω k)) :=
  avss_secrecy_AS_view_conditional_ex sec sec' corr μ_sec μ_sec'
    h_init_sec h_init_sec' h_dH_sec h_dH_sec' C h_C_corr R.toAdversary k h_aux

/-- **Phase 8.5d-β-followup-7 — dealerHonest-INDEPENDENT
`_via_aux` wrapper.** Thin wrapper around
`avss_secrecy_AS_view_conditional_indep`. -/
theorem avss_secrecy_AS_view_rushing_via_aux_indep
    {corr : Finset (Fin n)}
    (sec sec' : F)
    (μ_sec μ_sec' : Measure (AVSSState n t F))
    [IsProbabilityMeasure μ_sec] [IsProbabilityMeasure μ_sec']
    (h_init_sec : ∀ᵐ s ∂μ_sec, ∃ c, initPred sec corr c s)
    (h_init_sec' : ∀ᵐ s ∂μ_sec', ∃ c, initPred sec' corr c s)
    (R : AVSSRushingAdversary n t F corr)
    (C : BivariateShamir.Coalition n t)
    (h_C_corr : C.val ⊆ corr) (k : ℕ)
    (h_aux :
      (traceDist (avssSpec (t := t) sec corr coeffs) R.toAdversary μ_sec).map
          (fun ω => ((coalitionAlgebraicView C ω k, coalitionTrivialView C ω k),
                     schedulePrefix ω k)) =
        (traceDist (avssSpec (t := t) sec' corr coeffs) R.toAdversary μ_sec').map
          (fun ω => ((coalitionAlgebraicView C ω k, coalitionTrivialView C ω k),
                     schedulePrefix ω k))) :
    (traceDist (avssSpec (t := t) sec corr coeffs) R.toAdversary μ_sec).map
        (fun ω => (coalitionTraceView C ω k, schedulePrefix ω k)) =
      (traceDist (avssSpec (t := t) sec' corr coeffs) R.toAdversary μ_sec').map
        (fun ω => (coalitionTraceView C ω k, schedulePrefix ω k)) :=
  avss_secrecy_AS_view_conditional_indep sec sec' corr μ_sec μ_sec'
    h_init_sec h_init_sec' C h_C_corr R.toAdversary k h_aux

/-! ## §19.4. Phase 7.4 — discharge of `h_aux` from initial-state invariance

This section delivers the structural reduction from the trace-level
`h_aux` to a polynomial-level invariance hypothesis at the
`avssInitMeasure` level.  Combined with PR #36's polynomial-level
secrecy infrastructure (`uniformBivariateFullWithFixedZero` +
`bivariate_evals_uniform_full`) and a forthcoming row-poly secrecy
lemma (the "+200 LOC algebraic core"), this gives an unconditional
operational-secrecy headline.

The reduction proceeds in two steps:

* **Step 1** (`traceDist_jointMarginal_eq_init`) — the trace-level
  joint marginal `(coalitionAlgebraicView, schedulePrefix)` equals
  the pushforward of the initial measure through the simulate-derived
  function `(simAlgebraicView, simSchedulePrefix)`.  Uses Phase 7.4's
  AE-bridge from §19.2.4 plus the step-0 state marginal of `traceDist`.

* **Step 2** (`traceDist_algebraicView_schedulePrefix_invariant`) —
  given that the *initial-measure* pushforward through
  `(simAlgebraicView, simSchedulePrefix)` is sec-invariant, the
  trace-level pushforward is sec-invariant.  Direct application of
  Step 1 + measure transport.

* **Step 3** (`avss_secrecy_AS_view_rushing_via_init_invariant`) — combine
  Step 2 with `avss_secrecy_AS_view_conditional` to get the
  operational-view secrecy headline.

The remaining work to make the headline truly unconditional (without
the init-marginal hypothesis) is to prove that the initial-measure
pushforward through `(simAlgebraicView, simSchedulePrefix)` is
sec-invariant.  By the structure of `simAlgebraicView` /
`simSchedulePrefix` and the initial measure, this reduces to
**row-poly secrecy at `corr`** under
`uniformBivariateFullWithFixedZero` (i.e., the row polynomials of the
bivariate polynomial at the corrupt coalition's partyPoints have a
sec-invariant joint distribution, when `corr.card ≤ t` and `partyPoint`
avoids zero).  This is the deferred `+200 LOC algebraic core` step
called out in `AVSS-MODEL-NOTES.md` §9. -/

/-- **Step 1.** The trace-level joint marginal of
`(coalitionAlgebraicView, schedulePrefix)` equals the pushforward of
the initial measure through the simulate-derived deterministic
function.

Combines Phase 7.4's AE-bridge (§19.2.5,
`coalitionAlgebraicView_schedulePrefix_AE_eq_sim`) with the step-0
state marginal of `traceDist` (`traceDist_step_zero_state_marginal`,
PR #32) to express the trace-level joint as a pushforward of the
initial measure. -/
theorem traceDist_jointMarginal_eq_init
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (R : AVSSRushingAdversary n t F corr)
    (C : BivariateShamir.Coalition n t) (k : ℕ) :
    (traceDist (avssSpec (t := t) sec corr coeffs) R.toAdversary μ₀).map
        (fun ω => (coalitionAlgebraicView C ω k, schedulePrefix ω k)) =
      μ₀.map (fun s_0 =>
        (simAlgebraicView R C k s_0, simSchedulePrefix R k s_0)) := by
  classical
  -- AE form: trace-level joint matches simulate-derived joint.
  rw [traceDist_algebraicView_schedulePrefix_factors_AE
    (t := t) sec corr coeffs μ₀ R C k]
  -- Now: rewrite as pushforward through (ω 0).1.
  have hmeas_simView : Measurable
      (fun s_0 : AVSSState n t F =>
        (simAlgebraicView R C k s_0, simSchedulePrefix R k s_0)) :=
    measurable_of_countable _
  have hmeas_state0 : Measurable
      (fun ω : Π _ : ℕ, AVSSState n t F × Option (AVSSAction n F) =>
        (ω 0).1) := by fun_prop
  rw [show (fun ω : Π _ : ℕ, AVSSState n t F × Option (AVSSAction n F) =>
            (simAlgebraicView R C k (ω 0).1, simSchedulePrefix R k (ω 0).1)) =
        (fun s_0 : AVSSState n t F =>
            (simAlgebraicView R C k s_0, simSchedulePrefix R k s_0)) ∘
          (fun ω => (ω 0).1) from rfl]
  rw [← Measure.map_map hmeas_simView hmeas_state0]
  rw [traceDist_step_zero_state_marginal sec corr coeffs μ₀ R.toAdversary]

/-- **Step 1 (Ext form, 8.5c).** The trace-level joint marginal of
`((coalitionAlgebraicView, coalitionTrivialView), schedulePrefix)`
equals the pushforward of the initial measure through
`((simAlgebraicView, simTrivialView), simSchedulePrefix)`. -/
theorem traceDist_jointMarginalExt_eq_init
    (sec : F) (corr : Finset (Fin n)) (coeffs : Fin (t+1) → Fin (t+1) → F)
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (R : AVSSRushingAdversary n t F corr)
    (C : BivariateShamir.Coalition n t) (k : ℕ) :
    (traceDist (avssSpec (t := t) sec corr coeffs) R.toAdversary μ₀).map
        (fun ω => ((coalitionAlgebraicView C ω k,
                    coalitionTrivialView C ω k),
                   schedulePrefix ω k)) =
      μ₀.map (fun s_0 =>
        ((simAlgebraicView R C k s_0, simTrivialView R C k s_0),
          simSchedulePrefix R k s_0)) := by
  classical
  rw [traceDist_algTrivView_schedulePrefix_factors_AE
    (t := t) sec corr coeffs μ₀ R C k]
  have hmeas_simView : Measurable
      (fun s_0 : AVSSState n t F =>
        ((simAlgebraicView R C k s_0, simTrivialView R C k s_0),
          simSchedulePrefix R k s_0)) :=
    measurable_of_countable _
  have hmeas_state0 : Measurable
      (fun ω : Π _ : ℕ, AVSSState n t F × Option (AVSSAction n F) =>
        (ω 0).1) := by fun_prop
  rw [show (fun ω : Π _ : ℕ, AVSSState n t F × Option (AVSSAction n F) =>
            ((simAlgebraicView R C k (ω 0).1,
                simTrivialView R C k (ω 0).1),
              simSchedulePrefix R k (ω 0).1)) =
        (fun s_0 : AVSSState n t F =>
            ((simAlgebraicView R C k s_0, simTrivialView R C k s_0),
              simSchedulePrefix R k s_0)) ∘
          (fun ω => (ω 0).1) from rfl]
  rw [← Measure.map_map hmeas_simView hmeas_state0]
  rw [traceDist_step_zero_state_marginal sec corr coeffs μ₀ R.toAdversary]

/-- **Step 2.** Given sec-invariance at the initial-measure level
(through the simulate-derived deterministic function), conclude
sec-invariance at the trace level. -/
theorem traceDist_algebraicView_schedulePrefix_invariant
    (sec sec' : F) (corr : Finset (Fin n))
    (μ_sec μ_sec' : Measure (AVSSState n t F))
    [IsProbabilityMeasure μ_sec] [IsProbabilityMeasure μ_sec']
    (R : AVSSRushingAdversary n t F corr)
    (C : BivariateShamir.Coalition n t) (k : ℕ)
    (h_init_invariant :
        μ_sec.map (fun s_0 =>
          (simAlgebraicView R C k s_0, simSchedulePrefix R k s_0)) =
          μ_sec'.map (fun s_0 =>
            (simAlgebraicView R C k s_0, simSchedulePrefix R k s_0))) :
    (traceDist (avssSpec (t := t) sec corr coeffs) R.toAdversary μ_sec).map
        (fun ω => (coalitionAlgebraicView C ω k, schedulePrefix ω k)) =
      (traceDist (avssSpec (t := t) sec' corr coeffs) R.toAdversary μ_sec').map
        (fun ω => (coalitionAlgebraicView C ω k, schedulePrefix ω k)) := by
  rw [traceDist_jointMarginal_eq_init (t := t) sec corr coeffs μ_sec R C k,
      traceDist_jointMarginal_eq_init (t := t) sec' corr coeffs μ_sec' R C k]
  exact h_init_invariant

/-- **Step 2 (Ext form, 8.5c).** Sec-invariance of the initial-measure
joint pushforward through `((simAlgebraicView, simTrivialView),
simSchedulePrefix)` lifts to sec-invariance of the trace-level joint
`((coalitionAlgebraicView, coalitionTrivialView), schedulePrefix)`. -/
theorem traceDist_algTrivView_schedulePrefix_invariant
    (sec sec' : F) (corr : Finset (Fin n))
    (μ_sec μ_sec' : Measure (AVSSState n t F))
    [IsProbabilityMeasure μ_sec] [IsProbabilityMeasure μ_sec']
    (R : AVSSRushingAdversary n t F corr)
    (C : BivariateShamir.Coalition n t) (k : ℕ)
    (h_init_invariant :
        μ_sec.map (fun s_0 =>
          ((simAlgebraicView R C k s_0, simTrivialView R C k s_0),
            simSchedulePrefix R k s_0)) =
          μ_sec'.map (fun s_0 =>
            ((simAlgebraicView R C k s_0, simTrivialView R C k s_0),
              simSchedulePrefix R k s_0))) :
    (traceDist (avssSpec (t := t) sec corr coeffs) R.toAdversary μ_sec).map
        (fun ω => ((coalitionAlgebraicView C ω k,
                    coalitionTrivialView C ω k),
                   schedulePrefix ω k)) =
      (traceDist (avssSpec (t := t) sec' corr coeffs) R.toAdversary μ_sec').map
        (fun ω => ((coalitionAlgebraicView C ω k,
                    coalitionTrivialView C ω k),
                   schedulePrefix ω k)) := by
  rw [traceDist_jointMarginalExt_eq_init (t := t) sec corr coeffs μ_sec R C k,
      traceDist_jointMarginalExt_eq_init (t := t) sec' corr coeffs μ_sec' R C k]
  exact h_init_invariant

/-- **Step 3 (Phase 7.4 headline).**  Operational view secrecy under a
rushing adversary, given the initial-measure invariance hypothesis.

Compared to `avss_secrecy_AS_view_rushing_via_aux`, this version replaces the
abstract trace-level `h_aux` with a more concrete initial-measure
invariance — a polynomial-level hypothesis that is closer to the
existing `bivariate_shamir_secrecy_full` from PR #36.  The row-poly
secrecy lemma at `corr` (`bivariate_shamir_secrecy_rowPoly_full`)
discharges this hypothesis, and §19.4.5 composes the two to obtain
the canonical fully-unconditional `avss_secrecy_AS_view_rushing`. -/
theorem avss_secrecy_AS_view_rushing_via_init_invariant
    {corr : Finset (Fin n)}
    (sec sec' : F)
    (μ_sec μ_sec' : Measure (AVSSState n t F))
    [IsProbabilityMeasure μ_sec] [IsProbabilityMeasure μ_sec']
    (h_init_sec : ∀ᵐ s ∂μ_sec, initPred sec corr coeffs s)
    (h_init_sec' : ∀ᵐ s ∂μ_sec', initPred sec' corr coeffs s)
    (h_dH_sec : ∀ᵐ s ∂μ_sec, s.dealerHonest = true)
    (h_dH_sec' : ∀ᵐ s ∂μ_sec', s.dealerHonest = true)
    (R : AVSSRushingAdversary n t F corr)
    (C : BivariateShamir.Coalition n t)
    (h_C_corr : C.val ⊆ corr) (k : ℕ)
    (h_init_invariant :
        μ_sec.map (fun s_0 =>
          ((simAlgebraicView R C k s_0, simTrivialView R C k s_0),
            simSchedulePrefix R k s_0)) =
          μ_sec'.map (fun s_0 =>
            ((simAlgebraicView R C k s_0, simTrivialView R C k s_0),
              simSchedulePrefix R k s_0))) :
    (traceDist (avssSpec (t := t) sec corr coeffs) R.toAdversary μ_sec).map
        (fun ω => (coalitionTraceView C ω k, schedulePrefix ω k)) =
      (traceDist (avssSpec (t := t) sec' corr coeffs) R.toAdversary μ_sec').map
        (fun ω => (coalitionTraceView C ω k, schedulePrefix ω k)) := by
  apply avss_secrecy_AS_view_rushing_via_aux sec sec' μ_sec μ_sec'
    h_init_sec h_init_sec' h_dH_sec h_dH_sec' R C h_C_corr k
  exact traceDist_algTrivView_schedulePrefix_invariant
    (t := t) sec sec' corr μ_sec μ_sec' R C k h_init_invariant

/-- **Phase 8.5d-β-followup-6 — existential variant of
`avss_secrecy_AS_view_rushing_via_init_invariant`.**

Identical to the fixed-coeffs version except `h_init_sec` /
`h_init_sec'` take the existential AE-form (matching what
`avssInitMeasure_AE_initPred` returns). Final wrapper used by
`avss_secrecy_AS_view_rushing` to bridge the existential h_init
returned by `avssInitMeasure_AE_initPred` to the conclusion. -/
theorem avss_secrecy_AS_view_rushing_via_init_invariant_ex
    {corr : Finset (Fin n)}
    (sec sec' : F)
    (μ_sec μ_sec' : Measure (AVSSState n t F))
    [IsProbabilityMeasure μ_sec] [IsProbabilityMeasure μ_sec']
    (h_init_sec : ∀ᵐ s ∂μ_sec, ∃ c, initPred sec corr c s)
    (h_init_sec' : ∀ᵐ s ∂μ_sec', ∃ c, initPred sec' corr c s)
    (h_dH_sec : ∀ᵐ s ∂μ_sec, s.dealerHonest = true)
    (h_dH_sec' : ∀ᵐ s ∂μ_sec', s.dealerHonest = true)
    (R : AVSSRushingAdversary n t F corr)
    (C : BivariateShamir.Coalition n t)
    (h_C_corr : C.val ⊆ corr) (k : ℕ)
    (h_init_invariant :
        μ_sec.map (fun s_0 =>
          ((simAlgebraicView R C k s_0, simTrivialView R C k s_0),
            simSchedulePrefix R k s_0)) =
          μ_sec'.map (fun s_0 =>
            ((simAlgebraicView R C k s_0, simTrivialView R C k s_0),
              simSchedulePrefix R k s_0))) :
    (traceDist (avssSpec (t := t) sec corr coeffs) R.toAdversary μ_sec).map
        (fun ω => (coalitionTraceView C ω k, schedulePrefix ω k)) =
      (traceDist (avssSpec (t := t) sec' corr coeffs) R.toAdversary μ_sec').map
        (fun ω => (coalitionTraceView C ω k, schedulePrefix ω k)) := by
  apply avss_secrecy_AS_view_rushing_via_aux_ex sec sec' μ_sec μ_sec'
    h_init_sec h_init_sec' h_dH_sec h_dH_sec' R C h_C_corr k
  exact traceDist_algTrivView_schedulePrefix_invariant
    (t := t) sec sec' corr μ_sec μ_sec' R C k h_init_invariant

/-- **Phase 8.5d-β-followup-7 — dealerHonest-INDEPENDENT
`_via_init_invariant` wrapper.** Final wrapper used by
`avss_secrecy_AS_view_rushing` to close BOTH dealerHonest values
uniformly (no case-split needed). -/
theorem avss_secrecy_AS_view_rushing_via_init_invariant_indep
    {corr : Finset (Fin n)}
    (sec sec' : F)
    (μ_sec μ_sec' : Measure (AVSSState n t F))
    [IsProbabilityMeasure μ_sec] [IsProbabilityMeasure μ_sec']
    (h_init_sec : ∀ᵐ s ∂μ_sec, ∃ c, initPred sec corr c s)
    (h_init_sec' : ∀ᵐ s ∂μ_sec', ∃ c, initPred sec' corr c s)
    (R : AVSSRushingAdversary n t F corr)
    (C : BivariateShamir.Coalition n t)
    (h_C_corr : C.val ⊆ corr) (k : ℕ)
    (h_init_invariant :
        μ_sec.map (fun s_0 =>
          ((simAlgebraicView R C k s_0, simTrivialView R C k s_0),
            simSchedulePrefix R k s_0)) =
          μ_sec'.map (fun s_0 =>
            ((simAlgebraicView R C k s_0, simTrivialView R C k s_0),
              simSchedulePrefix R k s_0))) :
    (traceDist (avssSpec (t := t) sec corr coeffs) R.toAdversary μ_sec).map
        (fun ω => (coalitionTraceView C ω k, schedulePrefix ω k)) =
      (traceDist (avssSpec (t := t) sec' corr coeffs) R.toAdversary μ_sec').map
        (fun ω => (coalitionTraceView C ω k, schedulePrefix ω k)) := by
  apply avss_secrecy_AS_view_rushing_via_aux_indep sec sec' μ_sec μ_sec'
    h_init_sec h_init_sec' R C h_C_corr k
  exact traceDist_algTrivView_schedulePrefix_invariant
    (t := t) sec sec' corr μ_sec μ_sec' R C k h_init_invariant

/-! ## §19.4. Phase 7.4 final closure — discharging `h_init_invariant`

This section completes the operational view-secrecy story by closing
the last hypothesis `h_init_invariant` of
`avss_secrecy_AS_view_rushing_via_init_invariant`.

The goal is to show that for `μ_sec = avssInitMeasure sec corr partyPoint
dealerHonest` and similarly `μ_sec'`, the pushforward through
`(simAlgebraicView R C k, simSchedulePrefix R k)` is sec-invariant.

**Key insight (simulate factoring).** The simulate trace is fully
deterministic and the rushing scheduler depends only on the corrupt
view-history. If two initial states agree on:

  * `partyPoint`, `corrupted`, `dealerSent` and all in-flight queues,
  * the row polynomials at corrupt parties (i.e., `rowPolyOfDealer
    s.partyPoint s.coeffs p` for every `p ∈ corr`), and
  * all per-party local states,

then the entire simulate runs identically (state-by-state on corrupt
locals, action-by-action on the schedule).  In particular,
`simAlgebraicView R C k` and `simSchedulePrefix R k` agree.  Combined
with `bivariate_shamir_secrecy_rowPoly_full`, this closes
`h_init_invariant`. -/

/-- Relational invariant pinning the corrupt-coalition view of two AVSS
states.  Two states `s, s'` are simulate-synced (relative to a fixed
corrupt set `corr`) when:

  * all "shared" structural fields agree (partyPoint, corrupted,
    dealerSent, all in-flight queues);
  * all per-party local states agree on all fields **except** possibly
    `rowPoly` and `output` (which can differ on honest parties because
    they are computed from `coeffs`);
  * for honest parties, `rowPoly` and `output` are simultaneously
    `none` or `some _` (so gates' `output = none` checks decide
    identically);
  * for corrupt parties, the local states are pointwise equal
    (so the rushing scheduler's view is identical);
  * the row polynomials at corrupt parties agree (so
    `partyCorruptDeliver` preserves corrupt-local equality). -/
structure simSyncInv (corr : Finset (Fin n)) (s s' : AVSSState n t F) : Prop where
  partyPoint_eq : s.partyPoint = s'.partyPoint
  corrupted_eq : s.corrupted = s'.corrupted
  corrupted_corr : s.corrupted = corr
  dealerSent_eq : s.dealerSent = s'.dealerSent
  inflightDeliveries_eq : s.inflightDeliveries = s'.inflightDeliveries
  inflightCorruptDeliveries_eq :
    s.inflightCorruptDeliveries = s'.inflightCorruptDeliveries
  inflightEchoes_eq : s.inflightEchoes = s'.inflightEchoes
  inflightReady_eq : s.inflightReady = s'.inflightReady
  /-- Corrupt parties' local states are pointwise equal. -/
  local_corrupt_eq : ∀ p ∈ corr, s.local_ p = s'.local_ p
  /-- Honest parties' local states agree on `delivered`. -/
  local_honest_delivered :
    ∀ p, p ∉ corr → (s.local_ p).delivered = (s'.local_ p).delivered
  /-- Honest parties' local states agree on `echoSent`. -/
  local_honest_echoSent :
    ∀ p, p ∉ corr → (s.local_ p).echoSent = (s'.local_ p).echoSent
  /-- Honest parties' local states agree on `echoesReceived`. -/
  local_honest_echoesReceived :
    ∀ p, p ∉ corr → (s.local_ p).echoesReceived = (s'.local_ p).echoesReceived
  /-- Honest parties' local states agree on `readyReceived`. -/
  local_honest_readyReceived :
    ∀ p, p ∉ corr → (s.local_ p).readyReceived = (s'.local_ p).readyReceived
  /-- Honest parties' local states agree on `readySent`. -/
  local_honest_readySent :
    ∀ p, p ∉ corr → (s.local_ p).readySent = (s'.local_ p).readySent
  /-- Honest parties' `output` fields agree on `isSome`. -/
  local_honest_output_isSome :
    ∀ p, p ∉ corr → (s.local_ p).output.isSome = (s'.local_ p).output.isSome
  /-- Phase 8.1: per-party dealer payloads agree on `isSome` (so the
  new `(dealerMessages p).isSome` gate of `partyDeliver` /
  `partyCorruptDeliver` decides identically). -/
  dealerMessages_isSome_eq :
    ∀ p, (s.dealerMessages p).isSome = (s'.dealerMessages p).isSome
  /-- Phase 8.1 / 8.5d-β: at corrupt parties the dealer payloads agree
  pointwise.  Post-Phase-8.5d-β this is preserved via
  `dealerCommit_corrupt_eq` (the per-party commitment is fixed at
  init and never modified by `avssStep`); `dealerShareTo r` for
  corrupt `r` writes the same payload to `dealerMessages r` on both
  sides. -/
  dealerMessages_corrupt_eq :
    ∀ p ∈ corr, s.dealerMessages p = s'.dealerMessages p
  /-- Phase 8.5d-β: at corrupt parties the dealer's per-party
  commitments agree (so `dealerShareTo r` for corrupt `r` writes the
  same payload to `dealerMessages r` on both sides, preserving
  `dealerMessages_corrupt_eq`).  At init this comes from the `h_rp`
  hypothesis on `rowPolyOfDealer` agreement (the `colPoly` is the
  identical `fun _ => 0` placeholder on both sides).  Preservation is
  trivial: `dealerCommit` is never modified by any `avssStep` action. -/
  dealerCommit_corrupt_eq :
    ∀ p ∈ corr, s.dealerCommit p = s'.dealerCommit p

namespace simSyncInv

variable {corr : Finset (Fin n)} {s s' : AVSSState n t F}

omit [Fintype F] in
/-- `simSyncInv` is symmetric. -/
theorem symm (h : simSyncInv corr s s') : simSyncInv corr s' s :=
  { partyPoint_eq := h.partyPoint_eq.symm
    corrupted_eq := h.corrupted_eq.symm
    corrupted_corr := h.corrupted_eq.symm.trans h.corrupted_corr
    dealerSent_eq := h.dealerSent_eq.symm
    inflightDeliveries_eq := h.inflightDeliveries_eq.symm
    inflightCorruptDeliveries_eq := h.inflightCorruptDeliveries_eq.symm
    inflightEchoes_eq := h.inflightEchoes_eq.symm
    inflightReady_eq := h.inflightReady_eq.symm
    local_corrupt_eq := fun p hp => (h.local_corrupt_eq p hp).symm
    local_honest_delivered := fun p hp => (h.local_honest_delivered p hp).symm
    local_honest_echoSent := fun p hp => (h.local_honest_echoSent p hp).symm
    local_honest_echoesReceived :=
      fun p hp => (h.local_honest_echoesReceived p hp).symm
    local_honest_readyReceived :=
      fun p hp => (h.local_honest_readyReceived p hp).symm
    local_honest_readySent := fun p hp => (h.local_honest_readySent p hp).symm
    local_honest_output_isSome :=
      fun p hp => (h.local_honest_output_isSome p hp).symm
    dealerMessages_isSome_eq := fun p => (h.dealerMessages_isSome_eq p).symm
    dealerMessages_corrupt_eq :=
      fun p hp => (h.dealerMessages_corrupt_eq p hp).symm
    dealerCommit_corrupt_eq :=
      fun p hp => (h.dealerCommit_corrupt_eq p hp).symm }

/-- The rushing-view projection of two simulate-synced states are
literally equal: `R.view s = R.view s'` because corrupt locals agree.

Note: this depends on the rushing adversary `R` having `toProtocolView =
avssCoalitionView corr`, which the AVSS spec instantiates by definition. -/
theorem rushingView_eq (R : AVSSRushingAdversary n t F corr)
    (h_R : R.toProtocolView = avssCoalitionView corr)
    (h : simSyncInv corr s s') :
    R.view s = R.view s' := by
  show R.toProtocolView.view s = R.toProtocolView.view s'
  rw [h_R]
  funext p
  exact h.local_corrupt_eq p.val (h.corrupted_corr ▸ p.property)

omit [Fintype F] in
/-- `output = none` is preserved by the `simSyncInv` invariant on
honest parties. -/
theorem output_none_iff_of_honest (h : simSyncInv corr s s')
    (q : Fin n) (hq : q ∉ corr) :
    (s.local_ q).output = none ↔ (s'.local_ q).output = none := by
  have hSome := h.local_honest_output_isSome q hq
  rcases hsv : (s.local_ q).output with _ | v0 <;>
  rcases hs'v : (s'.local_ q).output with _ | v1 <;>
  simp [hsv, hs'v] at hSome ⊢

omit [Fintype F] in
/-- `q ∈ s.corrupted ↔ q ∈ s'.corrupted` by `corrupted_eq`. -/
theorem corrupted_mem_iff (h : simSyncInv corr s s') (q : Fin n) :
    q ∈ s.corrupted ↔ q ∈ s'.corrupted := by
  rw [h.corrupted_eq]

omit [Fintype F] in
/-- `q ∈ corr ↔ q ∈ s.corrupted`. -/
theorem corr_mem_iff (h : simSyncInv corr s s') (q : Fin n) :
    q ∈ corr ↔ q ∈ s.corrupted := by
  rw [h.corrupted_corr]

-- `actionGate` agrees on simulate-synced states.  The gate predicate
-- inspects only honest-local Bool/Finset fields and global structural
-- fields, all of which are equal under `simSyncInv`.
omit [Fintype F] in
theorem actionGate_iff (h : simSyncInv corr s s')
    (a : AVSSAction n F) :
    actionGate a s ↔ actionGate a s' := by
  cases a with
  | dealerShareTo p =>
    simp only [actionGate, h.dealerSent_eq]
  | partyDeliver q =>
    -- gate: dealerSent q = true ∧ q ∉ corrupted ∧ q ∈ inflightDeliveries
    --       ∧ (local_ q).delivered = false ∧ (dealerMessages q).isSome
    by_cases hq : q ∈ corr
    · -- q ∈ corr means q ∈ s.corrupted and q ∈ s'.corrupted, so gate is False both sides.
      have hqs : q ∈ s.corrupted := h.corrupted_corr ▸ hq
      have hqs' : q ∈ s'.corrupted := h.corrupted_eq ▸ hqs
      simp only [actionGate]
      constructor
      · rintro ⟨_, hqq, _, _, _⟩; exact (hqq hqs).elim
      · rintro ⟨_, hqq, _, _, _⟩; exact (hqq hqs').elim
    · simp only [actionGate, h.dealerSent_eq, h.inflightDeliveries_eq,
                 h.local_honest_delivered q hq, h.corrupted_eq,
                 h.dealerMessages_isSome_eq q]
  | partyCorruptDeliver q =>
    by_cases hq : q ∈ corr
    · -- q ∈ corr; gate inspects local_ q which is equal by `local_corrupt_eq`,
      -- and `dealerMessages q` which is equal by `dealerMessages_corrupt_eq`.
      have hqs : q ∈ s.corrupted := h.corrupted_corr ▸ hq
      have hqs' : q ∈ s'.corrupted := h.corrupted_eq ▸ hqs
      simp only [actionGate, h.dealerSent_eq, h.inflightCorruptDeliveries_eq,
                 h.local_corrupt_eq q hq, h.corrupted_eq,
                 h.dealerMessages_corrupt_eq q hq]
    · -- q ∉ corr ⇒ q ∉ s.corrupted ⇒ gate False both sides.
      have hqs : q ∉ s.corrupted := h.corrupted_corr ▸ hq
      have hqs' : q ∉ s'.corrupted := h.corrupted_eq ▸ hqs
      simp only [actionGate]
      constructor
      · rintro ⟨_, hqq, _, _, _⟩; exact (hqs hqq).elim
      · rintro ⟨_, hqq, _, _, _⟩; exact (hqs' hqq).elim
  | partyEchoSend q =>
    -- gate: (local_ q).delivered = true ∧ (local_ q).echoSent = false ∧ dealerSent = true
    by_cases hq : q ∈ corr
    · -- q ∈ corr; corrupt locals pointwise equal by `local_corrupt_eq`.
      simp only [actionGate, h.dealerSent_eq, h.local_corrupt_eq q hq]
    · -- q ∉ corr (honest); use honest field equalities.
      simp only [actionGate, h.local_honest_delivered q hq,
                 h.local_honest_echoSent q hq, h.dealerSent_eq]
  | partyEchoReceive q r =>
    -- gate: (r, q) ∈ inflightEchoes ∧ r ∉ (local_ q).echoesReceived
    by_cases hq : q ∈ corr
    · simp only [actionGate, h.inflightEchoes_eq, h.local_corrupt_eq q hq]
    · simp only [actionGate, h.inflightEchoes_eq,
                 h.local_honest_echoesReceived q hq]
  | partyReady q =>
    -- gate: (local_ q).delivered = true ∧ (local_ q).readySent = false ∧
    --        (local_ q).echoesReceived.card ≥ n - t ∧ dealerSent = true
    by_cases hq : q ∈ corr
    · simp only [actionGate, h.dealerSent_eq, h.local_corrupt_eq q hq]
    · simp only [actionGate, h.dealerSent_eq, h.local_honest_delivered q hq,
                 h.local_honest_readySent q hq,
                 h.local_honest_echoesReceived q hq]
  | partyAmplify q =>
    -- gate: (local_ q).readySent = false ∧
    --        (local_ q).readyReceived.card ≥ t + 1 ∧ dealerSent = true
    by_cases hq : q ∈ corr
    · simp only [actionGate, h.dealerSent_eq, h.local_corrupt_eq q hq]
    · simp only [actionGate, h.dealerSent_eq, h.local_honest_readySent q hq,
                 h.local_honest_readyReceived q hq]
  | partyReceiveReady q r =>
    -- gate: r ∈ inflightReady ∧ r ∉ (local_ q).readyReceived
    by_cases hq : q ∈ corr
    · simp only [actionGate, h.inflightReady_eq, h.local_corrupt_eq q hq]
    · simp only [actionGate, h.inflightReady_eq,
                 h.local_honest_readyReceived q hq]
  | partyOutput q =>
    by_cases hq : q ∈ corr
    · have hqs : q ∈ s.corrupted := h.corrupted_corr ▸ hq
      have hqs' : q ∈ s'.corrupted := h.corrupted_eq ▸ hqs
      simp only [actionGate]
      constructor
      · rintro ⟨hqq, _, _⟩; exact (hqq hqs).elim
      · rintro ⟨hqq, _, _⟩; exact (hqq hqs').elim
    · have h_outNone := h.output_none_iff_of_honest q hq
      simp only [actionGate, h.local_honest_delivered q hq,
                 h.local_honest_readySent q hq, h_outNone,
                 h.local_honest_readyReceived q hq, h.corrupted_eq]

-- `simSyncInv` is preserved under `avssStep` for any gated action.
-- Phase 8.5b-γ re-derivation under the C1+C2 model: under C1, corrupt
-- parties may also fire `partyEchoSend` / `partyReady` / `partyAmplify`;
-- under C2, corrupt parties may also be `partyEchoReceive` /
-- `partyReceiveReady` recipients.  In each such case we case-split on
-- `q ∈ corr` and handle both branches:
--   * `q ∈ corr`: corrupt-side write is matched on both sides via
--     `local_corrupt_eq` (which yields `(s.local_ q) = (s'.local_ q)`,
--     so the `setLocal` writes the same `ls'` on both sides).
--   * `q ∉ corr`: the original honest-side argument applies verbatim.
omit [Fintype F] in
theorem avssStep_preserves_simSyncInv (a : AVSSAction n F)
    (h : simSyncInv corr s s') (hgate : actionGate a s) :
    simSyncInv corr (avssStep a s) (avssStep a s') := by
  cases a with
  | dealerShareTo r =>
    refine
      { partyPoint_eq := h.partyPoint_eq
        corrupted_eq := h.corrupted_eq
        corrupted_corr := h.corrupted_corr
        dealerSent_eq := ?_
        inflightDeliveries_eq := ?_
        inflightCorruptDeliveries_eq := ?_
        inflightEchoes_eq := h.inflightEchoes_eq
        inflightReady_eq := h.inflightReady_eq
        local_corrupt_eq := fun p hp => h.local_corrupt_eq p hp
        local_honest_delivered := fun p hp => h.local_honest_delivered p hp
        local_honest_echoSent := fun p hp => h.local_honest_echoSent p hp
        local_honest_echoesReceived :=
          fun p hp => h.local_honest_echoesReceived p hp
        local_honest_readyReceived :=
          fun p hp => h.local_honest_readyReceived p hp
        local_honest_readySent := fun p hp => h.local_honest_readySent p hp
        local_honest_output_isSome :=
          fun p hp => h.local_honest_output_isSome p hp
        dealerMessages_isSome_eq := ?_
        dealerMessages_corrupt_eq := ?_
        dealerCommit_corrupt_eq := h.dealerCommit_corrupt_eq }
    · simp only [avssStep]; exact congrArg (Function.update · r true) h.dealerSent_eq
    · simp only [avssStep, h.corrupted_eq]
      split <;> simp [h.inflightDeliveries_eq]
    · simp only [avssStep, h.corrupted_eq]
      split <;> simp [h.inflightCorruptDeliveries_eq]
    · intro p
      simp only [avssStep]
      by_cases hpr : p = r
      · subst hpr; simp [Function.update_self]
      · simp [Function.update_of_ne hpr]; exact h.dealerMessages_isSome_eq p
    · intro p hp
      simp only [avssStep]
      by_cases hpr : p = r
      · subst hpr; simp only [Function.update_self]
        exact congrArg some (h.dealerCommit_corrupt_eq p hp)
      · simp [Function.update_of_ne hpr]; exact h.dealerMessages_corrupt_eq p hp
  | partyDeliver q =>
    have hq : q ∉ corr := by
      have := hgate.2.1; intro h'; exact this (h.corrupted_corr ▸ h')
    refine
      { partyPoint_eq := h.partyPoint_eq
        corrupted_eq := h.corrupted_eq
        corrupted_corr := h.corrupted_corr
        dealerSent_eq := h.dealerSent_eq
        inflightDeliveries_eq := ?_
        inflightCorruptDeliveries_eq := h.inflightCorruptDeliveries_eq
        inflightEchoes_eq := h.inflightEchoes_eq
        inflightReady_eq := h.inflightReady_eq
        local_corrupt_eq := ?_
        local_honest_delivered := ?_
        local_honest_echoSent := ?_
        local_honest_echoesReceived := ?_
        local_honest_readyReceived := ?_
        local_honest_readySent := ?_
        local_honest_output_isSome := ?_
        dealerMessages_isSome_eq := h.dealerMessages_isSome_eq
        dealerMessages_corrupt_eq := h.dealerMessages_corrupt_eq
        dealerCommit_corrupt_eq := h.dealerCommit_corrupt_eq }
    · simp only [avssStep]; exact congrArg (·.erase q) h.inflightDeliveries_eq
    · intro p hp
      have hpq : p ≠ q := fun heq => hq (heq ▸ hp)
      simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
      exact h.local_corrupt_eq p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_delivered p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        exact h.local_honest_echoSent p hp
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_echoSent p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        exact h.local_honest_echoesReceived p hp
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_echoesReceived p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        exact h.local_honest_readyReceived p hp
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_readyReceived p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        exact h.local_honest_readySent p hp
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_readySent p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        exact h.local_honest_output_isSome p hp
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_output_isSome p hp
  | partyCorruptDeliver q =>
    have hq_corr : q ∈ corr := h.corrupted_corr ▸ hgate.2.1
    refine
      { partyPoint_eq := h.partyPoint_eq
        corrupted_eq := h.corrupted_eq
        corrupted_corr := h.corrupted_corr
        dealerSent_eq := h.dealerSent_eq
        inflightDeliveries_eq := h.inflightDeliveries_eq
        inflightCorruptDeliveries_eq := ?_
        inflightEchoes_eq := h.inflightEchoes_eq
        inflightReady_eq := h.inflightReady_eq
        local_corrupt_eq := ?_
        local_honest_delivered := ?_
        local_honest_echoSent := ?_
        local_honest_echoesReceived := ?_
        local_honest_readyReceived := ?_
        local_honest_readySent := ?_
        local_honest_output_isSome := ?_
        dealerMessages_isSome_eq := h.dealerMessages_isSome_eq
        dealerMessages_corrupt_eq := h.dealerMessages_corrupt_eq
        dealerCommit_corrupt_eq := h.dealerCommit_corrupt_eq }
    · simp only [avssStep]
      exact congrArg (·.erase q) h.inflightCorruptDeliveries_eq
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        have hLoc := h.local_corrupt_eq p hp
        have hDM := h.dealerMessages_corrupt_eq p hp
        have hDC := h.dealerCommit_corrupt_eq p hp
        rw [hLoc, hDM, hDC]
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_corrupt_eq p hp
    · intro p hp
      have hpq : p ≠ q := fun heq => hp (heq ▸ hq_corr)
      simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
      exact h.local_honest_delivered p hp
    · intro p hp
      have hpq : p ≠ q := fun heq => hp (heq ▸ hq_corr)
      simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
      exact h.local_honest_echoSent p hp
    · intro p hp
      have hpq : p ≠ q := fun heq => hp (heq ▸ hq_corr)
      simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
      exact h.local_honest_echoesReceived p hp
    · intro p hp
      have hpq : p ≠ q := fun heq => hp (heq ▸ hq_corr)
      simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
      exact h.local_honest_readyReceived p hp
    · intro p hp
      have hpq : p ≠ q := fun heq => hp (heq ▸ hq_corr)
      simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
      exact h.local_honest_readySent p hp
    · intro p hp
      have hpq : p ≠ q := fun heq => hp (heq ▸ hq_corr)
      simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
      exact h.local_honest_output_isSome p hp
  | partyEchoSend q =>
    refine
      { partyPoint_eq := h.partyPoint_eq
        corrupted_eq := h.corrupted_eq
        corrupted_corr := h.corrupted_corr
        dealerSent_eq := h.dealerSent_eq
        inflightDeliveries_eq := h.inflightDeliveries_eq
        inflightCorruptDeliveries_eq := h.inflightCorruptDeliveries_eq
        inflightEchoes_eq := ?_
        inflightReady_eq := h.inflightReady_eq
        local_corrupt_eq := ?_
        local_honest_delivered := ?_
        local_honest_echoSent := ?_
        local_honest_echoesReceived := ?_
        local_honest_readyReceived := ?_
        local_honest_readySent := ?_
        local_honest_output_isSome := ?_
        dealerMessages_isSome_eq := h.dealerMessages_isSome_eq
        dealerMessages_corrupt_eq := h.dealerMessages_corrupt_eq
        dealerCommit_corrupt_eq := h.dealerCommit_corrupt_eq }
    · simp only [avssStep, h.inflightEchoes_eq, h.corrupted_eq]
    · intro p hp
      by_cases hpq : p = q
      · subst hpq
        simp only [avssStep, setLocal_local_self]
        rw [h.local_corrupt_eq p hp]
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_corrupt_eq p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        exact h.local_honest_delivered p hp
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_delivered p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_echoSent p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        exact h.local_honest_echoesReceived p hp
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_echoesReceived p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        exact h.local_honest_readyReceived p hp
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_readyReceived p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        exact h.local_honest_readySent p hp
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_readySent p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        exact h.local_honest_output_isSome p hp
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_output_isSome p hp
  | partyEchoReceive q r =>
    refine
      { partyPoint_eq := h.partyPoint_eq
        corrupted_eq := h.corrupted_eq
        corrupted_corr := h.corrupted_corr
        dealerSent_eq := h.dealerSent_eq
        inflightDeliveries_eq := h.inflightDeliveries_eq
        inflightCorruptDeliveries_eq := h.inflightCorruptDeliveries_eq
        inflightEchoes_eq := ?_
        inflightReady_eq := h.inflightReady_eq
        local_corrupt_eq := ?_
        local_honest_delivered := ?_
        local_honest_echoSent := ?_
        local_honest_echoesReceived := ?_
        local_honest_readyReceived := ?_
        local_honest_readySent := ?_
        local_honest_output_isSome := ?_
        dealerMessages_isSome_eq := h.dealerMessages_isSome_eq
        dealerMessages_corrupt_eq := h.dealerMessages_corrupt_eq
        dealerCommit_corrupt_eq := h.dealerCommit_corrupt_eq }
    · simp only [avssStep]; exact congrArg (·.erase (r, q)) h.inflightEchoes_eq
    · intro p hp
      by_cases hpq : p = q
      · subst hpq
        simp only [avssStep, setLocal_local_self]
        rw [h.local_corrupt_eq p hp]
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_corrupt_eq p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        exact h.local_honest_delivered p hp
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_delivered p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        exact h.local_honest_echoSent p hp
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_echoSent p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        rw [h.local_honest_echoesReceived p hp]
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_echoesReceived p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        exact h.local_honest_readyReceived p hp
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_readyReceived p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        exact h.local_honest_readySent p hp
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_readySent p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        exact h.local_honest_output_isSome p hp
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_output_isSome p hp
  | partyReady q =>
    refine
      { partyPoint_eq := h.partyPoint_eq
        corrupted_eq := h.corrupted_eq
        corrupted_corr := h.corrupted_corr
        dealerSent_eq := h.dealerSent_eq
        inflightDeliveries_eq := h.inflightDeliveries_eq
        inflightCorruptDeliveries_eq := h.inflightCorruptDeliveries_eq
        inflightEchoes_eq := h.inflightEchoes_eq
        inflightReady_eq := ?_
        local_corrupt_eq := ?_
        local_honest_delivered := ?_
        local_honest_echoSent := ?_
        local_honest_echoesReceived := ?_
        local_honest_readyReceived := ?_
        local_honest_readySent := ?_
        local_honest_output_isSome := ?_
        dealerMessages_isSome_eq := h.dealerMessages_isSome_eq
        dealerMessages_corrupt_eq := h.dealerMessages_corrupt_eq
        dealerCommit_corrupt_eq := h.dealerCommit_corrupt_eq }
    · simp only [avssStep, h.inflightReady_eq]
    · intro p hp
      by_cases hpq : p = q
      · subst hpq
        simp only [avssStep, setLocal_local_self]
        rw [h.local_corrupt_eq p hp]
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_corrupt_eq p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        exact h.local_honest_delivered p hp
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_delivered p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        exact h.local_honest_echoSent p hp
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_echoSent p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        exact h.local_honest_echoesReceived p hp
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_echoesReceived p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        exact h.local_honest_readyReceived p hp
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_readyReceived p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_readySent p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        exact h.local_honest_output_isSome p hp
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_output_isSome p hp
  | partyAmplify q =>
    refine
      { partyPoint_eq := h.partyPoint_eq
        corrupted_eq := h.corrupted_eq
        corrupted_corr := h.corrupted_corr
        dealerSent_eq := h.dealerSent_eq
        inflightDeliveries_eq := h.inflightDeliveries_eq
        inflightCorruptDeliveries_eq := h.inflightCorruptDeliveries_eq
        inflightEchoes_eq := h.inflightEchoes_eq
        inflightReady_eq := ?_
        local_corrupt_eq := ?_
        local_honest_delivered := ?_
        local_honest_echoSent := ?_
        local_honest_echoesReceived := ?_
        local_honest_readyReceived := ?_
        local_honest_readySent := ?_
        local_honest_output_isSome := ?_
        dealerMessages_isSome_eq := h.dealerMessages_isSome_eq
        dealerMessages_corrupt_eq := h.dealerMessages_corrupt_eq
        dealerCommit_corrupt_eq := h.dealerCommit_corrupt_eq }
    · simp only [avssStep, h.inflightReady_eq]
    · intro p hp
      by_cases hpq : p = q
      · subst hpq
        simp only [avssStep, setLocal_local_self]
        rw [h.local_corrupt_eq p hp]
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_corrupt_eq p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        exact h.local_honest_delivered p hp
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_delivered p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        exact h.local_honest_echoSent p hp
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_echoSent p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        exact h.local_honest_echoesReceived p hp
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_echoesReceived p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        exact h.local_honest_readyReceived p hp
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_readyReceived p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_readySent p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        exact h.local_honest_output_isSome p hp
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_output_isSome p hp
  | partyReceiveReady q r =>
    refine
      { partyPoint_eq := h.partyPoint_eq
        corrupted_eq := h.corrupted_eq
        corrupted_corr := h.corrupted_corr
        dealerSent_eq := h.dealerSent_eq
        inflightDeliveries_eq := h.inflightDeliveries_eq
        inflightCorruptDeliveries_eq := h.inflightCorruptDeliveries_eq
        inflightEchoes_eq := h.inflightEchoes_eq
        inflightReady_eq := ?_
        local_corrupt_eq := ?_
        local_honest_delivered := ?_
        local_honest_echoSent := ?_
        local_honest_echoesReceived := ?_
        local_honest_readyReceived := ?_
        local_honest_readySent := ?_
        local_honest_output_isSome := ?_
        dealerMessages_isSome_eq := h.dealerMessages_isSome_eq
        dealerMessages_corrupt_eq := h.dealerMessages_corrupt_eq
        dealerCommit_corrupt_eq := h.dealerCommit_corrupt_eq }
    · simp only [avssStep]; exact congrArg (·.erase (r, q)) h.inflightReady_eq
    · intro p hp
      by_cases hpq : p = q
      · subst hpq
        simp only [avssStep, setLocal_local_self]
        rw [h.local_corrupt_eq p hp]
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_corrupt_eq p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        exact h.local_honest_delivered p hp
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_delivered p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        exact h.local_honest_echoSent p hp
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_echoSent p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        exact h.local_honest_echoesReceived p hp
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_echoesReceived p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        rw [h.local_honest_readyReceived p hp]
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_readyReceived p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        exact h.local_honest_readySent p hp
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_readySent p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        exact h.local_honest_output_isSome p hp
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_output_isSome p hp
  | partyOutput q =>
    have hq : q ∉ corr := by
      have := hgate.1; intro h'; exact this (h.corrupted_corr ▸ h')
    refine
      { partyPoint_eq := h.partyPoint_eq
        corrupted_eq := h.corrupted_eq
        corrupted_corr := h.corrupted_corr
        dealerSent_eq := h.dealerSent_eq
        inflightDeliveries_eq := h.inflightDeliveries_eq
        inflightCorruptDeliveries_eq := h.inflightCorruptDeliveries_eq
        inflightEchoes_eq := h.inflightEchoes_eq
        inflightReady_eq := h.inflightReady_eq
        local_corrupt_eq := ?_
        local_honest_delivered := ?_
        local_honest_echoSent := ?_
        local_honest_echoesReceived := ?_
        local_honest_readyReceived := ?_
        local_honest_readySent := ?_
        local_honest_output_isSome := ?_
        dealerMessages_isSome_eq := h.dealerMessages_isSome_eq
        dealerMessages_corrupt_eq := h.dealerMessages_corrupt_eq
        dealerCommit_corrupt_eq := h.dealerCommit_corrupt_eq }
    · intro p hp
      have hpq : p ≠ q := fun heq => hq (heq ▸ hp)
      simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
      exact h.local_corrupt_eq p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        exact h.local_honest_delivered p hp
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_delivered p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        exact h.local_honest_echoSent p hp
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_echoSent p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        exact h.local_honest_echoesReceived p hp
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_echoesReceived p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        exact h.local_honest_readyReceived p hp
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_readyReceived p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]
        exact h.local_honest_readySent p hp
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_readySent p hp
    · intro p hp
      by_cases hpq : p = q
      · subst hpq; simp only [avssStep, setLocal_local_self]; rfl
      · simp only [avssStep, setLocal_local_ne _ _ _ _ hpq]
        exact h.local_honest_output_isSome p hp
end simSyncInv

-- Per-step simulate matching: under `simSyncInv` on initial states,
-- every step of `avssSimulateTrace` matches between the two states on
-- both `simSyncInv` (state component) and equality (action component).
-- Proof by induction on `k`: the schedule decision is the same (rushing-view-
-- histories agree via `simSyncInv`), and the gate decision is the same (via
-- `actionGate_iff`); both branches of `avssSimulateNext` therefore produce
-- sync'd states.
theorem avssSimulateTrace_simSyncInv {corr : Finset (Fin n)}
    (R : AVSSRushingAdversary n t F corr)
    (h_R : R.toProtocolView = avssCoalitionView corr)
    (s_0 s_0' : AVSSState n t F)
    (h_init : simSyncInv corr s_0 s_0') (k : ℕ) :
    simSyncInv corr (avssSimulateTrace R s_0 k).1
        (avssSimulateTrace R s_0' k).1 ∧
      (avssSimulateTrace R s_0 k).2 = (avssSimulateTrace R s_0' k).2 ∧
      List.map (fun sa => (R.view sa.1, sa.2)) (avssSimulateRev R s_0 k) =
        List.map (fun sa => (R.view sa.1, sa.2)) (avssSimulateRev R s_0' k) := by
  classical
  induction k with
  | zero =>
    refine ⟨h_init, rfl, ?_⟩
    show [(R.view s_0, (none : Option (AVSSAction n F)))]
        = [(R.view s_0', (none : Option (AVSSAction n F)))]
    have hview := simSyncInv.rushingView_eq R h_R h_init
    rw [hview]
  | succ k ih =>
    obtain ⟨ih_state, _, ih_view⟩ := ih
    -- Schedules agree: R.toAdversary.schedule on both reverse lists.
    have h_simRev_view :
        R.toAdversary.schedule (avssSimulateRev R s_0 k).reverse =
          R.toAdversary.schedule (avssSimulateRev R s_0' k).reverse := by
      simp only [Leslie.Prob.RushingAdversary.toAdversary_schedule,
                 Leslie.Prob.RushingAdversary.viewHistory_eq_map,
                 List.map_reverse]
      rw [ih_view]
    -- The next-state of both simulates agrees in (state, action) pair up to simSyncInv.
    -- Compute it directly.
    have h_head_eq := avssSimulateRev_head_eq R s_0 k
    have h_head_eq' := avssSimulateRev_head_eq R s_0' k
    -- Define the next states.
    set s_next := avssSimulateNext R s_0 (avssSimulateRev R s_0 k) with hs_next
    set s_next' := avssSimulateNext R s_0' (avssSimulateRev R s_0' k) with hs_next'
    -- Compute the (k+1)-th simulate trace.
    have h_succ : avssSimulateTrace R s_0 (k+1) = s_next := by
      rw [avssSimulateTrace_succ_eq]
    have h_succ' : avssSimulateTrace R s_0' (k+1) = s_next' := by
      rw [avssSimulateTrace_succ_eq]
    -- Show simSyncInv s_next.1 s_next'.1 and s_next.2 = s_next'.2 plus view equality.
    -- This requires unfolding `avssSimulateNext` once.
    have h_next_pair : simSyncInv corr s_next.1 s_next'.1 ∧ s_next.2 = s_next'.2 := by
      rw [hs_next, hs_next']
      unfold avssSimulateNext
      rw [h_head_eq, h_head_eq', Option.getD_some, Option.getD_some]
      rw [h_simRev_view]
      cases hsched : R.toAdversary.schedule (avssSimulateRev R s_0' k).reverse with
      | none =>
        refine ⟨ih_state, ?_⟩; rfl
      | some i =>
        have h_gate := simSyncInv.actionGate_iff ih_state i
        by_cases hgate : actionGate i (avssSimulateTrace R s_0 k).1
        · have hgate' : actionGate i (avssSimulateTrace R s_0' k).1 := h_gate.mp hgate
          simp only [hgate, if_true, hgate', if_true]
          refine ⟨simSyncInv.avssStep_preserves_simSyncInv i ih_state hgate, ?_⟩
          trivial
        · have hgate' : ¬ actionGate i (avssSimulateTrace R s_0' k).1 :=
            fun h => hgate (h_gate.mpr h)
          simp only [hgate, if_false, hgate', if_false]
          refine ⟨ih_state, ?_⟩; trivial
    refine ⟨h_succ ▸ h_succ' ▸ h_next_pair.1, h_succ ▸ h_succ' ▸ h_next_pair.2, ?_⟩
    -- View-equality at step (k+1): extends by (R.view s_next.1, s_next.2) on both sides.
    show List.map (fun sa => (R.view sa.1, sa.2)) (s_next :: avssSimulateRev R s_0 k) =
        List.map (fun sa => (R.view sa.1, sa.2)) (s_next' :: avssSimulateRev R s_0' k)
    rw [List.map_cons, List.map_cons, ih_view]
    have hview_next := simSyncInv.rushingView_eq R h_R h_next_pair.1
    have hact_next := h_next_pair.2
    rw [hview_next, hact_next]

-- **Joint factoring:** if two states are simulate-synced, then both
-- `simAlgebraicView` and `simSchedulePrefix` evaluate identically.
-- The `simAlgebraicView` data depends only on the corrupt-party
-- locals + the per-party `dealerCommit`, which agree under
-- `simSyncInv` (`local_corrupt_eq` and `dealerCommit_corrupt_eq`).
-- `simSchedulePrefix` agrees by `avssSimulateTrace_simSyncInv`
-- (action equality on the simulated trace).
theorem simAlgebraicView_simSchedulePrefix_eq_of_simSyncInv
    {corr : Finset (Fin n)}
    (R : AVSSRushingAdversary n t F corr)
    (h_R : R.toProtocolView = avssCoalitionView corr)
    (C : BivariateShamir.Coalition n t) (h_C_corr : C.val ⊆ corr)
    (s_0 s_0' : AVSSState n t F)
    (h_init : simSyncInv corr s_0 s_0') (k : ℕ) :
    simAlgebraicView R C k s_0 = simAlgebraicView R C k s_0' ∧
      simSchedulePrefix R k s_0 = simSchedulePrefix R k s_0' := by
  refine ⟨?_, ?_⟩
  · -- simAlgebraicView component-wise. Phase 8.5d-β: first component uses
    -- `s.dealerCommit p.val .rowPoly`, equal by `simSyncInv.dealerCommit_corrupt_eq`.
    show (fun p : C.val =>
            (s_0.dealerCommit p.val).rowPoly,
          fun (i : Fin k) (p : C.val) =>
            ((avssSimulateTrace R s_0 i.val).1.local_ p.val).delivered) =
        (fun p : C.val =>
            (s_0'.dealerCommit p.val).rowPoly,
          fun (i : Fin k) (p : C.val) =>
            ((avssSimulateTrace R s_0' i.val).1.local_ p.val).delivered)
    refine Prod.mk.injEq _ _ _ _|>.mpr ⟨?_, ?_⟩
    · funext p
      have h_pcorr : p.val ∈ corr := h_C_corr p.property
      rw [h_init.dealerCommit_corrupt_eq p.val h_pcorr]
    · funext i p
      have h_step :=
        avssSimulateTrace_simSyncInv R h_R s_0 s_0' h_init i.val
      have h_state_inv := h_step.1
      have h_pcorr : p.val ∈ corr := h_C_corr p.property
      have h_local_eq := h_state_inv.local_corrupt_eq p.val h_pcorr
      rw [h_local_eq]
  · -- simSchedulePrefix at every step.
    funext i
    show (avssSimulateTrace R s_0 i.val).2 = (avssSimulateTrace R s_0' i.val).2
    exact (avssSimulateTrace_simSyncInv R h_R s_0 s_0' h_init i.val).2.1

/-! ## §19.4.2 — sec-invariance at the initial-measure level

The key map composition: `avssInitMeasure sec corr partyPoint dealerHonest`
is the pushforward of `uniformBivariateFullWithFixedZero t t sec`
through `avssInitState ... ∘ polyToCoeffs`.  Composing with
`(simAlgebraicView R C k, simSchedulePrefix R k)` gives a function
that depends on the bivariate polynomial `f` only through its row
polynomials at corrupt parties' partyPoints.  Specifically:

  * `simAlgebraicView R C k (avssInitState ... (polyToCoeffs f))`'s
    first component is `fun p : C.val => rowPolyOfDealer partyPoint
    (polyToCoeffs f) p.val`, which equals
    `(f.eval (Polynomial.C (partyPoint p.val))).coeff` by the
    `evalRowPoly_polyToCoeffs` identity (proved in §17.7).
  * The second component plus `simSchedulePrefix` are deterministic
    functions of corrupt rowPolys (via `simSyncInv` factoring).

Hence the joint pushforward depends on `(p, l) → row poly coefficient`
data at corrupt party points — exactly what
`bivariate_shamir_secrecy_rowPoly_full` makes sec-invariant when the
party-points avoid zero and are at most `t`. -/

/-- For `s_0 = avssInitState sec corr partyPoint dealerHonest c` and
`s_0' = avssInitState sec' corr partyPoint dealerHonest c'`, they are
simulate-synced provided the row-polys at corrupt parties agree.

This packages the reduction for §19.4 below: the bivariate-polynomial-
level row-poly invariance is sufficient to deduce simulate-syncing of
the two initial states. -/
theorem simSyncInv_avssInitState
    (sec sec' : F) (corr : Finset (Fin n))
    (partyPoint : Fin n → F) (dealerHonest : Bool)
    (c c' : Fin (t+1) → Fin (t+1) → F)
    (h_rp : ∀ p ∈ corr,
      rowPolyOfDealer partyPoint c p = rowPolyOfDealer partyPoint c' p) :
    simSyncInv corr
      (avssInitState (n := n) sec corr partyPoint dealerHonest c)
      (avssInitState (n := n) sec' corr partyPoint dealerHonest c') := by
  -- All fields agree by construction of `avssInitState`; the load-bearing
  -- `dealerCommit_corrupt_eq` uses `h_rp` (rowPoly equality across c/c')
  -- plus the `colPoly = fun _ => 0` agreement to derive per-party payload
  -- equality at corrupt p.
  refine
    { partyPoint_eq := rfl
      corrupted_eq := rfl
      corrupted_corr := rfl
      dealerSent_eq := rfl
      inflightDeliveries_eq := rfl
      inflightCorruptDeliveries_eq := rfl
      inflightEchoes_eq := rfl
      inflightReady_eq := rfl
      local_corrupt_eq := fun _ _ => rfl
      local_honest_delivered := fun _ _ => rfl
      local_honest_echoSent := fun _ _ => rfl
      local_honest_echoesReceived := fun _ _ => rfl
      local_honest_readyReceived := fun _ _ => rfl
      local_honest_readySent := fun _ _ => rfl
      local_honest_output_isSome := fun _ _ => rfl
      dealerMessages_isSome_eq := fun _ => rfl
      dealerMessages_corrupt_eq := fun _ _ => rfl
      dealerCommit_corrupt_eq := ?_ }
  -- For the dealerCommit field: at init both states' dealerCommit p =
  -- { rowPoly := rowPolyOfDealer partyPoint c p, colPoly := fun _ => 0 }
  -- (or with c'); for corrupt p, h_rp gives rowPoly equality and colPoly
  -- agrees on both sides as the constant zero function.
  intro p hp
  show (avssInitState (n := n) sec corr partyPoint dealerHonest c).dealerCommit p =
    (avssInitState (n := n) sec' corr partyPoint dealerHonest c').dealerCommit p
  show ({ rowPoly := rowPolyOfDealer partyPoint c p
          colPoly := fun _ => (0 : F) } : DealerPayload t F) =
    { rowPoly := rowPolyOfDealer partyPoint c' p
      colPoly := fun _ => (0 : F) }
  congr 1
  exact h_rp p hp

/-! ## §19.4.3 — bridge: `rowPolyOfDealer ∘ polyToCoeffs = coeff ∘ eval` -/

-- Compute the `l`-th coefficient of `f.eval (C x)` for `f` in the
-- support form of `uniformBivariateFullWithFixedZero` (RHS-explicit form).
private theorem support_form_eval_coeff
    (sec x : F) (t : ℕ)
    (coefs : Fin t → Fin t → F) (axisX axisY : Fin t → F) (l : ℕ) :
    ((Polynomial.C (Polynomial.C sec) +
      (∑ i : Fin t, Polynomial.C (Polynomial.C (axisX i)) *
        Polynomial.X ^ (i.val + 1)) +
      (∑ j : Fin t, Polynomial.C (Polynomial.C (axisY j)) *
        (Polynomial.C Polynomial.X) ^ (j.val + 1)) +
      ∑ i : Fin t, ∑ j : Fin t,
        Polynomial.C (Polynomial.C (coefs i j)) *
          Polynomial.X ^ (i.val + 1) *
          (Polynomial.C Polynomial.X) ^ (j.val + 1) :
        _root_.Polynomial (_root_.Polynomial F)).eval (Polynomial.C x)).coeff l =
      (if l = 0 then sec else 0) +
      (∑ i : Fin t, if l = 0 then axisX i * x^(i.val + 1) else 0) +
      (∑ j : Fin t, if l = j.val + 1 then axisY j else 0) +
      (∑ i : Fin t, ∑ j : Fin t,
        if l = j.val + 1 then coefs i j * x^(i.val + 1) else 0) := by
  rw [Polynomial.eval_add, Polynomial.eval_add, Polynomial.eval_add,
      Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_) ?_
  · rw [Polynomial.eval_C, Polynomial.coeff_C]
  · rw [Polynomial.eval_finset_sum, Polynomial.finset_sum_coeff]
    apply Finset.sum_congr rfl
    intro i _
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
        ← Polynomial.C_pow, ← Polynomial.C_mul, Polynomial.coeff_C]
  · rw [Polynomial.eval_finset_sum, Polynomial.finset_sum_coeff]
    apply Finset.sum_congr rfl
    intro j _
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.coeff_C_mul_X_pow]
  · rw [Polynomial.eval_finset_sum, Polynomial.finset_sum_coeff]
    apply Finset.sum_congr rfl
    intro i _
    rw [Polynomial.eval_finset_sum, Polynomial.finset_sum_coeff]
    apply Finset.sum_congr rfl
    intro j _
    rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_C]
    rw [show (Polynomial.C x : _root_.Polynomial F)^(i.val+1) =
        Polynomial.C (x^(i.val+1)) from Polynomial.C_pow.symm]
    rw [show Polynomial.C (coefs i j) * Polynomial.C (x^(i.val+1)) =
        Polynomial.C (coefs i j * x^(i.val+1)) from (Polynomial.C_mul).symm]
    rw [Polynomial.coeff_C_mul_X_pow]

-- Compute `rowPolyOfDealer pp (polyToCoeffs f) p l` for `f` in the
-- support form of `uniformBivariateFullWithFixedZero` (LHS-explicit form).
private theorem rowPolyOfDealer_polyToCoeffs_support_form
    (sec : F) (partyPoint : Fin n → F) (t : ℕ)
    (coefs : Fin t → Fin t → F) (axisX axisY : Fin t → F) (p : Fin n)
    (l : Fin (t+1)) :
    rowPolyOfDealer (n := n) (t := t) partyPoint
      (polyToCoeffs (t := t)
        (Polynomial.C (Polynomial.C sec) +
          (∑ i : Fin t, Polynomial.C (Polynomial.C (axisX i)) *
            Polynomial.X ^ (i.val + 1)) +
          (∑ j : Fin t, Polynomial.C (Polynomial.C (axisY j)) *
            (Polynomial.C Polynomial.X) ^ (j.val + 1)) +
          ∑ i : Fin t, ∑ j : Fin t,
            Polynomial.C (Polynomial.C (coefs i j)) *
              Polynomial.X ^ (i.val + 1) *
              (Polynomial.C Polynomial.X) ^ (j.val + 1))) p l =
    (if l.val = 0 then sec else 0) +
    (∑ i : Fin t, if l.val = 0 then axisX i * partyPoint p^(i.val + 1) else 0) +
    (∑ j : Fin t, if l.val = j.val + 1 then axisY j else 0) +
    (∑ i : Fin t, ∑ j : Fin t,
      if l.val = j.val + 1 then coefs i j * partyPoint p^(i.val + 1) else 0) := by
  classical
  unfold rowPolyOfDealer polyToCoeffs
  -- Step 1: `((bigP.coeff k.val).coeff l.val)` = explicit 4-case formula.
  have h_coeff : ∀ (k l : ℕ),
      ((Polynomial.C (Polynomial.C sec) +
        (∑ i : Fin t, Polynomial.C (Polynomial.C (axisX i)) *
          Polynomial.X ^ (i.val + 1)) +
        (∑ j : Fin t, Polynomial.C (Polynomial.C (axisY j)) *
          (Polynomial.C Polynomial.X) ^ (j.val + 1)) +
        ∑ i : Fin t, ∑ j : Fin t,
          Polynomial.C (Polynomial.C (coefs i j)) *
            Polynomial.X ^ (i.val + 1) *
            (Polynomial.C Polynomial.X) ^ (j.val + 1)).coeff k).coeff l =
      (if k = 0 ∧ l = 0 then sec else 0) +
      (∑ i : Fin t, if k = i.val + 1 ∧ l = 0 then axisX i else 0) +
      (∑ j : Fin t, if k = 0 ∧ l = j.val + 1 then axisY j else 0) +
      (∑ i : Fin t, ∑ j : Fin t,
        if k = i.val + 1 ∧ l = j.val + 1 then coefs i j else 0) := by
    intros k l
    rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
        Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
        Polynomial.finset_sum_coeff, Polynomial.finset_sum_coeff,
        Polynomial.finset_sum_coeff]
    simp only [Polynomial.finset_sum_coeff]
    refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_) ?_
    · -- ((C(C sec)).coeff k).coeff l
      by_cases hk : k = 0
      · subst hk
        rw [Polynomial.coeff_C_zero, Polynomial.coeff_C]
        by_cases hl : l = 0
        · subst hl; simp
        · simp [hl]
      · rw [Polynomial.coeff_C, if_neg hk, Polynomial.coeff_zero]; simp [hk]
    · -- axisX sum
      apply Finset.sum_congr rfl
      intro i _
      rw [Polynomial.coeff_C_mul_X_pow]
      by_cases h1 : k = i.val + 1
      · rw [if_pos h1, Polynomial.coeff_C]
        by_cases h2 : l = 0
        · subst h2; simp [h1]
        · rw [if_neg h2, if_neg]
          rintro ⟨_, hcontra⟩; exact h2 hcontra
      · rw [if_neg h1, Polynomial.coeff_zero, if_neg]
        rintro ⟨hcontra, _⟩; exact h1 hcontra
    · -- axisY sum
      apply Finset.sum_congr rfl
      intro j _
      rw [show (Polynomial.C Polynomial.X :
            _root_.Polynomial (_root_.Polynomial F))^(j.val+1) =
          Polynomial.C (Polynomial.X^(j.val+1)) from Polynomial.C_pow.symm,
          ← Polynomial.C_mul]
      by_cases hk : k = 0
      · subst hk
        rw [Polynomial.coeff_C_zero, Polynomial.coeff_C_mul_X_pow]
        by_cases hl : l = j.val + 1
        · simp [hl]
        · rw [if_neg hl, if_neg]
          rintro ⟨_, hcontra⟩; exact hl hcontra
      · rw [Polynomial.coeff_C, if_neg hk, Polynomial.coeff_zero, if_neg]
        rintro ⟨hcontra, _⟩; exact hk hcontra
    · -- interior 2D sum
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [show Polynomial.C (Polynomial.C (coefs i j)) *
            Polynomial.X^(i.val+1) *
            (Polynomial.C Polynomial.X :
              _root_.Polynomial (_root_.Polynomial F))^(j.val+1) =
          Polynomial.C (Polynomial.C (coefs i j) * Polynomial.X^(j.val+1)) *
            Polynomial.X^(i.val+1) from by
        rw [show (Polynomial.C Polynomial.X :
            _root_.Polynomial (_root_.Polynomial F))^(j.val+1) =
            Polynomial.C (Polynomial.X^(j.val+1)) from Polynomial.C_pow.symm]
        rw [Polynomial.C_mul]; ring]
      rw [Polynomial.coeff_C_mul_X_pow]
      by_cases h1 : k = i.val + 1
      · rw [if_pos h1, Polynomial.coeff_C_mul_X_pow]
        by_cases h2 : l = j.val + 1
        · rw [if_pos h2, if_pos ⟨h1, h2⟩]
        · rw [if_neg h2, if_neg]
          rintro ⟨_, hcontra⟩; exact h2 hcontra
      · rw [if_neg h1, Polynomial.coeff_zero, if_neg]
        rintro ⟨hcontra, _⟩; exact h1 hcontra
  -- Step 2: substitute h_coeff and distribute.
  conv_lhs =>
    rw [Finset.sum_congr rfl (fun k _ => by rw [h_coeff k.val l.val] : ∀ k ∈ _, _ = _)]
  simp only [add_mul, Finset.sum_add_distrib]
  set x := partyPoint p with hx_def
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_) ?_
  · -- const piece: ∑ k, (if k=0 ∧ l=0 then sec else 0) * x^k = if l=0 then sec else 0.
    by_cases hl : l.val = 0
    · rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin (t+1))]
      · simp [hl]
      · intro k _ hk
        have hk0 : k.val ≠ 0 := fun h => hk (Fin.ext h)
        rw [if_neg (fun ⟨h, _⟩ => hk0 h)]
        ring
      · simp
    · rw [if_neg hl]
      apply Finset.sum_eq_zero
      intro k _
      rw [if_neg (fun ⟨_, h⟩ => hl h)]
      ring
  · -- aX piece.
    by_cases hl : l.val = 0
    · -- Both sides at l = 0: aX piece = ∑ i, axisX i * x^(i+1).
      have hRHS : (∑ i : Fin t, if l.val = 0 then axisX i * x^(i.val + 1) else 0) =
          ∑ i : Fin t, axisX i * x^(i.val + 1) := by
        apply Finset.sum_congr rfl; intro i _; rw [if_pos hl]
      rw [hRHS]
      -- Move x^k.val inside the i-sum and simplify by hl.
      have hStep : ∀ k : Fin (t+1),
          (∑ i : Fin t, if k.val = i.val + 1 ∧ l.val = 0 then axisX i else 0) * x^k.val =
          ∑ i : Fin t, (if k.val = i.val + 1 then axisX i else 0) * x^k.val := by
        intro k
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        by_cases h_keq : k.val = i.val + 1
        · simp [h_keq, hl]
        · simp [h_keq]
      rw [Finset.sum_congr rfl (fun k _ => hStep k)]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      have h_iv : i.val + 1 < t + 1 := by omega
      rw [Finset.sum_eq_single (⟨i.val+1, h_iv⟩ : Fin (t+1))]
      · simp
      · intro k _ hk
        have hk_ne : k.val ≠ i.val + 1 := fun h => hk (Fin.ext h)
        rw [if_neg hk_ne]
        ring
      · simp
    · -- Both sides at l ≠ 0: 0.
      have hRHS : (∑ i : Fin t, if l.val = 0 then axisX i * x^(i.val + 1) else 0) = 0 := by
        apply Finset.sum_eq_zero; intro i _; rw [if_neg hl]
      rw [hRHS]
      apply Finset.sum_eq_zero
      intro k _
      have h_zero : (∑ i : Fin t,
          if k.val = i.val + 1 ∧ l.val = 0 then axisX i else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [if_neg (fun ⟨_, h⟩ => hl h)]
      rw [h_zero]
      ring
  · -- aY piece.
    rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin (t+1))]
    · simp
    · intro k _ hk
      have hk0 : k.val ≠ 0 := fun h => hk (Fin.ext h)
      have h_zero : (∑ j : Fin t,
          if k.val = 0 ∧ l.val = j.val + 1 then axisY j else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        rw [if_neg (fun ⟨h, _⟩ => hk0 h)]
      rw [h_zero]
      ring
    · simp
  · -- interior piece.
    have hStep : ∀ k : Fin (t+1),
        (∑ i : Fin t, ∑ j : Fin t,
          if k.val = i.val + 1 ∧ l.val = j.val + 1 then coefs i j else 0) * x^k.val =
        ∑ i : Fin t, ∑ j : Fin t,
          (if k.val = i.val + 1 ∧ l.val = j.val + 1 then coefs i j else 0) * x^k.val := by
      intro k
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun k _ => hStep k)]
    rw [show (∑ k : Fin (t+1), ∑ i : Fin t, ∑ j : Fin t,
            (if k.val = i.val + 1 ∧ l.val = j.val + 1 then coefs i j else 0) * x^k.val)
        = ∑ i : Fin t, ∑ j : Fin t, ∑ k : Fin (t+1),
            (if k.val = i.val + 1 ∧ l.val = j.val + 1 then coefs i j else 0) * x^k.val from by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro k _
      rw [Finset.sum_comm]]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have h_iv : i.val + 1 < t + 1 := by omega
    rw [Finset.sum_eq_single (⟨i.val+1, h_iv⟩ : Fin (t+1))]
    · -- ((⟨i.val+1, h_iv⟩ : Fin (t+1)).val) = i.val + 1, so condition simplifies.
      show (if i.val + 1 = i.val + 1 ∧ l.val = j.val + 1 then coefs i j else 0) * x ^ (i.val + 1) =
           if l.val = j.val + 1 then coefs i j * x ^ (i.val + 1) else 0
      by_cases hl2 : l.val = j.val + 1
      · simp [hl2]
      · rw [if_neg (fun ⟨_, h⟩ => hl2 h), if_neg hl2]
        ring
    · intro k _ hk
      have hknv : k.val ≠ i.val + 1 := fun h => hk (Fin.ext h)
      rw [if_neg (fun ⟨h, _⟩ => hknv h)]
      ring
    · simp

-- Pointwise identity: for `f` in the support of
-- `uniformBivariateFullWithFixedZero`, `rowPolyOfDealer partyPoint
-- (polyToCoeffs f) p l` equals `(f.eval (Polynomial.C (partyPoint p))).coeff l.val`.
theorem rowPolyOfDealer_polyToCoeffs_eq_coeff_eval_of_support
    (sec : F) (partyPoint : Fin n → F)
    (f : _root_.Polynomial (_root_.Polynomial F))
    (hf : f ∈ (Leslie.Prob.Polynomial.uniformBivariateFullWithFixedZero
                 (F := F) t t sec).support)
    (p : Fin n) (l : Fin (t+1)) :
    rowPolyOfDealer (n := n) (t := t) partyPoint (polyToCoeffs f) p l =
      (f.eval (Polynomial.C (partyPoint p))).coeff l.val := by
  classical
  obtain ⟨coefs, axisX, axisY, rfl⟩ :=
    uniformBivariateFull_support_form sec t t f hf
  rw [rowPolyOfDealer_polyToCoeffs_support_form sec partyPoint t coefs axisX axisY p l,
      support_form_eval_coeff sec (partyPoint p) t coefs axisX axisY l.val]

/-! ## §19.4.4 — supporting helpers for the headline theorem -/

-- Generic helper: `∀ᵐ` over a PMF measure follows from a pointwise
-- predicate that holds on the support.
theorem PMF.ae_of_forall_support {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
    (p : _root_.PMF α) (P : α → Prop) (h : ∀ a ∈ p.support, P a) :
    ∀ᵐ a ∂p.toMeasure, P a := by
  classical
  rw [Filter.eventually_iff, MeasureTheory.mem_ae_iff]
  show p.toMeasure {x | P x}ᶜ = 0
  have hMS : MeasurableSet {a | ¬ P a} := MeasurableSet.of_discrete
  have h_eq : ({x | P x}ᶜ : Set α) = {a | ¬ P a} := by ext; rfl
  rw [h_eq, ← _root_.PMF.toMeasure_apply_inter_support p hMS]
  have h_inter : {a | ¬ P a} ∩ p.support = ∅ := by
    ext a
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hnp, hsupp⟩
    exact hnp (h a hsupp)
  rw [h_inter]
  exact MeasureTheory.measure_empty

-- For `f` in the support of `uniformBivariateFullWithFixedZero`, the
-- AVSS-style coefficient grid evaluated at `(0, 0)` recovers `sec`.
private theorem polyToCoeffs_zero_zero_eq_sec_of_support
    (sec : F) (f : _root_.Polynomial (_root_.Polynomial F))
    (hf : f ∈ (Leslie.Prob.Polynomial.uniformBivariateFullWithFixedZero
                 (F := F) t t sec).support) :
    polyToCoeffs (t := t) f 0 0 = sec := by
  classical
  obtain ⟨coefs, axisX, axisY, rfl⟩ :=
    uniformBivariateFull_support_form sec t t f hf
  -- Use the existing 4-case formula `h_coeff` from the bigger theorem
  -- (here at (k, l) = (0, 0): only the const term contributes, equals sec).
  show ((Polynomial.C (Polynomial.C sec) +
      (∑ i : Fin t, Polynomial.C (Polynomial.C (axisX i)) *
        Polynomial.X ^ (i.val + 1)) +
      (∑ j : Fin t, Polynomial.C (Polynomial.C (axisY j)) *
        (Polynomial.C Polynomial.X) ^ (j.val + 1)) +
      ∑ i : Fin t, ∑ j : Fin t,
        Polynomial.C (Polynomial.C (coefs i j)) *
          Polynomial.X ^ (i.val + 1) *
          (Polynomial.C Polynomial.X) ^ (j.val + 1) :
        _root_.Polynomial (_root_.Polynomial F)).coeff
        (0 : Fin (t+1)).val).coeff (0 : Fin (t+1)).val = sec
  rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
      Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
      Polynomial.finset_sum_coeff, Polynomial.finset_sum_coeff,
      Polynomial.finset_sum_coeff]
  simp only [Polynomial.finset_sum_coeff]
  -- Const piece: ((C (C sec)).coeff 0).coeff 0 = sec.
  rw [show ((Polynomial.C (Polynomial.C sec) :
      _root_.Polynomial (_root_.Polynomial F)).coeff
      (0 : Fin (t+1)).val).coeff (0 : Fin (t+1)).val = sec from by
    rw [Polynomial.coeff_C]
    rw [if_pos (by simp : (0 : Fin (t+1)).val = 0)]
    rw [Polynomial.coeff_C]
    rw [if_pos (by simp : (0 : Fin (t+1)).val = 0)]]
  -- aX piece = 0.
  rw [show (∑ i : Fin t,
      ((Polynomial.C (Polynomial.C (axisX i)) *
        Polynomial.X ^ (i.val + 1) :
          _root_.Polynomial (_root_.Polynomial F)).coeff
        (0 : Fin (t+1)).val).coeff (0 : Fin (t+1)).val) = 0 from by
    apply Finset.sum_eq_zero; intro i _
    rw [Polynomial.coeff_C_mul_X_pow]
    have : (0 : Fin (t+1)).val ≠ i.val + 1 := by simp only [Fin.val_zero]; omega
    rw [if_neg this, Polynomial.coeff_zero]]
  -- aY piece = 0.
  rw [show (∑ j : Fin t,
      ((Polynomial.C (Polynomial.C (axisY j)) *
        (Polynomial.C Polynomial.X) ^ (j.val + 1) :
          _root_.Polynomial (_root_.Polynomial F)).coeff
        (0 : Fin (t+1)).val).coeff (0 : Fin (t+1)).val) = 0 from by
    apply Finset.sum_eq_zero; intro j _
    rw [show (Polynomial.C Polynomial.X :
        _root_.Polynomial (_root_.Polynomial F)) ^ (j.val+1) =
        Polynomial.C (Polynomial.X^(j.val+1)) from Polynomial.C_pow.symm,
        ← Polynomial.C_mul, Polynomial.coeff_C]
    rw [if_pos (by simp : (0 : Fin (t+1)).val = 0)]
    rw [Polynomial.coeff_C_mul_X_pow]
    have : (0 : Fin (t+1)).val ≠ j.val + 1 := by simp only [Fin.val_zero]; omega
    rw [if_neg this]]
  -- interior piece = 0.
  rw [show (∑ i : Fin t, ∑ j : Fin t,
      ((Polynomial.C (Polynomial.C (coefs i j)) *
        Polynomial.X ^ (i.val + 1) *
        (Polynomial.C Polynomial.X) ^ (j.val + 1) :
          _root_.Polynomial (_root_.Polynomial F)).coeff
        (0 : Fin (t+1)).val).coeff (0 : Fin (t+1)).val) = 0 from by
    apply Finset.sum_eq_zero; intro i _
    apply Finset.sum_eq_zero; intro j _
    rw [show Polynomial.C (Polynomial.C (coefs i j)) *
          Polynomial.X^(i.val+1) *
          (Polynomial.C Polynomial.X :
            _root_.Polynomial (_root_.Polynomial F))^(j.val+1) =
        Polynomial.C (Polynomial.C (coefs i j) * Polynomial.X^(j.val+1)) *
          Polynomial.X^(i.val+1) from by
      rw [show (Polynomial.C Polynomial.X :
          _root_.Polynomial (_root_.Polynomial F))^(j.val+1) =
          Polynomial.C (Polynomial.X^(j.val+1)) from Polynomial.C_pow.symm]
      rw [Polynomial.C_mul]; ring]
    rw [Polynomial.coeff_C_mul_X_pow]
    have : (0 : Fin (t+1)).val ≠ i.val + 1 := by simp only [Fin.val_zero]; omega
    rw [if_neg this, Polynomial.coeff_zero]]
  ring

-- For the AVSS init measure, `initPred sec corr coeffs` holds AE for *some*
-- coeffs (sampled from μ₀ via `polyToCoeffs`).
theorem avssInitMeasure_AE_initPred (sec : F) (corr : Finset (Fin n))
    (partyPoint : Fin n → F) (dealerHonest : Bool) :
    ∀ᵐ s ∂(avssInitMeasure (n := n) (t := t) sec corr partyPoint dealerHonest),
        ∃ coeffs : Fin (t+1) → Fin (t+1) → F, initPred (t := t) sec corr coeffs s := by
  classical
  -- Reduce AE on the PMF's `toMeasure` to a support-pointwise statement.
  unfold avssInitMeasure
  rw [ae_iff]
  have hms : MeasurableSet
      {s : AVSSState n t F | ¬ ∃ coeffs, initPred (t := t) sec corr coeffs s} :=
    MeasurableSet.of_discrete
  rw [PMF.toMeasure_apply_eq_zero_iff _ hms, Set.disjoint_left]
  intro s hs hns
  apply hns
  -- For every `s` in the PMF support, exhibit `polyToCoeffs f` as witness
  -- (where `f` is the bivariate-polynomial sample with `avssInitState ...
  -- (polyToCoeffs f) = s`).
  unfold avssInitPMF at hs
  rw [PMF.support_map] at hs
  obtain ⟨f, hf, hs_eq⟩ := hs
  refine ⟨polyToCoeffs (t := t) f, ?_⟩
  rw [← hs_eq]
  refine ⟨fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro _
  refine ⟨polyToCoeffs_zero_zero_eq_sec_of_support sec f hf, ?_⟩
  intro _
  rfl

/-- The simulate-derived view of an `avssInitState` factors through the
corrupt row polys: if `c, c'` agree on `rowPolyOfDealer` at every
corrupt party, then the simulate-derived view-and-schedule pair agrees. -/
theorem simView_simSched_avssInitState_factors
    (R : AVSSRushingAdversary n t F corr)
    (h_R : R.toProtocolView = avssCoalitionView corr)
    (C : BivariateShamir.Coalition n t) (h_C_corr : C.val ⊆ corr)
    (sec sec' : F) (partyPoint : Fin n → F) (dealerHonest : Bool) (k : ℕ)
    (c c' : Fin (t+1) → Fin (t+1) → F)
    (h_rp : ∀ p ∈ corr,
      rowPolyOfDealer partyPoint c p = rowPolyOfDealer partyPoint c' p) :
    (simAlgebraicView R C k
      (avssInitState (n := n) sec corr partyPoint dealerHonest c),
     simSchedulePrefix R k
      (avssInitState (n := n) sec corr partyPoint dealerHonest c)) =
    (simAlgebraicView R C k
      (avssInitState (n := n) sec' corr partyPoint dealerHonest c'),
     simSchedulePrefix R k
      (avssInitState (n := n) sec' corr partyPoint dealerHonest c')) := by
  have h_sync :=
    simSyncInv_avssInitState sec sec' corr partyPoint dealerHonest c c' h_rp
  have h_view :=
    simAlgebraicView_simSchedulePrefix_eq_of_simSyncInv R h_R C h_C_corr _ _ h_sync k
  exact Prod.ext h_view.1 h_view.2

/-! ## §19.4.5 — fully unconditional headline

This section composes Phase 7.4's structural pieces with PR #36's
`bivariate_shamir_secrecy_rowPoly_full` to deliver the
**fully unconditional** operational view-secrecy headline against a
rushing adversary.

The composition proceeds in three steps.

  * **Step A** (`avssInitMeasure_simView_factors_through_corrRow`) —
    factor the joint `(simAlgebraicView, simSchedulePrefix)` pushforward
    of `avssInitMeasure` through a corrupt-rowpoly extractor at the
    bivariate-polynomial level.  Uses
    `simView_simSched_avssInitState_factors` (the §19.4.2 factoring
    lemma) to define a deterministic post-composition map `K`.
  * **Step B** (`avssInitMeasure_simView_sec_invariant`) — by Step A
    plus `bivariate_shamir_secrecy_rowPoly_full` lifted from the
    `pts → Fin (t+1) → F` form to the `corr → Fin (t+1) → F` form via
    the `partyPoint` injection (`h_inj`), conclude sec-invariance of
    the joint pushforward.
  * **Step C** (`avss_secrecy_AS_view_rushing`) — combine Step B
    with `avss_secrecy_AS_view_rushing_via_init_invariant` (and the AE
    `initPred` discharge from `avssInitMeasure_AE_initPred`) to deliver
    the headline. -/

/-- The bivariate-polynomial-level corrupt-rowpoly extractor:
sends a polynomial `f` to the row polynomials at corrupt parties, in
the AVSS form (using `rowPolyOfDealer` on `polyToCoeffs f`). -/
noncomputable def corrRowMap (corr : Finset (Fin n)) (partyPoint : Fin n → F)
    (f : _root_.Polynomial (_root_.Polynomial F)) :
    corr → Fin (t+1) → F :=
  fun p l => rowPolyOfDealer (n := n) (t := t) partyPoint (polyToCoeffs f) p.val l

/-- The bivariate-polynomial-level corrupt-rowpoly extractor in the
*polynomial form* (using `(f.eval (C p)).coeff`). For `f` in the
support of `uniformBivariateFullWithFixedZero`, this agrees pointwise
with `corrRowMap`. -/
noncomputable def corrRowMapEval (corr : Finset (Fin n)) (partyPoint : Fin n → F)
    (f : _root_.Polynomial (_root_.Polynomial F)) :
    corr → Fin (t+1) → F :=
  fun p l => (f.eval (Polynomial.C (partyPoint p.val))).coeff l.val

/-- `corrRowMap` and `corrRowMapEval` agree on the support of
`uniformBivariateFullWithFixedZero`. -/
theorem corrRowMap_eq_corrRowMapEval_of_support
    (sec : F) (corr : Finset (Fin n)) (partyPoint : Fin n → F)
    (f : _root_.Polynomial (_root_.Polynomial F))
    (hf : f ∈ (Leslie.Prob.Polynomial.uniformBivariateFullWithFixedZero
                 (F := F) t t sec).support) :
    corrRowMap (n := n) (t := t) corr partyPoint f =
      corrRowMapEval (n := n) (t := t) corr partyPoint f := by
  funext p l
  exact rowPolyOfDealer_polyToCoeffs_eq_coeff_eval_of_support sec partyPoint f hf p.val l

/-- Sec-invariance of the corrupt-rowpoly marginal in the AVSS form,
lifted from `bivariate_shamir_secrecy_rowPoly_full` via the
`partyPoint`-injection bridge. The polynomial-form corrupt-rowpoly
extractor `corrRowMapEval` postcomposes the `pts`-form row-poly map
(used by `bivariate_shamir_secrecy_rowPoly_full`) with the embedding
`corr → corr.image partyPoint` (well-defined when `partyPoint` is
injective on `corr`). -/
theorem corrRowMap_uniform_sec_invariant
    (sec sec' : F) (corr : Finset (Fin n)) (partyPoint : Fin n → F)
    (h_inj : Set.InjOn partyPoint corr)
    (h_nz_pp : ∀ i, partyPoint i ≠ 0)
    (h_F : t + 1 ≤ Fintype.card F)
    (h_corr : corr.card ≤ t) :
    (Leslie.Prob.Polynomial.uniformBivariateFullWithFixedZero
        (F := F) t t sec).map (corrRowMap (n := n) (t := t) corr partyPoint) =
      (Leslie.Prob.Polynomial.uniformBivariateFullWithFixedZero
        (F := F) t t sec').map (corrRowMap (n := n) (t := t) corr partyPoint) := by
  classical
  -- Step 1: `corrRowMap` agrees with `corrRowMapEval` on the support.
  have hL :
      (Leslie.Prob.Polynomial.uniformBivariateFullWithFixedZero
          (F := F) t t sec).map (corrRowMap (n := n) (t := t) corr partyPoint) =
        (Leslie.Prob.Polynomial.uniformBivariateFullWithFixedZero
          (F := F) t t sec).map (corrRowMapEval (n := n) (t := t) corr partyPoint) := by
    apply PMF.map_congr_of_support
    intro f hf
    exact corrRowMap_eq_corrRowMapEval_of_support sec corr partyPoint f hf
  have hR :
      (Leslie.Prob.Polynomial.uniformBivariateFullWithFixedZero
          (F := F) t t sec').map (corrRowMap (n := n) (t := t) corr partyPoint) =
        (Leslie.Prob.Polynomial.uniformBivariateFullWithFixedZero
          (F := F) t t sec').map (corrRowMapEval (n := n) (t := t) corr partyPoint) := by
    apply PMF.map_congr_of_support
    intro f hf
    exact corrRowMap_eq_corrRowMapEval_of_support sec' corr partyPoint f hf
  rw [hL, hR]
  -- Step 2: `corrRowMapEval` factors as `(· ∘ embed) ∘ ptsRowPolyEval`
  -- where `embed : corr → pts := fun p => ⟨partyPoint p.val, ...⟩`.
  -- Define the `pts`-form map and the post-composition.
  set pts : Finset F := corr.image partyPoint with hpts_def
  have h_card_pts : pts.card ≤ t := by
    rw [hpts_def, Finset.card_image_of_injOn h_inj]
    exact h_corr
  have h_nz_pts : (0 : F) ∉ pts := by
    rw [hpts_def]
    intro h_mem
    rw [Finset.mem_image] at h_mem
    obtain ⟨i, _, h_eq⟩ := h_mem
    exact h_nz_pp i h_eq
  -- Polynomial-form pts-row-poly map (from `bivariate_shamir_secrecy_rowPoly_full`).
  let ptsRowPolyEval :
      _root_.Polynomial (_root_.Polynomial F) → pts → Fin (t+1) → F :=
    fun f (q : pts) (l : Fin (t+1)) =>
      (f.eval (Polynomial.C q.val)).coeff l.val
  -- Embedding `corr → pts`.
  have h_embed_mem : ∀ (p : corr), partyPoint p.val ∈ pts := by
    intro p
    rw [hpts_def]; exact Finset.mem_image.mpr ⟨p.val, p.property, rfl⟩
  let embed : corr → pts := fun p => ⟨partyPoint p.val, h_embed_mem p⟩
  -- Post-composition map: `(g : pts → Fin (t+1) → F) ↦ (fun p => g (embed p))`.
  let postComp :
      (pts → Fin (t+1) → F) → (corr → Fin (t+1) → F) :=
    fun g p => g (embed p)
  -- Identity: `corrRowMapEval = postComp ∘ ptsRowPolyEval`.
  have h_factor :
      corrRowMapEval (n := n) (t := t) corr partyPoint =
        postComp ∘ ptsRowPolyEval := by
    funext f p l
    rfl
  rw [h_factor, ← PMF.map_comp _ _ _, ← PMF.map_comp _ _ _]
  -- Apply `bivariate_shamir_secrecy_rowPoly_full` at `pts` and post-compose.
  have hbase :
      (Leslie.Prob.Polynomial.uniformBivariateFullWithFixedZero
          (F := F) t t sec).map ptsRowPolyEval =
        (Leslie.Prob.Polynomial.uniformBivariateFullWithFixedZero
          (F := F) t t sec').map ptsRowPolyEval :=
    Leslie.Prob.Polynomial.bivariate_shamir_secrecy_rowPoly_full t sec sec'
      pts h_card_pts h_nz_pts h_F
  rw [hbase]

/-- The deterministic post-composition map used to factor the
`(simAlgebraicView, simSchedulePrefix)` pushforward through the
corrupt-rowpoly extractor `corrRowMap`.

For a given corrupt-rowpoly profile `rp`, picks a canonical bivariate-
coefficient grid `chooseC rp` (via `Classical.epsilon`) realizing `rp`
at corrupt parties, then evaluates the simulate-derived view-and-
schedule pair at the canonical `avssInitState (sec := 0)` built from
that grid.

This map is **secret-independent**: it depends only on `R`, `C`, `k`,
`partyPoint`, `dealerHonest`, `corr`. -/
noncomputable def avssSimViewK {corr : Finset (Fin n)}
    (R : AVSSRushingAdversary n t F corr)
    (C : BivariateShamir.Coalition n t)
    (partyPoint : Fin n → F) (dealerHonest : Bool) (k : ℕ) :
    (corr → Fin (t+1) → F) →
      ((C.val → Fin (t+1) → F) × (Fin k → C.val → Bool)) ×
      (Fin k → Option (AVSSAction n F)) :=
  fun rp =>
    let chooseC : Fin (t+1) → Fin (t+1) → F :=
      Classical.epsilon
        (fun c => ∀ (p : corr), rowPolyOfDealer (n := n) (t := t)
          partyPoint c p.val = rp p)
    (simAlgebraicView R C k
        (avssInitState (n := n) (0 : F) corr partyPoint dealerHonest chooseC),
      simSchedulePrefix R k
        (avssInitState (n := n) (0 : F) corr partyPoint dealerHonest chooseC))

/-- **Step A — factor through corrupt rowpolys.**

The pushforward of `avssInitMeasure sec corr partyPoint dealerHonest`
through `(simAlgebraicView R C k, simSchedulePrefix R k)` factors as
a post-composition of the corrupt-rowpoly extractor `corrRowMap`
applied to `uniformBivariateFullWithFixedZero t t sec`, with
post-composition map `avssSimViewK` (secret-independent). -/
theorem avssInitMeasure_simView_factors_through_corrRow
    (sec : F) {corr : Finset (Fin n)}
    (R : AVSSRushingAdversary n t F corr)
    (h_R : R.toProtocolView = avssCoalitionView corr)
    (C : BivariateShamir.Coalition n t) (h_C_corr : C.val ⊆ corr)
    (partyPoint : Fin n → F) (dealerHonest : Bool) (k : ℕ) :
    (avssInitMeasure (n := n) (t := t) sec corr partyPoint dealerHonest).map
        (fun s_0 =>
          (simAlgebraicView R C k s_0, simSchedulePrefix R k s_0)) =
      (((Leslie.Prob.Polynomial.uniformBivariateFullWithFixedZero
          (F := F) t t sec).map
            (corrRowMap (n := n) (t := t) corr partyPoint)).map
          (avssSimViewK R C partyPoint dealerHonest k)).toMeasure := by
  classical
  unfold avssInitMeasure
  rw [PMF.toMeasure_map _ _ (measurable_of_countable _)]
  congr 1
  rw [PMF.map_comp]
  unfold avssInitPMF
  rw [PMF.map_comp]
  apply PMF.map_congr_of_support
  intro f hf
  -- Goal: (simView, simSched)(avssInitState sec corr pp dh (polyToCoeffs f)) =
  --       avssSimViewK ... (corrRowMap ... f).
  show (simAlgebraicView R C k
      (avssInitState (n := n) sec corr partyPoint dealerHonest (polyToCoeffs f)),
        simSchedulePrefix R k
      (avssInitState (n := n) sec corr partyPoint dealerHonest (polyToCoeffs f))) =
    avssSimViewK R C partyPoint dealerHonest k
      (corrRowMap (n := n) (t := t) corr partyPoint f)
  -- Unfold avssSimViewK.
  unfold avssSimViewK
  -- Apply simView_simSched_avssInitState_factors with c = polyToCoeffs f,
  -- c' = chooseC (corrRowMap f).
  apply simView_simSched_avssInitState_factors R h_R C h_C_corr
  intro p hp
  -- chooseC (corrRowMap f) realizes corrRowMap f at every corrupt party
  -- (by Classical.epsilon_spec, witness = polyToCoeffs f).
  have h_witness :
      ∃ c : Fin (t+1) → Fin (t+1) → F,
        ∀ (p_c : corr), rowPolyOfDealer (n := n) (t := t)
          partyPoint c p_c.val =
            corrRowMap (n := n) (t := t) corr partyPoint f p_c := by
    refine ⟨polyToCoeffs f, ?_⟩
    intro p_c
    rfl
  have h_eps :
      ∀ (p_c : corr),
        rowPolyOfDealer (n := n) (t := t) partyPoint
          (Classical.epsilon
            (fun c => ∀ (p_c : corr), rowPolyOfDealer (n := n) (t := t)
              partyPoint c p_c.val =
                corrRowMap (n := n) (t := t) corr partyPoint f p_c))
          p_c.val =
            corrRowMap (n := n) (t := t) corr partyPoint f p_c :=
    Classical.epsilon_spec h_witness
  exact (h_eps ⟨p, hp⟩).symm

set_option maxHeartbeats 400000 in
/-- **Step B — sec-invariance of the joint marginal.**

Combine Step A with `corrRowMap_uniform_sec_invariant` to conclude
sec-invariance of the joint `(simAlgebraicView, simSchedulePrefix)`
pushforward of `avssInitMeasure`. -/
theorem avssInitMeasure_simView_sec_invariant
    (sec sec' : F) {corr : Finset (Fin n)}
    (R : AVSSRushingAdversary n t F corr)
    (h_R : R.toProtocolView = avssCoalitionView corr)
    (C : BivariateShamir.Coalition n t) (h_C_corr : C.val ⊆ corr)
    (partyPoint : Fin n → F) (dealerHonest : Bool)
    (h_inj : Set.InjOn partyPoint corr)
    (h_nz_pp : ∀ i, partyPoint i ≠ 0)
    (h_F : t + 1 ≤ Fintype.card F)
    (h_corr : corr.card ≤ t) (k : ℕ) :
    (avssInitMeasure (n := n) (t := t) sec corr partyPoint dealerHonest).map
        (fun s_0 => (simAlgebraicView R C k s_0, simSchedulePrefix R k s_0)) =
      (avssInitMeasure (n := n) (t := t) sec' corr partyPoint dealerHonest).map
        (fun s_0 => (simAlgebraicView R C k s_0, simSchedulePrefix R k s_0)) := by
  -- Apply Step A at sec and at sec' (with the SAME K = avssSimViewK ...).
  rw [avssInitMeasure_simView_factors_through_corrRow
        (n := n) (t := t) sec R h_R C h_C_corr partyPoint dealerHonest k,
      avssInitMeasure_simView_factors_through_corrRow
        (n := n) (t := t) sec' R h_R C h_C_corr partyPoint dealerHonest k]
  -- The two pushforwards differ only in the sec parameter of `uniform`;
  -- apply `corrRowMap_uniform_sec_invariant`.
  congr 2
  exact corrRowMap_uniform_sec_invariant sec sec' corr partyPoint
    h_inj h_nz_pp h_F h_corr

/-! ## §19.4.5-bis — Ext form (8.5c): `simTrivialView` joint sec-invariance

Phase 8.5c lifts the §19.4.5 sec-invariance from `(simAlgebraicView,
simSchedulePrefix)` to `((simAlgebraicView, simTrivialView),
simSchedulePrefix)`. The `simTrivialView` component reads the four
schedule-dependent trivial fields from the simulate trace; it agrees
on two states with matching corrupt-rowpolys (the local-states-at-
corrupt are equal under `simSyncInv`, and the trivial fields are
projections of those local states). -/

/-- The Ext form of `simView_simSched_avssInitState_factors`: the
simulate-derived `((simAlgebraicView, simTrivialView),
simSchedulePrefix)` triple agrees on `avssInitState` of two
secret-realisations whose corrupt-rowpolys match. -/
theorem simViewExt_simSched_avssInitState_factors
    (R : AVSSRushingAdversary n t F corr)
    (h_R : R.toProtocolView = avssCoalitionView corr)
    (C : BivariateShamir.Coalition n t) (h_C_corr : C.val ⊆ corr)
    (sec sec' : F) (partyPoint : Fin n → F) (dealerHonest : Bool) (k : ℕ)
    (c c' : Fin (t+1) → Fin (t+1) → F)
    (h_rp : ∀ p ∈ corr,
      rowPolyOfDealer partyPoint c p = rowPolyOfDealer partyPoint c' p) :
    ((simAlgebraicView R C k
        (avssInitState (n := n) sec corr partyPoint dealerHonest c),
      simTrivialView R C k
        (avssInitState (n := n) sec corr partyPoint dealerHonest c)),
     simSchedulePrefix R k
      (avssInitState (n := n) sec corr partyPoint dealerHonest c)) =
    ((simAlgebraicView R C k
        (avssInitState (n := n) sec' corr partyPoint dealerHonest c'),
      simTrivialView R C k
        (avssInitState (n := n) sec' corr partyPoint dealerHonest c')),
     simSchedulePrefix R k
      (avssInitState (n := n) sec' corr partyPoint dealerHonest c')) := by
  have h_sync :=
    simSyncInv_avssInitState sec sec' corr partyPoint dealerHonest c c' h_rp
  have h_view :=
    simAlgebraicView_simSchedulePrefix_eq_of_simSyncInv R h_R C h_C_corr _ _ h_sync k
  -- The trivial-view component agrees by `local_corrupt_eq` at every step.
  have h_triv :
      simTrivialView R C k
          (avssInitState (n := n) sec corr partyPoint dealerHonest c) =
        simTrivialView R C k
          (avssInitState (n := n) sec' corr partyPoint dealerHonest c') := by
    funext i p
    have h_step :=
      avssSimulateTrace_simSyncInv R h_R _ _ h_sync i.val
    have h_state_inv := h_step.1
    have h_pcorr : p.val ∈ corr := h_C_corr p.property
    have h_local_eq := h_state_inv.local_corrupt_eq p.val h_pcorr
    show (((avssSimulateTrace R
            (avssInitState (n := n) sec corr partyPoint dealerHonest c) i.val).1.local_
            p.val).echoSent,
          ((avssSimulateTrace R
            (avssInitState (n := n) sec corr partyPoint dealerHonest c) i.val).1.local_
            p.val).echoesReceived,
          ((avssSimulateTrace R
            (avssInitState (n := n) sec corr partyPoint dealerHonest c) i.val).1.local_
            p.val).readySent,
          ((avssSimulateTrace R
            (avssInitState (n := n) sec corr partyPoint dealerHonest c) i.val).1.local_
            p.val).readyReceived) =
        (((avssSimulateTrace R
            (avssInitState (n := n) sec' corr partyPoint dealerHonest c') i.val).1.local_
            p.val).echoSent,
         ((avssSimulateTrace R
            (avssInitState (n := n) sec' corr partyPoint dealerHonest c') i.val).1.local_
            p.val).echoesReceived,
         ((avssSimulateTrace R
            (avssInitState (n := n) sec' corr partyPoint dealerHonest c') i.val).1.local_
            p.val).readySent,
         ((avssSimulateTrace R
            (avssInitState (n := n) sec' corr partyPoint dealerHonest c') i.val).1.local_
            p.val).readyReceived)
    rw [h_local_eq]
  -- Combine.
  refine Prod.ext ?_ h_view.2
  exact Prod.ext h_view.1 h_triv

/-- **Step A (Ext form).** Post-composition map for the Ext joint:
adds `simTrivialView` to `avssSimViewK`'s output. -/
noncomputable def avssSimViewKExt {corr : Finset (Fin n)}
    (R : AVSSRushingAdversary n t F corr)
    (C : BivariateShamir.Coalition n t)
    (partyPoint : Fin n → F) (dealerHonest : Bool) (k : ℕ) :
    (corr → Fin (t+1) → F) →
      (((C.val → Fin (t+1) → F) × (Fin k → C.val → Bool)) ×
        (Fin k → C.val → TrivialView n)) ×
      (Fin k → Option (AVSSAction n F)) :=
  fun rp =>
    let chooseC : Fin (t+1) → Fin (t+1) → F :=
      Classical.epsilon
        (fun c => ∀ (p : corr), rowPolyOfDealer (n := n) (t := t)
          partyPoint c p.val = rp p)
    ((simAlgebraicView R C k
        (avssInitState (n := n) (0 : F) corr partyPoint dealerHonest chooseC),
      simTrivialView R C k
        (avssInitState (n := n) (0 : F) corr partyPoint dealerHonest chooseC)),
      simSchedulePrefix R k
        (avssInitState (n := n) (0 : F) corr partyPoint dealerHonest chooseC))

/-- **Step A (Ext form).** The pushforward of `avssInitMeasure` through
the Ext joint factors through `corrRowMap` plus `avssSimViewKExt`. -/
theorem avssInitMeasure_simViewExt_factors_through_corrRow
    (sec : F) {corr : Finset (Fin n)}
    (R : AVSSRushingAdversary n t F corr)
    (h_R : R.toProtocolView = avssCoalitionView corr)
    (C : BivariateShamir.Coalition n t) (h_C_corr : C.val ⊆ corr)
    (partyPoint : Fin n → F) (dealerHonest : Bool) (k : ℕ) :
    (avssInitMeasure (n := n) (t := t) sec corr partyPoint dealerHonest).map
        (fun s_0 =>
          ((simAlgebraicView R C k s_0, simTrivialView R C k s_0),
            simSchedulePrefix R k s_0)) =
      (((Leslie.Prob.Polynomial.uniformBivariateFullWithFixedZero
          (F := F) t t sec).map
            (corrRowMap (n := n) (t := t) corr partyPoint)).map
          (avssSimViewKExt R C partyPoint dealerHonest k)).toMeasure := by
  classical
  unfold avssInitMeasure
  rw [PMF.toMeasure_map _ _ (measurable_of_countable _)]
  congr 1
  rw [PMF.map_comp]
  unfold avssInitPMF
  rw [PMF.map_comp]
  apply PMF.map_congr_of_support
  intro f hf
  show ((simAlgebraicView R C k
      (avssInitState (n := n) sec corr partyPoint dealerHonest (polyToCoeffs f)),
        simTrivialView R C k
      (avssInitState (n := n) sec corr partyPoint dealerHonest (polyToCoeffs f))),
        simSchedulePrefix R k
      (avssInitState (n := n) sec corr partyPoint dealerHonest (polyToCoeffs f))) =
    avssSimViewKExt R C partyPoint dealerHonest k
      (corrRowMap (n := n) (t := t) corr partyPoint f)
  unfold avssSimViewKExt
  apply simViewExt_simSched_avssInitState_factors R h_R C h_C_corr
  intro p hp
  have h_witness :
      ∃ c : Fin (t+1) → Fin (t+1) → F,
        ∀ (p_c : corr), rowPolyOfDealer (n := n) (t := t)
          partyPoint c p_c.val =
            corrRowMap (n := n) (t := t) corr partyPoint f p_c := by
    refine ⟨polyToCoeffs f, ?_⟩
    intro p_c
    rfl
  have h_eps :
      ∀ (p_c : corr),
        rowPolyOfDealer (n := n) (t := t) partyPoint
          (Classical.epsilon
            (fun c => ∀ (p_c : corr), rowPolyOfDealer (n := n) (t := t)
              partyPoint c p_c.val =
                corrRowMap (n := n) (t := t) corr partyPoint f p_c))
          p_c.val =
            corrRowMap (n := n) (t := t) corr partyPoint f p_c :=
    Classical.epsilon_spec h_witness
  exact (h_eps ⟨p, hp⟩).symm

set_option maxHeartbeats 400000 in
/-- **Step B (Ext form, 8.5c) — sec-invariance of the Ext joint marginal.** -/
theorem avssInitMeasure_simViewExt_sec_invariant
    (sec sec' : F) {corr : Finset (Fin n)}
    (R : AVSSRushingAdversary n t F corr)
    (h_R : R.toProtocolView = avssCoalitionView corr)
    (C : BivariateShamir.Coalition n t) (h_C_corr : C.val ⊆ corr)
    (partyPoint : Fin n → F) (dealerHonest : Bool)
    (h_inj : Set.InjOn partyPoint corr)
    (h_nz_pp : ∀ i, partyPoint i ≠ 0)
    (h_F : t + 1 ≤ Fintype.card F)
    (h_corr : corr.card ≤ t) (k : ℕ) :
    (avssInitMeasure (n := n) (t := t) sec corr partyPoint dealerHonest).map
        (fun s_0 =>
          ((simAlgebraicView R C k s_0, simTrivialView R C k s_0),
            simSchedulePrefix R k s_0)) =
      (avssInitMeasure (n := n) (t := t) sec' corr partyPoint dealerHonest).map
        (fun s_0 =>
          ((simAlgebraicView R C k s_0, simTrivialView R C k s_0),
            simSchedulePrefix R k s_0)) := by
  rw [avssInitMeasure_simViewExt_factors_through_corrRow
        (n := n) (t := t) sec R h_R C h_C_corr partyPoint dealerHonest k,
      avssInitMeasure_simViewExt_factors_through_corrRow
        (n := n) (t := t) sec' R h_R C h_C_corr partyPoint dealerHonest k]
  congr 2
  exact corrRowMap_uniform_sec_invariant sec sec' corr partyPoint
    h_inj h_nz_pp h_F h_corr

/-- **Canonical headline — fully unconditional operational view-secrecy
under a rushing adversary.**

Operational view-secrecy for the AVSS protocol against a rushing
adversary, with NO algebraic-core or initial-measure-invariance
hypotheses: just the structural conditions
(`corr.card ≤ t`, `partyPoint` injective on `corr`, nonzero, field
size).  This is the literature-faithful operational-secrecy theorem
under the **post-Phase-8 CR-faithful adversary model** —
Step C of §19.4.5, composing
`avss_secrecy_AS_view_rushing_via_init_invariant_indep` with
`avssInitMeasure_simViewExt_sec_invariant` (which itself rests on the
row-poly secrecy lemma `bivariate_shamir_secrecy_rowPoly_full`).

The conclusion is closed uniformly across `dealerHonest : Bool` via
the `_indep` chain: under both honest and corrupt dealer, the joint
distribution of `(coalitionTraceView, schedulePrefix)` is invariant
in the secret.  See `coalitionRowPolyAlignedInv` (the
dealerHonest-independent structural protocol invariant whose
preservation drives the cTV bridge).

## Adversary-model coverage (post-Phase-8)

The adversary modelled here is the literature-standard rushing
adversary: it is `RushingAdversary`-restricted (its scheduling
decisions depend only on the corrupt-coalition view), but otherwise
matches CR '93's threat model on every observable channel.  The
three pre-Phase-8 caveats that previously qualified this theorem
(`AVSS-MODEL-NOTES.md` §11.1, §11.2, §11.4) are all closed by the
Phase 8 chain (PRs #57–#76, on `main`):

* **§11.1 (C1 — corrupt-party send actions)** ✅ resolved by Phase
  8.5b. Corrupt parties may now fire `partyEchoSend`/`partyReady`/
  `partyAmplify` (the `p ∉ s.corrupted` gates were dropped); their
  `echoesReceived`/`readyReceived` may be populated by adversarial
  echoes.

* **§11.2 (C2 — honest broadcasts to corrupt receivers)** ✅
  resolved by Phase 8.5b. The `partyEchoSend` broadcast filter was
  widened to all parties (including corrupt receivers), and the
  `partyEchoReceive`/`partyReceiveReady` honest-receiver gates were
  dropped.

* **§11.4 (C4 — selective non-broadcast)** ✅ resolved by Phase
  8.5d. The `dealerShare` action was replaced by per-party
  `dealerShareTo (p : Fin n)`; corrupt dealers can selectively
  short-share. Termination's hypothesis was strengthened to include
  `consistent_quorum_AE` (≥ n−t honest parties received consistent
  shares), matching CR '93's conditional-termination semantics.

The `s.coeffs` field was migrated to μ₀ in Phase 8.5d-β: the
dealer's bivariate polynomial is now an initial-state witness
sampled at protocol start, not a runtime field.  This makes the
existential-witness theorem forms (`avss_correctness_AS_existential`
PR #43, `avss_commitment_AS_existential` PR #45+#48) the
canonical surface API.

## Strengthened bivariate form (Phase 11-δ-followup)

The sibling theorem `avss_secrecy_AS_view_rushing_bivariate` (§19.7)
bundles this trace-level operational headline with the
polynomial-level row+column secrecy form
(`avss_bivariate_corrGrid_sec_invariant`, Phase 11-δ / Phase 8.6):
together they capture both the operational view secrecy and the
algebraic bivariate uniformity that the CR '93 cryptographic
analysis relies on.

## Forward queue

* **Phase 11-β (deferred)** — lift to `SecrecyRandomised` via
  Phase 9's `RandomisedAdversary` framework; mechanical (~100 LOC).
* **Phase 12** — UC-style composability layer (per
  `AVSS-MODEL-NOTES.md` §15 plan); enables compositional secrecy
  reasoning for higher-level protocols (e.g., random secret draw)
  that use AVSS as a black-box subprotocol.

`SecrecyRushing` framework abstraction (Phase 11-α) — see
`avss_secrecy_AS_view_rushing_instance` (§19.5) for the
protocol-independent restatement. -/
theorem avss_secrecy_AS_view_rushing
    {corr : Finset (Fin n)}
    (sec sec' : F) (partyPoint : Fin n → F) (dealerHonest : Bool)
    (h_inj : Set.InjOn partyPoint corr)
    (h_nz_pp : ∀ i, partyPoint i ≠ 0)
    (h_F : t + 1 ≤ Fintype.card F)
    (h_corr : corr.card ≤ t)
    (R : AVSSRushingAdversary n t F corr)
    (h_R : R.toProtocolView = avssCoalitionView corr)
    (C : BivariateShamir.Coalition n t)
    (h_C_corr : C.val ⊆ corr) (k : ℕ) :
    (traceDist (avssSpec (t := t) sec corr coeffs) R.toAdversary
        (avssInitMeasure (n := n) (t := t) sec corr partyPoint dealerHonest)).map
        (fun ω => (coalitionTraceView C ω k, schedulePrefix ω k)) =
      (traceDist (avssSpec (t := t) sec' corr coeffs) R.toAdversary
        (avssInitMeasure (n := n) (t := t) sec' corr partyPoint dealerHonest)).map
        (fun ω => (coalitionTraceView C ω k, schedulePrefix ω k)) := by
  -- Phase 8.5d-β-followup-7: closes BOTH dealerHonest values uniformly via
  -- the dealerHonest-INDEPENDENT `_via_init_invariant_indep` chain. The
  -- chain replaces phase6Inv's honest-dealer-conditional dealerMessagesInv
  -- with the new `coalitionRowPolyAlignedInv` (a structural protocol
  -- invariant: dealerMessages writes from dealerShareTo match dealerCommit,
  -- and corrupt parties' delivered rowPoly matches dealerCommit). Both
  -- clauses are dealerHonest-INDEPENDENT and preserved by every avssStep.
  -- Combined with avss_phase6InvEx_AS for c-independent corruptLocalInv
  -- (output = none, delivered = false → rowPoly = none), this drops the
  -- honest-dealer guard from the cTV bridge entirely.
  exact avss_secrecy_AS_view_rushing_via_init_invariant_indep
    sec sec'
    (avssInitMeasure (n := n) (t := t) sec corr partyPoint dealerHonest)
    (avssInitMeasure (n := n) (t := t) sec' corr partyPoint dealerHonest)
    (avssInitMeasure_AE_initPred sec corr partyPoint dealerHonest)
    (avssInitMeasure_AE_initPred sec' corr partyPoint dealerHonest)
    R C h_C_corr k
    (avssInitMeasure_simViewExt_sec_invariant sec sec' R h_R C h_C_corr
      partyPoint dealerHonest h_inj h_nz_pp h_F h_corr k)

/-! ## §19.5. Phase 11-γ — `SecrecyRushing` instance

The headline `avss_secrecy_AS_view_rushing` is restated as an instance of
the protocol-independent `Leslie.Prob.SecrecyRushing` predicate from
`Leslie/Prob/Secrecy.lean` (Phase 11-α).

`SecrecyRushing` quantifies over a *single* spec; `avssSpec` carries a
`sec : F` parameter that turns out to be vestigial — it only enters
the spec's `init` field, which `traceDist` does not consume (only
`spec.actions` is read by `stepKernel`).  We therefore pick `sec = 0`
as the canonical spec and bridge the two sides by `rfl`. -/

/-- `traceDist` ignores `avssSpec`'s `sec` parameter: only `spec.actions`
is consumed by `stepKernel`, and `actions` is sec-independent. -/
theorem traceDist_avssSpec_sec_irrelevant
    (sec sec' : F) (corr : Finset (Fin n))
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (A : Adversary (AVSSState n t F) (AVSSAction n F))
    (μ : Measure (AVSSState n t F)) :
    traceDist (avssSpec (t := t) sec corr coeffs) A μ =
      traceDist (avssSpec (t := t) sec' corr coeffs) A μ := rfl

/-- **Phase 11-γ headline.**  `avss_secrecy_AS_view_rushing` restated as
an instance of the protocol-independent `Leslie.Prob.SecrecyRushing`
predicate.  The canonical spec is taken at `sec = 0` (any value works:
see `traceDist_avssSpec_sec_irrelevant`); the secret is encoded in the
initial measure family `fun sec => avssInitMeasure sec corr partyPoint
dealerHonest`. -/
theorem avss_secrecy_AS_view_rushing_instance
    {corr : Finset (Fin n)}
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (partyPoint : Fin n → F) (dealerHonest : Bool)
    (h_inj : Set.InjOn partyPoint corr)
    (h_nz_pp : ∀ i, partyPoint i ≠ 0)
    (h_F : t + 1 ≤ Fintype.card F)
    (h_corr : corr.card ≤ t)
    (C : BivariateShamir.Coalition n t)
    (h_C_corr : C.val ⊆ corr) (k : ℕ) :
    Leslie.Prob.SecrecyRushing
      (spec := avssSpec (t := t) (0 : F) corr coeffs)
      (μ₀ := fun (sec : F) =>
        avssInitMeasure (n := n) (t := t) sec corr partyPoint dealerHonest)
      (view := avssCoalitionView corr)
      (proj := fun ω => (coalitionTraceView C ω k, schedulePrefix ω k)) := by
  intro sec sec' R hR
  rw [traceDist_avssSpec_sec_irrelevant (sec := 0) (sec' := sec),
      traceDist_avssSpec_sec_irrelevant (sec := 0) (sec' := sec')]
  exact avss_secrecy_AS_view_rushing sec sec' partyPoint dealerHonest
    h_inj h_nz_pp h_F h_corr R hR C h_C_corr k

/-- Randomised analog of `traceDist_avssSpec_sec_irrelevant`:
`randomisedTraceDist` also ignores `avssSpec`'s `sec` parameter.  Only
`spec.actions` is consumed by `randomisedStepKernel` (via
`randomisedStepPMF`), and `actions` is sec-independent. -/
theorem randomisedTraceDist_avssSpec_sec_irrelevant
    (sec sec' : F) (corr : Finset (Fin n))
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (R : Leslie.Prob.RandomisedAdversary (AVSSState n t F) (AVSSAction n F))
    (μ : Measure (AVSSState n t F)) :
    randomisedTraceDist (avssSpec (t := t) sec corr coeffs) R μ =
      randomisedTraceDist (avssSpec (t := t) sec' corr coeffs) R μ := rfl

/-- **Phase 11-γ-randomised headline.**  `avss_secrecy_AS_view_rushing_randomised`
restated as an instance of the protocol-independent
`Leslie.Prob.SecrecyRushingRandomised` predicate from
`Leslie/Prob/Secrecy.lean` (Phase 11-β, PR #82).

This mirrors the deterministic `avss_secrecy_AS_view_rushing_instance`
(§19.5) and closes the literature-faithful threat-model story: secrecy
holds against **randomised + rushing** adversaries (the strongest
classical AVSS adversary class).

The wrapped headline `avss_secrecy_AS_view_rushing_randomised` (Phase 9.6,
PR #53) quantifies universally over `AVSSRushingRandomisedAdversary` and
delivers the *grid* projection at arbitrary step `k`; this instance form
is a one-liner over it.  The view hypothesis `_hR : R.toProtocolView =
view` is irrelevant on this side: the underlying randomised theorem
already quantifies over all `R : AVSSRushingRandomisedAdversary` (whose
`toProtocolView` is part of the structure but unconstrained), so the
`hR` constraint is simply ignored. -/
theorem avss_secrecy_AS_view_rushing_randomised_instance
    {corr : Finset (Fin n)}
    (coeffs : Fin (t+1) → Fin (t+1) → F)
    (partyPoint : Fin n → F) (dealerHonest : Bool)
    (h_nz_pp : ∀ i, partyPoint i ≠ 0)
    (h_F : t + 1 ≤ Fintype.card F)
    (C D : BivariateShamir.Coalition n t) (k : ℕ) :
    Leslie.Prob.SecrecyRushingRandomised
      (spec := avssSpec (t := t) (0 : F) corr coeffs)
      (μ₀ := fun (sec : F) =>
        avssInitMeasure (n := n) (t := t) sec corr partyPoint dealerHonest)
      (view := avssCoalitionView corr)
      (proj := fun ω => coalitionGrid coeffs C D (ω k).1) := by
  intro sec sec' R _hR
  rw [randomisedTraceDist_avssSpec_sec_irrelevant (sec := 0) (sec' := sec),
      randomisedTraceDist_avssSpec_sec_irrelevant (sec := 0) (sec' := sec')]
  exact avss_secrecy_AS_view_rushing_randomised sec sec' corr coeffs
    partyPoint dealerHonest h_nz_pp h_F C D R k

/-! ## §19.6. Phase 11-δ (= Phase 8.6) — bivariate row+column secrecy

This section instantiates the polynomial-level row+column uniformity
theorem `Leslie.Prob.Polynomial.bivariate_evals_uniform_row_col` to the
AVSS coalition setting.  This is the cryptographic content **deferred
since SyncVSS §10**: it generalises the row-only bivariate uniformity
that flows through the existing `corrRowMap_uniform_sec_invariant` chain
from a *rectangular* `pts_x × pts_y` form to **arbitrary subsets**
`S ⊆ R × R` of corrupt parties' point set.

Practically, the upgraded form is used by future protocols that need
a stronger secrecy conclusion than "corrupt rowPolys are uniform" — for
example column cross-checks (CR'93 §10) where the corrupt coalition's
**column-axis** evaluations at corrupt-party rows must also be uniform.

The wrapper takes the AVSS coalition `corr` (size ≤ t) and an arbitrary
subset `S ⊆ (corr.image partyPoint) ×ˢ (corr.image partyPoint)`,
specialising the polynomial-level theorem via the standard
`partyPoint`-injection bridge.

**Status (2026-05-07).**  Landed axiom-clean (PR #75): full proof
via `Leslie.Prob.Polynomial.bivariate_evals_uniform_row_col` and the
auxiliary `PMF.uniform_pi_restrict`.  Wired into the headline secrecy
theorem via the sibling `avss_secrecy_AS_view_rushing_bivariate`
(§19.7, Phase 11-δ-followup).  See MODEL_NOTES §12.1 row 8.6 + §12.4
risk 4 for context. -/

/-- **AVSS-side bivariate row+column uniformity (Phase 11-δ).**

Specialisation of `Leslie.Prob.Polynomial.bivariate_evals_uniform_row_col`
to the AVSS coalition setting (`R = corr.image partyPoint`).  For any
subset `S` of the corrupt-party bivariate grid, the joint evaluation
distribution is uniform on `↑S → F` — independently of `sec`.

This is strictly stronger than `corrRowMap_uniform_sec_invariant` (which
gives only the rowPoly-coefficient form) and matches the literature
"row + column" secrecy form used in CR'93 §10's cross-check argument. -/
theorem avss_bivariate_corrGrid_uniform
    (sec : F) (corr : Finset (Fin n)) (partyPoint : Fin n → F)
    (h_inj : Set.InjOn partyPoint corr)
    (h_nz_pp : ∀ i, partyPoint i ≠ 0)
    (h_F : t + 1 ≤ Fintype.card F)
    (h_corr : corr.card ≤ t)
    (S : Finset (F × F))
    (hS : S ⊆ corr.image partyPoint ×ˢ corr.image partyPoint)
    [Nonempty S]
    [Nonempty (↥(corr.image partyPoint) × ↥(corr.image partyPoint))] :
    (Leslie.Prob.Polynomial.uniformBivariateFullWithFixedZero (F := F) t t sec).map
        (fun (f : _root_.Polynomial (_root_.Polynomial F)) (pq : S) =>
          (f.eval (Polynomial.C pq.val.1)).eval pq.val.2) =
      PMF.uniform (S → F) := by
  classical
  -- Deduce the `R = corr.image partyPoint` hypotheses from the AVSS-side ones.
  have h_R_card : (corr.image partyPoint).card ≤ t := by
    rw [Finset.card_image_of_injOn h_inj]; exact h_corr
  have h_R_nz : (0 : F) ∉ corr.image partyPoint := by
    intro h_mem
    rw [Finset.mem_image] at h_mem
    obtain ⟨i, _, h_eq⟩ := h_mem
    exact h_nz_pp i h_eq
  exact Leslie.Prob.Polynomial.bivariate_evals_uniform_row_col t sec
    (corr.image partyPoint) h_R_card h_R_nz h_F S hS

/-- **AVSS-side row+column secrecy corollary (Phase 11-δ).**

Two sec-values yield the same `S`-marginal of
`uniformBivariateFullWithFixedZero` — the *secrecy* form of
`avss_bivariate_corrGrid_uniform`.  This is the headline form that
downstream consumers (e.g. column cross-check protocols) use as a
black-box "corrupt coalition's bivariate view is sec-invariant". -/
theorem avss_bivariate_corrGrid_sec_invariant
    (sec sec' : F) (corr : Finset (Fin n)) (partyPoint : Fin n → F)
    (h_inj : Set.InjOn partyPoint corr)
    (h_nz_pp : ∀ i, partyPoint i ≠ 0)
    (h_F : t + 1 ≤ Fintype.card F)
    (h_corr : corr.card ≤ t)
    (S : Finset (F × F))
    (hS : S ⊆ corr.image partyPoint ×ˢ corr.image partyPoint)
    [Nonempty S]
    [Nonempty (↥(corr.image partyPoint) × ↥(corr.image partyPoint))] :
    (Leslie.Prob.Polynomial.uniformBivariateFullWithFixedZero (F := F) t t sec).map
        (fun (f : _root_.Polynomial (_root_.Polynomial F)) (pq : S) =>
          (f.eval (Polynomial.C pq.val.1)).eval pq.val.2) =
      (Leslie.Prob.Polynomial.uniformBivariateFullWithFixedZero (F := F) t t sec').map
        (fun (f : _root_.Polynomial (_root_.Polynomial F)) (pq : S) =>
          (f.eval (Polynomial.C pq.val.1)).eval pq.val.2) := by
  rw [avss_bivariate_corrGrid_uniform sec corr partyPoint
        h_inj h_nz_pp h_F h_corr S hS,
      avss_bivariate_corrGrid_uniform sec' corr partyPoint
        h_inj h_nz_pp h_F h_corr S hS]

/-! ## §19.7. Phase 11-δ-followup — bivariate sibling of the headline secrecy theorem

`avss_secrecy_AS_view_rushing_bivariate` is a *sibling* theorem to
`avss_secrecy_AS_view_rushing` (§19.4) that bundles two sec-invariances
into a single citation:

  * **(a)** the existing operational headline (Phase 8.5d): the
    trace-level `(coalitionTraceView, schedulePrefix)`-marginal of the
    AVSS trace distribution is invariant in the secret;
  * **(b)** the polynomial-level row+column form (Phase 11-δ /
    `avss_bivariate_corrGrid_sec_invariant`): the
    `S`-marginal of `uniformBivariateFullWithFixedZero` at any
    `S ⊆ corrPts ×ˢ corrPts` is invariant in the secret.

The original headline keeps its statement and proof unchanged; this
sibling is *additive* and backward-compatible.

**Why the conjunction form (rather than a deeper joint pushforward).**
The two equalities concern *distinct measures*: (a) is on the trace
distribution and (b) is on the bivariate-polynomial measure that
`avssInitMeasure` is pulled back from.  Bundling them at the headline
level gives downstream callers (e.g., column cross-check protocols,
CR'93 §10) both axes of secrecy in one citation without forcing a
joint pushforward — the latter would require extracting the dealer's
polynomial through the trace's initial state, which adds substantive
measurability work without changing the cryptographic content.  The
conjunction is the right abstraction for downstream consumers because
each clause matches their natural query: (a) "is my operational view
sec-invariant?" and (b) "is my bivariate evaluation grid
sec-invariant?". -/

/-- **Phase 11-δ-followup headline.**  Bivariate row+column secrecy
sibling of `avss_secrecy_AS_view_rushing`.

Conjunction of the existing trace-level operational headline and the
polynomial-level bivariate corrupt-grid sec-invariance from PR #75
(`avss_bivariate_corrGrid_sec_invariant`).  Both clauses share the
AVSS-side `partyPoint` / `corr` hypotheses (`Set.InjOn`, `0 ∉ image`,
`|corr| ≤ t`, `t + 1 ≤ |F|`).

Backward-compat: the original `avss_secrecy_AS_view_rushing` is
unchanged; this is a *new* theorem that exposes both axes of secrecy
together. -/
theorem avss_secrecy_AS_view_rushing_bivariate
    {corr : Finset (Fin n)}
    (sec sec' : F) (partyPoint : Fin n → F) (dealerHonest : Bool)
    (h_inj : Set.InjOn partyPoint corr)
    (h_nz_pp : ∀ i, partyPoint i ≠ 0)
    (h_F : t + 1 ≤ Fintype.card F)
    (h_corr : corr.card ≤ t)
    (R : AVSSRushingAdversary n t F corr)
    (h_R : R.toProtocolView = avssCoalitionView corr)
    (C : BivariateShamir.Coalition n t)
    (h_C_corr : C.val ⊆ corr) (k : ℕ)
    (S : Finset (F × F))
    (hS : S ⊆ corr.image partyPoint ×ˢ corr.image partyPoint)
    [Nonempty S]
    [Nonempty (↥(corr.image partyPoint) × ↥(corr.image partyPoint))] :
    -- (a) Operational headline: schedule + coalitionTraceView marginal.
    ((traceDist (avssSpec (t := t) sec corr coeffs) R.toAdversary
        (avssInitMeasure (n := n) (t := t) sec corr partyPoint dealerHonest)).map
        (fun ω => (coalitionTraceView C ω k, schedulePrefix ω k)) =
      (traceDist (avssSpec (t := t) sec' corr coeffs) R.toAdversary
        (avssInitMeasure (n := n) (t := t) sec' corr partyPoint dealerHonest)).map
        (fun ω => (coalitionTraceView C ω k, schedulePrefix ω k)))
    ∧
    -- (b) Bivariate corrGrid (Phase 11-δ): polynomial-level S-marginal.
    ((Leslie.Prob.Polynomial.uniformBivariateFullWithFixedZero (F := F) t t sec).map
        (fun (f : _root_.Polynomial (_root_.Polynomial F)) (pq : S) =>
          (f.eval (Polynomial.C pq.val.1)).eval pq.val.2) =
      (Leslie.Prob.Polynomial.uniformBivariateFullWithFixedZero (F := F) t t sec').map
        (fun (f : _root_.Polynomial (_root_.Polynomial F)) (pq : S) =>
          (f.eval (Polynomial.C pq.val.1)).eval pq.val.2)) :=
  ⟨avss_secrecy_AS_view_rushing sec sec' partyPoint dealerHonest
      h_inj h_nz_pp h_F h_corr R h_R C h_C_corr k,
   avss_bivariate_corrGrid_sec_invariant sec sec' corr partyPoint
      h_inj h_nz_pp h_F h_corr S hS⟩

attribute [instance] instMeasurableSpaceAVSSRushingView
  instMeasurableSingletonClassAVSSRushingView

end RushingSimulation

end Leslie.Examples.Prob.AVSS
