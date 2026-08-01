/-
M2 W1 — `Adversary`: full version.

Promoted from the M1 stub with:
  * `corrupt : Set PartyId` — static corruption set.
  * `FairnessAssumptions` — predicate carving out fair adversaries.
  * `FairAdversary spec F` — bundle adversary + fairness witness.

Per implementation plan v2.2 §M2 W1 + design plan v2.2 §"Adversary,
scheduler, fairness".

The scheduler is **demonic and history-deterministic**: given the
visible history, the adversary picks an action (or `none` to
stutter). This matches the standard MDP / adversarial-randomization
encoding. Randomized schedulers are strictly more expressive but are
not needed for AST under fairness; deferred (see plan §"Open
questions").

Measurability conditions for kernel composition (needed when
`Trace.traceDist` lifts the adversary to a per-step Markov kernel)
land in `Trace.lean` rather than here, so this file remains
Mathlib-light.
-/

import Mathlib.Data.Set.Basic

namespace Leslie.Prob

/-- Party identifier. Concretely we use `ℕ`; protocols fix a finite
range (`Fin n`) and inject into `ℕ`. -/
abbrev PartyId : Type := ℕ

/-! ## Adversary -/

/-- A history-deterministic, demonic scheduler with a static
corruption set.

  * `schedule` — given the visible trace prefix, choose an action
    label (or `none` to stutter).
  * `corrupt` — the set of corrupted parties; under static
    corruption, this is fixed at the start of the run. -/
structure Adversary (σ : Type*) (ι : Type*) where
  schedule : List (σ × Option ι) → Option ι
  corrupt  : Set PartyId

namespace Adversary

variable {σ ι : Type*}

/-- An adversary that schedules `i` immediately at the empty history,
with no corruption. Useful for trivial test cases. -/
def trivial (i : ι) : Adversary σ ι where
  schedule _ := some i
  corrupt   := ∅

/-- An adversary that always stutters. -/
def alwaysStutter : Adversary σ ι where
  schedule _ := none
  corrupt   := ∅

end Adversary

/-! ## Fairness -/

/-- Fairness assumptions: a set of fair-required action labels and a
predicate carving out which adversaries are weakly fair w.r.t. those
actions.

The convention: an adversary is *weakly fair* w.r.t. `fair_actions`
iff every action in `fair_actions` that becomes continuously enabled
along an execution is eventually fired. This is the temporal
predicate; concrete instantiations (e.g., for the M3 AVSS proof)
specialize `isWeaklyFair`. -/
structure FairnessAssumptions (σ : Type*) (ι : Type*) where
  fair_actions : Set ι
  isWeaklyFair : Adversary σ ι → Prop

/-- A fair adversary: bundle an adversary together with a witness
that it satisfies the fairness predicate.

Carrying the witness as a hard type-level component (rather than as
a temporal-side-condition on traces) means downstream theorems
quantify directly over `FairAdversary _ F`, simplifying the
statements of `FairASTCertificate.sound`-style results. -/
structure FairAdversary (σ : Type*) (ι : Type*)
    (F : FairnessAssumptions σ ι) where
  toAdversary : Adversary σ ι
  fair        : F.isWeaklyFair toAdversary

/-! ## Rushing adversary (view-restricted scheduler)

Per the M3 AVSS Phase 7 brief: a *rushing adversary* is the standard
cryptography-literature notion (Canetti–Rabin '93, Goldwasser–Lindell
'02, Asharov–Lindell '17): the adversary may schedule its own moves
"after" seeing the visible-history of corrupt-party views, but its
choices are restricted to a function of that view-history rather than
the full state-history.

We split the design into two pieces, both deliberately
measurability-free at this layer:

* `ProtocolView σ V` — a record carrying just the projection
  `view : σ → V`. Generic; protocols (AVSS, Bracha-RBC, Lock-step
  consensus, …) instantiate `V` and `view` to capture what their
  corrupt coalition actually observes (corrupt local states +
  observed in-flight messages, etc.).

* `RushingAdversary σ ι V` — bundles a `ProtocolView` together with
  a deterministic schedule `List (V × Option ι) → Option ι` that
  takes the *view-history* (rather than the full
  state-history) and a static corruption set. The adapter
  `toAdversary` lifts a rushing adversary back to a plain
  `Adversary σ ι` by mapping `view` over each element of the
  history before consulting the rushing schedule.

By construction `(R.toAdversary).schedule` factors through `view`,
which is the cryptographic content used downstream by
`schedule_factors_through_view` (Phase 7.4) to argue that under a
`RushingAdversary` the schedule prefix at step `k` is a measurable
function of the view-history prefix.

Like the plain `Adversary` structure above, no measurability
typeclasses are imposed *here*; they are required only at
`Trace.traceDist` call sites where the per-step kernel needs
`Kernel.ofFunOfCountable`. This keeps the file Mathlib-light and
matches the existing `Adversary` design.

The structure carries only the projection `view`. Measurability of
`view` (when needed by a particular protocol's downstream theorems)
is provided as a separate `Measurable` hypothesis at use sites,
matching how the plain `Adversary` keeps measurability concerns out
of this file. -/
structure ProtocolView (σ : Type*) (V : Type*) where
  /-- The view that a corrupt coalition sees of a state. -/
  view : σ → V

/-- A *rushing* (view-restricted) adversary: the schedule depends
only on the view-history of `(view-of-state, action)` pairs, not on
the full state-history.

Mirrors `Adversary` but with the schedule re-typed to take
`List (V × Option ι)` (the view-history) instead of
`List (σ × Option ι)` (the full history). Recoverable as a plain
`Adversary` via `toAdversary`. -/
structure RushingAdversary (σ : Type*) (ι : Type*) (V : Type*) where
  /-- The protocol view carried by this adversary. -/
  toProtocolView : ProtocolView σ V
  /-- View-restricted schedule: choose an action label (or `none`)
  given the view-history. -/
  schedule : List (V × Option ι) → Option ι
  /-- Static corruption set, identically to a plain `Adversary`. -/
  corrupt  : Set PartyId

namespace RushingAdversary

variable {σ ι V : Type*}

/-- Convenience accessor: the projection `σ → V` of a rushing
adversary's protocol view. -/
def view (R : RushingAdversary σ ι V) : σ → V :=
  R.toProtocolView.view

/-- Lift a state-history to a view-history by applying `view`
component-wise. The helper is internal; we expose its `rfl`
reduction `viewHistory_eq_map` below for downstream rewriting. -/
def viewHistory (R : RushingAdversary σ ι V)
    (h : List (σ × Option ι)) : List (V × Option ι) :=
  h.map (fun sa => (R.view sa.1, sa.2))

/-- Adapter: every `RushingAdversary` is in particular an
`Adversary`. The schedule is obtained by applying `view`
component-wise to the state-history before consulting the
rushing-schedule.

This is the formal content of "every rushing adversary is in
particular an adversary"; the converse (when does an adversary
factor through some view?) is the cryptographic content captured
later by `schedule_factors_through_view`. -/
def toAdversary (R : RushingAdversary σ ι V) : Adversary σ ι where
  schedule h := R.schedule (R.viewHistory h)
  corrupt    := R.corrupt

@[simp]
theorem toAdversary_corrupt (R : RushingAdversary σ ι V) :
    R.toAdversary.corrupt = R.corrupt := rfl

@[simp]
theorem toAdversary_schedule (R : RushingAdversary σ ι V)
    (h : List (σ × Option ι)) :
    R.toAdversary.schedule h = R.schedule (R.viewHistory h) := rfl

@[simp]
theorem viewHistory_eq_map (R : RushingAdversary σ ι V)
    (h : List (σ × Option ι)) :
    R.viewHistory h = h.map (fun sa => (R.view sa.1, sa.2)) := rfl

@[simp]
theorem viewHistory_nil (R : RushingAdversary σ ι V) :
    R.viewHistory ([] : List (σ × Option ι)) = [] := rfl

@[simp]
theorem viewHistory_cons (R : RushingAdversary σ ι V)
    (sa : σ × Option ι) (h : List (σ × Option ι)) :
    R.viewHistory (sa :: h) =
      (R.view sa.1, sa.2) :: R.viewHistory h := rfl

/-- Sanity: the lifted schedule on a state-history depends on the
state component only via the chosen view. Two histories that map to
the same view-history yield the same schedule decision. -/
theorem toAdversary_schedule_congr_of_viewHistory
    (R : RushingAdversary σ ι V)
    (h₁ h₂ : List (σ × Option ι))
    (hview : R.viewHistory h₁ = R.viewHistory h₂) :
    R.toAdversary.schedule h₁ = R.toAdversary.schedule h₂ := by
  simp only [toAdversary_schedule, hview]

end RushingAdversary

end Leslie.Prob
