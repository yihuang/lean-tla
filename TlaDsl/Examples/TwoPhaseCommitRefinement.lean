import TlaDsl.Meta
import TlaDsl.Examples.TwoPhaseCommit

open scoped Tla

/-! # Two-phase commit refines atomic two-phase commit

The classic refinement (Lamport, *Specifying Systems*, ch. 14): the concrete
2PC protocol — where participants **prepare** one by one, and only then does
the coordinator decide and the participants follow — refines an **abstract
atomic** 2PC in which the coordinator decides immediately and participants
commit/abort afterwards. The refinement mapping

```
f s := { coord := s.coord, part := fun i => if s.part i = prepared then working else s.part i }
```

maps the intermediate `prepared` phase back to `working`: from the abstract
spec's point of view, a prepared-but-undecided participant is still
undecided. Under this mapping every concrete step is either an abstract
step (the coordinator deciding, participants committing/aborting) or an
abstract stutter (a participant preparing). This is exactly the Abadi–Lamport
refinement-mapping condition, applied with the `refine_via` tactic.
-/

namespace TlaDsl.Examples.TwoPhaseCommitRefinement

open TlaDsl.Examples.TwoPhaseCommit

/-! ## The abstract atomic spec -/

/-- The coordinator commits atomically (no prepare round). -/
@[simp] def AbsCoordCommit : Tla.Action St :=
  [a| coord = .working ∧ coord' = .committed ∧ part' = part]

/-- The coordinator aborts; like the concrete action it is idempotent (not
committed, not not-yet-started). -/
@[simp] def AbsCoordAbort : Tla.Action St :=
  [a| coord ≠ .committed ∧ coord' = .aborted ∧ part' = part]

/-- Participant `i` commits after the coordinator committed. -/
@[simp] def AbsRmCommit (i : Nat) : Tla.Action St :=
  [a| coord = .committed ∧ part' = Function.update part i .committed ∧ coord' = coord]

/-- Participant `i` aborts after the coordinator aborted. -/
@[simp] def AbsRmAbort (i : Nat) : Tla.Action St :=
  [a| coord = .aborted ∧ part' = Function.update part i .aborted ∧ coord' = coord]

@[simp] def AbsNext (i : Nat) : Tla.Action St :=
  [a| AbsCoordCommit ∨ AbsCoordAbort ∨ AbsRmCommit i ∨ AbsRmAbort i]

def AbsSpec (i : Nat) : Tla.Pred St :=
  [t| Init ∧ □[AbsNext i]_vars]

/-! ## The refinement mapping -/

/-- Prepared participants are still undecided from the abstract point of
view. -/
@[simp] def f : St → St :=
  fun s => { coord := if s.coord = .prepared then .working else s.coord,
             part := fun i => if s.part i = .prepared then .working else s.part i }

theorem init_refines : ∀ s, Init s → Init (f s) := by
  intro s hs
  tla_unfold
  rcases hs with ⟨hcoord, hpart⟩
  constructor
  · simp [hcoord]
  · intro j
    simp [hpart j]

/-- Every concrete step (or `vars`-stutter) maps to an abstract step (or
`vars`-stutter): preparing stutters abstractly; deciding and following map
to the atomic abstract actions. -/
theorem step_refines (i : Nat) : ∀ s s', (Next i s s' ∨ vars s' = vars s) →
    (AbsNext i (f s) (f s') ∨ vars (f s') = vars (f s)) := by
  intro s s' h
  rcases h with hnext | hstut
  · tla_unfold
    rcases hnext with h1 | h2 | h3 | h4 | h5
    · -- RmPrepare i: only participant i changes, from working to prepared;
      -- both map to working, so the abstract state stutters.
      rcases h1 with ⟨hpart, hupdate, hcoord⟩
      right
      have hc : (f s').coord = (f s).coord := by simp [hcoord]
      have hp : (f s').part = (f s).part := by
        funext j
        simp [f]
        by_cases hji : j = i
        · subst j
          simp [hpart, hupdate]
        · simp [hji, hupdate]
      exact ⟨hc, hp⟩
    · -- CoordCommit: coordinator prepared → committed (abstract: working →
      -- committed), participants unchanged (all prepared → working).
      rcases h2 with ⟨hcoordP, hallP, hcoordC, hpartU⟩
      left
      left
      constructor
      · simp [hcoordP]
      · constructor
        · simp [hcoordC]
        · funext j
          simp [hpartU]
    · -- RmCommit i: coordinator committed, participant i commits.
      rcases h3 with ⟨hcoordC, hupdate, hcoord⟩
      left
      right
      right
      left
      constructor
      · simp [hcoordC]
      · constructor
        · funext j
          by_cases hji : j = i
          · subst j
            simp [hupdate]
          · simp [hji, hupdate]
        · simp [hcoord]
    · -- CoordAbort: coordinator aborts (abstract: working → aborted, or
      -- idempotent from aborted).
      rcases h4 with ⟨hcoordNC, hcoordA, hpartU⟩
      left
      right
      left
      constructor
      · by_cases h : s.coord = .prepared
        · simp [h]
        · simp [h, hcoordNC]
      · constructor
        · simp [hcoordA]
        · funext j
          simp [hpartU]
    · -- RmAbort i: coordinator aborted, participant i aborts.
      rcases h5 with ⟨hcoordA, hupdate, hcoord⟩
      left
      right
      right
      right
      constructor
      · simp [hcoordA]
      · constructor
        · funext j
          by_cases hji : j = i
          · subst j
            simp [hupdate]
          · simp [hji, hupdate]
        · simp [hcoord]
  · -- concrete stutter maps to abstract stutter
    right
    change f s' = f s
    have hstut' : s' = s := by simpa [vars] using hstut
    rw [hstut']

/-- The concrete 2PC refines the abstract atomic 2PC. -/
theorem conc_refines_abs (i : Nat) : Tla.RefinesVia f (Spec i) (AbsSpec i) := by
  unfold Spec AbsSpec
  refine_via f
  · exact step_refines i

end TlaDsl.Examples.TwoPhaseCommitRefinement
