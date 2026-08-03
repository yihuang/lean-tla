import TlaDsl.Basic
import TlaDsl.Notation
import TlaDsl.Coercion
import TlaDsl.Prime
import TlaDsl.Rules
import TlaDsl.Tactic
import TlaDsl.TlaVar

open scoped Tla

/-! # Two-phase commit: agreement safety

The classic TLA+ case study (Specifying Systems, ch. 14), in the typed DSL.
One coordinator (`coord`) and unboundedly many participants (`part : Nat →
Phase`). Participants vote by preparing; the coordinator commits only after
every participant prepared, and aborts otherwise; a participant commits or
aborts only after the coordinator has decided. The safety property is
*agreement*: no participant is committed unless the coordinator is
committed, and none is aborted unless the coordinator is aborted.

This exercises the TLA-function machinery: `part[i]` reads, `part'[i]`
primed reads, and the `[part EXCEPT ![i] = st]` update pattern
(`Function.update`) for local participant updates.
-/

namespace TlaDsl.Examples.TwoPhaseCommit

/-- The local phase of the coordinator or a participant. -/
inductive Phase : Type where
  | working | prepared | committed | aborted
  deriving DecidableEq, Repr

structure St where
  coord : Phase
  part : Nat → Phase

tla_var St coord part

/-! ## The protocol actions -/

/-- Participant `i` votes to commit. -/
@[simp] def RmPrepare (i : Nat) : Tla.Action St :=
  [a| part[i] = .working ∧
      part' = Function.update part i .prepared ∧
      coord' = coord]

/-- The coordinator commits: every participant must have voted. -/
@[simp] def CoordCommit : Tla.Action St :=
  [a| coord = .prepared ∧ (∀ i, part[i] = .prepared) ∧
      coord' = .committed ∧ part' = part]

/-- Participant `i` commits only after the coordinator did. -/
@[simp] def RmCommit (i : Nat) : Tla.Action St :=
  [a| coord = .committed ∧
      part' = Function.update part i .committed ∧
      coord' = coord]

/-- The coordinator aborts (before it commits). -/
@[simp] def CoordAbort : Tla.Action St :=
  [a| coord ≠ .committed ∧ coord' = .aborted ∧ part' = part]

/-- Participant `i` aborts only after the coordinator did. -/
@[simp] def RmAbort (i : Nat) : Tla.Action St :=
  [a| coord = .aborted ∧
      part' = Function.update part i .aborted ∧
      coord' = coord]

/-- A step: the acting participant `i` does one of the five actions. -/
@[simp] def Next (i : Nat) : Tla.Action St :=
  [a| RmPrepare i ∨ CoordCommit ∨ RmCommit i ∨ CoordAbort ∨ RmAbort i]

/-! ## Agreement -/

@[simp] def Init : Tla.StatePred St := [p| coord = .working ∧ ∀ i, part[i] = .working]

/-- No participant decides against the coordinator. -/
@[simp] def Agree : Tla.StatePred St :=
  [p| (∀ i, part[i] = .committed → coord = .committed) ∧
      (∀ i, part[i] = .aborted → coord = .aborted)]

def Spec (i : Nat) : Tla.Pred St := [t| Init ∧ □[Next i]_vars]

/-! ## Agreement is preserved by every step -/

theorem agree_step (i : Nat) : ∀ s s' : St, Next i s s' → Agree s → Agree s' := by
  intro s s' hnext hInv
  tla_unfold
  rcases hnext with h1 | h2 | h3 | h4 | h5
  · -- RmPrepare i: only participant i changes, to `prepared`.
    rcases h1 with ⟨hpart, hupdate, hcoord⟩
    constructor <;> intro j hj <;> by_cases hji : j = i
    · simp_all
    · have hpj : part s j = .committed := by
        simpa [hupdate, hji] using hj
      have hc : coord s = .committed := hInv.1 j hpj
      simpa [hcoord, hc]
    · simp_all
    · have hpj : part s j = .aborted := by
        simpa [hupdate, hji] using hj
      have hc : coord s = .aborted := hInv.2 j hpj
      simpa [hcoord, hc]
  · -- CoordCommit: the coordinator commits; participants unchanged.
    rcases h2 with ⟨hcoordP, hallP, hcoordC, hpartU⟩
    constructor <;> intro j hj <;> simp_all
  · -- RmCommit i: the coordinator is (and stays) committed.
    rcases h3 with ⟨hcoordC, hupdate, hcoord⟩
    constructor <;> intro j hj <;> by_cases hji : j = i
    · simp_all
    · simp [hcoord, hcoordC]
    · simp_all
    · have hc : coord s = .aborted := hInv.2 j (by simpa [hupdate, hji] using hj)
      exfalso
      simp [hcoordC] at hc
  · -- CoordAbort: the coordinator aborts; participants unchanged.
    rcases h4 with ⟨hcoordNC, hcoordA, hpartU⟩
    constructor <;> intro j hj <;> simp_all
  · -- RmAbort i: the coordinator is (and stays) aborted.
    rcases h5 with ⟨hcoordA, hupdate, hcoord⟩
    constructor <;> intro j hj <;> by_cases hji : j = i
    · simp_all
    · have hc : coord s = .committed := hInv.1 j (by simpa [hupdate, hji] using hj)
      exfalso
      simp [hcoordA] at hc
    · simp_all
    · simp [hcoord, hcoordA]

theorem stutter_agree : ∀ s s' : St, vars s' = vars s → Agree s → Agree s' := by
  intro s s' hstut hInv
  tla_unfold
  cases hstut
  exact hInv

theorem init_agree : ∀ s : St, Init s → Agree s := by
  intro s hs
  tla_unfold
  constructor <;> intro i hi <;> simp_all

/-- The canonical safety theorem: `Init ∧ □[Next]_vars ⊢ □Agree`. -/
theorem spec_entails_agree (i : Nat) :
    (Tla.tlaAnd (Tla.statePred Init) (Tla.stutAlways (Next i) vars)) ⊢ □ ⌜ Agree ⌝ := by
  apply Tla.init_invariant_stut
  · exact init_agree
  · intro s s' hstep hInv
    rcases hstep with hnext | hstut
    · exact agree_step i s s' hnext hInv
    · exact stutter_agree s s' hstut hInv

end TlaDsl.Examples.TwoPhaseCommit
