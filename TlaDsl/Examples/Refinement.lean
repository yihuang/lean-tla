import TlaDsl.Basic
import TlaDsl.Notation
import TlaDsl.Coercion
import TlaDsl.Prime
import TlaDsl.Meta
import TlaDsl.Tactic

open scoped Tla

/-! # Refinement example: two-counter concrete spec refines one-counter abstract

The extra variable `y` is invisible to the abstract spec. Every concrete step
or stutter maps to an abstract step or stutter, so by the Abadi–Lamport
refinement-mapping theorem the concrete spec refines the abstract one.
-/

namespace TlaDsl.Examples.CounterRefinement

structure StAbs where
  x : Nat
deriving Repr

structure StConc where
  x : Nat
  y : Nat
deriving Repr

@[simp] def xA : StAbs → Nat := StAbs.x
@[simp] def xC : StConc → Nat := StConc.x
@[simp] def yC : StConc → Nat := StConc.y

@[simp] def InitAbs : Tla.StatePred StAbs := [p| xA = 0]
@[simp] def NextAbs : Tla.Action StAbs := [a| xA' = xA + 1]
@[simp] def VarsAbs : StAbs → Nat := StAbs.x

@[simp] def InitConc : Tla.StatePred StConc := [p| xC = 0 ∧ yC = 0]
@[simp] def NextConc : Tla.Action StConc := [a| xC' = xC + 1 ∧ yC' = yC + 1]
@[simp] def VarsConc : StConc → Nat × Nat := fun s => (s.x, s.y)

def SpecAbs : Tla.Pred StAbs := [t| InitAbs ∧ □[NextAbs]_VarsAbs]
def SpecConc : Tla.Pred StConc := [t| InitConc ∧ □[NextConc]_VarsConc]

/-- The refinement mapping: project away the internal variable `y`. -/
def f : StConc → StAbs := fun s => { x := s.x }

theorem init_refines : ∀ s, InitConc s → InitAbs (f s) := by
  intro s hs
  tla_unfold
  simp [f] at hs ⊢
  exact hs.1

theorem step_refines : ∀ s s', (NextConc s s' ∨ VarsConc s' = VarsConc s) →
    (NextAbs (f s) (f s') ∨ VarsAbs (f s') = VarsAbs (f s)) := by
  intro s s' h
  rcases h with hnext | hstut
  · tla_unfold
    simp [f] at hnext ⊢
    omega
  · have hx' : s'.x = s.x := by simpa [VarsConc] using congrArg Prod.fst hstut
    right
    simp [f, hx']

theorem conc_refines_abs : Tla.RefinesVia f SpecConc SpecAbs := by
  unfold SpecConc SpecAbs
  exact Tla.refinement_mapping InitAbs NextAbs VarsAbs InitConc NextConc VarsConc f
    init_refines step_refines

/-! ## Refinement with liveness

The same mapping also refines the *full* canonical forms
`(Init ∧ □[Next]_v) ∧ L` when the liveness conjunct is preserved by the
mapping — the Abadi–Lamport theorem with liveness. -/

/-- Liveness conjunct: eventually the visible counter reaches 3. -/
def LConc : Tla.Pred StConc := [t| ◇ ⌜ (fun s : StConc => s.x = 3) ⌝]
def LAbs : Tla.Pred StAbs := [t| ◇ ⌜ (fun s : StAbs => s.x = 3) ⌝]

def SpecAbsL : Tla.Pred StAbs := [t| (InitAbs ∧ □[NextAbs]_VarsAbs) ∧ LAbs]
def SpecConcL : Tla.Pred StConc := [t| (InitConc ∧ □[NextConc]_VarsConc) ∧ LConc]

/-- The liveness conjunct is preserved by the projection mapping. -/
theorem liveness_refines : ∀ e : Tla.Behavior StConc,
    LConc e → LAbs (Cslib.ωSequence.map f e) := by
  intro e hL
  rcases hL with ⟨n, hp⟩
  exact ⟨n, by
    simp [Tla.statePred, f, Cslib.ωSequence.drop] at hp ⊢
    exact hp⟩

theorem conc_refines_abs_liveness :
    Tla.RefinesVia f SpecConcL SpecAbsL := by
  unfold SpecConcL SpecAbsL
  exact Tla.refinement_mapping_liveness InitAbs NextAbs VarsAbs InitConc NextConc VarsConc
    LConc LAbs f init_refines step_refines liveness_refines

end TlaDsl.Examples.CounterRefinement
