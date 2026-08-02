import TlaDsl.Basic
import TlaDsl.Notation
import TlaDsl.Coercion
import TlaDsl.Prime
import TlaDsl.Rules
import TlaDsl.Tactic
import TlaDsl.TlaVar

open scoped Tla

/-! # Counter: the "hello world" of the TLA-flavored DSL

Two counters incremented in lockstep; the invariant is `x = y`.
Shows the three notation levels: `[p| ...]` (state), `[a| ...]` (action with
primes), `[t| ...]` (temporal formula).
-/

namespace TlaDsl.Examples.Counter

structure St where
  x : Nat
  y : Nat
deriving Repr

/-! State functions ("variables" in TLA speak), declared with `tla_var`. -/

tla_var St x y

@[simp] def Init : Tla.StatePred St := [p| x = 0 ∧ y = 0]

@[simp] def Next : Tla.Action St := [a| x' = x + 1 ∧ y' = y + 1]

/-- The specification, written with `[t| ...]` sugar (implicit lifting via
`Coe` lifts `Init` automatically). -/
def Spec : Tla.Pred St := [t| Init ∧ □[Next]_vars]

/-- The same spec with explicit lifts, for comparison. -/
def Spec' : Tla.Pred St := Tla.tlaAnd ⌜ Init ⌝ (□[Next]_vars)

theorem init_ok : ∀ s, Init s → s.x = s.y := by
  intro s hs
  tla_unfold
  omega

theorem step_ok : ∀ s s', (Next s s' ∨ vars s' = vars s) → s.x = s.y → s'.x = s'.y := by
  intro s s' hstep hxy
  rcases hstep with hnext | hstut
  · tla_unfold
    omega
  · tla_unfold
    cases hstut
    exact hxy

theorem x_eq_y_invariant : Spec ⊢ □ ⌜ (fun s : St => s.x = s.y) ⌝ := by
  unfold Spec
  tla_inv
  · exact init_ok
  · exact step_ok

/-! ## A bounded sanity check ("model checking" by omega) -/

example : ∀ s s' : St, x s ≤ 3 → y s ≤ 3 → Next s s' → x s' ≤ 4 ∧ y s' ≤ 4 := by
  intro s s' hx hy hnext
  tla_unfold
  omega

/-! ## grind demo (SMT-style automation, mathlib-era) -/

example : ∀ s s' : St, Init s → Next s s' → x s' = 1 ∧ y s' = 1 := by
  intro s s' hs hnext
  tla_grind

example : ∀ s s' : St, x s ≤ 3 → y s ≤ 3 → Next s s' → x s' ≤ 4 ∧ y s' ≤ 4 := by
  intro s s' hx hy hnext
  tla_grind

end TlaDsl.Examples.Counter
