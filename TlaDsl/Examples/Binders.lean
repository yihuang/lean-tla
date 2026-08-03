import TlaDsl.Basic
import TlaDsl.Notation
import TlaDsl.Coercion
import TlaDsl.Prime
import TlaDsl.Rules
import TlaDsl.Tactic
import TlaDsl.TlaVar

open scoped Tla

/-! # Binder and conditional notation

The bracket macros now lift `∀`/`∃` (including the TLA-style
`∀ x ∈ S, ...` / `∃ x ∈ S, ...` bounded quantifiers over set-valued state
functions), `if-then-else`, and `→`/`⇒`. This example shows the notation in
the process-quantifier style that real TLA specs need, and proves a small
invariant with it.
-/

namespace TlaDsl.Examples.Binders

structure St where
  x : Nat
  done : Finset Nat

tla_var St x done

/-- Every finished process index is below `x`. -/
@[simp] def Bounded : Tla.StatePred St := [p| ∀ p ∈ done, p < x]

/-- Some process is finished. -/
@[simp] def SomeDone : Tla.StatePred St := [p| ∃ p ∈ done, p < x]

/-- The counter advances. -/
@[simp] def Next : Tla.Action St := [a| x' = x + 1 ∧ done' = done]

/-- Bounded quantifiers compile to exactly the plain lambda. -/
example : [p| ∀ p ∈ done, p < x] = fun s : St => ∀ p ∈ s.done, p < s.x := by
  rfl

example : [a| ∃ p ∈ done, x' = x + 1] = fun s s' : St => ∃ p ∈ s.done, s'.x = s.x + 1 := by
  rfl

/-- `if-then-else` and implication lift pointwise. -/
example : [p| if x = 0 then x < 2 else x > 1] =
    fun s : St => if s.x = 0 then s.x < 2 else s.x > 1 := by
  rfl

example : [p| x = 0 → done = ∅] = fun s : St => s.x = 0 → s.done = ∅ := by
  rfl

/-- Temporal existential quantification. -/
example : [t| ∃ n, Tla.always (Tla.statePred (fun s : St => s.x = n))] =
    Tla.tlaExists (fun n : Nat => Tla.always (Tla.statePred (fun s : St => s.x = n))) := by
  rfl

/-- If some process is finished, the counter is positive — proved with the
binder-notation predicate. -/
theorem some_done_implies_positive :
    Tla.Entails (Tla.statePred SomeDone) (Tla.statePred (fun s : St => 0 < s.x)) := by
  intro e h
  rcases h with ⟨p, hp, hlt⟩
  change 0 < (e 0).x
  have hlt' : p < (e 0).x := by simpa using hlt
  omega

/-- Bounded quantification is monotone in the set: fewer finished processes
keep the bound. (A plain set variable is written outside the brackets — the
brackets treat bare identifiers as state functions.) -/
theorem bounded_mono {s : St} {t : Finset Nat} (ht : t ⊆ s.done) :
    Bounded s → (fun u : St => ∀ p ∈ t, p < u.x) s := by
  intro hb p hp
  have hb' : ∀ p ∈ s.done, p < s.x := by simpa [Bounded, Tla.statePred] using hb
  exact hb' p (ht hp)

end TlaDsl.Examples.Binders
