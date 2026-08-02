import TlaDsl.Basic
import TlaDsl.Notation
import TlaDsl.Coercion
import TlaDsl.Prime
import TlaDsl.Rules
import TlaDsl.Tactic
import TlaDsl.TlaVar

open scoped Tla

/-! # Liveness example: strong fairness (SF1)

A "set the flag" action `Set` under strong fairness: the spec increments a
counter forever, and `Set` (enabled whenever the flag is still down) marks
the work as done. `SF_v(Set)` forces the flag to be set eventually.

Note on the enablement premise: the semantically proved `sf1` asks for
`Enabled ⟨A⟩_v` at some later position along *every* behavior. Under a
stuttering semantics the only form that holds unconditionally is immediate
enablement (`j = 0`) — a behavior may stutter forever, so a spec-relative
"eventually enabled" premise (`p ∧ [N]_v ⇒ ◇ Enabled ⟨A⟩_v`) is the
standard-form SF1 and is tracked as the follow-up refinement of the rule.
-/

namespace TlaDsl.Examples.StrongFair

structure St where
  n : Nat
  done : Nat
deriving Repr

tla_var St n done

/-- The counter increments; the flag is untouched. -/
@[simp] def Next : Tla.Action St := [a| n' = n + 1 ∧ done' = done]

/-- The strong-fairness action: mark the work as done. -/
@[simp] def Set : Tla.Action St := [a| done' = 1 ∧ n' = n]

/-- The flag is down. -/
@[simp] def p : Tla.StatePred St := fun s => s.done = 0

/-- The flag is up. -/
@[simp] def q : Tla.StatePred St := fun s => s.done = 1

theorem hstep : ∀ s s', p s → Tla.StutAction Next (fun s : St => s) s s' → p s' ∨ q s' := by
  tla_grind

theorem haq : ∀ s s', p s → Tla.AngleAction Set (fun s : St => s) s s' → q s' := by
  tla_grind

theorem henable : ∀ e : Tla.Behavior St, ∀ k : Nat, p (e k) →
    ∃ j : Nat, Tla.Enabled (Tla.AngleAction Set (fun s : St => s)) (e (k + j)) := by
  intro e k hp
  refine ⟨0, ?_⟩
  refine ⟨{ n := (e k).n, done := 1 }, ?_, ?_⟩
  · tla_unfold
  · intro hEq
    have hd : 1 = (e k).done := congrArg St.done hEq
    simp [p] at hp
    omega

/-- Strong fairness on `Set` forces the flag to be set: `□[Next]_id ∧
SF_id(Set) ⊢ p ↝ q`. -/
theorem sf_liveness :
    Tla.Entails (Tla.tlaAnd (Tla.stutAlways Next (fun s : St => s))
        (Tla.SF_v Set (fun s : St => s)))
      (Tla.leadsTo (Tla.statePred p) (Tla.statePred q)) := by
  tla_sf1
  exact henable

end TlaDsl.Examples.StrongFair
