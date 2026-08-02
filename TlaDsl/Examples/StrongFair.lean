import TlaDsl.Basic
import TlaDsl.Notation
import TlaDsl.Coercion
import TlaDsl.Prime
import TlaDsl.Rules
import TlaDsl.Tactic
import TlaDsl.TlaVar

open scoped Tla

/-! # Liveness example: strong fairness (SF1, standard form)

The counter `n` increments forever; the action `A` is enabled exactly when
`n` is even, and firing it marks the work as done. Because the increments
alternate parity, `A` is enabled *infinitely often* along progressing
behaviors — but never *eventually always* (it is disabled at every odd
counter value). Weak fairness would not suffice; strong fairness
`SF_id(A)` forces the flag to be set.

This is the standard-form SF1 (`sf1_standard`): the enablement premise is
spec-relative — `p ∧ [N]_v ⇒ ◇ Enabled ⟨A⟩_v ∨ q` — and lives as a conjunct
of the spec. (The `sf1` variant asks for enablement along every behavior,
which under stuttering semantics is only usable when enablement is
immediate.)
-/

namespace TlaDsl.Examples.StrongFair

structure St where
  n : Nat
  done : Nat
deriving Repr

tla_var St n done

/-- The counter increments; when it is even, the work may be marked done. -/
@[simp] def Next : Tla.Action St :=
  [a| (n' = n + 1 ∧ done' = done) ∨ (n % 2 = 0 ∧ n' = n + 1 ∧ done' = 1)]

/-- The strong-fairness action: mark the work as done (on an even tick). -/
@[simp] def A : Tla.Action St := [a| n % 2 = 0 ∧ n' = n + 1 ∧ done' = 1]

/-- The flag is down. -/
@[simp] def p : Tla.StatePred St := fun s => s.done = 0

/-- The flag is up. -/
@[simp] def q : Tla.StatePred St := fun s => s.done = 1

theorem hstep : ∀ s s', p s → Tla.StutAction Next (fun s : St => s) s s' → p s' ∨ q s' := by
  tla_grind

theorem haq : ∀ s s', p s → Tla.AngleAction A (fun s : St => s) s s' → q s' := by
  tla_grind

/-- Strong fairness on `A` forces the flag to be set: under
`□[Next]_id ∧ SF_id(A)` plus the standard-form enablement premise
`p ∧ [Next]_id ⇒ ◇ Enabled ⟨A⟩_id ∨ q`, `p` leads to `q`. -/
theorem sf_liveness :
    Tla.Entails
      (Tla.tlaAnd (Tla.tlaAnd (Tla.stutAlways Next (fun s : St => s))
          (Tla.SF_v A (fun s : St => s)))
        (Tla.always (Tla.tlaImp
          (Tla.tlaAnd (Tla.statePred p) (Tla.actionPred (Tla.StutAction Next (fun s : St => s))))
          (Tla.tlaOr (Tla.eventually (Tla.statePred (Tla.Enabled (Tla.AngleAction A (fun s : St => s)))))
            (Tla.statePred q)))))
      (Tla.leadsTo (Tla.statePred p) (Tla.statePred q)) := by
  tla_sf1_standard

end TlaDsl.Examples.StrongFair
