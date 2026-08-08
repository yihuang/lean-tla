import TlaDsl.Basic

namespace Tla

/-! # Experimental: implicit lifting

A global `Coe` that lets state predicates appear directly where temporal
formulas are expected (e.g. `[t| Init ∧ ... ]` without `⌜ Init ⌝`).
This is the "invisible lifting" UX experiment. If it causes inference
surprises, drop this file and use explicit `⌜ p ⌝` lifts.
-/

instance {σ : Type u} : Coe (σ → Prop) (Behavior σ → Prop) :=
  ⟨statePred⟩

/-- Actions appear directly where temporal formulas are expected
(e.g. `[t| ... ∧ □◇ PollA ∧ ... ]`): the action is read as its
lifted temporal formula `◇ actionPred A`. This is the action half of the
"invisible lifting" experiment — state predicates lift via `statePred`,
actions via `actionPred`, so a spec reads like TLA:
`[t| Init ∧ □[Next]_vars ∧ □◇ Poll1A ∧ □◇ Poll2]`. -/
instance {σ : Type u} : Coe (σ → σ → Prop) (Behavior σ → Prop) :=
  ⟨actionPred⟩

end Tla
