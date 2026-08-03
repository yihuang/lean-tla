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

end Tla
