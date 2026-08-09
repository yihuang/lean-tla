import Bft.Core

namespace Bft

/-! # Bft.Skin.Coercion — implicit lifting (experimental)

A global `Coe` that lets state predicates appear directly where temporal
formulas are expected (e.g. `[t| Init ∧ ... ]` without `⌜ Init ⌝`), and
actions likewise (read as `actionPred`). This is the "invisible lifting" UX
experiment. If it causes inference surprises, drop this file and use explicit
`⌜ p ⌝` lifts.
-/

instance {σ : Type u} : Coe (σ → Prop) (Behavior σ → Prop) :=
  ⟨statePred⟩

/-- Actions appear directly where temporal formulas are expected
(e.g. `[t| ... ∧ □◇ PollA ∧ ... ]`). -/
instance {σ : Type u} : Coe (σ → σ → Prop) (Behavior σ → Prop) :=
  ⟨actionPred⟩

end Bft
