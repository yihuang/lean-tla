/-
M1 W1 — `ActionSpec → ProbActionSpec` coercion (skeleton).

Existing Leslie's `GatedAction.transition : σ → σ → Prop` is
relational; `ProbGatedAction.effect : (s : σ) → gate s → PMF σ` is
functional. Bridging requires a per-action successor function. M1 W1
takes the explicit-extractor approach: the user supplies
`succ : ι → σ → σ` witnessing the deterministic shape
`transition s s' ↔ s' = succ i s`. M1 W4 will add a
`Classical.choose`-based version for relational specs satisfying a
uniqueness hypothesis, and the level-2 conservativity theorems
(`invariant_preserved`, `refines_preserved`).
-/

import Leslie.Prob.Action
import Leslie.Action

namespace Leslie.Prob.ProbGatedAction

variable {σ : Type*}

/-- Dirac-effect constructor: gate plus a deterministic successor
function, lifted to a `ProbGatedAction` via `PMF.pure`. -/
noncomputable def dirac (gate : σ → Prop) (succ : σ → σ) : ProbGatedAction σ where
  gate   := gate
  effect := fun s _ => PMF.pure (succ s)

@[simp] theorem dirac_gate (gate : σ → Prop) (succ : σ → σ) :
    (dirac gate succ).gate = gate := rfl

@[simp] theorem dirac_effect (gate : σ → Prop) (succ : σ → σ) (s : σ) (h : gate s) :
    (dirac gate succ).effect s h = PMF.pure (succ s) := rfl

end Leslie.Prob.ProbGatedAction

namespace TLA.ActionSpec

variable {σ ι : Type*}

/-- Coerce a relational `ActionSpec` to a `ProbActionSpec` with Dirac
effects, given a per-action successor extractor. -/
noncomputable def toProbViaSucc
    (spec : TLA.ActionSpec σ ι) (succ : ι → σ → σ) :
    Leslie.Prob.ProbActionSpec σ ι where
  init    := spec.init
  actions := fun i =>
    Leslie.Prob.ProbGatedAction.dirac (spec.actions i).gate (succ i)

@[simp] theorem toProbViaSucc_init
    (spec : TLA.ActionSpec σ ι) (succ : ι → σ → σ) :
    (spec.toProbViaSucc succ).init = spec.init := rfl

@[simp] theorem toProbViaSucc_actions_gate
    (spec : TLA.ActionSpec σ ι) (succ : ι → σ → σ) (i : ι) :
    ((spec.toProbViaSucc succ).actions i).gate = (spec.actions i).gate := rfl

/-- Level-1 sanity: the coerced step on `s` is `Dirac (succ i s)`
when the gate holds. Level-2 (`invariant_preserved`,
`refines_preserved`) lands in M1 W4 with `Refinement.lean`. -/
theorem toProbViaSucc_step_eq_dirac
    (spec : TLA.ActionSpec σ ι) (succ : ι → σ → σ)
    (i : ι) (s : σ) (h : (spec.actions i).gate s) :
    (spec.toProbViaSucc succ).step i s = some (PMF.pure (succ i s)) :=
  Leslie.Prob.ProbActionSpec.step_eq_some h

end TLA.ActionSpec
