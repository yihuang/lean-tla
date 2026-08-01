/-
M1 W1 acceptance test — fair coin flip.

Defines a 1-action `ProbActionSpec Bool Unit` whose single action is
"flip a fair coin" and verifies that the resulting single-step
transition is `PMF.uniform Bool`. This exercises every public entry
of `Leslie/Prob/PMF.lean` and `Leslie/Prob/Action.lean` together.

Per implementation plan v2.2 §M1 W1 acceptance: ~30 lines, pass = the
full API composes.
-/

import Leslie.Prob.Action
import Leslie.Prob.PMF

namespace Leslie.Examples.Prob.Smoke

open Leslie.Prob

/-- A 1-action spec on `Bool`: the single action `()` is always
enabled and produces the uniform distribution on `Bool`. -/
noncomputable def coinFlip : ProbActionSpec Bool Unit where
  init := fun s => s = false
  actions := fun () =>
    { gate := fun _ => True
      effect := fun _ _ => PMF.uniform Bool }

/-- The initial-state predicate selects exactly `false`. -/
example : coinFlip.init false := rfl

/-- Stepping the only action `()` from any pre-state yields the
uniform distribution on `Bool`. -/
example (s : Bool) : coinFlip.step () s = some (PMF.uniform Bool) :=
  ProbActionSpec.step_eq_some trivial

/-- The step distribution evaluated at `true` is `1/2`. Demonstrates
that the PMF wrapper composes with `uniform_apply`. -/
example : (PMF.uniform Bool) true = 2⁻¹ := by
  rw [PMF.uniform_apply]
  norm_num

end Leslie.Examples.Prob.Smoke
