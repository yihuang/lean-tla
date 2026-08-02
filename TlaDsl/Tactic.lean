import TlaDsl.Rules
import TlaDsl.Prime

namespace Tla

/-! # Tactics

Thin tactic layer: unfold the DSL definitions, and apply the invariant
induction theorem. The point of the prototype is to see how much of the
proof ceremony this removes.
-/

/-- Unfold DSL definitions in the goal and all hypotheses. -/
macro "tla_unfold" : tactic =>
  `(tactic| (try simp [Tla.always, Tla.eventually, Tla.later, Tla.leadsTo, Tla.strongUntil,
    Tla.WF, Tla.SF, Tla.WF_v, Tla.SF_v, Tla.stutAlways, Tla.statePred, Tla.actionPred, Tla.purePred,
    Tla.tlaAnd, Tla.tlaOr, Tla.tlaNot, Tla.tlaImp, Tla.tlaIff, Tla.tlaTrue,
    Tla.tlaFalse, Tla.Valid, Tla.Entails, Tla.Satisfies, Tla.Enabled,
    Tla.Unchanged, Tla.StutAction, Tla.AngleAction, Tla.Behavior.drop,
    Tla.stEq, Tla.stNe, Tla.stAnd, Tla.stOr, Tla.stNot, Tla.stImp,
    Tla.stAdd, Tla.stSub, Tla.stMul, Tla.stLt, Tla.stLe,
    Tla.actEq, Tla.actNe, Tla.actAnd, Tla.actOr, Tla.actNot,
    Tla.actAdd, Tla.actSub, Tla.actMul, Tla.actLt, Tla.actLe] at *))

/-- Apply the stuttering-aware invariant induction theorem. Leaves the init
and step cases as goals. -/
macro "tla_inv" : tactic => `(tactic| (apply Tla.init_invariant_stut))

end Tla
