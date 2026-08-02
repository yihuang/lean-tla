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
    Tla.Unchanged, Tla.StutAction, Tla.AngleAction, Cslib.ωSequence.drop,
    Tla.stEq, Tla.stNe, Tla.stAnd, Tla.stOr, Tla.stNot, Tla.stImp,
    Tla.stAdd, Tla.stSub, Tla.stMul, Tla.stLt, Tla.stLe,
    Tla.stGt, Tla.stGe, Tla.stMod,
    Tla.actEq, Tla.actNe, Tla.actAnd, Tla.actOr, Tla.actNot,
    Tla.actAdd, Tla.actSub, Tla.actMul, Tla.actLt, Tla.actLe,
    Tla.actGt, Tla.actGe, Tla.actMod] at *))

/-- Apply the stuttering-aware invariant induction theorem. Leaves the init
and step cases as goals. -/
macro "tla_inv" : tactic => `(tactic| (apply Tla.init_invariant_stut))

/-- Unfold the DSL and finish with `grind` (SMT-style automation, from core
Lean; now the recommended workhorse for action-level obligations). -/
macro "tla_grind" : tactic =>
  `(tactic| (tla_unfold; grind))

/-- Apply the semantically proved WF1 rule to a goal of the shape
`⊢ Init ∧ □[N]_v ∧ WF_v(A) ⊢ P ↝ Q` (or the two-conjunct spec), leaving the
three obligation goals — the `[N]_v`-step case, the `⟨A⟩_v`-step case and the
enabledness — after discharging the simple ones with `tla_grind`. -/
macro "tla_wf1" : tactic =>
  `(tactic| (apply Tla.wf1 <;> try tla_grind))

/-- SF1 analogue of `tla_wf1`. -/
macro "tla_sf1" : tactic =>
  `(tactic| (apply Tla.sf1 <;> try tla_grind))

/-- Apply the standard-form SF1 rule (`sf1_standard`) — with the
spec-relative enablement premise `p ∧ [N]_v ⇒ ◇ Enabled ⟨A⟩_v ∨ q` as a
spec conjunct — leaving the two obligation goals (step case, angle-step
case). -/
macro "tla_sf1_standard" : tactic =>
  `(tactic| (apply Tla.sf1_standard <;> try tla_grind))

/-- Leads-to choreography: solve a `P ↝ Q` goal by assumption, disjunction
on the left, or transitivity through a chain of leads-to facts in context. -/
macro "tla_leads_to" : tactic => `(tactic| assumption)

macro_rules
  | `(tactic| tla_leads_to) => `(tactic| (first
      | assumption
      | exact Tla.leadsTo_or _ _ _ _ ⟨by assumption, by assumption⟩
      | exact Tla.leadsTo_trans_entails _ _ _ _ ⟨by assumption, by tla_leads_to⟩))

/-- Invariant-guided case split: apply `leads_to_cases` with the case
hypothesis `hcase` (a `p → p1 ∨ p2 ∨ p3` split under the invariant) and the
three case leads-to facts `h1 h2 h3`. -/
macro "tla_leads_to_cases" h1:ident h2:ident h3:ident hcase:term : tactic =>
  `(tactic| (exact Tla.leads_to_cases _ _ _ _ _ _ _ ($hcase) ($h1) ($h2) ($h3)))

end Tla
