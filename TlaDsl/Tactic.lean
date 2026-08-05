import TlaDsl.Rules
import TlaDsl.Meta
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

/-- Apply the rank-function leads-to rule (`leads_to_via_nat`), leaving the
per-rank obligation: each WF1/SF1 application only needs to show the rank
strictly decreases (or the goal is reached). -/
macro "tla_leads_to_via_nat " f:term : tactic =>
  `(tactic| (apply Tla.leads_to_via_nat _ _ $f <;> try tla_grind))

/-- Apply the relational-ranking liveness rule (`relational_ranking_rule`),
supplying the invariant `φ`, the relational ranking `δ` and the finite
envelope `R`; leaves the four obligations: `R` finite, and the C1/C2/C3
step premises (under the spec). -/
macro "tla_rel_rank " φ:term δ:term R:term : tactic =>
  `(tactic| (apply Tla.relational_ranking_rule _ _ _ $φ $δ $R <;> try tla_grind))

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

/-- Apply the Abadi–Lamport refinement-mapping theorem to a
`RefinesVia f conc abs` goal (with `conc`/`abs` in canonical
`Init ∧ □[Next]_v` form), leaving the initial-state and step mapping
obligations; `tla_grind` discharges the purely algebraic ones. -/
macro "refine_via " f:term : tactic =>
  `(tactic| (apply Tla.refinement_mapping _ _ _ _ _ _ $f <;> try tla_grind))

/-- The invariant-threaded variant of `refine_via`: applies
`refinement_mapping_inv`, additionally requiring the concrete invariant
`inv` to hold initially and be preserved (the step correspondence is then
only checked on reachable states). -/
macro "refine_via_inv " inv:term f:term : tactic =>
  `(tactic| (apply Tla.refinement_mapping_inv _ _ _ _ _ _ $inv $f <;> try tla_grind))

end Tla
