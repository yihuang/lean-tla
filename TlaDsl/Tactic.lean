import TlaDsl.Rules
import TlaDsl.Meta
import TlaDsl.Prime

import Lean

namespace Tla

open Lean Elab Tactic Meta

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

/-- **Invariant-preservation automation.** After a step proof has
established `s' = transformer s ...` and `subst s'`, `tla_inv_step` splits
the invariant structure in the goal (`Inv ... s'`), finds the pre-state
invariant hypothesis, and for each field tries, in order:

1. a definitional-equality check of <the corresponding pre-state field>
   against the goal (record-update projections reduce in the kernel, so
   `proposed`-only or `votes`-only changes are invisible to fields that do
   not mention the updated component);
2. `simpa [transformer] using <the corresponding pre-state field>` — the
   transformer is read from the goal's state expression (a record update,
   as in `Advance`, needs no lemmas);
3. the convention-named preservation lemma `⟨field⟩_⟨transformer⟩` (e.g.
   `votedEpoch_vote` for the `Inv.votedEpoch` field of `vote`), via
   `apply ⟨lemma⟩ <;> assumption`, which discharges fields whose proof
   needs case analysis on a `Function.update`-style state change.

Only the fields the action genuinely changes remain, in the structure's
field order, ready for bullets. -/
elab "tla_inv_step" : tactic => do
  -- identify the invariant structure from the goal: `Inv ... s'`
  let mvar ← getMainGoal
  let goalType := (← instantiateMVars (← mvar.getType)).consumeMData
  let invName ← match goalType.getAppFn with
    | Expr.const n _ => pure n
    | _ => throwError "tla_inv_step: goal is not an applied structure (expected `Inv ... state`)"
  let stateExpr ← match goalType.getAppArgs.toList.getLast? with
    | some st => pure st
    | none => throwError "tla_inv_step: goal is not an applied structure"
  -- the transformer def, if the state is an application of one
  let env ← getEnv
  let transformerName ← match stateExpr.getAppFn with
    | Expr.const n _ =>
        match env.find? n with
        | some (ConstantInfo.defnInfo _) => pure (some n)
        | _ => pure none
    | _ => pure none
  let simpLemma ← match transformerName with
    | some n => pure (some (← `(Parser.Tactic.simpLemma| $(mkIdent n):ident)))
    | none => pure none
  -- find the pre-state invariant hypothesis
  let ctx ← getLCtx
  let hInv ← ctx.findDeclM? fun d => do
    if d.isImplementationDetail then pure none
    else
      let ty ← instantiateMVars d.type
      match ty.consumeMData.getAppFn with
      | Expr.const n _ =>
          if n == invName then pure (some d) else pure none
      | _ => pure none
  let some hInv := hInv | throwError "tla_inv_step: no pre-state invariant hypothesis found"
  -- split the goal into the structure's fields
  try
    evalTactic (← `(tactic| constructor))
  catch _ => throwError "tla_inv_step: the goal is not a single-constructor structure"
  let goals := (← getGoals)
  if goals.isEmpty then return  -- single trivial field, already closed
  -- the structure's field projectors, in declaration order
  let env ← getEnv
  -- `constructor` introduces the fields in declaration order; `fieldNames`
  -- preserves that order (unlike `StructureInfo.fieldInfo`, which is sorted)
  let fields := (getStructureFields env invName).map
    (fun n => (getFieldInfo? env invName n).get!.projFn)
  if goals.length != fields.size then
    throwError "tla_inv_step: {goals.length} field goals but {fields.size} structure fields"
  -- convention-named preservation lemmas `⟨field⟩_⟨transformer⟩`, looked up
  -- next to the structure and at the root
  let convLemma : Name → Name → Option Name := fun proj transformer =>
    let fieldBase := (proj.toString.splitOn ".").getLast!
    let transformerBase := (transformer.toString.splitOn ".").getLast!
    let convStr := fieldBase ++ "_" ++ transformerBase
    let ns := proj.getPrefix.getPrefix
    if env.find? (ns.mkStr convStr) |>.isSome then
      some (ns.mkStr convStr)
    else if env.find? (Name.anonymous.mkStr convStr) |>.isSome then
      some (Name.anonymous.mkStr convStr)
    else none
  -- for each field subgoal, try the simplification route and then the
  -- convention lemma; unsolved goals are left for the user
  let hId := mkIdent hInv.userName
  let hFVar := mkFVar hInv.fvarId
  for (g, f) in goals.zip fields.toList do
    setGoals [g]
    let saved ← saveState
    -- attempt 1: the pre-state field is definitionally equal to the goal
    -- (the action does not touch the components the field mentions).  This
    -- is done at the meta level — unlike `exact`, a failed unification does
    -- not log error messages.
    let exactOk ← try
      let fieldName := f.toString.splitOn "." |>.getLast! |> Name.mkSimple
      let projExpr ← mkProjection hFVar fieldName
      isDefEq (mkMVar g) projExpr
    catch _ => pure false
    unless exactOk do
      saved.restore
      let tm ← `(term| $(mkIdent f) $hId)
      let tac ← match simpLemma with
        | some l => `(tactic| simpa [$l] using $tm)
        | none => `(tactic| simpa using $tm)
      -- `simpa` emits the `unnecessarySimpa` linter warning when the target
      -- does not change; that is the normal case here (the field was already
      -- in the right shape), so suppress it for the generated tactic.
      let simpaOk ← try
        withOptions (fun o => o.setBool `linter.unnecessarySimpa false) <| evalTactic tac
        pure (← g.isAssigned)
      catch _ => pure false
      unless simpaOk do
        saved.restore
        if let some n := transformerName.bind (convLemma f) then
          let convTac ← `(tactic| (apply $(mkIdent n) <;> assumption))
          try
            evalTactic convTac
          catch _ => saved.restore
    setGoals goals

end Tla
