import TlaDsl.Rules
import TlaDsl.RelRank
import TlaDsl.Meta
import TlaDsl.Prime
import TlaDsl.Pretty

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

/-- **Spec-splitting for liveness obligations.** The relational-ranking
rules (Rule 6/10/11) leave obligations of the shape `∀ e, H e → ...` where
`H` is the spec: a nested `Tla.tlaAnd` of the init, the next-step and the
justice conjuncts. `tla_spec_split` binds the behavior as `e` and the spec
hypothesis as `hH`, walks the nested conjunction, and derives the named
facts the obligations need:

* `hInit0 : Init (e 0)` from a `Tla.statePred Init` leaf;
* `hNextAll : ∀ m, Next (e m) (e (m + 1))` from a
  `Tla.always (Tla.actionPred Next)` leaf, or
  `hStutAll : ∀ m, Tla.StutAction Next vars (e m) (e (m + 1))` from a
  `Tla.stutAlways Next vars` leaf;
* `hJ1`, `hJ2`, ... for every other leaf (the justice conjuncts), in
  left-to-right order.

The remaining binders (`k hp`, `k hφ`, `k _hφ i hψ`, ...) are left for the
user, together with the invariant induction and the per-step case split —
exactly the parts that are example-specific. -/
elab "tla_spec_split" : tactic => withMainContext do
  let g ← getMainGoal
  -- bind the behavior and the spec hypothesis with exact names
  let (_, g) ← liftMetaM (g.intro `e)
  let (_, g) ← liftMetaM (g.intro `hH)
  setGoals [g]
  let eId := mkIdent `e
  -- walk the nested `Tla.tlaAnd` right-spine with an explicit stack of
  -- hypothesis names, classifying each leaf by its (un-reduced) type
  let mut stack : Array Name := #[`hH]
  let mut jIdx : Nat := 0
  while !stack.isEmpty do
    let hCur := stack.back!
    stack := stack.pop
    -- look up the hypothesis in the *main goal's* metavariable context
    -- (`getLCtx` is stale here: it does not reflect `MVarId.intro`-created
    -- hypotheses)
    let hType ← do
      let mg ← getMainGoal
      let mdecl ← liftMetaM mg.getDecl
      let some hDecl ← mdecl.lctx.findDeclM? (fun d =>
          pure (if d.userName == hCur then some d else none))
        | throwError "tla_spec_split: hypothesis `{hCur}` not found"
      -- the type is read from the stored declaration (`inferType` on the
      -- fvar would hit the stale elaborator context)
      liftMetaM (instantiateMVars hDecl.type)
    -- `hTypeW` reduces spec *definitions* (`H e` → the nested `tlaAnd`).
    -- A leaf is recognized by its un-reduced head; in particular a
    -- `statePred` leaf must not be split just because its predicate
    -- unfolds to a conjunction (`Init (e 0)` is often one).
    let hTypeW ← liftMetaM (whnf hType)
    let isLeaf : Bool := match hType.getAppFn with
      | .const n _ => n == ``Tla.statePred || n == ``Tla.always || n == ``Tla.stutAlways
      | _ => false
    let isAnd : Bool := !isLeaf && (match hTypeW.getAppFn with
      | .const n _ => n == ``And
      | _ => false)
    if isAnd then
      let hL ← mkFreshUserName `hL
      let hR ← mkFreshUserName `hR
      let hId : Ident := mkIdent hCur
      evalTactic (← `(tactic|
        rcases $hId:term with ⟨$(mkIdent hL), $(mkIdent hR)⟩))
      -- push right first so the left conjunct is processed next
      stack := (stack.push hR).push hL
    else
      match hType.getAppFn with
      | .const n' _ =>
          if n' == ``Tla.statePred then
            evalTactic (← `(tactic| have $(mkIdent `hInit0) :=
              Tla.statePred_at_zero _ $eId $(mkIdent hCur)))
          else if n' == ``Tla.always then
            let inner := hType.getAppArgs[1]!
            match inner.getAppFn with
            | .const n'' _ =>
                if n'' == ``Tla.actionPred then
                  match inner.getAppArgs[1]!.getAppFn with
                  | .const n''' _ =>
                      if n''' == ``Tla.StutAction then
                        evalTactic (← `(tactic| have $(mkIdent `hStutAll) :=
                          Tla.stutAlways_next _ _ $eId $(mkIdent hCur)))
                      else
                        evalTactic (← `(tactic| have $(mkIdent `hNextAll) :=
                          Tla.always_actionPred_next _ $eId $(mkIdent hCur)))
                  | _ =>
                      jIdx := jIdx + 1
                      let nm := Name.mkSimple ("hJ" ++ toString jIdx)
                      evalTactic (← `(tactic| have $(mkIdent nm) := $(mkIdent hCur)))
                else
                  jIdx := jIdx + 1
                  let nm := Name.mkSimple ("hJ" ++ toString jIdx)
                  evalTactic (← `(tactic| have $(mkIdent nm) := $(mkIdent hCur)))
            | _ =>
                jIdx := jIdx + 1
                let nm := Name.mkSimple ("hJ" ++ toString jIdx)
                evalTactic (← `(tactic| have $(mkIdent nm) := $(mkIdent hCur)))
          else if n' == ``Tla.stutAlways then
            evalTactic (← `(tactic| have $(mkIdent `hStutAll) :=
              Tla.stutAlways_next _ _ $eId $(mkIdent hCur)))
          else
            jIdx := jIdx + 1
            let nm := Name.mkSimple ("hJ" ++ toString jIdx)
            evalTactic (← `(tactic| have $(mkIdent nm) := $(mkIdent hCur)))
      | _ =>
          jIdx := jIdx + 1
          let nm := Name.mkSimple ("hJ" ++ toString jIdx)
          evalTactic (← `(tactic| have $(mkIdent nm) := $(mkIdent hCur)))

/-- The invariant-threaded variant of `refine_via`: applies
`refinement_mapping_inv`, additionally requiring the concrete invariant
`inv` to hold initially and be preserved (the step correspondence is then
only checked on reachable states). -/
macro "refine_via_inv " inv:term f:term : tactic =>
  `(tactic| (apply Tla.refinement_mapping_inv _ _ _ _ _ _ $inv $f <;> try tla_grind))

/-- **`ωSequence`-conversion simpa.** `e (n + j)` and `(e.drop n) j` are
not definitionally equal, so suffix-level conversions need the drop lemmas
and Nat reassociations in the simp set; this bundles them (plus the spec
layer unfoldings used at those sites) so the conversion reads as one call:

```lean
have hp0 : ... := by tla_drop_simpa using hnone
```

instead of repeating `simpa [Cslib.ωSequence.drop, Nat.add_assoc,
Nat.add_comm, Nat.add_left_comm] using ...`. -/
syntax "tla_drop_simpa" (" using " term)? : tactic
macro_rules
  | `(tactic| tla_drop_simpa) =>
      `(tactic| simpa [Tla.statePred, Tla.actionPred, Tla.always,
        Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm])
  | `(tactic| tla_drop_simpa using $h) =>
      `(tactic| simpa [Tla.statePred, Tla.actionPred, Tla.always,
        Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using $h)

/-- **Safe equality-conjunction split.** `rcases h with ⟨rfl, rfl⟩` on
`j = i ∧ e' = b.epoch` substitutes the *right*-hand-side variables
(eliminating `i` and `b.epoch`), so later references to them fail with
"unknown identifier". `tla_rcases_subst h` splits the conjunction and
substitutes the *left*-hand-side variables by name instead (the same as
`rcases h with ⟨h1, h2⟩; subst j; subst e'`):

```lean
tla_rcases_subst hje
```
-/
elab "tla_rcases_subst " h:ident : tactic => withMainContext do
  let hDecl ← getLocalDeclFromUserName h.getId
  let hType ← instantiateMVars hDecl.type
  -- collect the left-hand-side variables of the equality conjunction
  -- `a = b ∧ c = d` (one or two equalities)
  let lhsVars ← liftMetaM do
    let hType ← whnf hType
    let eqs := match hType with
      | .app (.app (.const ``And _) eq1) eq2 => #[eq1, eq2]
      | .app (.app (.app (.const ``Eq _) _) _) _ => #[hType]
      | _ => #[]
    let mut lhs : Array FVarId := #[]
    for eq in eqs do
      let eq ← whnf eq
      match eq with
      | .app (.app (.app (.const ``Eq _) _) l) _ =>
          if l.isFVar then lhs := lhs.push l.fvarId!
      | _ => pure ()
    pure lhs
  if lhsVars.isEmpty then
    throwError "tla_rcases_subst: expected an equality or conjunction of equalities, got {hType}"
  -- split the conjunction so the equalities are separate hypotheses
  if hType.consumeMData.getAppFn.isConst && hType.consumeMData.getAppFn.constName! == ``And then
    evalTactic (← `(tactic| rcases $h:term with ⟨h1, h2⟩))
  -- `subst` on a variable finds the equality in the context and replaces
  -- the *left*-hand side, keeping the right-hand-side variables alive
  for v in lhsVars do
    let name := (← v.getDecl).userName
    evalTactic (← `(tactic| subst $(mkIdent name)))

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
elab "tla_inv_step" : tactic => withMainContext do
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
