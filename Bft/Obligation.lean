import Bft.Core
import Bft.Rules
import Bft.RelRank
import Mathlib.Data.FinEnum

/-!
# Bft.Obligation — the obligation normalizer (M2)

Single-step certificate obligations (C1–C3, inductive-invariant steps, WF1
premises) always expand to the same shape:

```
∀ s s', Next s s' → φ s → q s' ∨ (φ s' ∧ Conserves δ s s')
```

This module is the tactic-layer machinery for discharging them
(docs/bft-design.md §3.2):

1. **Layered simp sets** — no all-or-nothing mega-simp (the lesson of
   lean-tla's 40-lemma `tla_unfold`). The state layer is user-extensible via
   the `tla_state` simp attribute.
2. **`tla_ob`** — the normalizer: introduces variables, unfolds
   `Conserves`/`Reduces` into element language (never `Set.ncard` — that is
   engine-internal), then tries `omega` and `grind`. On failure it reports
   **which layer** the residual goal belongs to (failure classification).
3. **`tla_rel_rank`** — Rule 6 entry point: applies
   `relational_ranking_rule`, names the four subgoals
   (`finiteness`/`C1`/`C2`/`C3`), runs `tla_ob` on each, and on failure
   reports the obligation's name together with its layer classification.
4. **`#tla_cex G to Q`** — two-state counterexamples: over a `FinEnum` state
   space, exhaustively searches for `s, s'` with `G s s' ∧ ¬ Q s s'`.
   A failed two-state obligation has such a pair; printing it is usually the
   fastest way to see *why* the proof failed.
-/

namespace Bft

open Lean Meta Elab Tactic Command

/-- User-extensible simp set for the state layer: register projections of the
user's state record, decidable guards, and local invariant facts here. -/
register_simp_attr tla_state

/-! ## The normalizer -/

/-- Unfold the ranking combinators into element language (and the state-layer
user set). Deliberately excludes `Set.ncard`: finiteness is an
engine-internal obligation, discharged by `finite_rank` or
`Set.Finite.subset`, not by unfolding. -/
macro "tla_ob_simp" : tactic =>
  `(tactic| simp only [Bft.Conserves, Bft.Reduces, Bft.ConservesFinset,
    Bft.ReducesFinset, Set.mem_ofPred_eq, Bft.StutAction, Bft.Unchanged,
    tla_state] at *)

/-- Finishers for a normalized obligation: `omega` first (cheap and
complete for the linear-arithmetic core), `grind` after. -/
macro "tla_ob_finish" : tactic =>
  `(tactic| first | omega | grind)

/-! ## Failure classification -/

/-- Does the goal mention any of the given constants? -/
def goalMentions (g : MVarId) (names : List Name) : MetaM Bool := do
  let t ← instantiateMVars (← g.getType)
  return names.any fun n => (t.find? fun e => e.isConstOf n).isSome

/-- Classify a residual obligation by layer, with a hint for the next step.
This is the first layer of engine diagnostics: the user should never see a
raw `grind` failure without knowing which layer the goal belongs to. -/
def classifyObligation (g : MVarId) : MetaM MessageData := do
  if ← goalMentions g [``Bft.always, ``Bft.eventually, ``Bft.leadsTo, ``Bft.later,
      ``Bft.WF_v, ``Bft.SF_v] then
    return m!"temporal residue — this is not a single-step obligation; \
      normalize with `tla_temporal` or pick a different rule"
  else if ← goalMentions g [``Bft.StutAction, ``Bft.AngleAction, ``Bft.Enabled,
      ``Bft.stutAlways] then
    return m!"action layer not unfolded — run `tla_action` first"
  else if ← goalMentions g [``Set.ncard] then
    return m!"finiteness obligation — engine-internal; do not unfold \
      `Set.ncard`, discharge via `finite_rank` or a `Set.Finite.subset` argument"
  else if ← goalMentions g [``Bft.Conserves, ``Bft.Reduces, ``Bft.ConservesFinset,
      ``Bft.ReducesFinset] then
    return m!"ranking obligation not normalized — `tla_ob` unfolds \
      Conserves/Reduces into element language"
  else
    return m!"two-state obligation — if the residual goal looks false, \
      `#tla_cex G to Q` searches for a counterexample pair over a `FinEnum` \
      state space"

/-! ## `tla_ob` -/

/-- The obligation normalizer: introduce everything, unfold the ranking
combinators into element language, then try `omega`/`grind` per residual
goal. Unsolved goals are kept and reported with their layer classification. -/
elab "tla_ob" : tactic => do
  evalTactic (← `(tactic| (intros; tla_ob_simp)))
  let mut remaining : List MVarId := []
  for g in (← getUnsolvedGoals) do
    setGoals [g]
    try evalTactic (← `(tactic| tla_ob_finish)) catch _ => pure ()
    remaining := remaining ++ (← getUnsolvedGoals)
  setGoals remaining
  for g in remaining do
    logWarningAt (← getRef) m!"tla_ob: obligation remains — {← classifyObligation g}"

/-! ## `tla_rel_rank` -/

/-- Rule 6 entry point: `tla_rel_rank φ δ R r` applies
`relational_ranking_rule`, names the subgoals (`finiteness`/`C1`/`C2`/`C3`),
and runs `tla_ob` on each. Failures are reported with the obligation's name
and layer classification; unsolved goals remain for manual proof. -/
elab "tla_rel_rank" φ:term δ:term r:term rr:term : tactic => do
  evalTactic (← `(tactic|
    apply Bft.relational_ranking_rule (φ := $φ) (δ := $δ) (r := $rr) (R := $r)))
  let names := #["finiteness", "C1", "C2", "C3"]
  let gs ← getUnsolvedGoals
  let offset := names.size - min names.size gs.length
  let mut remaining : List MVarId := []
  for i in [:gs.length] do
    let g := gs[i]!
    let name := if h : i + offset < names.size then names[i + offset]
      else s!"subgoal {i + 1}"
    setGoals [g]
    try evalTactic (← `(tactic| tla_ob)) catch _ => pure ()
    let rem ← getUnsolvedGoals
    unless rem.isEmpty do
      logErrorAt (← getRef)
        m!"tla_rel_rank: obligation {name} failed — {← classifyObligation rem[0]!}"
    remaining := remaining ++ rem
  setGoals remaining

/-! ## Two-state counterexamples -/

/-- Exhaustive search for a two-state witness of `P` over a `FinEnum` state
space. A two-state obligation `∀ s s', G s s' → Q s s'` fails exactly when
`findCex2 (fun s s' => decide (G s s' ∧ ¬ Q s s'))` is `some`. -/
def findCex2 {σ : Type u} [FinEnum σ] (P : σ → σ → Bool) : Option (σ × σ) :=
  (FinEnum.toList σ).findSome? fun s =>
    (FinEnum.toList σ).findSome? fun s' =>
      if P s s' then some (s, s') else none

/-- Soundness of the search: a returned pair is a genuine witness. -/
theorem findCex2_some {σ : Type u} [FinEnum σ] {P : σ → σ → Bool} {w : σ × σ} :
    findCex2 P = some w → P w.1 w.2 = true := by
  intro h
  rw [findCex2, List.findSome?_eq_some_iff] at h
  rcases h with ⟨_l₁, s, _l₂, _hcat, hsome, _hnone⟩
  rw [List.findSome?_eq_some_iff] at hsome
  rcases hsome with ⟨_m₁, s', _m₂, _hcat2, hsome2, _hnone2⟩
  split at hsome2
  next hP =>
    injection hsome2 with hh
    rw [← hh]
    exact hP
  next => contradiction

/-- `#tla_cex G to Q` searches for a counterexample to the two-state obligation
`∀ s s', G s s' → Q s s'` over a `FinEnum` state space. Prints
`some (s, s')` with `G s s' ∧ ¬ Q s s'`, or `none` if the obligation holds
(on the finite space). Requires `FinEnum σ`, decidable `G`/`Q`, `Repr σ`. -/
syntax (name := tlaCex) "#tla_cex " term "to" term : command

@[command_elab tlaCex]
unsafe def elabCex : CommandElab := fun stx =>
  match stx with
  | `(#tla_cex $G:term to $Q:term) => runTermElabM fun _ => do
    let e ← Term.elabTerm
      (← `(reprStr (Bft.findCex2 (fun s s' => decide (($G) s s' ∧ ¬ ($Q) s s')))))
      (some (mkConst ``String))
    Term.synthesizeSyntheticMVarsNoPostponing
    let s ← Meta.evalExpr String (mkConst ``String) (← instantiateMVars e)
    logInfo m!"{s}"
  | _ => throwUnsupportedSyntax

end Bft
