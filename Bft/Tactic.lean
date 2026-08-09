import Bft.Core
import Bft.Rules
import Bft.RelRank
import Bft.Obligation

/-!
# Bft.Tactic — the tactic layer

Principles (docs/bft-design.md §3.2):

1. Layered simp sets, no all-or-nothing mega-simp:
   - `tla_temporal`: temporal-layer unfolding (`always/eventually/leadsTo/...`);
   - `tla_action`: action-layer unfolding (`StutAction/AngleAction/Enabled/...`);
   - `tla_state`: state layer (user-registered `_apply` lemmas), defined in
     `Bft.Obligation`.
2. After `Conserves`/`Reduces` are unfolded, rewrite immediately back into
   the user's data-structure language; never unfold `Set.ncard` — that is
   engine-internal, not a user obligation.
3. One tactic per rule: `tla_inv` / `tla_wf1` / `tla_sf1` / `tla_rel_rank`
   (the latter lives in `Bft.Obligation` together with the obligation
   normalizer `tla_ob`, failure classification, and `#tla_cex`).
-/

namespace Bft

open Lean Elab Tactic

/-- Temporal-layer unfolding. -/
macro "tla_temporal" : tactic =>
  `(tactic| simp only [Bft.always, Bft.eventually, Bft.later, Bft.leadsTo,
    Bft.tlaAnd, Bft.tlaOr, Bft.tlaImp, Bft.tlaNot, Bft.statePred,
    Bft.actionPred, Bft.purePred, Bft.globalJustice, Bft.Entails])

/-- Action-layer unfolding. -/
macro "tla_action" : tactic =>
  `(tactic| simp only [Bft.StutAction, Bft.AngleAction, Bft.Enabled,
    Bft.Unchanged, Bft.WF_v, Bft.SF_v, Bft.stutAlways])

/-- Full unfolding (debug escape hatch; not recommended in scripts). -/
macro "tla_unfold" : tactic => `(tactic| (tla_temporal; tla_action))

/-- Inductive invariance: applies the stuttering version, leaving the
init/step obligations. -/
macro "tla_inv" : tactic => `(tactic| apply Bft.init_invariant_stut)

/-- Unfold then finish by grind: the workhorse for action-layer obligations. -/
macro "tla_grind" : tactic => `(tactic| (tla_unfold; grind))

/-- WF1: apply the rule, then try the easy obligations automatically. -/
macro "tla_wf1" : tactic => `(tactic| (apply Bft.wf1 <;> try tla_grind))

/-- SF1. -/
macro "tla_sf1" : tactic => `(tactic| (apply Bft.sf1 <;> try tla_grind))

/-- Certificate chaining: `cert₁.then cert₂ hH`. -/
theorem RelRankCert.then {σ : Type u} {p q q' : StatePred σ}
    (cert₁ : RelRankCert σ p q) (cert₂ : RelRankCert σ q q')
    (hH : ∀ e, tlaAnd cert₁.H (globalJustice cert₁.r) e →
      tlaAnd cert₂.H (globalJustice cert₂.r) e) :
    Entails (tlaAnd cert₁.H (globalJustice cert₁.r))
      (leadsTo (statePred p) (statePred q')) := by
  exact RelRankCert.trans cert₁ cert₂ hH

end Bft
