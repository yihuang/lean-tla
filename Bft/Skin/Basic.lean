import Bft.Core

/-! # Bft.Skin.Basic — kernel complements used only by the syntax skin

The kernel (`Bft.Core`) deliberately stays minimal. The few operators the
syntax layer needs but the proof layer never used live here instead, so the
skin is a genuinely replaceable layer: delete `Bft/Skin/` and nothing in
`Bft/` changes.

* `tlaIff`, `strongUntil`, `Satisfies`: notation targets (`↔`, `𝑈`, `⊨`).
* `CorrectAct`: the honest-processor guard, target of the `[c| Byz, p | body]`
  bracket.
* The `GetElem` instance for functions: TLA stores per-process state as
  functions and reads it as `f[i]`; Lean has no `GetElem (α → β)` instance,
  so the skin provides the total one (`f[i]` is definitionally `f i`).
-/

namespace Bft

/-- `P 𝑈 Q`: strong until. -/
def strongUntil {σ : Type u} (P Q : Pred σ) : Pred σ :=
  fun e => ∃ n, Q (e.drop n) ∧ ∀ m, m < n → P (e.drop m)

/-- Satisfaction: `e ⊨ F`. -/
def Satisfies {σ : Type u} (e : Behavior σ) (F : Pred σ) : Prop := F e

/-- `P ↔ Q` at the formula level. -/
def tlaIff {σ : Type u} (F G : Pred σ) : Pred σ := fun e => F e ↔ G e

/-- The honest-processor guard for Byzantine specs: the action `a` of
processor `p` (with Byzantine set `Byz`), i.e. `p ∉ Byz ∧ a`. Every
correct-processor action in a Byzantine protocol starts with this guard, so
the bracket notation `[c| Byz, p | body]` expands to
`CorrectAct Byz p [a| body]`. -/
def CorrectAct {σ : Type u} {α : Type v} [DecidableEq α] (Byz : Finset α) (p : α)
    (a : Action σ) : Action σ :=
  fun s s' => p ∉ Byz ∧ a s s'

/-- Function indexing (`f[i]`): the total `GetElem` instance for function
types, so per-process state functions read like TLA's `proc[i]`. -/
instance instGetElemFunction {α : Type u} {β : Type v} :
    GetElem (α → β) α β (fun _ _ => True) where
  getElem f i _ := f i

end Bft
