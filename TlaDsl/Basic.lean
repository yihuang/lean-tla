import Cslib.Foundations.Data.OmegaSequence.Defs
import Cslib.Foundations.Data.OmegaSequence.Init

/-! # TLA-flavored DSL: core semantics

A semantics for a TLA-like specification language: behaviors, temporal
predicates, actions, stuttering, fairness.

Behaviors are CSLib's `ωSequence` (a rich wrapper around `ℕ → σ`), so the
library inherits its API (`drop`, `take`, `extract`, `const`, `map`, ...) and
simp lemmas instead of hand-rolling them.
-/

namespace Tla

/-- An infinite behavior: the states at every time step. Alias of
`Cslib.ωSequence`, so `e.drop n`, `e.take n`, `e.extract n m`, `e.map f`
and friends come from CSLib. -/
abbrev Behavior (σ : Type u) := Cslib.ωSequence σ
abbrev Pred (σ : Type u) := Behavior σ → Prop
abbrev StatePred (σ : Type u) := σ → Prop
abbrev Action (σ : Type u) := σ → σ → Prop

/-! ## Function indexing (`f[i]`)

TLA stores per-process state as functions (`proc : St → Nat → ProcState`)
and reads it as `proc[i]`. Lean has no `GetElem` instance for function
types, so we provide the total one: `f[i]` is definitionally `f i`.
-/

instance instGetElemFunction {α : Type u} {β : Type v} :
    GetElem (α → β) α β (fun _ _ => True) where
  getElem f i _ := f i

/-! ## Lifting between the three levels -/

/-- A state predicate seen as a temporal formula (only the first state matters). -/
def statePred {σ : Type u} (p : StatePred σ) : Pred σ := fun e => p (e 0)

/-- An action seen as a temporal formula (only the first two states matter). -/
def actionPred {σ : Type u} (a : Action σ) : Pred σ := fun e => a (e 0) (e 1)

/-- A pure proposition seen as a temporal formula. -/
def purePred {σ : Type u} (p : Prop) : Pred σ := fun _ => p

/-! ## Propositional connectives on temporal formulas -/

def tlaTrue {σ : Type u} : Pred σ := purePred True
def tlaFalse {σ : Type u} : Pred σ := purePred False
def tlaNot {σ : Type u} (F : Pred σ) : Pred σ := fun e => ¬ F e
def tlaAnd {σ : Type u} (F G : Pred σ) : Pred σ := fun e => F e ∧ G e
def tlaOr {σ : Type u} (F G : Pred σ) : Pred σ := fun e => F e ∨ G e
def tlaImp {σ : Type u} (F G : Pred σ) : Pred σ := fun e => F e → G e
def tlaIff {σ : Type u} (F G : Pred σ) : Pred σ := fun e => F e ↔ G e
def tlaForall {σ : Type u} {α : Type v} (f : α → Pred σ) : Pred σ := fun e => ∀ a, f a e
def tlaExists {σ : Type u} {α : Type v} (f : α → Pred σ) : Pred σ := fun e => ∃ a, f a e

/-! ## Temporal operators -/

/-- `□ F`: F holds at every suffix. -/
def always {σ : Type u} (F : Pred σ) : Pred σ := fun e => ∀ n, F (e.drop n)

/-- `◇ F`: F holds at some suffix. -/
def eventually {σ : Type u} (F : Pred σ) : Pred σ := fun e => ∃ n, F (e.drop n)

/-- `◯ F`: F holds at the next suffix. -/
def later {σ : Type u} (F : Pred σ) : Pred σ := fun e => F (e.drop 1)

/-- `P ↝ Q`: P leads to Q. -/
def leadsTo {σ : Type u} (P Q : Pred σ) : Pred σ := always (tlaImp P (eventually Q))

/-- `P 𝑈 Q`: strong until. -/
def strongUntil {σ : Type u} (P Q : Pred σ) : Pred σ :=
  fun e => ∃ n, Q (e.drop n) ∧ ∀ m, m < n → P (e.drop m)

/-! ## Satisfaction, validity, entailment -/

def Satisfies {σ : Type u} (e : Behavior σ) (F : Pred σ) : Prop := F e
def Valid {σ : Type u} (F : Pred σ) : Prop := ∀ e : Behavior σ, F e
def Entails {σ : Type u} (F G : Pred σ) : Prop := ∀ e : Behavior σ, F e → G e

/-! ## Actions and stuttering -/

/-- `Enabled A`: the action can fire. -/
def Enabled {σ : Type u} (a : Action σ) : StatePred σ := fun s => ∃ s', a s s'

/-- `Unchanged v`: the state function `v` does not change. -/
def Unchanged {σ : Type u} {α : Type v} (v : σ → α) : Action σ := fun s s' => v s' = v s

/-- `[A]_v = A ∨ Unchanged v`. -/
def StutAction {σ : Type u} {α : Type v} (a : Action σ) (v : σ → α) : Action σ :=
  fun s s' => a s s' ∨ v s' = v s

/-- `⟨A⟩_v = A ∧ v' ≠ v`. -/
def AngleAction {σ : Type u} {α : Type v} (a : Action σ) (v : σ → α) : Action σ :=
  fun s s' => a s s' ∧ v s' ≠ v s

/-- `□[A]_v`: every step either fires A or leaves `v` unchanged. -/
def stutAlways {σ : Type u} {α : Type v} (a : Action σ) (v : σ → α) : Pred σ :=
  always (actionPred (StutAction a v))

/-- Weak fairness: if `A` is eventually always enabled, it fires eventually. -/
def WF {σ : Type u} (a : Action σ) : Pred σ :=
  always (tlaImp (always (statePred (Enabled a))) (eventually (actionPred a)))

/-- Strong fairness: if `A` is enabled infinitely often, it fires eventually. -/
def SF {σ : Type u} (a : Action σ) : Pred σ :=
  always (tlaImp (always (eventually (statePred (Enabled a)))) (eventually (actionPred a)))

/-- Weak fairness of `A` with respect to the state function `v`. -/
def WF_v {σ : Type u} {α : Type v} (A : Action σ) (v : σ → α) : Pred σ :=
  always (tlaImp (always (statePred (Enabled (AngleAction A v))))
    (eventually (actionPred (AngleAction A v))))

/-- Strong fairness of `A` with respect to the state function `v`. -/
def SF_v {σ : Type u} {α : Type v} (A : Action σ) (v : σ → α) : Pred σ :=
  always (tlaImp (always (eventually (statePred (Enabled (AngleAction A v)))))
    (eventually (actionPred (AngleAction A v))))

end Tla
