import Lean
import TlaDsl.Basic
import TlaDsl.Notation

open scoped Tla

open Lean Macro

namespace Tla

/-! # Pseudocode action/state syntax

`[p| x = 0 ∧ y = 0]` elaborates to a `StatePred σ`, and
`[a| x' = x + 1 ∧ y' = y]` elaborates to an `Action σ`, by lifting the body
pointwise over a state (resp. pre/post state pair). `x'` denotes the post
state value of state function `x`, `x` the pre state value.

Supported inside the brackets: identifiers (declared state functions),
numerals, the operators `= ≠ < ≤ > ≥ + - * % ∧ ∨ ¬`, parentheses, and
function applications (e.g. `Even n`, `f x`) — the arguments are lifted
pointwise. Type ascriptions are ignored.
-/

/-! ## Pointwise operators at the state level -/

abbrev stEq {σ : Type u} {α : Type v} (f g : σ → α) : σ → Prop := fun s => f s = g s
abbrev stNe {σ : Type u} {α : Type v} (f g : σ → α) : σ → Prop := fun s => f s ≠ g s
abbrev stAnd {σ : Type u} (f g : σ → Prop) : σ → Prop := fun s => f s ∧ g s
abbrev stOr {σ : Type u} (f g : σ → Prop) : σ → Prop := fun s => f s ∨ g s
abbrev stNot {σ : Type u} (f : σ → Prop) : σ → Prop := fun s => ¬ f s
abbrev stImp {σ : Type u} (f g : σ → Prop) : σ → Prop := fun s => f s → g s
abbrev stAdd {σ : Type u} {α : Type v} [Add α] (f g : σ → α) : σ → α := fun s => f s + g s
abbrev stSub {σ : Type u} {α : Type v} [Sub α] (f g : σ → α) : σ → α := fun s => f s - g s
abbrev stMul {σ : Type u} {α : Type v} [Mul α] (f g : σ → α) : σ → α := fun s => f s * g s
abbrev stLt {σ : Type u} {α : Type v} [LT α] (f g : σ → α) : σ → Prop := fun s => f s < g s
abbrev stLe {σ : Type u} {α : Type v} [LE α] (f g : σ → α) : σ → Prop := fun s => f s ≤ g s
abbrev stGt {σ : Type u} {α : Type v} [LT α] (f g : σ → α) : σ → Prop := fun s => f s > g s
abbrev stGe {σ : Type u} {α : Type v} [LE α] (f g : σ → α) : σ → Prop := fun s => f s ≥ g s
abbrev stMod {σ : Type u} {α : Type v} [Mod α] (f g : σ → α) : σ → α := fun s => f s % g s

/-! ## Pointwise operators at the action level -/

abbrev actEq {σ : Type u} {α : Type v} (f g : σ → σ → α) : σ → σ → Prop := fun s t => f s t = g s t
abbrev actNe {σ : Type u} {α : Type v} (f g : σ → σ → α) : σ → σ → Prop := fun s t => f s t ≠ g s t
abbrev actAnd {σ : Type u} (f g : σ → σ → Prop) : σ → σ → Prop := fun s t => f s t ∧ g s t
abbrev actOr {σ : Type u} (f g : σ → σ → Prop) : σ → σ → Prop := fun s t => f s t ∨ g s t
abbrev actNot {σ : Type u} (f : σ → σ → Prop) : σ → σ → Prop := fun s t => ¬ f s t
abbrev actAdd {σ : Type u} {α : Type v} [Add α] (f g : σ → σ → α) : σ → σ → α := fun s t => f s t + g s t
abbrev actSub {σ : Type u} {α : Type v} [Sub α] (f g : σ → σ → α) : σ → σ → α := fun s t => f s t - g s t
abbrev actMul {σ : Type u} {α : Type v} [Mul α] (f g : σ → σ → α) : σ → σ → α := fun s t => f s t * g s t
abbrev actLt {σ : Type u} {α : Type v} [LT α] (f g : σ → σ → α) : σ → σ → Prop := fun s t => f s t < g s t
abbrev actLe {σ : Type u} {α : Type v} [LE α] (f g : σ → σ → α) : σ → σ → Prop := fun s t => f s t ≤ g s t
abbrev actGt {σ : Type u} {α : Type v} [LT α] (f g : σ → σ → α) : σ → σ → Prop := fun s t => f s t > g s t
abbrev actGe {σ : Type u} {α : Type v} [LE α] (f g : σ → σ → α) : σ → σ → Prop := fun s t => f s t ≥ g s t
abbrev actMod {σ : Type u} {α : Type v} [Mod α] (f g : σ → σ → α) : σ → σ → α := fun s t => f s t % g s t

/-! ## The lifting macros -/

/-- Lift a `[p| ...]` body to a state predicate. -/
partial def liftState (stx : TSyntax `term) : MacroM (TSyntax `term) :=
  match stx with
  | `(($e)) => liftState e
  | `(($e : $_)) => liftState e
  | `($a % $b) => do
      let la ← liftState a
      let lb ← liftState b
      `(stMod $la $lb)
  | `($a + $b) => do
      let la ← liftState a
      let lb ← liftState b
      `(stAdd $la $lb)
  | `($a - $b) => do
      let la ← liftState a
      let lb ← liftState b
      `(stSub $la $lb)
  | `($a * $b) => do
      let la ← liftState a
      let lb ← liftState b
      `(stMul $la $lb)
  | `($a = $b) => do
      let la ← liftState a
      let lb ← liftState b
      `(stEq $la $lb)
  | `($a < $b) => do
      let la ← liftState a
      let lb ← liftState b
      `(stLt $la $lb)
  | `($a ≤ $b) => do
      let la ← liftState a
      let lb ← liftState b
      `(stLe $la $lb)
  | `($a > $b) => do
      let la ← liftState a
      let lb ← liftState b
      `(stGt $la $lb)
  | `($a ≥ $b) => do
      let la ← liftState a
      let lb ← liftState b
      `(stGe $la $lb)
  | `($a ≠ $b) => do
      let la ← liftState a
      let lb ← liftState b
      `(stNe $la $lb)
  | `($a ∧ $b) => do
      let la ← liftState a
      let lb ← liftState b
      `(stAnd $la $lb)
  | `($a ∨ $b) => do
      let la ← liftState a
      let lb ← liftState b
      `(stOr $la $lb)
  | `(¬ $a) => do
      let la ← liftState a
      `(stNot $la)
  | `($x:ident) => `(fun s => $x s)
  | `($n:num) => `(fun s => $n)
  | `($f $a) => do
      let la ← liftState a
      `(fun s => $f ($la s))
  | _ => Macro.throwError s!"[p| ...]: unsupported syntax in state predicate: {stx}"

/-- Lift an `[a| ...]` body to an action. `x'` is the post value of `x`. -/
partial def liftAction (stx : TSyntax `term) : MacroM (TSyntax `term) :=
  match stx with
  | `(($e)) => liftAction e
  | `(($e : $_)) => liftAction e
  | `($a % $b) => do
      let la ← liftAction a
      let lb ← liftAction b
      `(actMod $la $lb)
  | `($a + $b) => do
      let la ← liftAction a
      let lb ← liftAction b
      `(actAdd $la $lb)
  | `($a - $b) => do
      let la ← liftAction a
      let lb ← liftAction b
      `(actSub $la $lb)
  | `($a * $b) => do
      let la ← liftAction a
      let lb ← liftAction b
      `(actMul $la $lb)
  | `($a = $b) => do
      let la ← liftAction a
      let lb ← liftAction b
      `(actEq $la $lb)
  | `($a < $b) => do
      let la ← liftAction a
      let lb ← liftAction b
      `(actLt $la $lb)
  | `($a ≤ $b) => do
      let la ← liftAction a
      let lb ← liftAction b
      `(actLe $la $lb)
  | `($a > $b) => do
      let la ← liftAction a
      let lb ← liftAction b
      `(actGt $la $lb)
  | `($a ≥ $b) => do
      let la ← liftAction a
      let lb ← liftAction b
      `(actGe $la $lb)
  | `($a ≠ $b) => do
      let la ← liftAction a
      let lb ← liftAction b
      `(actNe $la $lb)
  | `($a ∧ $b) => do
      let la ← liftAction a
      let lb ← liftAction b
      `(actAnd $la $lb)
  | `($a ∨ $b) => do
      let la ← liftAction a
      let lb ← liftAction b
      `(actOr $la $lb)
  | `(¬ $a) => do
      let la ← liftAction a
      `(actNot $la)
  | `($x:ident) =>
      let n := x.getId.toString
      if n.endsWith "'" then
        let base : TSyntax `ident := ⟨mkIdent (n.dropEnd 1).toName⟩
        `(fun st0 st1 => $base st1)
      else
        `(fun st0 st1 => $x st0)
  | `($n:num) => `(fun st0 st1 => $n)
  | `($f $a) => do
      let la ← liftAction a
      `(fun st0 st1 => $f ($la st0 st1))
  | _ => Macro.throwError s!"[a| ...]: unsupported syntax in action: {stx}"

/-- Rewrite propositional connectives in `[t| ...]` bodies to the lifted ones,
leaving everything else (lifts, temporal notations, named formulas) alone. -/
partial def liftFormula (stx : TSyntax `term) : MacroM (TSyntax `term) :=
  match stx with
  | `(($e)) => liftFormula e
  | `($a ∧ $b) => do
      let la ← liftFormula a
      let lb ← liftFormula b
      `(tlaAnd $la $lb)
  | `($a ∨ $b) => do
      let la ← liftFormula a
      let lb ← liftFormula b
      `(tlaOr $la $lb)
  | `($a → $b) => do
      let la ← liftFormula a
      let lb ← liftFormula b
      `(tlaImp $la $lb)
  | `($a ⇒ $b) => do
      let la ← liftFormula a
      let lb ← liftFormula b
      `(tlaImp $la $lb)
  | `(¬ $a) => do
      let la ← liftFormula a
      `(tlaNot $la)
  | `($a ↔ $b) => do
      let la ← liftFormula a
      let lb ← liftFormula b
      `(tlaIff $la $lb)
  | `(⌜$p⌝) => `(statePred $p)
  | `(⌞$p⌟) => `(purePred $p)
  | `(□[$a]_$v) => `(stutAlways $a $v)
  | _ => pure stx

syntax "[p| " term "]" : term
macro_rules
  | `([p| $body]) => do
      let t ← liftState body
      pure t.raw

syntax "[a| " term "]" : term
macro_rules
  | `([a| $body]) => do
      let t ← liftAction body
      pure t.raw

syntax "[t| " term "]" : term
macro_rules
  | `([t| $body]) => do
      let t ← liftFormula body
      pure t.raw

end Tla
