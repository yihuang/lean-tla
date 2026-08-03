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

/-- Lift a `[p| ...]` body to a state predicate. `bound` tracks the
identifiers bound by `∀`/`∃` inside the body (they are plain values, not
state functions). -/
partial def liftState (bound : Array Name) (stx : TSyntax `term) : MacroM (TSyntax `term) :=
  match stx with
  | `(($e)) => liftState bound e
  | `(($e : $_)) => liftState bound e
  | `(∃ $x:ident ∈ $S, $b) => do
      let lS ← liftState bound S
      let lb ← liftState (bound.push x.getId) b
      `(fun s => ∃ $x:ident ∈ $lS s, $lb s)
  | `(∃ $x:ident, $b) => do
      let lb ← liftState (bound.push x.getId) b
      `(fun s => ∃ $x:ident, $lb s)
  | `(∀ $x:ident ∈ $S, $b) => do
      let lS ← liftState bound S
      let lb ← liftState (bound.push x.getId) b
      `(fun s => ∀ $x:ident ∈ $lS s, $lb s)
  | `(∀ $x:ident, $b) => do
      let lb ← liftState (bound.push x.getId) b
      `(fun s => ∀ $x:ident, $lb s)
  | `(if $c then $a else $b) => do
      let lc ← liftState bound c
      let la ← liftState bound a
      let lb ← liftState bound b
      `(fun s => if $lc s then $la s else $lb s)
  | `($a % $b) => do
      let la ← liftState bound a
      let lb ← liftState bound b
      `(stMod $la $lb)
  | `($a + $b) => do
      let la ← liftState bound a
      let lb ← liftState bound b
      `(stAdd $la $lb)
  | `($a - $b) => do
      let la ← liftState bound a
      let lb ← liftState bound b
      `(stSub $la $lb)
  | `($a * $b) => do
      let la ← liftState bound a
      let lb ← liftState bound b
      `(stMul $la $lb)
  | `($a = $b) => do
      let la ← liftState bound a
      let lb ← liftState bound b
      `(stEq $la $lb)
  | `($a < $b) => do
      let la ← liftState bound a
      let lb ← liftState bound b
      `(stLt $la $lb)
  | `($a ≤ $b) => do
      let la ← liftState bound a
      let lb ← liftState bound b
      `(stLe $la $lb)
  | `($a > $b) => do
      let la ← liftState bound a
      let lb ← liftState bound b
      `(stGt $la $lb)
  | `($a ≥ $b) => do
      let la ← liftState bound a
      let lb ← liftState bound b
      `(stGe $la $lb)
  | `($a ≠ $b) => do
      let la ← liftState bound a
      let lb ← liftState bound b
      `(stNe $la $lb)
  | `($a ∧ $b) => do
      let la ← liftState bound a
      let lb ← liftState bound b
      `(stAnd $la $lb)
  | `($a ∨ $b) => do
      let la ← liftState bound a
      let lb ← liftState bound b
      `(stOr $la $lb)
  | `($a → $b) => do
      let la ← liftState bound a
      let lb ← liftState bound b
      `(stImp $la $lb)
  | `($a ⇒ $b) => do
      let la ← liftState bound a
      let lb ← liftState bound b
      `(stImp $la $lb)
  | `(¬ $a) => do
      let la ← liftState bound a
      `(stNot $la)
  | `($x:ident) =>
      if bound.contains x.getId then
        `(fun s => $x)
      else
        `(fun s => $x s)
  | `($n:num) => `(fun s => $n)
  | `(∅) => `(fun s => ∅)
  | `(true) => `(fun s => true)
  | `(false) => `(fun s => false)
  | `($f $a) => do
      let la ← liftState bound a
      `(fun s => $f ($la s))
  | _ => Macro.throwError s!"[p| ...]: unsupported syntax in state predicate: {stx}"

/-- Lift an `[a| ...]` body to an action. `x'` is the post value of `x`. -/
partial def liftAction (bound : Array Name) (stx : TSyntax `term) : MacroM (TSyntax `term) :=
  match stx with
  | `(($e)) => liftAction bound e
  | `(($e : $_)) => liftAction bound e
  | `(∃ $x:ident ∈ $S, $b) => do
      let lS ← liftState bound S
      let lb ← liftAction (bound.push x.getId) b
      `(fun st0 st1 => ∃ $x:ident ∈ $lS st0, $lb st0 st1)
  | `(∀ $x:ident ∈ $S, $b) => do
      let lS ← liftState bound S
      let lb ← liftAction (bound.push x.getId) b
      `(fun st0 st1 => ∀ $x:ident ∈ $lS st0, $lb st0 st1)
  | `(∃ $x:ident, $b) => do
      let lb ← liftAction (bound.push x.getId) b
      `(fun st0 st1 => ∃ $x:ident, $lb st0 st1)
  | `(∀ $x:ident, $b) => do
      let lb ← liftAction (bound.push x.getId) b
      `(fun st0 st1 => ∀ $x:ident, $lb st0 st1)
  | `(if $c then $a else $b) => do
      let lc ← liftState bound c
      let la ← liftAction bound a
      let lb ← liftAction bound b
      `(fun st0 st1 => if $lc st0 then $la st0 st1 else $lb st0 st1)
  | `($a % $b) => do
      let la ← liftAction bound a
      let lb ← liftAction bound b
      `(actMod $la $lb)
  | `($a + $b) => do
      let la ← liftAction bound a
      let lb ← liftAction bound b
      `(actAdd $la $lb)
  | `($a - $b) => do
      let la ← liftAction bound a
      let lb ← liftAction bound b
      `(actSub $la $lb)
  | `($a * $b) => do
      let la ← liftAction bound a
      let lb ← liftAction bound b
      `(actMul $la $lb)
  | `($a = $b) => do
      let la ← liftAction bound a
      let lb ← liftAction bound b
      `(actEq $la $lb)
  | `($a < $b) => do
      let la ← liftAction bound a
      let lb ← liftAction bound b
      `(actLt $la $lb)
  | `($a ≤ $b) => do
      let la ← liftAction bound a
      let lb ← liftAction bound b
      `(actLe $la $lb)
  | `($a > $b) => do
      let la ← liftAction bound a
      let lb ← liftAction bound b
      `(actGt $la $lb)
  | `($a ≥ $b) => do
      let la ← liftAction bound a
      let lb ← liftAction bound b
      `(actGe $la $lb)
  | `($a ≠ $b) => do
      let la ← liftAction bound a
      let lb ← liftAction bound b
      `(actNe $la $lb)
  | `($a ∧ $b) => do
      let la ← liftAction bound a
      let lb ← liftAction bound b
      `(actAnd $la $lb)
  | `($a ∨ $b) => do
      let la ← liftAction bound a
      let lb ← liftAction bound b
      `(actOr $la $lb)
  | `($a → $b) => do
      let la ← liftAction bound a
      let lb ← liftAction bound b
      `(actImp $la $lb)
  | `($a ⇒ $b) => do
      let la ← liftAction bound a
      let lb ← liftAction bound b
      `(actImp $la $lb)
  | `(¬ $a) => do
      let la ← liftAction bound a
      `(actNot $la)
  | `($x:ident) =>
      let n := x.getId.toString
      if n.endsWith "'" then
        let base : TSyntax `ident := ⟨mkIdent (n.dropEnd 1).toName⟩
        `(fun st0 st1 => $base st1)
      else if bound.contains x.getId then
        `(fun st0 st1 => $x)
      else
        `(fun st0 st1 => $x st0)
  | `($n:num) => `(fun st0 st1 => $n)
  | `(∅) => `(fun st0 st1 => ∅)
  | `(true) => `(fun st0 st1 => true)
  | `(false) => `(fun st0 st1 => false)
  | `($f $a) => do
      let la ← liftAction bound a
      `(fun st0 st1 => $f ($la st0 st1))
  | _ => Macro.throwError s!"[a| ...]: unsupported syntax in action: {stx}"

/-- Rewrite propositional connectives in `[t| ...]` bodies to the lifted ones,
leaving everything else (lifts, temporal notations, named formulas) alone. -/
partial def liftFormula (stx : TSyntax `term) : MacroM (TSyntax `term) :=
  match stx with
  | `(($e)) => liftFormula e
  | `(∃ $x:ident, $b) => do
      let lb ← liftFormula b
      `(tlaExists (fun $x:ident => $lb))
  | `(∀ $x:ident, $b) => do
      let lb ← liftFormula b
      `(tlaForall (fun $x:ident => $lb))
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
      let t ← liftState #[] body
      pure t.raw

syntax "[a| " term "]" : term
macro_rules
  | `([a| $body]) => do
      let t ← liftAction #[] body
      pure t.raw

syntax "[t| " term "]" : term
macro_rules
  | `([t| $body]) => do
      let t ← liftFormula body
      pure t.raw

end Tla
