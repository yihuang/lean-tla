import TlaDsl.Basic
import TlaDsl.Notation

open Lean PrettyPrinter

namespace Tla

/-! # Pretty printing: goals read like TLA

`app_unexpander`s invert the `[t| ...]` macro: temporal formulas built from
`tlaAnd`/`always`/`stutAlways`/... are displayed with the TLA notation
(`∧`, `□`, `□[A]_v`, `⌜ p ⌝`, ...) instead of raw lifted lambdas, so goals
and hypotheses are readable without `set_option pp.all`.

The state/action brackets (`[p| ...]`, `[a| ...]`) elaborate to plain
lambdas, which are printed back as lambdas; the temporal layer is where the
notation pays off (e.g. `Spec ⊢ □Inv` goals).
-/

@[app_unexpander Tla.tlaAnd]
def unexpTlaAnd : Unexpander := fun stx => do
  match stx with
  | `($_ $F $G) => `($F ∧ $G)
  | _ => pure stx

@[app_unexpander Tla.tlaOr]
def unexpTlaOr : Unexpander := fun stx => do
  match stx with
  | `($_ $F $G) => `($F ∨ $G)
  | _ => pure stx

@[app_unexpander Tla.tlaImp]
def unexpTlaImp : Unexpander := fun stx => do
  match stx with
  | `($_ $F $G) => `($F ⇒ $G)
  | _ => pure stx

@[app_unexpander Tla.tlaIff]
def unexpTlaIff : Unexpander := fun stx => do
  match stx with
  | `($_ $F $G) => `($F ↔ $G)
  | _ => pure stx

@[app_unexpander Tla.tlaNot]
def unexpTlaNot : Unexpander := fun stx => do
  match stx with
  | `($_ $F) => `(¬ $F)
  | _ => pure stx

@[app_unexpander Tla.tlaForall]
def unexpTlaForall : Unexpander := fun stx => do
  match stx with
  | `($_ fun $x:ident => $F) => `(∀ $x:ident, $F)
  | _ => pure stx

@[app_unexpander Tla.tlaExists]
def unexpTlaExists : Unexpander := fun stx => do
  match stx with
  | `($_ fun $x:ident => $F) => `(∃ $x:ident, $F)
  | _ => pure stx

@[app_unexpander Tla.always]
def unexpAlways : Unexpander := fun stx => do
  match stx with
  | `($_ $F) => `(□ $F)
  | _ => pure stx

@[app_unexpander Tla.eventually]
def unexpEventually : Unexpander := fun stx => do
  match stx with
  | `($_ $F) => `(◇ $F)
  | _ => pure stx

@[app_unexpander Tla.later]
def unexpLater : Unexpander := fun stx => do
  match stx with
  | `($_ $F) => `(◯ $F)
  | _ => pure stx

@[app_unexpander Tla.stutAlways]
def unexpStutAlways : Unexpander := fun stx => do
  match stx with
  | `($_ $next $v) => `(□[$next]_$v)
  | _ => pure stx

@[app_unexpander Tla.leadsTo]
def unexpLeadsTo : Unexpander := fun stx => do
  match stx with
  | `($_ $P $Q) => `($P ↝ $Q)
  | _ => pure stx

@[app_unexpander Tla.strongUntil]
def unexpStrongUntil : Unexpander := fun stx => do
  match stx with
  | `($_ $P $Q) => `($P 𝑈 $Q)
  | _ => pure stx

@[app_unexpander Tla.statePred]
def unexpStatePred : Unexpander := fun stx => do
  match stx with
  | `($_ $p) => `(⌜$p⌝)
  | _ => pure stx

@[app_unexpander Tla.purePred]
def unexpPurePred : Unexpander := fun stx => do
  match stx with
  | `($_ $p) => `(⌞$p⌟)
  | _ => pure stx

end Tla
