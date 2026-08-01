import TlaDsl.Basic

namespace Tla

/-! # Scoped notation

Activate with `open scoped Tla`. Plain TLA-looking symbols for the temporal
layer; explicit lifts for state predicates and actions.
-/

scoped infix:60 " ⊨ " => Satisfies
scoped infix:40 " ⊢ " => Entails

scoped prefix:90 "□" => always
scoped prefix:90 "◇" => eventually
scoped prefix:90 "◯" => later
scoped infix:25 " ↝ " => leadsTo
scoped infix:30 " 𝑈 " => strongUntil
scoped infix:30 " ⇒ " => tlaImp

/-- `□[A]_v`: always, every step is A or leaves v unchanged. -/
scoped syntax:max "□[" term:60 "]_" term:max : term
macro_rules
  | `(□[$a]_$v) => `(stutAlways $a $v)

/-- Lift a state predicate to a temporal formula. -/
scoped syntax:max "⌜" term:80 "⌝" : term
macro_rules
  | `(⌜$p⌝) => `(statePred $p)

/-- Lift a pure proposition to a temporal formula. -/
scoped syntax:max "⌞" term:80 "⌟" : term
macro_rules
  | `(⌞$p⌟) => `(purePred $p)

end Tla
