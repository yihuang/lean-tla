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

/-- `⟨A⟩_v`: the angle action — `A` fires and `v` changes (the action half
of TLA's `[A]_v`/`⟨A⟩_v` pair, used in fairness: `□◇⟨A⟩_v`). -/
scoped syntax:max "⟨" term:60 "⟩_" term:max : term
macro_rules
  | `(⟨$a⟩_$v) => `(AngleAction $a $v)

/-- `WF_(v)(A)`: weak fairness of `A` with respect to the frame `v`
(TLA's `WF_v(A)`; Lean's lexer joins `WF_vars` into one identifier, so the
frame is parenthesized). -/
scoped syntax "WF_" term:max "(" term ")" : term
macro_rules
  | `(WF_$v($A)) => `(WF_v $A $v)

/-- `SF_(v)(A)`: strong fairness of `A` with respect to the frame `v`. -/
scoped syntax "SF_" term:max "(" term ")" : term
macro_rules
  | `(SF_$v($A)) => `(SF_v $A $v)

/-- Lift a state predicate to a temporal formula. -/
scoped syntax:max "⌜" term:80 "⌝" : term
macro_rules
  | `(⌜$p⌝) => `(statePred $p)

/-- Lift a pure proposition to a temporal formula. -/
scoped syntax:max "⌞" term:80 "⌟" : term
macro_rules
  | `(⌞$p⌟) => `(purePred $p)

end Tla
