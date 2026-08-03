import TlaDsl.Basic
import TlaDsl.Notation
import TlaDsl.Coercion
import TlaDsl.Prime
import TlaDsl.Rules
import TlaDsl.Tactic
import TlaDsl.TlaVar

open scoped Tla

/-! # Bracket-notation regression tests

`[p| ...]` and `[a| ...]` are a dedicated elaborator: it introduces fresh
pre/post state variables and lifts every identifier of state-function type
(`σ → α`) to an application of the state variable. These `example`s pin the
elaborated terms against the plain lambdas they should reduce to (`by rfl`),
so regressions in the elaborator are caught at build time.

The interesting regression cases are collected here deliberately:

- literals on either side of an operator (`x + 1`, `1 + x`), which must be
  pinned by their context;
- applications of plain functions (`EvenN x`), which must *not* be mistaken
  for state functions;
- untyped/typed/bounded binders, whose domain metavariables must be
  assignable from inside the operator builders;
- `true`/`false`, which elaborate to the propositions `True`/`False`;
- `if-then-else` and implication at the state and action level.
-/

namespace TlaDsl.Examples.Brackets

structure St where
  x : Nat
  y : Nat
  done : Finset Nat

tla_var St x y done

/-- A plain (non-state) function; must be applied, not lifted. -/
def EvenN (n : Nat) : Prop := n % 2 = 0

/-! ## State predicates: type-directed lifting -/

example : [p| x] = fun s : St => x s := by
  rfl

example : [p| x = 0] = fun s : St => x s = 0 := by
  rfl

example : [p| x = 0 ∧ y = 0] = fun s : St => x s = 0 ∧ y s = 0 := by
  rfl

example : [p| x ≠ 0 ∧ x > 1 ∧ x ≥ 2] = fun s : St => x s ≠ 0 ∧ x s > 1 ∧ x s ≥ 2 := by
  rfl

example : [p| x % 2 = 0] = fun s : St => x s % 2 = 0 := by
  rfl

/-! ## Literals are pinned by their context -/

example : [p| x + 1 = 1 + x] = fun s : St => x s + 1 = 1 + x s := by
  rfl

example : [p| 1 + x = x] = fun s : St => 1 + x s = x s := by
  rfl

example : [p| done = ∅] = fun s : St => done s = ∅ := by
  rfl

example : [p| x = 0 ∧ true] = fun s : St => x s = 0 ∧ True := by
  rfl

example : [p| x = 0 ∧ false] = fun s : St => x s = 0 ∧ False := by
  rfl

/-! ## Plain function application -/

example : [p| EvenN x] = fun s : St => EvenN (x s) := by
  rfl

example : [p| EvenN x ∧ x = 0] = fun s : St => EvenN (x s) ∧ x s = 0 := by
  rfl

/-! ## Binders -/

example : [p| ∃ p ∈ done, p < x] = fun s : St => ∃ p ∈ done s, p < x s := by
  rfl

example : [p| ∀ p ∈ done, p < x] = fun s : St => ∀ p ∈ done s, p < x s := by
  rfl

example : [p| ∃ z, z = x] = fun s : St => ∃ z, z = x s := by
  rfl

example : [p| ∃ z : Nat, z = x] = fun s : St => ∃ z : Nat, z = x s := by
  rfl

example : [p| ∀ z, z < x] = fun s : St => ∀ z, z < x s := by
  rfl

example : [p| ∀ z : Nat, z < x] = fun s : St => ∀ z : Nat, z < x s := by
  rfl

/-! ## Conditionals, implication, ascription -/

example : [p| if x = 0 then x < 2 else x > 1] =
    fun s : St => if x s = 0 then x s < 2 else x s > 1 := by
  rfl

example : [p| x = 0 → done = ∅] = fun s : St => x s = 0 → done s = ∅ := by
  rfl

example : [p| x = 0 ⇒ done = ∅] = fun s : St => x s = 0 → done s = ∅ := by
  rfl

example : [p| (x : Nat) = 0] = fun s : St => x s = 0 := by
  rfl

/-! ## Actions: primes resolve to the post state -/

example : [a| x' = x + 1] = fun s s' : St => x s' = x s + 1 := by
  rfl

example : [a| x' = x + 1 ∧ y' = y + 1] =
    fun s s' : St => x s' = x s + 1 ∧ y s' = y s + 1 := by
  rfl

example : [a| x % 2 = 0 ∧ y' = y + 1] =
    fun s s' : St => x s % 2 = 0 ∧ y s' = y s + 1 := by
  rfl

example : [a| ∃ p ∈ done, x' = p + 1] =
    fun s s' : St => ∃ p ∈ done s, x s' = p + 1 := by
  rfl

example : [a| if x = 0 then x' = 1 else x' = x + 1] =
    fun s s' : St => if x s = 0 then x s' = 1 else x s' = x s + 1 := by
  rfl

example : [a| x = 0 → x' = x + 1] =
    fun s s' : St => x s = 0 → x s' = x s + 1 := by
  rfl

/-! ## Temporal formulas -/

example (F G : Tla.Pred St) : [t| F → G] = Tla.tlaImp F G := by
  rfl

example (F G : Tla.Pred St) : [t| F ∧ G] = Tla.tlaAnd F G := by
  rfl

example (F : Nat → Tla.Pred St) : [t| ∃ n, F n] = Tla.tlaExists F := by
  rfl

example (F : Nat → Tla.Pred St) : [t| ∀ n, F n] = Tla.tlaForall F := by
  rfl

end TlaDsl.Examples.Brackets
