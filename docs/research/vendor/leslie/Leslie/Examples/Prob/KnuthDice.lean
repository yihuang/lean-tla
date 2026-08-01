/-
M1 W1 — Knuth-Yao 6-sided die.

Models the rejection-sampling form: flip a fair coin three times to
form a 3-bit value `v ∈ 0..7`; if `v < 6` output `v + 1` (or just `v`
as a `Fin 6`), else restart. Expected number of flips per output is
3 · 8/6 = 4.

This is a non-trivial probabilistic example (state machine + retry
loop) that exercises the full M1 W1 API beyond the trivial coin-flip
smoke test.
-/

import Leslie.Prob.Action
import Leslie.Prob.PMF

namespace Leslie.Examples.Prob.KnuthDice

open Leslie.Prob

/-! ## State

The state tracks bits collected so far (≤ 2 — once we hit 3, we
resolve in one step) and the output once it is determined.
-/

/-- A Knuth-Yao state: `bits` accumulates the most-recent coin flips
since the last resolution; `out` is `none` while still flipping and
`some v` once `v` is decided. -/
structure KState where
  bits : List Bool
  out  : Option (Fin 6)
  deriving DecidableEq, Repr

/-- Initial state: no bits collected, no output yet. -/
def init : KState := ⟨[], none⟩

/-- Interpret a list of bits as a `Nat`, LSB first. -/
def bitsValue : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bitsValue bs

/-- Deterministic post-state after appending coin `b`.

If three bits are now in hand, the value `v ∈ 0..7` is read off:
`v < 6` resolves to `some ⟨v, _⟩`, otherwise we drop the bits and
restart. Otherwise we just append the new bit. -/
def afterFlip (s : KState) (b : Bool) : KState :=
  let bs' := s.bits ++ [b]
  if bs'.length = 3 then
    let v := bitsValue bs'
    if h : v < 6 then ⟨[], some ⟨v, h⟩⟩
    else ⟨[], none⟩  -- v ∈ {6, 7}: rejection
  else
    ⟨bs', none⟩

/-! ## Spec

A single action `()` ("flip") is enabled while the output is unset.
Its effect is sampling a fair coin and advancing the state via
`afterFlip`. -/

/-- The flip action's effect: sample a uniform coin, advance. -/
noncomputable def flipEffect (s : KState) : PMF KState :=
  (PMF.uniform Bool).map (afterFlip s)

/-- The Knuth-Yao 6-sided die spec. -/
noncomputable def knuthDice : ProbActionSpec KState Unit where
  init    := fun s => s = init
  actions := fun () =>
    { gate   := fun s => s.out = none
      effect := fun s _ => flipEffect s }

/-! ## Sanity examples -/

/-- The initial-state predicate selects exactly `init`. -/
example : knuthDice.init init := rfl

/-- The flip action is enabled at the initial state. -/
example : knuthDice.is_enabled () init := rfl

/-- Once the output is set, the action is disabled. -/
example (v : Fin 6) : ¬ knuthDice.is_enabled () ⟨[], some v⟩ := by
  -- is_enabled unfolds to `(some v : Option _) = none`; not equal.
  simp [ProbActionSpec.is_enabled, knuthDice]

/-- After three flips with bits `[b₀, b₁, b₂]` whose value is `< 6`,
`afterFlip` resolves to a leaf with that value. -/
example :
    afterFlip ⟨[false, true], none⟩ false
      = ⟨[], some ⟨2, by decide⟩⟩ := by
  decide

/-- After three flips with value `7` (`[true, true, true]`), the
algorithm restarts: bits cleared, output still unset. -/
example :
    afterFlip ⟨[true, true], none⟩ true
      = ⟨[], none⟩ := by
  decide

/-- One flip from `init` lands in either `⟨[false], none⟩` or
`⟨[true], none⟩` and never resolves (length 1 < 3). -/
example (b : Bool) : afterFlip init b = ⟨[b], none⟩ := by
  cases b <;> rfl

/-- The single-step transition from `init` is the PMF
`(uniform Bool).map (afterFlip init)`. -/
example : knuthDice.step () init = some (flipEffect init) :=
  ProbActionSpec.step_eq_some rfl

end Leslie.Examples.Prob.KnuthDice
