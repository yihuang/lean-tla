import Mathlib.Data.Stream.Defs
import Mathlib.Data.Nat.Find
import TlaDsl.Basic

open Classical

namespace Tla

/-! # Full stuttering equivalence (run-compression)

The finite `Sim` in `TlaDsl/Meta.lean` identifies behaviors differing by
finitely many stuttering steps. Full TLA stuttering equivalence must also
identify behaviors differing in *infinitely many* stuttering steps (e.g. an
eventually-constant behavior and its stutter-free core).

The standard characterization used here: two behaviors are
stuttering-equivalent iff their *compressions* are equal — the sequences of
maximal-run values coincide, where an eventually-constant behavior
compresses to its final value repeated forever. Compression is computed with
`Nat.find` (the next index where the value changes), so the definition is
classical but total.

This module currently proves the equivalence structure (refl/symm/trans/
first-state/quotient). The remaining integration work — the suffix-matching
lemmas (`SimFull e f → ∀ n, ∃ m, SimFull (e.drop n) (f.drop m)`), the step
matching lemma, and `Sim.map` — requires block/drop machinery over
`Nat.find` and is tracked as the follow-up before the preservation theorems
in `Meta.lean` can migrate to `SimFull`.
-/

/-- The start of the next maximal run: the first index `≥ n` where the value
changes, plus one; if the tail is eventually constant, `n` itself (the run
continues forever). -/
noncomputable def nextBlock {σ : Type u} (e : Behavior σ) (n : Nat) : Nat :=
  if h : ∃ m : Nat, n ≤ m ∧ e (m + 1) ≠ e m then
    Nat.find (p := fun m => n ≤ m ∧ e (m + 1) ≠ e m) h + 1
  else n

/-- The start of the `n`-th maximal run (0-indexed). -/
noncomputable def BlockStart {σ : Type u} (e : Behavior σ) : Nat → Nat
  | 0 => 0
  | n + 1 => nextBlock e (BlockStart e n)

/-- The compression of a behavior: the values at the starts of its maximal
runs. -/
noncomputable def Compress {σ : Type u} (e : Behavior σ) : Nat → σ :=
  fun n => e (BlockStart e n)

/-- Full stuttering equivalence: equal compressed forms. -/
noncomputable def SimFull {σ : Type u} (e f : Behavior σ) : Prop :=
  Compress e = Compress f

/-- The next block starts at or after the current position. -/
theorem nextBlock_ge {σ : Type u} (e : Behavior σ) (n : Nat) : n ≤ nextBlock e n := by
  unfold nextBlock
  by_cases h : ∃ m : Nat, n ≤ m ∧ e (m + 1) ≠ e m
  · have hle : n ≤ Nat.find (p := fun m => n ≤ m ∧ e (m + 1) ≠ e m) h :=
      (Nat.find_spec h).1
    simp [h]
    exact le_trans hle (Nat.le_succ _)
  · simp [h]

/-- Block starts are monotone and never go backwards. -/
theorem BlockStart_mono {σ : Type u} (e : Behavior σ) (k : Nat) :
    BlockStart e k ≤ BlockStart e (Nat.succ k) := by
  simp [BlockStart]
  exact nextBlock_ge e (BlockStart e k)

namespace SimFull

theorem refl (e : Behavior σ) : SimFull e e := rfl

theorem symm {e f : Behavior σ} (h : SimFull e f) : SimFull f e := Eq.symm h

theorem trans {e f g : Behavior σ} (h1 : SimFull e f) (h2 : SimFull f g) : SimFull e g :=
  Eq.trans h1 h2

/-- Stuttering-equivalent behaviors agree on their first state. -/
theorem first {e f : Behavior σ} (h : SimFull e f) : e 0 = f 0 := by
  have hc := congrFun h 0
  simpa [Compress, BlockStart] using hc

instance setoid (σ : Type u) : Setoid (Behavior σ) where
  r := SimFull
  iseqv := ⟨SimFull.refl, SimFull.symm, SimFull.trans⟩

end SimFull

/-- The stuttering quotient for the full equivalence. -/
abbrev StutQuotFull (σ : Type u) := Quot (SimFull : Behavior σ → Behavior σ → Prop)

end Tla
