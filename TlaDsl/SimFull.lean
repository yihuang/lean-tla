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

This module proves the equivalence structure (refl/symm/trans/first-state/
quotient) and the block/drop machinery over `Nat.find` that the remaining
integration work needs: `nextBlock` and `BlockStart` commute with
`ωSequence.drop` at block boundaries, so compression commutes with such drops
(`Compress_drop_blockStart`), and `SimFull` is preserved when both behaviors
are dropped at corresponding block starts. The suffix-matching lemma
(`SimFull e f → ∀ n, ∃ m, SimFull (e.drop n) (f.drop m)`), the step matching
lemma, and `Sim.map` are the remaining pieces before the preservation
theorems in `Meta.lean` can migrate to `SimFull`.
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

/-! ## Block/drop interaction

These lemmas pair the `Nat.find`-based block machinery with CSLib's
`ωSequence.drop`: a drop at a block boundary shifts the block indexing by the
dropped prefix, and compression commutes with such drops. This is the core
mechanism behind the missing suffix-matching lemma.
-/

/-- `nextBlock` commutes with `drop`: a change in `e.drop m` at position `j`
is a change in `e` at position `m + j`, so the next block shifts by `m`. -/
theorem nextBlock_drop_add {σ : Type u} (e : Behavior σ) (m n : Nat) :
    nextBlock (e.drop m) n + m = nextBlock e (m + n) := by
  have hdrop_witness (j : Nat) (hj : m + n ≤ j ∧ e (j + 1) ≠ e j) :
      n ≤ j - m ∧ (e.drop m) (j - m + 1) ≠ (e.drop m) (j - m) := by
    have harith1 : (j - m + 1) + m = j + 1 := by omega
    have harith2 : (j - m) + m = j := by omega
    constructor
    · omega
    · simpa [Cslib.ωSequence.drop, harith1, harith2] using hj.2
  have hshift_witness (j : Nat) (hj : n ≤ j ∧ (e.drop m) (j + 1) ≠ (e.drop m) j) :
      m + n ≤ m + j ∧ e (m + j + 1) ≠ e (m + j) := by
    have harith1 : (j + 1) + m = (m + j) + 1 := by omega
    have harith2 : j + m = m + j := by omega
    constructor
    · omega
    · simpa [Cslib.ωSequence.drop, harith1, harith2] using hj.2
  by_cases h1 : ∃ j, n ≤ j ∧ (e.drop m) (j + 1) ≠ (e.drop m) j
  · have h2 : ∃ j, m + n ≤ j ∧ e (j + 1) ≠ e j := by
      rcases h1 with ⟨j, hj⟩
      exact ⟨m + j, hshift_witness j hj⟩
    have hle1 : m + Nat.find (p := fun j => n ≤ j ∧ (e.drop m) (j + 1) ≠ (e.drop m) j) h1
        ≤ Nat.find (p := fun j => m + n ≤ j ∧ e (j + 1) ≠ e j) h2 := by
      let j2 := Nat.find (p := fun j => m + n ≤ j ∧ e (j + 1) ≠ e j) h2
      have hspec2 : m + n ≤ j2 ∧ e (j2 + 1) ≠ e j2 :=
        Nat.find_spec (p := fun j => m + n ≤ j ∧ e (j + 1) ≠ e j) h2
      have hw : n ≤ j2 - m ∧ (e.drop m) (j2 - m + 1) ≠ (e.drop m) (j2 - m) :=
        hdrop_witness j2 hspec2
      have hmin : Nat.find (p := fun j => n ≤ j ∧ (e.drop m) (j + 1) ≠ (e.drop m) j) h1 ≤ j2 - m :=
        Nat.find_min' h1 hw
      dsimp [j2] at hmin
      omega
    have hle2 : Nat.find (p := fun j => m + n ≤ j ∧ e (j + 1) ≠ e j) h2
        ≤ m + Nat.find (p := fun j => n ≤ j ∧ (e.drop m) (j + 1) ≠ (e.drop m) j) h1 := by
      have hspec1 : n ≤ Nat.find (p := fun j => n ≤ j ∧ (e.drop m) (j + 1) ≠ (e.drop m) j) h1 ∧
          (e.drop m) (Nat.find (p := fun j => n ≤ j ∧ (e.drop m) (j + 1) ≠ (e.drop m) j) h1 + 1) ≠
            (e.drop m) (Nat.find (p := fun j => n ≤ j ∧ (e.drop m) (j + 1) ≠ (e.drop m) j) h1) :=
        Nat.find_spec (p := fun j => n ≤ j ∧ (e.drop m) (j + 1) ≠ (e.drop m) j) h1
      have hw : m + n ≤ m + Nat.find (p := fun j => n ≤ j ∧ (e.drop m) (j + 1) ≠ (e.drop m) j) h1 ∧
          e (m + Nat.find (p := fun j => n ≤ j ∧ (e.drop m) (j + 1) ≠ (e.drop m) j) h1 + 1) ≠
            e (m + Nat.find (p := fun j => n ≤ j ∧ (e.drop m) (j + 1) ≠ (e.drop m) j) h1) :=
        hshift_witness (Nat.find (p := fun j => n ≤ j ∧ (e.drop m) (j + 1) ≠ (e.drop m) j) h1) hspec1
      exact Nat.find_min' h2 hw
    have hEq : Nat.find (p := fun j => n ≤ j ∧ (e.drop m) (j + 1) ≠ (e.drop m) j) h1 + m =
        Nat.find (p := fun j => m + n ≤ j ∧ e (j + 1) ≠ e j) h2 := by omega
    unfold nextBlock
    rw [dif_pos h1, dif_pos h2]
    omega
  · have hn1 : ¬ ∃ j, m + n ≤ j ∧ e (j + 1) ≠ e j := by
      intro h2
      rcases h2 with ⟨j, hj⟩
      exact h1 ⟨j - m, hdrop_witness j hj⟩
    unfold nextBlock
    rw [dif_neg h1, dif_neg hn1]
    omega

/-- Block starts compose with drops at block boundaries: dropping at the
start of block `i` and then taking block `k` lands at block `i + k`. -/
theorem BlockStart_drop_add {σ : Type u} (e : Behavior σ) (i k : Nat) :
    BlockStart (e.drop (BlockStart e i)) k + BlockStart e i = BlockStart e (i + k) := by
  induction k with
  | zero => simp [BlockStart]
  | succ k ih =>
      simp [BlockStart]
      rw [nextBlock_drop_add, Nat.add_comm, ih]

/-- Compression commutes with dropping at a block boundary: the compression
of `e` from block `i` onwards is the compression of `e.drop (BlockStart e i)`
with its first `i` blocks removed. -/
theorem Compress_drop_blockStart {σ : Type u} (e : Behavior σ) (i : Nat) :
    Compress (e.drop (BlockStart e i)) = Cslib.ωSequence.drop i (Compress e) := by
  funext k
  simp [Compress]
  rw [Nat.add_comm, BlockStart_drop_add]

namespace SimFull

theorem refl (e : Behavior σ) : SimFull e e := rfl

theorem symm {e f : Behavior σ} (h : SimFull e f) : SimFull f e := Eq.symm h

theorem trans {e f g : Behavior σ} (h1 : SimFull e f) (h2 : SimFull f g) : SimFull e g :=
  Eq.trans h1 h2

/-- Stuttering-equivalent behaviors agree on their first state. -/
theorem first {e f : Behavior σ} (h : SimFull e f) : e 0 = f 0 := by
  have hc := congrFun h 0
  simpa [Compress, BlockStart] using hc

/-- `SimFull` is preserved when both behaviors are dropped at corresponding
block starts (block `i` of each). -/
theorem drop_blockStart {e f : Behavior σ} (h : SimFull e f) (i : Nat) :
    SimFull (e.drop (BlockStart e i)) (f.drop (BlockStart f i)) := by
  unfold SimFull
  rw [Compress_drop_blockStart, Compress_drop_blockStart]
  rw [h]

instance setoid (σ : Type u) : Setoid (Behavior σ) where
  r := SimFull
  iseqv := ⟨SimFull.refl, SimFull.symm, SimFull.trans⟩

end SimFull

/-- The stuttering quotient for the full equivalence. -/
abbrev StutQuotFull (σ : Type u) := Quot (SimFull : Behavior σ → Behavior σ → Prop)

end Tla
