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
are dropped at corresponding block starts. The in-block truncation machinery
(`BlockOf`, `Compress_drop_blockOf`) then yields the suffix-matching lemmas
(`SimFull e f → ∀ n, ∃ m, SimFull (e.drop n) (f.drop m)` and the right-handed
version). The step-matching lemma (`SimFull.sim_step`, with the block-final
and block-boundary cases handled via `BlockOf_eq_of_between` and
`SimFull.nonfinal_iff`) completes the machinery the action-level preservation
theorems in `Meta.lean` migrate with.
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

/-! ## In-block truncation and suffix matching -/

/-- `BlockOf`'s search terminates: either block starts outrun `n`, or they
stabilize at the final block. -/
theorem BlockOf_exists {σ : Type u} (e : Behavior σ) (n : Nat) :
    ∃ k, n < BlockStart e (k + 1) ∨ BlockStart e (k + 1) = BlockStart e k := by
  by_cases hdiv : ∀ k, BlockStart e k < BlockStart e (k + 1)
  · refine ⟨n, Or.inl ?_⟩
    have hge : ∀ k, k ≤ BlockStart e k := by
      intro k
      induction k with
      | zero => simp [BlockStart]
      | succ k ih =>
          have hlt : BlockStart e k < BlockStart e (k + 1) := hdiv k
          omega
    have hge' : n + 1 ≤ BlockStart e (n + 1) := hge (n + 1)
    omega
  · rcases not_forall.mp hdiv with ⟨k, hnot⟩
    refine ⟨k, Or.inr ?_⟩
    exact (le_antisymm (BlockStart_mono e k) (le_of_not_gt hnot)).symm

/-- `BlockOf e n`: the index of the maximal run (block) containing position
`n`. If the tail from that block on is constant (the final block), the search
terminates at that block. -/
noncomputable def BlockOf {σ : Type u} (e : Behavior σ) (n : Nat) : Nat :=
  Nat.find (p := fun k => n < BlockStart e (k + 1) ∨ BlockStart e (k + 1) = BlockStart e k)
    (BlockOf_exists e n)

/-- The block containing `n` starts at or before `n`. -/
theorem BlockOf_le {σ : Type u} (e : Behavior σ) (n : Nat) :
    BlockStart e (BlockOf e n) ≤ n := by
  by_cases hz : BlockOf e n = 0
  · simp [hz, BlockStart]
  · have hnot : ¬ (n < BlockStart e (BlockOf e n - 1 + 1) ∨
        BlockStart e (BlockOf e n - 1 + 1) = BlockStart e (BlockOf e n - 1)) := by
      intro hp
      have hmin : BlockOf e n ≤ BlockOf e n - 1 :=
        Nat.find_min' (BlockOf_exists e n) (m := BlockOf e n - 1) hp
      omega
    have hz1 : 1 ≤ BlockOf e n := by omega
    exact (by simpa [Nat.sub_add_cancel hz1] using (le_of_not_gt (not_or.mp hnot).1))

/-- The block containing `n`: either `n` is before the next block start, or
the block is the final (infinite) one. -/
theorem BlockOf_spec {σ : Type u} (e : Behavior σ) (n : Nat) :
    n < BlockStart e (BlockOf e n + 1) ∨ BlockStart e (BlockOf e n + 1) = BlockStart e (BlockOf e n) :=
  Nat.find_spec (p := fun k => n < BlockStart e (k + 1) ∨ BlockStart e (k + 1) = BlockStart e k)
    (BlockOf_exists e n)

/-- No changes inside a block: if `b ≤ n < nextBlock e b`, then `e n = e b`. -/
theorem eq_of_block_between {σ : Type u} (e : Behavior σ) (b n : Nat)
    (hb : b ≤ n) (hn : n < nextBlock e b) : e n = e b := by
  by_cases hch : ∃ m, b ≤ m ∧ e (m + 1) ≠ e m
  · have hstep (j : Nat) (hj : b ≤ j)
        (hjf : j < Nat.find (p := fun m => b ≤ m ∧ e (m + 1) ≠ e m) hch) :
        e (j + 1) = e j := by
      by_contra hne
      have hw : b ≤ j ∧ e (j + 1) ≠ e j := ⟨hj, hne⟩
      have hmin : Nat.find (p := fun m => b ≤ m ∧ e (m + 1) ≠ e m) hch ≤ j :=
        Nat.find_min' hch hw
      omega
    have hchain : ∀ m : Nat, b ≤ m → m < nextBlock e b → e m = e b := by
      intro m
      induction m with
      | zero => intro hb' hm; have hb0 : b = 0 := le_antisymm hb' (Nat.zero_le b); subst hb0; rfl
      | succ m ih =>
          intro hb' hm
          by_cases hbm : b ≤ m
          · have hmf : m < Nat.find (p := fun m => b ≤ m ∧ e (m + 1) ≠ e m) hch := by
              have hm' : m + 1 < Nat.find (p := fun m => b ≤ m ∧ e (m + 1) ≠ e m) hch + 1 := by
                unfold nextBlock at hm
                rw [dif_pos hch] at hm
                exact hm
              omega
            have hstepm : e (m + 1) = e m := hstep m hbm hmf
            rw [hstepm]
            have hm2 : m < nextBlock e b := by
              unfold nextBlock
              have hm' : m + 1 < Nat.find (p := fun m => b ≤ m ∧ e (m + 1) ≠ e m) hch + 1 := by
                unfold nextBlock at hm
                rw [dif_pos hch] at hm
                exact hm
              simp [hch]
              omega
            exact ih hbm hm2
          · have hb' : b = m + 1 := le_antisymm hb' (Nat.succ_le_of_lt (Nat.lt_of_not_ge hbm))
            subst hb'
            rfl
    exact hchain n hb hn
  · have hn' : n < b := by
      unfold nextBlock at hn
      simpa [hch] using hn
    omega

/-- `nextBlock` is constant within a non-final block. -/
theorem nextBlock_eq_of_block_between {σ : Type u} (e : Behavior σ) (b n : Nat)
    (hch : ∃ m, b ≤ m ∧ e (m + 1) ≠ e m)
    (hb : b ≤ n) (hn : n < nextBlock e b) : nextBlock e n = nextBlock e b := by
  unfold nextBlock
  have hfindb : n ≤ Nat.find (p := fun m => b ≤ m ∧ e (m + 1) ≠ e m) hch := by
    unfold nextBlock at hn
    rw [dif_pos hch] at hn
    omega
  have hchn : ∃ m, n ≤ m ∧ e (m + 1) ≠ e m := by
    refine ⟨Nat.find (p := fun m => b ≤ m ∧ e (m + 1) ≠ e m) hch, ?_, ?_⟩
    · exact hfindb
    · exact (Nat.find_spec (p := fun m => b ≤ m ∧ e (m + 1) ≠ e m) hch).2
  have hle1 : Nat.find (p := fun m => n ≤ m ∧ e (m + 1) ≠ e m) hchn ≤
      Nat.find (p := fun m => b ≤ m ∧ e (m + 1) ≠ e m) hch := by
    apply Nat.find_min' hchn
    constructor
    · exact hfindb
    · exact (Nat.find_spec (p := fun m => b ≤ m ∧ e (m + 1) ≠ e m) hch).2
  have hle2 : Nat.find (p := fun m => b ≤ m ∧ e (m + 1) ≠ e m) hch ≤
      Nat.find (p := fun m => n ≤ m ∧ e (m + 1) ≠ e m) hchn := by
    apply Nat.find_min' hch
    constructor
    · have hnle : n ≤ Nat.find (p := fun m => n ≤ m ∧ e (m + 1) ≠ e m) hchn :=
        (Nat.find_spec (p := fun m => n ≤ m ∧ e (m + 1) ≠ e m) hchn).1
      omega
    · exact (Nat.find_spec (p := fun m => n ≤ m ∧ e (m + 1) ≠ e m) hchn).2
  have hEq : Nat.find (p := fun m => n ≤ m ∧ e (m + 1) ≠ e m) hchn =
      Nat.find (p := fun m => b ≤ m ∧ e (m + 1) ≠ e m) hch := le_antisymm hle1 hle2
  rw [dif_pos hchn, dif_pos hch, hEq]

/-- Dropping at a position inside a non-final block shifts the later block
starts by one: block `k + 1` of `e.drop n` starts at block `i + k + 1` of `e`,
where `i` is the block containing `n`. -/
theorem BlockStart_drop_shift {σ : Type u} (e : Behavior σ) (i n : Nat)
    (hb : BlockStart e i ≤ n) (hn : n < nextBlock e (BlockStart e i)) :
    ∀ k : Nat, BlockStart (e.drop n) (Nat.succ k) + n = BlockStart e (i + Nat.succ k) := by
  intro k
  induction k with
  | zero =>
      simp [BlockStart]
      rw [nextBlock_drop_add]
      simp
      have hchb : ∃ m, BlockStart e i ≤ m ∧ e (m + 1) ≠ e m := by
        by_contra hnone
        have hnb : n < BlockStart e i := by
          unfold nextBlock at hn
          rw [dif_neg hnone] at hn
          exact hn
        omega
      rw [nextBlock_eq_of_block_between e (BlockStart e i) n hchb hb hn]
  | succ k ih =>
      simp [BlockStart]
      rw [nextBlock_drop_add]
      rw [Nat.add_comm]
      have ih' : nextBlock (e.drop n) (BlockStart (e.drop n) k) + n =
          BlockStart e (i + Nat.succ k) := by
        simpa [BlockStart] using ih
      rw [ih']
      simp [BlockStart]

/-- Compression commutes with dropping at any position: dropping `n` shifts
the compressed value sequence to the block containing `n`. -/
theorem Compress_drop_blockOf {σ : Type u} (e : Behavior σ) (n : Nat) :
    Compress (e.drop n) = Cslib.ωSequence.drop (BlockOf e n) (Compress e) := by
  let i := BlockOf e n
  let b := BlockStart e i
  have hb : b ≤ n := by
    dsimp [b, i]
    exact BlockOf_le e n
  rcases BlockOf_spec e n with hstrict | hfinal
  · have hn' : n < nextBlock e b := by
      simpa [b, i, BlockStart] using hstrict
    have hneq : e n = e b := eq_of_block_between e b n hb hn'
    have hshift : ∀ k : Nat, BlockStart (e.drop n) (Nat.succ k) + n =
        BlockStart e (i + Nat.succ k) :=
      BlockStart_drop_shift e i n (by simpa [b] using hb) hn'
    funext k
    cases k with
    | zero =>
        simp [Compress, BlockStart, Cslib.ωSequence.drop]
        simpa [i, b] using hneq
    | succ k =>
        simp [Compress, BlockStart]
        have hsk' : n + nextBlock (e.drop n) (BlockStart (e.drop n) k) =
            nextBlock e (BlockStart e (i + k)) := by
          simpa [BlockStart, Nat.add_comm] using hshift k
        rw [hsk']
  · have hfinal' : nextBlock e b = b := by
      simpa [b, i, BlockStart] using hfinal
    have hnone : ¬ ∃ j, b ≤ j ∧ e (j + 1) ≠ e j := by
      intro hc
      have hgt : b < nextBlock e b := by
        unfold nextBlock
        have hfind : b ≤ Nat.find (p := fun j => b ≤ j ∧ e (j + 1) ≠ e j) hc :=
          (Nat.find_spec (p := fun j => b ≤ j ∧ e (j + 1) ≠ e j) hc).1
        simp [hc]
        omega
      omega
    have hconst (m : Nat) (hm : b ≤ m) : e m = e b := by
      induction m with
      | zero => have hb0 : b = 0 := le_antisymm hm (Nat.zero_le b); simp [hb0]
      | succ m ih =>
          by_cases hbm : b ≤ m
          · have hstepm : e (m + 1) = e m := by
              by_contra hne
              exact False.elim (hnone ⟨m, hbm, hne⟩)
            rw [hstepm]
            exact ih hbm
          · have hb'' : b = m + 1 := le_antisymm hm (Nat.succ_le_of_lt (Nat.lt_of_not_ge hbm))
            simp [hb'']
    have hconstDrop (j : Nat) : (e.drop n) (j + 1) = (e.drop n) j := by
      simp [Cslib.ωSequence.drop]
      rw [hconst (j + 1 + n) (by omega), hconst (j + n) (by omega)]
    have hnoneDrop : ¬ ∃ j, (e.drop n) (j + 1) ≠ (e.drop n) j := by
      intro hc
      rcases hc with ⟨j, hj⟩
      exact hj (hconstDrop j)
    have hnext0 : nextBlock (e.drop n) 0 = 0 := by
      unfold nextBlock
      have hnone0 : ¬ ∃ j, 0 ≤ j ∧ (e.drop n) (j + 1) ≠ (e.drop n) j := by
        intro hc
        rcases hc with ⟨j, _hj0, hj⟩
        exact False.elim (hnoneDrop ⟨j, hj⟩)
      rw [dif_neg hnone0]
    have hBS (k : Nat) : BlockStart (e.drop n) k = 0 := by
      induction k with
      | zero => simp [BlockStart]
      | succ k ih =>
          simp [BlockStart, ih, hnext0]
    have hBS2 (k : Nat) : BlockStart e (i + k) = b := by
      induction k with
      | zero => simp [b]
      | succ k ih =>
          simp [BlockStart, ih, hfinal', b]
    funext k
    simp [Compress, hBS k]
    rw [hBS2 k]
    exact hconst n hb

/-! ## Step-level matching -/

/-- Block starts are monotone in the block index. -/
theorem BlockStart_mono_le {σ : Type u} (e : Behavior σ) {j k : Nat} (h : j ≤ k) :
    BlockStart e j ≤ BlockStart e k := by
  induction k with
  | zero =>
      have hj : j = 0 := Nat.eq_zero_of_le_zero h
      subst hj
      rfl
  | succ k ih =>
      by_cases hjk : j ≤ k
      · exact le_trans (ih hjk) (BlockStart_mono e k)
      · have hj : j = k + 1 := le_antisymm h (Nat.succ_le_of_lt (Nat.lt_of_not_ge hjk))
        subst hj
        rfl

/-- Either the next block starts strictly after the current one, or the
block starts have stabilized (the final block). -/
theorem BlockStart_next_spec {σ : Type u} (e : Behavior σ) (i : Nat) :
    BlockStart e (i + 1) < BlockStart e (i + 2) ∨ BlockStart e (i + 2) = BlockStart e (i + 1) := by
  by_cases h : BlockStart e (i + 1) < BlockStart e (i + 2)
  · exact Or.inl h
  · exact Or.inr (le_antisymm (le_of_not_gt h) (BlockStart_mono_le e (by omega)))

/-- Block `i` is non-final (there is a change after its start) iff the
compressed sequence changes at `i`. -/
theorem nonfinal_iff_compression_change {σ : Type u} (e : Behavior σ) (i : Nat) :
    nextBlock e (BlockStart e i) > BlockStart e i ↔ Compress e i ≠ Compress e (i + 1) := by
  let b := BlockStart e i
  have hc : Compress e i = e b := by simp [Compress, b]
  have hc' : Compress e (i + 1) = e (nextBlock e b) := by
    simp [Compress, b, BlockStart]
  rw [hc, hc']
  constructor
  · intro h
    by_contra hEq
    have hch : ∃ m, b ≤ m ∧ e (m + 1) ≠ e m := by
      by_cases hc2 : ∃ m, b ≤ m ∧ e (m + 1) ≠ e m
      · exact hc2
      · have hnb : nextBlock e b = b := by
          unfold nextBlock
          rw [dif_neg hc2]
        have hb : b = nextBlock e b := hnb.symm
        dsimp [b] at h hb
        exact False.elim (by omega)
    have hnb : nextBlock e b = Nat.find (p := fun m => b ≤ m ∧ e (m + 1) ≠ e m) hch + 1 := by
      unfold nextBlock
      rw [dif_pos hch]
    have hstep : e (nextBlock e b) ≠ e (nextBlock e b - 1) := by
      rw [hnb]
      simpa [Nat.add_sub_cancel] using (Nat.find_spec (p := fun m => b ≤ m ∧ e (m + 1) ≠ e m) hch).2
    have hpred : e (nextBlock e b - 1) = e b := by
      exact eq_of_block_between e b (nextBlock e b - 1) (by dsimp [b]; omega) (by dsimp [b]; omega)
    exact hstep (hEq.symm.trans hpred.symm)
  · intro hne
    by_contra hle
    have hEq : nextBlock e b = b := le_antisymm (le_of_not_gt hle) (nextBlock_ge e b)
    exact hne (by rw [hEq])

namespace SimFull

/-- Non-finality of block `i` transfers across the equivalence. -/
theorem nonfinal_iff {σ : Type u} {e f : Behavior σ} (h : SimFull e f) (i : Nat) :
    nextBlock e (BlockStart e i) > BlockStart e i ↔
      nextBlock f (BlockStart f i) > BlockStart f i := by
  have hc1 : Compress e i ≠ Compress e (i + 1) ↔ Compress f i ≠ Compress f (i + 1) := by
    constructor
    · intro hne hnef
      have hce := congrFun h i
      have hcf := congrFun h (i + 1)
      exact hne (hce.trans (hnef.trans hcf.symm))
    · intro hne hnef
      have hce := congrFun h i
      have hcf := congrFun h (i + 1)
      exact hne (hce.symm.trans (hnef.trans hcf))
  rw [nonfinal_iff_compression_change e i, nonfinal_iff_compression_change f i]
  exact hc1

end SimFull

/-- Every block before `BlockOf e n` is non-final. -/
theorem BlockOf_blocks_nonfinal {σ : Type u} (e : Behavior σ) (n : Nat) :
    ∀ k, k < BlockOf e n → nextBlock e (BlockStart e k) > BlockStart e k := by
  intro k hk
  by_contra hnot
  have hEq : nextBlock e (BlockStart e k) = BlockStart e k :=
    le_antisymm (le_of_not_gt hnot) (nextBlock_ge e (BlockStart e k))
  have hstart : BlockStart e (k + 1) = BlockStart e k := by
    simpa [BlockStart] using hEq
  have hpk : n < BlockStart e (k + 1) ∨ BlockStart e (k + 1) = BlockStart e k := Or.inr hstart
  have hmin : BlockOf e n ≤ k := by
    simpa [BlockOf] using Nat.find_min' (BlockOf_exists e n) (m := k) hpk
  omega

/-- If `n` lies in block `i` (before its end, or in the final block) and all
earlier blocks are non-final, then `BlockOf e n = i`. -/
theorem BlockOf_eq_of_between {σ : Type u} (e : Behavior σ) (i n : Nat)
    (hle : BlockStart e i ≤ n)
    (hlt : n < BlockStart e (i + 1) ∨ BlockStart e (i + 1) = BlockStart e i)
    (hstrict : ∀ k, k < i → nextBlock e (BlockStart e k) > BlockStart e k) :
    BlockOf e n = i := by
  have hle1 : BlockOf e n ≤ i := by
    simpa [BlockOf] using Nat.find_min' (BlockOf_exists e n) (m := i) hlt
  have hnot : ∀ k, k < i →
      ¬ (n < BlockStart e (k + 1) ∨ BlockStart e (k + 1) = BlockStart e k) := by
    intro k hk hp
    rcases hp with h1 | h2
    · have hmono : BlockStart e (k + 1) ≤ BlockStart e i := BlockStart_mono_le e (by omega)
      omega
    · have hstrictk := hstrict k hk
      have hnb : BlockStart e (k + 1) = nextBlock e (BlockStart e k) := by
        simp [BlockStart]
      omega
  have hle2 : i ≤ BlockOf e n := by
    by_contra hlt2
    have hko : BlockOf e n < i := by omega
    have hp : n < BlockStart e (BlockOf e n + 1) ∨ BlockStart e (BlockOf e n + 1) = BlockStart e (BlockOf e n) :=
      Nat.find_spec (p := fun k => n < BlockStart e (k + 1) ∨ BlockStart e (k + 1) = BlockStart e k)
        (BlockOf_exists e n)
    exact (hnot (BlockOf e n) hko) hp
  exact le_antisymm hle1 hle2

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

/-- Every suffix of `e` is stuttering-equivalent to some suffix of `f`:
dropping `n` steps shifts the compression to the block containing `n`, and
`f` has a block with the same index. -/
theorem sim_suffix_left {σ : Type u} {e f : Behavior σ} (h : SimFull e f) :
    ∀ n : Nat, ∃ m : Nat, SimFull (e.drop n) (f.drop m) := by
  intro n
  let i := BlockOf e n
  refine ⟨BlockStart f i, ?_⟩
  unfold SimFull
  rw [Compress_drop_blockOf e n, Compress_drop_blockStart f i]
  dsimp [i]
  rw [h]

/-- Right-handed version of `sim_suffix_left`. -/
theorem sim_suffix_right {σ : Type u} {e f : Behavior σ} (h : SimFull e f) :
    ∀ m : Nat, ∃ n : Nat, SimFull (e.drop n) (f.drop m) := by
  intro m
  rcases sim_suffix_left (SimFull.symm h) m with ⟨n, hsf⟩
  exact ⟨n, SimFull.symm hsf⟩

/-- Step-level suffix matching: for each position there is a matching
position such that either the next steps also match, or the left next step
matches the same right position (a stutter on the right). -/
theorem sim_step {σ : Type u} {e f : Behavior σ} (h : SimFull e f) :
    ∀ n : Nat, ∃ m : Nat,
      SimFull (e.drop n) (f.drop m) ∧
        (SimFull (e.drop (n + 1)) (f.drop (m + 1)) ∨ SimFull (e.drop (n + 1)) (f.drop m)) := by
  intro n
  have hle_i : BlockStart e (BlockOf e n) ≤ n := BlockOf_le e n
  have hblocks : ∀ k, k < BlockOf e n →
      nextBlock e (BlockStart e k) > BlockStart e k := BlockOf_blocks_nonfinal e n
  rcases BlockOf_spec e n with hstrict | hfinal
  · by_cases hn1 : n + 1 < BlockStart e (BlockOf e n + 1)
    · -- n and n+1 are both inside block i
      refine ⟨BlockStart f (BlockOf e n), ?_, Or.inr ?_⟩
      · unfold SimFull
        rw [Compress_drop_blockOf e n, Compress_drop_blockStart f (BlockOf e n)]
        rw [h]
      · have hbo : BlockOf e (n + 1) = BlockOf e n :=
          BlockOf_eq_of_between e (BlockOf e n) (n + 1) (by omega) (Or.inl hn1) hblocks
        unfold SimFull
        rw [Compress_drop_blockOf e (n + 1), Compress_drop_blockStart f (BlockOf e n)]
        rw [hbo, h]
    · -- n is the last position of block i: e takes a real step into block i+1
      have hn1' : n + 1 = BlockStart e (BlockOf e n + 1) := by omega
      have hnonfinal : nextBlock e (BlockStart e (BlockOf e n)) > BlockStart e (BlockOf e n) := by
        have hnb : BlockStart e (BlockOf e n + 1) = nextBlock e (BlockStart e (BlockOf e n)) := by
          simp [BlockStart]
        have hgt : BlockStart e (BlockOf e n + 1) > BlockStart e (BlockOf e n) := by
          rw [← hn1']
          omega
        rw [← hnb]
        exact hgt
      have hnonfinal_f : nextBlock f (BlockStart f (BlockOf e n)) > BlockStart f (BlockOf e n) :=
        (SimFull.nonfinal_iff h (BlockOf e n)).1 hnonfinal
      have hnonfinal_f' : BlockStart f (BlockOf e n) < BlockStart f (BlockOf e n + 1) := by
        simpa [BlockStart] using hnonfinal_f
      let m := BlockStart f (BlockOf e n + 1) - 1
      have hm1 : m + 1 = BlockStart f (BlockOf e n + 1) := by
        dsimp [m]
        omega
      have hbo_f : BlockOf f m = BlockOf e n := BlockOf_eq_of_between f (BlockOf e n) m
        (by dsimp [m]; omega) (Or.inl (by dsimp [m]; omega)) (by
          intro k hk
          exact (SimFull.nonfinal_iff h k).1 (hblocks k hk))
      have hbo_e_next : BlockOf e (n + 1) = BlockOf e n + 1 :=
        BlockOf_eq_of_between e (BlockOf e n + 1) (n + 1)
        (by omega) (by
          rcases BlockStart_next_spec e (BlockOf e n) with h1 | h2
          · left
            rw [hn1']
            exact h1
          · right
            exact h2) (by
          intro k hk
          by_cases hki : k < BlockOf e n
          · exact hblocks k hki
          · have : k = BlockOf e n := by omega
            subst k
            exact hnonfinal)
      have hbo_f_next : BlockOf f (m + 1) = BlockOf e n + 1 :=
        BlockOf_eq_of_between f (BlockOf e n + 1) (m + 1)
        (by omega) (by
          rcases BlockStart_next_spec f (BlockOf e n) with h1 | h2
          · left
            rw [hm1]
            exact h1
          · right
            exact h2) (by
          intro k hk
          by_cases hki : k < BlockOf e n
          · exact (SimFull.nonfinal_iff h k).1 (hblocks k hki)
          · have : k = BlockOf e n := by omega
            subst k
            exact hnonfinal_f)
      refine ⟨m, ?_, Or.inl ?_⟩
      · unfold SimFull
        rw [Compress_drop_blockOf e n, Compress_drop_blockOf f m]
        rw [hbo_f, h]
      · unfold SimFull
        rw [Compress_drop_blockOf e (n + 1), Compress_drop_blockOf f (m + 1)]
        rw [hbo_e_next, hbo_f_next, h]
  · -- block i is final
    have hfinal_e : nextBlock e (BlockStart e (BlockOf e n)) = BlockStart e (BlockOf e n) := by
      simpa [BlockStart] using hfinal
    have hfinal_f : nextBlock f (BlockStart f (BlockOf e n)) = BlockStart f (BlockOf e n) := by
      by_contra hnot
      have hgt_f : nextBlock f (BlockStart f (BlockOf e n)) > BlockStart f (BlockOf e n) :=
        lt_of_le_of_ne (nextBlock_ge f (BlockStart f (BlockOf e n))) (fun h => hnot h.symm)
      have hgt_e := (SimFull.nonfinal_iff h (BlockOf e n)).2 hgt_f
      omega
    refine ⟨BlockStart f (BlockOf e n), ?_, Or.inr ?_⟩
    · unfold SimFull
      rw [Compress_drop_blockOf e n, Compress_drop_blockStart f (BlockOf e n)]
      rw [h]
    · have hbo : BlockOf e (n + 1) = BlockOf e n :=
        BlockOf_eq_of_between e (BlockOf e n) (n + 1) (by omega) (Or.inr hfinal) hblocks
      unfold SimFull
      rw [Compress_drop_blockOf e (n + 1), Compress_drop_blockStart f (BlockOf e n)]
      rw [hbo, h]

instance setoid (σ : Type u) : Setoid (Behavior σ) where
  r := SimFull
  iseqv := ⟨SimFull.refl, SimFull.symm, SimFull.trans⟩

end SimFull

/-- The stuttering quotient for the full equivalence. -/
abbrev StutQuotFull (σ : Type u) := Quot (SimFull : Behavior σ → Behavior σ → Prop)

/-! ## Full stuttering invariance (preservation theorems migrated to `SimFull`)

The preservation theorems of `TlaDsl/Meta.lean`, re-proved for the full
stuttering equivalence. The `always`/`eventually`/`leadsTo` cases use the
suffix-matching lemmas above; the action-level (`NstutInv`, `WF_v`, `SF_v`)
cases use `sim_step` and live in `TlaDsl/Meta.lean` (`NstutInvFull`,
`stutinv_full_WF_v`, `stutinv_full_SF_v`, ...), with `SimFull.map`
completing the refinement-side migration.
-/

/-- A formula is invariant under full stuttering equivalence. -/
def StutInvFull {σ : Type u} (F : Pred σ) : Prop :=
  ∀ e f : Behavior σ, SimFull e f → (F e ↔ F f)

theorem stutinv_full_statePred {σ : Type u} (p : StatePred σ) : StutInvFull (statePred p) := by
  intro e f h
  constructor <;> intro hpf
  · simpa [statePred] using (SimFull.first h ▸ hpf)
  · simpa [statePred] using (SimFull.first h ▸ hpf)

theorem stutinv_full_purePred {σ : Type u} (p : Prop) : StutInvFull (purePred (σ := σ) p) := by
  intro e f h
  simp [purePred]

theorem stutinv_full_and {σ : Type u} {F G : Pred σ} (hF : StutInvFull F) (hG : StutInvFull G) :
    StutInvFull (tlaAnd F G) := by
  intro e f h
  constructor <;> intro hfg
  · exact ⟨(hF e f h).1 hfg.1, (hG e f h).1 hfg.2⟩
  · exact ⟨(hF e f h).2 hfg.1, (hG e f h).2 hfg.2⟩

theorem stutinv_full_or {σ : Type u} {F G : Pred σ} (hF : StutInvFull F) (hG : StutInvFull G) :
    StutInvFull (tlaOr F G) := by
  intro e f h
  constructor <;> intro hfg
  · exact hfg.elim (fun hFe => Or.inl ((hF e f h).1 hFe)) (fun hGe => Or.inr ((hG e f h).1 hGe))
  · exact hfg.elim (fun hFf => Or.inl ((hF e f h).2 hFf)) (fun hGf => Or.inr ((hG e f h).2 hGf))

theorem stutinv_full_not {σ : Type u} {F : Pred σ} (hF : StutInvFull F) : StutInvFull (tlaNot F) := by
  intro e f h
  constructor
  · intro hnf hFf
    exact hnf ((hF e f h).2 hFf)
  · intro hnf hFe
    exact hnf ((hF e f h).1 hFe)

theorem stutinv_full_imp {σ : Type u} {F G : Pred σ} (hF : StutInvFull F) (hG : StutInvFull G) :
    StutInvFull (tlaImp F G) := by
  intro e f h
  constructor
  · intro hfg hFf
    exact (hG e f h).1 (hfg ((hF e f h).2 hFf))
  · intro hfg hFe
    exact (hG e f h).2 (hfg ((hF e f h).1 hFe))

theorem stutinv_full_iff {σ : Type u} {F G : Pred σ} (hF : StutInvFull F) (hG : StutInvFull G) :
    StutInvFull (tlaIff F G) := by
  intro e f h
  constructor <;> intro hfg
  · constructor
    · intro hFf
      exact (hG e f h).1 (hfg.1 ((hF e f h).2 hFf))
    · intro hGf
      exact (hF e f h).1 (hfg.2 ((hG e f h).2 hGf))
  · constructor
    · intro hFe
      exact (hG e f h).2 (hfg.1 ((hF e f h).1 hFe))
    · intro hGe
      exact (hF e f h).2 (hfg.2 ((hG e f h).1 hGe))

theorem stutinv_full_always {σ : Type u} {F : Pred σ} (hF : StutInvFull F) :
    StutInvFull (always F) := by
  intro e f h
  constructor <;> intro hA
  · intro m
    rcases SimFull.sim_suffix_right h m with ⟨n, hsim⟩
    exact (hF (e.drop n) (f.drop m) hsim).1 (hA n)
  · intro n
    rcases SimFull.sim_suffix_left h n with ⟨m, hsim⟩
    exact (hF (e.drop n) (f.drop m) hsim).2 (hA m)

theorem stutinv_full_eventually {σ : Type u} {F : Pred σ} (hF : StutInvFull F) :
    StutInvFull (eventually F) := by
  intro e f h
  constructor <;> intro hE
  · rcases hE with ⟨n, hFn⟩
    rcases SimFull.sim_suffix_left h n with ⟨m, hsim⟩
    exact ⟨m, (hF (e.drop n) (f.drop m) hsim).1 hFn⟩
  · rcases hE with ⟨m, hFm⟩
    rcases SimFull.sim_suffix_right h m with ⟨n, hsim⟩
    exact ⟨n, (hF (e.drop n) (f.drop m) hsim).2 hFm⟩

theorem stutinv_full_leadsTo {σ : Type u} {P Q : Pred σ} (hP : StutInvFull P) (hQ : StutInvFull Q) :
    StutInvFull (leadsTo P Q) := by
  unfold leadsTo
  exact stutinv_full_always (stutinv_full_imp hP (stutinv_full_eventually hQ))

/-! ## The full quotient characterization -/

namespace StutInvFull

/-- A fully stuttering-invariant formula descends to the full quotient. -/
def lift {σ : Type u} {F : Pred σ} (hF : StutInvFull F) : StutQuotFull σ → Prop :=
  Quot.lift F (fun e f hsim => propext (hF e f hsim))

theorem lift_apply {σ : Type u} {F : Pred σ} (hF : StutInvFull F) (e : Behavior σ) :
    hF.lift (Quot.mk SimFull e) = F e := by
  simp [StutInvFull.lift]

end StutInvFull

/-- Fully stuttering-invariant formulas are exactly the well-defined
predicates on the full stuttering quotient. -/
theorem stutinv_full_descends {σ : Type u} (F : Pred σ) :
    StutInvFull F ↔
      ∃ G : StutQuotFull σ → Prop,
        (∀ e : Behavior σ, G (Quot.mk SimFull e) = F e) ∧
          ∀ G' : StutQuotFull σ → Prop, (∀ e : Behavior σ, G' (Quot.mk SimFull e) = F e) → G' = G := by
  constructor
  · intro hF
    refine ⟨hF.lift, ?_⟩
    constructor
    · intro e
      exact hF.lift_apply e
    · intro G hG
      funext q
      refine Quot.ind (β := fun q => G q = hF.lift q) ?_ q
      intro e
      calc
        G (Quot.mk SimFull e) = F e := hG e
        _ = hF.lift (Quot.mk SimFull e) := (hF.lift_apply e).symm
  · rintro ⟨G, hG, _⟩
    intro e f hsim
    have hq : Quot.mk SimFull e = Quot.mk SimFull f := Quot.sound hsim
    constructor <;> intro hFe
    · simpa [(hG e).symm, hG f, hq] using hFe
    · simpa [(hG f).symm, hG e, hq.symm] using hFe

end Tla
