import TlaDsl.SimFull

open Classical

namespace Tla

/-! ## Projection preserves the full stuttering equivalence

Projecting away the hidden component can only *merge* adjacent blocks, so
the compression of the projection is the compression of the projected
block values (`compress_proj`). Hence `map proj` is a `SimFull` morphism
(`SimFull.map_proj`). This closes the representation theorem: the history
canonical spec `histSpec F` is itself stuttering-invariant (used in
`TlaDsl/Canonical.lean`).
-/

/-- The projected block values of a behavior. -/
noncomputable def projCompress {σ : Type u} {H : Type w} (e : Behavior (σ × H)) : Behavior σ :=
  ⟨fun n => (Compress e n).1⟩

/-- A final block (whose start does not advance) makes its tail constant. -/
theorem eq_of_final {σ : Type u} (e : Behavior σ) (k : Nat)
    (h : BlockStart e (k + 1) = BlockStart e k) :
    ∀ m : Nat, BlockStart e k ≤ m → e m = e (BlockStart e k) := by
  have hself : nextBlock e (BlockStart e k) = BlockStart e k := by
    simpa [BlockStart] using h
  have hnochange : ¬ ∃ m : Nat, BlockStart e k ≤ m ∧ e (m + 1) ≠ e m := by
    intro hc
    have hfind : BlockStart e k ≤
        Nat.find (p := fun m => BlockStart e k ≤ m ∧ e (m + 1) ≠ e m) hc :=
      (Nat.find_spec (p := fun m => BlockStart e k ≤ m ∧ e (m + 1) ≠ e m) hc).1
    unfold nextBlock at hself
    rw [dif_pos hc] at hself
    omega
  refine Nat.le_induction ?_ ?_
  · rfl
  · intro m hm ih
    have hnm : e (m + 1) = e m := by
      by_contra hne
      exact hnochange ⟨m, hm, hne⟩
    rw [hnm, ih]

/-- A block whose start does not advance is final: its tail is constant, so
all later blocks have the same compression. -/
theorem compress_constant_of_final {σ : Type u} (e : Behavior σ) (k : Nat)
    (h : BlockStart e (k + 1) = BlockStart e k) :
    ∀ j : Nat, k ≤ j → Compress e j = Compress e k := by
  have htail := eq_of_final e k h
  intro j hj
  simp [Compress]
  exact htail (BlockStart e j) (BlockStart_mono_le e hj)

/-- A change in the projected block values makes the block non-final. -/
theorem nonfinal_of_proj_change {σ : Type u} {H : Type w} (e : Behavior (σ × H))
    (b : Nat) (h : (projCompress e) (b + 1) ≠ (projCompress e) b) :
    nextBlock e (BlockStart e b) > BlockStart e b := by
  apply (nonfinal_iff_compression_change e b).2
  intro hEq
  exact h (by simp [projCompress, hEq])

/-- A visible change happens exactly at a boundary between blocks with
different projections: the block before the change, and the change implies
a change of the projected block values at that block. -/
theorem proj_change_of_block_change {σ : Type u} {H : Type w}
    (e : Behavior (σ × H)) (i : Nat)
    (h : (Cslib.ωSequence.map Prod.fst e) (i + 1) ≠ (Cslib.ωSequence.map Prod.fst e) i) :
    e (i + 1) ≠ e i ∧
      (projCompress e) (BlockOf e i + 1) ≠ (projCompress e) (BlockOf e i) := by
  have hene : e (i + 1) ≠ e i := by
    intro hEq
    exact h (by simp [hEq])
  let b := BlockOf e i
  have hspec := BlockOf_spec e i
  have hstrict : i < BlockStart e (b + 1) := by
    rcases hspec with h1 | h2
    · exact h1
    · -- final block: the tail is constant, contradicting the visible change
      exfalso
      have htail := eq_of_final e b h2
      have hi0 : e i = Compress e b := by
        simpa [Compress, b] using htail i (by simpa [b] using BlockOf_le e i)
      have hi1 : e (i + 1) = Compress e b := by
        simpa [Compress, b] using htail (i + 1) (by have hb := BlockOf_le e i; dsimp [b]; omega)
      exact hene (hi1.trans hi0.symm)
  have hnext : i + 1 = BlockStart e (b + 1) := by
    have hle : i + 1 ≤ BlockStart e (b + 1) := by omega
    have hge : BlockStart e (b + 1) ≤ i + 1 := by
      by_contra hnot
      have hlt : i + 1 < BlockStart e (b + 1) := by omega
      have hsame : e (i + 1) = e i := by
        have h1 : e (i + 1) = e (BlockStart e b) :=
          eq_of_block_between e (BlockStart e b) (i + 1)
            (by have hb := BlockOf_le e i; dsimp [b]; omega)
            (by simpa [b, BlockStart] using hlt)
        have h2 : e i = e (BlockStart e b) :=
          eq_of_block_between e (BlockStart e b) i
            (by have hb := BlockOf_le e i; dsimp [b]; omega)
            (by simpa [b, BlockStart] using hstrict)
        exact h1.trans h2.symm
      exact hene hsame
    exact (le_antisymm hge hle).symm
  have hei : e i = Compress e b := by
    simpa [Compress, b] using eq_of_block_between e (BlockStart e b) i
      (by simpa [b] using BlockOf_le e i) (by simpa [b, BlockStart] using hstrict)
  constructor
  · exact hene
  · have hpe : (Cslib.ωSequence.map Prod.fst e) (i + 1) ≠ (Cslib.ωSequence.map Prod.fst e) i := h
    intro hEq
    apply hpe
    simp [Cslib.ωSequence.map, hnext, hei]
    change (Compress e (b + 1)).1 = (Compress e b).1
    exact hEq

/-- The first visible change after a block start is the start of the first
block whose projected value differs (`nextBlock` on both sides). -/
theorem nextBlock_map_proj {σ : Type u} {H : Type w} (e : Behavior (σ × H)) (k : Nat) :
    nextBlock (Cslib.ωSequence.map Prod.fst e) (BlockStart e k) =
      BlockStart e (nextBlock (projCompress e) k) := by
  let p : Behavior σ := projCompress e
  let pe : Behavior σ := Cslib.ωSequence.map Prod.fst e
  by_cases hQ : ∃ b : Nat, k ≤ b ∧ p (b + 1) ≠ p b
  · let m0 : Nat := Nat.find (p := fun b => k ≤ b ∧ p (b + 1) ≠ p b) hQ
    have hq1 : k ≤ m0 := (Nat.find_spec (p := fun b => k ≤ b ∧ p (b + 1) ≠ p b) hQ).1
    have hq2 : p (m0 + 1) ≠ p m0 := (Nat.find_spec (p := fun b => k ≤ b ∧ p (b + 1) ≠ p b) hQ).2
    -- every block up to `m0` is non-final (otherwise the projection would be
    -- constant from there on, contradicting the change at `m0`)
    have hnonfinal : ∀ b : Nat, b ≤ m0 → nextBlock e (BlockStart e b) > BlockStart e b := by
      intro b hb
      by_contra hnot
      have hself : nextBlock e (BlockStart e b) = BlockStart e b :=
        le_antisymm (le_of_not_gt hnot) (nextBlock_ge e (BlockStart e b))
      have hbs : BlockStart e (b + 1) = BlockStart e b := by simpa [BlockStart] using hself
      have hconst := compress_constant_of_final e b hbs
      have hpconst : ∀ j : Nat, b ≤ j → p j = p b := by
        intro j hj
        simpa [p, projCompress] using congrArg Prod.fst (hconst j hj)
      exact hq2 ((hpconst m0 (by omega)).trans (hpconst (m0 + 1) (by omega)).symm).symm
    let i0 : Nat := BlockStart e (m0 + 1) - 1
    have hbsm : BlockStart e (m0 + 1) > BlockStart e m0 := by
      simpa [BlockStart] using hnonfinal m0 (by omega)
    have hpos : 0 < BlockStart e (m0 + 1) := by omega
    have hi0 : i0 + 1 = BlockStart e (m0 + 1) := by
      dsimp [i0]
      omega
    -- the first visible change is at `i0`
    have hRw : BlockStart e k ≤ i0 ∧ pe (i0 + 1) ≠ pe i0 := by
      constructor
      · dsimp [i0]
        have hle : BlockStart e k ≤ BlockStart e m0 := BlockStart_mono_le e hq1
        omega
      · have hei0 : e i0 = Compress e m0 := by
          have hb1 : BlockStart e m0 ≤ BlockStart e (m0 + 1) - 1 := by omega
          have hb2 : BlockStart e (m0 + 1) - 1 < nextBlock e (BlockStart e m0) := by
            simpa [BlockStart] using (by omega : BlockStart e (m0 + 1) - 1 < BlockStart e (m0 + 1))
          simpa [Compress, i0] using eq_of_block_between e (BlockStart e m0)
            (BlockStart e (m0 + 1) - 1) hb1 hb2
        have hpe : pe (i0 + 1) ≠ pe i0 := by
          intro hEq
          apply hq2
          change (Compress e (m0 + 1)).1 = (Compress e m0).1
          convert hEq using 1
          · simp [pe, hi0, Compress]
          · simp [pe, hei0, Compress]
        exact hpe
    have hRmin : ∀ i : Nat, BlockStart e k ≤ i → i < i0 →
        ¬ (pe (i + 1) ≠ pe i) := by
      intro i hik hi hne
      have hene : e (i + 1) ≠ e i := by
        intro hEq
        exact hne (by simp [pe, hEq])
      let b := BlockOf e i
      have hbm : b ≤ m0 := by
        by_contra hb
        have hle1 : BlockStart e (m0 + 1) ≤ BlockStart e b := BlockStart_mono_le e (by omega)
        have hle2 : BlockStart e b ≤ i := BlockOf_le e i
        dsimp [i0] at hi
        omega
      have hkb : k ≤ b := by
        by_contra hb
        have hspec := BlockOf_spec e i
        rcases hspec with h1 | h2
        · have hmono : BlockStart e (b + 1) ≤ BlockStart e k :=
            BlockStart_mono_le e (by dsimp [b] at hb ⊢; omega)
          dsimp [b] at h1 hmono
          omega
        · have hconst := compress_constant_of_final e b h2
          have hpconst : ∀ j : Nat, b ≤ j → p j = p b := by
            intro j hj
            simpa [p, projCompress] using congrArg Prod.fst (hconst j hj)
          exact hq2 ((hpconst m0 (by dsimp [b] at hb ⊢; omega)).trans
            (hpconst (m0 + 1) (by dsimp [b] at hb ⊢; omega)).symm).symm
      have hnonfinal_b : nextBlock e (BlockStart e b) > BlockStart e b := hnonfinal b hbm
      have hbs : BlockStart e (b + 1) > BlockStart e b := by simpa [BlockStart] using hnonfinal_b
      have hbstart : BlockStart e b ≤ i := BlockOf_le e i
      have hbend : i < BlockStart e (b + 1) := by
        have hspec := BlockOf_spec e i
        rcases hspec with h1 | h2
        · exact h1
        · exfalso
          exact hbs.ne h2.symm
      by_cases hsplit : i + 1 < BlockStart e (b + 1)
      · have hsame : e (i + 1) = e i :=
          have h1 : e (i + 1) = e (BlockStart e b) :=
            eq_of_block_between e (BlockStart e b) (i + 1)
              (by dsimp [b] at hbstart ⊢; omega)
              (by simpa [BlockStart] using hsplit)
          have h2 : e i = e (BlockStart e b) :=
            eq_of_block_between e (BlockStart e b) i
              (by exact hbstart)
              (by simpa [BlockStart] using hbend)
          h1.trans h2.symm
        exact hne (by simp [pe, hsame])
      · have hnext : i + 1 = BlockStart e (b + 1) := by dsimp [b] at hbend hsplit ⊢; omega
        have hb_lt : b < m0 := by
          by_contra hnot
          have hmono : BlockStart e (m0 + 1) ≤ BlockStart e (b + 1) :=
            BlockStart_mono_le e (by dsimp [b] at hnot ⊢; omega)
          dsimp [i0] at hi
          dsimp [b] at hnext
          omega
        have hnotQ : ¬ (k ≤ b ∧ p (b + 1) ≠ p b) := by
          intro hQb
          have hmin : m0 ≤ b := Nat.find_min' hQ (m := b) hQb
          omega
        have hpb : p (b + 1) = p b := by
          by_contra hneq
          exact hnotQ ⟨hkb, hneq⟩
        have hei : e i = Compress e b := by
          simpa [Compress, b] using eq_of_block_between e (BlockStart e b) i hbstart
            (by simpa [BlockStart] using hbend)
        apply hne
        simp [Cslib.ωSequence.map, pe, hnext, hei]
        change (Compress e (b + 1)).1 = (Compress e b).1
        exact hpb
    -- minimality gives the found change position, and hence the equality
    have hR : ∃ i : Nat, BlockStart e k ≤ i ∧ pe (i + 1) ≠ pe i := ⟨i0, hRw⟩
    have hfind_le : Nat.find (p := fun i => BlockStart e k ≤ i ∧ pe (i + 1) ≠ pe i) hR ≤ i0 :=
      Nat.find_min' hR (m := i0) hRw
    have hfind_ge : i0 ≤ Nat.find (p := fun i => BlockStart e k ≤ i ∧ pe (i + 1) ≠ pe i) hR := by
      by_contra hnot
      have hlt : Nat.find (p := fun i => BlockStart e k ≤ i ∧ pe (i + 1) ≠ pe i) hR < i0 := by omega
      have hspec := Nat.find_spec (p := fun i => BlockStart e k ≤ i ∧ pe (i + 1) ≠ pe i) hR
      exact (hRmin (Nat.find (p := fun i => BlockStart e k ≤ i ∧ pe (i + 1) ≠ pe i) hR)
        hspec.1 hlt) hspec.2
    have hfind : Nat.find (p := fun i => BlockStart e k ≤ i ∧ pe (i + 1) ≠ pe i) hR = i0 :=
      le_antisymm hfind_le hfind_ge
    unfold nextBlock
    rw [dif_pos hR, dif_pos hQ, hfind]
    exact hi0
  · -- no projected change from `k` on: the projection is constant from
    -- `BlockStart e k` on, so the next block of the projection is itself
    have hRnone : ¬ ∃ i : Nat, BlockStart e k ≤ i ∧ pe (i + 1) ≠ pe i := by
      rintro ⟨i, hik, hne⟩
      have hpc := proj_change_of_block_change e i (by simpa [pe] using hne)
      apply hQ
      refine ⟨BlockOf e i, ?_, hpc.2⟩
      by_contra hb
      have hspec := BlockOf_spec e i
      rcases hspec with h1 | h2
      · have hmono : BlockStart e (BlockOf e i + 1) ≤ BlockStart e k :=
          BlockStart_mono_le e (by omega)
        omega
      · have hconst := compress_constant_of_final e (BlockOf e i) h2
        have hpconst : ∀ j : Nat, BlockOf e i ≤ j → p j = p (BlockOf e i) := by
          intro j hj
          simpa [p, projCompress] using congrArg Prod.fst (hconst j hj)
        -- no change at all from the final block on, so `p` is constant:
        -- use the change witness `i` via `hpc.2`
        have hne' : p (BlockOf e i + 1) ≠ p (BlockOf e i) := hpc.2
        exact hne' ((hpconst (BlockOf e i + 1) (by omega)).trans
          (hpconst (BlockOf e i) (by omega)).symm)
    have hnext_pe : nextBlock pe (BlockStart e k) = BlockStart e k := by
      unfold nextBlock
      rw [dif_neg (by simpa [pe] using hRnone)]
    have hnext_p : nextBlock p k = k := by
      unfold nextBlock
      rw [dif_neg hQ]
    rw [hnext_pe, hnext_p]

/-- The block starts of the projection are the block starts of the original
behavior indexed by the block starts of the projected block values. -/
theorem BlockStart_map_proj {σ : Type u} {H : Type w} (e : Behavior (σ × H)) (n : Nat) :
    BlockStart (Cslib.ωSequence.map Prod.fst e) n = BlockStart e (BlockStart (projCompress e) n) := by
  induction n with
  | zero => simp [BlockStart]
  | succ n ih =>
      simp [BlockStart, ih, nextBlock_map_proj]

/-- The compression of the projection is the compression of the projected
block values. -/
theorem compress_proj {σ : Type u} {H : Type w} (e : Behavior (σ × H)) :
    Compress (Cslib.ωSequence.map Prod.fst e) = Compress (projCompress e) := by
  funext n
  calc
    Compress (Cslib.ωSequence.map Prod.fst e) n
        = (Cslib.ωSequence.map Prod.fst e) (BlockStart (Cslib.ωSequence.map Prod.fst e) n) := by
          simp [Compress]
    _ = (Cslib.ωSequence.map Prod.fst e) (BlockStart e (BlockStart (projCompress e) n)) := by
          rw [BlockStart_map_proj]
    _ = (Compress e (BlockStart (projCompress e) n)).1 := by
          simp [Cslib.ωSequence.map, Compress]
    _ = Compress (projCompress e) n := by simp [Compress, projCompress]

namespace SimFull

/-- Projecting away the hidden component preserves the full stuttering
equivalence (adjacent blocks may merge, but the compressed projections
agree). -/
theorem map_proj {σ : Type u} {H : Type w} {e f : Behavior (σ × H)}
    (h : SimFull e f) :
    SimFull (Cslib.ωSequence.map Prod.fst e) (Cslib.ωSequence.map Prod.fst f) := by
  unfold SimFull
  calc
    Compress (Cslib.ωSequence.map Prod.fst e) = Compress (projCompress e) := compress_proj e
    _ = Compress (projCompress f) := by
        congr 1
        ext n
        simp [projCompress]
        exact congrArg Prod.fst (congrFun h n)
    _ = Compress (Cslib.ωSequence.map Prod.fst f) := (compress_proj f).symm

end SimFull

end Tla
