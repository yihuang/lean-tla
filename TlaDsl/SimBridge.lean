import TlaDsl.Meta
import TlaDsl.SimFull

open Classical

namespace Tla

/-! # The Sim ↔ SimFull bridge

`Sim` (`Meta.lean`, finite stuttering: delete or duplicate finitely many
equal-state runs) and `SimFull` (`SimFull.lean`, run-compression: equal
maximal-run value sequences) are the two parallel stuttering-equivalence
theories. This file closes the reviewer's gap between them:

* `Sim.simFull` — every finite-stuttering equivalence is a full one, so
  `Sim ⊆ SimFull`. The key lemma `simFull_drop_stutter` shows a single
  stutter deletion/duplication leaves the compression unchanged (the first
  run loses one element, its value sequence is untouched).
* `stutQuot_to_full` — the **unified quotient**: the finite quotient
  (`StutQuot`, over `Sim`) embeds into the existing full one
  (`StutQuotFull`, over `SimFull`), via `Sim.simFull` + `Quot.lift`.
* the **characterization of the difference** — `simFull_doubled_alt` +
  `not_sim_doubled_alt` exhibit behaviors that are full-equivalent but not
  finite-equivalent: `doubled a b = a,a,b,b,a,a,…` has a stutter step in
  every run, forever, while `alt a b = a,b,a,b,…` has none. `SimFull`
  identifies them (both compress to `a,b,a,b,…`); `Sim` cannot, because
  "eventually no stutter steps" is a `Sim`-invariant that `alt` satisfies
  and `doubled` does not. So `SimFull` is exactly the closure of `Sim`
  under infinitely many stutter steps.
-/

/-! ## The refinement: `Sim` ⊆ `SimFull` -/

/-- Deleting a stuttering first step does not change the run-compression:
if `e 0 = e 1`, then `e` and `e.drop 1` have the same maximal runs (the
first run just loses one element). -/
theorem simFull_drop_stutter {σ : Type u} {e : Behavior σ} (hst : e 0 = e 1) :
    SimFull e (e.drop 1) := by
  unfold SimFull
  -- the compression of the dropped behavior is the compression of `e` from
  -- the block containing position 1
  have hcd := Compress_drop_blockOf e 1
  -- position 1 lies in the first block: `e 0 = e 1` means the next change
  -- is not at the boundary, so `nextBlock e 0 ≠ 1`
  have hnext : nextBlock e 0 ≠ 1 := by
    intro h1
    unfold nextBlock at h1
    by_cases hch : ∃ m : Nat, 0 ≤ m ∧ e (m + 1) ≠ e m
    · rw [dif_pos hch] at h1
      have hf : Nat.find (p := fun m => 0 ≤ m ∧ e (m + 1) ≠ e m) hch = 0 := by omega
      have hspec := Nat.find_spec (p := fun m => 0 ≤ m ∧ e (m + 1) ≠ e m) hch
      have hne : e 1 ≠ e 0 := by
        rw [hf] at hspec
        simpa using hspec.2
      exact hne hst.symm
    · rw [dif_neg hch] at h1
      omega
  have hlt : 1 < BlockStart e 1 ∨ BlockStart e 1 = BlockStart e 0 := by
    have hlt1 : 1 < nextBlock e 0 ∨ nextBlock e 0 = 0 := by
      have hle0 : 0 ≤ nextBlock e 0 := Nat.zero_le _
      omega
    simpa [BlockStart] using hlt1
  have hb : BlockOf e 1 = 0 :=
    BlockOf_eq_of_between e 0 1 (by simp [BlockStart]) hlt (by intro k hk; omega)
  ext n
  have hc := congrFun hcd n
  rw [hb] at hc
  simpa [Cslib.ωSequence.drop] using hc.symm

namespace Sim

/-- The finite stuttering equivalence refines the full one: deleting or
duplicating a stutter step (inductively, finitely many times) never changes
the run-compression. -/
theorem simFull {σ : Type u} {e f : Behavior σ} (h : Sim e f) : SimFull e f := by
  induction h with
  | refl e => exact SimFull.refl e
  | stepL e f hst hrest ih =>
      have h1 : SimFull e (e.drop 1) := simFull_drop_stutter hst
      exact SimFull.trans h1 ih
  | stepR e f hst hrest ih =>
      have h1 : SimFull (f.drop 1) f := SimFull.symm (simFull_drop_stutter hst)
      exact SimFull.trans ih h1

end Sim

/-! ## The unified quotient -/

/-- The finite quotient embeds into the full one: every finite-stuttering
equivalence is a full one (`Sim.simFull`), so the map on representatives
is well-defined. The full quotient is the *unified* one — it identifies at
least as much as `StutQuot`, and the finite theory is its subquotient. -/
def stutQuot_to_full (σ : Type u) : StutQuot σ → StutQuotFull σ :=
  Quot.lift (fun e : Behavior σ => Quot.mk (@SimFull σ) e) (by
    intro e f h
    exact Quot.sound (Sim.simFull h))

/-! ## Where they differ: the infinite-stuttering behaviors -/

/-- A behavior has no stutter steps eventually. -/
def EventuallyNoStutter {σ : Type u} (e : Behavior σ) : Prop :=
  ∃ N : Nat, ∀ n : Nat, N ≤ n → e (n + 1) ≠ e n

/-- Dropping the first step does not change "eventually no stutter steps"
(whether it is a stutter or not — the property is about the tail). -/
theorem eventuallyNoStutter_drop_left {σ : Type u} {e : Behavior σ} :
    EventuallyNoStutter e ↔ EventuallyNoStutter (e.drop 1) := by
  constructor
  · rintro ⟨N, h⟩
    refine ⟨N, ?_⟩
    intro n hn
    have h' := h (n + 1) (by omega)
    simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h'
  · rintro ⟨N, h⟩
    refine ⟨N + 1, ?_⟩
    intro n hn
    have h' := h (n - 1) (by omega)
    have hne : e ((n - 1) + 2) ≠ e ((n - 1) + 1) := by
      simpa [Cslib.ωSequence.drop] using h'
    have h1 : (n - 1) + 2 = n + 1 := by omega
    have h2 : (n - 1) + 1 = n := by omega
    simpa [h1, h2] using hne

/-- "Eventually no stutter steps" is a `Sim`-invariant. -/
theorem eventuallyNoStutter_of_sim {σ : Type u} {e f : Behavior σ} (h : Sim e f) :
    EventuallyNoStutter e ↔ EventuallyNoStutter f := by
  induction h with
  | refl e => rfl
  | stepL e f hst hrest ih =>
      rw [eventuallyNoStutter_drop_left]
      exact ih
  | stepR e f hst hrest ih =>
      rw [eventuallyNoStutter_drop_left (e := f)]
      exact ih

/-- The alternating behavior `a, b, a, b, …` — no stutter steps at all. -/
def alt {σ : Type u} (a b : σ) : Behavior σ :=
  fun n => if n % 2 = 0 then a else b

/-- The doubled behavior `a, a, b, b, a, a, …` — a stutter step in every
run, forever. -/
def doubled {σ : Type u} (a b : σ) : Behavior σ :=
  fun n => if (n / 2) % 2 = 0 then a else b

/-- `alt` is eventually (in fact always) stutter-free. -/
theorem alt_stutter_free {σ : Type u} {a b : σ} (hne : a ≠ b) :
    EventuallyNoStutter (alt a b) := by
  refine ⟨0, ?_⟩
  intro n hn
  simp [alt]
  by_cases hpar : n % 2 = 0
  · have h1 : (n + 1) % 2 ≠ 0 := by omega
    simp [hpar, h1]
    exact hne.symm
  · have h0 : (n + 1) % 2 = 0 := by omega
    simp [hpar, h0]
    exact hne

/-- `doubled` never becomes stutter-free: every run has a stutter at its
second position, so some odd position is a stutter no matter how far out
one looks. -/
theorem not_eventuallyNoStutter_doubled {σ : Type u} {a b : σ} :
    ¬ EventuallyNoStutter (doubled a b) := by
  rintro ⟨N, h⟩
  let k := N + 1
  have h1 : doubled a b (2 * k + 1) = doubled a b (2 * k) := by
    have hq1 : (2 * k + 1) / 2 = k := by omega
    have hq2 : (2 * k) / 2 = k := by omega
    change (if (2 * k + 1) / 2 % 2 = 0 then a else b) =
      (if (2 * k) / 2 % 2 = 0 then a else b)
    rw [hq1, hq2]
  have hgt : N ≤ 2 * k := by omega
  have hne' := h (2 * k) hgt
  exact hne' h1

namespace SimFull

/-- The next change of `doubled` at an even position: the value flips at
`2k + 1` (from a to b or back), so the next block starts at `2k + 2`. -/
theorem nextBlock_doubled_even {σ : Type u} {a b : σ} (hne : a ≠ b) (k : Nat) :
    nextBlock (doubled a b) (2 * k) = 2 * k + 2 := by
  unfold nextBlock
  have hch : ∃ m : Nat, 2 * k ≤ m ∧ (doubled a b) (m + 1) ≠ (doubled a b) m := by
    refine ⟨2 * k + 1, ⟨by omega, ?_⟩⟩
    simp [doubled]
    have hq1 : (2 * k + 2) / 2 = k + 1 := by omega
    have hq2 : (2 * k + 1) / 2 = k := by omega
    by_cases hk : k % 2 = 0
    · have hk1 : (k + 1) % 2 ≠ 0 := by omega
      simp [hq1, hq2, hk, hk1]
      exact hne.symm
    · have hk1 : (k + 1) % 2 = 0 := by omega
      simp [hq1, hq2, hk, hk1]
      exact hne
  rw [dif_pos hch]
  -- the first change is at `2k + 1` itself: minimality on the witness, and
  -- `2k` is not a change (it is a stutter), so the find is exactly `2k + 1`
  apply le_antisymm
  · have hw1 : 2 * k ≤ 2 * k + 1 := by omega
    have hw2 : (doubled a b) (2 * k + 2) ≠ (doubled a b) (2 * k + 1) := by
      have hq1 : (2 * k + 2) / 2 = k + 1 := by omega
      have hq2 : (2 * k + 1) / 2 = k := by omega
      change (if (2 * k + 2) / 2 % 2 = 0 then a else b) ≠
        (if (2 * k + 1) / 2 % 2 = 0 then a else b)
      rw [hq1, hq2]
      by_cases hk : k % 2 = 0
      · have hk1 : (k + 1) % 2 ≠ 0 := by omega
        simp [hk, hk1]
        exact hne.symm
      · have hk1 : (k + 1) % 2 = 0 := by omega
        simp [hk, hk1]
        exact hne
    exact Nat.succ_le_succ (Nat.find_min' hch (m := 2 * k + 1) ⟨hw1, hw2⟩)
  · by_contra hgt
    have hf := Nat.find_spec (p := fun m => 2 * k ≤ m ∧
        (doubled a b) (m + 1) ≠ (doubled a b) m) hch
    have hfeq : Nat.find (p := fun m => 2 * k ≤ m ∧
        (doubled a b) (m + 1) ≠ (doubled a b) m) hch = 2 * k := by
      apply le_antisymm
      · have hle : Nat.find (p := fun m => 2 * k ≤ m ∧
          (doubled a b) (m + 1) ≠ (doubled a b) m) hch ≤ 2 * k := by omega
        exact hle
      · exact hf.1
    have hstut : (doubled a b) (2 * k + 1) = (doubled a b) (2 * k) := by
      have hq1 : (2 * k + 1) / 2 = k := by omega
      have hq2 : (2 * k) / 2 = k := by omega
      change (if (2 * k + 1) / 2 % 2 = 0 then a else b) =
        (if (2 * k) / 2 % 2 = 0 then a else b)
      rw [hq1, hq2]
    exact hf.2 (by simpa [hfeq] using hstut)

/-- The block starts of `doubled` are the even positions. -/
theorem BlockStart_doubled {σ : Type u} {a b : σ} (hne : a ≠ b) (n : Nat) :
    BlockStart (doubled a b) n = 2 * n := by
  induction n with
  | zero => simp [BlockStart]
  | succ n ih =>
      rw [BlockStart, ih]
      have hnext := nextBlock_doubled_even hne n
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext

/-- The next change of `alt` at any position: every step changes value. -/
theorem nextBlock_alt {σ : Type u} {a b : σ} (hne : a ≠ b) (n : Nat) :
    nextBlock (alt a b) n = n + 1 := by
  unfold nextBlock
  have hch : ∃ m : Nat, n ≤ m ∧ (alt a b) (m + 1) ≠ (alt a b) m := by
    refine ⟨n, ⟨le_rfl, ?_⟩⟩
    simp [alt]
    by_cases hpar : n % 2 = 0
    · have h1 : (n + 1) % 2 ≠ 0 := by omega
      simp [hpar, h1]
      exact hne.symm
    · have h0 : (n + 1) % 2 = 0 := by omega
      simp [hpar, h0]
      exact hne
  rw [dif_pos hch]
  -- the first change is at `n` itself: `n` is a witness, so the find is
  -- at most `n`, and `n ≤ find` by the search range
  apply le_antisymm
  · have hw : (alt a b) (n + 1) ≠ (alt a b) n := by
      change (if (n + 1) % 2 = 0 then a else b) ≠ (if n % 2 = 0 then a else b)
      by_cases hpar : n % 2 = 0
      · have h1 : (n + 1) % 2 ≠ 0 := by omega
        simp [hpar, h1]
        exact hne.symm
      · have h0 : (n + 1) % 2 = 0 := by omega
        simp [hpar, h0]
        exact hne
    exact Nat.succ_le_succ (Nat.find_min' hch (m := n) ⟨le_rfl, hw⟩)
  · have hf := (Nat.find_spec (p := fun m => n ≤ m ∧ (alt a b) (m + 1) ≠ (alt a b) m) hch).1
    exact Nat.succ_le_succ hf

/-- The block starts of `alt` are all positions. -/
theorem BlockStart_alt {σ : Type u} {a b : σ} (hne : a ≠ b) (n : Nat) :
    BlockStart (alt a b) n = n := by
  induction n with
  | zero => simp [BlockStart]
  | succ n ih =>
      rw [BlockStart, ih]
      exact nextBlock_alt hne n

/-- `doubled` and `alt` compress to the same alternating sequence: `SimFull`
identifies them even though `doubled` stutters in every run. -/
theorem simFull_doubled_alt {σ : Type u} {a b : σ} (hne : a ≠ b) :
    SimFull (doubled a b) (alt a b) := by
  unfold SimFull
  ext n
  have hb1 : BlockStart (doubled a b) n = 2 * n := BlockStart_doubled hne n
  have hb2 : BlockStart (alt a b) n = n := BlockStart_alt hne n
  have hq : (2 * n) / 2 = n := by omega
  simp [Compress, hb1, hb2]
  simp [alt, doubled, hq]

/-- `Sim` does not identify them: `alt` is eventually stutter-free, `doubled`
is not, and that property is `Sim`-invariant — the difference is exactly the
infinitely many stutter steps. -/
theorem not_sim_doubled_alt {σ : Type u} {a b : σ} (hne : a ≠ b) :
    ¬ Sim (doubled a b) (alt a b) := by
  intro h
  have hP : EventuallyNoStutter (doubled a b) ↔ EventuallyNoStutter (alt a b) :=
    eventuallyNoStutter_of_sim h
  have h1 : EventuallyNoStutter (alt a b) := alt_stutter_free hne
  have h2 : ¬ EventuallyNoStutter (doubled a b) := not_eventuallyNoStutter_doubled
  exact h2 (hP.2 h1)

/-- **Characterization of the difference**: `SimFull` is the closure of
`Sim` under infinitely many stutter steps — every `Sim`-equivalence is a
`SimFull`-equivalence (`Sim.simFull`), and there are `SimFull`-equivalent
behaviors that `Sim` does not identify (the infinite-stuttering `doubled`
vs the stutter-free `alt`). -/
theorem simFull_not_sim {σ : Type u} {a b : σ} (hne : a ≠ b) :
    SimFull (doubled a b) (alt a b) ∧ ¬ Sim (doubled a b) (alt a b) :=
  ⟨simFull_doubled_alt hne, not_sim_doubled_alt hne⟩

end SimFull

end Tla
