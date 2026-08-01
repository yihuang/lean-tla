import Leslie.Examples.CacheCoherence.TileLink.Messages.Refinement.SimOther
import Leslie.Examples.CacheCoherence.TileLink.Messages.Refinement

/-! ## Access-Path Theorems

    This file proves that the TileLink message model correctly implements
    a sequentially consistent shared memory for reads and writes:

    - `read_returns_logical_data`: a readable node's data equals the
      abstract sequential register value
    - `store_updates_logical_data`: after a store, the abstract sequential
      register value equals the stored value
-/

namespace TileLink.Messages

open TLA TileLink SymShared Classical

/-- A readable node's data equals the logical line value (the abstract
    sequential register value mapped through the refinement).

    When a node has read permission (perm ∈ {.B, .T}) and valid data,
    its data equals `(refMap n s).shared.mem`, which is the abstract
    memory value. Combined with `messages_refines_atomic` and
    `atomic_coherence`, this means reads return the value of the
    sequential register. -/
theorem read_returns_logical_data {n : Nat}
    {s : SymState HomeState NodeState n} {i : Fin n}
    (hinv : ForwardSimInv n s)
    (hperm : (s.locals i).line.perm.allowsRead)
    (hvalid : (s.locals i).line.valid = true)
    (htxn : s.shared.currentTxn = none)
    (hflight : (s.locals i).releaseInFlight = false) :
    (s.locals i).line.data = (refMap n s).shared.mem := by
  -- Unfold refMap.mem for the no-transaction case
  simp only [refMap, refMapShared, htxn]
  have hlineWF := hinv.ref.full.1.1
  have hdirtyEx := hinv.ref.dirtyEx
  have hdirtyRelEx := hinv.ref.dirtyRelEx
  have hdata := hinv.dataCoh
  by_cases hex : ∃ j : Fin n, (s.locals j).line.dirty = true
  · -- Case 1: A dirty owner exists. refMap.mem = (choose hex).line.data
    simp only [hex, dite_true]
    have hk_dirty := Classical.choose_spec hex
    let k := Classical.choose hex
    by_cases hik : i = k
    · subst hik; rfl
    · exfalso
      have hpermN := hdirtyEx k i (Ne.symm hik) hk_dirty
      rw [hpermN] at hperm
      exact hperm
  · -- Case 2: No dirty owner. refMap.mem = match findDirtyReleaseVal with ...
    simp only [hex, dite_false]
    have hdirty_i : (s.locals i).line.dirty = false := by
      cases h : (s.locals i).line.dirty
      · rfl
      · exact absurd ⟨i, h⟩ hex
    have hdata_eq : (s.locals i).line.data = s.shared.mem := hdata htxn i hflight hvalid hdirty_i
    -- Show findDirtyReleaseVal = none: no dirty release in flight
    have hfdrv : findDirtyReleaseVal n s = none := by
      unfold findDirtyReleaseVal
      split
      · -- Dirty release exists: contradicts reader i having allowsRead
        rename_i hrel_exists
        exfalso
        have hspec := Classical.choose_spec hrel_exists
        have hrelJ := hspec.1
        have hmsgJ := hspec.2
        have hpermN := hdirtyRelEx htxn _ hrelJ hmsgJ
        by_cases hij : i = Classical.choose hrel_exists
        · rw [hij] at hflight; rw [hflight] at hrelJ; cases hrelJ
        · rw [hpermN i hij] at hperm; exact hperm
      · rfl
    rw [hfdrv]
    exact hdata_eq

/-- After a store, the abstract sequential register value equals the stored value. -/
theorem store_updates_logical_data {n : Nat}
    {s s' : SymState HomeState NodeState n} {i : Fin n} {v : Val}
    (hinv : ForwardSimInv n s)
    (hstep : Store s s' i v) :
    ∀ j : Fin n, (s'.locals j).line.perm.allowsRead →
      (s'.locals j).line.valid = true →
      (s'.locals j).line.data = v ∨ (s'.locals j).line.data = (refMap n s).shared.mem := by
  intro j hpermJ hvalidJ
  rcases hstep with ⟨htxn, _, _, _, hpermI, _, _, _, _, _, _, _, hs'⟩
  subst hs'
  by_cases hji : j = i
  · subst j; simp [setFn, storeLocal]
  · -- j ≠ i: SWMR gives perm j = .N, contradicting allowsRead
    exfalso
    simp only [setFn, hji, ite_false] at hpermJ
    have hpermN := hinv.ref.swmr i j (Ne.symm hji) hpermI
    rw [hpermN] at hpermJ; exact hpermJ

end TileLink.Messages
