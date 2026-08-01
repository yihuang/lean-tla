import Leslie.Refinement
import Leslie.Examples.CacheCoherence.TileLink.Atomic.Theorem

namespace TileLink.Atomic

open TLA SymShared

/-! ### Sequential Refinement

    The atomic TileLink model exposes a single logical line value via
    `logicalData`. Refinement maps each reachable concrete state to that value.

    As in `MESIParam`, the abstract sequential memory safety spec is a single
    register initialized to `0`, with unconstrained next-state relation.
-/

/-- Refinement mapping from the atomic TileLink model to a logical single-line value. -/
noncomputable def ref_map (n : Nat) (s : SymState HomeState CacheLine n) : Val :=
  logicalData n s

/-- Sequential single-register memory used for the safety refinement theorem. -/
def seq_mem : Spec Val where
  init := fun v => v = 0
  next := fun _ _ => True

/-- Initial TileLink states map to the initial abstract register value. -/
theorem ref_map_init (n : Nat) (s : SymState HomeState CacheLine n)
    (hs : (tlAtomic.toSpec n).init s) : ref_map n s = 0 := by
  rcases hs with ⟨⟨hmem, _, _, _, _⟩, hlocals⟩
  have hnoDirty : ¬∃ i : Fin n, (s.locals i).dirty = true := by
    intro hdirty
    rcases hdirty with ⟨i, hiDirty⟩
    rcases hlocals i with ⟨_, _, hdirty, _⟩
    simp [hdirty] at hiDirty
  unfold ref_map logicalData
  rw [dif_neg hnoDirty, hmem]

/-- The atomic TileLink model refines a sequential one-line memory. -/
theorem atomic_coherence (n : Nat) :
    refines_via (ref_map n) (tlAtomic.toSpec n).safety seq_mem.safety := by
  apply refinement_mapping_nostutter
  · intro s hs
    exact ref_map_init n s hs
  · intro _ _ _
    trivial

end TileLink.Atomic
