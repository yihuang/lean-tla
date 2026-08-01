import Leslie.Round

/-! ## Flood Min: A Round-Based Consensus Example

    A simple flooding protocol for two processes. Each round, every process
    broadcasts its current value (a natural number). Upon receiving messages,
    each process updates its value to the minimum of its own value and all
    received values.

    Under reliable communication, after one round both processes hold
    `min v₁ v₂` (the global minimum of the initial values), so they agree.

    This example demonstrates:
    - A round-based algorithm with a nontrivial update function
    - Proving agreement using the `round_invariant` rule
    - Monotonicity as a property of the update function
    - A refinement to an abstract consensus specification
-/

open TLA

namespace FloodMin

/-! ### Algorithm definition (2 processes, indexed by Bool) -/

/-- Flood-min algorithm for two processes.
    - Every process broadcasts its current value.
    - Every process updates to the min of its own value and all received values.
      For messages not received, the process's own value is used as the default. -/
def flood_min_alg : RoundAlg Bool Nat Nat where
  init := fun _ _ => True
  send := fun _p s => s
  update := fun _p s msgs =>
    let v_true := (msgs true).getD s
    let v_false := (msgs false).getD s
    min s (min v_true v_false)

/-- Specification with reliable communication. -/
def fm_spec : RoundSpec Bool Nat Nat where
  alg := flood_min_alg
  comm := comm_reliable Bool

/-! ### Agreement property -/

/-- After the first round with reliable communication, both processes
    hold the same value. -/
theorem flood_min_agreement :
    pred_implies fm_spec.toSpec.safety
      [tlafml| □ ⌜fun (s : RoundState Bool Nat) =>
        s.round ≥ 1 → s.locals true = s.locals false⌝] := by
  apply round_invariant
  · -- Init: round = 0, vacuously true
    intro s ⟨hround, _⟩ hge
    omega
  · -- Step: under reliable comm, both compute the same min
    intro s ho _hinv hcomm s' ⟨_, hlocals⟩ _
    have htt := hcomm true true
    have htf := hcomm true false
    have hft := hcomm false true
    have hff := hcomm false false
    simp only [hlocals, fm_spec, flood_min_alg, delivered, htt, htf, hft, hff,
               ite_true, Option.getD_some]
    omega

/-! ### Monotonicity: values never increase -/

/-- Under any communication (even lossy), each process's value never
    increases across rounds. Stated as: the value after update is ≤ the
    value before. This is a consequence of taking `min`. -/
theorem update_le_self (p : Bool) (s : Nat) (msgs : Bool → Option Nat) :
    flood_min_alg.update p s msgs ≤ s := by
  simp [flood_min_alg]
  omega

/-! ### Refinement to abstract consensus spec -/

/-- Abstract consensus specification: each process has a value, and once
    all values are equal they remain equal. -/
def consensus_spec : Spec (Bool → Nat) where
  init := fun _ => True
  next := fun vs vs' =>
    (∀ p, vs' p ≤ vs p) ∧                     -- values only decrease
    ((vs true = vs false) → vs' true = vs' false)  -- agreement is stable

/-- Refinement mapping: extract the local states. -/
def ref_map (s : RoundState Bool Nat) : Bool → Nat := s.locals

theorem flood_min_refines_consensus :
    refines_via ref_map fm_spec.toSpec.safety consensus_spec.safety_stutter := by
  apply round_refinement fm_spec consensus_spec ref_map
  · -- init preserved
    intro s _
    simp [consensus_spec]
  · -- step simulation
    intro s ho hcomm s' ⟨_, hlocals⟩
    left
    simp only [consensus_spec, ref_map]
    refine ⟨fun p => ?_, fun heq => ?_⟩
    · -- values only decrease
      rw [hlocals p]
      exact update_le_self p (s.locals p) (delivered fm_spec.alg s ho p)
    · -- agreement is stable
      simp only [hlocals, fm_spec, flood_min_alg, delivered, heq]
      -- All values are s.locals false; the if-conditions don't matter
      have hsimp : ∀ (c : Bool),
          (if c = true then some (s.locals false) else none).getD (s.locals false)
            = s.locals false := by
        intro c ; cases c <;> simp
      simp [hsimp]

end FloodMin
