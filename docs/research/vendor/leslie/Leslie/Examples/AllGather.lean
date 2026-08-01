import Leslie.Round

/-! ## All-Gather: A Round-Based Example

    An all-gather protocol for `n` processes (`Fin n`). Each process starts
    knowing only itself. Every round, each process broadcasts its knowledge
    bitmap and merges all received bitmaps into its own.

    Under reliable communication, after one round every process knows
    about every other process.

    This example demonstrates:
    - A round-based algorithm with general `n` processes
    - Using `round_invariant` with a strengthened invariant
    - How process-local properties (self-knowledge) support global safety
-/

open TLA

namespace AllGather

variable (n : Nat)

/-! ### Algorithm definition -/

/-- All-Gather algorithm for `n` processes.
    - State: bitmap `Fin n → Bool` of known processes.
    - Message: the same bitmap.
    - Init: process `p` knows only itself.
    - Send: broadcast the bitmap.
    - Update: OR own bitmap with all received bitmaps. -/
def ag_alg : RoundAlg (Fin n) (Fin n → Bool) (Fin n → Bool) where
  init := fun p s => ∀ q, s q = decide (q = p)
  send := fun _p s => s
  update := fun _p s msgs => fun q =>
    s q || (List.finRange n).any fun r =>
      match msgs r with
      | some m => m q
      | none => false

/-- Specification with reliable communication. -/
def ag_spec : RoundSpec (Fin n) (Fin n → Bool) (Fin n → Bool) where
  alg := ag_alg n
  comm := comm_reliable (Fin n)

/-! ### Completeness -/

/-- Combined invariant: self-knowledge and completeness. Self-knowledge
    is needed in the inductive step to establish completeness: under
    reliable communication, process `p` receives `q`'s bitmap, which
    has `q`'s own bit set. -/
def ag_inv (s : RoundState (Fin n) (Fin n → Bool)) : Prop :=
  (∀ p, s.locals p p = true) ∧
  (s.round ≥ 1 → ∀ p q, s.locals p q = true)

/-- After one round with reliable communication, every process knows
    about every other process (and self-knowledge holds at all times). -/
theorem ag_completeness :
    pred_implies (ag_spec n).toSpec.safety [tlafml| □ ⌜ag_inv n⌝] := by
  apply round_invariant
  · -- Init: round = 0, self-knowledge from init predicate
    intro s ⟨hround, hinit⟩
    refine ⟨fun p => ?_, fun h => by omega⟩
    -- hinit p : ∀ q, s.locals p q = decide (q = p)
    -- specializing at q = p gives s.locals p p = decide (p = p) = true
    have := hinit p p
    simp at this
    exact this
  · -- Step: both parts of the invariant are preserved
    intro s ho ⟨hself, _⟩ hcomm s' ⟨_, hlocals⟩
    constructor
    · -- Self-knowledge: OR includes old value, which was true
      intro p
      -- Convert (ag_spec n).alg to ag_alg n (definitionally equal)
      show (s'.locals p) p = true
      rw [hlocals p]
      show (ag_alg n).update p (s.locals p) (delivered (ag_alg n) s ho p) p = true
      -- Unfold update: s.locals p p || any(...), left disjunct is true
      simp only [ag_alg, Bool.or_eq_true]
      left
      exact hself p
    · -- Completeness: reliable comm delivers q's self-knowledge to p
      intro _ p q
      show (s'.locals p) q = true
      rw [hlocals p]
      show (ag_alg n).update p (s.locals p) (delivered (ag_alg n) s ho p) q = true
      -- Unfold update: s.locals p q || any(...)
      simp only [ag_alg, Bool.or_eq_true, List.any_eq_true]
      right
      -- Witness: process q itself, whose message contains q's bit
      refine ⟨q, List.mem_finRange q, ?_⟩
      -- Under reliable comm, p receives q's bitmap
      simp only [delivered_heard (hcomm p q)]
      -- (ag_alg n).send q (s.locals q) = s.locals q by definition
      show s.locals q q = true
      exact hself q

end AllGather
