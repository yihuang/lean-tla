import Leslie.Round

/-! ## Leader Broadcast: A Round-Based Example

    A simple round-based protocol with two processes: a leader and a follower.
    Each round, every process broadcasts its current value. Upon receiving
    the leader's value, a process adopts it.

    Under reliable communication, after one round both processes hold
    the leader's initial value — i.e., they agree.

    This example demonstrates:
    - Defining a round-based algorithm using `RoundAlg`
    - Converting to a Leslie `Spec` via `RoundSpec.toSpec`
    - Proving agreement using the `round_invariant` proof rule
-/

open TLA

namespace LeaderBroadcast

/-! ### Process type -/

inductive Proc where | leader | follower
  deriving DecidableEq, Repr

/-! ### Algorithm definition -/

/-- Leader broadcast algorithm.
    - Every process broadcasts its current value.
    - Every process adopts the leader's value if heard from the leader,
      otherwise keeps its own value. -/
def lf_alg : RoundAlg Proc Nat Nat where
  init := fun _ _ => True
  send := fun _p s => s
  update := fun _p s msgs => (msgs .leader).getD s

/-- Specification with reliable communication. -/
def lf_spec : RoundSpec Proc Nat Nat where
  alg := lf_alg
  comm := comm_reliable Proc

/-! ### Agreement property -/

/-- After the first round with reliable communication, the leader and
    follower agree on the same value. -/
theorem lf_agreement :
    pred_implies lf_spec.toSpec.safety
      [tlafml| □ ⌜fun (s : RoundState Proc Nat) =>
        s.round ≥ 1 → s.locals .leader = s.locals .follower⌝] := by
  apply round_invariant
  · -- Init: round = 0, so the implication is vacuously true
    intro s ⟨hround, _⟩ hge
    omega
  · -- Step: under reliable comm, both processes adopt the leader's value
    intro s ho _hinv hcomm s' ⟨_, hlocals⟩ _
    have hL := hcomm .leader .leader
    have hF := hcomm .follower .leader
    simp only [hlocals, lf_spec, lf_alg, delivered, hL, hF, ite_true,
               Option.getD_some]

end LeaderBroadcast
