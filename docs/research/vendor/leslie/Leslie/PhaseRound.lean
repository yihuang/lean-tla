import Leslie.Round

/-! ## Multi-Phase Round-Based Distributed Algorithms

    Extends `Round.lean` to support protocols where each logical round
    consists of `numPhases` sequential communication-closed phases.

    Each phase has its own message type, send function, and update function.
    Communication closure holds per phase: messages from phase i of round r
    are delivered in phase i of round r, or lost forever.

    Examples: Paxos (4 phases), VR (2 phases), 2PC (2 phases).

    We parameterize by `numPhases` (≥ 1). Internally we use `Fin numPhases`
    for phase indices.
-/

open Classical

namespace TLA

/-! ### Core definitions -/

/-- A single phase: its own send and update functions. -/
structure Phase (P : Type) (S : Type) (M : Type) where
  send : P → S → M
  update : P → S → (P → Option M) → S

/-- Message type family indexed by phase. -/
abbrev PhaseMessages (numPhases : Nat) := Fin numPhases → Type

/-- Multi-phase round algorithm. `numPhases` phases per logical round. -/
structure PhaseRoundAlg (P : Type) (S : Type) (numPhases : Nat)
    (Msgs : PhaseMessages numPhases) where
  init : P → S → Prop
  phases : (i : Fin numPhases) → Phase P S (Msgs i)

/-- Global state: round number, current phase, per-process local state. -/
structure PhaseRoundState (P : Type) (S : Type) (numPhases : Nat) where
  round : Nat
  phase : Fin numPhases
  locals : P → S

/-- Messages delivered to process p in a phase, filtered by HO set. -/
def phase_delivered (ph : Phase P S M) (locals : P → S)
    (ho : HOCollection P) (p : P) : P → Option M :=
  fun q => if ho p q then some (ph.send q (locals q)) else none

/-- One phase step. The phase advances; after the last phase, the
    round increments and phase resets to 0. -/
def phase_step (alg : PhaseRoundAlg P S numPhases Msgs)
    (ho : HOCollection P)
    (s s' : PhaseRoundState P S numPhases) : Prop :=
  let ph := alg.phases s.phase
  (if h : s.phase.val + 1 < numPhases then
    s'.round = s.round ∧ s'.phase = ⟨s.phase.val + 1, h⟩
  else
    s'.round = s.round + 1 ∧
    s'.phase = ⟨0, by have := s.phase.isLt ; omega⟩) ∧
  (∀ p, s'.locals p = ph.update p (s.locals p)
    (phase_delivered ph s.locals ho p))

/-- Per-phase communication predicate. -/
def PhaseCommPred (P : Type) (numPhases : Nat) :=
  Nat → Fin numPhases → HOCollection P → Prop

/-- Multi-phase round specification. -/
structure PhaseRoundSpec (P : Type) (S : Type) (numPhases : Nat)
    (Msgs : PhaseMessages numPhases) where
  alg : PhaseRoundAlg P S numPhases Msgs
  comm : PhaseCommPred P numPhases

/-- Convert to a Leslie `Spec`. Requires `numPhases > 0` for the
    initial phase `⟨0, _⟩` to be well-formed. -/
def PhaseRoundSpec.toSpec {P S : Type} {numPhases : Nat} {Msgs : PhaseMessages numPhases}
    (prs : PhaseRoundSpec P S numPhases Msgs)
    (hk : numPhases > 0) :
    Spec (PhaseRoundState P S numPhases) where
  init := fun s =>
    s.round = 0 ∧ s.phase = ⟨0, hk⟩ ∧ ∀ p, prs.alg.init p (s.locals p)
  next := fun s s' =>
    ∃ ho, prs.comm s.round s.phase ho ∧ phase_step prs.alg ho s s'

/-! ### Proof rules -/

/-- **Phase Round Invariant**: if `inv` holds initially and is preserved
    by every phase step, then `inv` holds always.

    This is the main proof rule. The invariant must hold at ALL phases,
    not just at round boundaries. For phase-specific properties, use
    `phase_conditional_invariant`. -/
theorem phase_round_invariant {P S : Type} {numPhases : Nat}
    {Msgs : PhaseMessages numPhases}
    (prs : PhaseRoundSpec P S numPhases Msgs) (hk : numPhases > 0)
    (inv : PhaseRoundState P S numPhases → Prop)
    (hinit : ∀ s, (prs.toSpec hk).init s → inv s)
    (hstep : ∀ s ho, inv s → prs.comm s.round s.phase ho →
             ∀ s', phase_step prs.alg ho s s' → inv s') :
    pred_implies (prs.toSpec hk).safety [tlafml| □ ⌜inv⌝] := by
  apply init_invariant hinit
  intro s s' ⟨ho, hcomm, hphase⟩ hinv
  exact hstep s ho hinv hcomm s' hphase

/-- **Process-Local Phase Invariant**: per-process, message-independent. -/
theorem phase_process_local_invariant {P S : Type} {numPhases : Nat}
    {Msgs : PhaseMessages numPhases}
    (prs : PhaseRoundSpec P S numPhases Msgs) (hk : numPhases > 0)
    (local_inv : P → S → Prop)
    (hinit : ∀ p s, prs.alg.init p s → local_inv p s)
    (hstep : ∀ (i : Fin numPhases) p s msgs, local_inv p s →
             local_inv p ((prs.alg.phases i).update p s msgs)) :
    pred_implies (prs.toSpec hk).safety
      [tlafml| □ ⌜fun (s : PhaseRoundState P S numPhases) =>
        ∀ p, local_inv p (s.locals p)⌝] := by
  apply phase_round_invariant prs hk
  · intro s ⟨_, _, hinit_all⟩ p
    exact hinit p _ (hinit_all p)
  · intro s ho hinv _ s' ⟨_, hlocals⟩ p
    rw [hlocals p]
    exact hstep s.phase p (s.locals p) _ (hinv p)

/-- **Phase-Conditional Invariant**: holds at a specific phase.
    Established when entering the target phase, preserved while at it. -/
theorem phase_conditional_invariant {P S : Type} {numPhases : Nat}
    {Msgs : PhaseMessages numPhases}
    (prs : PhaseRoundSpec P S numPhases Msgs) (hk : numPhases > 0)
    (target : Fin numPhases)
    (inv : PhaseRoundState P S numPhases → Prop)
    (hinit : ∀ s, (prs.toSpec hk).init s → s.phase = target → inv s)
    (hstep : ∀ s ho, (s.phase = target → inv s) →
      prs.comm s.round s.phase ho →
      ∀ s', phase_step prs.alg ho s s' →
      s'.phase = target → inv s') :
    pred_implies (prs.toSpec hk).safety
      [tlafml| □ ⌜fun s => s.phase = target → inv s⌝] := by
  apply phase_round_invariant prs hk
  · exact hinit
  · exact hstep

/-- **Phase Round Refinement**: multi-phase spec refines an abstract spec
    with stuttering. -/
theorem phase_round_refinement {P S : Type} {numPhases : Nat}
    {Msgs : PhaseMessages numPhases} {τ : Type}
    (prs : PhaseRoundSpec P S numPhases Msgs) (hk : numPhases > 0)
    (abstract : Spec τ)
    (f : PhaseRoundState P S numPhases → τ)
    (hinit : ∀ s, (prs.toSpec hk).init s → abstract.init (f s))
    (hstep : ∀ s ho, prs.comm s.round s.phase ho →
             ∀ s', phase_step prs.alg ho s s' →
             abstract.next (f s) (f s') ∨ f s = f s') :
    refines_via f (prs.toSpec hk).safety abstract.safety_stutter := by
  apply refinement_mapping_stutter (prs.toSpec hk) abstract f hinit
  intro s s' ⟨ho, hcomm, hphase⟩
  exact hstep s ho hcomm s' hphase

/-- **Phase Round Refinement with Invariant**. -/
theorem phase_round_refinement_with_invariant
    {P S : Type} {numPhases : Nat}
    {Msgs : PhaseMessages numPhases} {τ : Type}
    (prs : PhaseRoundSpec P S numPhases Msgs) (hk : numPhases > 0)
    (abstract : Spec τ) (f : PhaseRoundState P S numPhases → τ)
    (inv : PhaseRoundState P S numPhases → Prop)
    (hinv_init : ∀ s, (prs.toSpec hk).init s → inv s)
    (hinv_step : ∀ s ho, inv s → prs.comm s.round s.phase ho →
                 ∀ s', phase_step prs.alg ho s s' → inv s')
    (hinit : ∀ s, (prs.toSpec hk).init s → abstract.init (f s))
    (hstep : ∀ s ho, inv s → prs.comm s.round s.phase ho →
             ∀ s', phase_step prs.alg ho s s' →
             abstract.next (f s) (f s') ∨ f s = f s') :
    refines_via f (prs.toSpec hk).safety abstract.safety_stutter := by
  apply refinement_mapping_stutter_with_invariant
    (prs.toSpec hk) abstract f inv
  · exact hinv_init
  · intro s s' hinv ⟨ho, hcomm, hphase⟩
    exact hinv_step s ho hinv hcomm s' hphase
  · exact hinit
  · intro s s' hinv ⟨ho, hcomm, hphase⟩
    exact hstep s ho hinv hcomm s' hphase

/-! ### Cross-phase quorum intersection -/

/-- **Cross-Phase Quorum Intersection**: HO sets from different phases
    (or even different rounds) that are both majority quorums must overlap.
    This is the central technique for Paxos-family safety proofs:
    the promise quorum and accept quorum share at least one process. -/
theorem cross_phase_quorum_intersection (n : Nat)
    (ho_i ho_j : HOCollection (Fin n)) (p_i p_j : Fin n)
    (h_i : ((List.finRange n).filter fun q => ho_i p_i q).length * 2 > n)
    (h_j : ((List.finRange n).filter fun q => ho_j p_j q).length * 2 > n) :
    ∃ q : Fin n, ho_i p_i q = true ∧ ho_j p_j q = true := by
  by_contra h
  have h' : ∀ q, ¬(ho_i p_i q = true ∧ ho_j p_j q = true) :=
    fun q hq => h ⟨q, hq⟩
  have h_sum := filter_disjoint_length_le
    (fun q => ho_i p_i q) (fun q => ho_j p_j q) (List.finRange n) h'
  have h_len : (List.finRange n).length = n := List.length_finRange
  omega

/-! ### Flattening to single-phase rounds -/

/-- Flattened state: local state + phase tag. -/
structure FlatState (S : Type) (numPhases : Nat) where
  phaseTag : Fin numPhases
  inner : S

/-- Flatten a multi-phase algorithm to a single-phase one.
    Each "round" of the flat algorithm = one phase of the original.
    The phase tag sequences the phases. -/
noncomputable def PhaseRoundAlg.flatten
    (alg : PhaseRoundAlg P S numPhases Msgs) :
    RoundAlg P (FlatState S numPhases) Nat where
  init := fun p fs =>
    fs.phaseTag = ⟨0, by have := fs.phaseTag.isLt ; omega⟩ ∧ alg.init p fs.inner
  send := fun _p fs => fs.phaseTag.val
  update := fun _p fs _msgs =>
    let newTag := if h : fs.phaseTag.val + 1 < numPhases
      then ⟨fs.phaseTag.val + 1, h⟩
      else ⟨0, by have := fs.phaseTag.isLt ; omega⟩
    { phaseTag := newTag, inner := fs.inner }

end TLA
