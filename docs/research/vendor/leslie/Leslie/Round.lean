import Leslie.Refinement

/-! ## Round-Based Distributed Algorithms (Heard-Of Model)

    This file defines a framework for specifying and verifying round-based
    distributed algorithms using the Heard-Of (HO) model of Charron-Bost
    and Schiper.

    In the HO model, computation proceeds in synchronous rounds. Each round
    consists of three phases: send, receive, and state update. A round is
    "communication-closed": messages sent in round r are either delivered in
    round r or lost forever. The fault model is captured entirely by
    Heard-Of sets, which specify which messages each process receives.

    This file defines:
    - `RoundAlg`: a round-based distributed algorithm
    - `RoundState`: global state (round number + local states)
    - `HOCollection`: heard-of sets for a round
    - `CommPred`: communication predicate (constraint on HO sets)
    - `RoundSpec`: algorithm + communication predicate
    - `RoundSpec.toSpec`: conversion to a Leslie `Spec`
    - Proof rules: round invariant, process-local invariant, round refinement
    - Common communication predicates (reliable, lossy, self-delivery)
-/

open Classical

namespace TLA

/-! ### Heard-Of Collections and Communication Predicates -/

/-- A heard-of collection for one round: `ho p q = true` means process `p`
    received the message from process `q` in this round. Using `Bool` rather
    than `Prop` keeps definitions computable. -/
abbrev HOCollection (P : Type) := P → P → Bool

/-- Communication predicate: a constraint on which HO collections are valid
    in a given round. This captures the fault model. -/
def CommPred (P : Type) := Nat → HOCollection P → Prop

/-! ### Round-Based Algorithm -/

/-- A round-based distributed algorithm in the Heard-Of model.
    - `P` : process type
    - `S` : local state type
    - `M` : message type

    Each round, every process broadcasts a message (determined by `send`),
    receives a subset of messages (determined by the HO set), and updates
    its local state (determined by `update`). -/
structure RoundAlg (P : Type) (S : Type) (M : Type) where
  /-- Initial local state predicate for each process. -/
  init : P → S → Prop
  /-- The message that process `p` broadcasts given its local state.
      In the standard HO model, a process sends the same message to everyone. -/
  send : P → S → M
  /-- How process `p` updates its state given received messages.
      `msgs : P → Option M` maps each potential sender to the message received
      (`some m` if heard, `none` if not heard from that sender). -/
  update : P → S → (P → Option M) → S

/-! ### Global State -/

/-- Global state of a round-based system: a round counter and the
    local state of each process. -/
structure RoundState (P : Type) (S : Type) where
  /-- Current round number (0 = initial, before any round has executed). -/
  round : Nat
  /-- Local state of each process. -/
  locals : P → S

/-! ### Message Delivery -/

/-- The messages delivered to process `p` in a round, filtered by the HO set.
    `delivered alg s ho p q` is `some m` if `p` heard from `q` (where `m` is
    the message `q` broadcast), and `none` otherwise. -/
def delivered (alg : RoundAlg P S M) (s : RoundState P S)
    (ho : HOCollection P) (p : P) : P → Option M :=
  fun q => if ho p q then some (alg.send q (s.locals q)) else none

@[simp] theorem delivered_heard {alg : RoundAlg P S M} {s : RoundState P S}
    {ho : HOCollection P} {p q : P} (h : ho p q = true) :
    delivered alg s ho p q = some (alg.send q (s.locals q)) := by
  simp [delivered, h]

@[simp] theorem delivered_not_heard {alg : RoundAlg P S M} {s : RoundState P S}
    {ho : HOCollection P} {p q : P} (h : ho p q = false) :
    delivered alg s ho p q = none := by
  simp [delivered, h]

/-! ### Round Transition -/

/-- One round step: all processes transition simultaneously.
    The round counter increments and each process updates its local state
    based on the messages it received (as determined by the HO collection). -/
def round_step (alg : RoundAlg P S M) (ho : HOCollection P)
    (s s' : RoundState P S) : Prop :=
  s'.round = s.round + 1 ∧
  ∀ p, s'.locals p = alg.update p (s.locals p) (delivered alg s ho p)

/-! ### Round Specification -/

/-- A complete round-based specification: an algorithm together with a
    communication predicate that constrains the environment's choice of
    HO collections. -/
structure RoundSpec (P : Type) (S : Type) (M : Type) where
  alg : RoundAlg P S M
  comm : CommPred P

/-- Convert a round-based specification to a Leslie `Spec`.
    The HO collection is existentially quantified in the transition relation:
    the environment nondeterministically chooses it, subject to the
    communication predicate. -/
def RoundSpec.toSpec (rs : RoundSpec P S M) : Spec (RoundState P S) where
  init := fun s => s.round = 0 ∧ ∀ p, rs.alg.init p (s.locals p)
  next := fun s s' => ∃ ho, rs.comm s.round ho ∧ round_step rs.alg ho s s'

/-! ### Proof Rules -/

/-- **Round Invariant Rule**: if `inv` holds initially and is preserved by
    any valid round step (for any HO collection satisfying the communication
    predicate), then `inv` holds at all times.

    This is the main proof rule for round-based algorithms. It reduces
    temporal reasoning to single-round, non-temporal reasoning. -/
theorem round_invariant {P S M : Type} (rs : RoundSpec P S M)
    (inv : RoundState P S → Prop)
    (hinit : ∀ s, rs.toSpec.init s → inv s)
    (hstep : ∀ s ho, inv s → rs.comm s.round ho →
             ∀ s', round_step rs.alg ho s s' → inv s') :
    pred_implies rs.toSpec.safety [tlafml| □ ⌜inv⌝] := by
  apply init_invariant hinit
  intro s s' ⟨ho, hcomm, hround⟩ hinv
  exact hstep s ho hinv hcomm s' hround

/-- **Process-Local Invariant Rule**: an invariant that can be checked
    per-process, independently of what messages are received.

    If `inv p s` holds for each process `p` in its initial state, and
    `update` preserves the invariant regardless of what messages arrive,
    then the invariant holds globally at all times. -/
theorem process_local_invariant {P S M : Type} (rs : RoundSpec P S M)
    (local_inv : P → S → Prop)
    (hinit : ∀ p s, rs.alg.init p s → local_inv p s)
    (hstep : ∀ p s msgs, local_inv p s → local_inv p (rs.alg.update p s msgs)) :
    pred_implies rs.toSpec.safety
      [tlafml| □ ⌜fun (s : RoundState P S) => ∀ p, local_inv p (s.locals p)⌝] := by
  apply init_invariant
  · intro s ⟨_, hinit_all⟩ p
    exact hinit p _ (hinit_all p)
  · intro s s' ⟨ho, _, _, hlocals⟩ hinv p
    rw [hlocals p]
    exact hstep p (s.locals p) _ (hinv p)

/-- **Round Refinement Rule**: a round-based spec refines an abstract spec
    via a state mapping, allowing stuttering. -/
theorem round_refinement {P S M : Type} {τ : Type}
    (rs : RoundSpec P S M) (abstract : Spec τ)
    (f : RoundState P S → τ)
    (hinit : ∀ s, rs.toSpec.init s → abstract.init (f s))
    (hstep : ∀ s ho, rs.comm s.round ho →
             ∀ s', round_step rs.alg ho s s' →
             abstract.next (f s) (f s') ∨ f s = f s') :
    refines_via f rs.toSpec.safety abstract.safety_stutter := by
  apply refinement_mapping_stutter rs.toSpec abstract f hinit
  intro s s' ⟨ho, hcomm, hround⟩
  exact hstep s ho hcomm s' hround

/-- **Round Refinement with Invariant**: refinement under an inductive
    invariant on the round-based state. -/
theorem round_refinement_with_invariant {P S M : Type} {τ : Type}
    (rs : RoundSpec P S M) (abstract : Spec τ)
    (f : RoundState P S → τ) (inv : RoundState P S → Prop)
    (hinv_init : ∀ s, rs.toSpec.init s → inv s)
    (hinv_step : ∀ s ho, inv s → rs.comm s.round ho →
                 ∀ s', round_step rs.alg ho s s' → inv s')
    (hinit : ∀ s, rs.toSpec.init s → abstract.init (f s))
    (hstep : ∀ s ho, inv s → rs.comm s.round ho →
             ∀ s', round_step rs.alg ho s s' →
             abstract.next (f s) (f s') ∨ f s = f s') :
    refines_via f rs.toSpec.safety abstract.safety_stutter := by
  apply refinement_mapping_stutter_with_invariant
    rs.toSpec abstract f inv
  · exact hinv_init
  · intro s s' hinv ⟨ho, hcomm, hround⟩
    exact hinv_step s ho hinv hcomm s' hround
  · exact hinit
  · intro s s' hinv ⟨ho, hcomm, hround⟩
    exact hstep s ho hinv hcomm s' hround

/-! ### Common Communication Predicates -/

/-- Reliable communication: all messages are delivered in every round. -/
def comm_reliable (P : Type) : CommPred P :=
  fun _ ho => ∀ p q, ho p q = true

/-- Lossy communication: no constraints on delivery (any HO set is valid). -/
def comm_lossy (P : Type) : CommPred P :=
  fun _ _ => True

/-- Self-delivery: every process always hears from itself. -/
def comm_self_delivery (P : Type) : CommPred P :=
  fun _ ho => ∀ p, ho p p = true

/-! ### Utility: disjoint filter bound -/

/-- For disjoint predicates on a list, the combined filter lengths don't
    exceed the original list length. Useful for quorum intersection arguments. -/
theorem filter_disjoint_length_le {α : Type} (p₁ p₂ : α → Bool) (l : List α)
    (h_disj : ∀ x, ¬(p₁ x = true ∧ p₂ x = true)) :
    (l.filter p₁).length + (l.filter p₂).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hx := h_disj x
    simp only [List.filter, List.length]
    by_cases h1 : p₁ x = true <;> by_cases h2 : p₂ x = true
    · exact absurd ⟨h1, h2⟩ hx
    · simp [h1, h2] ; omega
    · simp [h1, h2] ; omega
    · simp [h1, h2] ; omega

/-- Filtering a `filterMap` result for value `b` gives at most as many hits
    as filtering the original list for elements that map to `some b`. -/
theorem filterMap_filter_count_le {α β : Type} [BEq β] [LawfulBEq β]
    (l : List α) (f : α → Option β) (b : β)
    (pred : α → Bool)
    (h : ∀ a, f a = some b → pred a = true) :
    ((l.filterMap f).filter (· == b)).length ≤ (l.filter pred).length := by
  induction l with
  | nil => simp
  | cons a as ih =>
    cases hf : f a with
    | none =>
      simp only [List.filterMap_cons, hf]
      calc ((as.filterMap f).filter (· == b)).length
        _ ≤ (as.filter pred).length := ih
        _ ≤ ((a :: as).filter pred).length := by
            simp only [List.filter] ; split <;> simp_all
    | some val =>
      simp only [List.filterMap_cons, hf]
      by_cases hb : (val == b) = true
      · have hval : val = b := beq_iff_eq.mp hb
        have hp := h a (show f a = some b by rw [hf, hval])
        simp only [List.filter, hb, hp, List.length]
        exact Nat.succ_le_succ ih
      · have hbf : (val == b) = false := by revert hb ; cases (val == b) <;> simp
        simp only [List.filter, hbf]
        calc ((as.filterMap f).filter (· == b)).length
          _ ≤ (as.filter pred).length := ih
          _ ≤ ((a :: as).filter pred).length := by
              simp only [List.filter] ; split <;> simp_all

/-- Monotonicity of filter: if `p₁` implies `p₂` on every element,
    then the filter by `p₁` is no longer than the filter by `p₂`. -/
theorem filter_length_mono {α : Type} (l : List α) (p₁ p₂ : α → Bool)
    (h : ∀ a, p₁ a = true → p₂ a = true) :
    (l.filter p₁).length ≤ (l.filter p₂).length := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.filter]
    by_cases h1 : p₁ a = true
    · simp [h1, h a h1] ; omega
    · have h1f : p₁ a = false := by revert h1 ; cases p₁ a <;> simp
      simp only [h1f]
      by_cases h2 : p₂ a = true
      · simp [h2] ; omega
      · have h2f : p₂ a = false := by revert h2 ; cases p₂ a <;> simp
        simp [h2f]; exact ih

end TLA
