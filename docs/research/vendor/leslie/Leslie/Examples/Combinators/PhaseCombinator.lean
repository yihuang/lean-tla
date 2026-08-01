import Leslie.Examples.Combinators.QuorumSystem
import Leslie.PhaseRound

/-! ## Phase Combinators with Composition Theorems

    Composable protocol phases for multi-phase distributed algorithms.
    The key result is `seq_preserves`: if phase A preserves invariant `inv_A`
    and phase B preserves `inv_B` (assuming `inv_A`), then their sequential
    composition preserves `inv_A ∧ inv_B`.

    This file also demonstrates the pattern with a two-phase consensus protocol
    where agreement follows from composing per-phase safety properties.

    ### Structure

    1. `CPhase` — a single protocol phase (send + update)
    2. `CPhase.step` — execute a phase given an HO collection
    3. `CPhase.preserves` — a phase preserves an invariant under a comm predicate
    4. `CPhase.seq` — sequential composition of two phases
    5. `seq_preserves` — the main composition theorem
    6. `cross_phase_quorum_intersection` — quorum intersection across phases
    7. Two-phase consensus demo with composed agreement proof
-/

open TLA TLA.Combinator

namespace TLA.Combinator.PhaseCombinator

variable {n : Nat}

/-! ### Phase: the atomic building block -/

/-- A single protocol phase: broadcast a message, receive from HO set, update state.
    Named `CPhase` (combinator phase) to avoid collision with `TLA.Phase`. -/
structure CPhase (n : Nat) (S M : Type) where
  /-- The message process `p` sends given its local state. -/
  send : Fin n → S → M
  /-- How process `p` updates its state given received messages.
      `msgs : Fin n → Option M` maps each sender to `some m` or `none`. -/
  update : Fin n → S → (Fin n → Option M) → S

/-- Execute a phase: deliver messages according to HO, then update all processes. -/
def CPhase.step (ph : CPhase n S M) (ho : HOCollection (Fin n))
    (locals : Fin n → S) : Fin n → S :=
  fun p => ph.update p (locals p)
    (fun q => if ho p q then some (ph.send q (locals q)) else none)

/-- A phase preserves invariant `inv` under communication predicate `comm`.
    For any valid HO collection and any state satisfying `inv`, the
    post-state after executing the phase also satisfies `inv`. -/
def CPhase.preserves (ph : CPhase n S M) (comm : HOCollection (Fin n) → Prop)
    (inv : (Fin n → S) → Prop) : Prop :=
  ∀ locals ho, inv locals → comm ho → inv (ph.step ho locals)

/-! ### Sequential composition -/

/-- The result of sequentially composing two phases.
    Each phase gets its own HO collection (matching `PhaseRoundAlg`).
    The composed step applies phase A's HO, then phase B's HO. -/
structure SeqStep (n : Nat) (S : Type) where
  /-- The pre-state of the composition. -/
  pre : Fin n → S
  /-- The intermediate state (after phase A, before phase B). -/
  mid : Fin n → S
  /-- The post-state (after phase B). -/
  post : Fin n → S

/-- Execute two phases in sequence: phase A with `hoA`, then phase B with `hoB`. -/
def CPhase.seqStep (phA : CPhase n S MA) (phB : CPhase n S MB)
    (hoA hoB : HOCollection (Fin n)) (locals : Fin n → S) : SeqStep n S where
  pre := locals
  mid := phA.step hoA locals
  post := phB.step hoB (phA.step hoA locals)

/-- The post-state of sequential composition. -/
def CPhase.seqResult (phA : CPhase n S MA) (phB : CPhase n S MB)
    (hoA hoB : HOCollection (Fin n)) (locals : Fin n → S) : Fin n → S :=
  phB.step hoB (phA.step hoA locals)

/-! ### The Composition Theorems

    We provide two composition theorems:

    1. `seq_compose` — the **one-shot** pattern: phase A preserves a global
       invariant `inv_A`, and phase B both preserves `inv_A` AND establishes
       a new property `inv_B` given `inv_A`. This matches Paxos-style proofs
       where phase 1 establishes "at most one proposal" and phase 2 establishes
       "decision = proposal".

    2. `seq_preserves_both` — the **inductive** pattern: both phases preserve
       both invariants. This is the standard inductive invariant composition
       where `inv_A ∧ inv_B` is an inductive invariant of the composed system.
-/

/-- **Composition theorem (one-shot)**: the correct formulation where
    phase A preserves `inv_A`, phase B preserves `inv_A` AND establishes
    `inv_B` given `inv_A` at input.

    This is the practical theorem: `inv_A` is a "global" invariant preserved
    by both phases, and `inv_B` is established by phase B. -/
theorem seq_compose
    (phA : CPhase n S MA) (phB : CPhase n S MB)
    (commA commB : HOCollection (Fin n) → Prop)
    (inv_A inv_B : (Fin n → S) → Prop)
    (hA_preserves_A : phA.preserves commA inv_A)
    (hB_preserves_A : ∀ locals hoB, inv_A locals → commB hoB →
                      inv_A (phB.step hoB locals))
    (hB_establishes_B : ∀ locals hoB, inv_A locals → commB hoB →
                        inv_B (phB.step hoB locals)) :
    ∀ locals hoA hoB,
      inv_A locals → commA hoA → commB hoB →
      inv_A (CPhase.seqResult phA phB hoA hoB locals) ∧
      inv_B (CPhase.seqResult phA phB hoA hoB locals) := by
  intro locals hoA hoB hInvA hCommA hCommB
  unfold CPhase.seqResult
  have hMidA : inv_A (phA.step hoA locals) := hA_preserves_A locals hoA hInvA hCommA
  exact ⟨hB_preserves_A _ hoB hMidA hCommB,
         hB_establishes_B _ hoB hMidA hCommB⟩

/-- **Inductive composition**: both phases preserve both invariants.
    This is the standard inductive invariant composition. -/
theorem seq_preserves_both
    (phA : CPhase n S MA) (phB : CPhase n S MB)
    (commA commB : HOCollection (Fin n) → Prop)
    (inv_A inv_B : (Fin n → S) → Prop)
    (hA_A : phA.preserves commA inv_A)
    (hA_B : ∀ locals hoA, inv_A locals → inv_B locals → commA hoA →
            inv_B (phA.step hoA locals))
    (hB_A : ∀ locals hoB, inv_A locals → inv_B locals → commB hoB →
            inv_A (phB.step hoB locals))
    (hB_B : ∀ locals hoB, inv_A locals → inv_B locals → commB hoB →
            inv_B (phB.step hoB locals)) :
    ∀ locals hoA hoB,
      inv_A locals → inv_B locals → commA hoA → commB hoB →
      inv_A (CPhase.seqResult phA phB hoA hoB locals) ∧
      inv_B (CPhase.seqResult phA phB hoA hoB locals) := by
  intro locals hoA hoB hInvA hInvB hCommA hCommB
  unfold CPhase.seqResult
  have hMidA : inv_A (phA.step hoA locals) := hA_A locals hoA hInvA hCommA
  have hMidB : inv_B (phA.step hoA locals) := hA_B locals hoA hInvA hInvB hCommA
  exact ⟨hB_A _ hoB hMidA hMidB hCommB,
         hB_B _ hoB hMidA hMidB hCommB⟩

/-! ### Cross-Phase Quorum Intersection -/

/-- If phase A collected a quorum `Q_A` and phase B collects a quorum `Q_B`
    from the same quorum system, they share a witness. This is the core
    technique for Paxos-family proofs: the promise quorum and accept
    quorum must overlap. -/
theorem cross_phase_quorum_intersection (qs : QuorumSystem n)
    (Q_A Q_B : Fin n → Bool)
    (hA : qs.isQuorum Q_A) (hB : qs.isQuorum Q_B) :
    ∃ i, Q_A i = true ∧ Q_B i = true :=
  qs.intersection Q_A Q_B hA hB

/-! ### Iterated Composition -/

/-- A multi-phase protocol: a list of phases sharing the same state type.
    Messages may differ per phase (erased to a common type via `M`). -/
structure MultiPhase (n : Nat) (S M : Type) where
  /-- The phases in order. -/
  phases : List (CPhase n S M)
  /-- At least one phase. -/
  nonempty : phases.length > 0

/-- Execute the first `k` phases of a multi-phase protocol in sequence. -/
def MultiPhase.runAux (mp : MultiPhase n S M) (hos : Fin mp.phases.length → HOCollection (Fin n))
    (locals : Fin n → S) : (k : Nat) → k ≤ mp.phases.length → Fin n → S
  | 0, _ => locals
  | k + 1, hk =>
    let prev := mp.runAux hos locals k (by omega)
    (mp.phases[k]'(by omega)).step (hos ⟨k, by omega⟩) prev

/-- Execute all phases of a multi-phase protocol in sequence. -/
def MultiPhase.run (mp : MultiPhase n S M) (hos : Fin mp.phases.length → HOCollection (Fin n))
    (locals : Fin n → S) : Fin n → S :=
  mp.runAux hos locals mp.phases.length (Nat.le_refl _)

/-! ### Demonstration: Two-Phase Consensus -/

/-- Value type for the demonstration. -/
inductive TPValue where
  | v0 | v1
  deriving DecidableEq, Repr

/-- Local state for the two-phase consensus demo. -/
structure TPState where
  /-- Current value held by the process. -/
  val : TPValue
  /-- Proposed value (set after phase 1 if majority agrees). -/
  proposal : Option TPValue
  /-- Decision (set after phase 2 if majority accepts). -/
  decision : Option TPValue
  deriving DecidableEq

/-! #### Phase 1: Propose -/

/-- Phase 1 message: broadcast current value. -/
def phase1 (n : Nat) : CPhase n TPState TPValue where
  send := fun _p s => s.val
  update := fun _p s msgs =>
    let received := (List.finRange n).filterMap msgs
    let count0 := (received.filter (· == .v0)).length
    let count1 := (received.filter (· == .v1)).length
    if count0 * 2 > n then { s with proposal := some .v0 }
    else if count1 * 2 > n then { s with proposal := some .v1 }
    else { s with proposal := none }

/-- Phase 2 message: broadcast proposal. -/
def phase2 (n : Nat) : CPhase n TPState (Option TPValue) where
  send := fun _p s => s.proposal
  update := fun _p s msgs =>
    let received := (List.finRange n).filterMap msgs
    let acceptCount (v : TPValue) := (received.filter (· == some v)).length
    if acceptCount .v0 * 2 > n then { s with decision := some .v0 }
    else if acceptCount .v1 * 2 > n then { s with decision := some .v1 }
    else s

/-! #### Invariants -/

/-- Phase 1 invariant: at most one value can be proposed.
    If any process proposed `v`, then `v` has majority support, which means
    no other value can also have majority support (by quorum intersection). -/
def atMostOneProposal (locals : Fin n → TPState) : Prop :=
  ∀ p q v w, (locals p).proposal = some v → (locals q).proposal = some w → v = w

/-- Phase 2 invariant: if any process decided `v`, then `v` was proposed. -/
def decisionWasProposed (locals : Fin n → TPState) : Prop :=
  ∀ p v, (locals p).decision = some v →
    ∃ q, (locals q).proposal = some v

/-- Agreement: all decided processes agree. -/
def tpAgreement (locals : Fin n → TPState) : Prop :=
  ∀ p q v w,
    (locals p).decision = some v →
    (locals q).decision = some w →
    v = w

/-! #### Counting helpers -/

/-- Fuse a `filter`-of-`filterMap` into a single combined filter length.
    Used to count how many elements of `L` satisfy both a Bool condition
    `c` and a value-match predicate after applying `g`. -/
private theorem filter_filterMap_length_eq {α β : Type} [BEq β] (L : List α)
    (c : α → Bool) (g : α → β) (v : β) :
    (List.filter (· == v) (List.filterMap
      (fun q => if c q = true then some (g q) else none) L)).length =
    (L.filter (fun q => c q && g q == v)).length := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.filterMap_cons]
    cases hc : c a with
    | true =>
      simp only [hc, if_true, List.filter_cons, Bool.true_and]
      cases hv : (g a == v) with
      | true => simp only [hv, if_true, List.length_cons, ih]
      | false =>
        simp only [hv, Bool.false_eq_true, if_false, ih]
    | false =>
      simp only [hc, Bool.false_eq_true, if_false, List.filter_cons, Bool.false_and]
      exact ih

/-- For any list `L` of `Fin n`, the v0-filter length + v1-filter length = L.length. -/
private theorem tpvalue_filter_sum (n : Nat) (locals : Fin n → TPState)
    (L : List (Fin n)) :
    (L.filter (fun q => (locals q).val == TPValue.v0)).length +
    (L.filter (fun q => (locals q).val == TPValue.v1)).length =
    L.length := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.filter_cons, List.length_cons]
    cases hv : (locals a).val with
    | v0 =>
      have e0 : (TPValue.v0 == TPValue.v0) = true := by decide
      have e1 : (TPValue.v0 == TPValue.v1) = false := by decide
      simp only [hv, e0, e1, Bool.false_eq_true, if_true, if_false, List.length_cons]
      omega
    | v1 =>
      have e0 : (TPValue.v1 == TPValue.v0) = false := by decide
      have e1 : (TPValue.v1 == TPValue.v1) = true := by decide
      simp only [hv, e0, e1, Bool.false_eq_true, if_false, if_true, List.length_cons]
      omega

/-- Global v0/v1 counts sum to `n`. -/
private theorem tpvalue_counts_partition (n : Nat) (locals : Fin n → TPState) :
    ((List.finRange n).filter (fun q => (locals q).val == TPValue.v0)).length +
    ((List.finRange n).filter (fun q => (locals q).val == TPValue.v1)).length =
    n := by
  rw [tpvalue_filter_sum, List.length_finRange]

/-- If a filtered list is nonempty, there exists an element satisfying the predicate. -/
private theorem filter_pos_exists {α : Type} (L : List α) (P : α → Bool) :
    (L.filter P).length > 0 → ∃ x ∈ L, P x = true := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.filter_cons]
    cases hP : P a with
    | true =>
      intro _
      exact ⟨a, List.mem_cons_self, hP⟩
    | false =>
      simp only [hP, Bool.false_eq_true, if_false]
      intro h
      obtain ⟨x, hxL, hPx⟩ := ih h
      exact ⟨x, List.mem_cons_of_mem _ hxL, hPx⟩

/-- Filter length is monotone in the predicate. -/
private theorem filter_length_mono {α : Type} (L : List α) (P Q : α → Bool)
    (h : ∀ x, P x = true → Q x = true) :
    (L.filter P).length ≤ (L.filter Q).length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.filter_cons]
    cases hP : P a with
    | true =>
      have hQ := h a hP
      simp only [hP, hQ, if_true, List.length_cons]
      omega
    | false =>
      simp only [hP, Bool.false_eq_true, if_false]
      cases hQ : Q a with
      | true =>
        simp only [hQ, if_true, List.length_cons]
        omega
      | false =>
        simp only [hQ, Bool.false_eq_true, if_false]
        exact ih

/-! #### The composition argument -/

/-- **Agreement from composed invariants** (sorry-free).
    Given `atMostOneProposal` and `decisionWasProposed`, agreement follows. -/
theorem agreement_from_invariants (locals : Fin n → TPState)
    (h1 : atMostOneProposal locals) (h2 : decisionWasProposed locals) :
    tpAgreement locals := by
  intro p q v w hv hw
  obtain ⟨pv, hpv⟩ := h2 p v hv
  obtain ⟨qw, hqw⟩ := h2 q w hw
  exact h1 pv qw v w hpv hqw

/-- Phase 1 establishes `atMostOneProposal` when the communication
    predicate guarantees majority delivery. The proof uses the majority
    quorum intersection from `QuorumSystem.lean`. -/
theorem phase1_establishes_proposal (n : Nat) :
    ∀ locals (ho : HOCollection (Fin n)),
      (∀ p, ((List.finRange n).filter fun q => ho p q).length * 2 > n) →
      atMostOneProposal (CPhase.step (phase1 n) ho locals) := by
  intro locals ho _hcomm p q v w hv hw
  -- Helper: local count at any proposer ≤ global count.
  have bound : ∀ (r : Fin n) (val : TPValue),
      (List.filter (fun x => x == val)
        (List.filterMap (fun s => if ho r s = true then some (locals s).val else none)
          (List.finRange n))).length ≤
      ((List.finRange n).filter (fun s => (locals s).val == val)).length := by
    intro r val
    rw [filter_filterMap_length_eq]
    exact filter_length_mono _ _ _ (by
      intro x hx
      simp only [Bool.and_eq_true] at hx
      exact hx.2)
  have hpart := tpvalue_counts_partition n locals
  -- Unfold hv and hw to extract the count conditions.
  simp only [CPhase.step, phase1] at hv hw
  cases v with
  | v0 =>
    cases w with
    | v0 => rfl
    | v1 =>
      exfalso
      -- Extract: hv forces count0_p * 2 > n (otherwise prop ≠ some v0).
      have hp0 : (List.filter (fun x => x == TPValue.v0)
        (List.filterMap (fun s => if ho p s = true then some (locals s).val else none)
          (List.finRange n))).length * 2 > n := by
        rcases Nat.lt_or_ge n _ with h | h
        · exact h
        · exfalso
          simp only [Nat.not_lt.mpr h, if_false] at hv
          split at hv <;> simp_all [reduceCtorEq]
      -- Extract: hw forces count1_q * 2 > n (and count0_q * 2 ≤ n).
      have hq1 : (List.filter (fun x => x == TPValue.v1)
        (List.filterMap (fun s => if ho q s = true then some (locals s).val else none)
          (List.finRange n))).length * 2 > n := by
        rcases Nat.lt_or_ge n _ with h | h
        · exact h
        · exfalso
          split at hw
          · simp_all [reduceCtorEq]
          · simp only [Nat.not_lt.mpr h, if_false] at hw
            simp_all [reduceCtorEq]
      have b0 := bound p TPValue.v0
      have b1 := bound q TPValue.v1
      omega
  | v1 =>
    cases w with
    | v0 =>
      exfalso
      have hq0 : (List.filter (fun x => x == TPValue.v0)
        (List.filterMap (fun s => if ho q s = true then some (locals s).val else none)
          (List.finRange n))).length * 2 > n := by
        rcases Nat.lt_or_ge n _ with h | h
        · exact h
        · exfalso
          simp only [Nat.not_lt.mpr h, if_false] at hw
          split at hw <;> simp_all [reduceCtorEq]
      have hp1 : (List.filter (fun x => x == TPValue.v1)
        (List.filterMap (fun s => if ho p s = true then some (locals s).val else none)
          (List.finRange n))).length * 2 > n := by
        rcases Nat.lt_or_ge n _ with h | h
        · exact h
        · exfalso
          split at hv
          · simp_all [reduceCtorEq]
          · simp only [Nat.not_lt.mpr h, if_false] at hv
            simp_all [reduceCtorEq]
      have b0 := bound q TPValue.v0
      have b1 := bound p TPValue.v1
      omega
    | v1 => rfl

/-- Phase 2 establishes `decisionWasProposed` assuming `atMostOneProposal`
    holds and proposals are unchanged by phase 2.
    (Phase 2 does not modify the `proposal` field.) -/
theorem phase2_preserves_proposal (n : Nat) :
    ∀ locals (ho : HOCollection (Fin n)),
      atMostOneProposal locals →
      atMostOneProposal (CPhase.step (phase2 n) ho locals) := by
  intro locals ho h1 p q v w hpv hqw
  -- Phase 2 does not change the proposal field.
  have h_eq : ∀ r, ((phase2 n).step ho locals r).proposal = (locals r).proposal := by
    intro r
    show ((phase2 n).update r (locals r) _).proposal = _
    unfold phase2
    simp only
    split
    · rfl
    · split
      · rfl
      · rfl
  rw [h_eq p] at hpv
  rw [h_eq q] at hqw
  exact h1 p q v w hpv hqw

/-- Phase 2 preserves/establishes `decisionWasProposed`. The theorem is a
    preservation statement: if the pre-state already satisfies the invariant,
    the post-state does too. New decisions set by phase 2 require a majority
    of `some v` messages, so at least one process had `proposal = some v`.
    Existing decisions are inherited via the pre-state invariant. -/
theorem phase2_establishes_decision (n : Nat) :
    ∀ locals (ho : HOCollection (Fin n)),
      decisionWasProposed locals →
      (∀ p, ((List.finRange n).filter fun q => ho p q).length * 2 > n) →
      decisionWasProposed (CPhase.step (phase2 n) ho locals) := by
  intro locals ho hprev _hcomm p v hv
  -- Phase 2 preserves the proposal field.
  have h_eq : ∀ r, ((phase2 n).step ho locals r).proposal = (locals r).proposal := by
    intro r
    show ((phase2 n).update r (locals r) _).proposal = _
    unfold phase2
    simp only
    split
    · rfl
    · split
      · rfl
      · rfl
  suffices h : ∃ q, (locals q).proposal = some v by
    obtain ⟨q, hq⟩ := h
    exact ⟨q, by rw [h_eq q]; exact hq⟩
  -- Helper: from a positive-count filter, extract a proposer.
  have extract : ∀ (val : TPValue),
      (List.filter (fun x => x == some val)
        (List.filterMap (fun s => if ho p s = true then some (locals s).proposal else none)
          (List.finRange n))).length > 0 →
      ∃ q, (locals q).proposal = some val := by
    intro val hpos
    obtain ⟨x, hxL, hxv⟩ := filter_pos_exists _ _ hpos
    rw [List.mem_filterMap] at hxL
    obtain ⟨q, _, hq_eq⟩ := hxL
    refine ⟨q, ?_⟩
    cases hho : ho p q with
    | true =>
      rw [hho] at hq_eq
      simp only [if_true] at hq_eq
      -- hq_eq: some (locals q).proposal = x, hxv: x == some val
      -- So (locals q).proposal = x and x == some val. Need x = some val.
      have : x = some val := by
        cases x with
        | none => simp at hxv
        | some y =>
          cases val with
          | v0 =>
            cases y with
            | v0 => rfl
            | v1 => simp at hxv
          | v1 =>
            cases y with
            | v0 => simp at hxv
            | v1 => rfl
      rw [this] at hq_eq
      exact Option.some.inj hq_eq
    | false =>
      rw [hho] at hq_eq
      simp at hq_eq
  simp only [CPhase.step, phase2] at hv
  -- Case analysis on phase2's three branches.
  split at hv
  · -- Branch 1: majority of v0 → new decision = some v0
    rename_i h0
    obtain rfl : v = TPValue.v0 := by cases hv; rfl
    exact extract TPValue.v0 (by omega)
  · split at hv
    · -- Branch 2: majority of v1 → new decision = some v1
      rename_i h1
      obtain rfl : v = TPValue.v1 := by cases hv; rfl
      exact extract TPValue.v1 (by omega)
    · -- Branch 3: decision inherited from pre-state
      exact hprev p v hv

/-- **The composition: agreement for the two-phase protocol** (sorry-free).

    Requires `hNoDec : ∀ r, (locals r).decision = none` — we start with no
    pre-existing decisions (the natural initial condition for consensus).
    This makes `decisionWasProposed locals` vacuous, and since phase 1 doesn't
    touch the decision field, it remains vacuous entering phase 2, where
    `phase2_establishes_decision` takes over. -/
theorem two_phase_agreement (n : Nat)
    (commA commB : HOCollection (Fin n) → Prop)
    (hcommA : ∀ ho, commA ho →
      ∀ p, ((List.finRange n).filter fun q => ho p q).length * 2 > n)
    (hcommB : ∀ ho, commB ho →
      ∀ p, ((List.finRange n).filter fun q => ho p q).length * 2 > n)
    (locals : Fin n → TPState)
    (hoA hoB : HOCollection (Fin n))
    (hInvA : atMostOneProposal locals)
    (hNoDec : ∀ r, (locals r).decision = none)
    (hCommA : commA hoA) (hCommB : commB hoB) :
    tpAgreement (CPhase.seqResult (phase1 n) (phase2 n) hoA hoB locals) := by
  unfold CPhase.seqResult
  -- Phase 1 establishes atMostOneProposal on its output.
  have midA : atMostOneProposal ((phase1 n).step hoA locals) :=
    phase1_establishes_proposal n locals hoA (hcommA hoA hCommA)
  -- Phase 1 preserves "no decisions" because it doesn't touch decision field.
  have midNoDec : ∀ r, ((phase1 n).step hoA locals r).decision = none := by
    intro r
    show ((phase1 n).update r (locals r) _).decision = none
    unfold phase1
    simp only
    split
    · exact hNoDec r
    · split
      · exact hNoDec r
      · exact hNoDec r
  -- Decision invariant is vacuously true on the mid-state.
  have midPrevB : decisionWasProposed ((phase1 n).step hoA locals) := by
    intro p v hv
    rw [midNoDec p] at hv
    exact absurd hv (by simp [reduceCtorEq])
  -- Phase 2 preserves atMostOneProposal.
  have postA : atMostOneProposal ((phase2 n).step hoB ((phase1 n).step hoA locals)) :=
    phase2_preserves_proposal n _ hoB midA
  -- Phase 2 establishes decisionWasProposed on its output.
  have postB : decisionWasProposed ((phase2 n).step hoB ((phase1 n).step hoA locals)) :=
    phase2_establishes_decision n _ hoB midPrevB (hcommB hoB hCommB)
  exact agreement_from_invariants _ postA postB

/-! ### Connecting to Round Infrastructure -/

/-- Convert a two-phase combinator protocol (with uniform message type)
    into a `TLA.PhaseRoundAlg`. This shows that the combinator phases are
    compatible with the existing `PhaseRound.lean` infrastructure. -/
def toPhaseRoundAlg (ph1 ph2 : CPhase n S M)
    (initPred : Fin n → S → Prop) :
    TLA.PhaseRoundAlg (Fin n) S 2 (fun _ => M) where
  init := initPred
  phases := fun i =>
    if i.val = 0 then
      { send := ph1.send, update := ph1.update }
    else
      { send := ph2.send, update := ph2.update }

end TLA.Combinator.PhaseCombinator
