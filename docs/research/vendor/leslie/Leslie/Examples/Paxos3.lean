import Leslie.Action

/-! ## Single-Decree Paxos as an ActionSpec

    A simplified single-decree Paxos protocol with 3 acceptors and
    2 proposers (each using a fixed ballot). Demonstrates refinement
    from the concrete Paxos protocol to an abstract Consensus spec.

    **Abstract spec (Consensus)**:
      State: `chosen : Option Value`
      Init:  `chosen = none`
      Next:  choose a value (if none chosen yet)

    **Concrete spec (Paxos)**:
      State: acceptor promises/accepts, proposer proposals, message flags
      Init:  no promises, no proposals
      Next:  phase 1b (promise), phase 2a (propose), phase 2b (accept)

    We prove: Paxos refines Consensus (safety only).

    Simplifications:
    - 2 proposers with fixed ballots (b1 < b2)
    - 3 acceptors (quorum = any 2)
    - 2 possible values
    - Phase 1a is implicit (proposers start with their ballot)
    - Messages modeled as Boolean flags
-/

open TLA

namespace Paxos

/-! ### Types -/

inductive Value where | v1 | v2
  deriving DecidableEq, Repr

/-- Ballot numbers. b1 < b2 by convention. -/
inductive Ballot where | b1 | b2
  deriving DecidableEq, Repr

/-! ### Abstract Spec: Consensus -/

structure ConsensusState where
  chosen : Option Value

inductive ConsensusAction where
  | choose1 | choose2

def consensus : ActionSpec ConsensusState ConsensusAction where
  init := fun s => s.chosen = none
  actions := fun
    | .choose1 => {
        gate := fun s => s.chosen = none
        transition := fun _ s' => s' = { chosen := some .v1 }
      }
    | .choose2 => {
        gate := fun s => s.chosen = none
        transition := fun _ s' => s' = { chosen := some .v2 }
      }

/-! ### Concrete Spec: Single-Decree Paxos -/

@[ext]
structure PaxosState where
  -- Per-acceptor: highest ballot promised (None = no promise yet)
  prom1 : Option Ballot
  prom2 : Option Ballot
  prom3 : Option Ballot
  -- Per-acceptor: last accepted (ballot, value) pair
  acc1  : Option (Ballot × Value)
  acc2  : Option (Ballot × Value)
  acc3  : Option (Ballot × Value)
  -- Phase 1b received: proposer i got promise from acceptor j
  got1b_1_1 : Bool
  got1b_1_2 : Bool
  got1b_1_3 : Bool
  got1b_2_1 : Bool
  got1b_2_2 : Bool
  got1b_2_3 : Bool
  -- Acceptor reports in phase-1b to proposer 2
  rep2_1 : Option (Ballot × Value)
  rep2_2 : Option (Ballot × Value)
  rep2_3 : Option (Ballot × Value)
  -- Per-proposer: proposed value (None = hasn't proposed yet)
  prop1 : Option Value
  prop2 : Option Value
  -- Phase 2b: acceptor j accepted proposer i's value
  did2b_1_1 : Bool
  did2b_1_2 : Bool
  did2b_1_3 : Bool
  did2b_2_1 : Bool
  did2b_2_2 : Bool
  did2b_2_3 : Bool

/-! ### Helpers -/

def majority3 (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

/-- Any two majorities of 3 share at least one member **at the same index**.
    This is the useful form for quorum-intersection arguments: given that
    acceptor-set A and acceptor-set B each form a majority, there exists
    some acceptor index i that belongs to both. -/
theorem majority3_quorum_intersection (a1 a2 a3 b1 b2 b3 : Bool)
    (ha : majority3 a1 a2 a3 = true) (hb : majority3 b1 b2 b3 = true) :
    (a1 = true ∧ b1 = true) ∨ (a2 = true ∧ b2 = true) ∨ (a3 = true ∧ b3 = true) := by
  simp only [majority3, Bool.or_eq_true, Bool.and_eq_true] at ha hb
  rcases ha with ⟨ha1, ha2⟩ | ⟨ha1, ha3⟩ | ⟨ha2, ha3⟩ <;>
  rcases hb with ⟨hb1, hb2⟩ | ⟨hb1, hb3⟩ | ⟨hb2, hb3⟩ <;> simp_all

/-! ### Paxos Actions -/

inductive PaxosAction where
  | p1b_1_1 | p1b_1_2 | p1b_1_3
  | p1b_2_1 | p1b_2_2 | p1b_2_3
  | p2a_1 | p2a_2
  | p2b_1_1 | p2b_1_2 | p2b_1_3
  | p2b_2_1 | p2b_2_2 | p2b_2_3

def paxos : ActionSpec PaxosState PaxosAction where
  init := fun s =>
    s.prom1 = none ∧ s.prom2 = none ∧ s.prom3 = none ∧
    s.acc1 = none ∧ s.acc2 = none ∧ s.acc3 = none ∧
    s.got1b_1_1 = false ∧ s.got1b_1_2 = false ∧ s.got1b_1_3 = false ∧
    s.got1b_2_1 = false ∧ s.got1b_2_2 = false ∧ s.got1b_2_3 = false ∧
    s.rep2_1 = none ∧ s.rep2_2 = none ∧ s.rep2_3 = none ∧
    s.prop1 = none ∧ s.prop2 = none ∧
    s.did2b_1_1 = false ∧ s.did2b_1_2 = false ∧ s.did2b_1_3 = false ∧
    s.did2b_2_1 = false ∧ s.did2b_2_2 = false ∧ s.did2b_2_3 = false
  actions := fun
    -- Phase 1b: acceptor j promises to proposer 1 (ballot b1)
    | .p1b_1_1 => {
        gate := fun s => s.got1b_1_1 = false ∧
          (s.prom1 = none ∨ s.prom1 = some .b1)
        transition := fun s s' =>
          s' = { s with prom1 := some .b1, got1b_1_1 := true }
      }
    | .p1b_1_2 => {
        gate := fun s => s.got1b_1_2 = false ∧
          (s.prom2 = none ∨ s.prom2 = some .b1)
        transition := fun s s' =>
          s' = { s with prom2 := some .b1, got1b_1_2 := true }
      }
    | .p1b_1_3 => {
        gate := fun s => s.got1b_1_3 = false ∧
          (s.prom3 = none ∨ s.prom3 = some .b1)
        transition := fun s s' =>
          s' = { s with prom3 := some .b1, got1b_1_3 := true }
      }
    -- Phase 1b: acceptor j promises to proposer 2 (ballot b2, highest)
    | .p1b_2_1 => {
        gate := fun s => s.got1b_2_1 = false
        transition := fun s s' =>
          s' = { s with prom1 := some .b2, got1b_2_1 := true, rep2_1 := s.acc1 }
      }
    | .p1b_2_2 => {
        gate := fun s => s.got1b_2_2 = false
        transition := fun s s' =>
          s' = { s with prom2 := some .b2, got1b_2_2 := true, rep2_2 := s.acc2 }
      }
    | .p1b_2_3 => {
        gate := fun s => s.got1b_2_3 = false
        transition := fun s s' =>
          s' = { s with prom3 := some .b2, got1b_2_3 := true, rep2_3 := s.acc3 }
      }
    -- Phase 2a: proposer 1 proposes (free choice, b1 is lowest ballot)
    | .p2a_1 => {
        gate := fun s => s.prop1 = none ∧
          majority3 s.got1b_1_1 s.got1b_1_2 s.got1b_1_3 = true
        transition := fun s s' => ∃ v, s' = { s with prop1 := some v }
      }
    -- Phase 2a: proposer 2 proposes (must respect highest b1 report)
    | .p2a_2 => {
        gate := fun s => s.prop2 = none ∧
          majority3 s.got1b_2_1 s.got1b_2_2 s.got1b_2_3 = true
        transition := fun s s' => ∃ v, s' = { s with prop2 := some v } ∧
          -- Constraint: if any phase-1b report has a b1 entry, use that value
          (∀ w, (s.got1b_2_1 = true ∧ s.rep2_1 = some (.b1, w)) ∨
                (s.got1b_2_2 = true ∧ s.rep2_2 = some (.b1, w)) ∨
                (s.got1b_2_3 = true ∧ s.rep2_3 = some (.b1, w)) → v = w)
      }
    -- Phase 2b: acceptor j accepts proposer 1's value
    | .p2b_1_1 => {
        gate := fun s => s.did2b_1_1 = false ∧
          (s.prom1 = none ∨ s.prom1 = some .b1)
        transition := fun s s' => ∃ v, s.prop1 = some v ∧
          s' = { s with acc1 := some (.b1, v), prom1 := some .b1, did2b_1_1 := true }
      }
    | .p2b_1_2 => {
        gate := fun s => s.did2b_1_2 = false ∧
          (s.prom2 = none ∨ s.prom2 = some .b1)
        transition := fun s s' => ∃ v, s.prop1 = some v ∧
          s' = { s with acc2 := some (.b1, v), prom2 := some .b1, did2b_1_2 := true }
      }
    | .p2b_1_3 => {
        gate := fun s => s.did2b_1_3 = false ∧
          (s.prom3 = none ∨ s.prom3 = some .b1)
        transition := fun s s' => ∃ v, s.prop1 = some v ∧
          s' = { s with acc3 := some (.b1, v), prom3 := some .b1, did2b_1_3 := true }
      }
    -- Phase 2b: acceptor j accepts proposer 2's value
    | .p2b_2_1 => {
        gate := fun s => s.did2b_2_1 = false
        transition := fun s s' => ∃ v, s.prop2 = some v ∧
          s' = { s with acc1 := some (.b2, v), prom1 := some .b2, did2b_2_1 := true }
      }
    | .p2b_2_2 => {
        gate := fun s => s.did2b_2_2 = false
        transition := fun s s' => ∃ v, s.prop2 = some v ∧
          s' = { s with acc2 := some (.b2, v), prom2 := some .b2, did2b_2_2 := true }
      }
    | .p2b_2_3 => {
        gate := fun s => s.did2b_2_3 = false
        transition := fun s s' => ∃ v, s.prop2 = some v ∧
          s' = { s with acc3 := some (.b2, v), prom3 := some .b2, did2b_2_3 := true }
      }

/-! ### Refinement mapping -/

def paxos_ref (s : PaxosState) : ConsensusState where
  chosen :=
    if majority3 s.did2b_1_1 s.did2b_1_2 s.did2b_1_3 then s.prop1
    else if majority3 s.did2b_2_1 s.did2b_2_2 s.did2b_2_3 then s.prop2
    else none

/-! ### Protocol Invariant

    Eight groups of properties, each a named field of a structure.
    Using a structure (not a flat `∧`) means adding a new field never
    breaks existing field accesses, and proofs can name the hypothesis
    they need directly (e.g. `hinv.hE`) rather than destructuring by
    position.

    **(A)** Phase-2b acks imply the proposer has proposed.

    **(B)** Any ballot-b1 acceptance matches prop1's value.
        (All acceptors that accepted at b1 accepted the same value,
        because b1 acceptances come from prop1.)

    **(C)** Phase-1b reports carrying a b1 entry match prop1.
        (Reports faithfully reflect b1 acceptances.)

    **(D)** Before prop2 is set, if an acceptor both did phase-2b for
        proposer 1 AND sent phase-1b to proposer 2, the report has
        a b1 entry. (Key ordering argument: p2b_1_j must happen before
        p1b_2_j because promising b2 blocks b1 acceptance. And since
        prop2 = none means no p2b_2 has happened, the b1 acceptance
        is still in place when the report is made.)

    **(E)** Core safety: if proposer 2 has proposed and proposer 1 has
        a majority of phase-2b acks, they proposed the same value.
        (Follows from quorum intersection + D + C.)

    **(H)** Receiving a phase-1b from proposer 2 permanently locks that
        acceptor's promise at b2. (Needed to derive got1b_2_j = false
        from p2b_1_j's gate when proving E is preserved.)

    **(I')** Before prop2 is set, a b1 acceptance is still recorded in
        the acceptor's state. (p2b_2 overwrites acc_j but requires
        prop2 ≠ none, so acc_j is stable while prop2 = none.)

    **(J)** Once prop2 is set, proposer 2's quorum is permanent.
        (got1b_2 flags only grow; the gate for p2a_2 establishes the
        majority, and it can only increase thereafter.) -/

structure PaxosInv (s : PaxosState) : Prop where
  -- (A) did2b implies prop exists
  hA1  : s.did2b_1_1 = true → s.prop1 ≠ none
  hA2  : s.did2b_1_2 = true → s.prop1 ≠ none
  hA3  : s.did2b_1_3 = true → s.prop1 ≠ none
  hA4  : s.did2b_2_1 = true → s.prop2 ≠ none
  hA5  : s.did2b_2_2 = true → s.prop2 ≠ none
  hA6  : s.did2b_2_3 = true → s.prop2 ≠ none
  -- (B) b1 acceptances match prop1
  hB1  : ∀ v, s.acc1 = some (.b1, v) → s.prop1 = some v
  hB2  : ∀ v, s.acc2 = some (.b1, v) → s.prop1 = some v
  hB3  : ∀ v, s.acc3 = some (.b1, v) → s.prop1 = some v
  -- (C) b1 reports to proposer 2 match prop1
  hC1  : ∀ v, s.rep2_1 = some (.b1, v) → s.prop1 = some v
  hC2  : ∀ v, s.rep2_2 = some (.b1, v) → s.prop1 = some v
  hC3  : ∀ v, s.rep2_3 = some (.b1, v) → s.prop1 = some v
  -- (D) Before prop2 is set: overlap implies b1 report
  hD1  : s.prop2 = none → s.did2b_1_1 = true → s.got1b_2_1 = true →
           ∃ v, s.rep2_1 = some (.b1, v)
  hD2  : s.prop2 = none → s.did2b_1_2 = true → s.got1b_2_2 = true →
           ∃ v, s.rep2_2 = some (.b1, v)
  hD3  : s.prop2 = none → s.did2b_1_3 = true → s.got1b_2_3 = true →
           ∃ v, s.rep2_3 = some (.b1, v)
  -- (E) Core safety: prop2 set + majority for prop1 → agree
  hE   : s.prop2 ≠ none →
           majority3 s.did2b_1_1 s.did2b_1_2 s.did2b_1_3 = true →
           s.prop1 = s.prop2
  -- (H) got1b_2_j = true locks prom_j at b2
  hH1  : s.got1b_2_1 = true → s.prom1 = some .b2
  hH2  : s.got1b_2_2 = true → s.prom2 = some .b2
  hH3  : s.got1b_2_3 = true → s.prom3 = some .b2
  -- (I') b1 acceptance survives in acc_j while prop2 = none
  hI1  : s.prop2 = none → s.did2b_1_1 = true → ∃ v, s.acc1 = some (.b1, v)
  hI2  : s.prop2 = none → s.did2b_1_2 = true → ∃ v, s.acc2 = some (.b1, v)
  hI3  : s.prop2 = none → s.did2b_1_3 = true → ∃ v, s.acc3 = some (.b1, v)
  -- (J) Proposer 2's quorum persists once prop2 is set
  hJ   : s.prop2 ≠ none → majority3 s.got1b_2_1 s.got1b_2_2 s.got1b_2_3 = true
  -- (K) Quorum-miss safety: if prop2 is set and acceptor j is NOT in proposer 2's
  --     quorum but some other acceptor k has a b1 acceptance, they agreed.
  --     (When p2b_1_j fires creating a new majority while prop2 ≠ none, the overlap
  --     acceptor k satisfies got1b_2_j = false ∧ did2b_1_k = true. K provides the
  --     prop1 = prop2 conclusion needed to preserve hE.)
  hK12 : s.prop2 ≠ none → s.got1b_2_1 = false → s.did2b_1_2 = true → s.prop1 = s.prop2
  hK13 : s.prop2 ≠ none → s.got1b_2_1 = false → s.did2b_1_3 = true → s.prop1 = s.prop2
  hK21 : s.prop2 ≠ none → s.got1b_2_2 = false → s.did2b_1_1 = true → s.prop1 = s.prop2
  hK23 : s.prop2 ≠ none → s.got1b_2_2 = false → s.did2b_1_3 = true → s.prop1 = s.prop2
  hK31 : s.prop2 ≠ none → s.got1b_2_3 = false → s.did2b_1_1 = true → s.prop1 = s.prop2
  hK32 : s.prop2 ≠ none → s.got1b_2_3 = false → s.did2b_1_2 = true → s.prop1 = s.prop2

/-- Convenience alias so existing proof skeletons continue to compile. -/
def paxos_inv (s : PaxosState) : Prop := PaxosInv s

/-! ### Refinement proof

    The proof uses `refinement_mapping_stutter_with_invariant`.

    **Invariant init**: All flags are false, all options are none.
    Every conjunct holds vacuously.

    **Invariant preservation**: 14 actions × 23 fields.
    Most are trivial (the action doesn't touch relevant fields).
    Non-trivial cases:
    - p1b_2_j preserving hC: report is set from acc, which by hB
      matches prop1 if it has a b1 entry.
    - p1b_2_j preserving hD: use hI to get acc_j = some (.b1,w),
      so rep2_j has a b1 entry.
    - p1b_2_j preserving hH: action sets prom_j = b2 simultaneously.
    - p2a_2 preserving hE: diagonal quorum intersection gives acceptor k
      with did2b_1_k ∧ got1b_2_k; by hD its report has a b1 entry;
      by hC that matches prop1; the constraint forces prop2 = prop1.
    - p2b_1_j preserving hE: use hH to derive got1b_2_j = false from
      the gate; use hJ to get majority3 got1b_2 = true; pigeonhole gives
      overlap acceptor k; then hD → hC → constraint gives prop1 = prop2.
    - p2b_1_j preserving hD: impossible — gate needs prom_j ≤ b1,
      but hH says got1b_2_j = true → prom_j = b2.
    - p2b_2_j preserving hI: gate requires prop2 ≠ none, so hI
      becomes vacuously true after the step.

    **Step simulation**: Most actions are stuttering steps (don't change
    did2b or prop). The key cases are p2b_i_j creating a new majority,
    which maps to the abstract choose action. When both majorities exist,
    invariant (E) ensures they agree (stutter step). -/

-- Invariant holds initially
theorem paxos_inv_init : ∀ s, paxos.init s → paxos_inv s := by
  intro s ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hp1, hp2,
         hd11, hd12, hd13, hd21, hd22, hd23⟩
  -- All 29 fields vacuously true at init: flags = false, options = none
  exact {
    hA1 := by simp_all, hA2 := by simp_all, hA3 := by simp_all,
    hA4 := by simp_all, hA5 := by simp_all, hA6 := by simp_all,
    hB1 := by simp_all, hB2 := by simp_all, hB3 := by simp_all,
    hC1 := by simp_all, hC2 := by simp_all, hC3 := by simp_all,
    hD1 := by simp_all, hD2 := by simp_all, hD3 := by simp_all,
    hE  := by simp_all,
    hH1 := by simp_all, hH2 := by simp_all, hH3 := by simp_all,
    hI1 := by simp_all, hI2 := by simp_all, hI3 := by simp_all,
    hJ  := by simp_all,
    hK12 := by simp_all, hK13 := by simp_all,
    hK21 := by simp_all, hK23 := by simp_all,
    hK31 := by simp_all, hK32 := by simp_all,
  }

-- Invariant is preserved by all actions
theorem paxos_inv_next : ∀ s s', paxos_inv s →
    (∃ i, (paxos.actions i).fires s s') → paxos_inv s' := by
  intro s s' hinv ⟨i, hfires⟩
  cases i <;> (simp only [GatedAction.fires] at hfires; dsimp only [paxos] at hfires)
  -- ════════════════════════════════════════
  -- p1b_1_1 : prom1 ← b1, got1b_1_1 ← true
  -- ════════════════════════════════════════
  · obtain ⟨⟨hg1, hg2⟩, rfl⟩ := hfires
    exact {
      hA1 := hinv.hA1, hA2 := hinv.hA2, hA3 := hinv.hA3,
      hA4 := hinv.hA4, hA5 := hinv.hA5, hA6 := hinv.hA6,
      hB1 := hinv.hB1, hB2 := hinv.hB2, hB3 := hinv.hB3,
      hC1 := hinv.hC1, hC2 := hinv.hC2, hC3 := hinv.hC3,
      hD1 := hinv.hD1, hD2 := hinv.hD2, hD3 := hinv.hD3,
      hE := hinv.hE,
      -- prom1 changed to b1, so got1b_2_1 = true → prom1 = b2 would require prom1 = b2,
      -- but gate says prom1 ∈ {none, b1} — contradiction, so got1b_2_1 = false (vacuous)
      hH1 := fun h => by simp [hinv.hH1 h] at hg2,
      hH2 := hinv.hH2, hH3 := hinv.hH3,
      hI1 := hinv.hI1, hI2 := hinv.hI2, hI3 := hinv.hI3,
      hJ := hinv.hJ,
      hK12 := hinv.hK12, hK13 := hinv.hK13,
      hK21 := hinv.hK21, hK23 := hinv.hK23,
      hK31 := hinv.hK31, hK32 := hinv.hK32 }
  -- ════════════════════════════════════════
  -- p1b_1_2 : prom2 ← b1, got1b_1_2 ← true
  -- ════════════════════════════════════════
  · obtain ⟨⟨hg1, hg2⟩, rfl⟩ := hfires
    exact {
      hA1 := hinv.hA1, hA2 := hinv.hA2, hA3 := hinv.hA3,
      hA4 := hinv.hA4, hA5 := hinv.hA5, hA6 := hinv.hA6,
      hB1 := hinv.hB1, hB2 := hinv.hB2, hB3 := hinv.hB3,
      hC1 := hinv.hC1, hC2 := hinv.hC2, hC3 := hinv.hC3,
      hD1 := hinv.hD1, hD2 := hinv.hD2, hD3 := hinv.hD3,
      hE := hinv.hE,
      hH1 := hinv.hH1,
      hH2 := fun h => by simp [hinv.hH2 h] at hg2,
      hH3 := hinv.hH3,
      hI1 := hinv.hI1, hI2 := hinv.hI2, hI3 := hinv.hI3,
      hJ := hinv.hJ,
      hK12 := hinv.hK12, hK13 := hinv.hK13,
      hK21 := hinv.hK21, hK23 := hinv.hK23,
      hK31 := hinv.hK31, hK32 := hinv.hK32 }
  -- ════════════════════════════════════════
  -- p1b_1_3 : prom3 ← b1, got1b_1_3 ← true
  -- ════════════════════════════════════════
  · obtain ⟨⟨hg1, hg2⟩, rfl⟩ := hfires
    exact {
      hA1 := hinv.hA1, hA2 := hinv.hA2, hA3 := hinv.hA3,
      hA4 := hinv.hA4, hA5 := hinv.hA5, hA6 := hinv.hA6,
      hB1 := hinv.hB1, hB2 := hinv.hB2, hB3 := hinv.hB3,
      hC1 := hinv.hC1, hC2 := hinv.hC2, hC3 := hinv.hC3,
      hD1 := hinv.hD1, hD2 := hinv.hD2, hD3 := hinv.hD3,
      hE := hinv.hE,
      hH1 := hinv.hH1, hH2 := hinv.hH2,
      hH3 := fun h => by simp [hinv.hH3 h] at hg2,
      hI1 := hinv.hI1, hI2 := hinv.hI2, hI3 := hinv.hI3,
      hJ := hinv.hJ,
      hK12 := hinv.hK12, hK13 := hinv.hK13,
      hK21 := hinv.hK21, hK23 := hinv.hK23,
      hK31 := hinv.hK31, hK32 := hinv.hK32 }
  -- ════════════════════════════════════════════════════════════
  -- p1b_2_1 : prom1 ← b2, got1b_2_1 ← true, rep2_1 ← acc1
  -- ════════════════════════════════════════════════════════════
  · obtain ⟨hg, rfl⟩ := hfires
    exact {
      hA1 := hinv.hA1, hA2 := hinv.hA2, hA3 := hinv.hA3,
      hA4 := hinv.hA4, hA5 := hinv.hA5, hA6 := hinv.hA6,
      hB1 := hinv.hB1, hB2 := hinv.hB2, hB3 := hinv.hB3,
      -- rep2_1 ← acc1, so b1-entries in rep2_1 come from b1-entries in acc1 (hB1)
      hC1 := fun v h => hinv.hB1 v h,
      hC2 := hinv.hC2, hC3 := hinv.hC3,
      -- got1b_2_1 now true; D1 needs ∃ w, rep2_1 = some (.b1, w) = acc1 — use hI1
      hD1 := fun hp hd _ => hinv.hI1 hp hd,
      hD2 := hinv.hD2, hD3 := hinv.hD3,
      hE := hinv.hE,
      -- got1b_2_1 and prom1 both set simultaneously
      hH1 := fun _ => rfl,
      hH2 := hinv.hH2, hH3 := hinv.hH3,
      hI1 := hinv.hI1, hI2 := hinv.hI2, hI3 := hinv.hI3,
      -- J: gate says got1b_2_1=false; from hinv.hJ got got1b_2_2∧got1b_2_3=true
      hJ := fun hp2 => by
        have h := hinv.hJ hp2
        simp only [hg, majority3, Bool.false_and, Bool.false_or, Bool.and_eq_true] at h
        dsimp only; simp [majority3, h.1, h.2],
      -- got1b_2_1 = true now, so K12/K13 antecedent (got1b_2_1 = false) is vacuous
      hK12 := fun _ h _ => by simp at h,
      hK13 := fun _ h _ => by simp at h,
      hK21 := hinv.hK21, hK23 := hinv.hK23,
      hK31 := hinv.hK31, hK32 := hinv.hK32 }
  -- ════════════════════════════════════════════════════════════
  -- p1b_2_2 : prom2 ← b2, got1b_2_2 ← true, rep2_2 ← acc2
  -- ════════════════════════════════════════════════════════════
  · obtain ⟨hg, rfl⟩ := hfires
    exact {
      hA1 := hinv.hA1, hA2 := hinv.hA2, hA3 := hinv.hA3,
      hA4 := hinv.hA4, hA5 := hinv.hA5, hA6 := hinv.hA6,
      hB1 := hinv.hB1, hB2 := hinv.hB2, hB3 := hinv.hB3,
      hC1 := hinv.hC1,
      hC2 := fun v h => hinv.hB2 v h,
      hC3 := hinv.hC3,
      hD1 := hinv.hD1,
      hD2 := fun hp hd _ => hinv.hI2 hp hd,
      hD3 := hinv.hD3,
      hE := hinv.hE,
      hH1 := hinv.hH1,
      hH2 := fun _ => rfl,
      hH3 := hinv.hH3,
      hI1 := hinv.hI1, hI2 := hinv.hI2, hI3 := hinv.hI3,
      -- J: gate says got1b_2_2=false; from hinv.hJ got got1b_2_1∧got1b_2_3=true
      hJ := fun hp2 => by
        have h := hinv.hJ hp2
        simp only [hg, majority3, Bool.false_and, Bool.and_false,
                   Bool.false_or, Bool.or_false, Bool.and_eq_true] at h
        dsimp only; simp [majority3, h.1, h.2],
      hK12 := hinv.hK12, hK13 := hinv.hK13,
      hK21 := fun _ h _ => by simp at h,
      hK23 := fun _ h _ => by simp at h,
      hK31 := hinv.hK31, hK32 := hinv.hK32 }
  -- ════════════════════════════════════════════════════════════
  -- p1b_2_3 : prom3 ← b2, got1b_2_3 ← true, rep2_3 ← acc3
  -- ════════════════════════════════════════════════════════════
  · obtain ⟨hg, rfl⟩ := hfires
    exact {
      hA1 := hinv.hA1, hA2 := hinv.hA2, hA3 := hinv.hA3,
      hA4 := hinv.hA4, hA5 := hinv.hA5, hA6 := hinv.hA6,
      hB1 := hinv.hB1, hB2 := hinv.hB2, hB3 := hinv.hB3,
      hC1 := hinv.hC1, hC2 := hinv.hC2,
      hC3 := fun v h => hinv.hB3 v h,
      hD1 := hinv.hD1, hD2 := hinv.hD2,
      hD3 := fun hp hd _ => hinv.hI3 hp hd,
      hE := hinv.hE,
      hH1 := hinv.hH1, hH2 := hinv.hH2,
      hH3 := fun _ => rfl,
      hI1 := hinv.hI1, hI2 := hinv.hI2, hI3 := hinv.hI3,
      -- J: gate says got1b_2_3=false; from hinv.hJ got got1b_2_1∧got1b_2_2=true
      hJ := fun hp2 => by
        have h := hinv.hJ hp2
        simp only [hg, majority3, Bool.false_and, Bool.and_false,
                   Bool.false_or, Bool.or_false, Bool.and_eq_true] at h
        dsimp only; simp [majority3, h.1, h.2],
      hK12 := hinv.hK12, hK13 := hinv.hK13,
      hK21 := hinv.hK21, hK23 := hinv.hK23,
      hK31 := fun _ h _ => by simp at h,
      hK32 := fun _ h _ => by simp at h }
  -- ═════════════════════════════════════════════════
  -- p2a_1 : prop1 ← some v  (gate: prop1 = none, majority1 = true)
  -- ═════════════════════════════════════════════════
  · obtain ⟨⟨hg1, hg2⟩, v, rfl⟩ := hfires
    -- When prop1 = none, did2b_1_j = false and acc_j has no b1 entry (by hA, hB)
    exact {
      hA1 := fun _ => by simp,
      hA2 := fun _ => by simp,
      hA3 := fun _ => by simp,
      hA4 := hinv.hA4, hA5 := hinv.hA5, hA6 := hinv.hA6,
      -- If acc_j had a b1 entry, hinv.hB_j would give prop1 = some w ≠ none, contradicting gate
      hB1 := fun w h => by have := hinv.hB1 w h; simp [hg1] at this,
      hB2 := fun w h => by have := hinv.hB2 w h; simp [hg1] at this,
      hB3 := fun w h => by have := hinv.hB3 w h; simp [hg1] at this,
      -- Same for rep2_j via hC
      hC1 := fun w h => by have := hinv.hC1 w h; simp [hg1] at this,
      hC2 := fun w h => by have := hinv.hC2 w h; simp [hg1] at this,
      hC3 := fun w h => by have := hinv.hC3 w h; simp [hg1] at this,
      -- hD unchanged (prop2, got1b_2, rep2, did2b_1 unchanged)
      hD1 := hinv.hD1, hD2 := hinv.hD2, hD3 := hinv.hD3,
      -- hE: majority3 did2b_1 = true → some did2b_1_j = true → prop1 ≠ none, contradicts gate
      hE := fun _ h => by
        have h' : majority3 s.did2b_1_1 s.did2b_1_2 s.did2b_1_3 = true := h
        simp only [majority3, Bool.or_eq_true, Bool.and_eq_true] at h'
        rcases h' with (⟨ha, _⟩ | ⟨ha, _⟩) | ⟨ha, _⟩
        · exact absurd (hinv.hA1 ha) (by simp [hg1])
        · exact absurd (hinv.hA1 ha) (by simp [hg1])
        · exact absurd (hinv.hA2 ha) (by simp [hg1]),
      hH1 := hinv.hH1, hH2 := hinv.hH2, hH3 := hinv.hH3,
      hI1 := hinv.hI1, hI2 := hinv.hI2, hI3 := hinv.hI3,
      hJ := hinv.hJ,
      -- K conclusion is prop1 = prop2; did2b_1_k = true → prop1 ≠ none, contradicts gate
      hK12 := fun _ _ h => by exact absurd (hinv.hA2 h) (by simp [hg1]),
      hK13 := fun _ _ h => by exact absurd (hinv.hA3 h) (by simp [hg1]),
      hK21 := fun _ _ h => by exact absurd (hinv.hA1 h) (by simp [hg1]),
      hK23 := fun _ _ h => by exact absurd (hinv.hA3 h) (by simp [hg1]),
      hK31 := fun _ _ h => by exact absurd (hinv.hA1 h) (by simp [hg1]),
      hK32 := fun _ _ h => by exact absurd (hinv.hA2 h) (by simp [hg1]) }
  -- ═══════════════════════════════════════════════════════════════════════
  -- p2a_2 : prop2 ← some v  (gate: prop2 = none, majority2 = true, + constraint)
  -- ═══════════════════════════════════════════════════════════════════════
  · obtain ⟨⟨hg1, hg2⟩, v, rfl, hconstr⟩ := hfires
    -- Core: quorum intersection gives a witness for prop1 = some v
    -- (used by hE and all K fields)
    have prop1_eq : ∀ (h_d1 : majority3 s.did2b_1_1 s.did2b_1_2 s.did2b_1_3 = true),
        s.prop1 = some v := fun h_d1 => by
      rcases majority3_quorum_intersection _ _ _ _ _ _ h_d1 hg2
        with ⟨hd1, hg21⟩ | ⟨hd2, hg22⟩ | ⟨hd3, hg23⟩
      · obtain ⟨w, hrep⟩ := hinv.hD1 hg1 hd1 hg21
        exact (hconstr w (Or.inl ⟨hg21, hrep⟩)) ▸ hinv.hC1 w hrep
      · obtain ⟨w, hrep⟩ := hinv.hD2 hg1 hd2 hg22
        exact (hconstr w (Or.inr (Or.inl ⟨hg22, hrep⟩))) ▸ hinv.hC2 w hrep
      · obtain ⟨w, hrep⟩ := hinv.hD3 hg1 hd3 hg23
        exact (hconstr w (Or.inr (Or.inr ⟨hg23, hrep⟩))) ▸ hinv.hC3 w hrep
    -- Helper for K fields: got1b_2_j = false + majority2 = true → other two = true
    exact {
      hA1 := hinv.hA1, hA2 := hinv.hA2, hA3 := hinv.hA3,
      hA4 := fun _ => by simp,
      hA5 := fun _ => by simp,
      hA6 := fun _ => by simp,
      hB1 := hinv.hB1, hB2 := hinv.hB2, hB3 := hinv.hB3,
      hC1 := hinv.hC1, hC2 := hinv.hC2, hC3 := hinv.hC3,
      -- prop2 ≠ none now, so D (prop2 = none → ...) vacuously true
      hD1 := fun h _ _ => by simp at h,
      hD2 := fun h _ _ => by simp at h,
      hD3 := fun h _ _ => by simp at h,
      -- Core safety: quorum intersection argument
      hE := fun _ h_d1 => prop1_eq h_d1,
      hH1 := hinv.hH1, hH2 := hinv.hH2, hH3 := hinv.hH3,
      -- prop2 ≠ none now, so I (prop2 = none → ...) vacuously true
      hI1 := fun h _ => by simp at h,
      hI2 := fun h _ => by simp at h,
      hI3 := fun h _ => by simp at h,
      -- J: majority2 was established by gate
      hJ := fun _ => hg2,
      -- K fields: got1b_2_j = false reduces to a 2-node quorum in got1b_2 → witness in D
      hK12 := fun _ hg21_f hdid12 => by
        have : majority3 false s.got1b_2_2 s.got1b_2_3 = true := hg21_f ▸ hg2
        simp [majority3] at this
        obtain ⟨w, hrep⟩ := hinv.hD2 hg1 hdid12 this.1
        exact (hconstr w (Or.inr (Or.inl ⟨this.1, hrep⟩))) ▸ hinv.hC2 w hrep,
      hK13 := fun _ hg21_f hdid13 => by
        have : majority3 false s.got1b_2_2 s.got1b_2_3 = true := hg21_f ▸ hg2
        simp [majority3] at this
        obtain ⟨w, hrep⟩ := hinv.hD3 hg1 hdid13 this.2
        exact (hconstr w (Or.inr (Or.inr ⟨this.2, hrep⟩))) ▸ hinv.hC3 w hrep,
      hK21 := fun _ hg22_f hdid11 => by
        have : majority3 s.got1b_2_1 false s.got1b_2_3 = true := hg22_f ▸ hg2
        simp [majority3] at this
        obtain ⟨w, hrep⟩ := hinv.hD1 hg1 hdid11 this.1
        exact (hconstr w (Or.inl ⟨this.1, hrep⟩)) ▸ hinv.hC1 w hrep,
      hK23 := fun _ hg22_f hdid13 => by
        have : majority3 s.got1b_2_1 false s.got1b_2_3 = true := hg22_f ▸ hg2
        simp [majority3] at this
        obtain ⟨w, hrep⟩ := hinv.hD3 hg1 hdid13 this.2
        exact (hconstr w (Or.inr (Or.inr ⟨this.2, hrep⟩))) ▸ hinv.hC3 w hrep,
      hK31 := fun _ hg23_f hdid11 => by
        have : majority3 s.got1b_2_1 s.got1b_2_2 false = true := hg23_f ▸ hg2
        simp [majority3] at this
        obtain ⟨w, hrep⟩ := hinv.hD1 hg1 hdid11 this.1
        exact (hconstr w (Or.inl ⟨this.1, hrep⟩)) ▸ hinv.hC1 w hrep,
      hK32 := fun _ hg23_f hdid12 => by
        have : majority3 s.got1b_2_1 s.got1b_2_2 false = true := hg23_f ▸ hg2
        simp [majority3] at this
        obtain ⟨w, hrep⟩ := hinv.hD2 hg1 hdid12 this.2
        exact (hconstr w (Or.inr (Or.inl ⟨this.2, hrep⟩))) ▸ hinv.hC2 w hrep }
  -- ════════════════════════════════════════════════════════════════════
  -- p2b_1_1 : acc1 ← (.b1,v), prom1 ← b1, did2b_1_1 ← true
  --           (gate: did2b_1_1=false, prom1 ∈ {none,b1}, prop1 = some v)
  -- ════════════════════════════════════════════════════════════════════
  · obtain ⟨⟨hg1, hg2⟩, v, hp1, rfl⟩ := hfires
    -- Gate (prom1 ∈ {none,b1}) + hH1 (got1b_2_1=true → prom1=b2) → got1b_2_1 = false
    have hg21_f : s.got1b_2_1 = false := by
      cases h : s.got1b_2_1
      · rfl
      · exact absurd (hinv.hH1 h) (by rcases hg2 with h' | h' <;> simp [h'])
    exact {
      -- did2b_1_1 = true now, and prop1 = some v ≠ none
      hA1 := fun _ => by simp [hp1],
      hA2 := hinv.hA2, hA3 := hinv.hA3,
      hA4 := hinv.hA4, hA5 := hinv.hA5, hA6 := hinv.hA6,
      -- acc1 = some (.b1, v), prop1 = some v
      hB1 := fun w h => by simp_all,
      hB2 := hinv.hB2, hB3 := hinv.hB3,
      hC1 := hinv.hC1, hC2 := hinv.hC2, hC3 := hinv.hC3,
      -- D1 vacuous: got1b_2_1 = true would need prom1 = b2 (hH1), contradicts gate
      hD1 := fun _ _ h => by simp [hinv.hH1 h] at hg2,
      hD2 := hinv.hD2, hD3 := hinv.hD3,
      -- hE: new majority involves index 1 (did2b_1_1 now true); overlap must be at 2 or 3;
      -- got1b_2_1=false so use K12/K13 for the overlap acceptor
      hE := fun h_p2 h_maj => by
        have h_maj' : majority3 true s.did2b_1_2 s.did2b_1_3 = true := h_maj
        simp only [majority3, Bool.true_and, Bool.or_eq_true, Bool.and_eq_true] at h_maj'
        rcases h_maj' with (h2 | h3) | ⟨h2, _⟩
        · exact hinv.hK12 h_p2 hg21_f h2
        · exact hinv.hK13 h_p2 hg21_f h3
        · exact hinv.hK12 h_p2 hg21_f h2,
      -- prom1 changed to b1; got1b_2_1=false (derived above) keeps hH1 vacuous
      hH1 := fun h => by simp [hinv.hH1 h] at hg2,
      hH2 := hinv.hH2, hH3 := hinv.hH3,
      -- I1: prop2=none → did2b_1_1=true → ∃ w, acc1=some(.b1,w). acc1 = some(.b1,v). ✓
      hI1 := fun _ _ => ⟨v, rfl⟩,
      hI2 := hinv.hI2, hI3 := hinv.hI3,
      hJ := hinv.hJ,
      hK12 := fun h1 h2 h3 => hinv.hK12 h1 h2 h3,
      hK13 := fun h1 h2 h3 => hinv.hK13 h1 h2 h3,
      -- K21/K23/K31/K32: got1b_2_1=false + another false → majority3=false, contradicts hJ
      hK21 := fun h1 h2 _ => by
        have h2' : s.got1b_2_2 = false := h2
        have hJ := hinv.hJ h1; simp [hg21_f, h2', majority3] at hJ,
      hK23 := fun h1 h2 _ => by
        have h2' : s.got1b_2_2 = false := h2
        have hJ := hinv.hJ h1; simp [hg21_f, h2', majority3] at hJ,
      hK31 := fun h1 h3 _ => by
        have h3' : s.got1b_2_3 = false := h3
        have hJ := hinv.hJ h1; simp [hg21_f, h3', majority3] at hJ,
      hK32 := fun h1 h3 _ => by
        have h3' : s.got1b_2_3 = false := h3
        have hJ := hinv.hJ h1; simp [hg21_f, h3', majority3] at hJ }
  -- ════════════════════════════════════════════════════════════════════
  -- p2b_1_2 : acc2 ← (.b1,v), prom2 ← b1, did2b_1_2 ← true
  -- ════════════════════════════════════════════════════════════════════
  · obtain ⟨⟨hg1, hg2⟩, v, hp1, rfl⟩ := hfires
    have hg22_f : s.got1b_2_2 = false := by
      cases h : s.got1b_2_2
      · rfl
      · exact absurd (hinv.hH2 h) (by rcases hg2 with h' | h' <;> simp [h'])
    exact {
      hA1 := hinv.hA1,
      hA2 := fun _ => by simp [hp1],
      hA3 := hinv.hA3,
      hA4 := hinv.hA4, hA5 := hinv.hA5, hA6 := hinv.hA6,
      hB1 := hinv.hB1,
      hB2 := fun w h => by simp_all,
      hB3 := hinv.hB3,
      hC1 := hinv.hC1, hC2 := hinv.hC2, hC3 := hinv.hC3,
      hD1 := hinv.hD1,
      hD2 := fun _ _ h => by simp [hinv.hH2 h] at hg2,
      hD3 := hinv.hD3,
      hE := fun h_p2 h_maj => by
        have h_maj' : majority3 s.did2b_1_1 true s.did2b_1_3 = true := h_maj
        simp only [majority3, Bool.true_and, Bool.and_true, Bool.or_eq_true, Bool.and_eq_true] at h_maj'
        rcases h_maj' with (h1 | ⟨h1, _⟩) | h3
        · exact hinv.hK21 h_p2 hg22_f h1
        · exact hinv.hK21 h_p2 hg22_f h1
        · exact hinv.hK23 h_p2 hg22_f h3,
      hH1 := hinv.hH1,
      hH2 := fun h => by simp [hinv.hH2 h] at hg2,
      hH3 := hinv.hH3,
      hI1 := hinv.hI1,
      hI2 := fun _ _ => ⟨v, rfl⟩,
      hI3 := hinv.hI3,
      hJ := hinv.hJ,
      hK12 := fun h1 h2 _ => by
        have h2' : s.got1b_2_1 = false := h2
        have hJ := hinv.hJ h1; simp [h2', hg22_f, majority3] at hJ,
      hK13 := fun h1 h2 h3 => hinv.hK13 h1 h2 h3,
      hK21 := fun h1 h2 h3 => hinv.hK21 h1 h2 h3,
      hK23 := fun h1 h2 h3 => hinv.hK23 h1 h2 h3,
      hK31 := fun h1 h3 _ => by
        have h3' : s.got1b_2_3 = false := h3
        have hJ := hinv.hJ h1; simp [hg22_f, h3', majority3] at hJ,
      hK32 := fun h1 h3 _ => by
        have h3' : s.got1b_2_3 = false := h3
        have hJ := hinv.hJ h1; simp [hg22_f, h3', majority3] at hJ }
  -- ════════════════════════════════════════════════════════════════════
  -- p2b_1_3 : acc3 ← (.b1,v), prom3 ← b1, did2b_1_3 ← true
  -- ════════════════════════════════════════════════════════════════════
  · obtain ⟨⟨hg1, hg2⟩, v, hp1, rfl⟩ := hfires
    have hg23_f : s.got1b_2_3 = false := by
      cases h : s.got1b_2_3
      · rfl
      · exact absurd (hinv.hH3 h) (by rcases hg2 with h' | h' <;> simp [h'])
    exact {
      hA1 := hinv.hA1, hA2 := hinv.hA2,
      hA3 := fun _ => by simp [hp1],
      hA4 := hinv.hA4, hA5 := hinv.hA5, hA6 := hinv.hA6,
      hB1 := hinv.hB1, hB2 := hinv.hB2,
      hB3 := fun w h => by simp_all,
      hC1 := hinv.hC1, hC2 := hinv.hC2, hC3 := hinv.hC3,
      hD1 := hinv.hD1, hD2 := hinv.hD2,
      hD3 := fun _ _ h => by simp [hinv.hH3 h] at hg2,
      hE := fun h_p2 h_maj => by
        have h_maj' : majority3 s.did2b_1_1 s.did2b_1_2 true = true := h_maj
        simp only [majority3, Bool.and_true, Bool.or_eq_true, Bool.and_eq_true] at h_maj'
        rcases h_maj' with (⟨h1, _⟩ | h1) | h2
        · exact hinv.hK31 h_p2 hg23_f h1
        · exact hinv.hK31 h_p2 hg23_f h1
        · exact hinv.hK32 h_p2 hg23_f h2,
      hH1 := hinv.hH1, hH2 := hinv.hH2,
      hH3 := fun h => by simp [hinv.hH3 h] at hg2,
      hI1 := hinv.hI1, hI2 := hinv.hI2,
      hI3 := fun _ _ => ⟨v, rfl⟩,
      hJ := hinv.hJ,
      hK12 := fun h1 h2 h3 => hinv.hK12 h1 h2 h3,
      hK13 := fun h1 h2 _ => by
        have h2' : s.got1b_2_1 = false := h2
        have hJ := hinv.hJ h1; simp [h2', hg23_f, majority3] at hJ,
      hK21 := fun h1 h2 h3 => hinv.hK21 h1 h2 h3,
      hK23 := fun h1 h2 _ => by
        have h2' : s.got1b_2_2 = false := h2
        have hJ := hinv.hJ h1; simp [h2', hg23_f, majority3] at hJ,
      hK31 := fun h1 h3 h4 => hinv.hK31 h1 h3 h4,
      hK32 := fun h1 h3 h4 => hinv.hK32 h1 h3 h4 }
  -- ══════════════════════════════════════════════════════════════
  -- p2b_2_1 : acc1 ← (.b2,v), prom1 ← b2, did2b_2_1 ← true
  --           (gate: did2b_2_1=false, prop2 = some v)
  -- ══════════════════════════════════════════════════════════════
  · obtain ⟨_hg, v, hp2, rfl⟩ := hfires
    exact {
      hA1 := hinv.hA1, hA2 := hinv.hA2, hA3 := hinv.hA3,
      -- did2b_2_1 = true and prop2 = some v ≠ none
      hA4 := fun _ => by simp [hp2],
      hA5 := hinv.hA5, hA6 := hinv.hA6,
      -- acc1 = some (.b2, v); no b1 entry, so hB1 vacuously true
      hB1 := fun _ h => by simp at h,
      hB2 := hinv.hB2, hB3 := hinv.hB3,
      hC1 := hinv.hC1, hC2 := hinv.hC2, hC3 := hinv.hC3,
      -- D vacuous: prop2 ≠ none
      hD1 := fun h _ _ => by simp [hp2] at h,
      hD2 := fun h _ _ => by simp [hp2] at h,
      hD3 := fun h _ _ => by simp [hp2] at h,
      hE := hinv.hE,
      -- prom1 ← b2; got1b_2_1 → prom1 = b2 still holds
      hH1 := fun _ => rfl,
      hH2 := hinv.hH2, hH3 := hinv.hH3,
      -- I vacuous: prop2 ≠ none
      hI1 := fun h _ => by simp [hp2] at h,
      hI2 := fun h _ => by simp [hp2] at h,
      hI3 := fun h _ => by simp [hp2] at h,
      hJ := hinv.hJ,
      hK12 := hinv.hK12, hK13 := hinv.hK13,
      hK21 := hinv.hK21, hK23 := hinv.hK23,
      hK31 := hinv.hK31, hK32 := hinv.hK32 }
  -- ══════════════════════════════════════════════════════════════
  -- p2b_2_2 : acc2 ← (.b2,v), prom2 ← b2, did2b_2_2 ← true
  -- ══════════════════════════════════════════════════════════════
  · obtain ⟨_hg, v, hp2, rfl⟩ := hfires
    exact {
      hA1 := hinv.hA1, hA2 := hinv.hA2, hA3 := hinv.hA3,
      hA4 := hinv.hA4,
      hA5 := fun _ => by simp [hp2],
      hA6 := hinv.hA6,
      hB1 := hinv.hB1,
      hB2 := fun _ h => by simp at h,
      hB3 := hinv.hB3,
      hC1 := hinv.hC1, hC2 := hinv.hC2, hC3 := hinv.hC3,
      hD1 := fun h _ _ => by simp [hp2] at h,
      hD2 := fun h _ _ => by simp [hp2] at h,
      hD3 := fun h _ _ => by simp [hp2] at h,
      hE := hinv.hE,
      hH1 := hinv.hH1,
      hH2 := fun _ => rfl,
      hH3 := hinv.hH3,
      hI1 := fun h _ => by simp [hp2] at h,
      hI2 := fun h _ => by simp [hp2] at h,
      hI3 := fun h _ => by simp [hp2] at h,
      hJ := hinv.hJ,
      hK12 := hinv.hK12, hK13 := hinv.hK13,
      hK21 := hinv.hK21, hK23 := hinv.hK23,
      hK31 := hinv.hK31, hK32 := hinv.hK32 }
  -- ══════════════════════════════════════════════════════════════
  -- p2b_2_3 : acc3 ← (.b2,v), prom3 ← b2, did2b_2_3 ← true
  -- ══════════════════════════════════════════════════════════════
  · obtain ⟨_hg, v, hp2, rfl⟩ := hfires
    exact {
      hA1 := hinv.hA1, hA2 := hinv.hA2, hA3 := hinv.hA3,
      hA4 := hinv.hA4, hA5 := hinv.hA5,
      hA6 := fun _ => by simp [hp2],
      hB1 := hinv.hB1, hB2 := hinv.hB2,
      hB3 := fun _ h => by simp at h,
      hC1 := hinv.hC1, hC2 := hinv.hC2, hC3 := hinv.hC3,
      hD1 := fun h _ _ => by simp [hp2] at h,
      hD2 := fun h _ _ => by simp [hp2] at h,
      hD3 := fun h _ _ => by simp [hp2] at h,
      hE := hinv.hE,
      hH1 := hinv.hH1, hH2 := hinv.hH2,
      hH3 := fun _ => rfl,
      hI1 := fun h _ => by simp [hp2] at h,
      hI2 := fun h _ => by simp [hp2] at h,
      hI3 := fun h _ => by simp [hp2] at h,
      hJ := hinv.hJ,
      hK12 := hinv.hK12, hK13 := hinv.hK13,
      hK21 := hinv.hK21, hK23 := hinv.hK23,
      hK31 := hinv.hK31, hK32 := hinv.hK32 }

-- Initial states map correctly
theorem paxos_init_preserved : ∀ s, paxos.init s →
    consensus.init (paxos_ref s) := by
  intro s ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
         hd11, hd12, hd13, hd21, hd22, hd23⟩
  simp [paxos_ref, consensus, majority3, hd11, hd12, hd13, hd21, hd22, hd23]

-- Step simulation: each concrete step maps to an abstract step or stutters
-- (The interesting cases are p2b creating a new majority → abstract choose)
theorem paxos_step_sim : ∀ s s', paxos_inv s →
    (∃ i, (paxos.actions i).fires s s') →
    (∃ i, (consensus.actions i).fires (paxos_ref s) (paxos_ref s')) ∨
      paxos_ref s = paxos_ref s' := by
  intro s s' hinv ⟨i, hfires⟩
  have hinv' : paxos_inv s' := paxos_inv_next s s' hinv ⟨i, hfires⟩
  have hprop2_of_maj2 :
      majority3 s.did2b_2_1 s.did2b_2_2 s.did2b_2_3 = true → s.prop2 ≠ none := by
    intro hmaj2
    simp only [majority3, Bool.or_eq_true, Bool.and_eq_true] at hmaj2
    rcases hmaj2 with (⟨h21, _⟩ | ⟨h21, _⟩) | ⟨h22, _⟩
    · exact hinv.hA4 h21
    · exact hinv.hA4 h21
    · exact hinv.hA5 h22
  cases i <;> (simp only [GatedAction.fires] at hfires; dsimp only [paxos] at hfires)
  -- p1b_1_1
  · obtain ⟨_, rfl⟩ := hfires
    right; rfl
  -- p1b_1_2
  · obtain ⟨_, rfl⟩ := hfires
    right; rfl
  -- p1b_1_3
  · obtain ⟨_, rfl⟩ := hfires
    right; rfl
  -- p1b_2_1
  · obtain ⟨_, rfl⟩ := hfires
    right; rfl
  -- p1b_2_2
  · obtain ⟨_, rfl⟩ := hfires
    right; rfl
  -- p1b_2_3
  · obtain ⟨_, rfl⟩ := hfires
    right; rfl
  -- p2a_1
  · obtain ⟨⟨hg1, _hg2⟩, v, rfl⟩ := hfires
    have hmaj1 : majority3 s.did2b_1_1 s.did2b_1_2 s.did2b_1_3 = false := by
      cases h : majority3 s.did2b_1_1 s.did2b_1_2 s.did2b_1_3 <;> simp [h]
      have h' : majority3 s.did2b_1_1 s.did2b_1_2 s.did2b_1_3 = true := h
      simp only [majority3, Bool.or_eq_true, Bool.and_eq_true] at h'
      rcases h' with (⟨h11, _⟩ | ⟨h11, _⟩) | ⟨h12, _⟩
      · exact absurd (hinv.hA1 h11) (by simp [hg1])
      · exact absurd (hinv.hA1 h11) (by simp [hg1])
      · exact absurd (hinv.hA2 h12) (by simp [hg1])
    right
    simp [paxos_ref, hmaj1]
  -- p2a_2
  · obtain ⟨⟨hg1, _hg2⟩, v, rfl, _hconstr⟩ := hfires
    by_cases hmaj1 : majority3 s.did2b_1_1 s.did2b_1_2 s.did2b_1_3 = true
    · right
      simp [paxos_ref, hmaj1]
    · by_cases hmaj2 : majority3 s.did2b_2_1 s.did2b_2_2 s.did2b_2_3 = true
      · left
        cases v with
        | v1 =>
            refine ⟨.choose1, ?_, ?_⟩ <;>
            simp [consensus, paxos_ref, hmaj1, hmaj2, hg1]
        | v2 =>
            refine ⟨.choose2, ?_, ?_⟩ <;>
            simp [consensus, paxos_ref, hmaj1, hmaj2, hg1]
      · right
        simp [paxos_ref, hmaj1, hmaj2, hg1]
  -- p2b_1_1
  · obtain ⟨⟨hd11f, _⟩, v, hp1, rfl⟩ := hfires
    by_cases hmaj1 : majority3 s.did2b_1_1 s.did2b_1_2 s.did2b_1_3 = true
    · right
      have hmaj1' : majority3 true s.did2b_1_2 s.did2b_1_3 = true := by
        have h23 : s.did2b_1_2 = true ∧ s.did2b_1_3 = true := by
          simpa [majority3, hd11f] using hmaj1
        simp [majority3, h23.1, h23.2]
      simp [paxos_ref, hmaj1, hmaj1']
    · by_cases hmaj1' : majority3 true s.did2b_1_2 s.did2b_1_3 = true
      · by_cases hmaj2 : majority3 s.did2b_2_1 s.did2b_2_2 s.did2b_2_3 = true
        · right
          have hprop2 : s.prop2 ≠ none := hprop2_of_maj2 hmaj2
          have hEq : s.prop1 = s.prop2 := hinv'.hE hprop2 hmaj1'
          have hEqv : s.prop2 = some v := by simpa [hp1] using hEq.symm
          simp [paxos_ref, hmaj1, hmaj1', hmaj2, hEqv, hp1]
        · left
          cases v with
          | v1 =>
              refine ⟨.choose1, ?_, ?_⟩ <;>
              simp [consensus, paxos_ref, hmaj1, hmaj1', hmaj2, hp1]
          | v2 =>
              refine ⟨.choose2, ?_, ?_⟩ <;>
              simp [consensus, paxos_ref, hmaj1, hmaj1', hmaj2, hp1]
      · right
        simp [paxos_ref, hmaj1, hmaj1', hp1]
  -- p2b_1_2
  · obtain ⟨⟨hd12f, _⟩, v, hp1, rfl⟩ := hfires
    by_cases hmaj1 : majority3 s.did2b_1_1 s.did2b_1_2 s.did2b_1_3 = true
    · right
      have hmaj1' : majority3 s.did2b_1_1 true s.did2b_1_3 = true := by
        have h13 : s.did2b_1_1 = true ∧ s.did2b_1_3 = true := by
          simpa [majority3, hd12f] using hmaj1
        simp [majority3, h13.1, h13.2]
      simp [paxos_ref, hmaj1, hmaj1']
    · by_cases hmaj1' : majority3 s.did2b_1_1 true s.did2b_1_3 = true
      · by_cases hmaj2 : majority3 s.did2b_2_1 s.did2b_2_2 s.did2b_2_3 = true
        · right
          have hprop2 : s.prop2 ≠ none := hprop2_of_maj2 hmaj2
          have hEq : s.prop1 = s.prop2 := hinv'.hE hprop2 hmaj1'
          have hEqv : s.prop2 = some v := by simpa [hp1] using hEq.symm
          simp [paxos_ref, hmaj1, hmaj1', hmaj2, hEqv, hp1]
        · left
          cases v with
          | v1 =>
              refine ⟨.choose1, ?_, ?_⟩ <;>
              simp [consensus, paxos_ref, hmaj1, hmaj1', hmaj2, hp1]
          | v2 =>
              refine ⟨.choose2, ?_, ?_⟩ <;>
              simp [consensus, paxos_ref, hmaj1, hmaj1', hmaj2, hp1]
      · right
        simp [paxos_ref, hmaj1, hmaj1', hp1]
  -- p2b_1_3
  · obtain ⟨⟨hd13f, _⟩, v, hp1, rfl⟩ := hfires
    by_cases hmaj1 : majority3 s.did2b_1_1 s.did2b_1_2 s.did2b_1_3 = true
    · right
      have hmaj1' : majority3 s.did2b_1_1 s.did2b_1_2 true = true := by
        have h12 : s.did2b_1_1 = true ∧ s.did2b_1_2 = true := by
          simpa [majority3, hd13f] using hmaj1
        simp [majority3, h12.1, h12.2]
      simp [paxos_ref, hmaj1, hmaj1']
    · by_cases hmaj1' : majority3 s.did2b_1_1 s.did2b_1_2 true = true
      · by_cases hmaj2 : majority3 s.did2b_2_1 s.did2b_2_2 s.did2b_2_3 = true
        · right
          have hprop2 : s.prop2 ≠ none := hprop2_of_maj2 hmaj2
          have hEq : s.prop1 = s.prop2 := hinv'.hE hprop2 hmaj1'
          have hEqv : s.prop2 = some v := by simpa [hp1] using hEq.symm
          simp [paxos_ref, hmaj1, hmaj1', hmaj2, hEqv, hp1]
        · left
          cases v with
          | v1 =>
              refine ⟨.choose1, ?_, ?_⟩ <;>
              simp [consensus, paxos_ref, hmaj1, hmaj1', hmaj2, hp1]
          | v2 =>
              refine ⟨.choose2, ?_, ?_⟩ <;>
              simp [consensus, paxos_ref, hmaj1, hmaj1', hmaj2, hp1]
      · right
        simp [paxos_ref, hmaj1, hmaj1', hp1]
  -- p2b_2_1
  · obtain ⟨hd21f, v, hp2, rfl⟩ := hfires
    by_cases hmaj1 : majority3 s.did2b_1_1 s.did2b_1_2 s.did2b_1_3 = true
    · right
      simp [paxos_ref, hmaj1]
    · by_cases hmaj2 : majority3 s.did2b_2_1 s.did2b_2_2 s.did2b_2_3 = true
      · right
        have hmaj2' : majority3 true s.did2b_2_2 s.did2b_2_3 = true := by
          have h23 : s.did2b_2_2 = true ∧ s.did2b_2_3 = true := by
            simpa [majority3, hd21f] using hmaj2
          simp [majority3, h23.1, h23.2]
        simp [paxos_ref, hmaj1, hmaj2, hmaj2', hp2]
      · by_cases hmaj2' : majority3 true s.did2b_2_2 s.did2b_2_3 = true
        · left
          cases v with
          | v1 =>
              refine ⟨.choose1, ?_, ?_⟩ <;>
              simp [consensus, paxos_ref, hmaj1, hmaj2, hmaj2', hp2]
          | v2 =>
              refine ⟨.choose2, ?_, ?_⟩ <;>
              simp [consensus, paxos_ref, hmaj1, hmaj2, hmaj2', hp2]
        · right
          simp [paxos_ref, hmaj1, hmaj2, hmaj2', hp2]
  -- p2b_2_2
  · obtain ⟨hd22f, v, hp2, rfl⟩ := hfires
    by_cases hmaj1 : majority3 s.did2b_1_1 s.did2b_1_2 s.did2b_1_3 = true
    · right
      simp [paxos_ref, hmaj1]
    · by_cases hmaj2 : majority3 s.did2b_2_1 s.did2b_2_2 s.did2b_2_3 = true
      · right
        have hmaj2' : majority3 s.did2b_2_1 true s.did2b_2_3 = true := by
          have h13 : s.did2b_2_1 = true ∧ s.did2b_2_3 = true := by
            simpa [majority3, hd22f] using hmaj2
          simp [majority3, h13.1, h13.2]
        simp [paxos_ref, hmaj1, hmaj2, hmaj2', hp2]
      · by_cases hmaj2' : majority3 s.did2b_2_1 true s.did2b_2_3 = true
        · left
          cases v with
          | v1 =>
              refine ⟨.choose1, ?_, ?_⟩ <;>
              simp [consensus, paxos_ref, hmaj1, hmaj2, hmaj2', hp2]
          | v2 =>
              refine ⟨.choose2, ?_, ?_⟩ <;>
              simp [consensus, paxos_ref, hmaj1, hmaj2, hmaj2', hp2]
        · right
          simp [paxos_ref, hmaj1, hmaj2, hmaj2', hp2]
  -- p2b_2_3
  · obtain ⟨hd23f, v, hp2, rfl⟩ := hfires
    by_cases hmaj1 : majority3 s.did2b_1_1 s.did2b_1_2 s.did2b_1_3 = true
    · right
      simp [paxos_ref, hmaj1]
    · by_cases hmaj2 : majority3 s.did2b_2_1 s.did2b_2_2 s.did2b_2_3 = true
      · right
        have hmaj2' : majority3 s.did2b_2_1 s.did2b_2_2 true = true := by
          have h12 : s.did2b_2_1 = true ∧ s.did2b_2_2 = true := by
            simpa [majority3, hd23f] using hmaj2
          simp [majority3, h12.1, h12.2]
        simp [paxos_ref, hmaj1, hmaj2, hmaj2', hp2]
      · by_cases hmaj2' : majority3 s.did2b_2_1 s.did2b_2_2 true = true
        · left
          cases v with
          | v1 =>
              refine ⟨.choose1, ?_, ?_⟩ <;>
              simp [consensus, paxos_ref, hmaj1, hmaj2, hmaj2', hp2]
          | v2 =>
              refine ⟨.choose2, ?_, ?_⟩ <;>
              simp [consensus, paxos_ref, hmaj1, hmaj2, hmaj2', hp2]
        · right
          simp [paxos_ref, hmaj1, hmaj2, hmaj2', hp2]

-- The main refinement theorem
theorem paxos_refines_consensus :
    refines_via paxos_ref paxos.toSpec.safety consensus.toSpec.safety_stutter := by
  apply refinement_mapping_stutter_with_invariant paxos.toSpec consensus.toSpec
    paxos_ref paxos_inv
  · exact paxos_inv_init
  · exact fun s s' hinv hstep => paxos_inv_next s s' hinv hstep
  · exact paxos_init_preserved
  · exact paxos_step_sim

end Paxos
