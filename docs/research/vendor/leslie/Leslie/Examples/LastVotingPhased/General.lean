import Leslie.Examples.LastVotingPhased.Defs

/-! ## General-n LastVoting

    Generalizes the n = 3 proof to arbitrary n > 0.
    See `Defs.lean` for the shared type definitions. -/

open TLA

namespace LastVotingPhased

/-! ## General-n LastVoting

    The following section generalizes the n = 3 proof to arbitrary n > 0.
    Types (`LState`, `LVState`, `LVMsg`, `Value`) are reused from the
    n = 3 section since they do not depend on the process count.

    The key change: `hasMaj3` (count ≥ 2) becomes `hasMajG` (count * 2 > n),
    and quorum intersection uses `filter_disjoint_length_le` from `Round.lean`
    instead of case analysis on `Fin 3`. -/

namespace Gen

variable (n : Nat) (hn : n > 0)

/-! ### General-n helpers -/

/-- Coordinator of ballot `r` with `n` processes. -/
def coordinatorG (r : Nat) : Fin n := ⟨r % n, Nat.mod_lt r hn⟩

/-- Strict majority predicate for `n` processes: more than half satisfy `p`. -/
def hasMajG (p : Fin n → Bool) : Bool :=
  decide (((List.finRange n).filter (fun r => p r)).length * 2 > n)

/-- Extract the highest-ballot lastVote from promises (general n). -/
def highestVoteG (promises : Fin n → Option LVMsg) : Option Value :=
  let collected := (List.finRange n).filterMap fun p =>
    match promises p with
    | some (.promise (some vb)) => some vb
    | _ => none
  match collected with
  | [] => none
  | (v, b) :: rest =>
    some (rest.foldl (fun best cur => if cur.2 > best.2 then cur else best) (v, b)).1

/-- Uniform message type for all phases (same as n = 3).
    Note: explicitly not parameterized by n. -/
abbrev LVMsgsG : PhaseMessages 4 := LVMsgs

/-! ### General-n phase definitions -/

def lvPhase0G : Phase (Fin n) LVState LVMsg where
  send := fun p s =>
    if p = coordinatorG n hn s.roundNum then .prepare else .skip
  update := fun p s msgs =>
    let c := coordinatorG n hn s.roundNum
    let heardPrepare := match msgs c with | some .prepare => true | _ => false
    { s with core := { s.core with
        prepared := heardPrepare
        accepted := false
        proposal := if p = c then none else s.core.proposal } }

def lvPhase1G : Phase (Fin n) LVState LVMsg where
  send := fun _p s => .promise s.core.lastVote
  update := fun p s msgs =>
    if p = coordinatorG n hn s.roundNum then
      let promiseCount := (List.finRange n).filter (fun q =>
        match msgs q with | some (.promise _) => true | _ => false) |>.length
      if promiseCount * 2 > n then
        let collected := (List.finRange n).filterMap fun q =>
          match msgs q with
          | some (.promise (some vb)) => some vb
          | _ => none
        let prop := match collected with
          | [] => defaultValue
          | (v, b) :: rest =>
            (rest.foldl (fun best cur => if cur.2 > best.2 then cur else best) (v, b)).1
        { s with core := { s.core with proposal := some prop } }
      else { s with core := { s.core with proposal := none } }
    else s

def lvPhase2G : Phase (Fin n) LVState LVMsg where
  send := fun p s =>
    if p = coordinatorG n hn s.roundNum then
      match s.core.proposal with | some v => .propose v | none => .skip
    else .skip
  update := fun _p s msgs =>
    let c := coordinatorG n hn s.roundNum
    match msgs c with
    | some (.propose v) =>
      { s with core := { s.core with lastVote := some (v, s.roundNum), accepted := true } }
    | _ => s

def lvPhase3G : Phase (Fin n) LVState LVMsg where
  send := fun _p s =>
    if s.core.accepted then
      match s.core.lastVote with
      | some (v, _) => .accepted v
      | none => .notAccepted
    else .notAccepted
  update := fun _p s msgs =>
    let acceptors : Fin n → Bool := fun q =>
      match msgs q with | some (.accepted _) => true | _ => false
    let core' :=
      if hasMajG n acceptors then
        let decidedVal := (List.finRange n).filterMap (fun q =>
          match msgs q with | some (.accepted v) => some v | _ => none) |>.head?
        match decidedVal with
        | some v => { s.core with decided := some v, prepared := false, accepted := false }
        | none => { s.core with prepared := false, accepted := false }
      else { s.core with prepared := false, accepted := false }
    { roundNum := s.roundNum + 1, core := core' }

/-! ### General-n algorithm and spec -/

def lvAlgG : PhaseRoundAlg (Fin n) LVState 4 LVMsgsG where
  init := fun _p s =>
    s.roundNum = 0 ∧
    s.core = { lastVote := none, decided := none,
               prepared := false, accepted := false,
               proposal := none }
  phases := fun i =>
    if i.val = 0 then lvPhase0G n hn
    else if i.val = 1 then lvPhase1G n hn
    else if i.val = 2 then lvPhase2G n hn
    else lvPhase3G n

def lvCommG : PhaseCommPred (Fin n) 4 := fun _ _ _ => True

def lvSpecG : PhaseRoundSpec (Fin n) LVState 4 LVMsgsG where
  alg := lvAlgG n hn
  comm := lvCommG n

def lvLeslieSpecG : Spec (PhaseRoundState (Fin n) LVState 4) :=
  (lvSpecG n hn).toSpec (by omega)

/-! ### General-n safety property -/

def agreementG (s : PhaseRoundState (Fin n) LVState 4) : Prop :=
  ∀ (p q : Fin n) (v w : Value),
    (s.locals p).core.decided = some v →
    (s.locals q).core.decided = some w →
    v = w

/-! ### General-n invariant (10 conjuncts, A-I)

    The key change from the old 9-conjunct invariant: G1+G2 (pairwise ballot
    domination + majority v-voters) is replaced by the "safe ballot"
    formulation (∃ b_safe with a gap), and a new conjunct I (same-ballot
    agreement) is added. This formulation is correct for all n ≥ 1. -/

def lv_inv_gen (s : PhaseRoundState (Fin n) LVState 4) : Prop :=
  -- (A) Agreement
  agreementG n s ∧
  -- (B) Accepted consistency
  (∀ p : Fin n, (s.locals p).core.accepted = true →
    ∃ v b, (s.locals p).core.lastVote = some (v, b) ∧ b = s.round) ∧
  -- (C) Phase 3 consistency
  (s.phase = ⟨3, by omega⟩ →
    ∀ p : Fin n, (s.locals p).core.accepted = true →
    ∃ v, (s.locals p).core.lastVote = some (v, s.round)) ∧
  -- (D) Decision-proposal consistency
  (∀ p : Fin n, ∀ v, (s.locals p).core.decided = some v →
    s.phase = ⟨3, by omega⟩ →
    hasMajG n (fun q => (s.locals q).core.accepted) = true →
    ∀ q : Fin n, (s.locals q).core.accepted = true →
    ∃ w, (s.locals q).core.lastVote = some (w, s.round) ∧ w = v) ∧
  -- (E) Round synchronization
  (∀ p : Fin n, (s.locals p).roundNum = s.round) ∧
  -- (F') Acceptance only at phase 3
  (∀ p : Fin n, (s.locals p).core.accepted = true → s.phase = ⟨3, by omega⟩) ∧
  -- (F) Uniform value at phase 3
  (s.phase = ⟨3, by omega⟩ →
    ∀ (p q : Fin n) (vp vq : Value),
    (s.locals p).core.accepted = true →
    (s.locals q).core.accepted = true →
    (s.locals p).core.lastVote = some (vp, s.round) →
    (s.locals q).core.lastVote = some (vq, s.round) →
    vp = vq) ∧
  -- (G) Safe value property: decided value has a "safety gap"
  (∀ p v, (s.locals p).core.decided = some v →
    -- G1: ∃ b_safe such that non-v votes < b_safe and majority v-voters at ≥ b_safe
    (∃ b_safe, b_safe ≤ s.round ∧
      (∀ q w b, (s.locals q).core.lastVote = some (w, b) → w ≠ v → b < b_safe) ∧
      ((List.finRange n).filter fun q =>
        match (s.locals q).core.lastVote with
        | some (w, b) => decide (w = v ∧ b ≥ b_safe) | none => false).length * 2 > n) ∧
    -- G3: at phase ≥ 2, coordinator proposes v
    (s.phase.val ≥ 2 →
      ∀ w, (s.locals (coordinatorG n hn s.round)).core.proposal = some w → w = v)) ∧
  -- (H) Ballot bound
  (∀ q w b, (s.locals q).core.lastVote = some (w, b) →
    b ≤ s.round ∧
    (b = s.round → s.phase = ⟨3, by omega⟩ ∧ (s.locals q).core.accepted = true)) ∧
  -- (I) Same-ballot agreement: votes at the same ballot have the same value
  (∀ q₁ q₂ v₁ v₂ b, (s.locals q₁).core.lastVote = some (v₁, b) →
    (s.locals q₂).core.lastVote = some (v₂, b) → v₁ = v₂)

/-! ### Key lemma: general-n majority quorum intersection -/

/-- Two strict majorities of `n` processes must share at least one process. -/
theorem majority_intersect (p₁ p₂ : Fin n → Bool)
    (h₁ : ((List.finRange n).filter fun r => p₁ r).length * 2 > n)
    (h₂ : ((List.finRange n).filter fun r => p₂ r).length * 2 > n) :
    ∃ r : Fin n, p₁ r = true ∧ p₂ r = true := by
  by_contra h
  have h' : ∀ r, ¬(p₁ r = true ∧ p₂ r = true) := fun r hr => h ⟨r, hr⟩
  have h_sum := filter_disjoint_length_le
    (fun r => p₁ r) (fun r => p₂ r) (List.finRange n) h'
  have h_len : (List.finRange n).length = n := List.length_finRange
  omega

/-! ### Init proof -/

theorem lv_inv_init_gen :
    ∀ s, (lvLeslieSpecG n hn).init s → lv_inv_gen n hn s := by
  intro s ⟨hround, hphase, hinit⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (A) Agreement: vacuously true, no decisions
    intro p q v w hv _
    have hp := (hinit p).2
    simp at hp ; rw [hp] at hv ; simp at hv
  · -- (B) Accepted consistency: vacuously true, no accepts
    intro p hacc
    have hp := (hinit p).2
    simp at hp ; rw [hp] at hacc ; simp at hacc
  · -- (C) Phase 3 consistency: phase = 0 ≠ 3
    intro hph ; simp [hphase] at hph
  · -- (D) Decision-proposal consistency: vacuously true
    intro p v hv
    have hp := (hinit p).2
    simp at hp ; rw [hp] at hv ; simp at hv
  · -- (E) Round synchronization
    intro p
    have hp := (hinit p).1
    simp at hp ; rw [hround, hp]
  · -- (F') Acceptance only at phase 3: vacuous
    intro p hacc
    have hp := (hinit p).2
    simp at hp ; rw [hp] at hacc ; simp at hacc
  · -- (F) Uniform value: phase = 0 ≠ 3
    intro hph ; simp [hphase] at hph
  · -- (G) Cross-ballot: vacuously true, no decisions
    intro p v hv
    have hp := (hinit p).2
    simp at hp ; rw [hp] at hv ; simp at hv
  · -- (H) Ballot bound: vacuously true, all lastVote = none
    intro q w b hlv
    have hp := (hinit q).2
    simp at hp ; rw [hp] at hlv ; simp at hlv
  · -- (I) Same-ballot agreement: vacuously true, all lastVote = none
    intro q₁ q₂ v₁ v₂ b hlv₁ _
    have hp := (hinit q₁).2
    simp at hp ; rw [hp] at hlv₁ ; simp at hlv₁

/-! ### Step proof -/

/-- The main invariant preservation theorem (general n).
    Each of the 4 phase transitions preserves `lv_inv_gen`.
    This follows the same structure as `lv_inv_step` (n = 3),
    using `majority_intersect` for quorum arguments. -/
theorem lv_inv_step_gen :
    ∀ s ho, lv_inv_gen n hn s → (lvCommG n) s.round s.phase ho →
    ∀ s', phase_step (lvAlgG n hn) ho s s' → lv_inv_gen n hn s' := by
  intro s ho ⟨h_agree, h_acc, h_ph3, h_dec_prop, h_rsync, h_acc_ph3, h_uniform, h_cross, h_ballot_bound, h_same_ballot⟩ _ s' ⟨hadvance, hlocals⟩
  have hph : s.phase.val = 0 ∨ s.phase.val = 1 ∨ s.phase.val = 2 ∨ s.phase.val = 3 := by
    have := s.phase.isLt ; omega
  rcases hph with hph0 | hph1 | hph2 | hph3
  · ---- Phase 0 → Phase 1 ----
    have hph_eq : s.phase = ⟨0, by omega⟩ := Fin.ext hph0
    have h_phase : (lvAlgG n hn).phases s.phase = lvPhase0G n hn := by simp [lvAlgG, hph_eq]
    have hs'_phase : s'.phase = ⟨1, by omega⟩ := by
      simp [hph0] at hadvance ; exact hadvance.2
    have hs'_round : s'.round = s.round := by
      simp [hph0] at hadvance ; exact hadvance.1
    have hlocals' : ∀ p, s'.locals p = (lvPhase0G n hn).update p (s.locals p)
        (phase_delivered (lvPhase0G n hn) s.locals ho p) := by
      intro p ; have := hlocals p ; rwa [h_phase] at this
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- (A) Agreement
      intro p q v w hv hw
      rw [hlocals' p] at hv ; rw [hlocals' q] at hw
      simp [lvPhase0G, phase_delivered] at hv hw
      exact h_agree p q v w hv hw
    · -- (B) Accepted consistency
      intro p hacc
      rw [hlocals' p] at hacc
      simp [lvPhase0G, phase_delivered] at hacc
    · -- (C) Phase 3 consistency
      intro hph3' ; rw [hs'_phase] at hph3' ; simp at hph3'
    · -- (D) Decision-proposal consistency
      intro p v _ hph3' ; rw [hs'_phase] at hph3' ; simp at hph3'
    · -- (E) Round sync
      intro p ; rw [hlocals' p]
      simp [lvPhase0G, phase_delivered, hs'_round]
      exact h_rsync p
    · -- (F') Acceptance only at phase 3
      intro p hacc ; rw [hlocals' p] at hacc
      simp [lvPhase0G, phase_delivered] at hacc
    · -- (F) Uniform value
      intro hph3' ; rw [hs'_phase] at hph3' ; simp at hph3'
    · -- (G) Cross-ballot
      intro p v hv
      have h_dec : ∀ r, (s'.locals r).core.decided = (s.locals r).core.decided := by
        intro r ; rw [hlocals' r] ; simp [lvPhase0G, phase_delivered]
      rw [h_dec p] at hv
      have h_lv : ∀ r, (s'.locals r).core.lastVote = (s.locals r).core.lastVote := by
        intro r ; rw [hlocals' r] ; simp [lvPhase0G, phase_delivered]
      obtain ⟨⟨b_safe, hbs_le, hbs_below, hbs_maj⟩, hG3⟩ := h_cross p v hv
      refine ⟨⟨b_safe, by rw [hs'_round] ; exact hbs_le, ?_, ?_⟩, ?_⟩
      · intro q w b hlv₁ hw
        rw [h_lv q] at hlv₁
        exact hbs_below q w b hlv₁ hw
      · have : (List.finRange n).filter (fun q => match (s'.locals q).core.lastVote with
            | some (w, b) => decide (w = v ∧ b ≥ b_safe) | none => false) =
          (List.finRange n).filter (fun q => match (s.locals q).core.lastVote with
            | some (w, b) => decide (w = v ∧ b ≥ b_safe) | none => false) := by
          congr 1 ; funext q ; simp [h_lv q]
        rw [this] ; exact hbs_maj
      · intro hph_ge2 ; simp [hs'_phase] at hph_ge2
    · -- (H) Ballot bound
      intro q w b hlv
      have h_lv : (s'.locals q).core.lastVote = (s.locals q).core.lastVote := by
        rw [hlocals' q] ; simp [lvPhase0G, phase_delivered]
      rw [h_lv] at hlv
      have hb := h_ballot_bound q w b hlv
      refine ⟨by rw [hs'_round] ; exact hb.1, ?_⟩
      intro hb_eq
      exfalso
      have hcur := hb.2 (by rwa [hs'_round] at hb_eq)
      rw [hcur.1] at hph0
      simp at hph0
    · -- (I) Same-ballot agreement: lastVote unchanged
      intro q₁ q₂ v₁ v₂ b hlv₁ hlv₂
      have h_lv : ∀ r, (s'.locals r).core.lastVote = (s.locals r).core.lastVote := by
        intro r ; rw [hlocals' r] ; simp [lvPhase0G, phase_delivered]
      rw [h_lv q₁] at hlv₁ ; rw [h_lv q₂] at hlv₂
      exact h_same_ballot q₁ q₂ v₁ v₂ b hlv₁ hlv₂
  · ---- Phase 1 → Phase 2 ----
    have hph_eq : s.phase = ⟨1, by omega⟩ := Fin.ext hph1
    have h_phase : (lvAlgG n hn).phases s.phase = lvPhase1G n hn := by simp [lvAlgG, hph_eq]
    have hs'_phase : s'.phase = ⟨2, by omega⟩ := by
      simp [hph1] at hadvance ; exact hadvance.2
    have hs'_round : s'.round = s.round := by
      simp [hph1] at hadvance ; exact hadvance.1
    have hlocals' : ∀ p, s'.locals p = (lvPhase1G n hn).update p (s.locals p)
        (phase_delivered (lvPhase1G n hn) s.locals ho p) := by
      intro p ; have := hlocals p ; rwa [h_phase] at this
    have h_acc_pres : ∀ r, (s'.locals r).core.accepted = (s.locals r).core.accepted := by
      intro r ; rw [hlocals' r] ; simp only [lvPhase1G, phase_delivered]
      split <;> (try split) <;> simp
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- (A) Agreement
      intro p q v w hv hw
      have h_dec : ∀ r, (s'.locals r).core.decided = (s.locals r).core.decided := by
        intro r ; rw [hlocals' r]
        simp only [lvPhase1G, phase_delivered]
        split <;> (try split) <;> simp
      rw [h_dec p] at hv ; rw [h_dec q] at hw
      exact h_agree p q v w hv hw
    · -- (B) Accepted consistency
      intro p hacc
      rw [h_acc_pres p] at hacc
      obtain ⟨v, b, hvb, hb⟩ := h_acc p hacc
      have h_lv_pres : (s'.locals p).core.lastVote = (s.locals p).core.lastVote := by
        rw [hlocals' p] ; simp only [lvPhase1G, phase_delivered]
        split <;> (try split) <;> simp
      exact ⟨v, b, by rw [h_lv_pres, hvb], by rw [hs'_round, hb]⟩
    · -- (C) Phase 3
      intro hph3' ; rw [hs'_phase] at hph3' ; simp at hph3'
    · -- (D) Decision-proposal
      intro p v _ hph3' ; rw [hs'_phase] at hph3' ; simp at hph3'
    · -- (E) Round sync
      intro p ; rw [hlocals' p, hs'_round]
      simp only [lvPhase1G, phase_delivered]
      split <;> (try split) <;> simp [h_rsync p]
    · -- (F') accepted preserved
      intro p hacc' ; rw [h_acc_pres p] at hacc'
      have := h_acc_ph3 p hacc'
      rw [this] at hph1 ; simp at hph1
    · -- (F)
      intro hph3' ; rw [hs'_phase] at hph3' ; simp at hph3'
    · -- (G) Cross-ballot with safe ballot formulation
      intro p v hv
      have h_dec : ∀ r, (s'.locals r).core.decided = (s.locals r).core.decided := by
        intro r ; rw [hlocals' r] ; simp only [lvPhase1G, phase_delivered]
        split <;> (try split) <;> simp
      rw [h_dec p] at hv
      have h_lv : ∀ r, (s'.locals r).core.lastVote = (s.locals r).core.lastVote := by
        intro r ; rw [hlocals' r] ; simp only [lvPhase1G, phase_delivered]
        split <;> (try split) <;> simp
      obtain ⟨⟨b_safe, hbs_le, hbs_below, hbs_maj⟩, hG3⟩ := h_cross p v hv
      refine ⟨⟨b_safe, by rw [hs'_round] ; exact hbs_le, ?_, ?_⟩, ?_⟩
      · -- G1: non-v votes < b_safe (lastVote unchanged)
        intro q w b hlv₁ hw
        rw [h_lv q] at hlv₁
        exact hbs_below q w b hlv₁ hw
      · -- G1 majority preserved (lastVote unchanged)
        have : (List.finRange n).filter (fun q => match (s'.locals q).core.lastVote with
            | some (w, b) => decide (w = v ∧ b ≥ b_safe) | none => false) =
          (List.finRange n).filter (fun q => match (s.locals q).core.lastVote with
            | some (w, b) => decide (w = v ∧ b ≥ b_safe) | none => false) := by
          congr 1 ; funext q ; simp [h_lv q]
        rw [this] ; exact hbs_maj
      · -- (G3) At phase ≥ 2: coordinator's proposal = v.
        -- s'.phase = 2. The coordinator MAY have set the proposal.
        -- Quorum intersection + foldl_max_picks_safe_value argument.
        intro _ w h_prop
        let c := coordinatorG n hn s.round
        rw [hs'_round] at h_prop
        rw [hlocals' c] at h_prop
        simp only [lvPhase1G, phase_delivered] at h_prop
        have hc_eq : c = coordinatorG n hn (s.locals c).roundNum := by
          simp [c, h_rsync c]
        rw [if_pos hc_eq] at h_prop
        split at h_prop
        · case _ hcount =>
          simp at h_prop
          let msgs := fun q => phase_delivered (lvPhase1G n hn) s.locals ho c q
          let collected := (List.finRange n).filterMap fun q =>
            match msgs q with
            | some (.promise (some vb)) => some vb
            | _ => none
          have h_collected_from_lv : ∀ vb ∈ collected, ∃ q,
              ho c q = true ∧ (s.locals q).core.lastVote = some vb := by
            intro vb hvb
            simp only [collected, msgs, List.mem_filterMap,
                        List.mem_finRange, true_and, phase_delivered, lvPhase1G] at hvb
            obtain ⟨q, hq⟩ := hvb
            by_cases hho : ho c q = true
            · simp [hho] at hq
              cases hlv_q : (s.locals q).core.lastVote with
              | none => simp [hlv_q] at hq
              | some vb' => simp [hlv_q] at hq ; exact ⟨q, hho, by rw [hq] at hlv_q ; exact hlv_q⟩
            · have hf : ho c q = false := by revert hho ; cases ho c q <;> simp
              simp [hf] at hq
          -- The promise senders heard by coordinator
          have h_heard : ((List.finRange n).filter (fun q => ho c q)).length * 2 > n := by
            have : (List.finRange n).filter (fun q =>
                match msgs q with | some (.promise _) => true | _ => false) =
              (List.finRange n).filter (fun q => ho c q) := by
              congr 1 ; funext q
              simp only [msgs, phase_delivered, lvPhase1G]
              cases ho c q <;> simp
            rw [← this] ; exact hcount
          -- Quorum intersection: ∃ q in both the heard set and the G1 majority
          have h_v_safe_in_collected : ∃ vb ∈ collected, vb.1 = v ∧ vb.2 ≥ b_safe := by
            -- The G1 majority filter: processes with v-vote at ≥ b_safe
            -- The heard filter: processes heard by coordinator
            -- Intersection is nonempty by majority_intersect
            by_contra h_no_overlap
            have h_no : ∀ q, ¬(ho c q = true ∧ (match (s.locals q).core.lastVote with
                | some (w, b) => decide (w = v ∧ b ≥ b_safe) | none => false) = true) := by
              intro q hq ; apply h_no_overlap
              obtain ⟨hho, hlv_q⟩ := hq
              cases hlv_q' : (s.locals q).core.lastVote with
              | none => simp [hlv_q'] at hlv_q
              | some vb =>
                simp [hlv_q', decide_eq_true_eq] at hlv_q
                obtain ⟨val, bal⟩ := vb
                simp at hlv_q
                refine ⟨(v, bal), ?_, rfl, hlv_q.2⟩
                simp only [collected, msgs, List.mem_filterMap,
                            List.mem_finRange, true_and, phase_delivered, lvPhase1G]
                exact ⟨q, by simp [hho, hlv_q.1, hlv_q']⟩
            have h_sum := filter_disjoint_length_le
              (fun q => ho c q) (fun q => match (s.locals q).core.lastVote with
                | some (w, b) => decide (w = v ∧ b ≥ b_safe) | none => false)
              (List.finRange n) h_no
            have h_len : (List.finRange n).length = n := List.length_finRange
            omega
          -- All non-v elements in collected have ballot < b_safe
          have h_below_collected : ∀ x ∈ collected, x.1 ≠ v → x.2 < b_safe := by
            intro x hx hxne
            obtain ⟨qx, _, hqx_lv⟩ := h_collected_from_lv x hx
            rw [show x = (x.1, x.2) from by simp] at hqx_lv
            exact hbs_below qx x.1 x.2 hqx_lv hxne
          -- Apply foldl_max_picks_safe_value
          obtain ⟨vb, hvb_mem, hvb_val, hvb_ge⟩ := h_v_safe_in_collected
          cases hcol : collected with
          | nil => simp [hcol] at hvb_mem
          | cons init rest =>
            have h_exists : ∃ x ∈ init :: rest, x.1 = v ∧ x.2 ≥ b_safe :=
              ⟨vb, hcol ▸ hvb_mem, hvb_val, hvb_ge⟩
            have h_below : ∀ x ∈ init :: rest, x.1 ≠ v → x.2 < b_safe := by
              intro x hx hxne
              exact h_below_collected x (hcol ▸ hx) hxne
            have hpick_v :
                (rest.foldl (fun best cur => if cur.2 > best.2 then cur else best) init).1 = v :=
              foldl_max_picks_safe_value rest init v b_safe h_exists h_below
            have h_collected_eq : (List.finRange n).filterMap (fun q =>
                match (if ho c q = true then some (LVMsg.promise (s.locals q).core.lastVote) else none) with
                | some (.promise (some vb)) => some vb
                | _ => none) = collected := by
              rfl
            rw [h_collected_eq, hcol] at h_prop
            have hpick_v' :
                (rest.foldl (fun best cur => if best.2 < cur.2 then cur else best) init).1 = v := by
              simpa [gt_iff_lt] using hpick_v
            rw [← h_prop] ; exact hpick_v'
        · -- promiseCount * 2 ≤ n: proposal = none ≠ some w
          simp at h_prop
    · -- (H) Ballot bound
      intro q w b hlv
      have h_lv : (s'.locals q).core.lastVote = (s.locals q).core.lastVote := by
        rw [hlocals' q] ; simp only [lvPhase1G, phase_delivered]
        split <;> (try split) <;> simp
      rw [h_lv] at hlv
      have hb := h_ballot_bound q w b hlv
      refine ⟨by rw [hs'_round] ; exact hb.1, ?_⟩
      intro hb_eq
      exfalso
      have hcur := hb.2 (by rwa [hs'_round] at hb_eq)
      rw [hcur.1] at hph1
      simp at hph1
    · -- (I) Same-ballot agreement: lastVote unchanged
      intro q₁ q₂ v₁ v₂ b hlv₁ hlv₂
      have h_lv : ∀ r, (s'.locals r).core.lastVote = (s.locals r).core.lastVote := by
        intro r ; rw [hlocals' r] ; simp only [lvPhase1G, phase_delivered]
        split <;> (try split) <;> simp
      rw [h_lv q₁] at hlv₁ ; rw [h_lv q₂] at hlv₂
      exact h_same_ballot q₁ q₂ v₁ v₂ b hlv₁ hlv₂
  · ---- Phase 2 → Phase 3 ----
    have hph_eq : s.phase = ⟨2, by omega⟩ := Fin.ext hph2
    have h_phase : (lvAlgG n hn).phases s.phase = lvPhase2G n hn := by simp [lvAlgG, hph_eq]
    have hs'_phase : s'.phase = ⟨3, by omega⟩ := by
      simp [hph2] at hadvance ; exact hadvance.2
    have hs'_round : s'.round = s.round := by
      simp [hph2] at hadvance ; exact hadvance.1
    have hlocals' : ∀ p, s'.locals p = (lvPhase2G n hn).update p (s.locals p)
        (phase_delivered (lvPhase2G n hn) s.locals ho p) := by
      intro p ; have := hlocals p ; rwa [h_phase] at this
    have h_no_acc : ∀ r, (s.locals r).core.accepted = false := by
      intro r ; by_contra h
      have := h_acc_ph3 r (by revert h ; cases (s.locals r).core.accepted <;> simp)
      rw [this] at hph2 ; simp at hph2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- (A) Agreement
      intro p q v w hv hw
      have h_dec : ∀ r, (s'.locals r).core.decided = (s.locals r).core.decided := by
        intro r ; rw [hlocals' r]
        simp only [lvPhase2G, phase_delivered]
        split <;> simp
      rw [h_dec p] at hv ; rw [h_dec q] at hw
      exact h_agree p q v w hv hw
    · -- (B) Accepted
      intro p hacc
      rw [hlocals' p] at hacc
      simp only [lvPhase2G, phase_delivered] at hacc
      rw [hlocals' p]
      simp only [lvPhase2G, phase_delivered]
      split
      · case _ v' _ =>
        exact ⟨v', (s.locals p).roundNum,
               by simp,
               by rw [hs'_round, h_rsync p]⟩
      · case _ _ =>
        simp at hacc
        obtain ⟨v, b, hvb, hb⟩ := h_acc p hacc
        exact ⟨v, b, hvb, by rw [hs'_round] ; exact hb⟩
    · -- (C) Phase 3 consistency
      intro _ p hacc
      rw [hlocals' p] at hacc ⊢
      simp only [lvPhase2G, phase_delivered] at hacc ⊢
      split
      · case _ v' _ =>
        exact ⟨v', by simp ; rw [h_rsync p, hs'_round]⟩
      · case _ _ =>
        simp at hacc
        obtain ⟨v, b, hvb, hb⟩ := h_acc p hacc
        exact ⟨v, by rw [hvb, hb, hs'_round]⟩
    · -- (D) Decision-proposal consistency
      intro p v hdec _ hmaj q hacc_q
      have h_dec : ∀ r, (s'.locals r).core.decided = (s.locals r).core.decided := by
        intro r ; rw [hlocals' r] ; simp only [lvPhase2G, phase_delivered] ; split <;> simp
      rw [h_dec p] at hdec
      obtain ⟨_, hG3⟩ := h_cross p v hdec
      cases h_prop : (s.locals (coordinatorG n hn s.round)).core.proposal with
      | none =>
        exfalso
        rw [hlocals' q] at hacc_q
        simp only [lvPhase2G, phase_delivered, h_rsync q] at hacc_q
        by_cases hho : ho q (coordinatorG n hn s.round) = true
        · simp only [hho, ite_true, h_rsync (coordinatorG n hn s.round), h_prop] at hacc_q
          rw [h_no_acc q] at hacc_q ; simp at hacc_q
        · have hf : ho q (coordinatorG n hn s.round) = false := by
            revert hho ; cases ho q (coordinatorG n hn s.round) <;> simp
          simp [hf, h_no_acc q] at hacc_q
      | some w =>
        have hw_eq := hG3 (by omega) w h_prop
        rw [hlocals' q] at hacc_q ⊢
        simp only [lvPhase2G, phase_delivered, h_rsync q] at hacc_q ⊢
        by_cases hho : ho q (coordinatorG n hn s.round) = true
        · simp only [hho, ite_true, h_rsync (coordinatorG n hn s.round), h_prop] at hacc_q ⊢
          exact ⟨w, by simp [hs'_round], hw_eq⟩
        · have hf : ho q (coordinatorG n hn s.round) = false := by
            revert hho ; cases ho q (coordinatorG n hn s.round) <;> simp
          simp [hf, h_no_acc q] at hacc_q
    · -- (E) Round sync
      intro p ; rw [hlocals' p, hs'_round]
      simp only [lvPhase2G, phase_delivered]
      split <;> simp [h_rsync p]
    · -- (F') accepted → phase = 3
      intro _ _ ; exact hs'_phase
    · -- (F) Uniform value
      intro _ p q vp vq hacc_p hacc_q hlv_p hlv_q
      suffices h_eq : (s'.locals p).core.lastVote = (s'.locals q).core.lastVote by
        rw [hlv_p, hlv_q] at h_eq
        simp only [Option.some.injEq, Prod.mk.injEq] at h_eq
        exact h_eq.1
      rw [hlocals' p, hlocals' q]
      simp only [lvPhase2G, phase_delivered, h_rsync p, h_rsync q]
      rw [hlocals' p] at hacc_p ; rw [hlocals' q] at hacc_q
      simp only [lvPhase2G, phase_delivered, h_rsync p, h_rsync q] at hacc_p hacc_q
      cases h_prop : (s.locals (coordinatorG n hn s.round)).core.proposal with
      | none =>
        exfalso
        simp only [h_rsync (coordinatorG n hn s.round), h_prop] at hacc_p
        by_cases hho : ho p (coordinatorG n hn s.round) = true
        · simp [hho, h_no_acc p] at hacc_p
        · have hf : ho p (coordinatorG n hn s.round) = false := by
            revert hho ; cases ho p (coordinatorG n hn s.round) <;> simp
          simp [hf, h_no_acc p] at hacc_p
      | some v₀ =>
        simp only [h_rsync (coordinatorG n hn s.round)]
        by_cases hp_ho : ho p (coordinatorG n hn s.round) = true <;>
          by_cases hq_ho : ho q (coordinatorG n hn s.round) = true
        · simp [hp_ho, hq_ho]
        · simp [hq_ho, h_no_acc q] at hacc_q
        · simp [hp_ho, h_no_acc p] at hacc_p
        · simp [hp_ho, h_no_acc p] at hacc_p
    · -- (G) Cross-ballot
      intro p v hv
      have h_dec : ∀ r, (s'.locals r).core.decided = (s.locals r).core.decided := by
        intro r ; rw [hlocals' r] ; simp only [lvPhase2G, phase_delivered] ; split <;> simp
      rw [h_dec p] at hv
      obtain ⟨⟨b_safe, hbs_le, hbs_below, hbs_maj⟩, hG3⟩ := h_cross p v hv
      refine ⟨⟨b_safe, by rw [hs'_round] ; exact hbs_le, ?_, ?_⟩, ?_⟩
      · -- G1: non-v votes < b_safe
        -- New votes are for the coordinator's value (= v by G3). So no new non-v votes.
        intro q₁ w b₁ hlv₁ hw
        cases h_prop : (s.locals (coordinatorG n hn s.round)).core.proposal with
        | none =>
          have h_lv_pres : ∀ r, (s'.locals r).core.lastVote = (s.locals r).core.lastVote := by
            intro r ; rw [hlocals' r]
            simp only [lvPhase2G, phase_delivered, h_rsync r]
            by_cases hho : ho r (coordinatorG n hn s.round) = true
            · simp [hho, h_rsync (coordinatorG n hn s.round), h_prop]
            · have hf : ho r (coordinatorG n hn s.round) = false := by
                revert hho ; cases ho r (coordinatorG n hn s.round) <;> simp
              simp [hf]
          rw [h_lv_pres q₁] at hlv₁
          exact hbs_below q₁ w b₁ hlv₁ hw
        | some v₀ =>
          have hv₀_eq := hG3 (by omega) v₀ h_prop
          -- q₁ has non-v vote. If q₁ received the proposal, it would get v₀ = v. Contradiction.
          have h_q₁_old : (s'.locals q₁).core.lastVote = (s.locals q₁).core.lastVote := by
            rw [hlocals' q₁]
            simp only [lvPhase2G, phase_delivered, h_rsync q₁]
            by_cases hho : ho q₁ (coordinatorG n hn s.round) = true
            · exfalso ; rw [hlocals' q₁] at hlv₁
              simp [lvPhase2G, phase_delivered, h_rsync q₁, hho,
                    h_rsync (coordinatorG n hn s.round), h_prop] at hlv₁
              exact hw (by rw [← hv₀_eq] ; exact hlv₁.1.symm)
            · have hf : ho q₁ (coordinatorG n hn s.round) = false := by
                revert hho ; cases ho q₁ (coordinatorG n hn s.round) <;> simp
              simp [hf]
          rw [h_q₁_old] at hlv₁
          exact hbs_below q₁ w b₁ hlv₁ hw
      · -- G1 majority: v-voters at ≥ b_safe can only grow
        have h_mono : ((List.finRange n).filter fun q =>
            match (s.locals q).core.lastVote with
            | some (w, b) => decide (w = v ∧ b ≥ b_safe) | none => false).length ≤
          ((List.finRange n).filter fun q =>
            match (s'.locals q).core.lastVote with
            | some (w, b) => decide (w = v ∧ b ≥ b_safe) | none => false).length := by
          apply filter_length_mono
          intro q hq
          cases h_prop : (s.locals (coordinatorG n hn s.round)).core.proposal with
          | none =>
            have : (s'.locals q).core.lastVote = (s.locals q).core.lastVote := by
              rw [hlocals' q] ; simp only [lvPhase2G, phase_delivered, h_rsync q]
              by_cases hho : ho q (coordinatorG n hn s.round) = true
              · simp [hho, h_rsync (coordinatorG n hn s.round), h_prop]
              · have hf : ho q (coordinatorG n hn s.round) = false := by
                  revert hho ; cases ho q (coordinatorG n hn s.round) <;> simp
                simp [hf]
            rw [this] ; exact hq
          | some v₀ =>
            have hv₀ := hG3 (by omega) v₀ h_prop
            rw [hlocals' q] ; simp only [lvPhase2G, phase_delivered, h_rsync q]
            by_cases hho : ho q (coordinatorG n hn s.round) = true
            · -- q got new vote (v₀, round). v₀ = v. ballot = round ≥ b_safe.
              simp [hho, h_rsync (coordinatorG n hn s.round), h_prop, hv₀]
              exact hbs_le
            · have hf : ho q (coordinatorG n hn s.round) = false := by
                revert hho ; cases ho q (coordinatorG n hn s.round) <;> simp
              simp [hf]
              cases hlvq : (s.locals q).core.lastVote with
              | none => simp [hlvq] at hq
              | some vb =>
                obtain ⟨val, bal⟩ := vb
                simp [hlvq, decide_eq_true_eq] at hq ⊢
                exact hq
        omega
      · -- (G3) s'.phase = 3, val ≥ 2. Proposal unchanged.
        intro hph_ge2 w h_prop
        have h_prop_pres : (s'.locals (coordinatorG n hn s'.round)).core.proposal =
            (s.locals (coordinatorG n hn s.round)).core.proposal := by
          rw [hs'_round, hlocals' (coordinatorG n hn s.round)]
          simp only [lvPhase2G, phase_delivered] ; split <;> simp
        rw [h_prop_pres] at h_prop
        exact hG3 (by omega) w h_prop
    · -- (H) Ballot bound
      intro q w b hlv
      rw [hlocals' q] at hlv
      simp only [lvPhase2G, phase_delivered] at hlv
      split at hlv
      · case _ _ heq =>
          simp at hlv
          refine ⟨by rw [← hlv.2, h_rsync q, hs'_round] ; exact Nat.le_refl _, ?_⟩
          intro hb_eq
          refine ⟨hs'_phase, ?_⟩
          rw [hlocals' q]
          simp only [lvPhase2G, phase_delivered]
          rw [heq]
      · have hb := h_ballot_bound q w b hlv
        refine ⟨by rw [hs'_round] ; exact hb.1, ?_⟩
        intro hb_eq
        exfalso
        have hcur := hb.2 (by rwa [hs'_round] at hb_eq)
        rw [hcur.1] at hph2
        simp at hph2
    · -- (I) Same-ballot agreement
      intro q₁ q₂ v₁ v₂ b hlv₁ hlv₂
      -- New votes are at ballot s.round for the coordinator's value.
      -- By H (pre-state), no prior votes at s.round exist (ballot = s.round → phase = 3 but we're at phase 2).
      -- So all votes at s.round in post-state are new, all with the same value.
      -- Votes at other ballots are unchanged.
      -- Helper: characterize lastVote in post-state
      have h_lv_cases : ∀ r, (s'.locals r).core.lastVote = (s.locals r).core.lastVote ∨
          (∃ v₀, (s.locals (coordinatorG n hn s.round)).core.proposal = some v₀ ∧
                  ho r (coordinatorG n hn s.round) = true ∧
                  (s'.locals r).core.lastVote = some (v₀, s.round)) := by
        intro r
        by_cases hho : ho r (coordinatorG n hn s.round) = true
        · cases h_prop : (s.locals (coordinatorG n hn s.round)).core.proposal with
          | none =>
            left
            rw [hlocals' r]
            simp [lvPhase2G, phase_delivered, h_rsync r, hho,
                  h_rsync (coordinatorG n hn s.round), h_prop]
          | some v₀ =>
            right ; refine ⟨v₀, rfl, hho, ?_⟩
            rw [hlocals' r]
            simp [lvPhase2G, phase_delivered, h_rsync r, hho,
                  h_rsync (coordinatorG n hn s.round), h_prop]
        · have hf : ho r (coordinatorG n hn s.round) = false := by
            revert hho ; cases ho r (coordinatorG n hn s.round) <;> simp
          left
          rw [hlocals' r]
          simp [lvPhase2G, phase_delivered, h_rsync r, hf]
      -- No votes at ballot s.round exist in pre-state
      have h_no_cur_ballot : ∀ r w, (s.locals r).core.lastVote = some (w, s.round) → False := by
        intro r w hlv
        have hb := h_ballot_bound r w s.round hlv
        have hcur := hb.2 rfl
        rw [hcur.1] at hph2
        simp at hph2
      -- Case analysis on q₁ and q₂
      rcases h_lv_cases q₁ with h₁_old | ⟨v₀₁, hp₁, _, h₁_new⟩
      · -- q₁'s vote is old
        rcases h_lv_cases q₂ with h₂_old | ⟨v₀₂, _, _, h₂_new⟩
        · -- Both old: use h_same_ballot
          rw [h₁_old] at hlv₁ ; rw [h₂_old] at hlv₂
          exact h_same_ballot q₁ q₂ v₁ v₂ b hlv₁ hlv₂
        · -- q₁ old, q₂ new at s.round
          rw [h₂_new] at hlv₂
          simp only [Option.some.injEq, Prod.mk.injEq] at hlv₂
          -- b = s.round (from hlv₂)
          rw [h₁_old] at hlv₁
          -- q₁ has old vote at ballot b = s.round. Contradiction.
          exact absurd (hlv₂.2 ▸ hlv₁) (by intro h ; exact h_no_cur_ballot q₁ v₁ h)
      · -- q₁'s vote is new at s.round
        rw [h₁_new] at hlv₁
        simp only [Option.some.injEq, Prod.mk.injEq] at hlv₁
        rcases h_lv_cases q₂ with h₂_old | ⟨v₀₂, hp₂, _, h₂_new⟩
        · -- q₂ old, q₁ new at s.round
          rw [h₂_old] at hlv₂
          -- q₂ has old vote at ballot b = s.round. Contradiction.
          exact absurd (hlv₁.2 ▸ hlv₂) (by intro h ; exact h_no_cur_ballot q₂ v₂ h)
        · -- Both new at s.round
          rw [h₂_new] at hlv₂
          simp only [Option.some.injEq, Prod.mk.injEq] at hlv₂
          -- Both have the coordinator's value: v₁ = v₀₁ and v₂ = v₀₂
          rw [← hlv₁.1, ← hlv₂.1]
          rw [hp₁] at hp₂
          simp at hp₂
          exact hp₂
  · ---- Phase 3 → Phase 0 ----
    have hph_eq : s.phase = ⟨3, by omega⟩ := Fin.ext hph3
    have h_phase : (lvAlgG n hn).phases s.phase = lvPhase3G n := by
      show (if s.phase.val = 0 then lvPhase0G n hn
            else if s.phase.val = 1 then lvPhase1G n hn
            else if s.phase.val = 2 then lvPhase2G n hn
            else lvPhase3G n) = lvPhase3G n
      simp [show s.phase.val ≠ 0 by omega,
            show s.phase.val ≠ 1 by omega, show s.phase.val ≠ 2 by omega]
    have hs'_round : s'.round = s.round + 1 := by
      simp [hph3] at hadvance ; exact hadvance.1
    have hs'_phase : s'.phase = ⟨0, by omega⟩ := by
      simp [hph3] at hadvance ; exact hadvance.2
    have hlocals' : ∀ p, s'.locals p = (lvPhase3G n).update p (s.locals p)
        (phase_delivered (lvPhase3G n) s.locals ho p) := by
      intro p ; have := hlocals p ; rwa [h_phase] at this
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- (A) Agreement
      intro p q v w hv hw
      have h_dec_or : ∀ r val, (s'.locals r).core.decided = some val →
          (s.locals r).core.decided = some val ∨
          (∃ msgs_accepted,
            msgs_accepted = (List.finRange n).filterMap (fun q' =>
              match (phase_delivered (lvPhase3G n) s.locals ho r q') with
              | some (.accepted v') => some v'
              | _ => none) ∧
            msgs_accepted.head? = some val ∧
            hasMajG n (fun q' => match (phase_delivered (lvPhase3G n) s.locals ho r q') with
              | some (.accepted _) => true | _ => false) = true) := by
        intro r val hr
        rw [hlocals' r] at hr
        simp only [lvPhase3G, phase_delivered] at hr
        split at hr
        · case _ hmaj =>
          split at hr
          · case _ v' hhead =>
            right ; simp at hr ; exact ⟨_, rfl, by rw [← hr] ; exact hhead, hmaj⟩
          · left ; simp at hr ; exact hr
        · left ; simp at hr ; exact hr
      -- Helper: HO-filtered accepted → globally accepted
      have h_impl_for : ∀ (r : Fin n) (obs : Fin n),
          (match phase_delivered (lvPhase3G n) s.locals ho obs r with
            | some (.accepted _) => true | _ => false) = true →
          (s.locals r).core.accepted = true := by
        intro r obs hr_filt
        simp only [phase_delivered, lvPhase3G] at hr_filt
        by_cases hho : ho obs r = true
        · simp only [hho, ite_true] at hr_filt
          by_cases hacc : (s.locals r).core.accepted = true
          · exact hacc
          · have hf : (s.locals r).core.accepted = false := by
              revert hacc ; cases (s.locals r).core.accepted <;> simp
            simp [hf] at hr_filt
        · have hf : ho obs r = false := by revert hho ; cases ho obs r <;> simp
          simp [hf] at hr_filt
      -- Helper: HO majority → global majority
      have h_global_maj_from : ∀ obs : Fin n,
          hasMajG n (fun r => match phase_delivered (lvPhase3G n) s.locals ho obs r with
            | some (.accepted _) => true | _ => false) = true →
          hasMajG n (fun r => (s.locals r).core.accepted) = true := by
        intro obs hmaj
        have h_mono := filter_length_mono (List.finRange n) _ _ (h_impl_for · obs)
        unfold hasMajG at hmaj ⊢
        simp only [decide_eq_true_eq] at hmaj ⊢
        omega
      -- Helper: all values in filterMap are v when all acceptors have value v
      have h_all_vals : ∀ (obs : Fin n) (val : Value),
          (∀ r : Fin n, (s.locals r).core.accepted = true →
            ∃ w, (s.locals r).core.lastVote = some (w, s.round) ∧ w = val) →
          ∀ x ∈ (List.finRange n).filterMap (fun q' =>
            match phase_delivered (lvPhase3G n) s.locals ho obs q' with
            | some (.accepted v') => some v'
            | _ => none), x = val := by
        intro obs val h_all_v x hx
        simp only [List.mem_filterMap, List.mem_finRange, true_and] at hx
        obtain ⟨r, hr⟩ := hx
        simp only [phase_delivered, lvPhase3G] at hr
        by_cases hho : ho obs r = true
        · simp only [hho, ite_true] at hr
          by_cases hacc_r : (s.locals r).core.accepted = true
          · obtain ⟨w', hw', hv'⟩ := h_all_v r hacc_r
            simp only [hacc_r, ite_true] at hr
            revert hr ; rw [hw'] ; simp ; intro hr ; rw [← hr] ; exact hv'
          · have hf : (s.locals r).core.accepted = false := by
              revert hacc_r ; cases (s.locals r).core.accepted <;> simp
            simp [hf] at hr
        · have hf : ho obs r = false := by revert hho ; cases ho obs r <;> simp
          simp [hf] at hr
      rcases h_dec_or p v hv with hp_old | ⟨mp, hmp_eq, hp_new, hp_maj⟩
      · rcases h_dec_or q w hw with hq_old | ⟨mq, hmq_eq, hq_new, hq_maj⟩
        · exact h_agree p q v w hp_old hq_old
        · have h_global_maj := h_global_maj_from q hq_maj
          have h_all_v := h_dec_prop p v hp_old hph_eq h_global_maj
          have h_mq_all_v := h_all_vals q v h_all_v
          have hw_in : w ∈ mq := by
            cases mq with
            | nil => simp at hq_new
            | cons a as => simp [List.head?] at hq_new ; subst hq_new ; exact List.Mem.head _
          exact (h_mq_all_v w (hmq_eq ▸ hw_in)).symm
      · rcases h_dec_or q w hw with hq_old | ⟨mq, hmq_eq, hq_new, hq_maj⟩
        · have h_global_maj := h_global_maj_from p hp_maj
          have h_all_w := h_dec_prop q w hq_old hph_eq h_global_maj
          have h_mp_all_w := h_all_vals p w h_all_w
          have hv_in : v ∈ mp := by
            cases mp with
            | nil => simp at hp_new
            | cons a as => simp [List.head?] at hp_new ; subst hp_new ; exact List.Mem.head _
          exact h_mp_all_w v (hmp_eq ▸ hv_in)
        · -- Both new
          have hv_in : v ∈ mp := by
            cases mp with
            | nil => simp at hp_new
            | cons a as => simp [List.head?] at hp_new ; subst hp_new ; exact List.Mem.head _
          have hw_in : w ∈ mq := by
            cases mq with
            | nil => simp at hq_new
            | cons a as => simp [List.head?] at hq_new ; subst hq_new ; exact List.Mem.head _
          rw [hmp_eq] at hv_in
          simp only [List.mem_filterMap, List.mem_finRange, true_and] at hv_in
          obtain ⟨r₁, hr₁⟩ := hv_in
          rw [hmq_eq] at hw_in
          simp only [List.mem_filterMap, List.mem_finRange, true_and] at hw_in
          obtain ⟨r₂, hr₂⟩ := hw_in
          simp only [phase_delivered, lvPhase3G] at hr₁ hr₂
          have h_r₁_acc : (s.locals r₁).core.accepted = true := by
            by_cases hho : ho p r₁ = true
            · simp only [hho, ite_true] at hr₁
              by_cases hacc : (s.locals r₁).core.accepted = true
              · exact hacc
              · have hf : (s.locals r₁).core.accepted = false := by
                  revert hacc ; cases (s.locals r₁).core.accepted <;> simp
                simp [hf] at hr₁
            · have hf : ho p r₁ = false := by revert hho ; cases ho p r₁ <;> simp
              simp [hf] at hr₁
          have h_r₂_acc : (s.locals r₂).core.accepted = true := by
            by_cases hho : ho q r₂ = true
            · simp only [hho, ite_true] at hr₂
              by_cases hacc : (s.locals r₂).core.accepted = true
              · exact hacc
              · have hf : (s.locals r₂).core.accepted = false := by
                  revert hacc ; cases (s.locals r₂).core.accepted <;> simp
                simp [hf] at hr₂
            · have hf : ho q r₂ = false := by revert hho ; cases ho q r₂ <;> simp
              simp [hf] at hr₂
          obtain ⟨v₁, hv₁⟩ := h_ph3 hph_eq r₁ h_r₁_acc
          obtain ⟨v₂, hv₂⟩ := h_ph3 hph_eq r₂ h_r₂_acc
          have hv_eq := h_uniform hph_eq r₁ r₂ v₁ v₂ h_r₁_acc h_r₂_acc hv₁ hv₂
          have hv_val : v = v₁ := by
            by_cases hho : ho p r₁ = true
            · simp [hho, h_r₁_acc, hv₁] at hr₁ ; exact hr₁.symm
            · have hf : ho p r₁ = false := by revert hho ; cases ho p r₁ <;> simp
              simp [hf] at hr₁
          have hw_val : w = v₂ := by
            by_cases hho : ho q r₂ = true
            · simp [hho, h_r₂_acc, hv₂] at hr₂ ; exact hr₂.symm
            · have hf : ho q r₂ = false := by revert hho ; cases ho q r₂ <;> simp
              simp [hf] at hr₂
          rw [hv_val, hw_val, hv_eq]
    · -- (B) Accepted: lvPhase3G always sets accepted := false
      intro p hacc
      have h_false : (s'.locals p).core.accepted = false := by
        rw [hlocals' p]
        simp [lvPhase3G, hasMajG, phase_delivered]
        split <;> (try split) <;> simp
      simp [h_false] at hacc
    · -- (C) s'.phase = 0 ≠ 3
      intro hph3' ; rw [hs'_phase] at hph3' ; simp at hph3'
    · -- (D) s'.phase = 0 ≠ 3
      intro p v _ hph3' ; rw [hs'_phase] at hph3' ; simp at hph3'
    · -- (E) Round sync
      intro p ; rw [hlocals' p, hs'_round]
      simp only [lvPhase3G, phase_delivered, h_rsync p]
    · -- (F') Phase 3 resets accepted to false
      intro p hacc
      have h_false : (s'.locals p).core.accepted = false := by
        rw [hlocals' p]
        simp [lvPhase3G, hasMajG, phase_delivered]
        split <;> (try split) <;> simp
      simp [h_false] at hacc
    · -- (F) s'.phase = 0 ≠ 3
      intro hph3' ; rw [hs'_phase] at hph3' ; simp at hph3'
    · -- (G) Cross-ballot with safe ballot formulation
      intro p v hv
      have h_lv : ∀ r, (s'.locals r).core.lastVote = (s.locals r).core.lastVote := by
        intro r ; rw [hlocals' r]
        simp only [lvPhase3G, phase_delivered]
        split <;> (try split) <;> simp
      rw [hlocals' p] at hv
      simp only [lvPhase3G, phase_delivered] at hv
      split at hv
      · case _ hmaj =>
        split at hv
        · case _ v' hhead =>
          simp at hv ; subst hv
          let acceptedVals : List Value := (List.finRange n).filterMap (fun q' =>
            match phase_delivered (lvPhase3G n) s.locals ho p q' with
            | some (.accepted x) => some x
            | _ => none)
          have hhead' : acceptedVals.head? = some v' := by
            simpa [acceptedVals] using hhead
          have hv'_mem : v' ∈ acceptedVals := by
            cases hvals : acceptedVals with
            | nil => simp [hvals] at hhead'
            | cons x xs =>
              have hx : x = v' := by simpa [hvals] using hhead'
              subst hx ; simp
          have h_msg_v' : ∃ r₀ : Fin n,
              phase_delivered (lvPhase3G n) s.locals ho p r₀ = some (.accepted v') := by
            rcases (by
              simpa [acceptedVals] using hv'_mem :
                ∃ a, (match phase_delivered (lvPhase3G n) s.locals ho p a with
                  | some (.accepted x) => some x
                  | _ => none) = some v') with ⟨r₀, hr₀⟩
            cases hdel : phase_delivered (lvPhase3G n) s.locals ho p r₀ with
            | none => rw [hdel] at hr₀ ; simp at hr₀
            | some m =>
              rw [hdel] at hr₀
              cases m <;> simp at hr₀
              case accepted x => cases hr₀ ; exact ⟨r₀, by simp [hdel]⟩
          obtain ⟨r₀, hr₀⟩ := h_msg_v'
          have h_impl : ∀ r : Fin n,
              (match phase_delivered (lvPhase3G n) s.locals ho p r with
                | some (.accepted _) => true | _ => false) = true →
              (s.locals r).core.accepted = true := by
            intro r hr_filt
            simp only [phase_delivered, lvPhase3G] at hr_filt
            by_cases hho : ho p r = true
            · simp only [hho, ite_true] at hr_filt
              by_cases hacc : (s.locals r).core.accepted = true
              · exact hacc
              · have hf : (s.locals r).core.accepted = false := by
                  revert hacc ; cases (s.locals r).core.accepted <;> simp
                simp [hf] at hr_filt
            · have hf : ho p r = false := by revert hho ; cases ho p r <;> simp
              simp [hf] at hr_filt
          have h_mono := filter_length_mono (List.finRange n)
            (fun r => match phase_delivered (lvPhase3G n) s.locals ho p r with
              | some (.accepted _) => true | _ => false)
            (fun r => (s.locals r).core.accepted) h_impl
          have h_filter_eq : (List.finRange n).filter (fun r =>
              match phase_delivered (lvPhase3G n) s.locals ho p r with
              | some (.accepted _) => true | _ => false) =
            (List.finRange n).filter (fun r =>
              match (if ho p r = true then
                some (if (s.locals r).core.accepted = true then
                  match (s.locals r).core.lastVote with
                  | some (v, _) => LVMsg.accepted v
                  | none => LVMsg.notAccepted
                else LVMsg.notAccepted)
              else none) with
              | some (.accepted _) => true | _ => false) := by
            simp [phase_delivered, lvPhase3G]
          have h_global_maj : hasMajG n (fun r => (s.locals r).core.accepted) = true := by
            unfold hasMajG at hmaj ⊢
            simp only [decide_eq_true_eq] at hmaj ⊢
            rw [h_filter_eq] at h_mono
            omega
          have h_r₀_acc : (s.locals r₀).core.accepted = true :=
            h_impl r₀ (by simp [hr₀])
          obtain ⟨u₀, hu₀⟩ := h_ph3 hph_eq r₀ h_r₀_acc
          have hu₀_eq_v' : u₀ = v' := by
            have hmsg := hr₀
            simp only [phase_delivered, lvPhase3G] at hmsg
            by_cases hho : ho p r₀ = true
            · simp [hho, h_r₀_acc, hu₀] at hmsg ; exact hmsg
            · have hf : ho p r₀ = false := by revert hho ; cases ho p r₀ <;> simp
              simp [hf] at hmsg
          have h_acc_val : ∀ r : Fin n, (s.locals r).core.accepted = true →
              (s.locals r).core.lastVote = some (v', s.round) := by
            intro r hr
            obtain ⟨u, hu⟩ := h_ph3 hph_eq r hr
            have hu_eq : u = u₀ := h_uniform hph_eq r r₀ u u₀ hr h_r₀_acc hu hu₀
            rw [hu_eq, hu₀_eq_v'] at hu ; exact hu
          refine ⟨⟨s.round, by omega, ?_, ?_⟩, ?_⟩
          · -- G1: non-v' votes have ballot < s.round
            intro q₁ w b₁ hlv₁ hw
            have hlv₁s : (s.locals q₁).core.lastVote = some (w, b₁) := by
              rwa [h_lv q₁] at hlv₁
            -- q₁ with non-v' vote cannot be accepted (accepted → lastVote value = v')
            have h_q₁_not_acc : (s.locals q₁).core.accepted = false := by
              by_cases hacc₁ : (s.locals q₁).core.accepted = true
              · have hq₁v := h_acc_val q₁ hacc₁
                rw [hq₁v] at hlv₁s
                simp only [Option.some.injEq, Prod.mk.injEq] at hlv₁s
                exact (hw hlv₁s.1.symm).elim
              · revert hacc₁ ; cases (s.locals q₁).core.accepted <;> simp
            -- By (H), b₁ ≤ s.round. If b₁ = s.round, then by (H), accepted = true. Contradiction.
            have hb₁ := h_ballot_bound q₁ w b₁ hlv₁s
            have hb₁_ne : b₁ ≠ s.round := by
              intro hb_eq
              have hcur := hb₁.2 hb_eq
              rw [h_q₁_not_acc] at hcur ; simp at hcur
            omega
          · -- G1 majority: majority of v'-voters at ≥ s.round
            -- The accepted majority have (v', s.round). These are in the filter.
            have h_mono_v : ((List.finRange n).filter fun q => (s.locals q).core.accepted).length ≤
                ((List.finRange n).filter fun q =>
                  match (s'.locals q).core.lastVote with
                  | some (w, b) => decide (w = v' ∧ b ≥ s.round)
                  | none => false).length := by
              apply filter_length_mono
              intro q hq
              have hqv := h_acc_val q hq
              have hqv' : (s'.locals q).core.lastVote = some (v', s.round) := by
                rw [h_lv q, hqv]
              rw [hqv'] ; simp
            unfold hasMajG at h_global_maj
            simp only [decide_eq_true_eq] at h_global_maj
            omega
          · -- G3: s'.phase = 0, val < 2. Vacuous.
            intro hph_ge2
            simp [hs'_phase] at hph_ge2
        · -- decidedVal = none: old decision preserved
          simp at hv
          obtain ⟨⟨b_safe, hbs_le, hbs_below, hbs_maj⟩, hG3⟩ := h_cross p v hv
          refine ⟨⟨b_safe, by omega, ?_, ?_⟩, ?_⟩
          · intro q₁ w b₁ hlv₁ hw
            rw [h_lv q₁] at hlv₁
            exact hbs_below q₁ w b₁ hlv₁ hw
          · have : (List.finRange n).filter (fun q => match (s'.locals q).core.lastVote with
                | some (w, b) => decide (w = v ∧ b ≥ b_safe) | none => false) =
              (List.finRange n).filter (fun q => match (s.locals q).core.lastVote with
                | some (w, b) => decide (w = v ∧ b ≥ b_safe) | none => false) := by
              congr 1 ; funext q ; simp [h_lv q]
            rw [this] ; exact hbs_maj
          · intro hph_ge2 ; simp [hs'_phase] at hph_ge2
      · -- no majority: old decision preserved
        simp at hv
        obtain ⟨⟨b_safe, hbs_le, hbs_below, hbs_maj⟩, hG3⟩ := h_cross p v hv
        refine ⟨⟨b_safe, by omega, ?_, ?_⟩, ?_⟩
        · intro q₁ w b₁ hlv₁ hw
          rw [h_lv q₁] at hlv₁
          exact hbs_below q₁ w b₁ hlv₁ hw
        · have : (List.finRange n).filter (fun q => match (s'.locals q).core.lastVote with
              | some (w, b) => decide (w = v ∧ b ≥ b_safe) | none => false) =
            (List.finRange n).filter (fun q => match (s.locals q).core.lastVote with
              | some (w, b) => decide (w = v ∧ b ≥ b_safe) | none => false) := by
            congr 1 ; funext q ; simp [h_lv q]
          rw [this] ; exact hbs_maj
        · intro hph_ge2 ; simp [hs'_phase] at hph_ge2
    · -- (H) Ballot bound
      intro q w b hlv
      have h_lv : (s'.locals q).core.lastVote = (s.locals q).core.lastVote := by
        rw [hlocals' q] ; simp only [lvPhase3G, phase_delivered]
        split <;> (try split) <;> simp
      rw [h_lv] at hlv
      have hb := h_ballot_bound q w b hlv
      refine ⟨by rw [hs'_round] ; omega, ?_⟩
      intro hb_eq
      exfalso
      rw [hs'_round] at hb_eq
      omega
    · -- (I) Same-ballot agreement: lastVote unchanged
      intro q₁ q₂ v₁ v₂ b hlv₁ hlv₂
      have h_lv : ∀ r, (s'.locals r).core.lastVote = (s.locals r).core.lastVote := by
        intro r ; rw [hlocals' r]
        simp only [lvPhase3G, phase_delivered]
        split <;> (try split) <;> simp
      rw [h_lv q₁] at hlv₁ ; rw [h_lv q₂] at hlv₂
      exact h_same_ballot q₁ q₂ v₁ v₂ b hlv₁ hlv₂
/-! ### Safety theorem -/

/-- Agreement is an invariant of the general-n phased LastVoting protocol. -/
theorem lv_agreement_gen :
    pred_implies (lvLeslieSpecG n hn).safety [tlafml| □ ⌜agreementG n⌝] := by
  suffices h : pred_implies (lvLeslieSpecG n hn).safety
      [tlafml| □ ⌜lv_inv_gen n hn⌝] by
    intro e he k
    exact (h e he k).1
  apply phase_round_invariant (lvSpecG n hn) (by omega)
  · exact lv_inv_init_gen n hn
  · exact lv_inv_step_gen n hn

end Gen


end LastVotingPhased
