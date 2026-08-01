import Leslie.Examples.LastVotingPhased.Defs

/-! ## N=3 LastVoting safety proof

    Proves the 9-conjunct inductive invariant `lv_inv` for the
    n = 3 specialization of LastVoting.
    See `Defs.lean` for the protocol definition and invariant statement. -/

open TLA

namespace LastVotingPhased

/-! ### N=3 specific lemmas -/

/-- In a 3-process system, if two distinct processes are not in the filtered
    set, then that set has size at most 1. -/
private theorem filter_len_le_one_of_two_distinct_false
    (acc : Proc → Bool) (q₁ q₂ : Proc)
    (hq₁ : acc q₁ = false) (hq₂ : acc q₂ = false) (hne : q₁ ≠ q₂) :
    ((List.finRange 3).filter fun r => acc r).length ≤ 1 := by
  rcases q₁ with ⟨q1, hq1lt⟩
  rcases q₂ with ⟨q2, hq2lt⟩
  simp at hq₁ hq₂ hne ⊢
  have hq1_cases : q1 = 0 ∨ q1 = 1 ∨ q1 = 2 := by omega
  have hq2_cases : q2 = 0 ∨ q2 = 1 ∨ q2 = 2 := by omega
  rcases hq1_cases with rfl | rfl | rfl
  · rcases hq2_cases with rfl | rfl | rfl
    · cases hne rfl
    · have hq₁' : acc 0 = false := by simpa using hq₁
      have hq₂' : acc 1 = false := by simpa using hq₂
      change (([0, 1, 2].filter fun r => acc r).length ≤ 1)
      cases h : acc 2 <;> simp [hq₁', hq₂', h]
    · have hq₁' : acc 0 = false := by simpa using hq₁
      have hq₂' : acc 2 = false := by simpa using hq₂
      change (([0, 1, 2].filter fun r => acc r).length ≤ 1)
      cases h : acc 1 <;> simp [hq₁', hq₂', h]
  · rcases hq2_cases with rfl | rfl | rfl
    · have hq₁' : acc 1 = false := by simpa using hq₁
      have hq₂' : acc 0 = false := by simpa using hq₂
      change (([0, 1, 2].filter fun r => acc r).length ≤ 1)
      cases h : acc 2 <;> simp [hq₁', hq₂', h]
    · cases hne rfl
    · have hq₁' : acc 1 = false := by simpa using hq₁
      have hq₂' : acc 2 = false := by simpa using hq₂
      change (([0, 1, 2].filter fun r => acc r).length ≤ 1)
      cases h : acc 0 <;> simp [hq₁', hq₂', h]
  · rcases hq2_cases with rfl | rfl | rfl
    · have hq₁' : acc 2 = false := by simpa using hq₁
      have hq₂' : acc 0 = false := by simpa using hq₂
      change (([0, 1, 2].filter fun r => acc r).length ≤ 1)
      cases h : acc 1 <;> simp [hq₁', hq₂', h]
    · have hq₁' : acc 2 = false := by simpa using hq₁
      have hq₂' : acc 1 = false := by simpa using hq₂
      change (([0, 1, 2].filter fun r => acc r).length ≤ 1)
      cases h : acc 0 <;> simp [hq₁', hq₂', h]
    · cases hne rfl



/-! ### Safety property -/

/-- Agreement (n = 3): if two processes have decided, they decided the same value. -/
def agreement (s : PhaseRoundState Proc LVState 4) : Prop :=
  ∀ (p q : Proc) (v w : Value),
    (s.locals p).core.decided = some v →
    (s.locals q).core.decided = some w →
    v = w

/-! ### Invariant (n = 3)

    The inductive invariant combines several properties. The quorum
    arguments (G1, G2, G3 and the decision case in D) rely on the
    fact that two majorities of 3 processes (each of size ≥ 2) must
    overlap. For general n, these would use `cross_phase_quorum_intersection`.

    (A) **Agreement**: all existing decisions agree.

    (B) **Accepted consistency**: if a process has `accepted = true`,
        its `lastVote` matches the current ballot's proposal.

    (C) **Phase 3 consistency**: in phase 3, acceptors' lastVotes match
        the proposal.

    (D) **Decision-proposal consistency**: any existing decision agrees
        with the current proposal (if a majority accepted).

    (E) **Round synchronization**: `roundNum` in local state matches the
        global round counter. -/

def lv_inv (s : PhaseRoundState Proc LVState 4) : Prop :=
  -- (A) Agreement on all decisions made so far
  agreement s ∧
  -- (B) If a process accepted in this ballot, its lastVote matches a proposal
  (∀ p : Proc, (s.locals p).core.accepted = true →
    ∃ v b, (s.locals p).core.lastVote = some (v, b) ∧
      b = s.round) ∧
  -- (C) Phase 3 consistency
  (s.phase = ⟨3, by omega⟩ →
    ∀ p : Proc, (s.locals p).core.accepted = true →
    ∃ v, (s.locals p).core.lastVote = some (v, s.round)) ∧
  -- (D) Decision-proposal consistency: existing decisions agree with any
  --     new majority accept in phase 3
  (∀ p : Proc, ∀ v, (s.locals p).core.decided = some v →
    s.phase = ⟨3, by omega⟩ →
    hasMaj3 (fun q => (s.locals q).core.accepted) = true →
    -- All acceptors have the same value
    ∀ q : Proc, (s.locals q).core.accepted = true →
    ∃ w, (s.locals q).core.lastVote = some (w, s.round) ∧ w = v) ∧
  -- (E) Round synchronization
  (∀ p : Proc, (s.locals p).roundNum = s.round) ∧
  -- (F') Acceptance only at phase 3: if accepted, we must be in phase 3
  (∀ p : Proc, (s.locals p).core.accepted = true → s.phase = ⟨3, by omega⟩) ∧
  -- (F) Uniform value: at phase 3, all accepted processes agree on lastVote value
  (s.phase = ⟨3, by omega⟩ →
    ∀ (p q : Proc) (vp vq : Value),
    (s.locals p).core.accepted = true →
    (s.locals q).core.accepted = true →
    (s.locals p).core.lastVote = some (vp, s.round) →
    (s.locals q).core.lastVote = some (vq, s.round) →
    vp = vq) ∧
  -- (G) Cross-ballot: decided value dominates all lastVote values.
  -- If decided v, then:
  --   (G1) Non-v votes have strictly lower ballots than all v-votes.
  --   (G2) ≥ 2 processes have lastVote value v.
  --   (G3) At phase ≥ 2, the coordinator's proposal (if set) equals v.
  (∀ p v, (s.locals p).core.decided = some v →
    (∀ q₁ w b₁, (s.locals q₁).core.lastVote = some (w, b₁) → w ≠ v →
      ∀ q₂ b₂, (s.locals q₂).core.lastVote = some (v, b₂) → b₁ < b₂) ∧
    ((List.finRange 3).filter fun q =>
      match (s.locals q).core.lastVote with
      | some (w, _) => decide (w = v) | none => false).length ≥ 2 ∧
    (s.phase.val ≥ 2 →
      ∀ w, (s.locals (coordinator s.round)).core.proposal = some w → w = v)) ∧
  -- (H) Ballot bound: all lastVote ballots are ≤ s.round.
  -- Moreover, if a process stores a vote from the current round, then that
  -- vote came from the phase-2 accept step of the current round, so the
  -- process must still be in phase 3 with `accepted = true`.
  (∀ q w b, (s.locals q).core.lastVote = some (w, b) →
    b ≤ s.round ∧
    (b = s.round →
      s.phase = ⟨3, by omega⟩ ∧ (s.locals q).core.accepted = true))

/-! ### Invariant proofs -/

theorem lv_inv_init :
    ∀ s, lvLeslieSpec.init s → lv_inv s := by
  intro s ⟨hround, hphase, hinit⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Agreement: vacuously true, no decisions
    intro p q v w hv hw
    have hp := (hinit p).2
    simp at hp ; rw [hp] at hv ; simp at hv
  · -- Accepted consistency: vacuously true, no accepts
    intro p hacc
    have hp := (hinit p).2
    simp at hp ; rw [hp] at hacc ; simp at hacc
  · -- Phase 3 consistency: phase = 0 ≠ 3
    intro hph ; simp [hphase] at hph
  · -- Decision-proposal consistency: vacuously true
    intro p v hv
    have hp := (hinit p).2
    simp at hp ; rw [hp] at hv ; simp at hv
  · -- Round synchronization
    intro p
    have hp := (hinit p).1
    simp at hp ; rw [hround, hp]
  · -- (F') Acceptance only at phase 3: vacuous, no accepts at init
    intro p hacc
    have hp := (hinit p).2
    simp at hp ; rw [hp] at hacc ; simp at hacc
  · -- (F) Uniform value: phase = 0 ≠ 3
    intro hph ; simp [hphase] at hph
  · -- (G) Cross-ballot: vacuously true, no decisions at init
    intro p v hv
    have hp := (hinit p).2
    simp at hp ; rw [hp] at hv ; simp at hv
  · -- (H) Ballot bound: vacuously true, all lastVote = none at init
    intro q w b hlv
    have hp := (hinit q).2
    simp at hp ; rw [hp] at hlv ; simp at hlv

/-- The main invariant preservation theorem (n = 3).
    Each of the 4 phase transitions preserves `lv_inv`.
    The Phase 1→2 and Phase 3→0 cases use quorum intersection for n = 3
    (two sets of size ≥ 2 out of 3 must overlap). -/
theorem lv_inv_step :
    ∀ s ho, lv_inv s → lvComm s.round s.phase ho →
    ∀ s', phase_step lvAlg ho s s' → lv_inv s' := by
  intro s ho ⟨h_agree, h_acc, h_ph3, h_dec_prop, h_rsync, h_acc_ph3, h_uniform, h_cross, h_ballot_bound⟩ _ s' ⟨hadvance, hlocals⟩
  -- Determine which phase we're in
  have hph : s.phase.val = 0 ∨ s.phase.val = 1 ∨ s.phase.val = 2 ∨ s.phase.val = 3 := by
    have := s.phase.isLt ; omega
  rcases hph with hph0 | hph1 | hph2 | hph3
  · ---- Phase 0 → Phase 1 (Prepare → Promise) ----
    -- Phase 0 resets `accepted := false`, sets `prepared`, resets coordinator's proposal.
    -- No new decisions, no new accepts. Invariant mostly trivially preserved.
    have hph_eq : s.phase = ⟨0, by omega⟩ := Fin.ext hph0
    have h_phase : lvAlg.phases s.phase = lvPhase0 := by simp [lvAlg, hph_eq]
    -- s' has phase = 1, same round
    have hs'_phase : s'.phase = ⟨1, by omega⟩ := by
      simp [hph0] at hadvance ; exact hadvance.2
    have hs'_round : s'.round = s.round := by
      simp [hph0] at hadvance ; exact hadvance.1
    -- What hlocals says for each process after unfolding
    have hlocals' : ∀ p, s'.locals p = lvPhase0.update p (s.locals p)
        (phase_delivered lvPhase0 s.locals ho p) := by
      intro p ; have := hlocals p ; rwa [h_phase] at this
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- (A) Agreement: no new decisions (phase0Update doesn't touch `decided`)
      intro p q v w hv hw
      rw [hlocals' p] at hv ; rw [hlocals' q] at hw
      simp [lvPhase0, phase_delivered] at hv hw
      exact h_agree p q v w hv hw
    · -- (B) Accepted consistency: accepted is reset to false
      intro p hacc
      rw [hlocals' p] at hacc
      simp [lvPhase0, phase_delivered] at hacc
    · -- (C) Phase 3 consistency: s'.phase = 1 ≠ 3, vacuous
      intro hph3' ; rw [hs'_phase] at hph3' ; simp at hph3'
    · -- (D) Decision-proposal: s'.phase = 1 ≠ 3, vacuous
      intro p v _ hph3' ; rw [hs'_phase] at hph3' ; simp at hph3'
    · -- (E) Round sync: round unchanged, roundNum unchanged by phase0Update
      intro p ; rw [hlocals' p]
      simp [lvPhase0, phase_delivered, hs'_round]
      exact h_rsync p
    · -- (F') Phase 0 resets accepted to false
      intro p hacc ; rw [hlocals' p] at hacc
      simp [lvPhase0, phase_delivered] at hacc
    · -- (F) s'.phase = 1 ≠ 3, vacuous
      intro hph3' ; rw [hs'_phase] at hph3' ; simp at hph3'
    · -- (G) Cross-ballot: decided/lastVote unchanged by phase 0.
      intro p v hv
      -- decided preserved
      have h_dec : ∀ r, (s'.locals r).core.decided = (s.locals r).core.decided := by
        intro r ; rw [hlocals' r] ; simp [lvPhase0, phase_delivered]
      rw [h_dec p] at hv
      -- lastVote preserved
      have h_lv : ∀ r, (s'.locals r).core.lastVote = (s.locals r).core.lastVote := by
        intro r ; rw [hlocals' r] ; simp [lvPhase0, phase_delivered]
      obtain ⟨hG1, hG2, hG3⟩ := h_cross p v hv
      refine ⟨?_, ?_, ?_⟩
      · intro q₁ w b₁ hlv₁ hw q₂ b₂ hlv₂
        rw [h_lv q₁] at hlv₁ ; rw [h_lv q₂] at hlv₂
        exact hG1 q₁ w b₁ hlv₁ hw q₂ b₂ hlv₂
      · -- lastVote unchanged → filter count unchanged
        have : (List.finRange 3).filter (fun q => match (s'.locals q).core.lastVote with
            | some (w, _) => decide (w = v) | none => false) =
          (List.finRange 3).filter (fun q => match (s.locals q).core.lastVote with
            | some (w, _) => decide (w = v) | none => false) := by
          congr 1 ; funext q ; simp [h_lv q]
        rw [this] ; exact hG2
      · -- s'.phase = 1, val < 2. Vacuous.
        intro hph_ge2 ; simp [hs'_phase] at hph_ge2
    · -- (H) Ballot bound: lastVote unchanged, round unchanged.
      intro q w b hlv
      have h_lv : (s'.locals q).core.lastVote = (s.locals q).core.lastVote := by
        rw [hlocals' q] ; simp [lvPhase0, phase_delivered]
      rw [h_lv] at hlv
      have hb := h_ballot_bound q w b hlv
      refine ⟨by rw [hs'_round] ; exact hb.1, ?_⟩
      intro hb_eq
      exfalso
      have hcur := hb.2 (by rwa [hs'_round] at hb_eq)
      rw [hcur.1] at hph0
      simp at hph0
  · ---- Phase 1 → Phase 2 (Promise → Accept) ----
    -- Coordinator collects promises and stores proposal. Others unchanged.
    -- No new decisions, no new accepts.
    have hph_eq : s.phase = ⟨1, by omega⟩ := Fin.ext hph1
    have h_phase : lvAlg.phases s.phase = lvPhase1 := by simp [lvAlg, hph_eq]
    have hs'_phase : s'.phase = ⟨2, by omega⟩ := by
      simp [hph1] at hadvance ; exact hadvance.2
    have hs'_round : s'.round = s.round := by
      simp [hph1] at hadvance ; exact hadvance.1
    have hlocals' : ∀ p, s'.locals p = lvPhase1.update p (s.locals p)
        (phase_delivered lvPhase1 s.locals ho p) := by
      intro p ; have := hlocals p ; rwa [h_phase] at this
    -- Helper: lvPhase1 preserves accepted
    have h_acc_pres : ∀ r, (s'.locals r).core.accepted = (s.locals r).core.accepted := by
      intro r ; rw [hlocals' r] ; simp only [lvPhase1, phase_delivered]
      split <;> (try split) <;> simp
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- (A) Agreement: lvPhase1.update only changes `proposal`, not `decided`
      intro p q v w hv hw
      have h_dec : ∀ r, (s'.locals r).core.decided = (s.locals r).core.decided := by
        intro r ; rw [hlocals' r]
        simp only [lvPhase1, phase_delivered]
        split <;> (try split) <;> simp
      rw [h_dec p] at hv ; rw [h_dec q] at hw
      exact h_agree p q v w hv hw
    · -- (B) Accepted consistency: lvPhase1.update doesn't change `accepted` or `lastVote`
      intro p hacc
      rw [h_acc_pres p] at hacc
      obtain ⟨v, b, hvb, hb⟩ := h_acc p hacc
      have h_lv_pres : (s'.locals p).core.lastVote = (s.locals p).core.lastVote := by
        rw [hlocals' p] ; simp only [lvPhase1, phase_delivered]
        split <;> (try split) <;> simp
      exact ⟨v, b, by rw [h_lv_pres, hvb], by rw [hs'_round, hb]⟩
    · -- (C) Phase 3: s'.phase = 2 ≠ 3, vacuous
      intro hph3' ; rw [hs'_phase] at hph3' ; simp at hph3'
    · -- (D) Decision-proposal: s'.phase = 2 ≠ 3, vacuous
      intro p v _ hph3' ; rw [hs'_phase] at hph3' ; simp at hph3'
    · -- (E) Round sync: lvPhase1.update doesn't change roundNum
      intro p ; rw [hlocals' p, hs'_round]
      simp only [lvPhase1, phase_delivered]
      split <;> (try split) <;> simp [h_rsync p]
    · -- (F') accepted preserved → use h_acc_ph3 on pre-state
      intro p hacc' ; rw [h_acc_pres p] at hacc'
      have := h_acc_ph3 p hacc'
      rw [this] at hph1 ; simp at hph1
    · -- (F) s'.phase = 2 ≠ 3, vacuous
      intro hph3' ; rw [hs'_phase] at hph3' ; simp at hph3'
    · -- (G) Cross-ballot: decided/lastVote unchanged. (G1,G2) carry over.
      -- (G3) at phase ≥ 2: coordinator's proposal. NON-TRIVIAL at phase 2.
      intro p v hv
      have h_dec : ∀ r, (s'.locals r).core.decided = (s.locals r).core.decided := by
        intro r ; rw [hlocals' r] ; simp only [lvPhase1, phase_delivered]
        split <;> (try split) <;> simp
      rw [h_dec p] at hv
      have h_lv : ∀ r, (s'.locals r).core.lastVote = (s.locals r).core.lastVote := by
        intro r ; rw [hlocals' r] ; simp only [lvPhase1, phase_delivered]
        split <;> (try split) <;> simp
      obtain ⟨hG1, hG2, hG3⟩ := h_cross p v hv
      refine ⟨?_, ?_, ?_⟩
      · -- (G1) lastVote unchanged
        intro q₁ w b₁ hlv₁ hw q₂ b₂ hlv₂
        rw [h_lv q₁] at hlv₁ ; rw [h_lv q₂] at hlv₂
        exact hG1 q₁ w b₁ hlv₁ hw q₂ b₂ hlv₂
      · -- (G2) lastVote unchanged → filter count unchanged
        have : (List.finRange 3).filter (fun q => match (s'.locals q).core.lastVote with
            | some (w, _) => decide (w = v) | none => false) =
          (List.finRange 3).filter (fun q => match (s.locals q).core.lastVote with
            | some (w, _) => decide (w = v) | none => false) := by
          congr 1 ; funext q ; simp [h_lv q]
        rw [this] ; exact hG2
      · -- (G3) At phase ≥ 2: coordinator's proposal = v.
        -- s'.phase = 2. The coordinator MAY have set the proposal.
        -- This is the highestVote argument: the coordinator collected promises
        -- from ≥ 2 processes. By (G2), ≥ 2 have value v. By quorum intersection,
        -- the promise quorum includes a v-voter. By (G1), the v-voter's ballot
        -- is strictly higher than any non-v voter's ballot. So highestVote picks v.
        -- This requires reasoning about the foldl computation in lvPhase1.
        intro _ w h_prop
        -- The coordinator c set its proposal in lvPhase1.update.
        -- Extract what happened to c's proposal.
        let c := coordinator s.round
        rw [hs'_round] at h_prop
        rw [hlocals' c] at h_prop
        simp only [lvPhase1, phase_delivered] at h_prop
        -- c = coordinator s.round = coordinator (s.locals c).roundNum (by h_rsync)
        have hc_eq : c = coordinator (s.locals c).roundNum := by
          simp [c, h_rsync c]
        rw [if_pos hc_eq] at h_prop
        -- Now h_prop involves: if promiseCount ≥ 2 then prop = w else none = some w
        -- The collected list and the foldl computation
        split at h_prop
        · -- promiseCount ≥ 2: proposal = some prop
          case _ hcount =>
          simp at h_prop
          -- h_prop : prop = w where prop is from the foldl
          -- We need to show prop = v.
          -- The `collected` list contains (val, ballot) pairs from received promises.
          -- Each pair (val, bal) comes from a process q with lastVote = some (val, bal).
          -- By (G1): non-v elements have lower ballots than v-elements.
          -- By quorum intersection (≥ 2 promise senders ∩ ≥ 2 v-voters): ∃ v-element.
          -- By foldl_max_picks_dominated_value: foldl picks v. So prop = v = w.
          -- Define the collected list
          let msgs := fun q => phase_delivered lvPhase1 s.locals ho c q
          let collected := collectPromiseVotes msgs
          -- Show h_prop relates to foldl on collected
          -- The foldl picks the max-ballot value from collected
          -- If collected = [], prop = defaultValue (might not be v)
          -- If collected ≠ [], use foldl_max_picks_dominated_value
          -- First: collected contains a v-element (quorum intersection)
          -- The promise senders: processes q where msgs q = some (.promise _)
          -- Each sends its lastVote. By (G2): ≥ 2 have lastVote value v.
          -- The coordinator received ≥ 2 promises (hcount).
          -- Among those received, at least one has lastVote value v.
          -- That process contributes (v, b_v) to collected.
          -- The quorum intersection argument:
          -- Let A = {q | msgs q ≠ none} (heard by coordinator). |A| ≥ 2 (from hcount).
          -- Let B = {q | lastVote q has value v}. |B| ≥ 2 (from hG2).
          -- For n=3, |A| ≥ 2 and |B| ≥ 2 → |A ∩ B| ≥ 1.
          -- Formally: use filter_disjoint_length_le or maj3_intersect.
          -- Step 1: h_prop tells us w is the foldl result. We need w = v.
          -- The foldl operates on `collected`. We need to show collected ≠ []
          -- and then apply foldl_max_picks_dominated_value.
          -- The expression in h_prop uses the specific `collected` from lvPhase1.
          -- After the split, h_prop should have the form:
          -- match collected with | [] => defaultValue | (v0,b0) :: rest => foldl ... = w
          -- We case-split on collected.
          -- Actually, h_prop is already simplified. Let me work with what we have.
          -- The key: each element (val, bal) ∈ collected came from some process q
          -- with ho c q = true and (s.locals q).core.lastVote = some (val, bal).
          -- Step 1: collected elements are from pre-state lastVotes
          have h_collected_from_lv : ∀ vb ∈ collected, ∃ q,
              ho c q = true ∧ (s.locals q).core.lastVote = some vb := by
            intro vb hvb
            simp only [collected, collectPromiseVotes, msgs, List.mem_filterMap,
                        List.mem_finRange, true_and, phase_delivered, lvPhase1] at hvb
            obtain ⟨q, hq⟩ := hvb
            by_cases hho : ho c q = true
            · simp [hho] at hq
              cases hlv_q : (s.locals q).core.lastVote with
              | none => simp [hlv_q] at hq
              | some vb' => simp [hlv_q] at hq ; exact ⟨q, hho, by rw [hq] at hlv_q ; exact hlv_q⟩
            · have hf : ho c q = false := by revert hho ; cases ho c q <;> simp
              simp [hf] at hq
          -- Step 2: ∃ v-element in collected (quorum intersection)
          -- The promise senders: {q | ho c q = true}. Count ≥ 2 (from hcount).
          -- Actually hcount is about promiseCount ≥ 2, which counts processes
          -- where msgs q = some (.promise _). This includes both some vb and none.
          -- The v-voters: {q | lastVote q has value v}. |B| ≥ 2 (from hG2).
          -- Overlap: ≥ 1 process with ho c q = true and lastVote value v.
          -- That process contributes (v, b_v) to collected.
          have h_v_in_collected : ∃ vb ∈ collected, vb.1 = v := by
            -- Need: ∃ q heard by c with lastVote value v.
            -- Pigeonhole: |heard by c| ≥ 2 and |v-voters| ≥ 2 out of 3.
            -- promiseCount ≥ 2 means ≥ 2 processes with ho c q = true
            -- (since lvPhase1.send always produces .promise _, so the
            --  filter matches iff the message was received, i.e., ho c q = true).
            -- So we need: heard ≥ 2 ∧ v-voters ≥ 2 → overlap ≥ 1.
            -- Step: show promiseCount = |{q | ho c q}|
            have h_heard : ((List.finRange 3).filter (fun q => ho c q)).length ≥ 2 := by
              have : (List.finRange 3).filter (fun q =>
                  match msgs q with | some (.promise _) => true | _ => false) =
                (List.finRange 3).filter (fun q => ho c q) := by
                congr 1 ; funext q
                simp only [msgs, phase_delivered, lvPhase1]
                cases ho c q <;> simp
              rw [← this] ; exact hcount
            -- Quorum intersection: ≥ 2 + ≥ 2 out of 3 → overlap ≥ 1
            by_contra h_no_overlap
            have h_no : ∀ q, ¬(ho c q = true ∧ (match (s.locals q).core.lastVote with
                | some (w, _) => decide (w = v) | none => false) = true) := by
              intro q hq ; apply h_no_overlap
              obtain ⟨hho, hlv_q⟩ := hq
              cases hlv_q' : (s.locals q).core.lastVote with
              | none => simp [hlv_q'] at hlv_q
              | some vb =>
                simp [hlv_q', decide_eq_true_eq] at hlv_q
                obtain ⟨val, bal⟩ := vb
                simp at hlv_q
                -- (val, bal) with val = v
                refine ⟨(v, bal), ?_, rfl⟩
                simp only [collected, collectPromiseVotes, msgs, List.mem_filterMap,
                            List.mem_finRange, true_and, phase_delivered, lvPhase1]
                exact ⟨q, by simp [hho, hlv_q, hlv_q']⟩
            have h_sum := filter_disjoint_length_le
              (fun q => ho c q) (fun q => match (s.locals q).core.lastVote with
                | some (w, _) => decide (w = v) | none => false)
              (List.finRange 3) h_no
            have h_len : (List.finRange 3).length = 3 := List.length_finRange
            omega
          -- Step 3: non-v elements dominated (from G1)
          have h_dom_collected : ∀ x ∈ collected, x.1 ≠ v →
              ∀ y ∈ collected, y.1 = v → x.2 < y.2 := by
            intro x hx hxne y hy hyeq
            obtain ⟨qx, _, hqx_lv⟩ := h_collected_from_lv x hx
            obtain ⟨qy, _, hqy_lv⟩ := h_collected_from_lv y hy
            rw [show x = (x.1, x.2) from by simp] at hqx_lv
            rw [show y = (y.1, y.2) from by simp] at hqy_lv
            rw [hyeq] at hqy_lv
            exact hG1 qx x.1 x.2 hqx_lv hxne qy y.2 hqy_lv
          -- Step 4: Apply foldl_max_picks_dominated_value.
          -- h_prop is: (match collected with [] => defaultValue | hd::tl => foldl...) = w
          -- collected is nonempty (h_v_in_collected), so the [] case is impossible.
          -- In the hd::tl case, foldl_max_picks_dominated_value gives result = v.
          -- The connection between h_prop's match expression and `collected` is
          -- definitional (both are the same filterMap). We case-split on collected.
          obtain ⟨vb, hvb_mem, hvb_val⟩ := h_v_in_collected
          -- Case split on collected (= collectPromiseVotes msgs)
          cases hcol : collected with
          | nil => simp [hcol] at hvb_mem
          | cons init rest =>
            have h_exists : ∃ x ∈ init :: rest, x.1 = v :=
              ⟨vb, hcol ▸ hvb_mem, hvb_val⟩
            have h_dom : ∀ x ∈ init :: rest, x.1 ≠ v →
                ∀ y ∈ init :: rest, y.1 = v → x.2 < y.2 := by
              intro x hx hxne y hy hyeq
              exact h_dom_collected x (hcol ▸ hx) hxne y (hcol ▸ hy) hyeq
            have hpick_v :
                (rest.foldl (fun best cur => if cur.2 > best.2 then cur else best) init).1 = v :=
              foldl_max_picks_dominated_value rest init v h_exists h_dom
            -- h_prop says pickProposal collected = w. Unfold pickProposal with hcol.
            have hpick_w : pickProposal collected = w := by
              simp only [collectPromiseVotes, pickProposal] at h_prop
              exact h_prop
            rw [hcol, pickProposal] at hpick_w
            -- hpick_w : foldl ... = w, hpick_v : foldl ... = v
            -- The foldl uses `cur.2 > best.2` while hpick_w may use `best.2 < cur.2`
            have hpick_v' :
                (rest.foldl (fun best cur => if best.2 < cur.2 then cur else best) init).1 = v := by
              simpa [gt_iff_lt] using hpick_v
            exact hpick_w.symm.trans hpick_v'
        · -- promiseCount < 2: proposal = none ≠ some w
          simp at h_prop
    · -- (H) Ballot bound: lastVote unchanged, round unchanged.
      intro q w b hlv
      have h_lv : (s'.locals q).core.lastVote = (s.locals q).core.lastVote := by
        rw [hlocals' q] ; simp only [lvPhase1, phase_delivered]
        split <;> (try split) <;> simp
      rw [h_lv] at hlv
      have hb := h_ballot_bound q w b hlv
      refine ⟨by rw [hs'_round] ; exact hb.1, ?_⟩
      intro hb_eq
      exfalso
      have hcur := hb.2 (by rwa [hs'_round] at hb_eq)
      rw [hcur.1] at hph1
      simp at hph1
  · ---- Phase 2 → Phase 3 (Accept → Decide) ----
    -- Some processes accept the coordinator's proposal.
    -- No new decisions yet (decisions happen in Phase 3).
    -- The hard part: establishing conjunct (D) for Phase 3.
    have hph_eq : s.phase = ⟨2, by omega⟩ := Fin.ext hph2
    have h_phase : lvAlg.phases s.phase = lvPhase2 := by simp [lvAlg, hph_eq]
    have hs'_phase : s'.phase = ⟨3, by omega⟩ := by
      simp [hph2] at hadvance ; exact hadvance.2
    have hs'_round : s'.round = s.round := by
      simp [hph2] at hadvance ; exact hadvance.1
    have hlocals' : ∀ p, s'.locals p = lvPhase2.update p (s.locals p)
        (phase_delivered lvPhase2 s.locals ho p) := by
      intro p ; have := hlocals p ; rwa [h_phase] at this
    -- Helper: by (F'), no process is accepted at phase 2
    have h_no_acc : ∀ r, (s.locals r).core.accepted = false := by
      intro r ; by_contra h
      have := h_acc_ph3 r (by revert h ; cases (s.locals r).core.accepted <;> simp)
      rw [this] at hph2 ; simp at hph2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- (A) Agreement: lvPhase2.update doesn't change `decided`
      intro p q v w hv hw
      have h_dec : ∀ r, (s'.locals r).core.decided = (s.locals r).core.decided := by
        intro r ; rw [hlocals' r]
        simp only [lvPhase2, phase_delivered]
        split <;> simp
      rw [h_dec p] at hv ; rw [h_dec q] at hw
      exact h_agree p q v w hv hw
    · -- (B) Accepted: if accepted in s', lastVote matches current round
      intro p hacc
      rw [hlocals' p] at hacc
      simp only [lvPhase2, phase_delivered] at hacc
      rw [hlocals' p]
      simp only [lvPhase2, phase_delivered]
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
      simp only [lvPhase2, phase_delivered] at hacc ⊢
      split
      · case _ v' _ =>
        exact ⟨v', by simp ; rw [h_rsync p, hs'_round]⟩
      · case _ _ =>
        simp at hacc
        obtain ⟨v, b, hvb, hb⟩ := h_acc p hacc
        exact ⟨v, by rw [hvb, hb, hs'_round]⟩
    · -- (D) Decision-proposal consistency: follows from (G3).
      -- By (G3): coordinator's proposal = v. By (F): all accepted have same value.
      -- So all accepted have value v.
      intro p v hdec _ hmaj q hacc_q
      have h_dec : ∀ r, (s'.locals r).core.decided = (s.locals r).core.decided := by
        intro r ; rw [hlocals' r] ; simp only [lvPhase2, phase_delivered] ; split <;> simp
      rw [h_dec p] at hdec
      obtain ⟨_, _, hG3⟩ := h_cross p v hdec
      -- Coordinator's proposal: by (G3), if some w then w = v
      -- Case split on coordinator's proposal
      cases h_prop : (s.locals (coordinator s.round)).core.proposal with
      | none =>
        -- No proposal → coordinator sends .skip → no one accepts → contradiction
        exfalso
        rw [hlocals' q] at hacc_q
        simp only [lvPhase2, phase_delivered, h_rsync q] at hacc_q
        by_cases hho : ho q (coordinator s.round) = true
        · simp only [hho, ite_true, h_rsync (coordinator s.round), h_prop] at hacc_q
          rw [h_no_acc q] at hacc_q ; simp at hacc_q
        · have hf : ho q (coordinator s.round) = false := by
            revert hho ; cases ho q (coordinator s.round) <;> simp
          simp [hf, h_no_acc q] at hacc_q
      | some w =>
        -- Proposal = some w. By (G3): w = v.
        have hw_eq := hG3 (by omega) w h_prop
        -- Coordinator sends .propose w = .propose v
        -- q accepted: received .propose v. lastVote = (v, round).
        rw [hlocals' q] at hacc_q ⊢
        simp only [lvPhase2, phase_delivered, h_rsync q] at hacc_q ⊢
        by_cases hho : ho q (coordinator s.round) = true
        · simp only [hho, ite_true, h_rsync (coordinator s.round), h_prop] at hacc_q ⊢
          exact ⟨w, by simp [hs'_round], hw_eq⟩
        · have hf : ho q (coordinator s.round) = false := by
            revert hho ; cases ho q (coordinator s.round) <;> simp
          simp [hf, h_no_acc q] at hacc_q
    · -- (E) Round sync: lvPhase2.update doesn't change roundNum
      intro p ; rw [hlocals' p, hs'_round]
      simp only [lvPhase2, phase_delivered]
      split <;> simp [h_rsync p]
    · -- (F') accepted → phase = 3. s'.phase = 3, so just need True.
      intro _ _ ; exact hs'_phase
    · -- (F) Uniform value: all accepted in s' got the same proposal from coordinator.
      -- By h_no_acc, no process was accepted in s. So any accepted in s' must be
      -- newly accepted via lvPhase2.update receiving .propose from the coordinator.
      -- The coordinator sends the same message to all, so the value is uniform.
      intro _ p q vp vq hacc_p hacc_q hlv_p hlv_q
      -- Show: (s'.locals p).core.lastVote = (s'.locals q).core.lastVote
      -- Then from hlv_p and hlv_q we get vp = vq.
      suffices h_eq : (s'.locals p).core.lastVote = (s'.locals q).core.lastVote by
        rw [hlv_p, hlv_q] at h_eq
        simp only [Option.some.injEq, Prod.mk.injEq] at h_eq
        exact h_eq.1
      -- Prove both lastVotes are the same by showing both come from the same function
      -- applied to the same coordinator state.
      -- lvPhase2.update r s msgs = match msgs c with | some (.propose v) => {lastVote := (v,round),...} | _ => s
      -- For accepted in s', must be in .propose branch (since h_no_acc gives acc=false in else branch)
      -- The coordinator's message to both p and q is lvPhase2.send c (s.locals c), same for both.
      rw [hlocals' p, hlocals' q]
      simp only [lvPhase2, phase_delivered, h_rsync p, h_rsync q]
      -- Now both sides match on the coordinator's message, potentially different HO.
      -- But if both sides result in accepted=true, both took the .propose branch.
      -- Use hacc_p/hacc_q to know which branch was taken.
      rw [hlocals' p] at hacc_p ; rw [hlocals' q] at hacc_q
      simp only [lvPhase2, phase_delivered, h_rsync p, h_rsync q] at hacc_p hacc_q
      -- Now case-split on the coordinator's proposal
      cases h_prop : (s.locals (coordinator s.round)).core.proposal with
      | none =>
        -- Coordinator has no proposal, sends .skip. No one gets accepted.
        exfalso
        simp only [h_rsync (coordinator s.round), h_prop] at hacc_p
        -- After simp, the coordinator sends .skip.
        -- If ho p c: match (some .skip) → not .propose → state unchanged → accepted = false
        -- If not ho: match none → state unchanged → accepted = false
        by_cases hho : ho p (coordinator s.round) = true
        · simp [hho, h_no_acc p] at hacc_p
        · have hf : ho p (coordinator s.round) = false := by
            revert hho ; cases ho p (coordinator s.round) <;> simp
          simp [hf, h_no_acc p] at hacc_p
      | some v₀ =>
        -- Coordinator sends .propose v₀
        -- Both p and q (if accepted) received .propose v₀ and set lastVote = (v₀, round)
        -- Their lastVote is the same.
        simp only [h_rsync (coordinator s.round)]
        -- After simp, both sides should be:
        -- match (if ho r c then some (.propose v₀) else none) with | some (.propose v) => ... | _ => ...
        -- For the goal (lastVote equality), both sides have the same structure
        -- but with different ho. However, the .propose value v₀ is the same.
        -- Split on ho p c and ho q c
        by_cases hp_ho : ho p (coordinator s.round) = true <;>
          by_cases hq_ho : ho q (coordinator s.round) = true
        · -- Both heard: lastVote = (v₀, round) for both. Equal.
          simp [hp_ho, hq_ho]
        · -- p heard, q didn't: q's accepted = false. Contradiction.
          simp [hq_ho, h_no_acc q] at hacc_q
        · -- p didn't hear: p's accepted = false. Contradiction.
          simp [hp_ho, h_no_acc p] at hacc_p
        · -- Neither heard: both accepted = false. Contradiction.
          simp [hp_ho, h_no_acc p] at hacc_p
    · -- (G) Cross-ballot: decided unchanged. lastVote updated for accepted processes.
      -- New lastVotes have value v₀ = v (by G3) with ballot = s.round.
      -- Old lastVotes preserved. (G1, G2, G3) maintained.
      intro p v hv
      have h_dec : ∀ r, (s'.locals r).core.decided = (s.locals r).core.decided := by
        intro r ; rw [hlocals' r] ; simp only [lvPhase2, phase_delivered] ; split <;> simp
      rw [h_dec p] at hv
      obtain ⟨hG1, hG2, hG3⟩ := h_cross p v hv
      -- By (G3): coordinator's proposal = v
      refine ⟨?_, ?_, ?_⟩
      · -- (G1) Non-v votes dominated by v-votes.
        -- Key: non-v votes are old (pre-state), v-votes may be old or new.
        -- Old non-v ballot b₁ ≤ s.round (by H). New v-ballot = s.round.
        -- Old non-v ballot b₁ < old v-ballot (by G1 on pre-state).
        -- We need b₁ < b₂ for any v-vote b₂ in s'.
        intro q₁ w b₁ hlv₁ hw q₂ b₂ hlv₂
        -- q₁ has non-v lastVote. If q₁ newly accepted, it got value v (by G3). Contradiction.
        -- So q₁'s lastVote is old (from pre-state).
        -- q₂ has v-lastVote. Could be old or new.
        -- Case: coordinator's proposal
        cases h_prop : (s.locals (coordinator s.round)).core.proposal with
        | none =>
          -- No proposal → all lastVotes unchanged
          have h_lv_pres : ∀ r, (s'.locals r).core.lastVote = (s.locals r).core.lastVote := by
            intro r ; rw [hlocals' r]
            simp only [lvPhase2, phase_delivered, h_rsync r]
            by_cases hho : ho r (coordinator s.round) = true
            · simp [hho, h_rsync (coordinator s.round), h_prop]
            · have hf : ho r (coordinator s.round) = false := by
                revert hho ; cases ho r (coordinator s.round) <;> simp
              simp [hf]
          rw [h_lv_pres q₁] at hlv₁ ; rw [h_lv_pres q₂] at hlv₂
          exact hG1 q₁ w b₁ hlv₁ hw q₂ b₂ hlv₂
        | some v₀ =>
          have hv₀_eq := hG3 (by omega) v₀ h_prop
          -- q₁'s lastVote is old (receiving .propose v₀ = .propose v would give value v)
          have h_q₁_old : (s'.locals q₁).core.lastVote = (s.locals q₁).core.lastVote := by
            rw [hlocals' q₁]
            simp only [lvPhase2, phase_delivered, h_rsync q₁]
            by_cases hho : ho q₁ (coordinator s.round) = true
            · exfalso ; rw [hlocals' q₁] at hlv₁
              simp [lvPhase2, phase_delivered, h_rsync q₁, hho,
                    h_rsync (coordinator s.round), h_prop] at hlv₁
              exact hw (by rw [← hv₀_eq] ; exact hlv₁.1.symm)
            · have hf : ho q₁ (coordinator s.round) = false := by
                revert hho ; cases ho q₁ (coordinator s.round) <;> simp
              simp [hf]
          rw [h_q₁_old] at hlv₁
          -- q₂: check if old or new
          rw [hlocals' q₂] at hlv₂
          simp only [lvPhase2, phase_delivered, h_rsync q₂] at hlv₂
          by_cases hho₂ : ho q₂ (coordinator s.round) = true
          · -- q₂ got new v-vote at ballot s.round
            simp [hho₂, h_rsync (coordinator s.round), h_prop] at hlv₂
            -- hlv₂ gives b₂ = s.round (via roundNum = s.round)
            -- b₁ ≤ s.round (by H), and b₁ < s.round since b₁ < any old v-vote's ballot
            -- and old v-votes exist (by G2, ≥ 2 v-voters) with ballot ≤ s.round (by H)
            -- Actually simpler: by H, b₁ ≤ s.round. And b₁ ≠ s.round:
            -- if b₁ = s.round, then by H, b₁ ≤ s.round ✓ but we need strict.
            -- Any old v-voter q₃ has ballot b₃ ≤ s.round. By G1: b₁ < b₃.
            -- So b₁ < b₃ ≤ s.round.  (b₃ ≤ s.round by H.)
            -- Therefore b₁ < s.round = b₂ (from hlv₂).
            -- hlv₂ after simp should give us that b₂ relates to s.round.
            -- b₁ < s.round follows from: by G2, ∃ old v-voter q₃ with ballot b₃.
            -- By G1: b₁ < b₃. By H: b₃ ≤ s.round. So b₁ < s.round.
            -- Extract a v-voter from G2 (≥ 2 v-voters exist in pre-state)
            have h_exists_v : ∃ q₃ b₃, (s.locals q₃).core.lastVote = some (v, b₃) := by
              -- From G2: the filter is nonempty (length ≥ 2).
              have h_ne : ((List.finRange 3).filter fun q =>
                match (s.locals q).core.lastVote with
                | some (w, _) => decide (w = v) | none => false) ≠ [] := by
                intro h_empty ; simp [h_empty] at hG2
              obtain ⟨q₃, hq₃_mem⟩ := List.exists_mem_of_ne_nil _ h_ne
              simp only [List.mem_filter, List.mem_finRange, true_and] at hq₃_mem
              cases hlv_q₃ : (s.locals q₃).core.lastVote with
              | none => simp [hlv_q₃] at hq₃_mem
              | some vb =>
                obtain ⟨val, bal⟩ := vb
                simp [hlv_q₃, decide_eq_true_eq] at hq₃_mem
                exact ⟨q₃, bal, by subst hq₃_mem ; exact hlv_q₃⟩
            obtain ⟨q₃, b₃, hq₃⟩ := h_exists_v
            have hb₁_lt_b₃ := hG1 q₁ w b₁ hlv₁ hw q₃ b₃ hq₃
            have hb₃_le := (h_ballot_bound q₃ v b₃ hq₃).1
            omega
          · -- q₂ has old v-vote
            have hf₂ : ho q₂ (coordinator s.round) = false := by
              revert hho₂ ; cases ho q₂ (coordinator s.round) <;> simp
            simp [hf₂] at hlv₂
            exact hG1 q₁ w b₁ hlv₁ hw q₂ b₂ hlv₂
      · -- (G2) ≥ 2 v-voters in s'. v-voters can only gain members (new accepts are v).
        -- Old v-voters are still v-voters in s'.
        -- Count can only increase.
        have h_mono : ((List.finRange 3).filter fun q =>
            match (s.locals q).core.lastVote with
            | some (w, _) => decide (w = v) | none => false).length ≤
          ((List.finRange 3).filter fun q =>
            match (s'.locals q).core.lastVote with
            | some (w, _) => decide (w = v) | none => false).length := by
          apply filter_length_mono
          intro q hq
          cases h_prop : (s.locals (coordinator s.round)).core.proposal with
          | none =>
            have : (s'.locals q).core.lastVote = (s.locals q).core.lastVote := by
              rw [hlocals' q] ; simp only [lvPhase2, phase_delivered, h_rsync q]
              by_cases hho : ho q (coordinator s.round) = true
              · simp [hho, h_rsync (coordinator s.round), h_prop]
              · have hf : ho q (coordinator s.round) = false := by
                  revert hho ; cases ho q (coordinator s.round) <;> simp
                simp [hf]
            rw [this] ; exact hq
          | some v₀ =>
            have hv₀ := hG3 (by omega) v₀ h_prop
            rw [hlocals' q] ; simp only [lvPhase2, phase_delivered, h_rsync q]
            by_cases hho : ho q (coordinator s.round) = true
            · -- q got new vote (v₀, round). v₀ = v. So v-voter in s'.
              simp [hho, h_rsync (coordinator s.round), h_prop, hv₀]
            · -- q kept old vote. v-voter status preserved.
              have hf : ho q (coordinator s.round) = false := by
                revert hho ; cases ho q (coordinator s.round) <;> simp
              simp [hf] ; exact hq
        exact Nat.le_trans hG2 h_mono
      · -- (G3) s'.phase = 3, val ≥ 2. Proposal unchanged (phase 2 doesn't change proposal).
        intro hph_ge2 w h_prop
        -- Proposal is preserved in s' from s (lvPhase2 doesn't change proposal)
        -- Actually, lvPhase2.update doesn't change proposal.
        -- The coordinator's proposal in s' = coordinator's proposal in s
        -- (coordinator s'.round = coordinator s.round since s'.round = s.round)
        -- The goal asks about coordinator s'.round. Since s'.round = s.round:
        have h_prop_pres : (s'.locals (coordinator s'.round)).core.proposal =
            (s.locals (coordinator s.round)).core.proposal := by
          rw [hs'_round, hlocals' (coordinator s.round)]
          simp only [lvPhase2, phase_delivered] ; split <;> simp
        rw [h_prop_pres] at h_prop
        exact hG3 (by omega) w h_prop
    · -- (H) Ballot bound: new lastVotes have ballot = s.round ≤ s'.round.
      -- Old lastVotes: b ≤ s.round = s'.round by h_ballot_bound.
      intro q w b hlv
      rw [hlocals' q] at hlv
      simp only [lvPhase2, phase_delivered] at hlv
      split at hlv
      · -- Received .propose: lastVote = (v', roundNum). ballot = roundNum = s.round.
        case _ _ heq =>
          simp at hlv
          refine ⟨by rw [← hlv.2, h_rsync q, hs'_round] ; exact Nat.le_refl _, ?_⟩
          intro hb_eq
          refine ⟨hs'_phase, ?_⟩
          rw [hlocals' q]
          simp only [lvPhase2, phase_delivered]
          rw [heq]
      · -- No proposal: lastVote unchanged. Use h_ballot_bound.
        have hb := h_ballot_bound q w b hlv
        refine ⟨by rw [hs'_round] ; exact hb.1, ?_⟩
        intro hb_eq
        exfalso
        have hcur := hb.2 (by rwa [hs'_round] at hb_eq)
        rw [hcur.1] at hph2
        simp at hph2
  · ---- Phase 3 → Phase 0 (Decide → Prepare of next round) ----
    -- Majority decision happens here. Hardest case for agreement.
    have hph_eq : s.phase = ⟨3, by omega⟩ := Fin.ext hph3
    have h_phase : lvAlg.phases s.phase = lvPhase3 := by
      show (if s.phase.val = 0 then lvPhase0
            else if s.phase.val = 1 then lvPhase1
            else if s.phase.val = 2 then lvPhase2
            else lvPhase3) = lvPhase3
      simp [show s.phase.val ≠ 0 by omega,
            show s.phase.val ≠ 1 by omega, show s.phase.val ≠ 2 by omega]
    have hs'_round : s'.round = s.round + 1 := by
      simp [hph3] at hadvance ; exact hadvance.1
    have hlocals' : ∀ p, s'.locals p = lvPhase3.update p (s.locals p)
        (phase_delivered lvPhase3 s.locals ho p) := by
      intro p ; have := hlocals p ; rwa [h_phase] at this
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- (A) Agreement: new decisions must agree with old
      intro p q v w hv hw
      -- Helper: extract decided from post-state.
      -- lvPhase3.update either sets decided := some v (majority + head?) or keeps old.
      -- A process's decided in s' is either:
      --   (i) a new value from head? of accepted messages (if hasMaj3 in HO set)
      --   (ii) the old value from s (unchanged)
      -- Helper: characterize each process's decided in s'.
      -- Either old (from s) or new (from head? of accepted messages).
      -- For new decisions, also extract that hasMaj3 held on received.
      have h_dec_or : ∀ r val, (s'.locals r).core.decided = some val →
          (s.locals r).core.decided = some val ∨
          (∃ msgs_accepted,
            msgs_accepted = (List.finRange 3).filterMap (fun q' =>
              match (phase_delivered lvPhase3 s.locals ho r q') with
              | some (.accepted v') => some v'
              | _ => none) ∧
            msgs_accepted.head? = some val ∧
            -- hasMaj3 held on the received messages
            hasMaj3 (fun q' => match (phase_delivered lvPhase3 s.locals ho r q') with
              | some (.accepted _) => true | _ => false) = true) := by
        intro r val hr
        rw [hlocals' r] at hr
        simp only [lvPhase3, phase_delivered] at hr
        split at hr
        · -- hasMaj3 branch
          case _ hmaj =>
          split at hr
          · -- decidedVal = some val: new decision
            case _ v' hhead =>
            right ; simp at hr ; exact ⟨_, rfl, by rw [← hr] ; exact hhead, hmaj⟩
          · -- decidedVal = none: old decision preserved
            left ; simp at hr ; exact hr
        · -- no majority: old decision preserved
          left ; simp at hr ; exact hr
      -- Now case-split on whether p's and q's decisions are old or new
      rcases h_dec_or p v hv with hp_old | ⟨mp, hmp_eq, hp_new, hp_maj⟩
      · -- p's decision is old (from pre-state)
        rcases h_dec_or q w hw with hq_old | ⟨mq, hmq_eq, hq_new, hq_maj⟩
        · -- Both old: use pre-state agreement
          exact h_agree p q v w hp_old hq_old
        · -- p old, q new: h_dec_prop gives all acceptors have value v
          -- q's new decision from head? of accepted values in q's HO set.
          -- Step 1: q's majority implies global majority accepted
          -- q decided via head? of mq. mq is the filterMap of accepted values
          -- from q's HO set. For mq to be nonempty, ≥ 1 sender sent .accepted.
          -- Actually, the full structure: q decided because hasMaj3 on received,
          -- meaning ≥ 2 in q's HO have accepted = true. These are globally accepted.
          -- So hasMaj3 of global accepted holds.
          -- h_dec_prop + global majority → all acceptors have value v
          -- → q's received accepted values are all v → head? = v = w
          -- Step 1: HO-filtered majority → global majority
          -- h_impl: HO-filtered accepted implies globally accepted
          have h_impl : ∀ r : Fin 3,
              (match phase_delivered lvPhase3 s.locals ho q r with
                | some (.accepted _) => true | _ => false) = true →
              (s.locals r).core.accepted = true := by
            intro r hr_filt
            simp only [phase_delivered, lvPhase3] at hr_filt
            by_cases hho : ho q r = true
            · simp only [hho, ite_true] at hr_filt
              by_cases hacc : (s.locals r).core.accepted = true
              · exact hacc
              · have hf : (s.locals r).core.accepted = false := by
                  revert hacc ; cases (s.locals r).core.accepted <;> simp
                simp [hf] at hr_filt
            · have hf : ho q r = false := by revert hho ; cases ho q r <;> simp
              simp [hf] at hr_filt
          have h_mono := filter_length_mono (List.finRange 3) _ _ h_impl
          have h_global_maj : hasMaj3 (fun r => (s.locals r).core.accepted) = true := by
            unfold hasMaj3 at hq_maj ⊢
            simp only [decide_eq_true_eq] at hq_maj ⊢
            exact Nat.le_trans hq_maj h_mono
          -- Step 2: all globally accepted have value v
          have h_all_v := h_dec_prop p v hp_old hph_eq h_global_maj
          -- Step 3: every value in mq is v (each came from an accepted sender)
          have h_mq_all_v : ∀ x ∈ mq, x = v := by
            intro x hx ; rw [hmq_eq] at hx
            simp only [List.mem_filterMap, List.mem_finRange, true_and] at hx
            obtain ⟨r, hr⟩ := hx
            simp only [phase_delivered, lvPhase3] at hr
            by_cases hho : ho q r = true
            · simp only [hho, ite_true] at hr
              by_cases hacc_r : (s.locals r).core.accepted = true
              · obtain ⟨w', hw', hv'⟩ := h_all_v r hacc_r
                simp only [hacc_r, ite_true] at hr
                revert hr ; rw [hw'] ; simp ; intro hr ; rw [← hr] ; exact hv'
              · have hf : (s.locals r).core.accepted = false := by
                  revert hacc_r ; cases (s.locals r).core.accepted <;> simp
                simp [hf] at hr
            · have hf : ho q r = false := by revert hho ; cases ho q r <;> simp
              simp [hf] at hr
          -- Step 4: head? mq = some w, so w = v
          have hw_in : w ∈ mq := by
            cases mq with
            | nil => simp at hq_new
            | cons a as =>
              simp [List.head?] at hq_new
              subst hq_new ; exact List.Mem.head _
          exact (h_mq_all_v w hw_in).symm
      · -- p's decision is new
        rcases h_dec_or q w hw with hq_old | ⟨mq, hmq_eq, hq_new, hq_maj⟩
        · -- p new, q old: symmetric to old-new
          -- h_impl: HO-filtered accepted implies globally accepted
          have h_impl : ∀ r : Fin 3,
              (match phase_delivered lvPhase3 s.locals ho p r with
                | some (.accepted _) => true | _ => false) = true →
              (s.locals r).core.accepted = true := by
            intro r hr_filt
            simp only [phase_delivered, lvPhase3] at hr_filt
            by_cases hho : ho p r = true
            · simp only [hho, ite_true] at hr_filt
              by_cases hacc : (s.locals r).core.accepted = true
              · exact hacc
              · have hf : (s.locals r).core.accepted = false := by
                  revert hacc ; cases (s.locals r).core.accepted <;> simp
                simp [hf] at hr_filt
            · have hf : ho p r = false := by revert hho ; cases ho p r <;> simp
              simp [hf] at hr_filt
          have h_mono := filter_length_mono (List.finRange 3) _ _ h_impl
          have h_global_maj : hasMaj3 (fun r => (s.locals r).core.accepted) = true := by
            unfold hasMaj3 at hp_maj ⊢
            simp only [decide_eq_true_eq] at hp_maj ⊢
            exact Nat.le_trans hp_maj h_mono
          have h_all_w := h_dec_prop q w hq_old hph_eq h_global_maj
          -- All values in mp are w (each came from an accepted sender)
          have h_mp_all_w : ∀ x ∈ mp, x = w := by
            intro x hx ; rw [hmp_eq] at hx
            simp only [List.mem_filterMap, List.mem_finRange, true_and] at hx
            obtain ⟨r, hr⟩ := hx
            simp only [phase_delivered, lvPhase3] at hr
            by_cases hho : ho p r = true
            · simp only [hho, ite_true] at hr
              by_cases hacc_r : (s.locals r).core.accepted = true
              · obtain ⟨w', hw', hv'⟩ := h_all_w r hacc_r
                simp only [hacc_r, ite_true] at hr
                revert hr ; rw [hw'] ; simp ; intro hr ; rw [← hr] ; exact hv'
              · have hf : (s.locals r).core.accepted = false := by
                  revert hacc_r ; cases (s.locals r).core.accepted <;> simp
                simp [hf] at hr
            · have hf : ho p r = false := by revert hho ; cases ho p r <;> simp
              simp [hf] at hr
          -- v is in mp (it's head?)
          have hv_in : v ∈ mp := by
            cases mp with
            | nil => simp at hp_new
            | cons a as =>
              simp [List.head?] at hp_new
              subst hp_new ; exact List.Mem.head _
          exact h_mp_all_w v hv_in
        · -- Both new: use (F) — all accepted have same value
          -- Both mp and mq contain values from accepted processes.
          -- By (F), any two accepted processes have the same lastVote value.
          -- So all elements of mp and mq are the same value.
          -- Therefore head? mp = head? mq, giving v = w.
          -- Step 1: extract an accepted process from mp
          have hv_in : v ∈ mp := by
            cases mp with
            | nil => simp at hp_new
            | cons a as =>
              simp [List.head?] at hp_new ; subst hp_new ; exact List.Mem.head _
          have hw_in : w ∈ mq := by
            cases mq with
            | nil => simp at hq_new
            | cons a as =>
              simp [List.head?] at hq_new ; subst hq_new ; exact List.Mem.head _
          -- Step 2: v came from an accepted process r₁, w from r₂
          rw [hmp_eq] at hv_in
          simp only [List.mem_filterMap, List.mem_finRange, true_and] at hv_in
          obtain ⟨r₁, hr₁⟩ := hv_in
          rw [hmq_eq] at hw_in
          simp only [List.mem_filterMap, List.mem_finRange, true_and] at hw_in
          obtain ⟨r₂, hr₂⟩ := hw_in
          -- Step 3: extract that r₁ and r₂ are accepted with specific lastVote values
          -- r₁ sent .accepted v, meaning r₁ has accepted = true and lastVote = some (v, _)
          simp only [phase_delivered, lvPhase3] at hr₁ hr₂
          -- For r₁:
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
          -- Step 4: by (C), r₁ and r₂ have lastVote = some (v₁, round) and some (v₂, round)
          obtain ⟨v₁, hv₁⟩ := h_ph3 hph_eq r₁ h_r₁_acc
          obtain ⟨v₂, hv₂⟩ := h_ph3 hph_eq r₂ h_r₂_acc
          -- Step 5: by (F), v₁ = v₂
          have hv_eq := h_uniform hph_eq r₁ r₂ v₁ v₂ h_r₁_acc h_r₂_acc hv₁ hv₂
          -- Step 6: trace v back to v₁ and w back to v₂
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
    · -- (B) Accepted: lvPhase3.update always sets accepted := false
      intro p hacc
      have h_false : (s'.locals p).core.accepted = false := by
        rw [hlocals' p]
        simp [lvPhase3, hasMaj3, phase_delivered]
        split <;> (try split) <;> simp
      simp [h_false] at hacc
    · -- (C) s'.phase = 0 ≠ 3 (after phase 3 wraps to 0), vacuous
      intro hph3'
      have : s'.phase = ⟨0, by omega⟩ := by simp [hph3] at hadvance ; exact hadvance.2
      rw [this] at hph3' ; simp at hph3'
    · -- (D) s'.phase = 0 ≠ 3, vacuous
      intro p v _ hph3'
      have : s'.phase = ⟨0, by omega⟩ := by simp [hph3] at hadvance ; exact hadvance.2
      rw [this] at hph3' ; simp at hph3'
    · -- (E) Round sync: roundNum incremented by lvPhase3.update
      intro p ; rw [hlocals' p, hs'_round]
      simp only [lvPhase3, phase_delivered, h_rsync p]
    · -- (F') Phase 3 resets accepted to false; s'.phase = 0 ≠ 3
      intro p hacc
      have h_false : (s'.locals p).core.accepted = false := by
        rw [hlocals' p]
        simp [lvPhase3, hasMaj3, phase_delivered]
        split <;> (try split) <;> simp
      simp [h_false] at hacc
    · -- (F) s'.phase = 0 ≠ 3, vacuous
      intro hph3'
      have : s'.phase = ⟨0, by omega⟩ := by simp [hph3] at hadvance ; exact hadvance.2
      rw [this] at hph3' ; simp at hph3'
    · -- (G) Cross-ballot: lastVote unchanged. decided MAY change (new decisions).
      intro p v hv
      -- decided in s' is either old (from s) or new (from phase 3 majority).
      -- lastVote is preserved by lvPhase3 (only decided/prepared/accepted change)
      have h_lv : ∀ r, (s'.locals r).core.lastVote = (s.locals r).core.lastVote := by
        intro r ; rw [hlocals' r]
        simp only [lvPhase3, phase_delivered]
        split <;> (try split) <;> simp
      -- Check if this is an old or new decision
      rw [hlocals' p] at hv
      simp only [lvPhase3, phase_delivered] at hv
      -- Phase 3 update: decided is either set to new value or preserved from s
      -- If decided was already in s: use h_cross from pre-state
      -- If decided is new: establish (G) from the phase 3 state
      -- For new decisions, ≥ 2 accepted v (by hasMaj3 + F), all with ballot = s.round
      -- Any non-v vote has ballot < s.round (from earlier rounds)
      -- So (G1): non-v ballot < v ballot. (G2): ≥ 2 v-voters.
      -- (G3): s'.phase = 0, val < 2. Vacuous.
      -- For old decisions: (G) from pre-state + lastVote unchanged.
      -- Case split on decided: old (from s) or new (from this phase 3 step)
      split at hv
      · -- hasMaj3 branch
        case _ hmaj =>
        split at hv
        · -- New decision: v = head? of accepted values
          case _ v' hhead =>
          simp at hv ; subst hv
          let acceptedVals : List Value := (List.finRange 3).filterMap (fun q' =>
            match phase_delivered lvPhase3 s.locals ho p q' with
            | some (.accepted x) => some x
            | _ => none)
          have hhead' : acceptedVals.head? = some v' := by
            simpa [acceptedVals] using hhead
          have hv'_mem : v' ∈ acceptedVals := by
            cases hvals : acceptedVals with
            | nil =>
              simp [hvals] at hhead'
            | cons x xs =>
              have hx : x = v' := by simpa [hvals] using hhead'
              subst hx
              simp
          have h_msg_v' : ∃ r₀ : Proc,
              phase_delivered lvPhase3 s.locals ho p r₀ = some (.accepted v') := by
            rcases (by
              simpa [acceptedVals] using hv'_mem :
                ∃ a, (match phase_delivered lvPhase3 s.locals ho p a with
                  | some (.accepted x) => some x
                  | _ => none) = some v') with ⟨r₀, hr₀⟩
            cases hdel : phase_delivered lvPhase3 s.locals ho p r₀ with
            | none =>
              rw [hdel] at hr₀
              simp at hr₀
            | some m =>
              rw [hdel] at hr₀
              cases m <;> simp at hr₀
              case accepted x =>
                cases hr₀
                exact ⟨r₀, by simp [hdel]⟩
          obtain ⟨r₀, hr₀⟩ := h_msg_v'
          have h_impl : ∀ r : Proc,
              (match phase_delivered lvPhase3 s.locals ho p r with
                | some (.accepted _) => true | _ => false) = true →
              (s.locals r).core.accepted = true := by
            intro r hr_filt
            simp only [phase_delivered, lvPhase3] at hr_filt
            by_cases hho : ho p r = true
            · simp only [hho, ite_true] at hr_filt
              by_cases hacc : (s.locals r).core.accepted = true
              · exact hacc
              · have hf : (s.locals r).core.accepted = false := by
                  revert hacc ; cases (s.locals r).core.accepted <;> simp
                simp [hf] at hr_filt
            · have hf : ho p r = false := by revert hho ; cases ho p r <;> simp
              simp [hf] at hr_filt
          have h_mono := filter_length_mono (List.finRange 3)
            (fun r => match phase_delivered lvPhase3 s.locals ho p r with
              | some (.accepted _) => true | _ => false)
            (fun r => (s.locals r).core.accepted) h_impl
          have h_global_maj : hasMaj3 (fun r => (s.locals r).core.accepted) = true := by
            unfold hasMaj3 at hmaj ⊢
            simp only [decide_eq_true_eq] at hmaj ⊢
            exact Nat.le_trans hmaj h_mono
          have h_r₀_acc : (s.locals r₀).core.accepted = true := by
            exact h_impl r₀ (by simp [hr₀])
          obtain ⟨u₀, hu₀⟩ := h_ph3 hph_eq r₀ h_r₀_acc
          have hu₀_eq_v' : u₀ = v' := by
            have hmsg := hr₀
            simp only [phase_delivered, lvPhase3] at hmsg
            by_cases hho : ho p r₀ = true
            · simp [hho, h_r₀_acc, hu₀] at hmsg
              exact hmsg
            · have hf : ho p r₀ = false := by revert hho ; cases ho p r₀ <;> simp
              simp [hf] at hmsg
          have h_acc_val : ∀ r : Proc, (s.locals r).core.accepted = true →
              (s.locals r).core.lastVote = some (v', s.round) := by
            intro r hr
            obtain ⟨u, hu⟩ := h_ph3 hph_eq r hr
            have hu_eq : u = u₀ := h_uniform hph_eq r r₀ u u₀ hr h_r₀_acc hu hu₀
            rw [hu_eq, hu₀_eq_v'] at hu
            exact hu
          refine ⟨?_, ?_, ?_⟩
          · intro q₁ w b₁ hlv₁ hw q₂ b₂ hlv₂
            have hlv₁s : (s.locals q₁).core.lastVote = some (w, b₁) := by
              rwa [h_lv q₁] at hlv₁
            have hlv₂s : (s.locals q₂).core.lastVote = some (v', b₂) := by
              rwa [h_lv q₂] at hlv₂
            have h_q₁_not_acc : (s.locals q₁).core.accepted = false := by
              by_cases hacc₁ : (s.locals q₁).core.accepted = true
              · have hq₁v := h_acc_val q₁ hacc₁
                rw [hq₁v] at hlv₁s
                simp only [Option.some.injEq, Prod.mk.injEq] at hlv₁s
                exact (hw hlv₁s.1.symm).elim
              · revert hacc₁ ; cases (s.locals q₁).core.accepted <;> simp
            have hq₁₂_ne : q₁ ≠ q₂ := by
              intro h_eq
              subst h_eq
              rw [hlv₂s] at hlv₁s
              simp only [Option.some.injEq, Prod.mk.injEq] at hlv₁s
              exact hw hlv₁s.1.symm
            have h_q₂_acc : (s.locals q₂).core.accepted = true := by
              by_cases hacc₂ : (s.locals q₂).core.accepted = true
              · exact hacc₂
              · have hacc₂f : (s.locals q₂).core.accepted = false := by
                  revert hacc₂ ; cases (s.locals q₂).core.accepted <;> simp
                have h_bound := filter_len_le_one_of_two_distinct_false
                  (fun r => (s.locals r).core.accepted) q₁ q₂ h_q₁_not_acc hacc₂f hq₁₂_ne
                have h_bound' :
                    ((List.finRange 3).filter fun r => (s.locals r).core.accepted).length ≤ 1 := by
                  simpa using h_bound
                unfold hasMaj3 at h_global_maj
                simp only [decide_eq_true_eq] at h_global_maj
                have h_not_maj :
                    ¬ 2 ≤ ((List.finRange 3).filter fun r => (s.locals r).core.accepted).length := by
                  omega
                exact (h_not_maj h_global_maj).elim
            have hq₂v := h_acc_val q₂ h_q₂_acc
            rw [hq₂v] at hlv₂s
            simp only [Option.some.injEq, Prod.mk.injEq] at hlv₂s
            have hb₁ := h_ballot_bound q₁ w b₁ hlv₁s
            have hb₁_lt : b₁ < s.round := by
              have hb₁_ne : b₁ ≠ s.round := by
                intro hb_eq
                have hcur := hb₁.2 hb_eq
                have hacc_cur := hcur.2
                rw [h_q₁_not_acc] at hacc_cur
                simp at hacc_cur
              omega
            omega
          · have h_mono_v : ((List.finRange 3).filter fun q => (s.locals q).core.accepted).length ≤
                ((List.finRange 3).filter fun q =>
                  match (s'.locals q).core.lastVote with
                  | some (w, _) => decide (w = v')
                  | none => false).length := by
              apply filter_length_mono
              intro q hq
              have hqv := h_acc_val q hq
              have hqv' : (s'.locals q).core.lastVote = some (v', s.round) := by
                rw [h_lv q, hqv]
              rw [hqv']
              simp
            unfold hasMaj3 at h_global_maj
            simp only [decide_eq_true_eq] at h_global_maj
            exact Nat.le_trans h_global_maj h_mono_v
          · intro hph_ge2
            have hs'_phase : s'.phase = ⟨0, by omega⟩ := by
              simp [hph3] at hadvance
              exact hadvance.2
            simp [hs'_phase] at hph_ge2
        · -- decidedVal = none: old decision preserved
          simp at hv
          obtain ⟨hG1, hG2, hG3⟩ := h_cross p v hv
          exact ⟨fun q₁ w b₁ hlv₁ hw q₂ b₂ hlv₂ => hG1 q₁ w b₁ (by rwa [h_lv q₁] at hlv₁) hw q₂ b₂ (by rwa [h_lv q₂] at hlv₂),
                 by have : (List.finRange 3).filter (fun q => match (s'.locals q).core.lastVote with | some (w, _) => decide (w = v) | none => false) =
                      (List.finRange 3).filter (fun q => match (s.locals q).core.lastVote with | some (w, _) => decide (w = v) | none => false) := by
                      congr 1 ; funext q ; simp [h_lv q]
                    rw [this] ; exact hG2,
                 fun hph_ge2 => by simp [show s'.phase = ⟨0, by omega⟩ from by simp [hph3] at hadvance ; exact hadvance.2] at hph_ge2⟩
      · -- no majority: old decision preserved
        simp at hv
        obtain ⟨hG1, hG2, hG3⟩ := h_cross p v hv
        exact ⟨fun q₁ w b₁ hlv₁ hw q₂ b₂ hlv₂ => hG1 q₁ w b₁ (by rwa [h_lv q₁] at hlv₁) hw q₂ b₂ (by rwa [h_lv q₂] at hlv₂),
               by have : (List.finRange 3).filter (fun q => match (s'.locals q).core.lastVote with | some (w, _) => decide (w = v) | none => false) =
                    (List.finRange 3).filter (fun q => match (s.locals q).core.lastVote with | some (w, _) => decide (w = v) | none => false) := by
                    congr 1 ; funext q ; simp [h_lv q]
                  rw [this] ; exact hG2,
               fun hph_ge2 => by simp [show s'.phase = ⟨0, by omega⟩ from by simp [hph3] at hadvance ; exact hadvance.2] at hph_ge2⟩
    · -- (H) Ballot bound: lastVote unchanged, round incremented.
      -- b ≤ s.round < s.round + 1 = s'.round
      intro q w b hlv
      have h_lv : (s'.locals q).core.lastVote = (s.locals q).core.lastVote := by
        rw [hlocals' q] ; simp only [lvPhase3, phase_delivered]
        split <;> (try split) <;> simp
      rw [h_lv] at hlv
      have hb := h_ballot_bound q w b hlv
      refine ⟨by rw [hs'_round] ; omega, ?_⟩
      intro hb_eq
      exfalso
      rw [hs'_round] at hb_eq
      omega

/-! ### Agreement theorem -/

/-- Agreement is an invariant of the phased LastVoting protocol (n = 3). -/
theorem lv_agreement :
    pred_implies lvLeslieSpec.safety [tlafml| □ ⌜agreement⌝] := by
  -- Prove the stronger combined invariant, then project
  suffices h : pred_implies lvLeslieSpec.safety [tlafml| □ ⌜lv_inv⌝] by
    intro e he n
    exact (h e he n).1
  apply phase_round_invariant lvSpec (by omega)
  · exact lv_inv_init
  · exact lv_inv_step

/-! ### Quorum intersection (reused from the framework)

    The `cross_phase_quorum_intersection` theorem from `PhaseRound.lean`
    provides the key quorum argument: any two majority HO sets among
    `Fin 3` must share a process. This is essential for Paxos safety:
    the promise quorum (Phase 1) and accept quorum (Phase 3) overlap.

    We instantiate it here for `n = 3` for documentation purposes. -/

/-- Two majorities of 3 processes must intersect.
    This is the n = 3 specialization of `cross_phase_quorum_intersection`
    from `PhaseRound.lean`. -/
theorem maj3_intersect (p₁ p₂ : Proc → Bool)
    (h₁ : ((List.finRange 3).filter fun r => p₁ r).length ≥ 2)
    (h₂ : ((List.finRange 3).filter fun r => p₂ r).length ≥ 2) :
    ∃ r : Proc, p₁ r = true ∧ p₂ r = true := by
  by_contra h
  have h' : ∀ r, ¬(p₁ r = true ∧ p₂ r = true) := fun r hr => h ⟨r, hr⟩
  have h_sum := filter_disjoint_length_le
    (fun r => p₁ r) (fun r => p₂ r) (List.finRange 3) h'
  have h_len : (List.finRange 3).length = 3 := List.length_finRange
  omega

def proposals_respect_votes (s : PhaseRoundState Proc LVState 4) : Prop :=
  ∀ p v, (s.locals p).core.decided = some v →
    s.phase.val ≥ 2 →
    ∀ w, (s.locals (coordinator s.round)).core.proposal = some w → w = v

/-- Proposals respect prior votes (n = 3). -/
theorem proposals_respect_votes_invariant :
    pred_implies lvLeslieSpec.safety
      [tlafml| □ ⌜proposals_respect_votes⌝] := by
  suffices h : pred_implies lvLeslieSpec.safety [tlafml| □ ⌜lv_inv⌝] by
    intro e he n p v hdec hphase w hprop
    rcases h e he n with ⟨_, _, _, _, _, _, _, hG, _⟩
    exact hG p v hdec |>.2.2 hphase w hprop
  apply phase_round_invariant lvSpec (by omega)
  · exact lv_inv_init
  · exact lv_inv_step


end LastVotingPhased
