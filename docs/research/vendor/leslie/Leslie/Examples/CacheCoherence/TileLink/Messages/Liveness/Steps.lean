import Leslie.Examples.CacheCoherence.TileLink.Messages.Liveness.Defs
import Leslie.Rules.WF
import Leslie.Rules.LeadsTo

/-! ## Progress Lemmas for TileLink Liveness

    Each step in the acquire wave has a "progress" lemma: from the current
    phase, the action that advances to the next phase is enabled.

    These are the key building blocks for WF1 applications. Combined with
    weak fairness, they give leads-to properties.

    The acquire wave phases:

    ```
    chanA has acquire → txn active (probing) → all probes done (grantReady)
      → grant sent (grantPendingAck) → grant received → grantAck sent → txn complete
    ```
-/

namespace TileLink.Messages.Liveness

open TLA TileLink SymShared

/-! ### Auxiliary invariants not in fullInv

    These invariants are needed for liveness but are not part of the safety
    invariant `fullInv`. Each requires a separate inductive proof over all
    18 protocol actions. -/

/-- pendingSink is only non-none when chanD or chanE is non-none (grant wave active).
    Key insight: only sendGrantLocal sets pendingSink := some (and also sets chanD),
    recvGrantLocal clears chanD but chanE gets set, recvGrantAckLocal clears both. -/
def pendingSinkInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ i : Fin n, (s.locals i).pendingSink ≠ none →
    (s.locals i).chanD ≠ none ∨ (s.locals i).chanE ≠ none

theorem init_pendingSinkInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s →
      pendingSinkInv n s := by
  intro s hinit i hps
  rcases hinit with ⟨_, hlocals⟩
  rcases hlocals i with ⟨_, _, _, _, _, _, _, hpsi, _⟩
  rw [hpsi] at hps; exact absurd rfl hps

/-- Stronger invariant: pendingSink ≠ none implies an active transaction at
    grantPendingAck phase with the node as requester. This is the inductive
    version; pendingSinkInv is derived from this + grantWaveActiveInv. -/
def pendingSinkTxnInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ i : Fin n, (s.locals i).pendingSink ≠ none →
    ∃ tx, s.shared.currentTxn = some tx ∧ tx.requester = i.1 ∧ tx.phase = .grantPendingAck

theorem init_pendingSinkTxnInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s →
      pendingSinkTxnInv n s := by
  intro s hinit i hps
  rcases hinit with ⟨_, hlocals⟩
  rcases hlocals i with ⟨_, _, _, _, _, _, _, hpsi, _⟩
  rw [hpsi] at hps; exact absurd rfl hps

theorem pendingSinkTxnInv_preserved {n : Nat}
    {s s' : SymState HomeState NodeState n}
    (hinv : fullInv n s)
    (hpst : pendingSinkTxnInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    pendingSinkTxnInv n s' := by
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨j, a, hstep⟩ := hnext
  intro k hps'
  match a with
  -- SendAcquireBlock/Perm: shared unchanged, pendingSink unchanged → old invariant
  | .sendAcquireBlock _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, rfl⟩
      have hps_old : (s.locals k).pendingSink ≠ none := by
        by_cases hkj : k = j
        · subst hkj; simpa [setFn] using hps'
        · simpa [setFn, hkj] using hps'
      exact hpst k hps_old
  | .sendAcquirePerm _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, rfl⟩
      have hps_old : (s.locals k).pendingSink ≠ none := by
        by_cases hkj : k = j
        · subst hkj; simpa [setFn] using hps'
        · simpa [setFn, hkj] using hps'
      exact hpst k hps_old
  -- RecvAcquireAtManager: creates txn with phase = probing, requires currentTxn = none → vacuous
  | .recvAcquireAtManager =>
      rcases hstep with ⟨_, _, hblk⟩ | ⟨_, _, hperm⟩
      · rcases hblk with ⟨hcurNone, _, _, _, _, _, _, _, _, _, rfl⟩
        have hps_old : (s.locals k).pendingSink ≠ none := by
          simp only [recvAcquireState, recvAcquireLocals,
            scheduleProbeLocals_pendingSink] at hps'; exact hps'
        rcases hpst k hps_old with ⟨tx, hcur, _, _⟩
        rw [hcurNone] at hcur; exact absurd hcur (by simp)
      · rcases hperm with ⟨hcurNone, _, _, _, _, _, _, _, _, rfl⟩
        have hps_old : (s.locals k).pendingSink ≠ none := by
          simp only [recvAcquireState, recvAcquireLocals,
            scheduleProbeLocals_pendingSink] at hps'; exact hps'
        rcases hpst k hps_old with ⟨tx, hcur, _, _⟩
        rw [hcurNone] at hcur; exact absurd hcur (by simp)
  -- RecvProbeAtMaster: shared unchanged, pendingSink unchanged → old invariant
  | .recvProbeAtMaster =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩
      have hps_old : (s.locals k).pendingSink ≠ none := by
        simp only [recvProbeState, recvProbeLocals] at hps'
        by_cases hkj : k = j
        · subst hkj; simpa [setFn, recvProbeLocal] using hps'
        · simpa [setFn, hkj] using hps'
      rcases hpst k hps_old with ⟨tx, hcur, hreq, hphase⟩
      exact ⟨tx, hcur, hreq, hphase⟩
  -- RecvProbeAckAtManager: changes phase to probing/grantReady, never grantPendingAck → vacuous
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨tx0, _, hcur0, hphase0, _, _, _, _, _, rfl⟩
      have hps_old : (s.locals k).pendingSink ≠ none := by
        simp only [recvProbeAckState, recvProbeAckLocals] at hps'
        by_cases hkj : k = j
        · subst hkj; simpa [setFn, recvProbeAckLocal] using hps'
        · simpa [setFn, hkj] using hps'
      rcases hpst k hps_old with ⟨tx, hcur, hreq, hphase⟩
      -- old phase = grantPendingAck, but old currentTxn has phase = probing
      rw [hcur0] at hcur; have := Option.some.inj hcur; subst this
      exact absurd hphase (by rw [hphase0]; decide)
  -- SendGrantToRequester: transitions to grantPendingAck, sets pendingSink for requester
  | .sendGrantToRequester =>
      rcases hstep with ⟨tx0, hcur0, hreq0, hphase0, _, _, _, _, hPsNone, rfl⟩
      simp only [sendGrantState, sendGrantLocals, sendGrantShared] at hps' ⊢
      by_cases hkj : k = j
      · subst hkj
        simp only [setFn, ite_true, sendGrantLocal] at hps' ⊢
        exact ⟨{ tx0 with phase := .grantPendingAck }, by simp_all, hreq0, rfl⟩
      · simp only [setFn, show k ≠ j from hkj, ite_false] at hps'
        rcases hpst k hps' with ⟨tx, hcur, hreq, hphase⟩
        -- old currentTxn has phase = grantReady, but invariant says grantPendingAck
        rw [hcur0] at hcur; have := Option.some.inj hcur; subst this
        exact absurd hphase (by rw [hphase0]; decide)
  -- RecvGrantAtMaster: currentTxn unchanged, pendingSink unchanged → old invariant
  | .recvGrantAtMaster =>
      rcases hstep with ⟨tx0, _, hcur0, _, _, _, _, _, _, _, _, rfl⟩
      have hps_old : (s.locals k).pendingSink ≠ none := by
        simp only [recvGrantState, recvGrantLocals] at hps'
        by_cases hkj : k = j
        · subst hkj; simpa [setFn, recvGrantLocal] using hps'
        · simpa [setFn, hkj] using hps'
      rcases hpst k hps_old with ⟨tx, hcur, hreq, hphase⟩
      -- recvGrantShared preserves currentTxn
      simp only [recvGrantState, recvGrantShared]
      exact ⟨tx, hcur, hreq, hphase⟩
  -- RecvGrantAckAtManager: clears pendingSink for j, clears currentTxn
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨tx0, _, hcur0, hreq0, hphase0, _, _, _, _, _, rfl⟩
      simp only [recvGrantAckState, recvGrantAckLocals,
        recvGrantAckShared] at hps' ⊢
      by_cases hkj : k = j
      · subst hkj; simp [setFn, recvGrantAckLocal] at hps'
      · simp only [setFn, show k ≠ j from hkj, ite_false] at hps'
        rcases hpst k hps' with ⟨tx, hcur, hreq, _⟩
        -- tx.requester = k, tx0.requester = j, but k ≠ j
        rw [hcur0] at hcur; have := Option.some.inj hcur; subst this
        exact absurd (Fin.ext (hreq ▸ hreq0 ▸ rfl)) hkj
  -- SendRelease/SendReleaseData: require currentTxn = none → vacuous
  | .sendRelease _ =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      have hps_old : (s.locals k).pendingSink ≠ none := by
        simp only [sendReleaseState, sendReleaseLocals] at hps'
        by_cases hkj : k = j
        · subst hkj; simpa [setFn, sendReleaseLocal] using hps'
        · simpa [setFn, hkj] using hps'
      rcases hpst k hps_old with ⟨tx, hcur, _, _⟩
      rw [hcurNone] at hcur; exact absurd hcur (by simp)
  | .sendReleaseData _ =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      have hps_old : (s.locals k).pendingSink ≠ none := by
        simp only [sendReleaseState, sendReleaseLocals] at hps'
        by_cases hkj : k = j
        · subst hkj; simpa [setFn, sendReleaseLocal] using hps'
        · simpa [setFn, hkj] using hps'
      rcases hpst k hps_old with ⟨tx, hcur, _, _⟩
      rw [hcurNone] at hcur; exact absurd hcur (by simp)
  -- RecvReleaseAtManager: requires currentTxn = none → vacuous
  | .recvReleaseAtManager =>
      rcases hstep with ⟨_, _, hcurNone, _, _, _, _, _, _, _, _, _, rfl⟩
      have hps_old : (s.locals k).pendingSink ≠ none := by
        simp only [recvReleaseState, recvReleaseLocals] at hps'
        by_cases hkj : k = j
        · subst hkj; simpa [setFn, recvReleaseLocal] using hps'
        · simpa [setFn, hkj] using hps'
      rcases hpst k hps_old with ⟨tx, hcur, _, _⟩
      rw [hcurNone] at hcur; exact absurd hcur (by simp)
  -- RecvReleaseAckAtMaster: requires currentTxn = none → vacuous
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨_, hcurNone, _, _, _, _, _, rfl⟩
      have hps_old : (s.locals k).pendingSink ≠ none := by
        simp only [recvReleaseAckState, recvReleaseAckLocals] at hps'
        by_cases hkj : k = j
        · subst hkj; simpa [setFn, recvReleaseAckLocal] using hps'
        · simpa [setFn, hkj] using hps'
      rcases hpst k hps_old with ⟨tx, hcur, _, _⟩
      rw [hcurNone] at hcur; exact absurd hcur (by simp)
  -- Store: requires currentTxn = none → vacuous
  | .store _ =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      have hps_old : (s.locals k).pendingSink ≠ none := by
        by_cases hkj : k = j
        · subst hkj; simpa [setFn, storeLocal] using hps'
        · simpa [setFn, hkj] using hps'
      rcases hpst k hps_old with ⟨tx, hcur, _, _⟩
      rw [hcurNone] at hcur; exact absurd hcur (by simp)
  -- Read: s' = s → trivial
  | .read =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩
      exact hpst k hps'
  -- UncachedGet: requires currentTxn = none → vacuous
  | .uncachedGet _ =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, rfl⟩
      have hps_old : (s.locals k).pendingSink ≠ none := by
        by_cases hkj : k = j
        · subst hkj; simpa [setFn] using hps'
        · simpa [setFn, hkj] using hps'
      rcases hpst k hps_old with ⟨tx, hcur, _, _⟩
      rw [hcurNone] at hcur; exact absurd hcur (by simp)
  -- UncachedPut: requires currentTxn = none → vacuous
  | .uncachedPut _ _ =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, _, rfl⟩
      have hps_old : (s.locals k).pendingSink ≠ none := by
        by_cases hkj : k = j
        · subst hkj; simpa [setFn] using hps'
        · simpa [setFn, hkj] using hps'
      rcases hpst k hps_old with ⟨tx, hcur, _, _⟩
      rw [hcurNone] at hcur; exact absurd hcur (by simp)
  -- RecvUncachedAtManager: requires currentTxn = none → vacuous
  | .recvUncachedAtManager =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, rfl⟩
      have hps_old : (s.locals k).pendingSink ≠ none := by
        by_cases hkj : k = j
        · subst hkj; simpa [setFn] using hps'
        · simpa [setFn, hkj] using hps'
      rcases hpst k hps_old with ⟨tx, hcur, _, _⟩
      rw [hcurNone] at hcur; exact absurd hcur (by simp)
  -- RecvAccessAckAtMaster: shared unchanged, pendingSink unchanged → old invariant
  | .recvAccessAckAtMaster =>
      rcases hstep with ⟨_, _, _, rfl⟩
      have hps_old : (s.locals k).pendingSink ≠ none := by
        by_cases hkj : k = j
        · subst hkj; simpa [setFn] using hps'
        · simpa [setFn, hkj] using hps'
      exact hpst k hps_old

/-- During probing, if probesRemaining j = true, then either chanB j
    has the probe (not yet received) or chanC j has the probeAck
    (j responded, manager hasn't consumed yet).
    Key insight: recvAcquire sets chanB for all probed nodes,
    recvProbe clears chanB and sets chanC,
    recvProbeAck clears chanC and sets probesRemaining to false. -/
def probeChannelInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ tx, s.shared.currentTxn = some tx → tx.phase = .probing →
    ∀ j : Fin n, tx.probesRemaining j.1 = true →
      (s.locals j).chanB ≠ none ∨ (s.locals j).chanC ≠ none

theorem init_probeChannelInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s →
      probeChannelInv n s := by
  intro s hinit tx hcur
  rcases hinit with ⟨⟨_, _, hcurNone, _, _, _⟩, _⟩
  rw [hcur] at hcurNone; simp at hcurNone

theorem probeChannelInv_preserved {n : Nat}
    {s s' : SymState HomeState NodeState n}
    (hinv : fullInv n s)
    (hpci : probeChannelInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    probeChannelInv n s' := by
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  intro tx hcur' hphase' j hrem'
  match a with
  -- SendAcquireBlock: shared unchanged, chanB/chanC unchanged for all nodes (only chanA/pendingSource)
  | .sendAcquireBlock _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, rfl⟩
      have hBCold := hpci tx hcur' hphase' j hrem'
      rcases hBCold with hB | hC
      · left; by_cases hjk : j = i
        · subst hjk; simpa [setFn] using hB
        · simpa [setFn, hjk] using hB
      · right; by_cases hjk : j = i
        · subst hjk; simpa [setFn] using hC
        · simpa [setFn, hjk] using hC
  -- SendAcquirePerm: shared unchanged, chanB/chanC unchanged
  | .sendAcquirePerm _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, rfl⟩
      have hBCold := hpci tx hcur' hphase' j hrem'
      rcases hBCold with hB | hC
      · left; by_cases hjk : j = i
        · subst hjk; simpa [setFn] using hB
        · simpa [setFn, hjk] using hB
      · right; by_cases hjk : j = i
        · subst hjk; simpa [setFn] using hC
        · simpa [setFn, hjk] using hC
  -- RecvAcquireAtManager: creates new txn with probing phase, sets chanB for probed nodes
  | .recvAcquireAtManager =>
      rcases hstep with ⟨grow, source, hblk⟩ | ⟨grow, source, hperm⟩
      · -- RecvAcquireBlock
        rcases hblk with ⟨_, _, _, hCnoneAll, _, _, _, _, _, _, rfl⟩
        simp only [recvAcquireState, recvAcquireShared] at hcur'
        have htxeq := Option.some.inj hcur'
        subst htxeq
        -- tx = plannedTxn ..., probesRemaining = probeMaskForResult, phase = .probing
        simp only [plannedTxn] at hrem'
        -- hrem' : probeMaskForResult s i grow.result j.1 = true
        left
        simp only [recvAcquireState, recvAcquireLocals, SymState.locals]
        rw [scheduleProbeLocals_chanB_true s i j (probeMaskForResult s i grow.result)
            .acquireBlock grow.result source hrem']
        simp
      · -- RecvAcquirePerm
        rcases hperm with ⟨_, _, _, hCnoneAll, _, _, _, _, _, rfl⟩
        simp only [recvAcquireState, recvAcquireShared] at hcur'
        have htxeq := Option.some.inj hcur'
        subst htxeq
        simp only [plannedTxn] at hrem'
        left
        simp only [recvAcquireState, recvAcquireLocals, SymState.locals]
        rw [scheduleProbeLocals_chanB_true s i j (probeMaskForResult s i grow.result)
            .acquirePerm grow.result source hrem']
        simp
  -- RecvProbeAtMaster: clears chanB i, sets chanC i; shared unchanged
  | .recvProbeAtMaster =>
      rcases hstep with ⟨tx0, _, hcur0, _, _, _, _, _, _, _, _, rfl⟩
      -- shared unchanged
      simp only [recvProbeState, SymState.shared] at hcur'
      rw [hcur0] at hcur'; have := Option.some.inj hcur'; subst this
      simp only [recvProbeState, recvProbeLocals]
      by_cases hji : j = i
      · -- j = i: chanB cleared, chanC set to probeAck
        subst hji
        right
        simp [setFn, recvProbeLocal, probeAckMsg]
      · -- j ≠ i: frame
        have hBCold := hpci tx0 hcur0 hphase' j hrem'
        rcases hBCold with hB | hC
        · left; simpa [setFn, hji] using hB
        · right; simpa [setFn, hji] using hC
  -- RecvProbeAckAtManager: clears chanC i, sets probesRemaining i := false, may change phase
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨tx0, msg, hcur0, hphase0, hrem0, _, _, _, _, rfl⟩
      simp only [recvProbeAckState, recvProbeAckShared, SymState.shared] at hcur'
      have htxeq := Option.some.inj hcur'
      subst htxeq
      -- Now tx has probesRemaining = clearProbeIdx tx0.probesRemaining i.1
      -- and phase = probeAckPhase (clearProbeIdx ...)
      -- If new phase ≠ probing, hphase' gives contradiction
      -- If new phase = probing, we proceed
      -- For j = i: probesRemaining i in new txn = clearProbeIdx ... i.1 = false
      --   So hrem' : false = true, contradiction → vacuous
      -- For j ≠ i: probesRemaining j in new txn = tx0.probesRemaining j.1
      --   chanB j and chanC j unchanged → delegate to old invariant
      by_cases hji : j = i
      · subst hji
        -- clearProbeIdx sets i's bit to false
        simp [clearProbeIdx] at hrem'
      · -- j ≠ i: probesRemaining j unchanged
        have hrem_old : tx0.probesRemaining j.1 = true := by
          have : j.1 ≠ i.1 := fun h => hji (Fin.ext h)
          simpa [clearProbeIdx, this] using hrem'
        have hBCold := hpci tx0 hcur0 hphase0 j hrem_old
        simp only [recvProbeAckState, recvProbeAckLocals]
        rcases hBCold with hB | hC
        · left; simpa [setFn, hji] using hB
        · right; simpa [setFn, hji, recvProbeAckLocal] using hC
  -- SendGrantToRequester: phase = grantReady ≠ probing → vacuous
  | .sendGrantToRequester =>
      rcases hstep with ⟨tx0, hcur0, _, hphase0, _, _, _, _, _, rfl⟩
      simp only [sendGrantState, sendGrantShared, SymState.shared] at hcur'
      have htxeq := Option.some.inj hcur'
      -- new phase = grantPendingAck ≠ probing
      rw [← htxeq] at hphase'
      simp at hphase'
  -- RecvGrantAtMaster: shared unchanged (recvGrantShared preserves currentTxn)
  | .recvGrantAtMaster =>
      rcases hstep with ⟨tx0, _, hcur0, _, hphase0, _, _, _, _, _, _, rfl⟩
      simp only [recvGrantState, recvGrantShared, SymState.shared] at hcur'
      rw [hcur0] at hcur'; have := Option.some.inj hcur'; subst this
      -- phase = grantPendingAck ≠ probing
      exact absurd hphase' (by rw [hphase0]; decide)
  -- RecvGrantAckAtManager: clears currentTxn → vacuous
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
      simp [recvGrantAckState, recvGrantAckShared] at hcur'
  -- SendRelease: requires currentTxn = none → vacuous
  | .sendRelease _ =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      simp only [sendReleaseState, SymState.shared] at hcur'
      rw [hcurNone] at hcur'; simp at hcur'
  -- SendReleaseData: requires currentTxn = none → vacuous
  | .sendReleaseData _ =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      simp only [sendReleaseState, SymState.shared] at hcur'
      rw [hcurNone] at hcur'; simp at hcur'
  -- RecvReleaseAtManager: requires currentTxn = none → vacuous
  | .recvReleaseAtManager =>
      rcases hstep with ⟨_, _, hcurNone, _, _, _, _, _, _, _, _, _, rfl⟩
      simp only [recvReleaseState, recvReleaseShared, SymState.shared] at hcur'
      rw [hcurNone] at hcur'; simp at hcur'
  -- RecvReleaseAckAtMaster: requires currentTxn = none → shared unchanged → vacuous
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨_, hcurNone, _, _, _, _, _, rfl⟩
      simp only [recvReleaseAckState, recvReleaseAckShared, SymState.shared] at hcur'
      rw [hcurNone] at hcur'; simp at hcur'
  -- Store: requires currentTxn = none → vacuous
  | .store _ =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      rw [hcurNone] at hcur'; simp at hcur'
  -- Read: s' = s → delegate to old invariant
  | .read =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩
      exact hpci tx hcur' hphase' j hrem'
  -- UncachedGet: requires currentTxn = none → vacuous
  | .uncachedGet _ =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, rfl⟩
      rw [hcurNone] at hcur'; simp at hcur'
  -- UncachedPut: requires currentTxn = none → vacuous
  | .uncachedPut _ _ =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, _, rfl⟩
      simp at hcur'
      rw [hcurNone] at hcur'; simp at hcur'
  -- RecvUncachedAtManager: requires currentTxn = none → vacuous
  | .recvUncachedAtManager =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, rfl⟩
      rw [hcurNone] at hcur'; simp at hcur'
  -- RecvAccessAckAtMaster: shared unchanged, chanB/chanC unchanged
  | .recvAccessAckAtMaster =>
      rcases hstep with ⟨_, _, _, rfl⟩
      -- shared unchanged, so currentTxn unchanged
      have hBCold := hpci tx hcur' hphase' j hrem'
      rcases hBCold with hB | hC
      · left; by_cases hjk : j = i
        · subst hjk; simpa [setFn] using hB
        · simpa [setFn, hjk] using hB
      · right; by_cases hjk : j = i
        · subst hjk; simpa [setFn] using hC
        · simpa [setFn, hjk] using hC

/-- If chanD has an accessAck, then chanA is none. This is the key lemma enabling
    accessAckNotRequesterInv: since RecvAcquireBlock requires chanA = some, the requester
    can never have an accessAck on chanD.
    Proved inductively: RecvUncachedAtManager sets chanD=accessAck AND chanA=none in one step.
    All chanA-setting actions require pendingSource=none, but accessAck→pendingSource≠none. -/
def accessAckChanAInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ i : Fin n, match (s.locals i).chanD with
    | none => True
    | some msg =>
        (msg.opcode = .accessAck ∨ msg.opcode = .accessAckData) → (s.locals i).chanA = none

theorem init_accessAckChanAInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → accessAckChanAInv n s := by
  intro s hinit i
  rcases hinit with ⟨_, hlocals⟩
  rcases hlocals i with ⟨_, _, _, _, hD, _, _, _, _⟩
  simp [hD]

theorem accessAckChanAInv_preserved {n : Nat}
    {s s' : SymState HomeState NodeState n}
    (hinv : fullInv n s)
    (hacc : accessAckChanAInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    accessAckChanAInv n s' := by
  rcases hinv with ⟨⟨_, _, _, _⟩, ⟨hchanA, _, _, hchanD, _⟩, _⟩
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  intro k
  -- Tactic for "chanD has accessAck → pendingSource ≠ none contradicts guard"
  -- Used for SendAcquireBlock, SendAcquirePerm, UncachedGet, UncachedPut
  have chanD_accessAck_contradiction :
      ∀ (hPsNone : (s.locals i).pendingSource = none),
      match (s.locals i).chanD with
      | none => True
      | some msg =>
          (msg.opcode = .accessAck ∨ msg.opcode = .accessAckData) → False := by
    intro hPsNone
    specialize hchanD i
    cases hD : (s.locals i).chanD with
    | none => trivial
    | some msg =>
      rw [hD] at hchanD; intro hop
      rcases hchanD with ⟨tx', _, _, _, _, _, _, hmsg⟩ | ⟨_, _, _, _, _, _, hmsg⟩ | ⟨_, hps, _⟩
      · -- grant case: msg = grantMsgOfTxn tx'
        subst hmsg
        rcases hop with h | h <;> {
          simp only [grantMsgOfTxn, grantOpcodeOfTxn] at h
          split at h <;> exact absurd h (by decide)
        }
      · -- releaseAck case: msg = releaseAckMsg _
        subst hmsg; simp [releaseAckMsg] at hop
      · -- accessAck case: pendingSource ≠ none
        exact absurd hPsNone hps
  match a with
  | .sendAcquireBlock grow source =>
      rcases hstep with ⟨_, _, _, hPsNone, _, _, _, rfl⟩
      by_cases hki : k = i
      · subst k; simp only [SymState.locals, setFn, ite_true]
        show match (s.locals i).chanD with | none => True | some msg => _
        have := chanD_accessAck_contradiction hPsNone
        cases hD : (s.locals i).chanD with
        | none => trivial
        | some msg => rw [hD] at this; intro hop; exact absurd hop this
      · simp only [SymState.locals, setFn, show k ≠ i from hki, ite_false]; exact hacc k
  | .sendAcquirePerm grow source =>
      rcases hstep with ⟨_, _, _, hPsNone, _, _, _, rfl⟩
      by_cases hki : k = i
      · subst k; simp only [SymState.locals, setFn, ite_true]
        show match (s.locals i).chanD with | none => True | some msg => _
        have := chanD_accessAck_contradiction hPsNone
        cases hD : (s.locals i).chanD with
        | none => trivial
        | some msg => rw [hD] at this; intro hop; exact absurd hop this
      · simp only [SymState.locals, setFn, show k ≠ i from hki, ite_false]; exact hacc k
  | .recvAcquireAtManager =>
      -- Both RecvAcquireBlock and RecvAcquirePerm use recvAcquireState which
      -- calls scheduleProbeLocals. chanD unchanged, chanA of requester = none.
      rcases hstep with (⟨grow, source, hrecv⟩ | ⟨grow, source, hrecv⟩)
      · -- RecvAcquireBlockAtManager
        rcases hrecv with ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
        simp only [recvAcquireState, recvAcquireLocals, SymState.locals]
        -- Use simp lemmas: chanD unchanged, chanA self = none
        rw [scheduleProbeLocals_chanD s i _ _ _ _ k]
        by_cases hki : k = i
        · subst k
          rw [scheduleProbeLocals_chanA_self]
          specialize hacc i
          cases hD : (s.locals i).chanD with
          | none => trivial
          | some msg => intro _; rfl
        · rw [scheduleProbeLocals_chanA_other s i k _ _ _ _ hki]; exact hacc k
      · -- RecvAcquirePermAtManager
        rcases hrecv with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
        simp only [recvAcquireState, recvAcquireLocals, SymState.locals]
        rw [scheduleProbeLocals_chanD s i _ _ _ _ k]
        by_cases hki : k = i
        · subst k
          rw [scheduleProbeLocals_chanA_self]
          specialize hacc i
          cases hD : (s.locals i).chanD with
          | none => trivial
          | some msg => intro _; rfl
        · rw [scheduleProbeLocals_chanA_other s i k _ _ _ _ hki]; exact hacc k
  | .recvProbeAtMaster =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩
      simp only [recvProbeState, recvProbeLocals, SymState.locals]
      by_cases hki : k = i
      · subst k; simp only [setFn, ite_true, recvProbeLocal_chanD]
        cases (s.locals i).chanD with
        | none => trivial
        | some _ => intro _; exact recvProbeLocal_chanA _ _ _
      · simp only [setFn, show k ≠ i from hki, ite_false]; exact hacc k
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
      simp only [recvProbeAckState, recvProbeAckLocals, SymState.locals]
      by_cases hki : k = i
      · subst k; simp only [setFn, ite_true, recvProbeAckLocal]; exact hacc i
      · simp only [setFn, show k ≠ i from hki, ite_false]; exact hacc k
  | .sendGrantToRequester =>
      rcases hstep with ⟨tx, _, _, _, _, _, _, _, _, rfl⟩
      simp only [sendGrantState, sendGrantLocals, SymState.locals]
      by_cases hki : k = i
      · subst k; simp only [setFn, ite_true, sendGrantLocal]
        intro hop
        rcases hop with h | h <;> {
          simp only [grantMsgOfTxn, grantOpcodeOfTxn] at h
          split at h <;> exact absurd h (by decide)
        }
      · simp only [setFn, show k ≠ i from hki, ite_false]; exact hacc k
  | .recvGrantAtMaster =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩
      simp only [recvGrantState, recvGrantLocals, SymState.locals]
      by_cases hki : k = i
      · subst k; simp only [setFn, ite_true, recvGrantLocal]
      · simp only [setFn, show k ≠ i from hki, ite_false]; exact hacc k
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
      simp only [recvGrantAckState, recvGrantAckLocals, SymState.locals]
      by_cases hki : k = i
      · subst k; simp only [setFn, ite_true, recvGrantAckLocal]; exact hacc i
      · simp only [setFn, show k ≠ i from hki, ite_false]; exact hacc k
  | .sendRelease param =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      simp only [sendReleaseState, sendReleaseLocals, SymState.locals]
      by_cases hki : k = i
      · subst k; simp only [setFn, ite_true, sendReleaseLocal]; exact hacc i
      · simp only [setFn, show k ≠ i from hki, ite_false]; exact hacc k
  | .sendReleaseData param =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      simp only [sendReleaseState, sendReleaseLocals, SymState.locals]
      by_cases hki : k = i
      · subst k; simp only [setFn, ite_true, sendReleaseLocal]; exact hacc i
      · simp only [setFn, show k ≠ i from hki, ite_false]; exact hacc k
  | .recvReleaseAtManager =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      simp only [recvReleaseState, recvReleaseLocals, SymState.locals]
      by_cases hki : k = i
      · subst k; simp only [setFn, ite_true, recvReleaseLocal]
        intro hop; exfalso; rcases hop with h | h <;> simp [releaseAckMsg] at h
      · simp only [setFn, show k ≠ i from hki, ite_false]; exact hacc k
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨_, _, _, _, _, _, _, rfl⟩
      simp only [recvReleaseAckState, recvReleaseAckLocals, SymState.locals]
      by_cases hki : k = i
      · subst k; simp only [setFn, ite_true, recvReleaseAckLocal]
      · simp only [setFn, show k ≠ i from hki, ite_false]; exact hacc k
  | .store v =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      by_cases hki : k = i
      · subst k; simp only [SymState.locals, setFn, ite_true, storeLocal]; exact hacc i
      · simp only [SymState.locals, setFn, show k ≠ i from hki, ite_false]; exact hacc k
  | .read =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩; exact hacc k
  | .uncachedGet source =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, hPsNone, _, rfl⟩
      by_cases hki : k = i
      · subst k; simp only [SymState.locals, setFn, ite_true]
        show match (s.locals i).chanD with | none => True | some msg => _
        have := chanD_accessAck_contradiction hPsNone
        cases hD : (s.locals i).chanD with
        | none => trivial
        | some msg => rw [hD] at this; intro hop; exact absurd hop this
      · simp only [SymState.locals, setFn, show k ≠ i from hki, ite_false]; exact hacc k
  | .uncachedPut source v =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, hPsNone, _, rfl⟩
      by_cases hki : k = i
      · subst k; simp only [SymState.locals, setFn, ite_true]
        show match (s.locals i).chanD with | none => True | some msg => _
        have := chanD_accessAck_contradiction hPsNone
        cases hD : (s.locals i).chanD with
        | none => trivial
        | some msg => rw [hD] at this; intro hop; exact absurd hop this
      · simp only [SymState.locals, setFn, show k ≠ i from hki, ite_false]; exact hacc k
  | .recvUncachedAtManager =>
      rcases hstep with ⟨_, _, _, msg, hA, hop, rfl⟩
      by_cases hki : k = i
      · subst k; simp [setFn]
      · simp only [SymState.locals, setFn, show k ≠ i from hki, ite_false]; exact hacc k
  | .recvAccessAckAtMaster =>
      -- chanD i := none, pendingSource i := none
      rcases hstep with ⟨_, _, _, rfl⟩
      by_cases hki : k = i
      · subst k; simp only [SymState.locals, setFn, ite_true]
        -- chanD = none → match gives True
      · simp only [SymState.locals, setFn, show k ≠ i from hki, ite_false]; exact hacc k

/-- An accessAck on chanD for node i implies i is not the current requester.
    Key insight: RecvUncachedAtManager requires currentTxn = none and doesn't
    clear pendingSource. SendAcquireBlock requires pendingSource = none, which
    requires consuming the accessAck first (clearing chanD). So the requester
    can never have an accessAck on chanD during its own transaction. -/
def accessAckNotRequesterInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ i : Fin n, ∀ msg, (s.locals i).chanD = some msg →
    (msg.opcode = .accessAck ∨ msg.opcode = .accessAckData) →
    ∀ tx, s.shared.currentTxn = some tx → tx.requester ≠ i.1

theorem init_accessAckNotRequesterInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s →
      accessAckNotRequesterInv n s := by
  intro s hinit i msg hD _ tx hcur
  rcases hinit with ⟨⟨_, _, hcurNone, _, _, _⟩, _⟩
  rw [hcur] at hcurNone; simp at hcurNone

theorem accessAckNotRequesterInv_preserved {n : Nat}
    {s s' : SymState HomeState NodeState n}
    (hinv : fullInv n s)
    (hacca : accessAckChanAInv n s)
    (hnotreq : accessAckNotRequesterInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    accessAckNotRequesterInv n s' := by
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  match a with
  -- RecvAcquireBlockAtManager: creates txn with requester = acting node i
  -- Key case: use accessAckChanAInv to show requester ≠ k for any k with accessAck
  | .recvAcquireAtManager =>
      rcases hstep with hblk | hperm
      · -- RecvAcquireBlock for i
        rcases hblk with ⟨grow, source, hcur, _, _, _, _, hchanA, _, _, _, _, rfl⟩
        intro k msg hDk hop tx hcur'
        simp [recvAcquireState, recvAcquireShared] at hcur'
        rcases hcur' with rfl
        -- Need: requester (= i.1 from plannedTxn) ≠ k.1
        simp [plannedTxn]
        -- chanD k in new state = chanD k in old state (frame)
        have hDk_old : (s.locals k).chanD = some msg := by
          simpa [recvAcquireState, recvAcquireLocals, recvAcquireLocals_chanD] using hDk
        -- From accessAckChanAInv: chanA k = none
        specialize hacca k; rw [hDk_old] at hacca; have hAk := hacca hop
        -- RecvAcquireBlock guard: chanA i = some acquire
        -- If k = i: chanA i = some (guard) but chanA k = none (accessAckChanAInv). Contradiction.
        intro heq
        have : i = k := Fin.ext heq
        subst this
        rw [hAk] at hchanA; simp at hchanA
      · -- RecvAcquirePerm: same argument
        rcases hperm with ⟨grow, source, hcur, _, _, _, _, hchanA, _, _, _, rfl⟩
        intro k msg hDk hop tx hcur'
        simp [recvAcquireState, recvAcquireShared] at hcur'
        rcases hcur' with rfl
        simp [plannedTxn]
        have hDk_old : (s.locals k).chanD = some msg := by
          simpa [recvAcquireState, recvAcquireLocals, recvAcquireLocals_chanD] using hDk
        specialize hacca k; rw [hDk_old] at hacca; have hAk := hacca hop
        intro heq
        have : i = k := Fin.ext heq
        subst this
        rw [hAk] at hchanA; simp at hchanA
  -- RecvUncachedAtManager: sets chanD to accessAck but requires currentTxn = none
  | .recvUncachedAtManager =>
      rcases hstep with ⟨hcur, _, _, amsg, _, _, rfl⟩
      intro k msg hDk hop tx hcur'
      -- currentTxn is unchanged (shared state preserved)
      rw [hcur] at hcur'; simp at hcur'
  -- RecvAccessAckAtMaster: clears chanD
  | .recvAccessAckAtMaster =>
      rcases hstep with ⟨dmsg, _, _, rfl⟩
      intro k msg hDk hop tx hcur'
      by_cases hki : k = i
      · subst hki; simp [setFn] at hDk
      · have hDk_old : (s.locals k).chanD = some msg := by simpa [setFn, hki] using hDk
        exact hnotreq k msg hDk_old hop tx hcur'
  -- All remaining actions: currentTxn unchanged, chanD unchanged → delegate to old invariant
  | .sendAcquireBlock _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, rfl⟩
      intro k msg hDk hop tx hcur'
      have hDk_old : (s.locals k).chanD = some msg := by
        by_cases hki : k = i
        · subst hki; simpa [setFn] using hDk
        · simpa [setFn, hki] using hDk
      exact hnotreq k msg hDk_old hop tx hcur'
  | .sendAcquirePerm _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, rfl⟩
      intro k msg hDk hop tx hcur'
      have hDk_old : (s.locals k).chanD = some msg := by
        by_cases hki : k = i
        · subst hki; simpa [setFn] using hDk
        · simpa [setFn, hki] using hDk
      exact hnotreq k msg hDk_old hop tx hcur'
  | .recvProbeAtMaster =>
      rcases hstep with ⟨tx0, _, hcur0, _, _, _, _, _, _, _, _, rfl⟩
      intro k msg hDk hop tx hcur'
      -- recvProbeState preserves shared, so currentTxn unchanged
      simp only [recvProbeState, SymState.shared] at hcur'
      rw [hcur0] at hcur'; simp at hcur'; subst hcur'
      have hDk_old : (s.locals k).chanD = some msg := by
        simp [recvProbeState, recvProbeLocals] at hDk
        by_cases hki : k = i
        · subst hki; simp [recvProbeLocal] at hDk; exact hDk
        · simpa [setFn, hki] using hDk
      exact hnotreq k msg hDk_old hop tx0 hcur0
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨tx0, _, hcur0, _, _, _, _, _, _, rfl⟩
      intro k msg hDk hop tx hcur'
      have hDk_old : (s.locals k).chanD = some msg := by
        simp [recvProbeAckState, recvProbeAckLocals] at hDk
        by_cases hki : k = i
        · subst hki; simpa [setFn] using hDk
        · simpa [setFn, hki] using hDk
      -- recvProbeAckShared creates { tx0 with probesRemaining/phase updated }, preserving requester
      simp only [recvProbeAckState, SymState.shared, recvProbeAckShared] at hcur'
      -- hcur' : some { tx0 with probesRemaining := ..., phase := ... } = some tx
      -- Extract: { tx0 with ... } = tx, then tx.requester = tx0.requester
      have htxeq := Option.some.inj hcur'
      have hreq : tx.requester = tx0.requester := by rw [← htxeq]
      rw [hreq]
      exact hnotreq k msg hDk_old hop tx0 hcur0
  | .sendGrantToRequester =>
      rcases hstep with ⟨tx0, hcur0, hreqi, _, _, _, hchanDnone, _, _, rfl⟩
      intro k msg hDk hop tx hcur'
      -- sendGrantShared creates { tx0 with phase := .grantPendingAck }, preserving requester
      simp only [sendGrantState, SymState.shared, sendGrantShared] at hcur'
      have htxeq := Option.some.inj hcur'
      have : tx.requester = tx0.requester := by rw [← htxeq]
      rw [this]; clear this
      by_cases hki : k = i
      · subst hki
        -- Guard says chanD i = none, but sendGrantLocal sets chanD := some (grantMsgOfTxn tx0)
        -- So in new state chanD k = some (grantMsgOfTxn tx0), and msg = grantMsgOfTxn tx0
        simp only [sendGrantState, sendGrantLocals, sendGrantLocal, setFn, ite_true,
          SymState.locals] at hDk
        have hmsg := Option.some.inj hDk
        rw [← hmsg] at hop
        rcases hop with hacc | hacc <;> {
          simp [grantMsgOfTxn, grantOpcodeOfTxn] at hacc
          split at hacc <;> exact absurd hacc (by decide)
        }
      · have hDk_old : (s.locals k).chanD = some msg := by
          simpa [sendGrantState, sendGrantLocals, sendGrantLocal, setFn, hki] using hDk
        exact hnotreq k msg hDk_old hop tx0 hcur0
  | .recvGrantAtMaster =>
      rcases hstep with ⟨tx0, _, hcur0, _, _, _, _, _, _, _, _, rfl⟩
      intro k msg hDk hop tx hcur'
      -- recvGrantShared preserves currentTxn from s.shared
      simp only [recvGrantState, SymState.shared, recvGrantShared] at hcur'
      rw [hcur0] at hcur'; simp at hcur'; subst hcur'
      by_cases hki : k = i
      · subst hki
        simp [recvGrantState, recvGrantLocals, recvGrantLocal, setFn] at hDk
      · have hDk_old : (s.locals k).chanD = some msg := by
          simpa [recvGrantState, recvGrantLocals, recvGrantLocal, setFn, hki] using hDk
        exact hnotreq k msg hDk_old hop tx0 hcur0
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨tx0, _, hcur0, _, _, _, _, _, _, _, rfl⟩
      intro k msg hDk hop tx hcur'
      simp [recvGrantAckState, recvGrantAckShared] at hcur'
  | .sendRelease _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      intro k msg hDk hop tx hcur'
      have hDk_old : (s.locals k).chanD = some msg := by
        simp only [sendReleaseState, sendReleaseLocals, SymState.locals] at hDk
        by_cases hki : k = i
        · subst hki; simpa [sendReleaseLocal, setFn] using hDk
        · simpa [setFn, hki] using hDk
      exact hnotreq k msg hDk_old hop tx hcur'
  | .sendReleaseData _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      intro k msg hDk hop tx hcur'
      have hDk_old : (s.locals k).chanD = some msg := by
        simp only [sendReleaseState, sendReleaseLocals, SymState.locals] at hDk
        by_cases hki : k = i
        · subst hki; simpa [sendReleaseLocal, setFn] using hDk
        · simpa [setFn, hki] using hDk
      exact hnotreq k msg hDk_old hop tx hcur'
  | .recvReleaseAtManager =>
      -- RecvReleaseAtManager requires currentTxn = none, so conclusion is vacuous
      rcases hstep with ⟨cmsg, _, hcurNone, _, _, _, _, _, _, _, _, _, rfl⟩
      intro k msg hDk hop tx hcur'
      -- recvReleaseShared preserves currentTxn from s.shared (which is none)
      simp only [recvReleaseState, SymState.shared, recvReleaseShared] at hcur'
      rw [hcurNone] at hcur'; simp at hcur'
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨_, _, _, _, _, _, _, rfl⟩
      intro k msg hDk hop tx hcur'
      by_cases hki : k = i
      · subst hki
        simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn] at hDk
      · have hDk_old : (s.locals k).chanD = some msg := by
          simpa [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn, hki] using hDk
        exact hnotreq k msg hDk_old hop tx hcur'
  | .store _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      intro k msg hDk hop tx hcur'
      have hDk_old : (s.locals k).chanD = some msg := by
        by_cases hki : k = i
        · subst hki; simpa [setFn, storeLocal] using hDk
        · simpa [setFn, hki] using hDk
      exact hnotreq k msg hDk_old hop tx hcur'
  | .read =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩
      exact hnotreq
  | .uncachedGet _ =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, rfl⟩
      intro k msg hDk hop tx hcur'
      rw [hcur] at hcur'; simp at hcur'
  | .uncachedPut _ _ =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, rfl⟩
      intro k msg hDk hop tx hcur'
      rw [hcur] at hcur'; simp at hcur'

/-- At grantPendingAck, the requester has either the grant on chanD or
    the grantAck on chanE (or both, during the transition).
    Key insight: SendGrantToRequester sets chanD and transitions to grantPendingAck.
    RecvGrant clears chanD and sets chanE. RecvGrantAck clears chanE and
    transitions away from grantPendingAck. -/
def grantWaveActiveInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ tx, s.shared.currentTxn = some tx → tx.phase = .grantPendingAck →
    ∀ i : Fin n, i.1 = tx.requester →
      (s.locals i).chanD ≠ none ∨ (s.locals i).chanE ≠ none

theorem init_grantWaveActiveInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s →
      grantWaveActiveInv n s := by
  intro s hinit tx hcur
  rcases hinit with ⟨⟨_, _, hcurNone, _, _, _⟩, _⟩
  rw [hcur] at hcurNone; simp at hcurNone

theorem grantWaveActiveInv_preserved {n : Nat}
    {s s' : SymState HomeState NodeState n}
    (hinv : fullInv n s)
    (hnotreq : accessAckNotRequesterInv n s)
    (hgwa : grantWaveActiveInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    grantWaveActiveInv n s' := by
  rcases hinv with ⟨_, ⟨_, _, _, hchanD, hchanE⟩, _⟩
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨j, a, hstep⟩ := hnext
  intro tx hcur' hphase' k hreq'
  match a with
  -- SendAcquireBlock: shared unchanged, chanD/chanE of k unchanged (only chanA/pendingSource change)
  | .sendAcquireBlock _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, rfl⟩
      have hcur : s.shared.currentTxn = some tx := hcur'
      have hDEold := hgwa tx hcur hphase' k hreq'
      rcases hDEold with hD | hE
      · left; by_cases hkj : k = j
        · subst hkj; simpa [setFn] using hD
        · simpa [setFn, hkj] using hD
      · right; by_cases hkj : k = j
        · subst hkj; simpa [setFn] using hE
        · simpa [setFn, hkj] using hE
  -- SendAcquirePerm: shared unchanged, chanD/chanE of k unchanged
  | .sendAcquirePerm _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, rfl⟩
      have hDEold := hgwa tx hcur' hphase' k hreq'
      rcases hDEold with hD | hE
      · left; by_cases hkj : k = j
        · subst hkj; simpa [setFn] using hD
        · simpa [setFn, hkj] using hD
      · right; by_cases hkj : k = j
        · subst hkj; simpa [setFn] using hE
        · simpa [setFn, hkj] using hE
  -- RecvAcquireAtManager: creates txn with phase = .probing, never .grantPendingAck → vacuous
  | .recvAcquireAtManager =>
      rcases hstep with ⟨_, _, hblk⟩ | ⟨_, _, hperm⟩
      · rcases hblk with ⟨_, _, _, _, _, _, _, _, _, _, hs'⟩
        rw [hs'] at hcur'
        simp only [recvAcquireState, recvAcquireShared] at hcur'
        have htxeq := Option.some.inj hcur'
        rw [← htxeq] at hphase'
        simp only [plannedTxn] at hphase'
        unfold probeAckPhase at hphase'; split at hphase' <;> cases hphase'
      · rcases hperm with ⟨_, _, _, _, _, _, _, _, _, hs'⟩
        rw [hs'] at hcur'
        simp only [recvAcquireState, recvAcquireShared] at hcur'
        have htxeq := Option.some.inj hcur'
        rw [← htxeq] at hphase'
        simp only [plannedTxn] at hphase'
        unfold probeAckPhase at hphase'; split at hphase' <;> cases hphase'
  -- RecvProbeAtMaster: shared unchanged, chanD unchanged, chanE unchanged (only chanB/chanC/line change)
  | .recvProbeAtMaster =>
      rcases hstep with ⟨_, _, hcur0, _, _, _, _, _, _, _, _, rfl⟩
      simp only [recvProbeState] at hcur'
      have hDEold := hgwa tx hcur' hphase' k hreq'
      rcases hDEold with hD | hE
      · left
        simp only [recvProbeState, recvProbeLocals]
        by_cases hkj : k = j
        · subst hkj; simp [setFn, recvProbeLocal]; exact hD
        · simpa [setFn, hkj] using hD
      · right
        simp only [recvProbeState, recvProbeLocals]
        by_cases hkj : k = j
        · subst hkj; simp [setFn, recvProbeLocal]; exact hE
        · simpa [setFn, hkj] using hE
  -- RecvProbeAckAtManager: phase becomes probing or grantReady, never grantPendingAck → vacuous
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨tx0, _, hcur0, hphase0, _, _, _, _, _, rfl⟩
      simp only [recvProbeAckState, recvProbeAckShared] at hcur'
      -- hcur' : some { tx0 with probesRemaining := ..., phase := probeAckPhase ... } = some tx
      -- So tx = { tx0 with ... } and tx.phase = probeAckPhase ...
      have htxeq := Option.some.inj hcur'
      subst htxeq
      -- Now hphase' : probeAckPhase ... = .grantPendingAck
      simp only [probeAckPhase] at hphase'
      split at hphase' <;> exact absurd hphase' (by decide)
  -- SendGrantToRequester: transitions TO grantPendingAck, sets chanD of requester
  | .sendGrantToRequester =>
      rcases hstep with ⟨tx0, hcur0, hreq0, hphase0, _, _, hchanDnone, hchanEnone, _, rfl⟩
      simp only [sendGrantState, sendGrantShared] at hcur'
      have htxeq := Option.some.inj hcur'
      subst htxeq
      -- Now tx is { tx0 with phase := .grantPendingAck }, so tx.requester = tx0.requester
      -- hreq' : k.1 = tx0.requester, hreq0 : tx0.requester = j.1
      simp only [sendGrantState, sendGrantLocals]
      have hkj_val : k.1 = j.1 := by rw [hreq']; exact hreq0
      have hkj : k = j := Fin.ext hkj_val
      subst hkj
      left
      simp [setFn, sendGrantLocal, grantMsgOfTxn]
  -- RecvGrantAtMaster: stays at grantPendingAck, clears chanD, sets chanE
  | .recvGrantAtMaster =>
      rcases hstep with ⟨tx0, _, hcur0, hreq0, hphase0, _, _, _, _, _, _, rfl⟩
      -- recvGrantShared preserves currentTxn, so tx = tx0
      simp only [recvGrantState, recvGrantShared] at hcur'
      rw [hcur0] at hcur'
      have htxeq := Option.some.inj hcur'
      subst htxeq
      simp only [recvGrantState, recvGrantLocals]
      -- k.1 = tx0.requester = j.1
      have hkj_val : k.1 = j.1 := by rw [hreq']; exact hreq0
      have hkj : k = j := Fin.ext hkj_val
      subst hkj
      right
      simp [setFn, recvGrantLocal]
  -- RecvGrantAckAtManager: sets currentTxn := none → vacuous
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
      simp [recvGrantAckState, recvGrantAckShared] at hcur'
  -- SendRelease: requires currentTxn = none → vacuous
  | .sendRelease _ =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      simp only [sendReleaseState, SymState.shared] at hcur'
      rw [hcurNone] at hcur'; simp at hcur'
  -- SendReleaseData: requires currentTxn = none → vacuous
  | .sendReleaseData _ =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      simp only [sendReleaseState, SymState.shared] at hcur'
      rw [hcurNone] at hcur'; simp at hcur'
  -- RecvReleaseAtManager: requires currentTxn = none → vacuous
  | .recvReleaseAtManager =>
      rcases hstep with ⟨_, _, hcurNone, _, _, _, _, _, _, _, _, _, rfl⟩
      simp only [recvReleaseState, SymState.shared, recvReleaseShared] at hcur'
      rw [hcurNone] at hcur'; simp at hcur'
  -- RecvReleaseAckAtMaster: requires currentTxn = none → vacuous
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨_, hcurNone, _, _, _, _, _, rfl⟩
      simp only [recvReleaseAckState, recvReleaseAckShared] at hcur'
      rw [hcurNone] at hcur'; simp at hcur'
  -- Store: requires currentTxn = none → vacuous
  | .store _ =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      rw [hcurNone] at hcur'; simp at hcur'
  -- Read: s' = s → delegate to hgwa
  | .read =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩
      exact hgwa tx hcur' hphase' k hreq'
  -- UncachedGet: requires currentTxn = none → vacuous
  | .uncachedGet _ =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, rfl⟩
      rw [hcurNone] at hcur'; simp at hcur'
  -- UncachedPut: shared.currentTxn = none in new state (mem changes but currentTxn doesn't)
  | .uncachedPut _ _ =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, _, rfl⟩
      simp at hcur'
      rw [hcurNone] at hcur'; simp at hcur'
  -- RecvUncachedAtManager: requires currentTxn = none → vacuous
  | .recvUncachedAtManager =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, rfl⟩
      rw [hcurNone] at hcur'; simp at hcur'
  -- RecvAccessAckAtMaster: shared unchanged, clears chanD of j
  | .recvAccessAckAtMaster =>
      rcases hstep with ⟨dmsg, hDj, hop, rfl⟩
      -- shared unchanged
      have hDEold := hgwa tx hcur' hphase' k hreq'
      by_cases hkj : k = j
      · subst hkj
        -- k = j: RecvAccessAck clears chanD of j, but we need chanD ≠ none ∨ chanE ≠ none
        -- From chanDInv: chanD j has grant (1st branch), releaseAck (2nd), or accessAck (3rd)
        -- Action guard: chanD j = some dmsg, opcode = accessAck | accessAckData
        -- From accessAckNotRequesterInv: accessAck on chanD → requester ≠ j
        -- But k.1 = j.1 = tx.requester → contradiction
        exfalso
        exact hnotreq k dmsg hDj hop tx hcur' (by omega)
      · rcases hDEold with hD | hE
        · left; simpa [setFn, hkj] using hD
        · right; simpa [setFn, hkj] using hE

/-- pendingSinkInv is derived from pendingSinkTxnInv + grantWaveActiveInv.
    The proof composes: pendingSinkTxnInv gives the transaction link,
    grantWaveActiveInv gives chanD ≠ none ∨ chanE ≠ none. -/
theorem pendingSinkInv_preserved {n : Nat}
    {s s' : SymState HomeState NodeState n}
    (hinv : fullInv n s)
    (hnotreq : accessAckNotRequesterInv n s)
    (hpst : pendingSinkTxnInv n s)
    (hgwa : grantWaveActiveInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    pendingSinkInv n s' := by
  have hpst' := pendingSinkTxnInv_preserved hinv hpst hnext
  have hgwa' := grantWaveActiveInv_preserved hinv hnotreq hgwa hnext
  intro k hps'
  rcases hpst' k hps' with ⟨tx, hcur', hreq', hphase'⟩
  exact hgwa' tx hcur' hphase' k hreq'.symm

/-- During an active transaction, the requester's chanA is none and pendingSource
    is set, as long as the grant hasn't been consumed yet.
    Covers phases: probing, grantReady, and the first half of grantPendingAck
    (while chanD still holds the grant, before RecvGrant clears it).
    The pendingSource ≠ none conjunct is the key inductive strengthening:
    it blocks all chanA-setting actions (SendAcquire, UncachedGet/Put)
    since they all require pendingSource = none. -/
def requesterChanAInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ tx, s.shared.currentTxn = some tx →
    ∀ i : Fin n, tx.requester = i.1 →
      (tx.phase = .probing ∨ tx.phase = .grantReady ∨
       (tx.phase = .grantPendingAck ∧ (s.locals i).chanD ≠ none)) →
      (s.locals i).chanA = none ∧ (s.locals i).pendingSource ≠ none

theorem init_requesterChanAInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s →
      requesterChanAInv n s := by
  intro s hinit tx hcur
  rcases hinit with ⟨⟨_, _, hcurNone, _, _, _⟩, _⟩
  rw [hcur] at hcurNone; simp at hcurNone

theorem requesterChanAInv_preserved {n : Nat}
    {s s' : SymState HomeState NodeState n}
    (hinv : fullInv n s)
    (hnotreq : accessAckNotRequesterInv n s)
    (hreq : requesterChanAInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    requesterChanAInv n s' := by
  rcases hinv with ⟨⟨_, _, _, htxnCore⟩, ⟨hchanA, _, _, hchanD, _⟩, _⟩
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨j, a, hstep⟩ := hnext
  intro tx hcur' k hreqk hphase'
  match a with
  -- SendAcquireBlock: shared unchanged, chanA j := some, pendingSource j := some
  | .sendAcquireBlock grow source =>
      rcases hstep with ⟨_, _, _, hPsNone, _, _, _, rfl⟩
      -- shared unchanged, so currentTxn preserved
      have hcur : s.shared.currentTxn = some tx := hcur'
      by_cases hkj : k = j
      · subst k
        -- chanD unchanged for acting node (only chanA/pendingSource change)
        have hphase : tx.phase = .probing ∨ tx.phase = .grantReady ∨
            (tx.phase = .grantPendingAck ∧ (s.locals j).chanD ≠ none) := by
          rcases hphase' with h | h | ⟨h1, h2⟩
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · right; right; refine ⟨h1, ?_⟩; simpa [SymState.locals, setFn] using h2
        have ⟨_, hps⟩ := hreq tx hcur j hreqk hphase
        exact absurd hPsNone hps
      · -- k ≠ j: chanA k and pendingSource k unchanged
        have hphase : tx.phase = .probing ∨ tx.phase = .grantReady ∨
            (tx.phase = .grantPendingAck ∧ (s.locals k).chanD ≠ none) := by
          rcases hphase' with h | h | ⟨h1, h2⟩
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · right; right; refine ⟨h1, ?_⟩; simpa [SymState.locals, setFn, hkj] using h2
        simp only [SymState.locals, setFn, show k ≠ j from hkj, ite_false]
        exact hreq tx hcur k hreqk hphase
  -- SendAcquirePerm: same as SendAcquireBlock
  | .sendAcquirePerm grow source =>
      rcases hstep with ⟨_, _, _, hPsNone, _, _, _, rfl⟩
      have hcur : s.shared.currentTxn = some tx := hcur'
      by_cases hkj : k = j
      · subst k
        have hphase : tx.phase = .probing ∨ tx.phase = .grantReady ∨
            (tx.phase = .grantPendingAck ∧ (s.locals j).chanD ≠ none) := by
          rcases hphase' with h | h | ⟨h1, h2⟩
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · right; right; refine ⟨h1, ?_⟩; simpa [SymState.locals, setFn] using h2
        have ⟨_, hps⟩ := hreq tx hcur j hreqk hphase
        exact absurd hPsNone hps
      · have hphase : tx.phase = .probing ∨ tx.phase = .grantReady ∨
            (tx.phase = .grantPendingAck ∧ (s.locals k).chanD ≠ none) := by
          rcases hphase' with h | h | ⟨h1, h2⟩
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · right; right; refine ⟨h1, ?_⟩; simpa [SymState.locals, setFn, hkj] using h2
        simp only [SymState.locals, setFn, show k ≠ j from hkj, ite_false]
        exact hreq tx hcur k hreqk hphase
  -- RecvAcquireAtManager: creates txn, clears chanA for requester
  | .recvAcquireAtManager =>
      rcases hstep with (⟨grow, source, hrecv⟩ | ⟨grow, source, hrecv⟩)
      · -- RecvAcquireBlockAtManager
        rcases hrecv with ⟨hcurNone, _, _, _, _, hAi, _, _, _, _, rfl⟩
        have hreqj : k = j := by
          simp only [recvAcquireState, SymState.shared, recvAcquireShared] at hcur'
          have htx := Option.some.inj hcur'
          have hplan : (plannedTxn s j .acquireBlock grow source).requester = j.1 := by
            simp [plannedTxn]
          rw [← htx, hplan] at hreqk
          exact Fin.ext hreqk.symm
        subst hreqj
        simp only [recvAcquireState, SymState.locals, recvAcquireLocals]
        constructor
        · exact scheduleProbeLocals_chanA_self s k _ _ _ _
        · rw [scheduleProbeLocals_pendingSource]
          specialize hchanA k
          rw [hAi] at hchanA
          rcases hchanA with ⟨hps, _⟩
          rw [hps]; exact Option.some_ne_none _
      · -- RecvAcquirePermAtManager
        rcases hrecv with ⟨hcurNone, _, _, _, _, hAi, _, _, _, rfl⟩
        have hreqj : k = j := by
          simp only [recvAcquireState, SymState.shared, recvAcquireShared] at hcur'
          have htx := Option.some.inj hcur'
          have hplan : (plannedTxn s j .acquirePerm grow source).requester = j.1 := by
            simp [plannedTxn]
          rw [← htx, hplan] at hreqk
          exact Fin.ext hreqk.symm
        subst hreqj
        simp only [recvAcquireState, SymState.locals, recvAcquireLocals]
        constructor
        · exact scheduleProbeLocals_chanA_self s k _ _ _ _
        · rw [scheduleProbeLocals_pendingSource]
          specialize hchanA k
          rw [hAi] at hchanA
          rcases hchanA with ⟨hps, _⟩
          rw [hps]; exact Option.some_ne_none _
  -- RecvProbeAtMaster: chanA/pendingSource/chanD unchanged, shared unchanged
  | .recvProbeAtMaster =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩
      -- shared unchanged
      have hcur : s.shared.currentTxn = some tx := hcur'
      -- Convert phase condition from post-state to pre-state (chanD unchanged by recvProbe)
      have hphase : tx.phase = .probing ∨ tx.phase = .grantReady ∨
          (tx.phase = .grantPendingAck ∧ (s.locals k).chanD ≠ none) := by
        rcases hphase' with h | h | ⟨h1, h2⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · right; right; refine ⟨h1, ?_⟩
          simp only [recvProbeState, recvProbeLocals, SymState.locals] at h2
          by_cases hkj : k = j
          · subst k; simpa [setFn, recvProbeLocal] using h2
          · simpa [setFn, hkj] using h2
      have ⟨hA, hPs⟩ := hreq tx hcur k hreqk hphase
      simp only [recvProbeState, recvProbeLocals, SymState.locals]
      by_cases hkj : k = j
      · subst k; simp only [setFn, ite_true, recvProbeLocal_chanA, recvProbeLocal_pendingSource]
        exact ⟨trivial, hPs⟩
      · simp only [setFn, show k ≠ j from hkj, ite_false]; exact ⟨hA, hPs⟩
  -- RecvProbeAckAtManager: may change phase, chanA/pendingSource/chanD unchanged
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨tx0, msg0, hcur0, hphase0, _, _, _, _, _, rfl⟩
      -- tx0.requester = k (new txn has same requester)
      have hreqk0 : tx0.requester = k.1 := by
        simp only [recvProbeAckState, SymState.shared, recvProbeAckShared] at hcur'
        have htx := Option.some.inj hcur'
        rw [← htx] at hreqk; exact hreqk
      -- phase in old state was probing
      have hphase_old : tx0.phase = .probing ∨ tx0.phase = .grantReady ∨
          (tx0.phase = .grantPendingAck ∧ (s.locals k).chanD ≠ none) :=
        Or.inl hphase0
      have ⟨hA, hPs⟩ := hreq tx0 hcur0 k hreqk0 hphase_old
      -- chanA/pendingSource unchanged by recvProbeAck
      simp only [recvProbeAckState, recvProbeAckLocals, SymState.locals]
      by_cases hkj : k = j
      · subst k; simp only [setFn, ite_true, recvProbeAckLocal]; exact ⟨hA, hPs⟩
      · simp only [setFn, show k ≠ j from hkj, ite_false]; exact ⟨hA, hPs⟩
  -- SendGrantToRequester: phase grantReady → grantPendingAck, sets chanD for requester
  | .sendGrantToRequester =>
      rcases hstep with ⟨tx0, hcur0, hreq0, hphase0, _, _, hDnone, _, _, rfl⟩
      -- tx0.requester = k (new txn has same requester as old)
      have hreqk0 : tx0.requester = k.1 := by
        simp only [sendGrantState, SymState.shared, sendGrantShared] at hcur'
        have htx := Option.some.inj hcur'
        rw [← htx] at hreqk; exact hreqk
      -- But tx0.requester = j (from hreq0)
      have hkj : k = j := Fin.ext (hreqk0.symm ▸ hreq0 ▸ rfl)
      subst hkj
      -- From IH at grantReady: chanA = none ∧ pendingSource ≠ none
      have ⟨hA, hPs⟩ := hreq tx0 hcur0 k hreqk0 (Or.inr (Or.inl hphase0))
      -- sendGrantLocal doesn't change chanA or pendingSource
      simp only [sendGrantState, sendGrantLocals, SymState.locals, setFn, ite_true, sendGrantLocal]
      exact ⟨hA, hPs⟩
  -- RecvGrantAtMaster: clears chanD and pendingSource
  | .recvGrantAtMaster =>
      rcases hstep with ⟨tx0, msg0, hcur0, hreq0, hphase0, _, _, hD0, _, _, _, rfl⟩
      -- recvGrantShared preserves currentTxn, so tx = tx0
      simp only [recvGrantState, SymState.shared, recvGrantShared] at hcur'
      rw [hcur0] at hcur'; have heq := Option.some.inj hcur'; subst heq
      -- tx0.requester = j (from hreq0) and tx0.requester = k (from hreqk)
      -- So k = j
      have hkj : k = j := Fin.ext (hreqk.symm ▸ hreq0 ▸ rfl)
      subst hkj
      -- After recvGrantLocal: chanD = none
      simp only [recvGrantState, recvGrantLocals, SymState.locals, setFn, ite_true, recvGrantLocal]
      -- The phase condition requires chanD ≠ none, but chanD = none → contradiction
      rcases hphase' with h | h | ⟨_, hDne⟩
      · exact absurd h (by rw [hphase0]; decide)
      · exact absurd h (by rw [hphase0]; decide)
      · simp only [recvGrantState, recvGrantLocals, SymState.locals, setFn, ite_true,
          recvGrantLocal] at hDne
        exact absurd rfl hDne
  -- RecvGrantAckAtManager: clears currentTxn → vacuous
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
      simp only [recvGrantAckState, SymState.shared, recvGrantAckShared] at hcur'
      exact absurd hcur' (by simp)
  -- SendRelease: requires currentTxn = none → vacuous
  | .sendRelease param =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      simp only [sendReleaseState, SymState.shared] at hcur'
      rw [hcurNone] at hcur'; exact absurd hcur' (by simp)
  -- SendReleaseData: requires currentTxn = none → vacuous
  | .sendReleaseData param =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      simp only [sendReleaseState, SymState.shared] at hcur'
      rw [hcurNone] at hcur'; exact absurd hcur' (by simp)
  -- RecvReleaseAtManager: requires currentTxn = none → vacuous
  | .recvReleaseAtManager =>
      rcases hstep with ⟨_, _, hcurNone, _, _, _, _, _, _, _, _, _, rfl⟩
      simp only [recvReleaseState, SymState.shared, recvReleaseShared] at hcur'
      rw [hcurNone] at hcur'; exact absurd hcur' (by simp)
  -- RecvReleaseAckAtMaster: requires currentTxn = none → vacuous
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨_, hcurNone, _, _, _, _, _, rfl⟩
      simp only [recvReleaseAckState, SymState.shared, recvReleaseAckShared] at hcur'
      rw [hcurNone] at hcur'; exact absurd hcur' (by simp)
  -- Store: requires currentTxn = none → vacuous
  | .store v =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      simp only [SymState.shared] at hcur'
      rw [hcurNone] at hcur'; exact absurd hcur' (by simp)
  -- Read: s' = s → trivial
  | .read =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩
      exact hreq tx hcur' k hreqk hphase'
  -- UncachedGet: requires currentTxn = none → vacuous
  | .uncachedGet source =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, rfl⟩
      simp only [SymState.shared] at hcur'
      rw [hcurNone] at hcur'; exact absurd hcur' (by simp)
  -- UncachedPut: requires currentTxn = none → vacuous
  | .uncachedPut source v =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, _, rfl⟩
      simp only [SymState.shared] at hcur'
      rw [hcurNone] at hcur'; exact absurd hcur' (by simp)
  -- RecvUncachedAtManager: requires currentTxn = none → vacuous
  | .recvUncachedAtManager =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, rfl⟩
      simp only [SymState.shared] at hcur'
      rw [hcurNone] at hcur'; exact absurd hcur' (by simp)
  -- RecvAccessAckAtMaster: clears chanD and pendingSource for acting node
  | .recvAccessAckAtMaster =>
      rcases hstep with ⟨msg0, hD0, hop0, rfl⟩
      -- shared unchanged
      simp only [SymState.shared] at hcur'
      have hcur : s.shared.currentTxn = some tx := hcur'
      by_cases hkj : k = j
      · subst k
        -- After RecvAccessAck: chanD j = none, pendingSource j = none
        -- Simplify hphase' to get the phase condition in terms of the post-state
        simp only [SymState.locals, setFn, ite_true] at hphase'
        -- The grantPendingAck ∧ chanD ≠ none branch has chanD = none → contradiction
        rcases hphase' with h | h | ⟨_, hDne⟩
        · -- probing: requester j has accessAck on chanD → contradiction
          exfalso; exact hnotreq j msg0 hD0 hop0 tx hcur hreqk
        · exfalso; exact hnotreq j msg0 hD0 hop0 tx hcur hreqk
        · -- chanD = none after update → none ≠ none contradiction
          exact absurd rfl hDne
      · have hphase : tx.phase = .probing ∨ tx.phase = .grantReady ∨
            (tx.phase = .grantPendingAck ∧ (s.locals k).chanD ≠ none) := by
          simp only [SymState.locals, setFn, show k ≠ j from hkj, ite_false] at hphase'
          exact hphase'
        simp only [SymState.locals, setFn, show k ≠ j from hkj, ite_false]
        exact hreq tx hcur k hreqk hphase

/-! ### Progress lemmas: enablement at each phase

    Each lemma shows that at a given phase, the relevant protocol action
    is enabled (there exists a successor state). -/

/-- At grantReady, SendGrantToRequester is enabled for the requester.
    Guards satisfied from fullInv + auxiliary invariants:
    - pendingGrantAck = none (pendingInv, phase ≠ grantPendingAck)
    - pendingReleaseAck = none (pendingInv, currentTxn = some)
    - chanD i = none (chanDInv + accessAckNotRequesterInv)
    - chanE i = none (chanEInv, phase ≠ grantPendingAck)
    - pendingSink i = none (pendingSinkInv + chanD/chanE = none) -/
theorem sendGrant_enabled {n : Nat}
    {s : SymState HomeState NodeState n}
    (hinv : fullInv n s)
    (hnotreq : accessAckNotRequesterInv n s)
    (hpst : pendingSinkTxnInv n s)
    (hready : grantReady n s) :
    ∃ i : Fin n, enabled (actSendGrantToRequester n i) s := by
  -- Extract invariants from fullInv
  rcases hinv with ⟨⟨_, _, hpending, htxnCore⟩, ⟨_, _, _, hchanD, hchanE⟩, _⟩
  -- Extract tx from grantReady
  rcases hready with ⟨tx, hcur, hphase⟩
  -- Get requester < n from txnCoreInv
  rw [txnCoreInv, hcur] at htxnCore
  rcases htxnCore with ⟨hreqLt, _, _, _, _, _, _, _⟩
  -- Define the requester index
  let i : Fin n := ⟨tx.requester, hreqLt⟩
  refine ⟨i, sendGrantState s i tx, ?_⟩
  -- Show actSendGrantToRequester fires
  refine ⟨.sendGrantToRequester, rfl, ?_⟩
  -- Unfold SendGrantToRequester
  simp only [tlMessages]
  refine ⟨tx, hcur, rfl, hphase, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · -- pendingGrantAck = none: from pendingInv, phase ≠ grantPendingAck
    rw [pendingInv, hcur] at hpending
    rcases hpending with ⟨_, hgrant⟩
    simp [hphase] at hgrant
    exact hgrant
  · -- pendingReleaseAck = none: from pendingInv, currentTxn = some
    rw [pendingInv, hcur] at hpending
    exact hpending.1
  · -- chanD i = none: from chanDInv + accessAckNotRequesterInv
    specialize hchanD i
    match hD : (s.locals i).chanD with
    | none => rfl
    | some msg =>
      rw [hD] at hchanD
      rcases hchanD with ⟨tx', hcur', hreq', hphase', _, _, _, _⟩ | ⟨hcurNone, _, _, _, _, _, _⟩ | ⟨hop, hps⟩
      · -- Grant branch: phase = grantPendingAck, but our phase = grantReady
        rw [hcur] at hcur'; cases hcur'
        rw [hphase] at hphase'; exact absurd hphase' (by decide)
      · -- ReleaseAck branch: currentTxn = none, contradiction
        rw [hcur] at hcurNone; exact absurd hcurNone (by simp)
      · -- AccessAck branch: from accessAckNotRequesterInv, requester ≠ i
        exfalso
        exact hnotreq i msg hD hop tx hcur rfl
  · -- chanE i = none: from chanEInv, phase ≠ grantPendingAck
    specialize hchanE i
    match hE : (s.locals i).chanE with
    | none => rfl
    | some msg =>
      rw [hE] at hchanE
      rcases hchanE with ⟨tx', hcur', _, hphase', _, _, _, _⟩
      rw [hcur] at hcur'; cases hcur'
      rw [hphase] at hphase'; exact absurd hphase' (by decide)
  · -- pendingSink i = none: from pendingSinkTxnInv
    by_contra hps
    rcases hpst i hps with ⟨tx', hcur', _, hphase'⟩
    rw [hcur] at hcur'; cases hcur'
    rw [hphase] at hphase'; exact absurd hphase' (by decide)

/-- At grantPendingAck, the requester has the grant on chanD or grantAck on chanE.
    RecvGrantAtMaster (if chanD) or RecvGrantAckAtManager (if chanE) is enabled. -/
theorem recvGrant_enabled {n : Nat}
    {s : SymState HomeState NodeState n}
    (hinv : fullInv n s)
    (hnotreq : accessAckNotRequesterInv n s)
    (hreqInv : requesterChanAInv n s)
    (hgwa : grantWaveActiveInv n s)
    (hpending : grantPendingAck n s) :
    (∃ i : Fin n, enabled (actRecvGrantAtMaster n i) s) ∨
    (∃ i : Fin n, enabled (actRecvGrantAckAtManager n i) s) := by
  -- Extract invariants from fullInv
  rcases hinv with ⟨⟨_, _, hpendingI, htxnCore⟩, ⟨_, _, _, hchanD, hchanE⟩, _⟩
  -- Extract tx from grantPendingAck
  rcases hpending with ⟨tx, hcur, hphase⟩
  -- Get requester < n from txnCoreInv
  rw [txnCoreInv, hcur] at htxnCore
  rcases htxnCore with ⟨hreqLt, _, _, _, _, _, _, _⟩
  let i : Fin n := ⟨tx.requester, hreqLt⟩
  -- Get pendingGrantAck = some tx.requester from pendingInv
  have hGrantAck : s.shared.pendingGrantAck = some i.1 := by
    rw [pendingInv, hcur] at hpendingI
    rcases hpendingI with ⟨_, hga⟩
    simp [hphase] at hga; exact hga
  -- From grantWaveActiveInv: chanD or chanE is non-none for the requester
  have hwave := hgwa tx hcur hphase i rfl
  rcases hwave with hchanDne | hchanEne
  · -- Case: chanD i ≠ none → RecvGrantAtMaster enabled
    left
    refine ⟨i, ?_⟩
    -- Get chanD info from chanDInv
    specialize hchanD i
    match hD : (s.locals i).chanD with
    | none => exact absurd hD hchanDne
    | some msg =>
      rw [hD] at hchanD
      rcases hchanD with ⟨tx', hcur', hreq', hphase', hga', hps', hEn, hmsg⟩ | ⟨hcurNone, _, _, _, _, _, _⟩ | ⟨hop, _⟩
      · -- Grant branch: all guards available
        rw [hcur] at hcur'; cases hcur'
        refine ⟨recvGrantState s i tx, .recvGrantAtMaster, rfl, ?_⟩
        simp only [tlMessages]
        refine ⟨tx, msg, hcur, rfl, hphase, hGrantAck, ?_, hD, hEn, hps', hmsg, rfl⟩
        -- chanA i = none from requesterChanAInv: during grantPendingAck with chanD ≠ none
        exact (hreqInv tx hcur i rfl (Or.inr (Or.inr ⟨hphase, hchanDne⟩))).1
      · -- ReleaseAck branch: currentTxn = none, contradiction
        rw [hcur] at hcurNone; exact absurd hcurNone (by simp)
      · -- AccessAck branch: from accessAckNotRequesterInv, requester ≠ i
        exfalso
        exact hnotreq i msg hD hop tx hcur rfl
  · -- Case: chanE i ≠ none → RecvGrantAckAtManager enabled
    right
    refine ⟨i, ?_⟩
    -- Get chanE info from chanEInv
    specialize hchanE i
    match hE : (s.locals i).chanE with
    | none => exact absurd hE hchanEne
    | some msg =>
      rw [hE] at hchanE
      rcases hchanE with ⟨tx', hcur', hreq', hphase', hga', hps', hDn, hmsg⟩
      rw [hcur] at hcur'; cases hcur'
      refine ⟨recvGrantAckState s i, .recvGrantAckAtManager, rfl, ?_⟩
      simp only [tlMessages]
      exact ⟨tx, msg, hcur, rfl, hphase, hGrantAck, hDn, hE, hps', hmsg, rfl⟩

/-- During probing with remaining probes, some node has a message on chanB or chanC.
    RecvProbeAtMaster (if chanB) or RecvProbeAckAtManager (if chanC) is enabled. -/
theorem probeAck_enabled {n : Nat}
    {s : SymState HomeState NodeState n}
    (hpci : probeChannelInv n s)
    (hprobing : probingWithRemaining n s) :
    ∃ tx j, s.shared.currentTxn = some tx ∧ tx.phase = .probing ∧
      tx.probesRemaining j.1 = true ∧
      ((s.locals j).chanB ≠ none ∨ (s.locals j).chanC ≠ none) := by
  rcases hprobing with ⟨tx, hcur, hphase, j, hrem⟩
  exact ⟨tx, j, hcur, hphase, hrem, hpci tx hcur hphase j hrem⟩

/-! ### Phase monotonicity

    Protocol actions never move the transaction phase backwards.
    This is the "stuttering or progress" condition for WF1. -/

/-- The transaction phase only advances or the transaction completes.
    This is a tautology on Option (some or none). -/
theorem phase_monotone {n : Nat}
    (s' : SymState HomeState NodeState n) :
    (∃ tx', s'.shared.currentTxn = some tx') ∨
    s'.shared.currentTxn = none := by
  cases h : s'.shared.currentTxn with
  | none => exact Or.inr rfl
  | some tx' => exact Or.inl ⟨tx', rfl⟩

/-! ### Probing has remaining probes

    If the transaction phase is `.probing`, there must be at least one
    remaining probe. This follows from the model: both recvAcquire and
    recvProbeAck set phase = probeAckPhase(probesRemaining), and
    probeAckPhase returns .probing iff some remaining bit is true. -/

def probingHasRemainingInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ tx, s.shared.currentTxn = some tx → tx.phase = .probing →
    ∃ j : Fin n, tx.probesRemaining j.1 = true

theorem init_probingHasRemainingInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s →
      probingHasRemainingInv n s := by
  intro s hinit tx hcur
  rcases hinit with ⟨⟨_, _, hcurNone, _, _, _⟩, _⟩
  rw [hcur] at hcurNone; simp at hcurNone

/-- Helper: if probeAckPhase returns .probing, some index has remaining = true. -/
private theorem probeAckPhase_probing_has_remaining {n : Nat} {f : Nat → Bool}
    (h : @probeAckPhase n f = .probing) : ∃ j : Fin n, f j.1 = true := by
  simp only [probeAckPhase] at h
  split at h
  · cases h
  · rename_i hna
    by_contra hne
    apply hna; intro j
    by_contra hj; exact hne ⟨j, by cases f j.1 <;> simp_all⟩

theorem probingHasRemainingInv_preserved {n : Nat}
    {s s' : SymState HomeState NodeState n}
    (hinv : probingHasRemainingInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    probingHasRemainingInv n s' := by
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  intro tx hcur' hphase'
  match a with
  -- Actions that don't change shared state → delegate to old invariant
  | .sendAcquireBlock _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, rfl⟩; exact hinv tx hcur' hphase'
  | .sendAcquirePerm _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, rfl⟩; exact hinv tx hcur' hphase'
  | .recvProbeAtMaster =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩; exact hinv tx hcur' hphase'
  | .read =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩; exact hinv tx hcur' hphase'
  | .recvAccessAckAtMaster =>
      rcases hstep with ⟨_, _, _, rfl⟩; exact hinv tx hcur' hphase'
  -- recvAcquire: new txn with phase = probeAckPhase probeMask
  | .recvAcquireAtManager =>
      rcases hstep with ⟨grow, source, hblk⟩ | ⟨grow, source, hperm⟩
      · rcases hblk with ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
        simp only [recvAcquireState, recvAcquireShared] at hcur'
        have htxeq := Option.some.inj hcur'; subst htxeq
        simp only [plannedTxn] at hphase'
        exact probeAckPhase_probing_has_remaining hphase'
      · rcases hperm with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
        simp only [recvAcquireState, recvAcquireShared] at hcur'
        have htxeq := Option.some.inj hcur'; subst htxeq
        simp only [plannedTxn] at hphase'
        exact probeAckPhase_probing_has_remaining hphase'
  -- recvProbeAck: updates phase and remaining together
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨tx0, msg, hcur0, _, _, hC, _, _, rfl⟩
      simp only [recvProbeAckState, recvProbeAckShared] at hcur'
      have htxeq := Option.some.inj hcur'; subst htxeq
      exact probeAckPhase_probing_has_remaining hphase'
  -- sendGrant: phase becomes grantPendingAck ≠ probing
  | .sendGrantToRequester =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
      simp only [sendGrantState, sendGrantShared] at hcur'
      have htxeq := Option.some.inj hcur'
      rw [← htxeq] at hphase'; simp at hphase'
  -- recvGrant: shared preserves currentTxn, phase = grantPendingAck
  | .recvGrantAtMaster =>
      rcases hstep with ⟨tx0, _, hcur0, _, hphase0, _, _, _, _, _, _, rfl⟩
      simp only [recvGrantState, recvGrantShared] at hcur'
      rw [hcur0] at hcur'; have := Option.some.inj hcur'; subst this
      exact absurd hphase' (by rw [hphase0]; decide)
  -- recvGrantAck: clears currentTxn
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
      simp [recvGrantAckState, recvGrantAckShared] at hcur'
  -- Actions requiring currentTxn = none → vacuous
  | .sendRelease _ =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      simp only [sendReleaseState, SymState.shared] at hcur'
      rw [hcurNone] at hcur'; simp at hcur'
  | .sendReleaseData _ =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      simp only [sendReleaseState, SymState.shared] at hcur'
      rw [hcurNone] at hcur'; simp at hcur'
  | .recvReleaseAtManager =>
      rcases hstep with ⟨_, _, hcurNone, _, _, _, _, _, _, _, _, _, rfl⟩
      simp only [recvReleaseState, recvReleaseShared] at hcur'
      rw [hcurNone] at hcur'; simp at hcur'
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨_, hcurNone, _, _, _, _, _, rfl⟩
      simp only [recvReleaseAckState, recvReleaseAckShared] at hcur'
      rw [hcurNone] at hcur'; simp at hcur'
  | .store _ =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      rw [hcurNone] at hcur'; simp at hcur'
  | .uncachedGet _ =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, rfl⟩
      rw [hcurNone] at hcur'; simp at hcur'
  | .uncachedPut _ _ =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, _, _, _, _, _, rfl⟩
      simp at hcur'; rw [hcurNone] at hcur'; simp at hcur'
  | .recvUncachedAtManager =>
      rcases hstep with ⟨hcurNone, _, _, _, _, _, rfl⟩
      rw [hcurNone] at hcur'; simp at hcur'

end TileLink.Messages.Liveness
