import Leslie.Examples.CacheCoherence.TileLink.Messages.Refinement.SimOther

namespace TileLink.Messages

open TLA TileLink SymShared Classical

/-! ### Forward-Simulation Invariant

    The forward-simulation theorem requires a stronger invariant than `refinementInv`
    to handle the sendGrant and recvGrantAck actions. We define `forwardSimInv` as the
    conjunction of all needed components. -/

/-- Combined invariant for the forward-simulation theorem. Includes:
    - `refinementInv` (fullInv + noDirtyInv + txnDataInv + cleanReleaseInv)
    - `cleanDataInv` (valid lines hold shared memory value)
    - `txnLineInv` (local lines match transaction snapshot)
    - `preLinesCleanInv` (pre-wave lines are clean)
    - `preLinesNoDirtyInv` (pre-wave lines not dirty)
    - `txnPlanInv` (transaction plan consistency) -/
structure ForwardSimInv (n : Nat) (s : SymState HomeState NodeState n) : Prop where
  ref : RefinementInv n s
  dataCoh : dataCoherenceInv n s
  txnLine : txnLineInv n s
  preClean : preLinesCleanInv n s
  preNoDirty : preLinesNoDirtyInv n s
  plan : txnPlanInv n s
  usedDirty : usedDirtySourceInv n s
  dirtyOwner : dirtyOwnerExistsInv n s
  reqPerm : preLinesReqPermInv n s
  preWF : preLinesWFInv n s
  txnTransferMem : txnTransferMemInv n s
  relData : releaseDataInv n s
  relDataChanC : releaseDataChanCInv n s
  txnNoRelease : txnNoReleaseInv n s

abbrev forwardSimInv := @ForwardSimInv

theorem init_forwardSimInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → forwardSimInv n s := by
  intro s hinit
  exact ⟨init_refinementInv n s hinit, init_dataCoherenceInv n s hinit,
    init_txnLineInv n s hinit, init_preLinesCleanInv n s hinit,
    init_preLinesNoDirtyInv n s hinit, init_txnPlanInv n s hinit,
    init_usedDirtySourceInv n s hinit, init_dirtyOwnerExistsInv n s hinit,
    init_preLinesReqPermInv n s hinit, init_preLinesWFInv n s hinit,
    init_txnTransferMemInv n s hinit, init_releaseDataInv n s hinit,
    init_releaseDataChanCInv n s hinit, init_txnNoReleaseInv n s hinit⟩

-- The following preservation proofs are needed to close `forwardSimInv_preserved`.
-- `refinementInv_preserved`, `preLinesNoDirtyInv_preserved`, and `preLinesCleanInv_preserved`
-- are already proved in Preservation.lean. The remaining three are mechanical case analyses
-- over the 12 actions; their structure mirrors the existing preservation proofs.

theorem dataCoherenceInv_preserved (n : Nat) (s s' : SymState HomeState NodeState n)
    (hinv : forwardSimInv n s) (hnext : (tlMessages.toSpec n).next s s') :
    dataCoherenceInv n s' := by
  rcases hinv with ⟨⟨hfull, hdirtyEx, hSwmr, htxnData, hcleanC, hrelUniq, hdirtyRelEx⟩, hdata, htxnLine', hpreClean', hpreNoDirty', _, husedDirty', _, _, hpreWF', _, hrelData', _, _⟩
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  -- intro pattern: j = currentTxn guard, hvalidJ = Fin n, hdirtyJ = releaseInFlight guard
  intro j hvalidJ hdirtyJ
  match a with
  | .sendAcquireBlock grow source =>
      rcases hstep with ⟨htxn, _, _, _, _, _, _, rfl⟩
      intro hvalid hdirtyK
      simp only [setFn] at *
      split at ⊢ <;> simp_all [dataCoherenceInv]
  | .sendAcquirePerm grow source =>
      rcases hstep with ⟨htxn, _, _, _, _, _, _, rfl⟩
      intro hvalid hdirtyK
      simp only [setFn] at *
      split at ⊢ <;> simp_all [dataCoherenceInv]
  | .recvAcquireAtManager =>
      -- lines/mem unchanged
      rcases hstep with hblk | hperm
      · rcases hblk with ⟨grow, source, _, _, _, _, _, _, _, _, _, _, rfl⟩
        simp [recvAcquireState, recvAcquireLocals, recvAcquireShared, setFn] at j hdirtyJ ⊢
      · rcases hperm with ⟨grow, source, _, _, _, _, _, _, _, _, _, rfl⟩
        simp [recvAcquireState, recvAcquireLocals, recvAcquireShared, setFn] at j hdirtyJ ⊢
  | .recvProbeAtMaster =>
      rcases hstep with ⟨tx, _, hcur, _, _, _, _, _, _, _, ⟨_, rfl⟩⟩
      simp [recvProbeState, hcur] at j
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, hC, _, _, rfl⟩
      simp [recvProbeAckState, recvProbeAckShared, hcur] at j
  | .sendGrantToRequester =>
      rcases hstep with ⟨tx, hcur, _, _, _, _, _, _, _, rfl⟩
      simp [sendGrantState, sendGrantShared, hcur] at j
  | .recvGrantAtMaster =>
      rcases hstep with ⟨tx, _, hcur, _, _, _, _, _, _, _, _, rfl⟩
      simp [recvGrantState, recvGrantShared, hcur] at j
  | .recvGrantAckAtManager =>
      -- recvGrantAck: currentTxn → none. Need: perm≠.N → dirty=false → data=mem.
      rcases hstep with ⟨tx, msg, hcur, hreq, hphase, _, _, _, _, hs'⟩
      rw [hs']
      -- Post-state: currentTxn = none (discharge guard), lines preserved, mem unchanged
      intro htxnNone hvalidJ hdirtyJ hvalid hdirtyK
      -- Lines preserved: recvGrantAckLocal only changes chanE/pendingSink
      have hline_eq : (recvGrantAckLocals s i hvalidJ).line = (s.locals hvalidJ).line := by
        simp [recvGrantAckLocals, setFn]; split <;> simp_all [recvGrantAckLocal]
      simp only [recvGrantAckState] at hvalid hdirtyK ⊢
      rw [hline_eq] at hvalid hdirtyK ⊢
      -- Now goal: (s.locals hvalidJ).line.data = s.shared.mem
      -- Use txnLineInv + probeSnapshotLine (same as cleanDataInv proof)
      have htxnL := by simpa [txnLineInv, hcur] using htxnLine'
      have hpreC := by simpa [preLinesCleanInv, hcur] using hpreClean'
      have htxnD := by simpa [txnDataInv, hcur] using htxnData
      have hwfPre := by simpa [preLinesWFInv, hcur] using hpreWF'
      have hlineCi := htxnL hvalidJ
      -- At grantPendingAck: requester with chanE → grantLine; others → probeSnapshotLine
      by_cases hreqJ : tx.requester = hvalidJ.1
      · -- Requester
        simp [txnSnapshotLine, hphase, hreqJ] at hlineCi
        by_cases hE : (s.locals hvalidJ).chanE = none
        · simp [hE] at hlineCi; rw [hlineCi] at hvalid hdirtyK ⊢
          exact hpreC hvalidJ.1 hvalidJ.is_lt hvalid hdirtyK
        · simp [show (s.locals hvalidJ).chanE ≠ none from hE] at hlineCi
          rw [hlineCi] at hvalid hdirtyK ⊢
          simp only [grantLine] at hvalid hdirtyK ⊢
          split at hvalid hdirtyK ⊢
          · exact htxnD.2.2 (Or.inr hphase)
          · exact hpreC hvalidJ.1 hvalidJ.is_lt (by rwa [← hreqJ]) hdirtyK
      · -- Non-requester: probeSnapshotLine
        simp [txnSnapshotLine, hphase, hreqJ] at hlineCi
        rw [hlineCi] at hvalid hdirtyK ⊢
        by_cases hneeded : tx.probesNeeded hvalidJ.1 = true
        · -- Probed: analyze probedLine
          simp only [probeSnapshotLine, hneeded, ite_true] at hvalid hdirtyK ⊢
          -- At grantPendingAck, all probesRemaining = false
          have ⟨⟨_, _, _, htxnCore⟩, _, _⟩ := hfull
          rw [txnCoreInv, hcur] at htxnCore
          have hrem := htxnCore.2.2.2.2.2.2.2 hphase hvalidJ
          simp only [hrem, show (false = true) = False from rfl, false_and, ite_false] at hvalid hdirtyK ⊢
          -- line = probedLine(preLines, cap)
          simp only [probedLine] at hvalid hdirtyK ⊢
          cases hcap : probeCapOfResult tx.resultPerm with
          | toN => simp [invalidatedLine] at hvalid
          | toB =>
            simp only [hcap, branchAfterProbe] at hvalid hdirtyK ⊢
            by_cases hdirtyPre : (tx.preLines hvalidJ.1).dirty = true
            · -- Dirty: txnDataInv + uniqueness
              have husedDS : tx.usedDirtySource = true := by
                by_contra h; have h' := Bool.eq_false_iff.mpr h
                have huds := by simpa [usedDirtySourceInv, hcur] using husedDirty'
                rw [huds h' hvalidJ.1 hvalidJ.is_lt (Ne.symm hreqJ)] at hdirtyPre; cases hdirtyPre
              obtain ⟨k, hklt, hk_dirty, htv_k⟩ := htxnD.2.1 husedDS
              have hj_eq_k : hvalidJ.1 = k := by
                by_contra hne
                have hpnd := by simpa [preLinesNoDirtyInv, hcur] using hpreNoDirty'
                exact absurd (hpnd k hvalidJ.1 hklt hvalidJ.is_lt (fun h => hne h.symm) hk_dirty)
                  ((hwfPre hvalidJ.1 hvalidJ.is_lt).1 hdirtyPre |>.1 ▸ TLPerm.noConfusion)
              rw [show hvalidJ.1 = k from hj_eq_k]; rw [← htv_k]
              exact (htxnD.2.2 (Or.inr hphase)).symm
            · -- Clean: preLinesCleanInv (perm ≠ .N)
              have hpermNeN : (tx.preLines hvalidJ.1).perm ≠ .N := by
                intro hpN; exact absurd ((hwfPre hvalidJ.1 hvalidJ.is_lt).2.2 hpN).2
                  (by rw [hdirtyPre]; decide)
              exact hpreC hvalidJ.1 hvalidJ.is_lt hpermNeN hdirtyPre
          | toT =>
            simp only [hcap, tipAfterProbe] at hvalid hdirtyK ⊢
            by_cases hdirtyPre : (tx.preLines hvalidJ.1).dirty = true
            · have husedDS : tx.usedDirtySource = true := by
                by_contra h; have h' := Bool.eq_false_iff.mpr h
                have huds := by simpa [usedDirtySourceInv, hcur] using husedDirty'
                rw [huds h' hvalidJ.1 hvalidJ.is_lt (Ne.symm hreqJ)] at hdirtyPre; cases hdirtyPre
              obtain ⟨k, hklt, hk_dirty, htv_k⟩ := htxnD.2.1 husedDS
              have hj_eq_k : hvalidJ.1 = k := by
                by_contra hne
                have hpnd := by simpa [preLinesNoDirtyInv, hcur] using hpreNoDirty'
                exact absurd (hpnd k hvalidJ.1 hklt hvalidJ.is_lt (fun h => hne h.symm) hk_dirty)
                  ((hwfPre hvalidJ.1 hvalidJ.is_lt).1 hdirtyPre |>.1 ▸ TLPerm.noConfusion)
              rw [show hvalidJ.1 = k from hj_eq_k]; rw [← htv_k]
              exact (htxnD.2.2 (Or.inr hphase)).symm
            · have hpermNeN : (tx.preLines hvalidJ.1).perm ≠ .N := by
                intro hpN; exact absurd ((hwfPre hvalidJ.1 hvalidJ.is_lt).2.2 hpN).2
                  (by rw [hdirtyPre]; decide)
              exact hpreC hvalidJ.1 hvalidJ.is_lt hpermNeN hdirtyPre
        · -- Unprobed: line = preLines. preLinesCleanInv applies.
          have hneededF : tx.probesNeeded hvalidJ.1 = false := by
            cases h : tx.probesNeeded hvalidJ.1 <;> simp_all
          simp only [probeSnapshotLine, hneededF, ite_false] at hvalid hdirtyK ⊢
          exact hpreC hvalidJ.1 hvalidJ.is_lt hvalid hdirtyK
  | .sendRelease param =>
      rcases hstep with ⟨htxn, _, _, _, _, _, _, _, _, _, _, hflight, _, _, _, hs'⟩
      subst hs'; intro hvalid hdirtyK
      -- sendRelease sets releaseInFlight := true at node i; shared unchanged
      by_cases hji : hvalidJ = i
      · -- node i: releaseInFlight = true in post-state, contradicts hdirtyJ
        subst hji; simp [sendReleaseState_releaseInFlight] at hdirtyJ
      · -- other nodes: unchanged, use hdata
        simp only [sendReleaseState_releaseInFlight, hji, ite_false] at hdirtyJ
        have hln : ((sendReleaseState s i param false).locals hvalidJ).line =
            (s.locals hvalidJ).line := by simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji]
        rw [hln] at hvalid hdirtyK ⊢
        simpa [sendReleaseState] using hdata (by simpa [sendReleaseState] using j) hvalidJ hdirtyJ hvalid hdirtyK
  | .sendReleaseData param =>
      rcases hstep with ⟨htxn, _, _, _, _, _, _, _, _, _, _, hflight, _, _, hs'⟩
      subst hs'; intro hvalid hdirtyK
      -- sendReleaseData sets releaseInFlight := true at node i; shared unchanged
      by_cases hji : hvalidJ = i
      · -- node i: releaseInFlight = true in post-state, contradicts hdirtyJ
        subst hji; simp [sendReleaseState_releaseInFlight] at hdirtyJ
      · -- other nodes: unchanged, use hdata
        simp only [sendReleaseState_releaseInFlight, hji, ite_false] at hdirtyJ
        have hln : ((sendReleaseState s i param true).locals hvalidJ).line =
            (s.locals hvalidJ).line := by simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji]
        rw [hln] at hvalid hdirtyK ⊢
        simpa [sendReleaseState] using hdata (by simpa [sendReleaseState] using j) hvalidJ hdirtyJ hvalid hdirtyK
  | .recvReleaseAtManager =>
      -- recvRelease at manager: shared.mem may change via releaseWriteback.
      -- recvReleaseLocal only changes chanC/chanD, NOT line or releaseInFlight.
      rcases hstep with ⟨msg, param, htxn, _, _, hflight, hchanC, _, _, _, _, _, hs'⟩
      subst hs'
      intro hvalid hdirtyK
      by_cases hji : hvalidJ = i
      · -- node i: releaseInFlight unchanged (still true), contradicts hdirtyJ
        subst hji
        simp only [recvReleaseState, recvReleaseLocals, setFn, ite_true,
          recvReleaseLocal] at hdirtyJ
        rw [hflight] at hdirtyJ; cases hdirtyJ
      · -- node j ≠ i: locals/line unchanged. Case split on msg.data (dirty vs clean release).
        have hlineEq : (recvReleaseState s i msg param).locals hvalidJ = s.locals hvalidJ := by
          simp [recvReleaseState, recvReleaseLocals, setFn, hji]
        simp only [hlineEq] at hvalid hdirtyK ⊢
        have hflightJ : (s.locals hvalidJ).releaseInFlight = false := by
          simp only [recvReleaseState, recvReleaseLocals, setFn, hji, ite_false] at hdirtyJ
          exact hdirtyJ
        -- Case split on whether the release carries dirty data
        by_cases hdirtyMsg : msg.data = none
        · -- Clean release: shared.mem = releaseWriteback old none = old.
          simp only [recvReleaseState, recvReleaseShared, releaseWriteback, hdirtyMsg]
          exact hdata htxn hvalidJ hflightJ hvalid hdirtyK
        · -- Dirty release: dirtyReleaseExclusiveInv gives perm j = .N → valid = false.
          have hDirtyRel : ∃ msg' : CMsg, (s.locals i).chanC = some msg' ∧ msg'.data ≠ none :=
            ⟨msg, hchanC, hdirtyMsg⟩
          have hpermN := hdirtyRelEx htxn i hflight hDirtyRel hvalidJ hji
          have hvalidFalse := (hfull.1.1 hvalidJ).2.2 hpermN |>.1
          rw [hvalidFalse] at hvalid; cases hvalid
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨msg, htxn, _, hrel, hflight, _, _, hs'⟩
      rw [hs']
      intro htxnNone hvalidJ hdirtyJ hvalid hdirtyK
      by_cases hji : hvalidJ = i
      · -- Node i: was releasing, releaseInFlight cleared. Use releaseDataInv.
        subst hji
        simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal,
          recvReleaseAckShared, setFn] at hvalid hdirtyK ⊢
        -- chanC i = none: from releaseUniqueInv (pendingReleaseAck ≠ none → all chanC = none)
        have hCnone := (hrelUniq htxn).1 (by rw [hrel]; simp)
        exact hrelData' htxn i hflight (fun msg h => by rw [hCnone i] at h; cases h) hvalid hdirtyK
      · -- Node j ≠ i: unchanged
        have hlineEq : (recvReleaseAckLocals s i hvalidJ).line = (s.locals hvalidJ).line := by
          simp [recvReleaseAckLocals, setFn, hji, recvReleaseAckLocal]
        simp only [recvReleaseAckState, recvReleaseAckShared] at hvalid hdirtyK ⊢
        rw [hlineEq] at hvalid hdirtyK ⊢
        have hdirtyJ' : (s.locals hvalidJ).releaseInFlight = false := by
          simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn, hji] at hdirtyJ
          exact hdirtyJ
        exact hdata htxn hvalidJ hdirtyJ' hvalid hdirtyK
  | .store v =>
      rcases hstep with ⟨htxn, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      intro hvalid hdirtyK
      simp only [setFn, storeLocal] at *
      split at ⊢ <;> simp_all [dataCoherenceInv, storeLocal]
  | .read =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩
      exact hdata j hvalidJ hdirtyJ
  | .uncachedGet source =>
      rcases hstep with ⟨htxn, _, _, _, _, _, _, _, _, _, rfl⟩
      intro hvalid hdirtyK
      simp only [setFn] at *
      split at ⊢ <;> simp_all [dataCoherenceInv]
  | .uncachedPut source v =>
      -- uncachedPut: all nodes have perm .N (from guard). Under lineWFInv,
      -- perm .N → valid = false. So the valid = true hypothesis is contradicted.
      rcases hstep with ⟨htxn, _, _, hallN, _, _, _, _, _, _, _, rfl⟩
      simp only [setFn] at j hdirtyJ ⊢
      intro hvalid
      -- s'.locals hvalidJ has same line as s.locals hvalidJ (uncachedPut only changes chanA/pendingSource)
      have hpermN : (s.locals hvalidJ).line.perm = .N := hallN hvalidJ
      have hvalidFalse : (s.locals hvalidJ).line.valid = false :=
        (hfull.1.1 hvalidJ).2.2 hpermN |>.1
      -- Post-state line is unchanged for all nodes (setFn only changes chanA/pendingSource)
      have hlineEq : (if hvalidJ = i then { (s.locals i) with chanA := some (mkPutMsg source), pendingSource := some source } else s.locals hvalidJ).line = (s.locals hvalidJ).line := by
        split
        · next h => subst h; rfl
        · rfl
      rw [hlineEq] at hvalid
      rw [hvalidFalse] at hvalid; cases hvalid
  | .recvUncachedAtManager =>
      rcases hstep with ⟨htxn, _, _, msg, _, _, rfl⟩
      intro hvalid hdirtyK
      simp only [setFn] at *
      split at ⊢ <;> simp_all [dataCoherenceInv]
  | .recvAccessAckAtMaster =>
      rcases hstep with ⟨msg, _, _, rfl⟩
      intro hvalid hdirtyK
      simp only [setFn] at *
      split at ⊢ <;> simp_all [dataCoherenceInv]

theorem txnLineInv_preserved (n : Nat) (s s' : SymState HomeState NodeState n)
    (hinv : forwardSimInv n s) (hnext : (tlMessages.toSpec n).next s s') :
    txnLineInv n s' := by
  rcases hinv with ⟨⟨hfull, hnoDirty, _, _, _⟩, _, htxnLine, _, _, _, _, _, _⟩
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  match a with
  | .sendAcquireBlock grow source =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp only [txnLineInv]
      match hcur : s.shared.currentTxn with
      | none => trivial
      | some tx =>
          rw [txnLineInv, hcur] at htxnLine
          intro j
          have hpre := htxnLine j
          by_cases hji : j = i
          · subst j; simp only [setFn, ite_true] at hpre ⊢
            simp only [txnSnapshotLine, probeSnapshotLine] at hpre ⊢; exact hpre
          · simp only [setFn, show (j = i) = False from propext ⟨hji, False.elim⟩, ite_false] at hpre ⊢
            exact hpre
  | .sendAcquirePerm grow source =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp only [txnLineInv]
      match hcur : s.shared.currentTxn with
      | none => trivial
      | some tx =>
          rw [txnLineInv, hcur] at htxnLine
          intro j
          have hpre := htxnLine j
          by_cases hji : j = i
          · subst j; simp only [setFn, ite_true] at hpre ⊢
            simp only [txnSnapshotLine, probeSnapshotLine] at hpre ⊢; exact hpre
          · simp only [setFn, show (j = i) = False from propext ⟨hji, False.elim⟩, ite_false] at hpre ⊢
            exact hpre
  | .recvAcquireAtManager =>
      rcases hstep with hblk | hperm
      · rcases hblk with ⟨grow, source, htxnNone, _, _, hCnone, _, _, _, _, _, _, hs'⟩
        rw [hs']
        simp only [txnLineInv, recvAcquireState, recvAcquireShared, recvAcquireLocals_line]
        intro j
        unfold txnSnapshotLine probeSnapshotLine plannedTxn
        have hCj := hCnone j
        have hlt := j.2
        by_cases hmask : probeMaskForResult s i grow.result j.1 = true
        · simp [hmask, hCj, hlt]
        · have hmaskF : probeMaskForResult s i grow.result j.1 = false := by
            cases h : probeMaskForResult s i grow.result j.1 <;> simp_all
          simp [hmaskF, hlt]
      · rcases hperm with ⟨grow, source, htxnNone, _, _, hCnone, _, _, _, _, _, hs'⟩
        rw [hs']
        simp only [txnLineInv, recvAcquireState, recvAcquireShared, recvAcquireLocals_line]
        intro j
        unfold txnSnapshotLine probeSnapshotLine plannedTxn
        have hCj := hCnone j
        have hlt := j.2
        by_cases hmask : probeMaskForResult s i grow.result j.1 = true
        · simp [hmask, hCj, hlt]
        · have hmaskF : probeMaskForResult s i grow.result j.1 = false := by
            cases h : probeMaskForResult s i grow.result j.1 <;> simp_all
          simp [hmaskF, hlt]
  | .recvProbeAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, hphase, hrem, _hA, _hB, _hsrc, _hop, hparam, hCnone, hs'⟩
      rw [hs']
      rw [txnLineInv, hcur] at htxnLine
      simp only [txnLineInv, recvProbeState, hcur]
      intro j
      by_cases hji : j = i
      · subst j
        simp only [recvProbeLocals, recvProbeLocal, setFn, ite_true]
        have hpre_i := htxnLine i
        have hnotGPA : ¬(tx.phase = .grantPendingAck ∧ tx.requester = i.1) := by
          intro ⟨h, _⟩; rw [hphase] at h; cases h
        simp only [txnSnapshotLine, hnotGPA, ite_false] at hpre_i ⊢
        rcases hfull with ⟨⟨_, _, _, htxnCore⟩, _, _⟩
        rcases (by simpa [txnCoreInv, hcur] using htxnCore :
            tx.requester < n ∧ _ ∧ _ ∧ _ ∧
            tx.probesNeeded tx.requester = false ∧
            (∀ k : Nat, tx.probesRemaining k = true → tx.probesNeeded k = true) ∧ _ ∧ _)
          with ⟨_, _, _, _, _, hsubset, _, _⟩
        have hneeded : tx.probesNeeded i.1 = true := hsubset i.1 hrem
        simp only [probeSnapshotLine, hneeded, ite_true, hrem, hCnone, and_self] at hpre_i
        simp only [probeSnapshotLine, hneeded, ite_true, hrem]
        simp only [show (some (probeAckMsg i (s.locals i).line) = none) = False from by simp, and_false, ite_false]
        rw [hpre_i, hparam]
      · simp only [recvProbeLocals, setFn, show (j = i) = False from propext ⟨hji, False.elim⟩, ite_false]
        exact htxnLine j
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨tx, msg, hcur, hphase, hrem, _hA, hC, _hsrc, _hwf, hs'⟩
      rw [hs']
      rw [txnLineInv, hcur] at htxnLine
      simp only [txnLineInv, recvProbeAckState, recvProbeAckShared, hcur]
      intro j
      by_cases hji : j = i
      · subst j
        simp only [recvProbeAckLocals, recvProbeAckLocal, setFn, ite_true]
        have hpre_i := htxnLine i
        have hnotGPA : ¬(tx.phase = .grantPendingAck ∧ tx.requester = i.1) := by
          intro ⟨h, _⟩; rw [hphase] at h; cases h
        simp only [txnSnapshotLine, hnotGPA, ite_false] at hpre_i ⊢
        rcases hfull with ⟨⟨_, _, _, htxnCore⟩, _, _⟩
        rcases (by simpa [txnCoreInv, hcur] using htxnCore :
            tx.requester < n ∧ _ ∧ _ ∧ _ ∧
            tx.probesNeeded tx.requester = false ∧
            (∀ k : Nat, tx.probesRemaining k = true → tx.probesNeeded k = true) ∧ _ ∧ _)
          with ⟨_, _, _, _, _, hsubset, _, _⟩
        have hneeded : tx.probesNeeded i.1 = true := hsubset i.1 hrem
        have hnotGPA' : ¬((probeAckPhase (n := n) (clearProbeIdx tx.probesRemaining i.1)) = .grantPendingAck ∧
            tx.requester = i.1) := by
          intro ⟨h, _⟩; simp [probeAckPhase] at h; split at h <;> cases h
        simp only [hnotGPA', ite_false]
        simp only [probeSnapshotLine, hneeded, ite_true] at hpre_i ⊢
        simp only [hC, hrem, show (some msg = none) = False from by simp, and_false, ite_false] at hpre_i
        simp only [clearProbeIdx, show i.1 = i.1 from rfl, ite_true, show (false = true) = False from by simp,
          false_and, ite_false]
        exact hpre_i
      · simp only [recvProbeAckLocals, setFn, show (j = i) = False from propext ⟨hji, False.elim⟩, ite_false]
        have hpre_j := htxnLine j
        have hnotGPA : ¬(tx.phase = .grantPendingAck ∧ tx.requester = j.1) := by
          intro ⟨h, _⟩; rw [hphase] at h; cases h
        have hnotGPA' : ¬((probeAckPhase (n := n) (clearProbeIdx tx.probesRemaining i.1)) = .grantPendingAck ∧
            tx.requester = j.1) := by
          intro ⟨h, _⟩; simp [probeAckPhase] at h; split at h <;> cases h
        simp only [txnSnapshotLine, hnotGPA, hnotGPA', ite_false] at hpre_j ⊢
        simp only [probeSnapshotLine] at hpre_j ⊢
        have hne : i.1 ≠ j.1 := by intro h; exact hji (Fin.ext_iff.mpr h.symm)
        simp only [clearProbeIdx, show (j.1 = i.1) = False from propext ⟨fun h => hne h.symm, False.elim⟩, ite_false]
        exact hpre_j
  | .sendGrantToRequester =>
      rcases hstep with ⟨tx, hcur, hreq, hphase, _, _, _hD, hE, _hSink, hs'⟩
      rw [hs']
      rw [txnLineInv, hcur] at htxnLine
      simp only [txnLineInv, sendGrantState, sendGrantShared, hcur]
      intro j
      have hpre_j := htxnLine j
      by_cases hji : j = i
      · subst j
        simp only [sendGrantLocals, setFn, ite_true, sendGrantLocal]
        simp only [txnSnapshotLine, show TxnPhase.grantPendingAck = TxnPhase.grantPendingAck from rfl,
          true_and, hreq, ite_true, hE]
        have hnotGPA : ¬(tx.phase = .grantPendingAck ∧ tx.requester = i.1) := by
          intro ⟨h, _⟩; rw [hphase] at h; cases h
        simp only [txnSnapshotLine, hnotGPA, ite_false] at hpre_j
        rcases hfull with ⟨⟨_, _, _, htxnCore⟩, _, _⟩
        rcases (by simpa [txnCoreInv, hcur] using htxnCore :
            tx.requester < n ∧ _ ∧ _ ∧ _ ∧
            tx.probesNeeded tx.requester = false ∧ _ ∧ _ ∧ _)
          with ⟨_, _, _, _, hnoProbeReq, _, _, _⟩
        rw [hreq] at hnoProbeReq
        simp only [probeSnapshotLine, hnoProbeReq, ite_false] at hpre_j
        exact hpre_j
      · simp only [sendGrantLocals, setFn, show (j = i) = False from propext ⟨hji, False.elim⟩, ite_false]
        have hreq_ne : ¬(tx.requester = j.1) := by
          intro h; apply hji; exact Fin.ext_iff.mpr (by rw [← hreq]; exact h.symm)
        -- Post txn has phase = grantPendingAck, but requester ≠ j → probeSnapshotLine
        simp only [txnSnapshotLine]
        simp only [show TxnPhase.grantPendingAck = TxnPhase.grantPendingAck from rfl, true_and,
          hreq_ne, ite_false]
        -- Pre: phase = grantReady → also probeSnapshotLine (with original tx)
        have hnotGPA : ¬(tx.phase = .grantPendingAck ∧ tx.requester = j.1) := by
          intro ⟨h, _⟩; rw [hphase] at h; cases h
        simp only [txnSnapshotLine, hnotGPA, ite_false] at hpre_j
        -- probeSnapshotLine doesn't use phase, so both are equal
        simp only [probeSnapshotLine] at hpre_j ⊢
        exact hpre_j
  | .recvGrantAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, hreq, hphase, _, _hA, _hD, hE, _hSink, _hmsg, hs'⟩
      rw [hs']
      rw [txnLineInv, hcur] at htxnLine
      simp only [txnLineInv, recvGrantState, recvGrantShared, hcur]
      intro j
      have hpre_j := htxnLine j
      by_cases hji : j = i
      · subst j
        simp only [recvGrantLocals, recvGrantLocal, setFn, ite_true]
        simp only [txnSnapshotLine, show TxnPhase.grantPendingAck = TxnPhase.grantPendingAck from rfl,
          true_and, hreq, ite_true, hphase]
        simp only [show (some ({ sink := tx.sink } : EMsg) = none) = False from by simp, ite_false]
        simp only [txnSnapshotLine, show TxnPhase.grantPendingAck = TxnPhase.grantPendingAck from rfl,
          true_and, hreq, ite_true, hphase, hE, ite_true] at hpre_j
        rw [hpre_j]
      · simp only [recvGrantLocals, setFn, show (j = i) = False from propext ⟨hji, False.elim⟩, ite_false]
        have hreq_ne : ¬(tx.requester = j.1) := by
          intro h; apply hji; exact Fin.ext_iff.mpr (by rw [← hreq]; exact h.symm)
        simp only [txnSnapshotLine, show ¬(TxnPhase.grantPendingAck = TxnPhase.grantPendingAck ∧ tx.requester = j.1) from
          fun ⟨_, h⟩ => hreq_ne h, ite_false] at hpre_j ⊢
        exact hpre_j
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨tx, msg, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnLineInv, recvGrantAckState, recvGrantAckShared]
  | .sendRelease param =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, htail⟩
      rcases htail with ⟨_, hs'⟩
      rw [hs']
      simp [txnLineInv, hcur, sendReleaseState]
  | .sendReleaseData param =>
      -- currentTxn = none → txnLineInv trivially True
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnLineInv, hcur, sendReleaseState]
  | .recvReleaseAtManager =>
      rcases hstep with ⟨msg, param, hcur, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnLineInv, hcur, recvReleaseState, recvReleaseShared]
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨msg, hcur, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnLineInv, hcur, recvReleaseAckState, recvReleaseAckShared]
  | .store v =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnLineInv, hcur]
  | .read =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩
      exact htxnLine
  | .uncachedGet source =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnLineInv, hcur]
  | .uncachedPut source v =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnLineInv, hcur]
  | .recvUncachedAtManager =>
      rcases hstep with ⟨hcur, _, _, msg, _, _, hs'⟩
      rw [hs']
      simp [txnLineInv, hcur]
  | .recvAccessAckAtMaster =>
      rcases hstep with ⟨msg, _, _, hs'⟩
      rw [hs']
      -- currentTxn unchanged (shared unchanged), so match on pre-state currentTxn
      simp only [txnLineInv]
      match hcur : s.shared.currentTxn with
      | none => trivial
      | some tx =>
          rw [txnLineInv, hcur] at htxnLine
          intro j
          have hpre := htxnLine j
          by_cases hji : j = i
          · subst j; simp [setFn] at hpre ⊢; exact hpre
          · simp [setFn, hji] at hpre ⊢; exact hpre

private theorem writableProbeMask_eq_snapshotWritableProbeMask {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n) (kind : ReqKind)
    (grow : GrowParam) (source : SourceId) :
    writableProbeMask s i =
      snapshotWritableProbeMask n (plannedTxn s i kind grow source) := by
  funext k
  by_cases hk : k < n
  · simp [writableProbeMask, snapshotWritableProbeMask, plannedTxn, hk, Fin.ext_iff]
  · simp [writableProbeMask, snapshotWritableProbeMask, hk]

private theorem cachedProbeMask_eq_snapshotCachedProbeMask {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n) (kind : ReqKind)
    (grow : GrowParam) (source : SourceId) :
    cachedProbeMask s i =
      snapshotCachedProbeMask n (plannedTxn s i kind grow source) := by
  funext k
  by_cases hk : k < n
  · simp [cachedProbeMask, snapshotCachedProbeMask, plannedTxn, hk, Fin.ext_iff]
  · simp [cachedProbeMask, snapshotCachedProbeMask, hk]

private theorem hasCachedOther_iff_snapshotHasCachedOther {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n) (kind : ReqKind)
    (grow : GrowParam) (source : SourceId) :
    hasCachedOther s i ↔
      snapshotHasCachedOther n (plannedTxn s i kind grow source) := by
  constructor
  · rintro ⟨j, hne, hperm⟩
    have hne' : j.1 ≠ i.1 := Fin.val_ne_of_ne hne
    exact ⟨j, hne', by simp [plannedTxn, j.is_lt, hperm]⟩
  · rintro ⟨j, hne, hperm⟩
    have hne' : j ≠ i := fun h => hne (congrArg Fin.val h)
    exact ⟨j, hne', by simpa [plannedTxn, j.is_lt] using hperm⟩

private theorem allOthersInvalid_iff_snapshotAllOthersInvalid {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n) (kind : ReqKind)
    (grow : GrowParam) (source : SourceId) :
    allOthersInvalid s i ↔
      snapshotAllOthersInvalid n (plannedTxn s i kind grow source) := by
  constructor
  · intro h j hne
    have hne' : j ≠ i := fun heq => hne (congrArg Fin.val heq)
    simp [plannedTxn, j.is_lt, h j hne']
  · intro h j hne
    have hne' : j.1 ≠ i.1 := Fin.val_ne_of_ne hne
    simpa [plannedTxn, j.is_lt] using h j hne'

theorem txnPlanInv_preserved (n : Nat) (s s' : SymState HomeState NodeState n)
    (hinv : forwardSimInv n s) (hnext : (tlMessages.toSpec n).next s s') :
    txnPlanInv n s' := by
  rcases hinv with ⟨⟨hfull, hnoDirty, _, _, _⟩, _, _, _, _, hplan, _, _, _⟩
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  match a with
  | .sendAcquireBlock _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [txnPlanInv] using hplan
  | .sendAcquirePerm _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [txnPlanInv] using hplan
  | .recvAcquireAtManager =>
      rcases hstep with hblk | hperm
      · -- RecvAcquireBlockAtManager
        rcases hblk with ⟨grow, source, _, _, _, _, _, _, hpermN, _, hcases, _, hs'⟩
        rw [hs']
        simp only [txnPlanInv, recvAcquireState, recvAcquireShared, plannedTxn]
        refine ⟨i.is_lt, trivial, ?_, ?_⟩
        · -- resultPerm = .B → snapshotHasCachedOther ∧ probesNeeded = snapshotWritableProbeMask
          intro hresB
          rcases hcases with ⟨hdirtyOther, hresult⟩ | ⟨_, hcached, hresult⟩ | ⟨_, hresult⟩
          · -- dirty case: hasDirtyOther → hasCachedOther (via lineWF: dirty→perm=.T→perm≠.N)
            rw [hresult] at hresB ⊢
            rcases hdirtyOther with ⟨j, hne, hdirty⟩
            rcases hfull with ⟨⟨hlineWF, _⟩, _, _⟩
            have hpermT := (hlineWF j).1 hdirty
            have hcached : hasCachedOther s i :=
              ⟨j, hne, by rw [hpermT.1]; exact TLPerm.noConfusion⟩
            exact ⟨(hasCachedOther_iff_snapshotHasCachedOther s i .acquireBlock grow source).mp hcached,
              by simp [probeMaskForResult];
                 exact writableProbeMask_eq_snapshotWritableProbeMask s i .acquireBlock grow source⟩
          · rw [hresult] at hresB ⊢
            exact ⟨(hasCachedOther_iff_snapshotHasCachedOther s i .acquireBlock grow source).mp hcached,
              by simp [probeMaskForResult];
                 exact writableProbeMask_eq_snapshotWritableProbeMask s i .acquireBlock grow source⟩
          · rw [hresult] at hresB; cases hresB
        · -- resultPerm = .T → snapshotAllOthersInvalid ∧ probesNeeded = noProbeMask
          intro hresT
          rcases hcases with ⟨_, hresult⟩ | ⟨_, _, hresult⟩ | ⟨hallInv, hresult⟩
          · rw [hresult] at hresT; cases hresT
          · rw [hresult] at hresT; cases hresT
          · rw [hresult] at hresT ⊢
            constructor
            · exact (allOthersInvalid_iff_snapshotAllOthersInvalid s i .acquireBlock grow source).mp hallInv
            · simp [probeMaskForResult]
              rw [cachedProbeMask_eq_noProbeMask_of_allOthersInvalid hallInv]
              rfl
      · -- RecvAcquirePermAtManager
        rcases hperm with ⟨grow, source, _, _, _, _, _, _, hgrowLegal, hresT, _, hs'⟩
        rw [hs']
        simp only [txnPlanInv, recvAcquireState, recvAcquireShared, plannedTxn]
        refine ⟨i.is_lt, trivial, hresT, ?_, ?_⟩
        · -- probesNeeded = snapshotCachedProbeMask
          rw [hresT]; simp [probeMaskForResult]
          exact cachedProbeMask_eq_snapshotCachedProbeMask s i .acquirePerm grow source
        · -- (preLines requester).perm ≠ .T
          simp [i.is_lt]
          cases grow <;> simp_all [GrowParam.legalFrom, GrowParam.source, GrowParam.result]
  | .recvProbeAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, _, hs'⟩
      rcases hs' with ⟨_, hs'⟩
      rw [hs']
      simpa [txnPlanInv, hcur, recvProbeState] using hplan
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp only [txnPlanInv, recvProbeAckState, recvProbeAckShared]
      simp only [txnPlanInv, hcur] at hplan
      exact hplan
  | .sendGrantToRequester =>
      rcases hstep with ⟨tx, hcur, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp only [txnPlanInv, sendGrantState, sendGrantShared]
      simp only [txnPlanInv, hcur] at hplan
      exact hplan
  | .recvGrantAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp only [txnPlanInv, recvGrantState, recvGrantShared, hcur]
      simp only [txnPlanInv, hcur] at hplan
      exact hplan
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨tx, msg, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnPlanInv, recvGrantAckState, recvGrantAckShared]
  | .sendRelease param =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, htail⟩
      rcases htail with ⟨_, hs'⟩
      rw [hs']
      simp [txnPlanInv, hcur, sendReleaseState]
  | .sendReleaseData param =>
      -- currentTxn = none → txnPlanInv trivially True
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnPlanInv, hcur, sendReleaseState]
  | .recvReleaseAtManager =>
      rcases hstep with ⟨msg, param, hcur, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnPlanInv, hcur, recvReleaseState, recvReleaseShared]
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨msg, hcur, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnPlanInv, hcur, recvReleaseAckState, recvReleaseAckShared]
  | .store v =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnPlanInv, hcur]
  | .read =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩
      exact hplan
  | .uncachedGet source =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnPlanInv, hcur]
  | .uncachedPut source v =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnPlanInv, hcur]
  | .recvUncachedAtManager =>
      rcases hstep with ⟨hcur, _, _, msg, _, _, hs'⟩
      rw [hs']
      simp [txnPlanInv, hcur]
  | .recvAccessAckAtMaster =>
      rcases hstep with ⟨msg, _, _, hs'⟩
      rw [hs']
      simp only [txnPlanInv]
      match hcur : s.shared.currentTxn with
      | none => trivial
      | some tx =>
          rw [txnPlanInv, hcur] at hplan
          exact hplan

theorem preLinesReqPermInv_preserved (n : Nat) (s s' : SymState HomeState NodeState n)
    (hfull : fullInv n s) (hreqPerm : preLinesReqPermInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    preLinesReqPermInv n s' := by
  -- preLines and requester are immutable ManagerTxn fields; only recvAcquire creates a new txn.
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  intro tx hcur hkind
  match a with
  | .recvAcquireAtManager =>
      rcases hstep with hblk | hperm
      · -- RecvAcquireBlockAtManager: precondition gives perm = .N
        rcases hblk with ⟨grow, source, _, _, _, _, _, _, hpermN, _, _, hBs, hs'⟩
        rw [hs'] at hcur
        simp [recvAcquireState, recvAcquireShared, plannedTxn] at hcur
        rw [← hcur]; simp [i.is_lt, hpermN]
      · -- RecvAcquirePermAtManager: kind = .acquirePerm ≠ .acquireBlock
        rcases hperm with ⟨grow, source, _, _, _, _, _, _, _, _, _, hs'⟩
        rw [hs'] at hcur
        simp [recvAcquireState, recvAcquireShared, plannedTxn] at hcur
        rw [← hcur] at hkind; simp at hkind
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs'] at hcur; simp [recvGrantAckState, recvGrantAckShared] at hcur
  | .recvProbeAckAtManager =>
      -- recvProbeAck updates phase/probesRemaining but preserves preLines, kind, requester
      rcases hstep with ⟨tx_orig, _, hcur_orig, _, _, _, _, _, _, hs'⟩
      rw [hs'] at hcur; simp [recvProbeAckState, recvProbeAckShared] at hcur
      rw [← hcur] at hkind ⊢; exact hreqPerm tx_orig hcur_orig hkind
  | .sendGrantToRequester =>
      -- sendGrant updates phase but preserves preLines, kind, requester
      rcases hstep with ⟨tx_orig, hcur_orig, _, _, _, _, _, _, _, hs'⟩
      rw [hs'] at hcur; simp [sendGrantState, sendGrantShared] at hcur
      rw [← hcur] at hkind ⊢; exact hreqPerm tx_orig hcur_orig hkind
  -- All remaining actions: currentTxn unchanged, use hreqPerm directly
  | .sendAcquireBlock grow source =>
      rcases hstep with ⟨_, _, _, _, _, _, _, rfl⟩; exact hreqPerm tx hcur hkind
  | .sendAcquirePerm grow source =>
      rcases hstep with ⟨_, _, _, _, _, _, _, rfl⟩; exact hreqPerm tx hcur hkind
  | .recvProbeAtMaster =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs'] at hcur; simpa using hreqPerm tx hcur hkind
  | .recvGrantAtMaster =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs'] at hcur; simpa using hreqPerm tx hcur hkind
  | .sendRelease param =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs'] at hcur; simpa using hreqPerm tx hcur hkind
  | .sendReleaseData param =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs'] at hcur; simpa using hreqPerm tx hcur hkind
  | .recvReleaseAtManager =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs'] at hcur; simpa using hreqPerm tx hcur hkind
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      rw [hs'] at hcur; simpa using hreqPerm tx hcur hkind
  | .store v =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      exact hreqPerm tx hcur hkind
  | .read => rcases hstep with ⟨_, _, _, _, _, _, rfl⟩; exact hreqPerm tx hcur hkind
  | .uncachedGet source =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
      exact hreqPerm tx hcur hkind
  | .uncachedPut source v =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩
      exact hreqPerm tx hcur hkind
  | .recvUncachedAtManager =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩; exact hreqPerm tx hcur hkind
  | .recvAccessAckAtMaster =>
      rcases hstep with ⟨_, _, _, rfl⟩; exact hreqPerm tx hcur hkind

theorem forwardSimInv_preserved (n : Nat) (s s' : SymState HomeState NodeState n)
    (hinv : forwardSimInv n s) (hnext : (tlMessages.toSpec n).next s s') :
    forwardSimInv n s' := by
  rcases hinv with ⟨hrefInv, hdata, htxnLine, hpreClean, hpreNoDirty, hplan, husedDirty, hdirtyOwner, hreqPerm, hpreWF, htxnTM, hrelData, hrelDCC, htxnNoRel⟩
  rcases hrefInv with ⟨hfull, hdirtyEx, hSwmr, htxnData, hcleanRel, hrelUniq, hdirtyRelEx⟩
  have hstrong : strongRefinementInv n s :=
    ⟨⟨hfull, hdirtyEx, hSwmr, htxnData, hcleanRel, hrelUniq, hdirtyRelEx⟩, htxnLine, hpreClean, hpreNoDirty, hplan, husedDirty, hdirtyOwner⟩
  have hfwd : forwardSimInv n s :=
    ⟨⟨hfull, hdirtyEx, hSwmr, htxnData, hcleanRel, hrelUniq, hdirtyRelEx⟩, hdata, htxnLine, hpreClean, hpreNoDirty, hplan, husedDirty, hdirtyOwner, hreqPerm, hpreWF, htxnTM, hrelData, hrelDCC, htxnNoRel⟩
  refine ⟨refinementInv_preserved n s s' hstrong hpreWF htxnTM hnext,
    dataCoherenceInv_preserved n s s' hfwd hnext,
    txnLineInv_preserved n s s' hfwd hnext,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact preLinesCleanInv_preserved n s s' hfull hdata hpreClean hcleanRel hpreNoDirty hpreWF hnext
  · exact preLinesNoDirtyInv_preserved n s s' hfull hdirtyEx hSwmr hpreNoDirty hnext
  · exact txnPlanInv_preserved n s s' hfwd hnext
  · exact usedDirtySourceInv_preserved n s s' hfull husedDirty hnext
  · exact dirtyOwnerExistsInv_preserved n s s' hfull hdirtyOwner hnext
  · exact preLinesReqPermInv_preserved n s s' hfull hreqPerm hnext
  · exact preLinesWFInv_preserved n s s' hfull hpreWF hnext
  · exact releaseDataInv_preserved n s s' hfull hdata hrelData hrelDCC htxnNoRel hdirtyRelEx hnext
  · exact releaseDataChanCInv_preserved n s s' hfull hrelDCC hnext
  · exact txnNoReleaseInv_preserved n s s' hfull htxnNoRel hnext
  · exact txnTransferMemInv_preserved n s s' hfull htxnData hpreNoDirty husedDirty hdirtyOwner hpreWF htxnTM hnext

theorem refinement_inv_invariant (n : Nat) :
    pred_implies (tlMessages.toSpec n).safety [tlafml| □ ⌜ refinementInv n ⌝] := by
  have h : pred_implies (tlMessages.toSpec n).safety [tlafml| □ ⌜ forwardSimInv n ⌝] := by
    apply init_invariant
    · intro s hinit; exact init_forwardSimInv n s hinit
    · intro s s' hnext hinv; exact forwardSimInv_preserved n s s' hinv hnext
  intro σ hsafe k
  exact (h σ hsafe k).1

/-! ### Forward-Simulation Dispatch

    For each message-level action, we prove that either:
    - the refMap is unchanged (stuttering), or
    - there exists an atomic-level action that transforms refMap(s) to refMap(s')

    Actions that require additional hypotheses (like `hCother` for recvReleaseAtManager
    and `hCnone` for recvReleaseAckAtMaster) derive them from the forwardSimInv. -/

-- Helper: when pendingReleaseAck = some i.1 and currentTxn = none,
-- all chanC are none (the release has already been consumed by the manager).
-- This follows from chanDInv (releaseAck on D implies chanC = none for that node)
-- and the single-release-in-flight constraint.
private theorem chanC_none_of_releaseAck_pending {n : Nat}
    {s : SymState HomeState NodeState n} {i : Fin n}
    (hrelUniq : releaseUniqueInv n s) (htxn : s.shared.currentTxn = none)
    (hrel : s.shared.pendingReleaseAck = some i.1) :
    ∀ j : Fin n, (s.locals j).chanC = none :=
  (hrelUniq htxn).1 (by rw [hrel]; simp)

theorem forwardSim_step (n : Nat) (s s' : SymState HomeState NodeState n)
    (hinv : forwardSimInv n s) (hnext : (tlMessages.toSpec n).next s s') :
    (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n s') ∨
    refMap n s = refMap n s' := by
  rcases hinv with ⟨⟨hfull, hnoDirty, hSwmr, htxnData, hcleanRel, hrelUniq, hdirtyRelEx⟩, hclean, htxnLine, hpreClean, hpreNoDirty, hplan, husedDirty, _, hreqPerm, hpreWF, _, _, _, _⟩
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  match a with
  | .sendAcquireBlock grow source =>
      right; exact (refMap_sendAcquireBlock_eq hstep).symm
  | .sendAcquirePerm grow source =>
      right; exact (refMap_sendAcquirePerm_eq hstep).symm
  | .recvAcquireAtManager =>
      left; exact refMap_recvAcquireAtManager_next ⟨hfull, hnoDirty, hSwmr, htxnData, hcleanRel, hrelUniq, hdirtyRelEx⟩ hstep
  | .recvProbeAtMaster =>
      right; exact (refMap_recvProbeAtMaster_eq hstep).symm
  | .recvProbeAckAtManager =>
      right; exact (refMap_recvProbeAckAtManager_eq hfull htxnData hpreNoDirty husedDirty hstep).symm
  | .sendGrantToRequester =>
      left
      rcases hstep with ⟨tx, hcur, hreq, hphase, hgrant, hrel, hD, hE, hSink, hs'⟩
      have hstep' : SendGrantToRequester s s' i := ⟨tx, hcur, hreq, hphase, hgrant, hrel, hD, hE, hSink, hs'⟩
      cases htx : tx.kind with
      | acquireBlock =>
          cases hperm : tx.resultPerm with
          | N => -- acquireBlock can't produce N; resultPerm = grow.result ≠ N
              have ⟨⟨_, _, _, htxnCore⟩, _, _⟩ := hfull
              unfold txnCoreInv at htxnCore; rw [hcur] at htxnCore
              rcases htxnCore with ⟨_, _, hresultEq, _⟩
              rw [hperm] at hresultEq; revert hresultEq
              cases tx.grow <;> simp [GrowParam.result]
          | B => -- Derive cleanDataInv at grantReady from txnDataInv + preLinesCleanInv + txnLineInv.
                 have hcleanData : cleanDataInv n s := by
                   intro ci hvalid_ci
                   -- txnLineInv: line = txnSnapshotLine = probeSnapshotLine (phase ≠ grantPendingAck)
                   have hnotGPA : tx.phase ≠ .grantPendingAck := by simp [hphase]
                   have htxnL := by simpa [txnLineInv, hcur] using htxnLine
                   have hlineCi := htxnL ci
                   simp [txnSnapshotLine, hphase] at hlineCi
                   -- hlineCi : (s.locals ci).line = probeSnapshotLine tx (s.locals ci) ci
                   rw [hlineCi] at hvalid_ci ⊢
                   -- Case split on probesNeeded
                   by_cases hneeded : tx.probesNeeded ci.1 = true
                   · -- probesNeeded = true: probedLine
                     simp only [probeSnapshotLine, hneeded, ite_true] at hvalid_ci ⊢
                     have ⟨⟨_, _, _, htxnCore⟩, _, _⟩ := hfull
                     rw [txnCoreInv, hcur] at htxnCore
                     -- At grantReady, all probesRemaining = false
                     have hrem := htxnCore.2.2.2.2.2.2.1 (Or.inl hphase) ci
                     split at hvalid_ci ⊢
                     · rename_i hand; exact absurd hand.1 (by rw [hrem]; decide)
                     · -- probedLine with cap = probeCapOfResult .B = .toB
                       rw [hperm]; simp [probeCapOfResult, probedLine, branchAfterProbe] at hvalid_ci ⊢
                       -- data = preLines.data; need preLines.data = mem
                       have hpreC := by simpa [preLinesCleanInv, hcur] using hpreClean
                       have htxnD := by simpa [txnDataInv, hcur] using htxnData
                       have hwfPre := by simpa [preLinesWFInv, hcur] using hpreWF
                       -- preLines ci had perm .T (in writableProbeMask); perm ≠ .N
                       by_cases hdirtyPre : (tx.preLines ci.1).dirty = true
                       · -- Dirty: txnDataInv Part 2 + uniqueness → data = mem
                         have husedDS : tx.usedDirtySource = true := by
                           by_contra h; have h' := Bool.eq_false_iff.mpr h
                           have huds := by simpa [usedDirtySourceInv, hcur] using husedDirty
                           have hreqNe : ci.1 ≠ tx.requester := by
                             intro heq; rw [heq] at hdirtyPre
                             have hpermT := (hwfPre tx.requester (by
                               rcases (by simpa [txnPlanInv, hcur] using hplan) with ⟨hlt, _⟩; exact hlt)).1 hdirtyPre |>.1
                             have hpermN := hreqPerm tx hcur htx
                             rw [hpermT] at hpermN; exact TLPerm.noConfusion hpermN
                           rw [huds h' ci.1 ci.is_lt hreqNe] at hdirtyPre; cases hdirtyPre
                         obtain ⟨k, hklt, hk_dirty, htv_k⟩ := htxnD.2.1 husedDS
                         have hj_eq_k : ci.1 = k := by
                           by_contra hne
                           have hpnd := by simpa [preLinesNoDirtyInv, hcur] using hpreNoDirty
                           exact absurd (hpnd k ci.1 hklt ci.is_lt (fun h => hne h.symm) hk_dirty)
                             ((hwfPre ci.1 ci.is_lt).1 hdirtyPre |>.1 ▸ TLPerm.noConfusion)
                         rw [show ci.1 = k from hj_eq_k]; rw [← htv_k]
                         exact (htxnD.2.2 (Or.inl hphase)).symm
                       · -- Clean: preLinesCleanInv (perm ≠ .N)
                         have hpermNeN : (tx.preLines ci.1).perm ≠ .N := by
                           intro hpN
                           exact absurd ((hwfPre ci.1 ci.is_lt).2.2 hpN).2 (by rw [hdirtyPre]; decide)
                         exact hpreC ci.1 ci.is_lt hpermNeN hdirtyPre
                   · -- probesNeeded = false: line = preLines
                     have hneededF : tx.probesNeeded ci.1 = false := by
                       cases h : tx.probesNeeded ci.1 <;> simp_all
                     simp only [probeSnapshotLine, hneededF, ite_false] at hvalid_ci ⊢
                     -- valid = true → perm ≠ .N (WF); preLinesCleanInv applies
                     have hwfPre := by simpa [preLinesWFInv, hcur] using hpreWF
                     have hpreC := by simpa [preLinesCleanInv, hcur] using hpreClean
                     have hpermNeN : (tx.preLines ci.1).perm ≠ .N := by
                       intro hpN; rw [(hwfPre ci.1 ci.is_lt).2.2 hpN |>.1] at hvalid_ci; cases hvalid_ci
                     -- dirty = false: dirty → perm .T → in writableProbeMask → probesNeeded = true
                     have hdirtyF : (tx.preLines ci.1).dirty = false := by
                       by_contra hd; simp only [Bool.not_eq_false] at hd
                       have hpermT := (hwfPre ci.1 ci.is_lt).1 hd |>.1
                       have hmask := (txnPlanInv_acquireBlock_branch hplan hcur htx hperm).2
                       -- probesNeeded ci = snapshotWritableProbeMask ci = true (perm .T, ci ≠ req)
                       have : tx.probesNeeded ci.1 = true := by
                         rw [hmask]; simp [snapshotWritableProbeMask, ci.is_lt, hpermT]
                         intro heq; rw [heq] at hpermT
                         exact absurd hpermT (by rw [hreqPerm tx hcur htx]; exact TLPerm.noConfusion)
                       -- contradicts hneeded (probesNeeded = false)
                       simp only [this] at hneeded
                     exact hpreC ci.1 ci.is_lt hpermNeN hdirtyF
                 exact refMap_sendGrant_block_branch_next hfull hcleanData htxnLine hpreNoDirty htxnData hplan husedDirty hpreWF hreqPerm hstep' hcur htx hperm
          | T => exact refMap_sendGrant_block_tip_next hfull htxnLine htxnData hplan hreqPerm hstep' hcur htx hperm
      | acquirePerm =>
          exact refMap_sendGrant_acquirePerm_next hfull hpreNoDirty htxnLine htxnData hplan husedDirty hpreWF hstep' hcur htx
  | .recvGrantAtMaster =>
      right; exact (refMap_recvGrantAtMaster_eq hstep).symm
  | .recvGrantAckAtManager =>
      left; exact refMap_recvGrantAckAtManager_next hfull htxnLine htxnData hpreNoDirty husedDirty hpreWF hstep
  | .sendRelease param =>
      left; exact refMap_sendRelease_next (hdirtyEx := hnoDirty) hfull hstep
  | .sendReleaseData param =>
      left; exact refMap_sendReleaseData_next (hdirtyEx := hnoDirty) hfull hstep
  | .recvReleaseAtManager =>
      rcases hstep with ⟨msg, param, htxn, hgrant, hrel, hflight, hC, hsource, hwf, hparam, hperm, hD, hs'⟩
      have hstep' : RecvReleaseAtManager s s' i := ⟨msg, param, htxn, hgrant, hrel, hflight, hC, hsource, hwf, hparam, hperm, hD, hs'⟩
      -- Derive hCother: with currentTxn = none, other nodes' chanC must be none
      -- (probe case needs currentTxn = some; release case is the only option but
      -- the single-line model has at most one release in flight)
      have hCother : ∀ j : Fin n, j ≠ i → (s.locals j).chanC = none := by
        intro j hne
        exact (hrelUniq htxn).2 i j (Ne.symm hne) (by rw [hC]; simp)
      right; exact (refMap_recvReleaseAtManager_eq hfull hcleanRel hCother hstep').symm
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨msg, htxn, hgrant, hrel, hflight, hD, hmsg, hs'⟩
      have hstep' : RecvReleaseAckAtMaster s s' i := ⟨msg, htxn, hgrant, hrel, hflight, hD, hmsg, hs'⟩
      have hCnone : ∀ j : Fin n, (s.locals j).chanC = none :=
        chanC_none_of_releaseAck_pending hrelUniq htxn hrel
      left; exact refMap_recvReleaseAckAtMaster_next hfull hCnone hstep'
  | .store v =>
      rcases hstep with ⟨hcur, hgrant, hrel, hallC, hperm, hA, hB, hCi, hD, hE, hSrc, hFlight, hs'⟩
      rw [hs']
      left
      simp only [SymSharedSpec.toSpec, TileLink.Atomic.tlAtomic]
      refine ⟨i, .store v, ?_⟩
      have hqueuedNone : queuedReleaseIdx n s = none :=
        queuedReleaseIdx_eq_none_of_all_chanC_none s hallC
      let s'store : SymState HomeState NodeState n :=
        { shared := s.shared, locals := setFn s.locals i (storeLocal (s.locals i) v) }
      have hqueuedPost : queuedReleaseIdx n s'store = none := by
        apply queuedReleaseIdx_eq_none_of_all_chanC_none
        intro j
        show (s'store.locals j).chanC = none
        by_cases hji : j = i
        · subst j; simp [s'store, setFn, storeLocal, hCi]
        · simp [s'store, setFn, hji]; exact hallC j
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- pendingGrantMeta = none
        simp [refMap, refMapShared, hcur]
      · -- pendingGrantAck = none
        simp [refMap, refMapShared, hcur, hrel, hqueuedNone, hgrant]
      · -- pendingReleaseAck = none
        simp [refMap, refMapShared, hcur, hrel, hqueuedNone]
      · -- perm = .T
        simpa [refMap, refMapLine, hcur] using hperm
      · -- postcondition
        apply SymState.ext
        · -- shared: store updates mem to v via dirty-owner override
          refine TileLink.Atomic.HomeState.ext ?_ ?_ ?_ ?_ ?_
          · -- mem: dirty override gives v (unique dirty node i has data v)
            simp only [refMap, TileLink.Atomic.storeState, refMapShared, hcur, s'store]
            have hDirtyI : ((setFn s.locals i (storeLocal (s.locals i) v)) i).line.dirty =
                true := by simp [setFn, storeLocal]
            have hExDirty : ∃ j : Fin n,
                ((setFn s.locals i (storeLocal (s.locals i) v)) j).line.dirty = true :=
              ⟨i, hDirtyI⟩
            rw [dif_pos hExDirty]
            have hChooseI : Classical.choose hExDirty = i := by
              have hcd := Classical.choose_spec hExDirty
              by_contra hne
              have hSame : ((setFn s.locals i (storeLocal (s.locals i) v))
                  (Classical.choose hExDirty)).line =
                  (s.locals (Classical.choose hExDirty)).line := by simp [setFn, hne]
              rw [hSame] at hcd
              exact absurd ((hfull.1.1 (Classical.choose hExDirty)).1 hcd).1
                (by rw [hSwmr i _ (Ne.symm hne) hperm]; simp)
            rw [hChooseI]; simp [setFn, storeLocal]
          · -- dir: syncDir unchanged because perm .T → .T at i, others unchanged
            simp only [refMap, TileLink.Atomic.storeState, refMapShared, hcur, s'store]
            funext k
            by_cases hk : k < n
            · simp only [TileLink.Atomic.syncDir, hk, dite_true]
              by_cases hki : (⟨k, hk⟩ : Fin n) = i
              · subst hki; simp [setFn, storeLocal, hperm]
              · simp [setFn, hki]
            · simp [TileLink.Atomic.syncDir, hk]
          · -- pendingGrantMeta
            simp [refMap, refMapShared, hcur]
          · -- pendingGrantAck
            simp [refMap, refMapShared, hcur, hgrant]
          · -- pendingReleaseAck
            simp only [refMap, refMapShared, hcur, hrel]
            rw [hqueuedNone]; exact hqueuedPost
        · -- locals: refMapLine at each index
          funext j
          simp only [refMap, refMapLine, hcur, setFn]
          by_cases hji : j = i
          · subst j; simp [storeLocal, TileLink.Atomic.dirtyTipLine]
          · simp [hji]
  | .read =>
      right
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩
      rfl
  | .uncachedGet source =>
      right; exact (refMap_uncachedGet_eq hstep).symm
  | .uncachedPut source v =>
      left; exact refMap_uncachedPut_next hfull hstep
  | .recvUncachedAtManager =>
      right; exact (refMap_recvUncachedAtManager_eq hstep).symm
  | .recvAccessAckAtMaster =>
      right; exact (refMap_recvAccessAckAtMaster_eq hstep).symm

/-! ### Main Forward-Simulation Theorem -/

/-- The explicit message-level TileLink model refines the atomic wave-level model
    (with stuttering). Every behavior of the message model, mapped through `refMap`,
    is a behavior of the atomic model. -/
theorem messages_refines_atomic (n : Nat) :
    refines_via (refMap n) (tlMessages.toSpec n).safety
      (TileLink.Atomic.tlAtomic.toSpec n).safety_stutter := by
  apply refinement_mapping_stutter_with_invariant
  · intro s hinit; exact init_forwardSimInv n s hinit
  · intro s s' hinv hnext; exact forwardSimInv_preserved n s s' hinv hnext
  · intro s hinit; exact refMap_init n s hinit
  · intro s s' hinv hnext
    rcases forwardSim_step n s s' hinv hnext with hstep | heq
    · exact Or.inl hstep
    · exact Or.inr heq

end TileLink.Messages
