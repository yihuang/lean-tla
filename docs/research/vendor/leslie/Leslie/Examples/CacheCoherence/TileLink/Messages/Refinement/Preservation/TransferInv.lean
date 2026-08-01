import Leslie.Examples.CacheCoherence.TileLink.Messages.Refinement.Invariants
import Leslie.Gadgets.ActionCases

/-! ## Preservation of preLinesWFInv and txnTransferMemInv

    These are newer invariants added to support the txnDataInv Part 3 proof
    (transferVal = mem at grantReady after dirty probeAck processing).
    Extracted from the main Preservation.lean for context manageability. -/

namespace TileLink.Messages

open TLA TileLink SymShared Classical

theorem preLinesWFInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hfull : fullInv n s) (hpreWF : preLinesWFInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    preLinesWFInv n s' := by
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  match a with
  | .sendAcquireBlock _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩; rw [hs']; exact hpreWF
  | .sendAcquirePerm _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩; rw [hs']; exact hpreWF
  | .recvAcquireAtManager =>
      rcases hstep with hblk | hperm
      · rcases hblk with ⟨grow, source, _, _, _, _, _, _, _, _, _, _, hs'⟩
        rw [hs']
        simp only [preLinesWFInv, recvAcquireState, recvAcquireShared]
        intro k hk
        rcases hfull with ⟨⟨hlineWF, _, _, _⟩, _, _⟩
        simp [plannedTxn, hk]
        exact hlineWF ⟨k, hk⟩
      · rcases hperm with ⟨grow, source, _, _, _, _, _, _, _, _, _, hs'⟩
        rw [hs']
        simp only [preLinesWFInv, recvAcquireState, recvAcquireShared]
        intro k hk
        rcases hfull with ⟨⟨hlineWF, _, _, _⟩, _, _⟩
        simp [plannedTxn, hk]
        exact hlineWF ⟨k, hk⟩
  | .recvProbeAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, _, hs'⟩
      rcases hs' with ⟨_, hs'⟩; rw [hs']
      simpa [preLinesWFInv, hcur, recvProbeState] using hpreWF
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, hs'⟩; rw [hs']
      simpa [preLinesWFInv, hcur, recvProbeAckState, recvProbeAckShared] using hpreWF
  | .sendGrantToRequester =>
      rcases hstep with ⟨tx, hcur, _, _, _, _, _, _, _, hs'⟩; rw [hs']
      simpa [preLinesWFInv, hcur, sendGrantState, sendGrantShared] using hpreWF
  | .recvGrantAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, _, _, hs'⟩; rw [hs']
      simpa [preLinesWFInv, hcur, recvGrantState, recvGrantShared] using hpreWF
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨tx, msg, _, _, _, _, _, _, _, _, hs'⟩; rw [hs']
      simp [preLinesWFInv, recvGrantAckState, recvGrantAckShared]
  | .sendRelease _ =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      subst hs'; simp [preLinesWFInv, hcur, sendReleaseState]
  | .sendReleaseData _ =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      subst hs'; simp [preLinesWFInv, hcur, sendReleaseState]
  | .recvReleaseAtManager =>
      rcases hstep with ⟨msg, param, hcur, _, _, _, _, _, _, _, _, _, hs'⟩
      subst hs'; simp [preLinesWFInv, hcur, recvReleaseState, recvReleaseShared]
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨msg, hcur, _, _, _, _, _, hs'⟩; rw [hs']
      simp [preLinesWFInv, hcur, recvReleaseAckState, recvReleaseAckShared]
  | .store v =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      simp [preLinesWFInv, hcur]
  | .read =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩; exact hpreWF
  | .uncachedGet source =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, rfl⟩
      simp [preLinesWFInv, hcur]
  | .uncachedPut source v =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, rfl⟩
      simp [preLinesWFInv, hcur]
  | .recvUncachedAtManager =>
      rcases hstep with ⟨hcur, _, _, _, _, _, rfl⟩
      simp [preLinesWFInv, hcur]
  | .recvAccessAckAtMaster =>
      rcases hstep with ⟨_, _, _, rfl⟩; exact hpreWF

theorem txnTransferMemInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hfull : fullInv n s) (htxnData : txnDataInv n s)
    (hpreNoDirty : preLinesNoDirtyInv n s) (husedDirty : usedDirtySourceInv n s)
    (hdirtyOwner : dirtyOwnerExistsInv n s) (hpreWF : preLinesWFInv n s)
    (htxnTM : txnTransferMemInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    txnTransferMemInv n s' := by
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  match a with
  | .sendAcquireBlock _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩; rw [hs']; exact htxnTM
  | .sendAcquirePerm _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩; rw [hs']; exact htxnTM
  | .recvAcquireAtManager =>
      -- New transaction: at init probesRemaining = probesNeeded.
      -- Dirty nodes have probesNeeded = true (from lineWFInv → perm .T → in mask).
      -- So the "all dirty processed" premise (remaining = false) is contradicted.
      rcases hstep with hblk | hperm
      · rcases hblk with ⟨grow, source, htxn, _, _, _, _, _, _, _, hresult, _, hs'⟩
        rw [hs']
        simp only [txnTransferMemInv, recvAcquireState, recvAcquireShared]
        intro huds hall
        exfalso
        by_cases hex : ∃ j : Fin n, j ≠ i ∧ (s.locals j).line.dirty = true
        · have hk := Classical.choose_spec hex
          let k := Classical.choose hex
          rcases hfull with ⟨⟨hlineWF, _, _, _⟩, _, _⟩
          have hpermT := (hlineWF k).1 hk.2 |>.1
          have hk_dirty_pre : ((plannedTxn s i .acquireBlock grow source).preLines k.1).dirty = true := by
            simp [plannedTxn, k.is_lt]; exact hk.2
          have hrem := hall k.1 k.is_lt hk_dirty_pre
          -- grow.result ∈ {.B, .T} from action precondition
          have hresultBT : grow.result = .B ∨ grow.result = .T := by
            rcases hresult with ⟨_, hr⟩ | ⟨_, _, hr⟩ | ⟨_, hr⟩
            · exact Or.inl hr
            · exact Or.inl hr
            · exact Or.inr hr
          -- At init, probesRemaining = probeMask; show mask(k) = true → contradiction
          have hmask : ∀ hr : grow.result = .B ∨ grow.result = .T,
              (probeMaskForResult s i grow.result) k.1 = true := by
            intro hr
            rcases hr with hr | hr <;> simp [probeMaskForResult, hr, writableProbeMask,
              cachedProbeMask, k.is_lt, dite_true, show (⟨k.1, k.is_lt⟩ : Fin n) = k from rfl,
              show k ≠ i from hk.1, hpermT]
          have hrem_eq : (plannedTxn s i .acquireBlock grow source).probesRemaining k.1 =
              (probeMaskForResult s i grow.result) k.1 := by
            simp [plannedTxn]
          rw [hrem_eq, hmask hresultBT] at hrem
          exact absurd hrem (by decide)
        · -- No dirty owner → usedDirtySource should be false → contradiction
          -- hex : ¬∃ j, j ≠ i ∧ dirty j → dirtyOwnerOpt = none → usedDirtySource = false
          exfalso; revert huds; simp [plannedTxn, plannedUsedDirtySource, dirtyOwnerOpt, dif_neg hex]
      · rcases hperm with ⟨grow, source, htxn, _, _, _, _, _, _, hresultT, _, hs'⟩
        rw [hs']
        simp only [txnTransferMemInv, recvAcquireState, recvAcquireShared]
        intro huds hall
        exfalso
        by_cases hex : ∃ j : Fin n, j ≠ i ∧ (s.locals j).line.dirty = true
        · have hk := Classical.choose_spec hex
          let k := Classical.choose hex
          rcases hfull with ⟨⟨hlineWF, _, _, _⟩, _, _⟩
          have hpermT := (hlineWF k).1 hk.2 |>.1
          have hk_dirty_pre : ((plannedTxn s i .acquirePerm grow source).preLines k.1).dirty = true := by
            simp [plannedTxn, k.is_lt]; exact hk.2
          have hrem := hall k.1 k.is_lt hk_dirty_pre
          -- grow.result = .T → cachedProbeMask includes k (perm .T ≠ .N) → true = false
          have hmask : (probeMaskForResult s i grow.result) k.1 = true := by
            simp [probeMaskForResult, hresultT, cachedProbeMask, k.is_lt, dite_true,
              show (⟨k.1, k.is_lt⟩ : Fin n) = k from rfl, show k ≠ i from hk.1, hpermT]
          have hrem_eq : (plannedTxn s i .acquirePerm grow source).probesRemaining k.1 =
              (probeMaskForResult s i grow.result) k.1 := by
            simp [plannedTxn]
          rw [hrem_eq, hmask] at hrem
          exact absurd hrem (by decide)
        · exfalso; revert huds; simp [plannedTxn, plannedUsedDirtySource, dirtyOwnerOpt, dif_neg hex]
  | .recvProbeAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, _, hs'⟩
      rcases hs' with ⟨_, hs'⟩; rw [hs']
      simpa [txnTransferMemInv, hcur, recvProbeState] using htxnTM
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨tx, msg, hcur, hphase, hrem, _, hC, _, _, hs'⟩
      rw [hs']
      -- From chanCInv: msg.data = probeAckDataOfLine (tx.preLines i.1)
      rcases hfull with ⟨⟨_, _, _, _⟩, ⟨_, _, hchanC, _, _⟩, _⟩
      specialize hchanC i; rw [hC] at hchanC
      rcases hchanC with ⟨tx', hcur', _, _, _, _, _, _, hdata⟩ | ⟨_, hcurNone, _⟩
      · rw [hcur] at hcur'; cases hcur'
        cases hdirtyI : (tx.preLines i.1).dirty
        · -- Clean probeAck: msg.data = none → transferVal and mem unchanged
          have hmsg : msg.data = none := by simp [hdata, probeAckDataOfLine, hdirtyI]
          simp only [txnTransferMemInv, recvProbeAckState, recvProbeAckShared, hmsg,
            Option.isSome, Bool.or_false]
          simp only [txnTransferMemInv, hcur] at htxnTM
          intro huds hall
          apply htxnTM huds
          intro k hk hdirty
          have hki : k ≠ i.1 := by
            intro heq; rw [heq] at hdirty; rw [hdirtyI] at hdirty; cases hdirty
          have := hall k hk hdirty
          simp [clearProbeIdx, hki] at this
          exact this
        · -- Dirty probeAck: msg.data = some data → both transferVal and mem set to same value
          have hmsg : msg.data = some (tx.preLines i.1).data := by
            simp [hdata, probeAckDataOfLine, hdirtyI]
          simp only [txnTransferMemInv, recvProbeAckState, recvProbeAckShared, hmsg,
            Option.isSome, Bool.or_true]
          intro huds _
          obtain ⟨k, hk, _, hk_dirty, htv⟩ := hdirtyOwner tx hcur huds
          have hpreWF' : ∀ k : Nat, k < n → (tx.preLines k).WellFormed := by
            simpa [preLinesWFInv, hcur] using hpreWF
          have hpreNoDirty' : ∀ k1 k2 : Nat, k1 < n → k2 < n → k1 ≠ k2 →
              (tx.preLines k1).dirty = true → (tx.preLines k2).perm = .N := by
            simpa [preLinesNoDirtyInv, hcur] using hpreNoDirty
          by_cases hki : k = i.1
          · rw [hki] at htv; exact htv
          · exfalso
            have hwf_k := hpreWF' k hk
            have hpermT_k := hwf_k.1 hk_dirty |>.1
            have hpermN_k := hpreNoDirty' i.1 k i.is_lt hk (Ne.symm hki) hdirtyI
            rw [hpermT_k] at hpermN_k; cases hpermN_k
      · rw [hcur] at hcurNone; simp at hcurNone
  | .sendGrantToRequester =>
      rcases hstep with ⟨tx, hcur, _, _, _, _, _, _, _, hs'⟩; rw [hs']
      simpa [txnTransferMemInv, hcur, sendGrantState, sendGrantShared] using htxnTM
  | .recvGrantAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, _, _, hs'⟩; rw [hs']
      simpa [txnTransferMemInv, hcur, recvGrantState, recvGrantShared] using htxnTM
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨tx, msg, _, _, _, _, _, _, _, _, hs'⟩; rw [hs']
      simp [txnTransferMemInv, recvGrantAckState, recvGrantAckShared]
  | .sendRelease _ =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      subst hs'; simp [txnTransferMemInv, hcur, sendReleaseState]
  | .sendReleaseData _ =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      subst hs'; simp [txnTransferMemInv, hcur, sendReleaseState]
  | .recvReleaseAtManager =>
      rcases hstep with ⟨msg, param, hcur, _, _, _, _, _, _, _, _, _, hs'⟩
      subst hs'; simp [txnTransferMemInv, hcur, recvReleaseState, recvReleaseShared]
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨msg, hcur, _, _, _, _, _, hs'⟩; rw [hs']
      simp [txnTransferMemInv, hcur, recvReleaseAckState, recvReleaseAckShared]
  | .store v =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      simp [txnTransferMemInv, hcur]
  | .read =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩; exact htxnTM
  | .uncachedGet source =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, rfl⟩
      simp [txnTransferMemInv, hcur]
  | .uncachedPut source v =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, rfl⟩
      simp [txnTransferMemInv, hcur]
  | .recvUncachedAtManager =>
      rcases hstep with ⟨hcur, _, _, _, _, _, rfl⟩
      simp [txnTransferMemInv, hcur]
  | .recvAccessAckAtMaster =>
      rcases hstep with ⟨_, _, _, rfl⟩; exact htxnTM

theorem releaseDataInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hfull : fullInv n s) (hdata : dataCoherenceInv n s)
    (hrelData : releaseDataInv n s)
    (hrelDCC : releaseDataChanCInv n s)
    (htxnNoRel : txnNoReleaseInv n s)
    (hdirtyRelEx : dirtyReleaseExclusiveInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    releaseDataInv n s' := by
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  match a with
  | .sendAcquireBlock _ _ =>
      rcases hstep with ⟨htxn, _, _, _, _, _, _, rfl⟩
      intro htxn' j hflight hperm hdirty
      simp only [setFn] at *
      by_cases hji : j = i <;> simp_all [releaseDataInv]
  | .sendAcquirePerm _ _ =>
      rcases hstep with ⟨htxn, _, _, _, _, _, _, rfl⟩
      intro htxn' j hflight hperm hdirty
      simp only [setFn] at *
      by_cases hji : j = i <;> simp_all [releaseDataInv]
  | .recvAcquireAtManager =>
      -- currentTxn → some → guard false
      rcases hstep with hblk | hperm
      · rcases hblk with ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
        intro htxn'; simp [recvAcquireState, recvAcquireShared] at htxn'
      · rcases hperm with ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩
        intro htxn'; simp [recvAcquireState, recvAcquireShared] at htxn'
  | .recvProbeAtMaster =>
      rcases hstep with ⟨tx, _, hcur, _, _, _, _, _, _, _, ⟨_, rfl⟩⟩
      intro htxn'; simp [recvProbeState, hcur] at htxn'
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨tx, _, hcur, _, _, _, _, _, _, rfl⟩
      intro htxn'; simp [recvProbeAckState, recvProbeAckShared, hcur] at htxn'
  | .sendGrantToRequester =>
      rcases hstep with ⟨tx, hcur, _, _, _, _, _, _, _, rfl⟩
      intro htxn'; simp [sendGrantState, sendGrantShared, hcur] at htxn'
  | .recvGrantAtMaster =>
      rcases hstep with ⟨tx, _, hcur, _, _, _, _, _, _, _, _, rfl⟩
      intro htxn'; simp [recvGrantState, recvGrantShared, hcur] at htxn'
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨tx, _, hcur, _, _, _, _, _, _, _, rfl⟩
      -- currentTxn was some → all releaseInFlight = false (txnNoReleaseInv)
      intro _ j hflight _hCclean _hperm _hdirty
      have hnoRel := htxnNoRel (by rw [hcur]; simp) j
      simp only [recvGrantAckState, recvGrantAckLocals, setFn] at hflight
      by_cases hji : j = i
      · subst hji; simp_all [recvGrantAckLocal]
      · simp_all
  | .sendRelease param =>
      -- Clean release: chanC has clean msg (data = none), guard holds. Use dataCoherenceInv.
      rcases hstep with ⟨htxn, _, _, _, _, _, _, _, _, _, _, hflight_pre, hlegal, hdirty_pre, _, hs'⟩
      subst hs'
      intro htxn' j hflight hCclean hperm hdirty
      by_cases hji : j = i
      · -- Node i: releasedLine preserves data. dataCoherenceInv pre → data = mem.
        rw [hji] at hperm hdirty ⊢
        simp only [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, ite_true] at hperm hdirty ⊢
        -- Eliminate param.result = .N case: post-perm = .N → hperm contradiction
        -- For .B/.T: data = line.data = mem from dataCoherenceInv
        -- For each param case: either derive perm ≠ .N (and use dataCoherenceInv) or
        -- show post-state perm = .N (contradicting hperm → vacuous)
        cases param with
        | TtoB | TtoN | BtoN | TtoT | BtoB =>
          have hperm_pre : (s.locals i).line.perm ≠ .N := by
            rw [PruneReportParam.legalFrom] at hlegal; rw [hlegal]; simp [PruneReportParam.source]
          have hmem := hdata htxn i hflight_pre hperm_pre hdirty_pre
          cases h : PruneReportParam.result _ <;>
            simp_all [releasedLine, invalidatedLine, branchAfterProbe, tipAfterProbe, PruneReportParam.result]
        | NtoN =>
          exfalso; simp [PruneReportParam.result, releasedLine, invalidatedLine] at hperm
      · simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] at hflight hCclean hperm hdirty ⊢
        exact hrelData htxn j hflight hCclean hperm hdirty
  | .sendReleaseData param =>
      -- Dirty release: chanC has dirty msg (data ≠ none) → hCclean gives contradiction for node i
      rcases hstep with ⟨htxn, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      subst hs'
      intro htxn' j hflight hCclean hperm hdirty
      by_cases hji : j = i
      · subst hji
        -- sendReleaseData: chanC = some (releaseMsg ... true). msg.data = some line.data ≠ none.
        -- hCclean says ∀ msg, chanC = some msg → msg.data = none. Apply to the release msg.
        exfalso
        simp only [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, ite_true] at hCclean
        have := hCclean _ rfl
        simp [releaseMsg, releaseDataPayload] at this
      · simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] at hflight hCclean hperm hdirty ⊢
        exact hrelData htxn j hflight hCclean hperm hdirty
  | .recvReleaseAtManager =>
      -- chanC cleared for node i; mem may change via releaseWriteback
      rcases hstep with ⟨msg, param, htxn, _, _, hflight_i, hCi, _, _, _, _, _, hs'⟩
      subst hs'
      intro htxn' j hflight hCnone hperm hdirty
      simp [recvReleaseState, recvReleaseShared] at htxn'
      by_cases hji : j = i
      · -- Node i: chanC cleared, mem = releaseWriteback old_mem msg
        rw [hji] at hflight hCnone hperm hdirty ⊢
        simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn] at hflight hCnone hperm hdirty ⊢
        simp only [recvReleaseShared, releaseWriteback]
        cases hmsg : msg.data with
        | none =>
          simp [hmsg]
          have hCclean : ∀ m : CMsg, (s.locals i).chanC = some m → m.data = none := by
            intro m hm; rw [hCi] at hm; cases hm; exact hmsg
          exact hrelData htxn i hflight_i hCclean hperm hdirty
        | some v =>
          simp [hmsg]
          have hrel_data := hrelDCC i hflight_i msg hCi (by rw [hmsg]; simp)
          rw [hmsg] at hrel_data; cases hrel_data; rfl
      · -- Node j ≠ i: mem changed, need data j = new mem
        simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn, hji] at hflight hCnone hperm hdirty ⊢
        -- So at recvRelease(i) time, pendingReleaseAck = none → j's recvRelease already acked.
        -- But wait, recvRelease sets pendingReleaseAck = some j. And recvReleaseAck clears it.
        -- So at recvRelease(i): pendingReleaseAck = none → j's full cycle completed → releaseInFlight(j) = false.
        -- Contradiction with hflight. But we need this formally.
        -- mem may change via releaseWriteback. Case split on msg.data.
        simp only [recvReleaseShared, releaseWriteback]
        cases hmsg : msg.data with
        | none =>
          -- Clean release from i: mem unchanged → use pre-state
          simp [hmsg]; exact hrelData htxn j hflight hCnone hperm hdirty
        | some v =>
          -- Dirty release from i: new mem = v. j has perm ≠ .N.
          -- But dirtyReleaseExclusiveInv: dirty release from i → all j ≠ i have perm .N.
          -- Contradiction with hperm (perm ≠ .N).
          exfalso
          rcases hfull with ⟨_, ⟨_, _, _, _, _⟩, _⟩
          have hDirtyRel : ∃ msg' : CMsg, (s.locals i).chanC = some msg' ∧ msg'.data ≠ none :=
            ⟨msg, hCi, by rw [hmsg]; simp⟩
          exact hperm (hdirtyRelEx htxn i hflight_i hDirtyRel j (fun h => hji h))
  | .recvReleaseAckAtMaster =>
      -- Node i: releaseInFlight cleared → guard false. Others: unchanged.
      rcases hstep with ⟨msg, htxn, _, _, hflight_i, _, _, hs'⟩
      subst hs'
      intro htxn' j hflight hCnone hperm hdirty
      simp [recvReleaseAckState, recvReleaseAckShared] at htxn'
      by_cases hji : j = i
      · subst hji
        simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn] at hflight
      · simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn, hji] at hflight hCnone hperm hdirty ⊢
        exact hrelData htxn j hflight hCnone hperm hdirty
  | .store v =>
      rcases hstep with ⟨htxn, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      intro htxn' j hflight hCnone hperm hdirty
      simp only [setFn] at *
      by_cases hji : j = i <;> simp_all [releaseDataInv, storeLocal]
  | .read =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩; exact hrelData
  | .uncachedGet source =>
      rcases hstep with ⟨htxn, _, _, _, _, _, _, _, _, _, rfl⟩
      intro htxn' j hflight hCnone hperm hdirty
      -- chanA/pendingSource changed at node i; line/releaseInFlight/chanC/mem unchanged
      -- For j = i: line unchanged → use pre-state. For j ≠ i: everything unchanged.
      exact hrelData htxn j (by simp only [setFn] at hflight; split at hflight <;> simp_all)
        (by intro msg hC; simp only [setFn] at hC; split at hC <;> simp_all [hCnone])
        (by simp only [setFn] at hperm; split at hperm <;> simp_all)
        (by simp only [setFn] at hdirty; split at hdirty <;> simp_all)
  | .uncachedPut source v =>
      rcases hstep with ⟨htxn, _, _, hpermAll, _, _, _, _, _, _, _, rfl⟩
      intro htxn' j hflight hCnone hperm hdirty
      -- All perm = .N → hperm (perm ≠ .N) fails
      exfalso; exact hperm (by simp only [setFn] at hperm ⊢; split at hperm ⊢ <;> simp_all [hpermAll])
  | .recvUncachedAtManager =>
      rcases hstep with ⟨htxn, _, _, _, _, _, rfl⟩
      intro htxn' j hflight hCnone hperm hdirty
      exact hrelData htxn j (by simp only [setFn] at hflight; split at hflight <;> simp_all)
        (by intro msg hC; simp only [setFn] at hC; split at hC <;> simp_all [hCnone])
        (by simp only [setFn] at hperm; split at hperm <;> simp_all)
        (by simp only [setFn] at hdirty; split at hdirty <;> simp_all)
  | .recvAccessAckAtMaster =>
      -- shared unchanged, chanD/pendingSource cleared, line/releaseInFlight/chanC unchanged
      rcases hstep with ⟨_, _, _, rfl⟩
      intro htxn' j hflight hCnone hperm hdirty
      simp only [setFn] at hflight hCnone hperm hdirty ⊢
      by_cases hji : j = i
      · simp_all; exact hrelData htxn' j hflight hCnone hperm hdirty
      · simp_all; exact hrelData htxn' j hflight hCnone hperm hdirty

theorem releaseDataChanCInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hfull : fullInv n s) (hrelDCC : releaseDataChanCInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    releaseDataChanCInv n s' := by
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  match a with
  | .sendAcquireBlock _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, rfl⟩
      intro j hflight msg hC hdata
      simp only [setFn] at hflight hC ⊢
      by_cases hji : j = i <;> simp_all
  | .sendAcquirePerm _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, rfl⟩
      intro j hflight msg hC hdata
      simp only [setFn] at hflight hC ⊢
      by_cases hji : j = i <;> simp_all
  | .recvAcquireAtManager =>
      rcases hstep with hblk | hperm
      · rcases hblk with ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
        intro j hflight msg hC
        simp [recvAcquireState, recvAcquireLocals, setFn] at hflight hC ⊢
        by_cases hji : j = i <;> simp_all
      · rcases hperm with ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩
        intro j hflight msg hC
        simp [recvAcquireState, recvAcquireLocals, setFn] at hflight hC ⊢
        by_cases hji : j = i <;> simp_all
  | .recvProbeAtMaster =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, ⟨_, rfl⟩⟩
      intro j hflight msg hC hdata
      simp [recvProbeState, recvProbeLocals, setFn] at hflight hC ⊢
      by_cases hji : j = i <;> simp_all [recvProbeLocal]
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
      intro j hflight msg hC hdata
      simp [recvProbeAckState, recvProbeAckLocals, setFn] at hflight hC ⊢
      by_cases hji : j = i <;> simp_all [recvProbeAckLocal]
  | .sendGrantToRequester =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
      intro j hflight msg hC hdata
      simp [sendGrantState, sendGrantLocals, setFn] at hflight hC ⊢
      by_cases hji : j = i <;> simp_all [sendGrantLocal]
  | .recvGrantAtMaster =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩
      intro j hflight msg hC hdata
      simp [recvGrantState, recvGrantLocals, setFn] at hflight hC ⊢
      by_cases hji : j = i <;> simp_all [recvGrantLocal]
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
      intro j hflight msg hC hdata
      simp [recvGrantAckState, recvGrantAckLocals, setFn] at hflight hC ⊢
      by_cases hji : j = i <;> simp_all [recvGrantAckLocal]
  | .sendRelease param =>
      -- KEY: sendReleaseLocal sets chanC := releaseMsg and line := releasedLine.
      -- releaseDataPayload preserves relationship: msg.data = some line.data for dirty.
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      subst hs'
      intro j hflight msg hC hdata
      by_cases hji : j = i
      · subst hji
        simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn] at hflight hC hdata ⊢
        subst hC -- msg = releaseMsg ...
        simp [releaseMsg, releaseDataPayload] at hdata ⊢
        -- withData = false for sendRelease → data = none → contradicts hdata
        simp at hdata
      · simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] at hflight hC hdata ⊢
        exact hrelDCC j hflight msg hC hdata
  | .sendReleaseData param =>
      -- KEY: sendReleaseLocal sets chanC := releaseMsg with data = some line.data.
      -- And line := releasedLine which preserves data.
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      subst hs'
      intro j hflight msg hC hdata
      by_cases hji : j = i
      · subst hji
        simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn] at hflight hC hdata ⊢
        subst hC
        -- msg = releaseMsg i param true (s.locals i).line
        -- msg.data = releaseDataPayload (s.locals i).line true = some (s.locals i).line.data
        -- releasedLine preserves data for all param results
        simp [releaseMsg, releaseDataPayload, releasedLine]
        cases param.result <;> simp [invalidatedLine, branchAfterProbe, tipAfterProbe]
      · simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] at hflight hC hdata ⊢
        exact hrelDCC j hflight msg hC hdata
  | .recvReleaseAtManager =>
      -- chanC cleared for node i → chanC i = none → condition vacuous for i
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      subst hs'
      intro j hflight msg hC hdata
      by_cases hji : j = i
      · subst hji; simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn] at hC
      · simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn, hji] at hflight hC hdata ⊢
        exact hrelDCC j hflight msg hC hdata
  | .recvReleaseAckAtMaster =>
      -- releaseInFlight cleared for node i; chanC unchanged
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      subst hs'
      intro j hflight msg hC hdata
      by_cases hji : j = i
      · subst hji; simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn] at hflight
      · simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn, hji] at hflight hC hdata ⊢
        exact hrelDCC j hflight msg hC hdata
  | .store v =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      intro j hflight msg hC hdata
      simp only [setFn] at hflight hC hdata ⊢
      by_cases hji : j = i <;> simp_all [storeLocal]
  | .read =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩; exact hrelDCC
  | .uncachedGet source =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
      intro j hflight msg hC hdata
      simp only [setFn] at hflight hC hdata ⊢
      by_cases hji : j = i <;> simp_all
  | .uncachedPut source v =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩
      intro j hflight msg hC hdata
      simp only [setFn] at hflight hC hdata ⊢
      by_cases hji : j = i <;> simp_all
  | .recvUncachedAtManager =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩
      intro j hflight msg hC hdata
      simp only [setFn] at hflight hC hdata ⊢
      by_cases hji : j = i <;> simp_all
  | .recvAccessAckAtMaster =>
      rcases hstep with ⟨_, _, _, rfl⟩
      intro j hflight msg hC hdata
      simp only [setFn] at hflight hC hdata ⊢
      by_cases hji : j = i <;> simp_all

theorem txnNoReleaseInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hfull : fullInv n s) (htxnNoRel : txnNoReleaseInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    txnNoReleaseInv n s' := by
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  match a with
  | .sendAcquireBlock _ _ =>
      rcases hstep with ⟨htxn, _, _, _, _, _, _, rfl⟩
      intro hcur j; simp only [setFn]; split <;> simp_all [txnNoReleaseInv]
  | .sendAcquirePerm _ _ =>
      rcases hstep with ⟨htxn, _, _, _, _, _, _, rfl⟩
      intro hcur j; simp only [setFn]; split <;> simp_all [txnNoReleaseInv]
  | .recvAcquireAtManager =>
      -- currentTxn → some; precondition: ∀ j, releaseInFlight j = false
      rcases hstep with hblk | hperm
      · rcases hblk with ⟨_, _, _, _, _, hnoFlight, _, _, _, _, _, _, rfl⟩
        intro _ j; simp [recvAcquireState, recvAcquireLocals, setFn]
        split <;> simp_all
      · rcases hperm with ⟨_, _, _, _, _, _, hnoFlight, _, _, _, _, rfl⟩
        intro _ j; simp [recvAcquireState, recvAcquireLocals, setFn]
        split <;> simp_all
  | .recvProbeAtMaster =>
      rcases hstep with ⟨_, _, hcur, _, _, _, _, _, _, _, ⟨_, rfl⟩⟩
      intro _ j; simp [recvProbeState, recvProbeLocals, setFn]
      split <;> simp_all [recvProbeLocal, txnNoReleaseInv, hcur]
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨_, _, hcur, _, _, _, _, _, _, rfl⟩
      intro _ j; simp [recvProbeAckState, recvProbeAckLocals, setFn]
      split <;> simp_all [recvProbeAckLocal, txnNoReleaseInv, hcur]
  | .sendGrantToRequester =>
      rcases hstep with ⟨_, hcur, _, _, _, _, _, _, _, rfl⟩
      intro _ j; simp [sendGrantState, sendGrantLocals, setFn]
      split <;> simp_all [sendGrantLocal, txnNoReleaseInv, hcur]
  | .recvGrantAtMaster =>
      rcases hstep with ⟨_, _, hcur, _, _, _, _, _, _, _, _, rfl⟩
      intro _ j; simp [recvGrantState, recvGrantLocals, setFn]
      split <;> simp_all [recvGrantLocal, txnNoReleaseInv, hcur]
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
      -- currentTxn → none → guard false
      intro hcur; simp [recvGrantAckState, recvGrantAckShared] at hcur
  | .sendRelease param =>
      -- sendRelease requires currentTxn = none → post has currentTxn = none → guard false
      rcases hstep with ⟨htxn, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      subst hs'; simp [sendReleaseState, txnNoReleaseInv, htxn]
  | .sendReleaseData param =>
      rcases hstep with ⟨htxn, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      subst hs'; simp [sendReleaseState, txnNoReleaseInv, htxn]
  | .recvReleaseAtManager =>
      rcases hstep with ⟨_, _, htxn, _, _, _, _, _, _, _, _, _, hs'⟩
      subst hs'; intro hcur; simp [recvReleaseState, recvReleaseShared, htxn] at hcur
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨_, htxn, _, _, _, _, _, hs'⟩
      subst hs'; simp [recvReleaseAckState, recvReleaseAckShared, txnNoReleaseInv, htxn]
  | .store v =>
      rcases hstep with ⟨htxn, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
      intro hcur; simp [htxn] at hcur
  | .read =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩; exact htxnNoRel
  | .uncachedGet source =>
      rcases hstep with ⟨htxn, _, _, _, _, _, _, _, _, _, rfl⟩
      intro hcur; simp [htxn] at hcur
  | .uncachedPut source v =>
      rcases hstep with ⟨htxn, _, _, _, _, _, _, _, _, _, _, rfl⟩
      intro hcur; simp [htxn] at hcur
  | .recvUncachedAtManager =>
      rcases hstep with ⟨htxn, _, _, _, _, _, rfl⟩
      intro hcur; simp [htxn] at hcur
  | .recvAccessAckAtMaster =>
      rcases hstep with ⟨_, _, _, rfl⟩; exact htxnNoRel

end TileLink.Messages
