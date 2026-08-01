import Leslie.Examples.CacheCoherence.TileLink.Messages.Refinement.SimAcquire

namespace TileLink.Messages

open TLA TileLink SymShared Classical

theorem refMap_recvProbeAtMaster_eq {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n}
    (hstep : RecvProbeAtMaster s s' i) :
    refMap n s' = refMap n s := by
  rcases hstep with ⟨tx, msg, hcur, hphase, _, _, _, _, _, _, _, hs'⟩
  rw [hs']
  apply SymState.ext
  · simp [refMap, refMapShared, recvProbeState, hcur, hphase]
  · funext j
    have hcur' : (recvProbeState s i msg).shared.currentTxn = some tx := by
      simp [recvProbeState, hcur]
    simp [refMap, refMapLine, recvProbeState, hcur, hcur', hphase]

private theorem recvProbeAckAtManager_mem_eq {n : Nat}
    {s : SymState HomeState NodeState n}
    {i : Fin n} {tx : ManagerTxn} {msg : CMsg}
    (hfull : fullInv n s)
    (htxnData : txnDataInv n s) (hpreNoDirty : preLinesNoDirtyInv n s)
    (husedDirty : usedDirtySourceInv n s)
    (hcur : s.shared.currentTxn = some tx)
    (hphase : tx.phase = .probing)
    (hremaining : tx.probesRemaining i.1 = true)
    (hCi : (s.locals i).chanC = some msg)
    (hwf : probeAckMsgWellFormed msg) :
    (if tx.usedDirtySource = true then tx.transferVal
     else match msg.data with | some v => v | none => s.shared.mem) =
    (if tx.usedDirtySource = true then tx.transferVal else s.shared.mem) := by
  by_cases hused : tx.usedDirtySource = true
  · simp [hused]
  · simp [hused]
    -- Extract chanCInv from fullInv
    rcases hfull with ⟨⟨_, _, _, htxnCore⟩, ⟨_, _, hchanC, _, _⟩, _⟩
    have hCdata := hchanC i
    rw [hCi] at hCdata
    rcases hCdata with ⟨tx', hcur', _, _, _, _, _, _, hdata⟩ | ⟨_, htxnNone, _⟩
    · rw [hcur] at hcur'; cases hcur'
      rw [hdata]
      simp [probeAckDataOfLine]
      split
      · -- (tx.preLines i.1).dirty = true, usedDirtySource = false → contradiction
        next hdirtyPre =>
        -- Derive i ≠ requester from txnCoreInv
        rw [txnCoreInv, hcur] at htxnCore
        have hi_ne : i.1 ≠ tx.requester := by
          intro h
          have hneeded := htxnCore.2.2.2.2.2.1 i.1 hremaining
          rw [h] at hneeded; rw [htxnCore.2.2.2.2.1] at hneeded; simp at hneeded
        -- From usedDirtySourceInv
        simp only [Bool.not_eq_true] at hused
        have := husedDirty tx hcur hused i.1 i.isLt hi_ne
        rw [this] at hdirtyPre; simp at hdirtyPre
      · rfl
    · rw [hcur] at htxnNone; cases htxnNone

theorem refMap_recvProbeAckAtManager_eq {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n}
    (hfull : fullInv n s)
    (htxnData : txnDataInv n s) (hpreNoDirty : preLinesNoDirtyInv n s)
    (husedDirty : usedDirtySourceInv n s)
    (hstep : RecvProbeAckAtManager s s' i) :
    refMap n s' = refMap n s := by
  rcases hstep with ⟨tx, msg, hcur, hphase, hremaining, _, hCi, _, hwf, hs'⟩
  rw [hs']
  apply SymState.ext
  · -- refMapShared equality
    simp only [refMap, refMapShared, recvProbeAckState, recvProbeAckShared, recvProbeAckLocals]
    have hphase_not_gpa : (probeAckPhase (n := n) (clearProbeIdx tx.probesRemaining i.1)) ≠ .grantPendingAck := by
      simp [probeAckPhase]; split <;> simp
    have hphase_probing : tx.phase ≠ .grantPendingAck := by simp [hphase]
    simp only [hcur, hphase_probing, hphase_not_gpa, ite_false]
    simp only [Atomic.HomeState.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact recvProbeAckAtManager_mem_eq hfull htxnData hpreNoDirty husedDirty hcur hphase hremaining hCi hwf
    · funext k; simp [preTxnDir, hphase, updateDirAt]; split <;> simp_all; omega
    · simp [absPendingGrantMeta, absGrantKind, hphase_not_gpa, hphase_probing]
    · simp [recvProbeAckShared]
    · simp [recvProbeAckShared]
  · -- refMapLine equality
    funext j
    simp only [refMap, refMapLine, recvProbeAckState, recvProbeAckShared,
      recvProbeAckLocals, recvProbeAckLocal, setFn]
    have hphase_not_gpa : (probeAckPhase (n := n) (clearProbeIdx tx.probesRemaining i.1)) ≠ .grantPendingAck := by
      simp [probeAckPhase]; split <;> simp [TxnPhase.noConfusion]
    simp [hcur, hphase, hphase_not_gpa]

theorem refMap_recvGrantAtMaster_eq {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n}
    (hstep : RecvGrantAtMaster s s' i) :
    refMap n s' = refMap n s := by
  rcases hstep with ⟨tx, msg, hcur, hreq, hphase, hgrant, _, _, _, _, hrest⟩
  rcases hrest with ⟨_, hs'⟩
  rw [hs']
  apply SymState.ext
  · change refMapShared n (recvGrantState s i tx) = refMapShared n s
    simp [refMapShared, recvGrantState, recvGrantShared, hcur, hphase, hgrant]
    rw [grantPendingDir_updateDirAt_eq tx s.shared.dir i tx.resultPerm hreq]
  · funext j
    by_cases hji : j = i
    · subst j
      simp [refMap, refMapLine, recvGrantState, recvGrantShared, hcur, hphase, hreq]
    · have hreqj : tx.requester ≠ j.1 := by
        intro hreq'
        apply hji
        exact Fin.ext (by omega)
      simpa [refMap, refMapLine, recvGrantState, recvGrantShared, recvGrantLocals,
        recvGrantLocal, setFn, hcur, hphase, hreqj, hji]

theorem refMap_recvGrantAckAtManager_next {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n}
    (hfull : fullInv n s) (htxnLine : txnLineInv n s) (htxnData : txnDataInv n s)
    (hpreNoDirty : preLinesNoDirtyInv n s) (husedDirty : usedDirtySourceInv n s)
    (hpreWF : preLinesWFInv n s)
    (hstep : RecvGrantAckAtManager s s' i) :
    (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n s') := by
  rcases hstep with ⟨tx, msg, hcur, hreq, hphase, hpga, _, hEi, _, _, hs'⟩
  rw [hs']
  -- Extract invariants from fullInv
  rcases hfull with ⟨⟨hlineWF, hdirInv, hpending, htxnCore⟩, ⟨_, _, hchanC, hchanD, hchanE⟩, _⟩
  -- txnCoreInv gives us grantHasData → resultPerm and probesRemaining all false
  rw [txnCoreInv, hcur] at htxnCore
  have hreqLt := htxnCore.1
  have hnoData := htxnCore.2.2.2.1
  have hprobesNone := htxnCore.2.2.2.2.2.2.2 hphase
  -- pendingInv gives pendingReleaseAck = none
  rw [pendingInv, hcur] at hpending
  have hrelAck := hpending.1
  -- dirInv: dir j = line.perm j when chanC j = none
  -- chanCInv during grantPendingAck: all chanC = none
  have hallC : ∀ j : Fin n, (s.locals j).chanC = none := by
    intro j
    have hcj := hchanC j
    cases hcjv : (s.locals j).chanC with
    | none => rfl
    | some msg' =>
      rw [hcjv] at hcj
      rcases hcj with ⟨tx', hcur', hphase', _⟩ | ⟨_, htxnNone, _⟩
      · rw [hcur] at hcur'; cases hcur'; rw [hphase] at hphase'; cases hphase'
      · rw [hcur] at htxnNone; cases htxnNone
  -- recvGrantAckLocal only changes chanE and pendingSink; line is preserved
  have hline_preserved : ∀ j : Fin n,
      ((recvGrantAckLocals s i j)).line = (s.locals j).line := by
    intro j
    simp [recvGrantAckLocals, setFn]
    split <;> simp_all [recvGrantAckLocal]
  -- All chanC are none in the post-state too
  have hallC_post : ∀ j : Fin n, ((recvGrantAckState s i).locals j).chanC = none := by
    intro j
    simp [recvGrantAckState, recvGrantAckLocals, setFn]
    split <;> simp_all [recvGrantAckLocal]
  have hQRI_post := queuedReleaseIdx_eq_none_of_all_chanC_none (recvGrantAckState s i) hallC_post
  have hDRV_post := findDirtyReleaseVal_none_of_all_chanC_none' (recvGrantAckState s i) hallC_post
  -- txnLineInv: during grantPendingAck with chanE = some, line = grantLine
  rw [txnLineInv, hcur] at htxnLine
  -- At the requester: line = grantLine because chanE ≠ none
  have hreq_fin : (⟨tx.requester, hreqLt⟩ : Fin n) = i := by ext; simp [hreq]
  have hline_req : (s.locals i).line = grantLine (tx.preLines i.1) tx := by
    have := htxnLine i
    simp [txnSnapshotLine, hphase, hreq, hEi] at this
    exact this
  -- grantLine perm = resultPerm
  have hperm_req : (s.locals i).line.perm = tx.resultPerm := by
    rw [hline_req]
    exact grantLine_perm_eq_result _ _ hnoData
  -- Witness: atomic grantAck at node i
  show ∃ (j : Fin n) (a : TileLink.Atomic.Act),
    TileLink.Atomic.tlAtomic.step n j a (refMap n s) (refMap n (recvGrantAckState s i))
  refine ⟨i, .grantAck, ?_, ?_⟩
  · -- Precondition: (refMap n s).shared.pendingGrantAck = some i.1
    simp [refMap, refMapShared, hpga]
  · -- Post-state equality: refMap n (recvGrantAckState s i) = grantAckState (refMap n s)
    apply SymState.ext
    · -- shared equality
      show refMapShared n (recvGrantAckState s i) =
        { (refMapShared n s) with pendingGrantMeta := none, pendingGrantAck := none }
      have hcur_post : (recvGrantAckState s i).shared.currentTxn = none := by
        simp [recvGrantAckState, recvGrantAckShared]
      -- pendingGrantMeta
      have hpgm : (refMapShared n (recvGrantAckState s i)).pendingGrantMeta = none := by
        simp [refMapShared, recvGrantAckState, recvGrantAckShared]
      -- pendingGrantAck
      have hpga_post : (refMapShared n (recvGrantAckState s i)).pendingGrantAck = none := by
        simp [refMapShared, recvGrantAckState, recvGrantAckShared]
      -- pendingReleaseAck
      have hpra_post : (refMapShared n (recvGrantAckState s i)).pendingReleaseAck = none := by
        rw [refMapShared_pra_none_notxn (by simp [recvGrantAckState, recvGrantAckShared, hrelAck]) hcur_post]
        exact hQRI_post
      have hpra_pre : (refMapShared n s).pendingReleaseAck = none := by
        exact refMapShared_pra_none_txn hrelAck hcur
      -- dir equality: grantPendingDir = syncDir with post-state lines
      have hdir_post : (refMapShared n (recvGrantAckState s i)).dir =
          TileLink.Atomic.syncDir s.shared.dir
            (fun j => ((recvGrantAckState s i).locals j).line) := by
        simp [refMapShared, recvGrantAckState, recvGrantAckShared]
      have hdir_pre : (refMapShared n s).dir = grantPendingDir n tx s.shared.dir := by
        exact refMapShared_dir_gpa hcur hphase
      have hdir_eq : (refMapShared n (recvGrantAckState s i)).dir = (refMapShared n s).dir := by
        rw [hdir_post, hdir_pre]
        -- grantPendingDir = syncDir with lines
        funext k
        simp only [TileLink.Atomic.syncDir]
        split
        · -- k < n
          next hk =>
          simp only [recvGrantAckState] at *
          rw [hline_preserved ⟨k, hk⟩]
          simp only [grantPendingDir, show tx.requester < n from hreqLt, dite_true, updateDirAt]
          by_cases hki : k = tx.requester
          · simp [hki, hreq, hperm_req]
          · simp [hki]
            exact (hdirInv ⟨k, hk⟩ (hallC ⟨k, hk⟩)).symm
        · -- k ≥ n
          simp [grantPendingDir, show tx.requester < n from hreqLt, updateDirAt]
          intro hki; omega
      -- mem equality
      have hmem_post : (refMapShared n (recvGrantAckState s i)).mem =
          (refMapShared n s).mem := by
        rw [refMapShared_mem_recvGrantAck]
        rw [refMapShared_mem_some hcur]
        -- Show: no dirty owner in post-state ↔ usedDirtySource determines mem
        -- From txnLineInv: all lines are determined by the txn snapshot
        -- grantLine has dirty = false; probed lines have dirty = false; unprobed preLines may have dirty
        -- But during grantPendingAck, all probesRemaining = false
        -- Need to show the dite matches the if-then-else
        -- Case 1: there exists a dirty line in post-state
        by_cases hdirtyPost : ∃ j : Fin n, ((recvGrantAckState s i).locals j).line.dirty = true
        · rw [dif_pos hdirtyPost]
          -- Generalize choose to get j in the goal
          generalize hj_eq : Classical.choose hdirtyPost = j
          have hdj : ((recvGrantAckState s i).locals j).line.dirty = true :=
            hj_eq ▸ Classical.choose_spec hdirtyPost
          simp only [recvGrantAckState] at hdj
          rw [hline_preserved] at hdj
          -- j cannot be the requester (grantLine has dirty = false)
          have hj_ne_i : j ≠ i := by
            intro heq
            have hdj' : (s.locals i).line.dirty = true := heq ▸ hdj
            rw [hline_req] at hdj'
            revert hdj'; simp only [grantLine]
            split <;> (cases tx.resultPerm <;> simp [invalidatedLine])
          -- From txnLineInv, j's line = probeSnapshotLine tx (s.locals j) j
          have hlinej := htxnLine j
          simp [txnSnapshotLine, hphase, show tx.requester ≠ j.1 from by
            intro h; exact hj_ne_i (Fin.ext (by omega))] at hlinej
          rw [hlinej] at hdj
          -- probeSnapshotLine: since probesRemaining j = false...
          simp [probeSnapshotLine] at hdj
          split at hdj
          · -- probesNeeded j = true, probesRemaining j = false (since grantPendingAck)
            have := hprobesNone j
            revert hdj; simp_all [probedLine]
            cases probeCapOfResult tx.grow.result <;> simp [invalidatedLine, branchAfterProbe, tipAfterProbe]
          · -- probesNeeded j = false: line = preLines j
            rename_i hprobesNeeded_false
            have htd := by simpa [txnDataInv, hcur] using htxnData
            have htv := htd.2.2 (Or.inr hphase)
            have hdata : (s.locals j).line.data = (tx.preLines j.1).data := by
              rw [hlinej]; simp [probeSnapshotLine, hprobesNeeded_false]
            have husedDS : tx.usedDirtySource = true := by
              by_contra h
              have h' := Bool.eq_false_iff.mpr h
              have huds := by simpa [usedDirtySourceInv, hcur] using husedDirty
              have := huds h' j.1 j.is_lt (show j.1 ≠ tx.requester from by
                intro heq; exact hj_ne_i (Fin.ext (by omega)))
              rw [this] at hdj; cases hdj
            obtain ⟨k, hklt, hk_dirty, htv_k⟩ := htd.2.1 husedDS
            have hj_eq_k : j.1 = k := by
              by_contra hne
              have hpnd := by simpa [preLinesNoDirtyInv, hcur] using hpreNoDirty
              have hpermN := hpnd k j.1 hklt j.is_lt (fun h => hne h.symm) hk_dirty
              have hwf := by simpa [preLinesWFInv, hcur] using hpreWF
              have hpermT := (hwf j.1 j.is_lt).1 hdj |>.1
              rw [hpermT] at hpermN; exact TLPerm.noConfusion hpermN
            -- Assemble: j.line.data = (preLines j.1).data = (preLines k).data = transferVal = mem
            have hgoal : (s.locals j).line.data = s.shared.mem := by
              rw [hdata, show j.1 = k from hj_eq_k, ← htv_k]; exact htv
            -- Close the full goal (generalized j matches the goal)
            rw [htv]; simp; exact hgoal
        · rw [dif_neg hdirtyPost, hDRV_post]
          -- No dirty owner in post-state.
          -- From txnDataInv Part 3: grantPendingAck → transferVal = s.shared.mem
          have htd := by simpa [txnDataInv, hcur] using htxnData
          have htv := htd.2.2 (Or.inr hphase)
          -- So: if usedDirtySource then transferVal else mem = mem (both branches = mem)
          simp [htv]
      -- Assemble shared equality
      cases hrhs : refMapShared n (recvGrantAckState s i) with | mk m d pgm pga pra =>
      simp only [hrhs] at hpgm hpga_post hpra_post hdir_eq hmem_post
      subst hpgm; subst hpga_post
      show Atomic.HomeState.mk m d none none pra =
        { refMapShared n s with pendingGrantMeta := none, pendingGrantAck := none }
      simp only [Atomic.HomeState.mk.injEq]
      refine ⟨hmem_post, ?_, trivial, trivial, ?_⟩
      · exact hdir_eq
      · rw [hpra_post, hpra_pre]
    · -- locals equality
      funext j
      show refMapLine (recvGrantAckState s i) j =
        refMapLine s j
      simp only [refMapLine, recvGrantAckState, recvGrantAckShared, show
        { s.shared with currentTxn := none, pendingGrantAck := none }.currentTxn = none from rfl]
      -- Post: currentTxn = none, so refMapLine = line
      show ((recvGrantAckLocals s i j)).line = _
      rw [hline_preserved]
      -- Pre: currentTxn = some tx, phase = grantPendingAck
      simp only [hcur, hphase]
      by_cases hji : tx.requester = j.1
      · -- j is the requester
        simp [hji]
        -- grantLine (preLines j) tx = (s.locals j).line
        have := htxnLine j
        simp [txnSnapshotLine, hphase, hji] at this
        -- j = i (requester)
        have : j = i := Fin.ext (by omega)
        subst this
        rw [hline_req]
      · -- j is not the requester
        simp [hji]

theorem releasedLine_eq (line : CacheLine) (perm : TLPerm) :
    TileLink.Messages.releasedLine line perm = TileLink.Atomic.releasedLine line perm := by
  cases perm <;> simp [TileLink.Messages.releasedLine, TileLink.Atomic.releasedLine,
    invalidatedLine, TileLink.Atomic.invalidateLine,
    branchAfterProbe, TileLink.Atomic.branchLine,
    tipAfterProbe, TileLink.Atomic.tipLine]

private theorem queuedReleaseIdx_sendRelease {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n)
    (param : PruneReportParam) (withData : Bool)
    (hCi : (s.locals i).chanC = none)
    (hflighti : (s.locals i).releaseInFlight = false)
    (hCother : ∀ j : Fin n, j ≠ i → (s.locals j).chanC = none) :
    queuedReleaseIdx n (sendReleaseState s i param withData) = some i.1 := by
  unfold queuedReleaseIdx
  have hexists : ∃ j : Fin n, ((sendReleaseState s i param withData).locals j).releaseInFlight = true ∧
      ((sendReleaseState s i param withData).locals j).chanC ≠ none := by
    refine ⟨i, ?_, ?_⟩
    · simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn]
    · simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn]
  rw [dif_pos hexists]
  have huniq : ∀ j : Fin n, ((sendReleaseState s i param withData).locals j).releaseInFlight = true ∧
      ((sendReleaseState s i param withData).locals j).chanC ≠ none → j = i := by
    intro j ⟨_, hcj⟩
    by_contra hne
    simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hne] at hcj
    exact hcj (hCother j hne)
  have heqi := huniq _ (Classical.choose_spec hexists)
  exact congrArg (fun x => some (x : Fin n).1) heqi

-- findDirtyReleaseVal_none_of_all_chanC_none removed: use findDirtyReleaseVal_none_of_all_chanC_none' from RefMap.lean

private theorem findDirtyReleaseVal_sendRelease {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n) (param : PruneReportParam)
    (hCi : (s.locals i).chanC = none)
    (hCother : ∀ j : Fin n, j ≠ i → (s.locals j).chanC = none) :
    findDirtyReleaseVal n (sendReleaseState s i param false) = none := by
  simp only [findDirtyReleaseVal]
  have hnone : ¬∃ j : Fin n, ((sendReleaseState s i param false).locals j).releaseInFlight = true ∧
      ∃ msg : CMsg, ((sendReleaseState s i param false).locals j).chanC = some msg ∧
        msg.data ≠ none := by
    intro ⟨j, _, msg, hcj, hdata⟩
    by_cases hji : j = i
    · subst j
      have : ((sendReleaseState s i param false).locals i).chanC =
          some (releaseMsg i.1 param false (s.locals i).line) := by
        simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn]
      rw [this] at hcj
      have := Option.some.inj hcj; subst this
      simp [releaseMsg, releaseDataPayload] at hdata
    · have : ((sendReleaseState s i param false).locals j).chanC = (s.locals j).chanC := by
        simp [sendReleaseState, sendReleaseLocals, setFn, hji]
      rw [this, hCother j hji] at hcj; cases hcj
  rw [dif_neg hnone]

theorem refMap_sendRelease_next {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n} {param : PruneReportParam}
    (hfull : fullInv n s) (hdirtyEx : dirtyExclusiveInv n s)
    (hstep : SendRelease s s' i param) :
    (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n s') := by
  rcases hstep with ⟨htxn, hgrantAck, hrelAck, hCother, hAi, hBi, hCi, hDi, hEi, hSrc, hSink,
    hflight, hlegal, hdirty, hvalid, hs'⟩
  rw [hs']
  rcases hfull with ⟨⟨hlineWF, _, _, _⟩, _, _⟩
  have hallC : ∀ j : Fin n, (s.locals j).chanC = none := by
    intro j
    by_cases hji : j = i
    · subst j; exact hCi
    · exact hCother j hji
  have hDRV_pre := findDirtyReleaseVal_none_of_all_chanC_none' s hallC
  have hQRI_pre := queuedReleaseIdx_eq_none_of_all_chanC_none s hallC
  have hQRI_post := queuedReleaseIdx_sendRelease s i param false hCi hflight hCother
  have hDRV_post := findDirtyReleaseVal_sendRelease s i param hCi hCother
  have hdirty_unique : ∀ j₁ j₂ : Fin n, (s.locals j₁).line.dirty = true →
      (s.locals j₂).line.dirty = true → j₁ = j₂ := by
    intro j₁ j₂ hd₁ hd₂; by_contra hne
    exact absurd (hdirtyEx j₁ j₂ hne hd₁) (by rw [((hlineWF j₂).1 hd₂).1]; exact TLPerm.noConfusion)
  -- Witness: atomic .release param at node i
  -- Prove preconditions and post-state equality
  refine ⟨i, .release param, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [refMap, refMapShared, htxn]
  · simp [refMap, refMapShared, htxn, hgrantAck]
  · simp [refMap, refMapShared, htxn, hrelAck, hQRI_pre]
  · simp [refMap, refMapLine, htxn]; exact hlegal
  · simp [refMap, refMapLine, htxn]; exact hdirty
  · simp [refMap, refMapLine, htxn]; exact hvalid
  · -- Post-state equality
    -- Abbreviate
    let s'_ := sendReleaseState s i param false
    -- Prove locals equality first (easier)
    have hlocs : (refMap n s'_).locals = setFn (refMap n s).locals i
        (TileLink.Atomic.releasedLine ((refMap n s).locals i) param.result) := by
      funext j
      simp only [refMap, refMapLine, show s'_.shared = s.shared from rfl, htxn, setFn]
      by_cases hji : j = i
      · subst j; simp [s'_, sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, releasedLine_eq]
      · simp [s'_, sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji]
    -- Prove shared equality field by field
    have hpgm : (refMap n s'_).shared.pendingGrantMeta = (refMap n s).shared.pendingGrantMeta := by
      simp [refMap, refMapShared, show s'_.shared = s.shared from rfl, htxn]
    have hpga : (refMap n s'_).shared.pendingGrantAck = (refMap n s).shared.pendingGrantAck := by
      simp [refMap, refMapShared, show s'_.shared = s.shared from rfl, htxn, hgrantAck]
    have hpra : (refMap n s'_).shared.pendingReleaseAck = some i.1 := by
      simp only [refMap, refMapShared, show s'_.shared = s.shared from rfl, htxn, hrelAck]
      exact hQRI_post
    have hdir : (refMap n s'_).shared.dir = TileLink.Atomic.syncDir (refMap n s).shared.dir
        (setFn (refMap n s).locals i (TileLink.Atomic.releasedLine ((refMap n s).locals i) param.result)) := by
      simp only [refMap, refMapShared, refMapLine, show s'_.shared = s.shared from rfl, htxn]
      funext k
      simp only [TileLink.Atomic.syncDir]
      split
      · -- k < n
        next hk =>
        simp only [setFn]
        split
        · -- k = i
          next hki =>
          simp [s'_, sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hki, releasedLine_eq]
        · -- k ≠ i
          next hki =>
          simp [s'_, sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hki, refMapLine, htxn]
      · -- k ≥ n
        rfl
    have hreleasedLine_dirty : (releasedLine (s.locals i).line param.result).dirty = false :=
      by cases param.result <;> simp [releasedLine, invalidatedLine, branchAfterProbe, tipAfterProbe]
    have hline_eq : ∀ j : Fin n, (s'_.locals j).line.dirty = (s.locals j).line.dirty := by
      intro j
      by_cases hji : j = i
      · subst hji
        simp [s'_, sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hreleasedLine_dirty, hdirty]
      · simp [s'_, sendReleaseState, sendReleaseLocals, setFn, hji]
    have hdata_eq : ∀ j : Fin n, j ≠ i → (s'_.locals j).line = (s.locals j).line := by
      intro j hji
      simp [s'_, sendReleaseState, sendReleaseLocals, setFn, hji]
    have hmem : (refMap n s'_).shared.mem = (refMap n s).shared.mem := by
      simp only [refMap, refMapShared, show s'_.shared = s.shared from rfl, htxn]
      -- Both pre and post have findDirtyReleaseVal = none
      rw [hDRV_post, hDRV_pre]
      -- Goal: dite on dirty(post locals) = dite on dirty(pre locals)
      by_cases hdirtyEx' : ∃ j : Fin n, (s.locals j).line.dirty = true
      · have hdirty_post : ∃ j : Fin n, (s'_.locals j).line.dirty = true := by
          obtain ⟨j, hd⟩ := hdirtyEx'; exact ⟨j, by rwa [hline_eq j]⟩
        rw [dif_pos hdirty_post, dif_pos hdirtyEx']
        -- Both choose a dirty owner; by uniqueness they're the same non-i index
        have howner := Classical.choose_spec hdirtyEx'
        have howner_ne_i : Classical.choose hdirtyEx' ≠ i := by
          intro heq; rw [heq] at howner; rw [hdirty] at howner; cases howner
        have howner' := Classical.choose_spec hdirty_post
        -- Both are dirty, so by uniqueness they're the same
        have heq_idx : Classical.choose hdirty_post = Classical.choose hdirtyEx' := by
          apply hdirty_unique
          · rwa [hline_eq] at howner'
          · exact howner
        rw [heq_idx]
        exact congrArg (·.data) (hdata_eq _ howner_ne_i)
      · have hno_dirty_post : ¬∃ j : Fin n, (s'_.locals j).line.dirty = true := by
          intro ⟨j, hd⟩; exact hdirtyEx' ⟨j, by rwa [← hline_eq j]⟩
        rw [dif_neg hno_dirty_post, dif_neg hdirtyEx']
    -- Assemble the post-state equality
    -- All 5 shared fields and locals are proved; combine into SymState equality
    exact SymState.ext (by
      show refMapShared n s'_ = _
      have h1 := hmem; have h2 := hdir; have h3 := hpgm; have h4 := hpga; have h5 := hpra
      simp only [refMap] at h1 h2 h3 h4 h5
      -- The goal and hypotheses both refer to refMapShared n s'_ fields
      -- Prove by showing the structure is eta-equivalent after rewriting fields
      cases hrhs : (refMapShared n s'_) with | mk m d pgm pga pra =>
      simp only [hrhs] at h1 h2 h3 h4 h5
      subst h1; subst h2; subst h5
      simp [h3, h4, refMap, refMapShared, htxn, hgrantAck]) hlocs

private theorem findDirtyReleaseVal_sendReleaseData {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n) (param : PruneReportParam)
    (hCi : (s.locals i).chanC = none)
    (hCother : ∀ j : Fin n, j ≠ i → (s.locals j).chanC = none) :
    findDirtyReleaseVal n (sendReleaseState s i param true) =
      some (s.locals i).line.data := by
  unfold findDirtyReleaseVal
  -- The existential witness is node i after sendReleaseState
  have hexists : ∃ j : Fin n, ((sendReleaseState s i param true).locals j).releaseInFlight = true ∧
      ∃ msg : CMsg, ((sendReleaseState s i param true).locals j).chanC = some msg ∧
        msg.data ≠ none := by
    refine ⟨i, ?_, ?_⟩
    · simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn]
    · refine ⟨releaseMsg i.1 param true (s.locals i).line, ?_, ?_⟩
      · simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn]
      · simp [releaseMsg, releaseDataPayload]
  rw [dif_pos hexists]
  -- Show Classical.choose picks i (it's the unique witness)
  have huniq : ∀ j : Fin n, ((sendReleaseState s i param true).locals j).releaseInFlight = true ∧
      (∃ msg : CMsg, ((sendReleaseState s i param true).locals j).chanC = some msg ∧
        msg.data ≠ none) → j = i := by
    intro j ⟨_, msg, hcj, _⟩
    by_contra hne
    simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hne] at hcj
    rw [hCother j hne] at hcj; cases hcj
  have hchosen := huniq _ (Classical.choose_spec hexists)
  -- The chanC at the chosen index is the release message
  have hlocals_eq : ((sendReleaseState s i param true).locals (Classical.choose hexists)).chanC =
      some (releaseMsg i.1 param true (s.locals i).line) := by
    simp [hchosen, sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn]
  -- The inner choose_spec for the existential msg
  -- Use `show` to make the goal refer to the exact term
  show (Classical.choose ((Classical.choose_spec hexists).2)).data = some (s.locals i).line.data
  have hmsg := Classical.choose_spec ((Classical.choose_spec hexists).2)
  -- hmsg.1 : chanC (chosen) = some (Classical.choose spec)
  -- hlocals_eq : chanC (chosen) = some (releaseMsg ...)
  have hmsg_eq : Classical.choose ((Classical.choose_spec hexists).2) =
      releaseMsg i.1 param true (s.locals i).line := by
    have h := hmsg.1.symm.trans hlocals_eq
    exact Option.some.inj h
  rw [hmsg_eq]
  simp [releaseMsg, releaseDataPayload]

theorem refMap_sendReleaseData_next {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n} {param : PruneReportParam}
    (hfull : fullInv n s) (hdirtyEx : dirtyExclusiveInv n s)
    (hstep : SendReleaseData s s' i param) :
    (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n s') := by
  rcases hstep with ⟨htxn, hgrantAck, hrelAck, hCother, hAi, hBi, hCi, hDi, hEi, hSrc, hSink,
    hflight, hlegal, hdirty, hs'⟩
  rw [hs']
  rcases hfull with ⟨⟨hlineWF, _, _, _⟩, _, _⟩
  have hallC : ∀ j : Fin n, (s.locals j).chanC = none := by
    intro j
    by_cases hji : j = i
    · subst j; exact hCi
    · exact hCother j hji
  have hDRV_pre := findDirtyReleaseVal_none_of_all_chanC_none' s hallC
  have hQRI_pre := queuedReleaseIdx_eq_none_of_all_chanC_none s hallC
  have hQRI_post := queuedReleaseIdx_sendRelease s i param true hCi hflight hCother
  have hDRV_post := findDirtyReleaseVal_sendReleaseData s i param hCi hCother
  have hdirty_unique : ∀ j₁ j₂ : Fin n, (s.locals j₁).line.dirty = true →
      (s.locals j₂).line.dirty = true → j₁ = j₂ := by
    intro j₁ j₂ hd₁ hd₂; by_contra hne
    exact absurd (hdirtyEx j₁ j₂ hne hd₁) (by rw [((hlineWF j₂).1 hd₂).1]; exact TLPerm.noConfusion)
  -- Witness: atomic .releaseData param at node i
  refine ⟨i, .releaseData param, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [refMap, refMapShared, htxn]
  · simp [refMap, refMapShared, htxn, hgrantAck]
  · simp [refMap, refMapShared, htxn, hrelAck, hQRI_pre]
  · simp [refMap, refMapLine, htxn]; exact hlegal
  · simp [refMap, refMapLine, htxn]; exact hdirty
  · -- Post-state equality
    let s'_ := sendReleaseState s i param true
    -- Prove locals equality
    have hlocs : (refMap n s'_).locals = setFn (refMap n s).locals i
        (TileLink.Atomic.releasedLine ((refMap n s).locals i) param.result) := by
      funext j
      simp only [refMap, refMapLine, show s'_.shared = s.shared from rfl, htxn, setFn]
      by_cases hji : j = i
      · subst j; simp [s'_, sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, releasedLine_eq]
      · simp [s'_, sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji]
    -- Prove shared fields
    have hpgm : (refMap n s'_).shared.pendingGrantMeta = (refMap n s).shared.pendingGrantMeta := by
      simp [refMap, refMapShared, show s'_.shared = s.shared from rfl, htxn]
    have hpga : (refMap n s'_).shared.pendingGrantAck = (refMap n s).shared.pendingGrantAck := by
      simp [refMap, refMapShared, show s'_.shared = s.shared from rfl, htxn, hgrantAck]
    have hpra : (refMap n s'_).shared.pendingReleaseAck = some i.1 := by
      simp only [refMap, refMapShared, show s'_.shared = s.shared from rfl, htxn, hrelAck]
      exact hQRI_post
    have hdir : (refMap n s'_).shared.dir = TileLink.Atomic.syncDir (refMap n s).shared.dir
        (setFn (refMap n s).locals i (TileLink.Atomic.releasedLine ((refMap n s).locals i) param.result)) := by
      simp only [refMap, refMapShared, refMapLine, show s'_.shared = s.shared from rfl, htxn]
      funext k
      simp only [TileLink.Atomic.syncDir]
      split
      · next hk =>
        simp only [setFn]
        split
        · next hki =>
          simp [s'_, sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hki, releasedLine_eq]
        · next hki =>
          simp [s'_, sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hki, refMapLine, htxn]
      · rfl
    -- Prove mem: pre has dirty owner i, post has findDirtyReleaseVal = some (s.locals i).line.data
    -- Atomic post mem = (refMap n s).locals i).data = (s.locals i).line.data
    have hreleasedLine_dirty : (releasedLine (s.locals i).line param.result).dirty = false :=
      by cases param.result <;> simp [releasedLine, invalidatedLine, branchAfterProbe, tipAfterProbe]
    have hno_dirty_post : ¬∃ j : Fin n, (s'_.locals j).line.dirty = true := by
      intro ⟨j, hd⟩
      by_cases hji : j = i
      · subst hji
        simp [s'_, sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hreleasedLine_dirty] at hd
      · have hd' : (s.locals j).line.dirty = true := by
          simp [s'_, sendReleaseState, sendReleaseLocals, setFn, hji] at hd; exact hd
        exact hji (hdirty_unique j i hd' hdirty)
    have hmem : (refMap n s'_).shared.mem = (s.locals i).line.data := by
      simp only [refMap, refMapShared, show s'_.shared = s.shared from rfl, htxn]
      rw [dif_neg hno_dirty_post, hDRV_post]
    have hmem_pre : (refMap n s).shared.mem = (s.locals i).line.data := by
      simp only [refMap, refMapShared, htxn, hDRV_pre]
      have hdirtyEx' : ∃ j : Fin n, (s.locals j).line.dirty = true := ⟨i, hdirty⟩
      rw [dif_pos hdirtyEx']
      exact congrArg (·.data) (congrArg (fun j => (s.locals j).line)
        (hdirty_unique (Classical.choose hdirtyEx') i (Classical.choose_spec hdirtyEx') hdirty))
    -- (refMap n s).locals i = refMapLine s i = (s.locals i).line
    have hlocal_i : (refMap n s).locals i = (s.locals i).line := by
      simp [refMap, refMapLine, htxn]
    -- The atomic post mem = (refMap n s).locals i .data
    have hmem' : (refMap n s'_).shared.mem = ((refMap n s).locals i).data := by
      rw [hmem, hlocal_i]
    -- Assemble the post-state equality
    exact SymState.ext (by
      show refMapShared n s'_ = _
      have h1 := hmem'; have h2 := hdir; have h3 := hpgm; have h4 := hpga; have h5 := hpra
      simp only [refMap] at h1 h2 h3 h4 h5
      cases hrhs : (refMapShared n s'_) with | mk m d pgm pga pra =>
      simp only [hrhs] at h1 h2 h3 h4 h5
      subst h1; subst h2; subst h5
      simp [h3, h4, refMap, refMapShared, htxn, hgrantAck]) hlocs

-- Helper: queuedReleaseIdx returns some i.1 when only node i has chanC ≠ none and releaseInFlight
private theorem queuedReleaseIdx_recvRelease {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n)
    (hflight : (s.locals i).releaseInFlight = true)
    (hCi : (s.locals i).chanC ≠ none)
    (hCother : ∀ j : Fin n, j ≠ i → (s.locals j).chanC = none) :
    queuedReleaseIdx n s = some i.1 := by
  unfold queuedReleaseIdx
  have hexists : ∃ j : Fin n, (s.locals j).releaseInFlight = true ∧ (s.locals j).chanC ≠ none :=
    ⟨i, hflight, hCi⟩
  rw [dif_pos hexists]
  have huniq : ∀ j : Fin n, (s.locals j).releaseInFlight = true ∧ (s.locals j).chanC ≠ none → j = i := by
    intro j ⟨_, hCj⟩
    by_contra hne
    exact hCj (hCother j hne)
  exact congrArg (fun x => some (x : Fin n).1) (huniq _ (Classical.choose_spec hexists))

-- Helper: findDirtyReleaseVal for state with node i's chanC having msg
private theorem findDirtyReleaseVal_unique_release {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n) (msg : CMsg)
    (hflight : (s.locals i).releaseInFlight = true)
    (hCi : (s.locals i).chanC = some msg) (hdata : msg.data ≠ none)
    (hCother : ∀ j : Fin n, j ≠ i → (s.locals j).chanC = none) :
    findDirtyReleaseVal n s = msg.data := by
  unfold findDirtyReleaseVal
  have hexists : ∃ j : Fin n, (s.locals j).releaseInFlight = true ∧
      ∃ m : CMsg, (s.locals j).chanC = some m ∧ m.data ≠ none :=
    ⟨i, hflight, msg, hCi, hdata⟩
  rw [dif_pos hexists]
  -- Show Classical.choose = i
  have huniq : ∀ j : Fin n, (s.locals j).releaseInFlight = true ∧
      (∃ m : CMsg, (s.locals j).chanC = some m ∧ m.data ≠ none) → j = i := by
    intro j ⟨_, m, hCj, _⟩
    by_contra hne
    rw [hCother j hne] at hCj; cases hCj
  have hchosen := huniq _ (Classical.choose_spec hexists)
  -- The chosen message at the chosen index equals msg
  have hCchosen : (s.locals (Classical.choose hexists)).chanC = some msg := by
    rw [hchosen]; exact hCi
  have hmsg_spec := Classical.choose_spec (Classical.choose_spec hexists).2
  have hmsg_eq : Classical.choose (Classical.choose_spec hexists).2 = msg := by
    exact Option.some.inj (hmsg_spec.1.symm.trans hCchosen)
  simp only [hmsg_eq]

theorem refMap_recvReleaseAtManager_eq {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n}
    (hfull : fullInv n s) (hcleanRel : cleanChanCInv n s)
    (hCother : ∀ j : Fin n, j ≠ i → (s.locals j).chanC = none)
    (hstep : RecvReleaseAtManager s s' i) :
    refMap n s' = refMap n s := by
  rcases hstep with ⟨msg, param, htxn, hgrantAck, hrelAck, hflight, hCi, _, _, _, _, _, hs'⟩
  rw [hs']
  apply SymState.ext
  · -- refMapShared equality
    simp only [refMap, refMapShared, recvReleaseState, recvReleaseShared, recvReleaseLocals, htxn]
    -- Post: pendingReleaseAck = some i.1, Pre: pendingReleaseAck = none → queuedReleaseIdx
    -- Lines are unchanged (recvReleaseLocal only touches chanC/chanD)
    have hline_eq : ∀ j : Fin n, ((setFn s.locals i (recvReleaseLocal (s.locals i) i.1)) j).line =
        (s.locals j).line := by
      intro j; simp [setFn]; split <;> simp_all [recvReleaseLocal]
    -- Dirty owner existence is the same
    have hdirty_iff : (∃ j : Fin n, ((setFn s.locals i (recvReleaseLocal (s.locals i) i.1)) j).line.dirty = true) ↔
        (∃ j : Fin n, (s.locals j).line.dirty = true) := by
      constructor
      · rintro ⟨j, hd⟩; exact ⟨j, by rw [hline_eq j] at hd; exact hd⟩
      · rintro ⟨j, hd⟩; exact ⟨j, by rw [hline_eq j]; exact hd⟩
    -- Post: all chanC = none
    have hallC_post : ∀ j : Fin n,
        ((setFn s.locals i (recvReleaseLocal (s.locals i) i.1)) j).chanC = none := by
      intro j; simp [setFn]; split
      · simp [recvReleaseLocal]
      · next h => exact hCother j (fun heq => h (by exact heq))
    -- Post findDirtyReleaseVal = none
    have hfind_post : findDirtyReleaseVal n (recvReleaseState s i msg param) = none := by
      simp [recvReleaseState]
      exact findDirtyReleaseVal_none_of_all_chanC_none' _ hallC_post
    -- Pre: queuedReleaseIdx = some i.1
    have hqueued : queuedReleaseIdx n s = some i.1 :=
      queuedReleaseIdx_recvRelease s i hflight (by rw [hCi]; exact Option.some_ne_none _) hCother
    -- dir: syncDir with same lines, updateDirAt is invisible for k ≥ n
    have hdir : TileLink.Atomic.syncDir (updateDirAt s.shared.dir i param.result)
        (fun j => ((setFn s.locals i (recvReleaseLocal (s.locals i) i.1)) j).line) =
        TileLink.Atomic.syncDir s.shared.dir (fun j => (s.locals j).line) := by
      funext k; simp only [TileLink.Atomic.syncDir]; split
      · next hk => rw [hline_eq ⟨k, hk⟩]
      · next hk => simp [updateDirAt, show k ≠ i.1 from fun h => hk (h ▸ i.is_lt)]
    -- pra
    have hpra_eq : (some i.1 : Option Nat) = queuedReleaseIdx n s := hqueued.symm
    -- Assemble all 5 fields
    simp only [Atomic.HomeState.mk.injEq]
    refine ⟨?_, hdir, trivial, trivial, by simp [hrelAck, hqueued]⟩
    -- mem: by_cases on dirty owner existence
    show _ = _
    by_cases hd : ∃ j : Fin n, ((setFn s.locals i (recvReleaseLocal (s.locals i) i.1)) j).line.dirty = true
    · rw [dif_pos hd, dif_pos (hdirty_iff.mp hd)]; simp only [hline_eq]
    · rw [dif_neg hd, dif_neg (fun h => hd (hdirty_iff.mpr h))]
      -- Normalize both goal and hfind_post to match
      show (match findDirtyReleaseVal n (recvReleaseState s i msg param) with
            | some v => v | none => releaseWriteback s.shared.mem msg) = _
      rw [hfind_post]
      cases hdata : msg.data with
        | some v =>
          have := findDirtyReleaseVal_unique_release s i msg hflight (hCi ▸ rfl) (by rw [hdata]; simp) hCother
          rw [this, hdata]; simp [releaseWriteback, hdata]
        | none =>
          have : findDirtyReleaseVal n s = none := by
            simp only [findDirtyReleaseVal]
            rw [dif_neg]; intro ⟨j, hfl, m, hcj, hdm⟩
            by_cases hji : j = i
            · subst j; rw [hCi] at hcj; cases Option.some.inj hcj; rw [hdata] at hdm; exact hdm rfl
            · rw [hCother j hji] at hcj; cases hcj
          rw [this]; simp [releaseWriteback, hdata]
  · -- refMapLine equality
    funext j
    simp only [refMap, refMapLine, recvReleaseState, recvReleaseShared, recvReleaseLocals, htxn,
      recvReleaseLocal, setFn]
    split <;> simp_all [recvReleaseLocal]

theorem refMap_recvReleaseAckAtMaster_next {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n}
    (hfull : fullInv n s)
    (hCnone : ∀ j : Fin n, (s.locals j).chanC = none)
    (hstep : RecvReleaseAckAtMaster s s' i) :
    (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n s') := by
  rcases hstep with ⟨msg, hcur, hgrant, hrelAck, hflight, hchanD, hmsg, hs'⟩
  rw [hs']
  -- Post-state definitions
  let sh' := recvReleaseAckShared s
  let ls' := recvReleaseAckLocals s i
  change (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n ⟨sh', ls'⟩)
  -- Frame: line and chanC unchanged by recvReleaseAckLocal
  have hline_eq : ∀ j : Fin n, (ls' j).line = (s.locals j).line := by
    intro j; simp only [ls', recvReleaseAckLocals, setFn]
    split
    · next h => subst h; simp [recvReleaseAckLocal]
    · rfl
  have hchanC_eq : ∀ j : Fin n, (ls' j).chanC = (s.locals j).chanC := by
    intro j; simp only [ls', recvReleaseAckLocals, setFn]
    split
    · next h => subst h; simp [recvReleaseAckLocal]
    · rfl
  -- Post: all chanC still none
  have hCnone' : ∀ j : Fin n, (ls' j).chanC = none := by
    intro j; rw [hchanC_eq j]; exact hCnone j
  -- findDirtyReleaseVal = none in both pre and post (all chanC = none)
  have hDRV_pre : findDirtyReleaseVal n s = none :=
    findDirtyReleaseVal_none_of_all_chanC_none' s hCnone
  have hDRV_post : findDirtyReleaseVal n (⟨sh', ls'⟩ : SymState HomeState NodeState n) = none :=
    findDirtyReleaseVal_none_of_all_chanC_none' _ hCnone'
  -- queuedReleaseIdx = none in both pre and post (all chanC = none)
  have hQRI_pre : queuedReleaseIdx n s = none :=
    queuedReleaseIdx_eq_none_of_all_chanC_none s hCnone
  have hQRI_post : queuedReleaseIdx n (⟨sh', ls'⟩ : SymState HomeState NodeState n) = none :=
    queuedReleaseIdx_eq_none_of_all_chanC_none _ hCnone'
  -- currentTxn unchanged = none
  have hcur' : sh'.currentTxn = none := by simp [sh', recvReleaseAckShared, hcur]
  -- Witness: atomic .releaseAck at node i
  show ∃ (j : Fin n) (a : TileLink.Atomic.Act),
    TileLink.Atomic.tlAtomic.step n j a (refMap n s) (refMap n ⟨sh', ls'⟩)
  refine ⟨i, .releaseAck, ?_⟩
  refine ⟨?_, ?_⟩
  · -- Precondition: (refMap n s).shared.pendingReleaseAck = some i.1
    show (refMapShared n s).pendingReleaseAck = some i.1
    simp only [refMapShared, hcur]
    show (match s.shared.pendingReleaseAck with
      | some i => some i
      | none => queuedReleaseIdx n s) = some i.1
    rw [hrelAck]
  · -- Postcondition: refMap n s' = { (refMap n s).shared with pendingReleaseAck := none, locals }
    apply SymState.ext
    · -- shared
      show refMapShared n ⟨sh', ls'⟩ =
        { (refMapShared n s) with pendingReleaseAck := none }
      rw [TileLink.Atomic.HomeState.mk.injEq]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- mem: refMapShared computes mem the same way since lines are identical
        show (refMapShared n ⟨sh', ls'⟩).mem = (refMapShared n s).mem
        simp only [refMapShared, hcur', hcur]
        -- Goal: the dite on dirty owners + findDirtyReleaseVal match
        -- Since (ls' j).line = (s.locals j).line, the dirty owner sets are identical
        -- and sh'.mem = s.shared.mem
        have hlsline : (fun j : Fin n => (ls' j).line) = (fun j => (s.locals j).line) :=
          funext hline_eq
        -- Rewrite (ls' j).line to (s.locals j).line everywhere
        show (if h : ∃ j : Fin n, (ls' j).line.dirty = true
              then (ls' (Classical.choose h)).line.data
              else match findDirtyReleaseVal n ⟨sh', ls'⟩ with
                   | some v => v | none => sh'.mem) =
             (if h : ∃ j : Fin n, (s.locals j).line.dirty = true
              then (s.locals (Classical.choose h)).line.data
              else match findDirtyReleaseVal n s with
                   | some v => v | none => s.shared.mem)
        -- Rewrite dirty predicates using line equality
        have hdirty_eq : (∃ j : Fin n, (ls' j).line.dirty = true) =
            (∃ j : Fin n, (s.locals j).line.dirty = true) := by
          congr 1; exact funext (fun j => by rw [hline_eq j])
        by_cases hd : ∃ j : Fin n, (ls' j).line.dirty = true
        · rw [dif_pos hd, dif_pos (hdirty_eq ▸ hd)]
          simp only [hline_eq]
        · rw [dif_neg hd, dif_neg (by rwa [hdirty_eq] at hd)]
          rw [hDRV_post, hDRV_pre]; rfl
      · -- dir: syncDir with same lines
        show (refMapShared n ⟨sh', ls'⟩).dir = (refMapShared n s).dir
        simp only [refMapShared, hcur', hcur]
        exact syncDir_lines_eq s.shared.dir s.locals ls' hline_eq
      · -- pendingGrantMeta
        simp only [refMapShared, hcur', hcur]
      · -- pendingGrantAck
        show (refMapShared n ⟨sh', ls'⟩).pendingGrantAck = (refMapShared n s).pendingGrantAck
        simp only [refMapShared, hcur', hcur]
        show (recvReleaseAckShared s).pendingGrantAck = s.shared.pendingGrantAck
        simp [recvReleaseAckShared]
      · -- pendingReleaseAck = none
        show (refMapShared n ⟨sh', ls'⟩).pendingReleaseAck = none
        simp only [refMapShared, hcur']
        show (match sh'.pendingReleaseAck with
          | some i => some i
          | none => queuedReleaseIdx n ⟨sh', ls'⟩) = none
        have : sh'.pendingReleaseAck = none := by simp [sh', recvReleaseAckShared]
        rw [this, hQRI_post]
    · -- locals: refMapLine unchanged since lines are preserved
      show (fun j => refMapLine ⟨sh', ls'⟩ j) = (fun j => refMapLine s j)
      funext j; simp only [refMapLine, hcur', hcur]; exact hline_eq j

theorem refMap_read_eq {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n}
    (hstep : Read s s' i) :
    refMap n s' = refMap n s := by
  rcases hstep with ⟨_, _, _, _, _, _, hs'⟩
  rw [hs']

theorem refMap_uncachedGet_eq {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n} {source : SourceId}
    (hstep : UncachedGet s s' i source) :
    refMap n s' = refMap n s := by
  rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, hs'⟩
  rw [hs']
  exact refMap_eq_of_invisible_local_change
    (fun j => by simp [setFn]; split <;> simp_all)
    (fun j => by simp [setFn]; split <;> simp_all)
    (fun j => by simp [setFn]; split <;> simp_all)

-- Helper: findDirtyReleaseVal is unchanged when chanC and releaseInFlight are preserved
private theorem findDirtyReleaseVal_eq_of_chanC_releaseEq {n : Nat}
    {s s' : SymState HomeState NodeState n}
    (hC : ∀ j : Fin n, (s'.locals j).chanC = (s.locals j).chanC)
    (hflight : ∀ j : Fin n, (s'.locals j).releaseInFlight = (s.locals j).releaseInFlight) :
    findDirtyReleaseVal n s' = findDirtyReleaseVal n s := by
  simp only [findDirtyReleaseVal, hC, hflight]

theorem refMap_uncachedPut_next {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n} {source : SourceId} {v : Val}
    (hfull : fullInv n s)
    (hstep : UncachedPut s s' i source v) :
    (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n s') := by
  rcases hstep with ⟨hcur, hgrant, hrel, hallN, hchanA, hchanB, hchanC, hchanD, hchanE,
    hpendSrc, hrelFlight, hs'⟩
  rw [hs']
  -- Define the post-state explicitly
  let localI' : NodeState := { (s.locals i) with
    chanA := some (mkPutMsg source), pendingSource := some source }
  let ls' : Fin n → NodeState := setFn s.locals i localI'
  let sh' : HomeState := { s.shared with mem := v }
  change (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n ⟨sh', ls'⟩)
  -- Key frame facts: line, chanC, releaseInFlight unchanged by UncachedPut
  have hline_eq : ∀ j : Fin n, (ls' j).line = (s.locals j).line := by
    intro j; simp only [ls', localI', setFn]
    split
    · next h => subst h; rfl
    · rfl
  have hchanC_eq : ∀ j : Fin n, (ls' j).chanC = (s.locals j).chanC := by
    intro j; simp only [ls', localI', setFn]
    split
    · next h => subst h; rfl
    · rfl
  have hflight_eq : ∀ j : Fin n, (ls' j).releaseInFlight = (s.locals j).releaseInFlight := by
    intro j; simp only [ls', localI', setFn]
    split
    · next h => subst h; rfl
    · rfl
  -- No dirty owner (all perm .N implies dirty = false by lineWF)
  have hnoDirty : ¬∃ j : Fin n, (s.locals j).line.dirty = true := by
    intro ⟨j, hdirty⟩
    rcases hfull with ⟨⟨hlineWF, _⟩, _⟩
    have := (hlineWF j).2.2 (hallN j)
    rw [this.2] at hdirty; exact absurd hdirty (by simp)
  have hnoDirty' : ¬∃ j : Fin n, (ls' j).line.dirty = true := by
    intro ⟨j, hdirty⟩; exact hnoDirty ⟨j, by rw [← hline_eq j]; exact hdirty⟩
  -- findDirtyReleaseVal and queuedReleaseIdx unchanged
  have hDRV : findDirtyReleaseVal n (⟨sh', ls'⟩ : SymState HomeState NodeState n) =
      findDirtyReleaseVal n s :=
    findDirtyReleaseVal_eq_of_chanC_releaseEq hchanC_eq hflight_eq
  have hQRI : queuedReleaseIdx n (⟨sh', ls'⟩ : SymState HomeState NodeState n) =
      queuedReleaseIdx n s :=
    queuedReleaseIdx_eq_of_chanC_releaseEq hchanC_eq hflight_eq
  -- dir unchanged (sh'.dir = s.shared.dir since only mem changed)
  have hdir_sh : sh'.dir = s.shared.dir := rfl
  have hdir_eq : TileLink.Atomic.syncDir sh'.dir (fun j => (ls' j).line) =
      TileLink.Atomic.syncDir s.shared.dir (fun j => (s.locals j).line) := by
    rw [hdir_sh]; funext k; by_cases hk : k < n
    · simp only [TileLink.Atomic.syncDir, hk, dite_true]
      exact congrArg CacheLine.perm (hline_eq ⟨k, hk⟩)
    · simp [TileLink.Atomic.syncDir, hk]
  have hcur' : sh'.currentTxn = none := hcur
  -- Witness: atomic uncachedWrite with the refMapShared mem of post-state.
  -- When no dirty release is in flight, this is v; when one exists, it equals
  -- the release value (and refMap n s' = refMap n s, making this a self-loop).
  show ∃ (j : Fin n) (a : TileLink.Atomic.Act),
    TileLink.Atomic.tlAtomic.step n j a (refMap n s) (refMap n ⟨sh', ls'⟩)
  refine ⟨i, .uncachedWrite (refMapShared n ⟨sh', ls'⟩).mem, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- pendingGrantMeta = none
    show (refMap n s).shared.pendingGrantMeta = none
    simp [refMap, refMapShared, hcur]
  · -- pendingGrantAck = none
    show (refMap n s).shared.pendingGrantAck = none
    simp [refMap, refMapShared, hcur]; exact hgrant
  · -- all perms .N
    intro j; show ((refMap n s).locals j).perm = .N
    simp [refMap, refMapLine, hcur, hallN j]
  · -- postcondition
    apply SymState.ext
    · -- shared: all fields match
      show refMapShared n ⟨sh', ls'⟩ =
        { mem := (refMapShared n ⟨sh', ls'⟩).mem
        , dir := (refMapShared n s).dir
        , pendingGrantMeta := (refMapShared n s).pendingGrantMeta
        , pendingGrantAck := (refMapShared n s).pendingGrantAck
        , pendingReleaseAck := (refMapShared n s).pendingReleaseAck }
      rw [TileLink.Atomic.HomeState.mk.injEq]
      refine ⟨rfl, ?_, ?_, ?_, ?_⟩
      · -- dir
        show (refMapShared n ⟨sh', ls'⟩).dir = (refMapShared n s).dir
        simp only [refMapShared, hcur', hcur]; exact hdir_eq
      · -- pendingGrantMeta
        simp [refMapShared, hcur', hcur]
      · -- pendingGrantAck
        show (refMapShared n ⟨sh', ls'⟩).pendingGrantAck = (refMapShared n s).pendingGrantAck
        simp only [refMapShared, hcur', hcur]
        show sh'.pendingGrantAck = s.shared.pendingGrantAck; rfl
      · -- pendingReleaseAck
        show (refMapShared n ⟨sh', ls'⟩).pendingReleaseAck = (refMapShared n s).pendingReleaseAck
        simp only [refMapShared, hcur', hcur]
        show (match sh'.pendingReleaseAck with
          | some i => some i
          | none => queuedReleaseIdx n ⟨sh', ls'⟩) =
          (match s.shared.pendingReleaseAck with
          | some i => some i
          | none => queuedReleaseIdx n s)
        simp only [show sh'.pendingReleaseAck = s.shared.pendingReleaseAck from rfl]
        cases s.shared.pendingReleaseAck with
        | some i => rfl
        | none => exact hQRI
    · -- locals: refMapLine unchanged since lines are preserved
      show (fun j => refMapLine ⟨sh', ls'⟩ j) = (fun j => refMapLine s j)
      funext j; simp only [refMapLine, hcur', hcur]; exact hline_eq j

theorem refMap_recvUncachedAtManager_eq {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n}
    (hstep : RecvUncachedAtManager s s' i) :
    refMap n s' = refMap n s := by
  rcases hstep with ⟨_, _, _, msg, _, _, hs'⟩
  rw [hs']
  exact refMap_eq_of_invisible_local_change
    (fun j => by simp [setFn]; split <;> simp_all)
    (fun j => by simp [setFn]; split <;> simp_all)
    (fun j => by simp [setFn]; split <;> simp_all)

theorem refMap_recvAccessAckAtMaster_eq {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n}
    (hstep : RecvAccessAckAtMaster s s' i) :
    refMap n s' = refMap n s := by
  rcases hstep with ⟨msg, _, _, hs'⟩
  rw [hs']
  exact refMap_eq_of_invisible_local_change
    (fun j => by simp [setFn]; split <;> simp_all)
    (fun j => by simp [setFn]; split <;> simp_all)
    (fun j => by simp [setFn]; split <;> simp_all)

end TileLink.Messages
