import Leslie.Examples.CacheCoherence.TileLink.Messages.StepProbe

namespace TileLink.Messages

open TLA TileLink SymShared

private theorem fin_val_ne_of_ne {n : Nat} {i j : Fin n} (h : j ≠ i) : j.1 ≠ i.1 := by
  intro hval
  apply h
  exact Fin.ext hval

private theorem chanB_none_of_phase_ne_probing (n : Nat)
    (s : SymState HomeState NodeState n) (hchanB : chanBInv n s)
    {tx : ManagerTxn} (hcur : s.shared.currentTxn = some tx) (hphase : tx.phase ≠ .probing) :
    ∀ j : Fin n, (s.locals j).chanB = none := by
  intro j
  specialize hchanB j
  cases hB : (s.locals j).chanB with
  | none => exact rfl
  | some _ =>
      rw [hB] at hchanB
      rcases hchanB with ⟨tx0, hcur0, hprobing, _, _, _, _⟩
      rw [hcur] at hcur0
      injection hcur0 with htx
      subst htx
      contradiction

private theorem chanC_none_of_phase_ne_probing (n : Nat)
    (s : SymState HomeState NodeState n) (hchanC : chanCInv n s)
    {tx : ManagerTxn} (hcur : s.shared.currentTxn = some tx) (hphase : tx.phase ≠ .probing) :
    ∀ j : Fin n, (s.locals j).chanC = none := by
  intro j
  specialize hchanC j
  cases hC : (s.locals j).chanC with
  | none => exact rfl
  | some _ =>
      rw [hC] at hchanC
      rcases hchanC with hprobe | hrel
      · rcases hprobe with ⟨tx0, hcur0, hprobing, _, _, _, _, _, _⟩
        rw [hcur] at hcur0
        injection hcur0 with htx
        subst htx
        contradiction
      · rcases hrel with ⟨_, hcurNone, _, _, _, _, _, _⟩
        rw [hcur] at hcurNone
        simp at hcurNone

private theorem chanD_noneOrAccessAck_of_pendingGrant_none (n : Nat)
    (s : SymState HomeState NodeState n) (hchanD : chanDInv n s)
    (hgrant : s.shared.pendingGrantAck = none)
    (hrel : s.shared.pendingReleaseAck = none) :
    ∀ j : Fin n, (s.locals j).chanD = none ∨
      (∃ msg, (s.locals j).chanD = some msg ∧
        (msg.opcode = .accessAck ∨ msg.opcode = .accessAckData) ∧
        (s.locals j).pendingSource ≠ none ∧
        (s.locals j).chanA = none) := by
  intro j
  specialize hchanD j
  cases hD : (s.locals j).chanD with
  | none => exact Or.inl rfl
  | some msg =>
      rw [hD] at hchanD
      rcases hchanD with hgrantBranch | hrelBranch | ⟨hacc, hps, hchanAnone⟩
      · rcases hgrantBranch with ⟨_, _, _, _, hpending, _, _, _⟩
        rw [hgrant] at hpending
        simp at hpending
      · rcases hrelBranch with ⟨_, _, hpendingRel, _, _, _, _⟩
        rw [hrel] at hpendingRel
        simp at hpendingRel
      · exact Or.inr ⟨msg, rfl, hacc, hps, hchanAnone⟩

private theorem chanE_none_of_pendingGrant_none (n : Nat)
    (s : SymState HomeState NodeState n) (hchanE : chanEInv n s)
    (hgrant : s.shared.pendingGrantAck = none) :
    ∀ j : Fin n, (s.locals j).chanE = none := by
  intro j
  specialize hchanE j
  cases hE : (s.locals j).chanE with
  | none => exact rfl
  | some _ =>
      rw [hE] at hchanE
      rcases hchanE with ⟨_, _, _, _, hpending, _, _, _⟩
      rw [hgrant] at hpending
      simp at hpending

private theorem chanD_noneOrAccessAck_of_other_requester (n : Nat)
    (s : SymState HomeState NodeState n) (hchanD : chanDInv n s)
    {tx : ManagerTxn} (hcur : s.shared.currentTxn = some tx) {i : Fin n} (hreq : tx.requester = i.1) :
    ∀ j : Fin n, j ≠ i → (s.locals j).chanD = none ∨
      (∃ msg, (s.locals j).chanD = some msg ∧
        (msg.opcode = .accessAck ∨ msg.opcode = .accessAckData) ∧
        (s.locals j).pendingSource ≠ none ∧
        (s.locals j).chanA = none) := by
  intro j hji
  specialize hchanD j
  cases hD : (s.locals j).chanD with
  | none => exact Or.inl rfl
  | some msg =>
      rw [hD] at hchanD
      rcases hchanD with hgrantBranch | hrelBranch | ⟨hacc, hps, hchanAnone⟩
      · rcases hgrantBranch with ⟨tx0, hcur0, hreq0, _, _, _, _, _⟩
        rw [hcur] at hcur0
        injection hcur0 with htx
        subst htx
        exfalso
        apply hji
        exact Fin.ext (hreq0.symm.trans hreq)
      · rcases hrelBranch with ⟨hcurNone, _, _, _, _, _, _⟩
        rw [hcur] at hcurNone
        simp at hcurNone
      · exact Or.inr ⟨msg, rfl, hacc, hps, hchanAnone⟩

private theorem chanE_none_of_other_requester (n : Nat)
    (s : SymState HomeState NodeState n) (hchanE : chanEInv n s)
    {tx : ManagerTxn} (hcur : s.shared.currentTxn = some tx) {i : Fin n} (hreq : tx.requester = i.1) :
    ∀ j : Fin n, j ≠ i → (s.locals j).chanE = none := by
  intro j hji
  specialize hchanE j
  cases hE : (s.locals j).chanE with
  | none => exact rfl
  | some _ =>
      rw [hE] at hchanE
      rcases hchanE with ⟨tx0, hcur0, hreq0, _, _, _, _, _⟩
      rw [hcur] at hcur0
      injection hcur0 with htx
      subst htx
      exfalso
      apply hji
      exact Fin.ext (hreq0.symm.trans hreq)

theorem coreInv_preserved_sendGrantToRequester (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : coreInv n s)
    {i : Fin n} (hstep : SendGrantToRequester s s' i) :
    coreInv n s' := by
  have hlineWF := hinv.lineWF
  have hdir := hinv.dir
  have hpending := hinv.pending
  have htxn := hinv.txnCore
  rcases hstep with ⟨tx, hcur, hreq, hphase, hgrantNone, hrelNone, hDnone, hEnone, hSinkNone, rfl⟩
  have htxn' : tx.requester < n ∧
      (tx.phase = .probing ∨ tx.phase = .grantReady ∨ tx.phase = .grantPendingAck) ∧
      tx.resultPerm = tx.grow.result ∧
      (tx.grantHasData = false → tx.resultPerm = .T) ∧
      tx.probesNeeded tx.requester = false ∧
      (∀ k : Nat, tx.probesRemaining k = true → tx.probesNeeded k = true) ∧
      (tx.phase = .grantReady → ∀ j : Fin n, tx.probesRemaining j.1 = false) ∧
      (tx.phase = .grantPendingAck → ∀ j : Fin n, tx.probesRemaining j.1 = false) := by
    simpa [txnCoreInv, hcur] using htxn
  rcases htxn' with ⟨hreqLt, _, hresult, hnoDataT, hreqFalse, hsubset, hready, hgrant⟩
  have hallFalse : ∀ j : Fin n, tx.probesRemaining j.1 = false := hready hphase
  refine { lineWF := ?_, dir := ?_, pending := ?_, txnCore := ?_ }
  · intro j
    simpa [sendGrantState_line] using hlineWF j
  · intro j hCnone
    by_cases hji : j = i
    · subst j
      have hCnone_old : (s.locals i).chanC = none := by
        simpa [sendGrantState, sendGrantLocals, setFn] using hCnone
      simpa [sendGrantState, sendGrantShared, sendGrantLocals, setFn] using hdir i hCnone_old
    · have hCnone_old : (s.locals j).chanC = none := by
        simpa [sendGrantState, sendGrantLocals, setFn, hji] using hCnone
      simpa [sendGrantState, sendGrantShared, sendGrantLocals, setFn, hji] using hdir j hCnone_old
  · simp [pendingInv, sendGrantState, sendGrantShared, hrelNone]
  · refine ⟨hreqLt, Or.inr (Or.inr rfl), hresult, hnoDataT, hreqFalse, hsubset, ?_, ?_⟩
    · intro hready'
      cases hready'
    · intro _ j
      exact hallFalse j

theorem channelInv_preserved_sendGrantToRequester (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : channelInv n s)
    {i : Fin n} (hstep : SendGrantToRequester s s' i) :
    channelInv n s' := by
  rcases hinv with ⟨hchanA, hchanB, hchanC, hchanD, hchanE⟩
  rcases hstep with ⟨tx, hcur, hreq, hphase, hgrantNone, hrelNone, hDnone, hEnone, hSinkNone, rfl⟩
  have hBnone := chanB_none_of_phase_ne_probing n s hchanB hcur (by simp [hphase])
  have hCnone := chanC_none_of_phase_ne_probing n s hchanC hcur (by simp [hphase])
  have hDdisj := chanD_noneOrAccessAck_of_pendingGrant_none n s hchanD hgrantNone hrelNone
  have hEnoneAll := chanE_none_of_pendingGrant_none n s hchanE hgrantNone
  let tx' : ManagerTxn := { tx with phase := .grantPendingAck }
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    simpa [sendGrantState_chanA] using hchanA j
  · intro j
    have hnone : ((sendGrantState s i tx).locals j).chanB = none := by
      by_cases hji : j = i
      · subst j
        simp [sendGrantState, sendGrantLocals, hBnone i]
      · simp [sendGrantState, sendGrantLocals, setFn, hji, hBnone j]
    rw [hnone]
    trivial
  · intro j
    have hnone : ((sendGrantState s i tx).locals j).chanC = none := by
      by_cases hji : j = i
      · subst j
        simp [sendGrantState, sendGrantLocals, hCnone i]
      · simp [sendGrantState, sendGrantLocals, setFn, hji, hCnone j]
    rw [hnone]
    trivial
  · intro j
    by_cases hji : j = i
    · subst j
      have hmsg :
          ((sendGrantState s i tx).locals i).chanD = some (grantMsgOfTxn tx) := by
        simp [sendGrantState, sendGrantLocals, grantMsgOfTxn]
      rw [hmsg]
      left
      refine ⟨tx', ?_⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [sendGrantState, sendGrantShared, tx']
      · simp [tx', hreq]
      · simp [tx']
      · simp [sendGrantState, sendGrantShared, hreq]
      · simp [sendGrantState, sendGrantLocals, tx']
      · simpa [sendGrantState, sendGrantLocals, tx'] using hEnone
      · cases tx
        rfl
    · rcases hDdisj j with hDnone | ⟨msg, hD, hacc, hps, hchanAnone⟩
      · have hnone : ((sendGrantState s i tx).locals j).chanD = none := by
          simp [sendGrantState, sendGrantLocals, setFn, hji, hDnone]
        rw [hnone]; trivial
      · have hD' : ((sendGrantState s i tx).locals j).chanD = some msg := by
          simp [sendGrantState, sendGrantLocals, setFn, hji, hD]
        have hps' : ((sendGrantState s i tx).locals j).pendingSource ≠ none := by
          simp [sendGrantState, sendGrantLocals, setFn, hji, hps]
        have hchanAnone' : ((sendGrantState s i tx).locals j).chanA = none := by
          simp [sendGrantState, sendGrantLocals, setFn, hji, hchanAnone]
        rw [hD']; exact Or.inr (Or.inr ⟨hacc, hps', hchanAnone'⟩)
  · intro j
    have hnone : ((sendGrantState s i tx).locals j).chanE = none := by
      by_cases hji : j = i
      · subst j
        simp [sendGrantState, sendGrantLocals, hEnoneAll i]
      · simp [sendGrantState, sendGrantLocals, setFn, hji, hEnoneAll j]
    rw [hnone]
    trivial

theorem coreInv_preserved_recvGrantAtMaster (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : coreInv n s)
    {i : Fin n} (hstep : RecvGrantAtMaster s s' i) :
    coreInv n s' := by
  have hlineWF := hinv.lineWF
  have hdir := hinv.dir
  have hpending := hinv.pending
  have htxn := hinv.txnCore
  rcases hstep with ⟨tx, msg, hcur, hreq, hphase, hpendingGrant, hA, hD, hE, hSink, hmsg, rfl⟩
  have htxn' : tx.requester < n ∧
      (tx.phase = .probing ∨ tx.phase = .grantReady ∨ tx.phase = .grantPendingAck) ∧
      tx.resultPerm = tx.grow.result ∧
      (tx.grantHasData = false → tx.resultPerm = .T) ∧
      tx.probesNeeded tx.requester = false ∧
      (∀ k : Nat, tx.probesRemaining k = true → tx.probesNeeded k = true) ∧
      (tx.phase = .grantReady → ∀ j : Fin n, tx.probesRemaining j.1 = false) ∧
      (tx.phase = .grantPendingAck → ∀ j : Fin n, tx.probesRemaining j.1 = false) := by
    simpa [txnCoreInv, hcur] using htxn
  rcases htxn' with ⟨hreqLt, hphaseOk, hresult, hnoDataT, hreqFalse, hsubset, hready, hgrant⟩
  refine { lineWF := ?_, dir := ?_, pending := ?_, txnCore := ?_ }
  · intro j
    by_cases hji : j = i
    · subst j
      simp [recvGrantState, recvGrantLocals, recvGrantLocal, grantLine_wf]
    · simpa [recvGrantState, recvGrantLocals, recvGrantLocal, setFn, hji] using hlineWF j
  · intro j hCnone
    by_cases hji : j = i
    · subst j
      simpa [recvGrantState, recvGrantShared, recvGrantLocals, recvGrantLocal, updateDirAt]
        using (grantLine_perm_eq_result (s.locals i).line tx hnoDataT).symm
    · have hCnone_old : (s.locals j).chanC = none := by
        simpa [recvGrantState, recvGrantLocals, recvGrantLocal, setFn, hji] using hCnone
      have hdirj := hdir j hCnone_old
      simpa [recvGrantState, recvGrantShared, recvGrantLocals, recvGrantLocal, setFn, hji,
        updateDirAt, fin_val_ne_of_ne hji] using hdirj
  · simpa [pendingInv, recvGrantState, recvGrantShared, hcur, hphase, hpendingGrant] using hpending
  · simpa [recvGrantState, recvGrantShared] using htxn

theorem channelInv_preserved_recvGrantAtMaster (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : channelInv n s)
    {i : Fin n} (hstep : RecvGrantAtMaster s s' i) :
    channelInv n s' := by
  rcases hinv with ⟨hchanA, hchanB, hchanC, hchanD, hchanE⟩
  rcases hstep with ⟨tx, msg, hcur, hreq, hphase, hpendingGrant, hA, hD, hE, hSink, hmsg, rfl⟩
  have hBnone := chanB_none_of_phase_ne_probing n s hchanB hcur (by simp [hphase])
  have hCnone := chanC_none_of_phase_ne_probing n s hchanC hcur (by simp [hphase])
  have hDotherDisj := chanD_noneOrAccessAck_of_other_requester n s hchanD hcur hreq
  have hEotherNone := chanE_none_of_other_requester n s hchanE hcur hreq
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hji : j = i
    · subst j
      simp [recvGrantState, recvGrantLocals, recvGrantLocal, hA]
    · simpa [recvGrantState_chanA, recvGrantState, recvGrantLocals, recvGrantLocal, setFn, hji] using hchanA j
  · intro j
    have hnone : ((recvGrantState s i tx).locals j).chanB = none := by
      by_cases hji : j = i
      · subst j
        simp [recvGrantState, recvGrantLocals, recvGrantLocal, hBnone i]
      · simp [recvGrantState, recvGrantLocals, recvGrantLocal, setFn, hji, hBnone j]
    rw [hnone]
    trivial
  · intro j
    have hnone : ((recvGrantState s i tx).locals j).chanC = none := by
      by_cases hji : j = i
      · subst j
        simp [recvGrantState, recvGrantLocals, recvGrantLocal, hCnone i]
      · simp [recvGrantState, recvGrantLocals, recvGrantLocal, setFn, hji, hCnone j]
    rw [hnone]
    trivial
  · intro j
    by_cases hji : j = i
    · subst j
      simp [recvGrantState, recvGrantLocals, recvGrantLocal]
    · rcases hDotherDisj j hji with hDnone | ⟨msg, hD, hacc, hps, hchanAnone⟩
      · have hnone : ((recvGrantState s i tx).locals j).chanD = none := by
          simp [recvGrantState, recvGrantLocals, recvGrantLocal, setFn, hji, hDnone]
        rw [hnone]; trivial
      · have hD' : ((recvGrantState s i tx).locals j).chanD = some msg := by
          simp [recvGrantState, recvGrantLocals, recvGrantLocal, setFn, hji, hD]
        have hps' : ((recvGrantState s i tx).locals j).pendingSource ≠ none := by
          simp [recvGrantState, recvGrantLocals, recvGrantLocal, setFn, hji, hps]
        have hchanAnone' : ((recvGrantState s i tx).locals j).chanA = none := by
          simp [recvGrantState, recvGrantLocals, recvGrantLocal, setFn, hji, hchanAnone]
        rw [hD']; exact Or.inr (Or.inr ⟨hacc, hps', hchanAnone'⟩)
  · intro j
    by_cases hji : j = i
    · subst j
      have hmsgE :
          ((recvGrantState s i tx).locals i).chanE = some ({ sink := tx.sink } : EMsg) := by
        simp [recvGrantState, recvGrantLocals, recvGrantLocal]
      rw [hmsgE]
      have hSink' : ((recvGrantState s i tx).locals i).pendingSink = some tx.sink := by
        simpa [recvGrantState, recvGrantLocals, recvGrantLocal] using hSink
      have hDnone' : ((recvGrantState s i tx).locals i).chanD = none := by
        simp [recvGrantState, recvGrantLocals, recvGrantLocal]
      refine ⟨tx, ?_⟩
      exact ⟨hcur, hreq, hphase, hpendingGrant, hSink', hDnone', rfl⟩
    · have hnone : ((recvGrantState s i tx).locals j).chanE = none := by
        simpa [recvGrantState, recvGrantLocals, recvGrantLocal, setFn, hji] using hEotherNone j hji
      rw [hnone]
      trivial

theorem coreInv_preserved_recvGrantAckAtManager (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : coreInv n s)
    {i : Fin n} (hstep : RecvGrantAckAtManager s s' i) :
    coreInv n s' := by
  have hlineWF := hinv.lineWF
  have hdir := hinv.dir
  have hpending := hinv.pending
  have htxn := hinv.txnCore
  rcases hstep with ⟨tx, msg, hcur, hreq, hphase, hpendingGrant, hD, hE, hSink, hmsg, rfl⟩
  have hpendPair : s.shared.pendingReleaseAck = none ∧ s.shared.pendingGrantAck = some tx.requester := by
    simpa [pendingInv, hcur, hphase] using hpending
  rcases hpendPair with ⟨hrelNone, _⟩
  refine { lineWF := ?_, dir := ?_, pending := ?_, txnCore := ?_ }
  · intro j
    simpa [recvGrantAckState_line] using hlineWF j
  · intro j hCnone
    by_cases hji : j = i
    · subst j
      have hCnone_old : (s.locals i).chanC = none := by
        simpa [recvGrantAckState, recvGrantAckLocals, setFn] using hCnone
      simpa [recvGrantAckState, recvGrantAckShared, recvGrantAckLocals, setFn] using hdir i hCnone_old
    · have hCnone_old : (s.locals j).chanC = none := by
        simpa [recvGrantAckState, recvGrantAckLocals, setFn, hji] using hCnone
      simpa [recvGrantAckState, recvGrantAckShared, recvGrantAckLocals, setFn, hji] using hdir j hCnone_old
  · simp [pendingInv, recvGrantAckState, recvGrantAckShared, hrelNone]
  · simp [txnCoreInv, recvGrantAckState, recvGrantAckShared]

theorem channelInv_preserved_recvGrantAckAtManager (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : channelInv n s)
    {i : Fin n} (hstep : RecvGrantAckAtManager s s' i) :
    channelInv n s' := by
  rcases hinv with ⟨hchanA, hchanB, hchanC, hchanD, hchanE⟩
  rcases hstep with ⟨tx, msg, hcur, hreq, hphase, hpendingGrant, hD, hE, hSink, hmsg, rfl⟩
  have hBnone := chanB_none_of_phase_ne_probing n s hchanB hcur (by simp [hphase])
  have hCnone := chanC_none_of_phase_ne_probing n s hchanC hcur (by simp [hphase])
  have hDotherDisj := chanD_noneOrAccessAck_of_other_requester n s hchanD hcur hreq
  have hEotherNone := chanE_none_of_other_requester n s hchanE hcur hreq
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    simpa [recvGrantAckState_chanA] using hchanA j
  · intro j
    have hnone : ((recvGrantAckState s i).locals j).chanB = none := by
      by_cases hji : j = i
      · subst j
        simp [recvGrantAckState, recvGrantAckLocals, hBnone i]
      · simp [recvGrantAckState, recvGrantAckLocals, setFn, hji, hBnone j]
    rw [hnone]
    trivial
  · intro j
    have hnone : ((recvGrantAckState s i).locals j).chanC = none := by
      by_cases hji : j = i
      · subst j
        simp [recvGrantAckState, recvGrantAckLocals, hCnone i]
      · simp [recvGrantAckState, recvGrantAckLocals, setFn, hji, hCnone j]
    rw [hnone]
    trivial
  · intro j
    by_cases hji : j = i
    · subst j
      simp [recvGrantAckState, recvGrantAckLocals, hD]
    · rcases hDotherDisj j hji with hDnone | ⟨msg, hDmsg, hacc, hps, hchanAnone⟩
      · have hnone : ((recvGrantAckState s i).locals j).chanD = none := by
          simp [recvGrantAckState, recvGrantAckLocals, setFn, hji, hDnone]
        rw [hnone]; trivial
      · have hD' : ((recvGrantAckState s i).locals j).chanD = some msg := by
          simp [recvGrantAckState, recvGrantAckLocals, setFn, hji, hDmsg]
        have hps' : ((recvGrantAckState s i).locals j).pendingSource ≠ none := by
          simp [recvGrantAckState, recvGrantAckLocals, setFn, hji, hps]
        have hchanAnone' : ((recvGrantAckState s i).locals j).chanA = none := by
          simp [recvGrantAckState, recvGrantAckLocals, setFn, hji, hchanAnone]
        rw [hD']; exact Or.inr (Or.inr ⟨hacc, hps', hchanAnone'⟩)
  · intro j
    by_cases hji : j = i
    · subst j
      simp [recvGrantAckState, recvGrantAckLocals]
    · have hnone : ((recvGrantAckState s i).locals j).chanE = none := by
        simp [recvGrantAckState, recvGrantAckLocals, setFn, hji, hEotherNone j hji]
      rw [hnone]
      trivial

end TileLink.Messages
