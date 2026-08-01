import Leslie.Examples.CacheCoherence.TileLink.Messages.StepGrant

namespace TileLink.Messages

open TLA TileLink SymShared

private theorem fin_val_ne_of_ne {n : Nat} {i j : Fin n} (h : j ≠ i) : j.1 ≠ i.1 := by
  intro hval
  apply h
  exact Fin.ext hval

private theorem chanB_none_of_currentTxn_none (n : Nat)
    (s : SymState HomeState NodeState n) (hchanB : chanBInv n s)
    (hcur : s.shared.currentTxn = none) :
    ∀ j : Fin n, (s.locals j).chanB = none := by
  intro j
  specialize hchanB j
  cases hB : (s.locals j).chanB with
  | none => exact rfl
  | some _ =>
      rw [hB] at hchanB
      rcases hchanB with ⟨tx, hcurTx, _, _, _, _, _⟩
      rw [hcur] at hcurTx
      simp at hcurTx

private theorem chanD_noneOrAccessAck_of_no_pending (n : Nat)
    (s : SymState HomeState NodeState n) (hchanD : chanDInv n s)
    (hcur : s.shared.currentTxn = none)
    (_hgrant : s.shared.pendingGrantAck = none)
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
      · rcases hgrantBranch with ⟨tx, hcurTx, _, _, hpending, _, _, _⟩
        rw [hcur] at hcurTx
        simp at hcurTx
      · rcases hrelBranch with ⟨hcurNone, hpendingGrant, hpendingRel, _, _, _, _⟩
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
      rcases hchanE with ⟨tx, _, _, _, hpending, _, _, _⟩
      rw [hgrant] at hpending
      simp at hpending

private theorem chanD_noneOrAccessAck_of_other_pendingRelease (n : Nat)
    (s : SymState HomeState NodeState n) (hchanD : chanDInv n s)
    (hcur : s.shared.currentTxn = none)
    (_hgrant : s.shared.pendingGrantAck = none)
    {i : Fin n} (hrel : s.shared.pendingReleaseAck = some i.1) :
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
      · rcases hgrantBranch with ⟨tx, hcurTx, _, _, _, _, _, _⟩
        rw [hcur] at hcurTx
        simp at hcurTx
      · rcases hrelBranch with ⟨hcurNone, _, hpendingRel, _, _, _, _⟩
        rw [hrel] at hpendingRel
        injection hpendingRel with hEq
        exfalso
        apply hji
        exact Fin.ext hEq.symm
      · exact Or.inr ⟨msg, rfl, hacc, hps, hchanAnone⟩

theorem coreInv_preserved_sendRelease (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : coreInv n s)
    {i : Fin n} {param : PruneReportParam} (hstep : SendRelease s s' i param) :
    coreInv n s' := by
  have hlineWF := hinv.lineWF
  have hdir := hinv.dir
  have hpending := hinv.pending
  have htxn := hinv.txnCore
  rcases hstep with ⟨hcur, hgrant, hrel, _, hA, hB, hC, hD, hE, _, _, _, _, _, _, rfl⟩
  refine { lineWF := ?_, dir := ?_, pending := ?_, txnCore := ?_ }
  · intro j
    by_cases hji : j = i
    · subst j
      simpa [sendReleaseState, sendReleaseLocals, sendReleaseLocal] using
        (releasedLine_wf (s.locals i).line param.result)
    · simpa [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] using hlineWF j
  · intro j hCnone
    by_cases hji : j = i
    · subst j
      simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal] at hCnone
    · have hCnone_old : (s.locals j).chanC = none := by
        simpa [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] using hCnone
      simpa [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] using hdir j hCnone_old
  · simpa [pendingInv, sendReleaseState, hcur, hgrant, hrel] using hpending
  · simpa [txnCoreInv, sendReleaseState, hcur] using htxn

theorem coreInv_preserved_sendReleaseData (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : coreInv n s)
    {i : Fin n} {param : PruneReportParam} (hstep : SendReleaseData s s' i param) :
    coreInv n s' := by
  have hlineWF := hinv.lineWF
  have hdir := hinv.dir
  have hpending := hinv.pending
  have htxn := hinv.txnCore
  rcases hstep with ⟨hcur, hgrant, hrel, _, hA, hB, hC, hD, hE, _, _, _, _, _, _, rfl⟩
  refine { lineWF := ?_, dir := ?_, pending := ?_, txnCore := ?_ }
  · intro j
    by_cases hji : j = i
    · subst j
      simpa [sendReleaseState, sendReleaseLocals, sendReleaseLocal] using
        (releasedLine_wf (s.locals i).line param.result)
    · simpa [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] using hlineWF j
  · intro j hCnone
    by_cases hji : j = i
    · subst j
      simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal] at hCnone
    · have hCnone_old : (s.locals j).chanC = none := by
        simpa [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] using hCnone
      simpa [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] using hdir j hCnone_old
  · simpa [pendingInv, sendReleaseState, hcur, hgrant, hrel] using hpending
  · simpa [txnCoreInv, sendReleaseState, hcur] using htxn

theorem channelInv_preserved_sendRelease (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : channelInv n s)
    {i : Fin n} {param : PruneReportParam} (hstep : SendRelease s s' i param) :
    channelInv n s' := by
  rcases hinv with ⟨hchanA, hchanB, hchanC, hchanD, hchanE⟩
  rcases hstep with ⟨hcur, hgrant, hrel, _, hA, hB, hC, hD, hE, _, _, _, _, _, _, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hji : j = i
    · subst j
      simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, hA]
    · simpa [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] using hchanA j
  · intro j
    by_cases hji : j = i
    · subst j
      simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, hB]
    · simpa [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] using hchanB j
  · intro j
    by_cases hji : j = i
    · subst j
      have hmsg :
          ((sendReleaseState s i param false).locals i).chanC =
            some (releaseMsg i.1 param false (s.locals i).line) := by
        simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal]
      rw [hmsg]
      right
      refine ⟨param, ?_⟩
      refine ⟨hcur, ?_, ?_, ?_, ?_, ?_, ?_, releaseMsg_of_clean i.1 param (s.locals i).line⟩
      · simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal]
      · simpa [sendReleaseState_chanA] using hA
      · simpa [sendReleaseState_chanB] using hB
      · simp [releaseMsg]
      · simp [releaseMsg]
      · simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, releasedLine_perm]
    · simpa [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] using hchanC j
  · intro j
    by_cases hji : j = i
    · subst j
      simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, hD]
    · simpa [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] using hchanD j
  · intro j
    by_cases hji : j = i
    · subst j
      simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, hE]
    · simpa [sendReleaseState_chanE, setFn, hji] using hchanE j

theorem channelInv_preserved_sendReleaseData (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : channelInv n s)
    {i : Fin n} {param : PruneReportParam} (hstep : SendReleaseData s s' i param) :
    channelInv n s' := by
  rcases hinv with ⟨hchanA, hchanB, hchanC, hchanD, hchanE⟩
  rcases hstep with ⟨hcur, hgrant, hrel, _, hA, hB, hC, hD, hE, _, _, _, _, _, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hji : j = i
    · subst j
      simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, hA]
    · simpa [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] using hchanA j
  · intro j
    by_cases hji : j = i
    · subst j
      simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, hB]
    · simpa [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] using hchanB j
  · intro j
    by_cases hji : j = i
    · subst j
      have hmsg :
          ((sendReleaseState s i param true).locals i).chanC =
            some (releaseMsg i.1 param true (s.locals i).line) := by
        simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal]
      rw [hmsg]
      right
      refine ⟨param, ?_⟩
      refine ⟨hcur, ?_, ?_, ?_, ?_, ?_, ?_, releaseMsg_of_dirty i.1 param (s.locals i).line⟩
      · simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal]
      · simpa [sendReleaseState_chanA] using hA
      · simpa [sendReleaseState_chanB] using hB
      · simp [releaseMsg]
      · simp [releaseMsg]
      · simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, releasedLine_perm]
    · simpa [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] using hchanC j
  · intro j
    by_cases hji : j = i
    · subst j
      simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, hD]
    · simpa [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] using hchanD j
  · intro j
    by_cases hji : j = i
    · subst j
      simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, hE]
    · simpa [sendReleaseState_chanE, setFn, hji] using hchanE j

theorem coreInv_preserved_recvReleaseAtManager (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : coreInv n s)
    {i : Fin n} (hstep : RecvReleaseAtManager s s' i) :
    coreInv n s' := by
  have hlineWF := hinv.lineWF
  have hdir := hinv.dir
  have hpending := hinv.pending
  have htxn := hinv.txnCore
  rcases hstep with ⟨msg, param, hcur, hgrant, hrel, hflight, hC, hsrc, hwf, hparam, hperm, hD, rfl⟩
  refine { lineWF := ?_, dir := ?_, pending := ?_, txnCore := ?_ }
  · intro j
    simpa [recvReleaseState_line] using hlineWF j
  · intro j hCnone
    by_cases hji : j = i
    · subst j
      simpa [recvReleaseState, recvReleaseShared, recvReleaseLocals, recvReleaseLocal, updateDirAt, hperm]
    · have hCnone_old : (s.locals j).chanC = none := by
        simpa [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn, hji] using hCnone
      have hdirj := hdir j hCnone_old
      simpa [recvReleaseState, recvReleaseShared, recvReleaseLocals, recvReleaseLocal, setFn, hji,
        updateDirAt, fin_val_ne_of_ne hji] using hdirj
  · simp [pendingInv, recvReleaseState, recvReleaseShared, hcur, hgrant]
    refine ⟨i, rfl, ?_⟩
    simpa [recvReleaseState, recvReleaseLocals, recvReleaseLocal] using hflight
  · simpa [txnCoreInv, recvReleaseState, recvReleaseShared, hcur] using htxn

theorem channelInv_preserved_recvReleaseAtManager (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : channelInv n s)
    {i : Fin n} (hstep : RecvReleaseAtManager s s' i) :
    channelInv n s' := by
  rcases hinv with ⟨hchanA, hchanB, hchanC, hchanD, hchanE⟩
  rcases hstep with ⟨msg, param, hcur, hgrant, hrel, hflight, hC, hsrc, hwf, hparam, hperm, hD, rfl⟩
  have hDdisjAll := chanD_noneOrAccessAck_of_no_pending n s hchanD hcur hgrant hrel
  have hEnoneAll := chanE_none_of_pendingGrant_none n s hchanE hgrant
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    simpa [recvReleaseState_chanA] using hchanA j
  · intro j
    simpa [recvReleaseState_chanB] using hchanB j
  · intro j
    by_cases hji : j = i
    · subst j
      simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal]
    · simpa [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn, hji] using hchanC j
  · intro j
    by_cases hji : j = i
    · subst j
      have hmsg :
          ((recvReleaseState s i msg param).locals i).chanD = some (releaseAckMsg i.1) := by
        simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal]
      rw [hmsg]
      right; left
      refine ⟨hcur, hgrant, ?_, ?_, ?_, ?_, rfl⟩
      · simp [recvReleaseState, recvReleaseShared]
      · simpa [recvReleaseState_releaseInFlight] using hflight
      · simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal]
      · simpa [recvReleaseState_chanE] using hEnoneAll i
    · rcases hDdisjAll j with hDnone | ⟨dmsg, hD, hacc, hps, hchanAnone⟩
      · have hnone : ((recvReleaseState s i msg param).locals j).chanD = none := by
          simpa [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn, hji] using hDnone
        rw [hnone]; trivial
      · have hD' : ((recvReleaseState s i msg param).locals j).chanD = some dmsg := by
          simpa [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn, hji] using hD
        have hps' : ((recvReleaseState s i msg param).locals j).pendingSource ≠ none := by
          simpa [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn, hji] using hps
        have hchanAnone' : ((recvReleaseState s i msg param).locals j).chanA = none := by
          simpa [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn, hji] using hchanAnone
        rw [hD']; exact Or.inr (Or.inr ⟨hacc, hps', hchanAnone'⟩)
  · intro j
    have hnone : ((recvReleaseState s i msg param).locals j).chanE = none := by
      simpa [recvReleaseState_chanE] using hEnoneAll j
    rw [hnone]
    trivial

theorem coreInv_preserved_recvReleaseAckAtMaster (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : coreInv n s)
    {i : Fin n} (hstep : RecvReleaseAckAtMaster s s' i) :
    coreInv n s' := by
  have hlineWF := hinv.lineWF
  have hdir := hinv.dir
  have hpending := hinv.pending
  have htxn := hinv.txnCore
  rcases hstep with ⟨msg, hcur, hgrant, hrel, hflight, hD, hmsg, rfl⟩
  refine { lineWF := ?_, dir := ?_, pending := ?_, txnCore := ?_ }
  · intro j
    simpa [recvReleaseAckState_line] using hlineWF j
  · intro j hCnone
    have hCnone_old : (s.locals j).chanC = none := by
      simpa [recvReleaseAckState_chanC] using hCnone
    have hline : ((recvReleaseAckState s i).locals j).line = (s.locals j).line := by
      simpa [recvReleaseAckState_line]
    rw [hline]
    exact hdir j hCnone_old
  · simp [pendingInv, recvReleaseAckState, recvReleaseAckShared, hcur, hgrant]
  · simpa [txnCoreInv, recvReleaseAckState, recvReleaseAckShared, hcur] using htxn

theorem channelInv_preserved_recvReleaseAckAtMaster (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : channelInv n s)
    {i : Fin n} (hstep : RecvReleaseAckAtMaster s s' i) :
    channelInv n s' := by
  rcases hinv with ⟨hchanA, hchanB, hchanC, hchanD, hchanE⟩
  rcases hstep with ⟨msg, hcur, hgrant, hrel, hflight, hD, hmsg, rfl⟩
  have hBnone := chanB_none_of_currentTxn_none n s hchanB hcur
  have hDotherDisj := chanD_noneOrAccessAck_of_other_pendingRelease n s hchanD hcur hgrant hrel
  have hEnone := chanE_none_of_pendingGrant_none n s hchanE hgrant
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    simpa [recvReleaseAckState_chanA] using hchanA j
  · intro j
    have hnone : ((recvReleaseAckState s i).locals j).chanB = none := by
      simpa [recvReleaseAckState_chanB] using hBnone j
    rw [hnone]
    trivial
  · intro j
    by_cases hji : j = i
    · subst j
      have hCi : (s.locals i).chanC = none := by
        specialize hchanD i
        rw [hD] at hchanD
        rcases hchanD with hgrantBranch | hrelBranch | ⟨_, _, _⟩
        · rcases hgrantBranch with ⟨tx, hcurTx, _, _, _, _, _, _⟩
          rw [hcur] at hcurTx
          simp at hcurTx
        · rcases hrelBranch with ⟨_, _, _, _, hCnone, _, _⟩
          exact hCnone
        · -- accessAck in chanD contradicts releaseAck opcode
          rename_i hacc _ _
          subst hmsg; simp [releaseAckMsg] at hacc
      simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, hCi]
    · simpa [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn, hji] using hchanC j
  · intro j
    by_cases hji : j = i
    · subst j
      simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal]
    · rcases hDotherDisj j hji with hDnone | ⟨dmsg, hDmsg, hacc, hps, hchanAnone⟩
      · have hnone : ((recvReleaseAckState s i).locals j).chanD = none := by
          simpa [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn, hji] using hDnone
        rw [hnone]; trivial
      · have hD' : ((recvReleaseAckState s i).locals j).chanD = some dmsg := by
          simpa [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn, hji] using hDmsg
        have hps' : ((recvReleaseAckState s i).locals j).pendingSource ≠ none := by
          simpa [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn, hji] using hps
        have hchanAnone' : ((recvReleaseAckState s i).locals j).chanA = none := by
          simpa [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn, hji] using hchanAnone
        rw [hD']; exact Or.inr (Or.inr ⟨hacc, hps', hchanAnone'⟩)
  · intro j
    have hnone : ((recvReleaseAckState s i).locals j).chanE = none := by
      simpa [recvReleaseAckState_chanE] using hEnone j
    rw [hnone]
    trivial

theorem fullInv_preserved_with_release (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hinv : fullInv n s) (htxnLine : txnLineInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    fullInv n s' := by
  rcases hinv with ⟨hcore, hchan, _hser⟩
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  match a with
  | .sendAcquireBlock grow source =>
      have hcore' := coreInv_preserved_sendAcquireBlock n s s' hcore hstep
      have hchan' := channelInv_preserved_sendAcquireBlock n s s' hchan hstep
      exact ⟨hcore', hchan', serializationInv_of_core_channel n s' hcore' hchan'⟩
  | .sendAcquirePerm grow source =>
      have hcore' := coreInv_preserved_sendAcquirePerm n s s' hcore hstep
      have hchan' := channelInv_preserved_sendAcquirePerm n s s' hchan hstep
      exact ⟨hcore', hchan', serializationInv_of_core_channel n s' hcore' hchan'⟩
  | .recvAcquireAtManager =>
      rcases hstep with hblk | hperm
      · rcases hblk with ⟨grow, source, hrecv⟩
        have hcore' := coreInv_preserved_recvAcquireBlock n s s' hcore hrecv
        have hchan' := channelInv_preserved_recvAcquireBlock n s s' hcore hchan hrecv
        exact ⟨hcore', hchan', serializationInv_of_core_channel n s' hcore' hchan'⟩
      · rcases hperm with ⟨grow, source, hrecv⟩
        have hcore' := coreInv_preserved_recvAcquirePerm n s s' hcore hrecv
        have hchan' := channelInv_preserved_recvAcquirePerm n s s' hcore hchan hrecv
        exact ⟨hcore', hchan', serializationInv_of_core_channel n s' hcore' hchan'⟩
  | .recvProbeAtMaster =>
      have hcore' := coreInv_preserved_recvProbeAtMaster n s s' hcore hstep
      have hchan' := channelInv_preserved_recvProbeAtMaster n s s' hchan htxnLine hstep
      exact ⟨hcore', hchan', serializationInv_of_core_channel n s' hcore' hchan'⟩
  | .recvProbeAckAtManager =>
      have hcore' := coreInv_preserved_recvProbeAckAtManager n s s' hcore hstep
      have hchan' := channelInv_preserved_recvProbeAckAtManager n s s' hchan hstep
      exact ⟨hcore', hchan', serializationInv_of_core_channel n s' hcore' hchan'⟩
  | .sendGrantToRequester =>
      have hcore' := coreInv_preserved_sendGrantToRequester n s s' hcore hstep
      have hchan' := channelInv_preserved_sendGrantToRequester n s s' hchan hstep
      exact ⟨hcore', hchan', serializationInv_of_core_channel n s' hcore' hchan'⟩
  | .recvGrantAtMaster =>
      have hcore' := coreInv_preserved_recvGrantAtMaster n s s' hcore hstep
      have hchan' := channelInv_preserved_recvGrantAtMaster n s s' hchan hstep
      exact ⟨hcore', hchan', serializationInv_of_core_channel n s' hcore' hchan'⟩
  | .recvGrantAckAtManager =>
      have hcore' := coreInv_preserved_recvGrantAckAtManager n s s' hcore hstep
      have hchan' := channelInv_preserved_recvGrantAckAtManager n s s' hchan hstep
      exact ⟨hcore', hchan', serializationInv_of_core_channel n s' hcore' hchan'⟩
  | .sendRelease param =>
      have hcore' := coreInv_preserved_sendRelease n s s' hcore hstep
      have hchan' := channelInv_preserved_sendRelease n s s' hchan hstep
      exact ⟨hcore', hchan', serializationInv_of_core_channel n s' hcore' hchan'⟩
  | .sendReleaseData param =>
      have hcore' := coreInv_preserved_sendReleaseData n s s' hcore hstep
      have hchan' := channelInv_preserved_sendReleaseData n s s' hchan hstep
      exact ⟨hcore', hchan', serializationInv_of_core_channel n s' hcore' hchan'⟩
  | .recvReleaseAtManager =>
      have hcore' := coreInv_preserved_recvReleaseAtManager n s s' hcore hstep
      have hchan' := channelInv_preserved_recvReleaseAtManager n s s' hchan hstep
      exact ⟨hcore', hchan', serializationInv_of_core_channel n s' hcore' hchan'⟩
  | .recvReleaseAckAtMaster =>
      have hcore' := coreInv_preserved_recvReleaseAckAtMaster n s s' hcore hstep
      have hchan' := channelInv_preserved_recvReleaseAckAtMaster n s s' hchan hstep
      exact ⟨hcore', hchan', serializationInv_of_core_channel n s' hcore' hchan'⟩
  | .store v =>
      rcases hstep with ⟨hcur, hgrant, hrel, _, hperm, hA, hB, hC, hD, hE, hSrc, hFlight, hs'⟩
      subst hs'
      have hlineWF := hcore.lineWF
      have hdir := hcore.dir
      have hpending := hcore.pending
      have htxn := hcore.txnCore
      rcases hchan with ⟨hchanA, hchanB, hchanC, hchanD, hchanE⟩
      have hcore' : coreInv n { shared := s.shared, locals := setFn s.locals i (storeLocal (s.locals i) v) } := by
        refine { lineWF := ?_, dir := ?_, pending := ?_, txnCore := ?_ }
        · -- lineWFInv
          intro j
          by_cases hji : j = i
          · subst j; simp [setFn, storeLocal, CacheLine.WellFormed]
          · simpa [setFn, hji] using hlineWF j
        · -- dirInv
          intro j hCnone
          by_cases hji : j = i
          · subst j
            simp [setFn, storeLocal] at hCnone ⊢
            rw [hdir i hC, hperm]
          · have hCnone_old : (s.locals j).chanC = none := by
              simpa [setFn, hji] using hCnone
            simpa [setFn, hji] using hdir j hCnone_old
        · -- pendingInv
          simpa [pendingInv, hcur, hgrant, hrel] using hpending
        · -- txnCoreInv
          simpa [txnCoreInv, hcur] using htxn
      have hchan' : channelInv n { shared := s.shared, locals := setFn s.locals i (storeLocal (s.locals i) v) } := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro j
          by_cases hji : j = i
          · subst j; simp [setFn, storeLocal, hA]
          · simpa [setFn, hji] using hchanA j
        · intro j
          by_cases hji : j = i
          · subst j; simp [setFn, storeLocal, hB]
          · simpa [setFn, hji] using hchanB j
        · intro j
          by_cases hji : j = i
          · subst j; simp [setFn, storeLocal, hC]
          · simpa [setFn, hji] using hchanC j
        · intro j
          by_cases hji : j = i
          · subst j; simp [setFn, storeLocal, hD]
          · simpa [setFn, hji] using hchanD j
        · intro j
          by_cases hji : j = i
          · subst j; simp [setFn, storeLocal, hE]
          · simpa [setFn, hji] using hchanE j
      exact ⟨hcore', hchan', serializationInv_of_core_channel _ _ hcore' hchan'⟩
  | .read =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩
      exact ⟨hcore, hchan, serializationInv_of_core_channel _ _ hcore hchan⟩
  | .uncachedGet source =>
      rcases hstep with ⟨hcur, hgrant, hrel, hA, hB, hC, hD, hE, hSrc, hFlight, hs'eq⟩
      have hlineWF := hcore.lineWF
      have hdir := hcore.dir
      have hpending := hcore.pending
      have htxn := hcore.txnCore
      rcases hchan with ⟨hchanA, hchanB, hchanC, hchanD, hchanE⟩
      have hcore' : coreInv n s' := by
        rw [hs'eq]
        refine { lineWF := ?_, dir := ?_, pending := ?_, txnCore := ?_ }
        · intro j; by_cases hji : j = i
          · subst j; simpa [setFn] using hlineWF i
          · simpa [setFn, hji] using hlineWF j
        · intro j hCnone; by_cases hji : j = i
          · subst j; simp [setFn] at hCnone ⊢; exact hdir i hC
          · simpa [setFn, hji] using hdir j (by simpa [setFn, hji] using hCnone)
        · simpa [pendingInv, hcur, hgrant, hrel] using hpending
        · simpa [txnCoreInv, hcur] using htxn
      have hchan' : channelInv n s' := by
        rw [hs'eq]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro j; by_cases hji : j = i
          · subst j; simp [setFn, mkGetMsg]
          · simpa [setFn, hji] using hchanA j
        · intro j; by_cases hji : j = i
          · subst j; simp [setFn, hB]
          · simpa [setFn, hji] using hchanB j
        · intro j; by_cases hji : j = i
          · subst j; simp [setFn, hC]
          · simpa [setFn, hji] using hchanC j
        · intro j; by_cases hji : j = i
          · subst j; simp [setFn, hD]
          · simpa [setFn, hji] using hchanD j
        · intro j; by_cases hji : j = i
          · subst j; simp [setFn, hE]
          · simpa [setFn, hji] using hchanE j
      exact ⟨hcore', hchan', serializationInv_of_core_channel _ _ hcore' hchan'⟩
  | .uncachedPut source v =>
      rcases hstep with ⟨hcur, hgrant, hrel, _hallN, hA, hB, hC, hD, hE, hSrc, hFlight, hs'eq⟩
      have hlineWF := hcore.lineWF
      have hdir := hcore.dir
      have hpending := hcore.pending
      have htxn := hcore.txnCore
      rcases hchan with ⟨hchanA, hchanB, hchanC, hchanD, hchanE⟩
      have hcore' : coreInv n s' := by
        rw [hs'eq]
        refine { lineWF := ?_, dir := ?_, pending := ?_, txnCore := ?_ }
        · intro j; by_cases hji : j = i
          · subst j; simpa [setFn] using hlineWF i
          · simpa [setFn, hji] using hlineWF j
        · intro j hCnone; by_cases hji : j = i
          · subst j; simp [setFn] at hCnone ⊢; exact hdir i hC
          · simpa [setFn, hji] using hdir j (by simpa [setFn, hji] using hCnone)
        · simpa [pendingInv, hcur, hgrant, hrel] using hpending
        · simpa [txnCoreInv, hcur] using htxn
      have hchan' : channelInv n s' := by
        rw [hs'eq]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro j; by_cases hji : j = i
          · subst j; simp [setFn, mkPutMsg]
          · simpa [setFn, hji] using hchanA j
        · intro j; by_cases hji : j = i
          · subst j; simp [setFn, hB]
          · simpa [setFn, hji] using hchanB j
        · intro j; by_cases hji : j = i
          · subst j; simp [setFn, hC]
          · simpa [setFn, hji] using hchanC j
        · intro j; by_cases hji : j = i
          · subst j; simp [setFn, hD]
          · simpa [setFn, hji] using hchanD j
        · intro j; by_cases hji : j = i
          · subst j; simp [setFn, hE]
          · simpa [setFn, hji] using hchanE j
      exact ⟨hcore', hchan', serializationInv_of_core_channel _ _ hcore' hchan'⟩
  | .recvUncachedAtManager =>
      rcases hstep with ⟨hcur, hgrant, hrel, msg, hA, hop, hs'eq⟩
      have hlineWF := hcore.lineWF
      have hdir := hcore.dir
      have hpending := hcore.pending
      have htxn := hcore.txnCore
      rcases hchan with ⟨hchanA, hchanB, hchanC, hchanD, hchanE⟩
      have hcore' : coreInv n s' := by
        rw [hs'eq]
        refine { lineWF := ?_, dir := ?_, pending := ?_, txnCore := ?_ }
        · intro j; by_cases hji : j = i
          · subst j; simpa [setFn] using hlineWF i
          · simpa [setFn, hji] using hlineWF j
        · intro j hCnone; by_cases hji : j = i
          · subst j; simp [setFn] at hCnone ⊢; exact hdir i (by simpa [setFn] using hCnone)
          · simpa [setFn, hji] using hdir j (by simpa [setFn, hji] using hCnone)
        · simpa [pendingInv, hcur, hgrant, hrel] using hpending
        · simpa [txnCoreInv, hcur] using htxn
      have hchan' : channelInv n s' := by
        rw [hs'eq]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro j; by_cases hji : j = i
          · subst j; simp [setFn]
          · simpa [setFn, hji] using hchanA j
        · intro j; by_cases hji : j = i
          · subst j; simp [setFn]; specialize hchanB i
            cases hB : (s.locals i).chanB with
            | none => simp
            | some _ => rw [hB] at hchanB; rcases hchanB with ⟨tx, hcurTx, _, _, _, _, _⟩
                        rw [hcur] at hcurTx; simp at hcurTx
          · simpa [setFn, hji] using hchanB j
        · intro j; by_cases hji : j = i
          · subst j; simp [setFn]; specialize hchanC i
            cases hC : (s.locals i).chanC with
            | none => simp
            | some cmsg =>
              rw [hC] at hchanC; rcases hchanC with hprobe | hrel_c
              · rcases hprobe with ⟨tx, hcurTx, _, _, _, _, _, _, _⟩
                rw [hcur] at hcurTx; simp at hcurTx
              · rcases hrel_c with ⟨param, hcurNone, hrelIF, hchanAnone, hchanBnone, hsrc, hparam, hperm, hwf⟩
                exact Or.inr ⟨hcurNone, hrelIF, hchanBnone, hsrc, param, hparam, hperm, hwf⟩
          · simpa [setFn, hji] using hchanC j
        · -- chanDInv: key case — node i gets an accessAck on chanD
          intro j; by_cases hji : j = i
          · subst j; simp [setFn]
            -- The new chanD message has opcode accessAck or accessAckData
            -- and pendingSource is preserved (not touched by the action)
            right; right
            constructor
            · -- opcode = accessAck ∨ accessAckData
              rcases hop with hget | hput
              · exact Or.inr hget
              · exact Or.inl (by simp [hput])
            · -- pendingSource ≠ none: from chanAInv, chanA = some msg → pendingSource = some msg.source
              specialize hchanA i; rw [hA] at hchanA
              rcases hchanA with ⟨hps, _⟩
              simp [hps]
          · simpa [setFn, hji] using hchanD j
        · intro j; by_cases hji : j = i
          · subst j; simp [setFn]; specialize hchanE i
            cases hE : (s.locals i).chanE with
            | none => simp
            | some _ => rw [hE] at hchanE
                        rcases hchanE with ⟨_, hcurTx, _, _, _, _, _, _⟩
                        rw [hcur] at hcurTx; simp at hcurTx
          · simpa [setFn, hji] using hchanE j
      exact ⟨hcore', hchan', serializationInv_of_core_channel _ _ hcore' hchan'⟩
  | .recvAccessAckAtMaster =>
      rcases hstep with ⟨msg, hD, hop, hs'eq⟩
      have hlineWF := hcore.lineWF
      have hdir := hcore.dir
      have hpending := hcore.pending
      have htxn := hcore.txnCore
      rcases hchan with ⟨hchanA, hchanB, hchanC, hchanD, hchanE⟩
      have hcore' : coreInv n s' := by
        rw [hs'eq]
        refine { lineWF := ?_, dir := ?_, pending := ?_, txnCore := ?_ }
        · intro j; by_cases hji : j = i
          · subst j; simpa [setFn] using hlineWF i
          · simpa [setFn, hji] using hlineWF j
        · intro j hCnone; by_cases hji : j = i
          · subst j; simp [setFn] at hCnone ⊢; exact hdir i (by simpa [setFn] using hCnone)
          · simpa [setFn, hji] using hdir j (by simpa [setFn, hji] using hCnone)
        · -- pendingInv: shared unchanged, releaseInFlight unchanged
          simp only [pendingInv]
          have : ∀ fi : Fin n, (setFn s.locals i
            { (s.locals i) with chanD := none, pendingSource := none } fi).releaseInFlight
            = (s.locals fi).releaseInFlight := by
            intro fi; simp [setFn]; split <;> simp_all
          simp only [this]
          exact hpending
        · -- txnCoreInv: only depends on shared, which is unchanged
          simp only [txnCoreInv]
          exact htxn
      have hchan' : channelInv n s' := by
        rw [hs'eq]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · -- chanAInv: chanA unchanged, but pendingSource cleared for node i
          intro j; by_cases hji : j = i
          · subst j; simp [setFn]
            specialize hchanA i
            cases hchanA_eq : (s.locals i).chanA with
            | none => simp
            | some amsg =>
              -- Derive contradiction: chanDInv 3rd disjunct says chanA i = none
              exfalso
              specialize hchanD i; rw [hD] at hchanD
              rcases hchanD with ⟨_, _, _, _, _, _, _, hmsg⟩ | ⟨_, _, _, _, _, _, hmsg⟩ | ⟨_, _, hchanAi_none⟩
              · -- grant branch: msg = grantMsgOfTxn tx, opcode is grant/grantData, not accessAck
                subst hmsg; rcases hop with h | h <;>
                  simp [grantMsgOfTxn, grantOpcodeOfTxn] at h <;> split at h <;> exact absurd h (by decide)
              · -- release ack branch: msg = releaseAckMsg, opcode is releaseAck
                subst hmsg; simp [releaseAckMsg] at hop
              · -- accessAck branch: chanA i = none contradicts hchanA_eq
                rw [hchanA_eq] at hchanAi_none; simp at hchanAi_none
          · simpa [setFn, hji] using hchanA j
        · -- chanBInv: chanB unchanged, shared unchanged
          intro j; by_cases hji : j = i
          · subst j; simp [setFn]; simpa using hchanB i
          · simpa [setFn, hji] using hchanB j
        · -- chanCInv: chanC unchanged, chanA/chanB unchanged, shared unchanged
          intro j; by_cases hji : j = i
          · subst j; simp [setFn]; simpa using hchanC i
          · simpa [setFn, hji] using hchanC j
        · intro j; by_cases hji : j = i
          · subst j; simp [setFn]  -- chanD cleared to none
          · simpa [setFn, hji] using hchanD j
        · -- chanEInv: chanE unchanged, but chanD cleared (chanEInv has chanD = none conjunct)
          intro j; by_cases hji : j = i
          · subst j; simp [setFn]
            specialize hchanE i
            cases hE : (s.locals i).chanE with
            | none => simp
            | some emsg =>
              rw [hE] at hchanE
              rcases hchanE with ⟨tx, hcurTx, hreq, hphase, hpga, hpsink, hchanDnone, hmsg⟩
              -- chanDInv says chanD i = some msg, but chanEInv says chanD i = none
              rw [hD] at hchanDnone; simp at hchanDnone
          · simpa [setFn, hji] using hchanE j
      exact ⟨hcore', hchan', serializationInv_of_core_channel _ _ hcore' hchan'⟩

end TileLink.Messages
