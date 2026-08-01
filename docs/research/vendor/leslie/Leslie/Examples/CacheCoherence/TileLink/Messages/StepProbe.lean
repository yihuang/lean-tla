import Leslie.Examples.CacheCoherence.TileLink.Messages.StepAcquire

namespace TileLink.Messages

open TLA TileLink SymShared

private theorem fin_val_ne_of_ne {n : Nat} {i j : Fin n} (h : j ≠ i) : j.1 ≠ i.1 := by
  intro hval
  apply h
  exact Fin.ext hval

private theorem probeAckPhase_of_true {n : Nat} {probeMask : Nat → Bool} {j : Fin n}
    (hj : probeMask j.1 = true) :
    probeAckPhase (n := n) probeMask = .probing := by
  by_cases hall : ∀ k : Fin n, probeMask k.1 = false
  · have := hall j
    rw [hj] at this
    contradiction
  · simp [probeAckPhase, hall]

private theorem chanD_noneOrAccessAck_of_phase_ne_grantPendingAck (n : Nat)
    (s : SymState HomeState NodeState n) (hchanD : chanDInv n s)
    {tx : ManagerTxn} (hcur : s.shared.currentTxn = some tx)
    (hphase : tx.phase ≠ .grantPendingAck) :
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
      · rcases hgrantBranch with ⟨tx0, hcur0, _, hphase0, _, _, _, _⟩
        rw [hcur] at hcur0
        injection hcur0 with htx
        subst htx
        contradiction
      · rcases hrelBranch with ⟨hcurNone, _, _, _, _, _, _⟩
        rw [hcur] at hcurNone
        simp at hcurNone
      · exact Or.inr ⟨msg, rfl, hacc, hps, hchanAnone⟩

private theorem chanE_none_of_phase_ne_grantPendingAck (n : Nat)
    (s : SymState HomeState NodeState n) (hchanE : chanEInv n s)
    {tx : ManagerTxn} (hcur : s.shared.currentTxn = some tx)
    (hphase : tx.phase ≠ .grantPendingAck) :
    ∀ j : Fin n, (s.locals j).chanE = none := by
  intro j
  specialize hchanE j
  cases hE : (s.locals j).chanE with
  | none => exact rfl
  | some _ =>
      rw [hE] at hchanE
      rcases hchanE with ⟨tx0, hcur0, _, hphase0, _, _, _, _⟩
      rw [hcur] at hcur0
      injection hcur0 with htx
      subst htx
      contradiction

theorem coreInv_preserved_recvProbeAtMaster (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : coreInv n s)
    {i : Fin n} (hstep : RecvProbeAtMaster s s' i) :
    coreInv n s' := by
  have hlineWF := hinv.lineWF
  have hdir := hinv.dir
  have hpending := hinv.pending
  have htxn := hinv.txnCore
  rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, _, ⟨hCnone, rfl⟩⟩
  refine { lineWF := ?_, dir := ?_, pending := ?_, txnCore := ?_ }
  · intro j
    by_cases hji : j = i
    · subst j
      simp [recvProbeState, recvProbeLocals, recvProbeLocal]
    · simpa [recvProbeState, recvProbeLocals, recvProbeLocal, setFn, hji] using hlineWF j
  · intro j hCnone
    by_cases hji : j = i
    · subst j
      simp [recvProbeState, recvProbeLocals, recvProbeLocal] at hCnone
    · have hCnone_old : (s.locals j).chanC = none := by
        simpa [recvProbeState, recvProbeLocals, recvProbeLocal, setFn, hji] using hCnone
      simpa [recvProbeState, recvProbeLocals, recvProbeLocal, setFn, hji] using hdir j hCnone_old
  · simpa [pendingInv, recvProbeState, hcur] using hpending
  · simpa [recvProbeState] using htxn

theorem channelInv_preserved_recvProbeAtMaster (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : channelInv n s)
    (htxnLine : txnLineInv n s)
    {i : Fin n} (hstep : RecvProbeAtMaster s s' i) :
    channelInv n s' := by
  rcases hinv with ⟨hchanA, hchanB, hchanC, hchanD, hchanE⟩
  rcases hstep with ⟨tx, msg, hcur, hphase, hremain, hB, hsrc, hop, hparam, ⟨hCnone, rfl⟩⟩
  -- Derive (s.locals i).line = tx.preLines i.1 from txnLineInv
  have hlineEq : (s.locals i).line = tx.preLines i.1 := by
    have htl : (s.locals i).line = txnSnapshotLine tx (s.locals i) i := by
      rw [txnLineInv, hcur] at htxnLine; exact htxnLine i
    unfold txnSnapshotLine at htl
    have hnotGP : ¬(tx.phase = .grantPendingAck ∧ tx.requester = i.1) := by
      intro ⟨h, _⟩; rw [hphase] at h; cases h
    rw [if_neg hnotGP] at htl
    unfold probeSnapshotLine at htl
    split at htl
    · -- probesNeeded: inner if with probesRemaining ∧ chanC = none
      rw [if_pos ⟨hremain, hCnone⟩] at htl; exact htl
    · -- not probesNeeded: preLines directly
      exact htl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hji : j = i
    · subst j
      simp [recvProbeState, recvProbeLocals, recvProbeLocal]
    · simpa [recvProbeState, recvProbeLocals, recvProbeLocal, setFn, hji] using hchanA j
  · intro j
    by_cases hji : j = i
    · subst j
      simp [recvProbeState, recvProbeLocals, recvProbeLocal]
    · simpa [recvProbeState, recvProbeLocals, recvProbeLocal, setFn, hji] using hchanB j
  · intro j
    by_cases hji : j = i
    · subst j
      have hCi :
          ((recvProbeState s i msg).locals i).chanC = some (probeAckMsg i (s.locals i).line) := by
        simp [recvProbeState, recvProbeLocals, recvProbeLocal]
      have hAi :
          ((recvProbeState s i msg).locals i).chanA = none := by
        simp [recvProbeState, recvProbeLocals, recvProbeLocal]
      have hBi :
          ((recvProbeState s i msg).locals i).chanB = none := by
        simp [recvProbeState, recvProbeLocals, recvProbeLocal]
      rw [hCi]
      left
      refine ⟨tx, ?_⟩
      refine ⟨hcur, hphase, hremain, hAi, hBi, ?_, probeAckMsg_wf i (s.locals i).line, ?_⟩
      · simp [probeAckMsg]
      · simp [probeAckMsg, hlineEq]
    · simpa [recvProbeState, recvProbeLocals, recvProbeLocal, setFn, hji] using hchanC j
  · intro j
    have hDdisj := chanD_noneOrAccessAck_of_phase_ne_grantPendingAck n s hchanD hcur (by simp [hphase])
    rcases hDdisj j with hDnone | ⟨dmsg, hD, hacc, hps, hchanAnone⟩
    · by_cases hji : j = i
      · subst j
        simp [recvProbeState, recvProbeLocals, recvProbeLocal, hDnone]
      · simp [recvProbeState, recvProbeLocals, recvProbeLocal, setFn, hji, hDnone]
    · by_cases hji : j = i
      · subst j
        have hD' : ((recvProbeState s i msg).locals i).chanD = some dmsg := by
          simp [recvProbeState, recvProbeLocals, recvProbeLocal, hD]
        have hps' : ((recvProbeState s i msg).locals i).pendingSource ≠ none := by
          simp [recvProbeState, recvProbeLocals, recvProbeLocal, hps]
        have hchanAnone' : ((recvProbeState s i msg).locals i).chanA = none := by
          simp [recvProbeState, recvProbeLocals, recvProbeLocal]
        rw [hD']; exact Or.inr (Or.inr ⟨hacc, hps', hchanAnone'⟩)
      · have hD' : ((recvProbeState s i msg).locals j).chanD = some dmsg := by
          simp [recvProbeState, recvProbeLocals, recvProbeLocal, setFn, hji, hD]
        have hps' : ((recvProbeState s i msg).locals j).pendingSource ≠ none := by
          simp [recvProbeState, recvProbeLocals, recvProbeLocal, setFn, hji, hps]
        have hchanAnone' : ((recvProbeState s i msg).locals j).chanA = none := by
          simp [recvProbeState, recvProbeLocals, recvProbeLocal, setFn, hji, hchanAnone]
        rw [hD']; exact Or.inr (Or.inr ⟨hacc, hps', hchanAnone'⟩)
  · intro j
    have hnoneOld := chanE_none_of_phase_ne_grantPendingAck n s hchanE hcur (by simp [hphase])
    by_cases hji : j = i
    · subst j
      simp [recvProbeState, recvProbeLocals, recvProbeLocal, hnoneOld i]
    · simp [recvProbeState, recvProbeLocals, recvProbeLocal, setFn, hji, hnoneOld j]

theorem coreInv_preserved_recvProbeAckAtManager (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : coreInv n s)
    {i : Fin n} (hstep : RecvProbeAckAtManager s s' i) :
    coreInv n s' := by
  have hlineWF := hinv.lineWF
  have hdir := hinv.dir
  have hpending := hinv.pending
  have htxn := hinv.txnCore
  rcases hstep with ⟨tx, msg, hcur, hphase, hremain, hC, hsrc, hwf, rfl⟩
  have htxn' : tx.requester < n ∧
      (tx.phase = .probing ∨ tx.phase = .grantReady ∨ tx.phase = .grantPendingAck) ∧
      tx.resultPerm = tx.grow.result ∧
      (tx.grantHasData = false → tx.resultPerm = .T) ∧
      tx.probesNeeded tx.requester = false ∧
      (∀ k : Nat, tx.probesRemaining k = true → tx.probesNeeded k = true) ∧
      (tx.phase = .grantReady → ∀ j : Fin n, tx.probesRemaining j.1 = false) ∧
      (tx.phase = .grantPendingAck → ∀ j : Fin n, tx.probesRemaining j.1 = false) := by
    simpa [txnCoreInv, hcur] using htxn
  rcases htxn' with ⟨hreq, hphaseOld, hresult, hnoDataT, hreqFalse, hsubset, hreadyOld, hgrantOld⟩
  have hpendPair : s.shared.pendingReleaseAck = none ∧ s.shared.pendingGrantAck = none := by
    simpa [pendingInv, hcur, hphase] using hpending
  rcases hpendPair with ⟨hrelNone, hgrantNone⟩
  refine { lineWF := ?_, dir := ?_, pending := ?_, txnCore := ?_ }
  · intro j
    by_cases hji : j = i
    · subst j
      have hline : ((recvProbeAckState s i tx msg).locals i).line = (s.locals i).line := by
        simp [recvProbeAckState, recvProbeAckLocals, setFn]
      rw [hline]
      exact hlineWF i
    · have hline : ((recvProbeAckState s i tx msg).locals j).line = (s.locals j).line := by
        simp [recvProbeAckState, recvProbeAckLocals, setFn, hji]
      rw [hline]
      exact hlineWF j
  · intro j hCnone
    by_cases hji : j = i
    · subst j
      simp [recvProbeAckState, recvProbeAckShared, recvProbeAckLocals, updateDirAt]
    · have hCnone_old : (s.locals j).chanC = none := by
        simpa [recvProbeAckState, recvProbeAckLocals, setFn, hji] using hCnone
      have hdirj := hdir j hCnone_old
      simpa [recvProbeAckState, recvProbeAckShared, recvProbeAckLocals, setFn, hji,
        updateDirAt, fin_val_ne_of_ne hji] using hdirj
  · refine ⟨hrelNone, ?_⟩
    have hnot :
        probeAckPhase (n := n) (clearProbeIdx tx.probesRemaining i.1) ≠ .grantPendingAck := by
      by_cases hall : ∀ k : Fin n, clearProbeIdx tx.probesRemaining i.1 k.1 = false
      · simp [probeAckPhase, hall]
      · simp [probeAckPhase, hall]
    by_cases hgp : probeAckPhase (n := n) (clearProbeIdx tx.probesRemaining i.1) = .grantPendingAck
    · exact False.elim (hnot hgp)
    · simp [recvProbeAckState, recvProbeAckShared, hgrantNone, hgp]
  · refine ⟨hreq, ?_, hresult, hnoDataT, hreqFalse, ?_, ?_, ?_⟩
    · by_cases hall : ∀ j : Fin n, clearProbeIdx tx.probesRemaining i.1 j.1 = false
      · right
        left
        simp [probeAckPhase, hall]
      · left
        simp [probeAckPhase, hall]
    · intro k hk
      by_cases hki : k = i.1
      · simp [clearProbeIdx, hki] at hk
      · exact hsubset k (by simpa [recvProbeAckShared, clearProbeIdx, hki] using hk)
    · intro hready j
      have hready' : probeAckPhase (n := n) (clearProbeIdx tx.probesRemaining i.1) = .grantReady := by
        simpa [recvProbeAckShared] using hready
      by_cases hall : ∀ k : Fin n, clearProbeIdx tx.probesRemaining i.1 k.1 = false
      · exact hall j
      · simp [probeAckPhase, hall] at hready'
    · intro hgrant
      have hnot :
          probeAckPhase (n := n) (clearProbeIdx tx.probesRemaining i.1) ≠ .grantPendingAck := by
        by_cases hall : ∀ k : Fin n, clearProbeIdx tx.probesRemaining i.1 k.1 = false
        · simp [probeAckPhase, hall]
        · simp [probeAckPhase, hall]
      exact False.elim (hnot hgrant)

theorem channelInv_preserved_recvProbeAckAtManager (n : Nat)
    (s s' : SymState HomeState NodeState n) (hinv : channelInv n s)
    {i : Fin n} (hstep : RecvProbeAckAtManager s s' i) :
    channelInv n s' := by
  rcases hinv with ⟨hchanA, hchanB, hchanC, hchanD, hchanE⟩
  rcases hstep with ⟨tx, msg, hcur, hphase, hremain, hC, hsrc, hwf, rfl⟩
  -- Derive chanA = none from chanCInv (chanC = some msg → chanA = none)
  have hA : (s.locals i).chanA = none := by
    have hchanCi := hchanC i
    rw [hC] at hchanCi
    rcases hchanCi with hprobe | hrel
    · rcases hprobe with ⟨_, _, _, _, hAnone, _, _, _, _⟩; exact hAnone
    · rcases hrel with ⟨_, _, _, hAnone, _, _, _, _, _⟩; exact hAnone
  have hDdisjOld := chanD_noneOrAccessAck_of_phase_ne_grantPendingAck n s hchanD hcur (by simp [hphase])
  have hEnoneOld := chanE_none_of_phase_ne_grantPendingAck n s hchanE hcur (by simp [hphase])
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hji : j = i
    · subst j
      simp [recvProbeAckState, recvProbeAckLocals, setFn, hA]
    · simpa [recvProbeAckState, recvProbeAckLocals, setFn, hji] using hchanA j
  · intro j
    by_cases hji : j = i
    · subst j
      have hBi : (s.locals i).chanB = none := by
        specialize hchanC i
        rw [hC] at hchanC
        rcases hchanC with hprobe | hrel
        · rcases hprobe with ⟨_, _, _, _, _, hBnone, _, _, _⟩
          exact hBnone
        · rcases hrel with ⟨_, _, _, _, hBnone, _, _, _⟩
          exact hBnone
      simp [recvProbeAckState, recvProbeAckLocals, setFn, hBi]
    · cases hBj : (s.locals j).chanB with
      | none =>
          simp [recvProbeAckState, recvProbeAckLocals, setFn, hji, hBj]
      | some bmsg =>
          have hchanBj := hchanB j
          rw [hBj] at hchanBj
          rcases hchanBj with ⟨tx0, hcur0, hphase0, hrem0, hsrc0, hop0, hparam0⟩
          rw [hcur] at hcur0
          injection hcur0 with htx
          subst htx
          let tx' : ManagerTxn :=
            { tx with
                probesRemaining := clearProbeIdx tx.probesRemaining i.1
                phase := probeAckPhase (n := n) (clearProbeIdx tx.probesRemaining i.1) }
          have hrem' : tx'.probesRemaining j.1 = true := by
            have hvalne := fin_val_ne_of_ne hji
            simp [tx', clearProbeIdx, hvalne, hrem0]
          have hphase' : tx'.phase = .probing := by
            exact probeAckPhase_of_true hrem'
          have hBj' : ((recvProbeAckState s i tx msg).locals j).chanB = some bmsg := by
            simp [recvProbeAckState, recvProbeAckLocals, setFn, hji, hBj]
          rw [hBj']
          refine ⟨tx', ?_⟩
          refine ⟨?_, hphase', hrem', hsrc0, hop0, hparam0⟩
          simp [recvProbeAckState, recvProbeAckShared, tx']
  · intro j
    by_cases hji : j = i
    · subst j
      simp [recvProbeAckState, recvProbeAckLocals, setFn]
    · cases hCj : (s.locals j).chanC with
      | none =>
          simp [recvProbeAckState, recvProbeAckLocals, setFn, hji, hCj]
      | some cmsg =>
          have hchanCj := hchanC j
          rw [hCj] at hchanCj
          rcases hchanCj with hprobe | hrel
          · rcases hprobe with ⟨tx0, hcur0, hphase0, hrem0, hA0, hBnone, hsrc0, hwf0, hdata0⟩
            rw [hcur] at hcur0
            injection hcur0 with htx
            subst htx
            let tx' : ManagerTxn :=
              { tx with
                  probesRemaining := clearProbeIdx tx.probesRemaining i.1
                  phase := probeAckPhase (n := n) (clearProbeIdx tx.probesRemaining i.1) }
            have hrem' : tx'.probesRemaining j.1 = true := by
              have hvalne := fin_val_ne_of_ne hji
              simp [tx', clearProbeIdx, hvalne, hrem0]
            have hphase' : tx'.phase = .probing := by
              exact probeAckPhase_of_true hrem'
            have hCj' : ((recvProbeAckState s i tx msg).locals j).chanC = some cmsg := by
              simp [recvProbeAckState, recvProbeAckLocals, setFn, hji, hCj]
            rw [hCj']
            left
            refine ⟨tx', ?_⟩
            refine ⟨?_, hphase', hrem', ?_, ?_, hsrc0, hwf0, hdata0⟩
            · simp [recvProbeAckState, recvProbeAckShared, tx']
            · simpa [recvProbeAckState, recvProbeAckLocals, setFn, hji] using hA0
            · simpa [recvProbeAckState, recvProbeAckLocals, setFn, hji] using hBnone
          · rcases hrel with ⟨_, hcurNone, _, _, _, _, _, _⟩
            rw [hcur] at hcurNone
            simp at hcurNone
  · intro j
    rcases hDdisjOld j with hDnone | ⟨dmsg, hD, hacc, hps, hchanAnone⟩
    · have hnone : ((recvProbeAckState s i tx msg).locals j).chanD = none := by
        by_cases hji : j = i
        · subst j
          simp [recvProbeAckState, recvProbeAckLocals, hDnone]
        · simp [recvProbeAckState, recvProbeAckLocals, setFn, hji, hDnone]
      rw [hnone]; trivial
    · by_cases hji : j = i
      · subst j
        have hD' : ((recvProbeAckState s i tx msg).locals i).chanD = some dmsg := by
          simp [recvProbeAckState, recvProbeAckLocals, hD]
        have hps' : ((recvProbeAckState s i tx msg).locals i).pendingSource ≠ none := by
          simp [recvProbeAckState, recvProbeAckLocals, hps]
        have hchanAnone' : ((recvProbeAckState s i tx msg).locals i).chanA = none := by
          simp [recvProbeAckState, recvProbeAckLocals, hchanAnone]
        rw [hD']; exact Or.inr (Or.inr ⟨hacc, hps', hchanAnone'⟩)
      · have hD' : ((recvProbeAckState s i tx msg).locals j).chanD = some dmsg := by
          simp [recvProbeAckState, recvProbeAckLocals, setFn, hji, hD]
        have hps' : ((recvProbeAckState s i tx msg).locals j).pendingSource ≠ none := by
          simp [recvProbeAckState, recvProbeAckLocals, setFn, hji, hps]
        have hchanAnone' : ((recvProbeAckState s i tx msg).locals j).chanA = none := by
          simp [recvProbeAckState, recvProbeAckLocals, setFn, hji, hchanAnone]
        rw [hD']; exact Or.inr (Or.inr ⟨hacc, hps', hchanAnone'⟩)
  · intro j
    have hnone : ((recvProbeAckState s i tx msg).locals j).chanE = none := by
      by_cases hji : j = i
      · subst j
        simp [recvProbeAckState, recvProbeAckLocals, hEnoneOld i]
      · simp [recvProbeAckState, recvProbeAckLocals, setFn, hji, hEnoneOld j]
    rw [hnone]
    trivial

end TileLink.Messages
