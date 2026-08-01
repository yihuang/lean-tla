import Leslie.Examples.CacheCoherence.TileLink.Messages.Refinement.RefMap

namespace TileLink.Messages

open TLA TileLink SymShared Classical

theorem txnSnapshotLine_eq_of_grantReady {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn}
    (hfull : fullInv n s) (htxnLine : txnLineInv n s)
    (hcur : s.shared.currentTxn = some tx) (hphase : tx.phase = .grantReady) :
    ∀ j : Fin n,
      (s.locals j).line =
        (if tx.probesNeeded j.1 then
          probedLine (tx.preLines j.1) (probeCapOfResult tx.resultPerm)
        else
          tx.preLines j.1) := by
  intro j
  have hallFalse := txnCoreInv_grantReady_allFalse hfull hcur hphase j
  have hlines : ∀ i : Fin n, (s.locals i).line = txnSnapshotLine tx (s.locals i) i := by
    simpa [txnLineInv, hcur] using htxnLine
  specialize hlines j
  simpa [txnSnapshotLine, probeSnapshotLine, hphase, hallFalse] using hlines

theorem txnSnapshotLine_eq_of_grantPendingAck_nonrequester {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn}
    (hfull : fullInv n s) (htxnLine : txnLineInv n s)
    (hcur : s.shared.currentTxn = some tx) (hphase : tx.phase = .grantPendingAck)
    {j : Fin n} (hreqj : tx.requester ≠ j.1) :
    (s.locals j).line =
      (if tx.probesNeeded j.1 then
        probedLine (tx.preLines j.1) (probeCapOfResult tx.resultPerm)
      else
        tx.preLines j.1) := by
  have hallFalse := by
    rcases hfull with ⟨⟨_, _, _, htxnCore⟩, _, _⟩
    rcases (by simpa [txnCoreInv, hcur] using htxnCore :
        tx.requester < n ∧
        (tx.phase = .probing ∨ tx.phase = .grantReady ∨ tx.phase = .grantPendingAck) ∧
        tx.resultPerm = tx.grow.result ∧
        (tx.grantHasData = false → tx.resultPerm = .T) ∧
        tx.probesNeeded tx.requester = false ∧
        (∀ k : Nat, tx.probesRemaining k = true → tx.probesNeeded k = true) ∧
        (tx.phase = .grantReady → ∀ j : Fin n, tx.probesRemaining j.1 = false) ∧
        (tx.phase = .grantPendingAck → ∀ j : Fin n, tx.probesRemaining j.1 = false))
      with ⟨_, _, _, _, _, _, _, hgp⟩
    exact hgp hphase j
  have hlines : ∀ i : Fin n, (s.locals i).line = txnSnapshotLine tx (s.locals i) i := by
    simpa [txnLineInv, hcur] using htxnLine
  specialize hlines j
  have hreqj' : tx.requester = j.1 ∧ (s.locals j).chanE = none → False := by
    intro h
    exact hreqj h.1
  simpa [txnSnapshotLine, probeSnapshotLine, hphase, hreqj, hallFalse, hreqj'] using hlines

theorem write_grant_nonrequester_invalid_of_strongRefinementInv {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn}
    (hinv : strongRefinementInv n s)
    (hcur : s.shared.currentTxn = some tx)
    (hphase : tx.phase = .grantReady ∨ tx.phase = .grantPendingAck)
    (hperm : tx.resultPerm = .T) :
    ∀ j : Fin n, j.1 ≠ tx.requester → (s.locals j).line.perm = .N := by
  rcases hinv with ⟨⟨hfull, _, _, _, _, _, _⟩, htxnLine, _, _, hplan⟩
  intro j hreqj
  cases hkind : tx.kind with
  | acquireBlock =>
      have hallInvalid : snapshotAllOthersInvalid n tx :=
        (txnPlanInv_acquireBlock_tip hplan hcur hkind hperm).1
      have hpreN : (tx.preLines j.1).perm = .N := hallInvalid j hreqj
      cases hphase with
      | inl hready =>
          have hlinej := txnSnapshotLine_eq_of_grantReady hfull htxnLine hcur hready j
          have hmask : tx.probesNeeded = TileLink.Atomic.noProbeMask :=
            (txnPlanInv_acquireBlock_tip hplan hcur hkind hperm).2
          have hprobe : tx.probesNeeded j.1 = false := by
            rw [hmask]
            simp [TileLink.Atomic.noProbeMask]
          rw [hlinej, hprobe]
          simpa [hpreN]
      | inr hgp =>
          have hlinej :=
            txnSnapshotLine_eq_of_grantPendingAck_nonrequester hfull htxnLine hcur hgp
              (fun h => hreqj h.symm)
          have hmask : tx.probesNeeded = TileLink.Atomic.noProbeMask :=
            (txnPlanInv_acquireBlock_tip hplan hcur hkind hperm).2
          have hprobe : tx.probesNeeded j.1 = false := by
            rw [hmask]
            simp [TileLink.Atomic.noProbeMask]
          rw [hlinej, hprobe]
          simpa [hpreN]
  | acquirePerm =>
      have hmask : tx.probesNeeded = snapshotCachedProbeMask n tx :=
        (txnPlanInv_acquirePerm hplan hcur hkind).2.1
      cases hphase with
      | inl hready =>
          have hlinej := txnSnapshotLine_eq_of_grantReady hfull htxnLine hcur hready j
          by_cases hN : (tx.preLines j.1).perm = .N
          · have hprobe : tx.probesNeeded j.1 = false := by
              rw [hmask]
              simp [snapshotCachedProbeMask, j.is_lt, hN]
            rw [hlinej, hprobe]
            simpa [hN]
          · have hprobe : tx.probesNeeded j.1 = true := by
              rw [hmask]
              simp [snapshotCachedProbeMask, j.is_lt, hN]
              exact fun h => hreqj h
            rw [hlinej, hprobe]
            simpa [hperm, probedLine, probeCapOfResult]
      | inr hgp =>
          have hlinej :=
            txnSnapshotLine_eq_of_grantPendingAck_nonrequester hfull htxnLine hcur hgp
              (fun h => hreqj h.symm)
          by_cases hN : (tx.preLines j.1).perm = .N
          · have hprobe : tx.probesNeeded j.1 = false := by
              rw [hmask]
              simp [snapshotCachedProbeMask, j.is_lt, hN]
            rw [hlinej, hprobe]
            simpa [hN]
          · have hprobe : tx.probesNeeded j.1 = true := by
              rw [hmask]
              simp [snapshotCachedProbeMask, j.is_lt, hN]
              exact fun h => hreqj h
            rw [hlinej, hprobe]
            simpa [hperm, probedLine, probeCapOfResult]

theorem preLine_data_eq_mem_of_grantReady_T {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {j : Fin n}
    (hfull : fullInv n s) (hclean : cleanDataInv n s) (htxnLine : txnLineInv n s)
    (hcur : s.shared.currentTxn = some tx) (hphase : tx.phase = .grantReady)
    (hres : tx.resultPerm = .B)
    (hpermT : (tx.preLines j.1).perm = .T)
    (hmask : tx.probesNeeded = snapshotWritableProbeMask n tx)
    (hreqj : tx.requester ≠ j.1) :
    (tx.preLines j.1).data = s.shared.mem := by
  have hprobe : tx.probesNeeded j.1 = true := by
    rw [hmask]
    simp [snapshotWritableProbeMask, j.is_lt, hpermT]
    exact fun h => hreqj h.symm
  have hlinej := txnSnapshotLine_eq_of_grantReady hfull htxnLine hcur hphase j
  have hactual : (s.locals j).line = branchAfterProbe (tx.preLines j.1) := by
    rw [hlinej, hprobe]
    simp [hres, hpermT, probeCapOfResult, probedLine]
  have hvalid_j : (s.locals j).line.valid = true := by rw [hactual]; rfl
  have hdata : (s.locals j).line.data = s.shared.mem := hclean j hvalid_j
  simpa [hactual, branchAfterProbe] using hdata

theorem refMapLine_sendGrant_requester_block_branch_eq {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {i : Fin n}
    (htxnData : txnDataInv n s) (hplan : txnPlanInv n s)
    (hcur : s.shared.currentTxn = some tx) (hreq : tx.requester = i.1)
    (hphase : tx.phase = .grantReady) (hkind : tx.kind = .acquireBlock)
    (hperm : tx.resultPerm = .B) :
    refMapLine (sendGrantState s i tx) i =
      TileLink.Atomic.branchLine (refMap n s).shared.mem := by
  have hgrantData : tx.grantHasData = true := by
    rw [txnPlanInv_grantHasData hplan hcur, hkind]; simp
  have hTransfer : tx.transferVal = s.shared.mem := by
    simp [txnDataInv, hcur] at htxnData; exact htxnData.2.2 (Or.inl hphase)
  simp [refMapLine, sendGrantState, sendGrantShared, sendGrantLocals, hreq,
    grantLine, TileLink.Atomic.branchLine, refMap, refMapShared, hcur, hphase]
  simp [hgrantData, hperm, hTransfer]

theorem refMapLine_sendGrant_requester_block_tip_eq {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {i : Fin n}
    (htxnData : txnDataInv n s) (hplan : txnPlanInv n s)
    (hcur : s.shared.currentTxn = some tx) (hreq : tx.requester = i.1)
    (hphase : tx.phase = .grantReady) (hkind : tx.kind = .acquireBlock)
    (hperm : tx.resultPerm = .T) :
    refMapLine (sendGrantState s i tx) i =
      TileLink.Atomic.tipLine (refMap n s).shared.mem := by
  have hgrantData : tx.grantHasData = true := by
    rw [txnPlanInv_grantHasData hplan hcur, hkind]; simp
  have hTransfer : tx.transferVal = s.shared.mem := by
    simp [txnDataInv, hcur] at htxnData; exact htxnData.2.2 (Or.inl hphase)
  simp [refMapLine, sendGrantState, sendGrantShared, sendGrantLocals, hreq,
    grantLine, TileLink.Atomic.tipLine, refMap, refMapShared, hcur, hphase]
  simp [hgrantData, hperm, hTransfer]

theorem refMapLine_sendGrant_requester_acquirePerm_eq {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {i : Fin n}
    (hplan : txnPlanInv n s)
    (hcur : s.shared.currentTxn = some tx) (hreq : tx.requester = i.1)
    (hphase : tx.phase = .grantReady) (hkind : tx.kind = .acquirePerm) :
    refMapLine (sendGrantState s i tx) i =
      TileLink.Atomic.grantPermLine ((refMap n s).locals i) := by
  have hgrantData : tx.grantHasData = false := by
    rw [txnPlanInv_grantHasData hplan hcur, hkind]
    simp
  simp [refMapLine, sendGrantState, sendGrantShared, sendGrantLocals, hreq,
    grantLine, TileLink.Atomic.grantPermLine, refMap, refMapShared, hcur, hphase]
  simp [hgrantData]

theorem refMapLine_sendGrant_nonrequester_block_branch_eq {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {i j : Fin n}
    (hfull : fullInv n s) (hclean : cleanDataInv n s) (htxnLine : txnLineInv n s)
    (htxnData : txnDataInv n s) (hplan : txnPlanInv n s)
    (hcur : s.shared.currentTxn = some tx)
    (hreq : tx.requester = i.1) (hphase : tx.phase = .grantReady)
    (hkind : tx.kind = .acquireBlock) (hperm : tx.resultPerm = .B)
    (hji : j ≠ i) :
    refMapLine (sendGrantState s i tx) j =
      TileLink.Atomic.acquireBlockSharedLocals (refMap n s) i j := by
  have hreqj : tx.requester ≠ j.1 := by
    intro h; exact hji (by ext; omega)
  -- Extract probe mask from txnPlanInv
  have hplanU := hplan
  simp only [txnPlanInv, hcur, hkind] at hplanU
  obtain ⟨_, _, hBplan, _⟩ := hplanU
  have ⟨_, hmask⟩ := hBplan hperm
  -- Get transferVal = mem from txnDataInv
  have hTransfer : tx.transferVal = s.shared.mem := by
    simp [txnDataInv, hcur] at htxnData; exact htxnData.2.2 (Or.inl hphase)
  -- Compute (refMap n s).shared.mem = s.shared.mem
  have hRefMem : (refMap n s).shared.mem = s.shared.mem := by
    simp [refMap, refMapShared, hcur, hphase, hTransfer]
  -- Get the snapshot line equality for j
  have hlinej := txnSnapshotLine_eq_of_grantReady hfull htxnLine hcur hphase j
  -- Simplify LHS to (s.locals j).line
  have hLHS : refMapLine (sendGrantState s i tx) j = (s.locals j).line := by
    simp [refMapLine, sendGrantState, sendGrantShared, sendGrantLocals,
      setFn, hji, hreqj]
  -- Simplify RHS: since j ≠ i, acquireBlockSharedLocals checks perm of refMapLine s j
  have hRefJ : (refMap n s).locals j = tx.preLines j.1 := by
    simp [refMap, refMapLine, hcur, hphase]
  have hRHS : TileLink.Atomic.acquireBlockSharedLocals (refMap n s) i j =
      (if (tx.preLines j.1).perm = .T
       then TileLink.Atomic.branchLine s.shared.mem
       else tx.preLines j.1) := by
    simp [TileLink.Atomic.acquireBlockSharedLocals, hji, hRefJ, hRefMem]
  rw [hLHS, hRHS]
  by_cases hT : (tx.preLines j.1).perm = .T
  · -- j has perm T, so was probed → line is branchAfterProbe
    simp only [hT, ite_true]
    have hprobe : tx.probesNeeded j.1 = true := by
      rw [hmask]; simp [snapshotWritableProbeMask, j.is_lt, hT]
      exact fun h => hreqj h.symm
    rw [hlinej, if_pos hprobe]
    simp only [hperm, probeCapOfResult, probedLine, branchAfterProbe, TileLink.Atomic.branchLine]
    exact congrArg _ (preLine_data_eq_mem_of_grantReady_T hfull hclean htxnLine hcur hphase hperm hT hmask hreqj)
  · -- j has non-T perm, not probed → line = tx.preLines j.1
    simp only [hT, ite_false]
    have hprobe : tx.probesNeeded j.1 = false := by
      rw [hmask]; simp [snapshotWritableProbeMask, j.is_lt, hreqj, hT]
    rw [hlinej, if_neg (by simp [hprobe])]

theorem invalidatedLine_eq_self_of_perm_N_wf {line : CacheLine}
    (hwf : line.WellFormed) (hperm : line.perm = .N) :
    invalidatedLine line = line := by
  rcases hwf.2.2 hperm with ⟨hvalid, hdirty⟩
  cases line
  simp at hperm
  subst hperm
  simp [invalidatedLine]
  exact ⟨hvalid, hdirty⟩

theorem refMapLine_sendGrant_nonrequester_block_tip_eq {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {i j : Fin n}
    (hfull : fullInv n s) (htxnLine : txnLineInv n s)
    (hplan : txnPlanInv n s) (hcur : s.shared.currentTxn = some tx)
    (hreq : tx.requester = i.1) (hphase : tx.phase = .grantReady)
    (hkind : tx.kind = .acquireBlock) (hperm : tx.resultPerm = .T)
    (hji : j ≠ i) :
    refMapLine (sendGrantState s i tx) j =
      setFn (refMap n s).locals i (TileLink.Atomic.tipLine (refMap n s).shared.mem) j := by
  have hallInvalid : snapshotAllOthersInvalid n tx :=
    (txnPlanInv_acquireBlock_tip hplan hcur hkind hperm).1
  have hreqj : tx.requester ≠ j.1 := by
    intro h
    apply hji
    exact Fin.ext (h.symm.trans hreq)
  have hpermN : (tx.preLines j.1).perm = .N := hallInvalid j hreqj.symm
  have hprobe : tx.probesNeeded j.1 = false := by
    rw [(txnPlanInv_acquireBlock_tip hplan hcur hkind hperm).2]
    simp [TileLink.Atomic.noProbeMask]
  have hlinej := txnSnapshotLine_eq_of_grantReady hfull htxnLine hcur hphase j
  calc
    refMapLine (sendGrantState s i tx) j = (s.locals j).line := by
      simp [refMapLine, sendGrantState, sendGrantShared, sendGrantLocals, hji, hreqj]
    _ = tx.preLines j.1 := by
      rw [hlinej, hprobe]
      simp
    _ = (refMap n s).locals j := by
      simp [refMap, refMapLine, hcur, hphase]
    _ = setFn (refMap n s).locals i (TileLink.Atomic.tipLine (refMap n s).shared.mem) j := by
      simp [setFn, hji]

theorem refMapLine_sendGrant_nonrequester_acquirePerm_eq {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {i j : Fin n}
    (hfull : fullInv n s) (htxnLine : txnLineInv n s)
    (hplan : txnPlanInv n s) (hcur : s.shared.currentTxn = some tx)
    (hreq : tx.requester = i.1) (hphase : tx.phase = .grantReady)
    (hkind : tx.kind = .acquirePerm) (hji : j ≠ i) :
    refMapLine (sendGrantState s i tx) j =
      TileLink.Atomic.acquirePermLocals (refMap n s) i j := by
  have hfull0 := hfull
  rcases hfull with ⟨⟨hlineWF, _, _, _⟩, _, _⟩
  have hmask : tx.probesNeeded = snapshotCachedProbeMask n tx :=
    (txnPlanInv_acquirePerm hplan hcur hkind).2.1
  have hpermT : tx.resultPerm = .T :=
    (txnPlanInv_acquirePerm hplan hcur hkind).1
  have hreqj : tx.requester ≠ j.1 := by
    intro h
    apply hji
    exact Fin.ext (h.symm.trans hreq)
  have hlinej := txnSnapshotLine_eq_of_grantReady hfull0 htxnLine hcur hphase j
  by_cases hN : (tx.preLines j.1).perm = .N
  · have hprobe : tx.probesNeeded j.1 = false := by
      rw [hmask]
      by_cases hreqeq : tx.requester = j.1
      · exact False.elim (hreqj hreqeq)
      · simp [snapshotCachedProbeMask, j.is_lt, hN]
    have hcurLine : (s.locals j).line = tx.preLines j.1 := by
      rw [hlinej, hprobe]
      simp
    have hwfPre : (tx.preLines j.1).WellFormed := by
      rw [← hcurLine]
      exact hlineWF j
    calc
      refMapLine (sendGrantState s i tx) j = (s.locals j).line := by
        simp [refMapLine, sendGrantState, sendGrantShared, sendGrantLocals, hji, hreqj]
      _ = tx.preLines j.1 := hcurLine
      _ = invalidatedLine (tx.preLines j.1) := by
        symm
        exact invalidatedLine_eq_self_of_perm_N_wf hwfPre hN
      _ = TileLink.Atomic.invalidateLine (tx.preLines j.1) := by
        rfl
      _ = TileLink.Atomic.acquirePermLocals (refMap n s) i j := by
        have href : (refMap n s).locals j = tx.preLines j.1 := by
          simp [refMap, refMapLine, hcur, hphase]
        rw [TileLink.Atomic.acquirePermLocals, href]
        simp [hji]
  · have hprobe : tx.probesNeeded j.1 = true := by
      rw [hmask]
      by_cases hreqeq : tx.requester = j.1
      · exact False.elim (hreqj hreqeq)
      · simp [snapshotCachedProbeMask, j.is_lt, hN]
        exact fun h => hreqeq h.symm
    have hcurLine : (s.locals j).line = invalidatedLine (tx.preLines j.1) := by
      rw [hlinej, hprobe]
      simp [hpermT, probedLine, probeCapOfResult]
    calc
      refMapLine (sendGrantState s i tx) j = (s.locals j).line := by
        simp [refMapLine, sendGrantState, sendGrantShared, sendGrantLocals, hji, hreqj]
      _ = invalidatedLine (tx.preLines j.1) := hcurLine
      _ = TileLink.Atomic.invalidateLine (tx.preLines j.1) := by
        rfl
      _ = TileLink.Atomic.acquirePermLocals (refMap n s) i j := by
        have href : (refMap n s).locals j = tx.preLines j.1 := by
          simp [refMap, refMapLine, hcur, hphase]
        rw [TileLink.Atomic.acquirePermLocals, href]
        simp [hji]

theorem refMap_sendGrant_block_branch_locals_eq {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {i : Fin n}
    (hfull : fullInv n s) (hclean : cleanDataInv n s) (htxnLine : txnLineInv n s)
    (htxnData : txnDataInv n s) (hplan : txnPlanInv n s)
    (hcur : s.shared.currentTxn = some tx) (hreq : tx.requester = i.1)
    (hphase : tx.phase = .grantReady) (hkind : tx.kind = .acquireBlock)
    (hperm : tx.resultPerm = .B) :
    (refMap n (sendGrantState s i tx)).locals =
      TileLink.Atomic.acquireBlockSharedLocals (refMap n s) i := by
  funext j
  by_cases hji : j = i
  · subst hji
    simpa [refMap, TileLink.Atomic.acquireBlockSharedLocals] using
      refMapLine_sendGrant_requester_block_branch_eq htxnData hplan hcur hreq hphase hkind hperm
  · simpa [refMap] using
      refMapLine_sendGrant_nonrequester_block_branch_eq hfull hclean htxnLine htxnData hplan hcur hreq hphase
        hkind hperm hji

theorem refMap_sendGrant_block_tip_locals_eq {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {i : Fin n}
    (hfull : fullInv n s) (htxnLine : txnLineInv n s)
    (htxnData : txnDataInv n s) (hplan : txnPlanInv n s)
    (hcur : s.shared.currentTxn = some tx) (hreq : tx.requester = i.1)
    (hphase : tx.phase = .grantReady) (hkind : tx.kind = .acquireBlock)
    (hperm : tx.resultPerm = .T) :
    (refMap n (sendGrantState s i tx)).locals =
      setFn (refMap n s).locals i (TileLink.Atomic.tipLine (refMap n s).shared.mem) := by
  funext j
  by_cases hji : j = i
  · subst hji
    simpa [refMap, setFn] using
      refMapLine_sendGrant_requester_block_tip_eq htxnData hplan hcur hreq hphase hkind hperm
  · simpa [refMap, setFn, hji] using
      refMapLine_sendGrant_nonrequester_block_tip_eq hfull htxnLine hplan hcur hreq hphase hkind
        hperm hji

theorem refMap_sendGrant_acquirePerm_locals_eq {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {i : Fin n}
    (hfull : fullInv n s) (htxnLine : txnLineInv n s)
    (hplan : txnPlanInv n s)
    (hcur : s.shared.currentTxn = some tx) (hreq : tx.requester = i.1)
    (hphase : tx.phase = .grantReady) (hkind : tx.kind = .acquirePerm) :
    (refMap n (sendGrantState s i tx)).locals =
      TileLink.Atomic.acquirePermLocals (refMap n s) i := by
  funext j
  by_cases hji : j = i
  · subst hji
    simpa [refMap, TileLink.Atomic.acquirePermLocals] using
      refMapLine_sendGrant_requester_acquirePerm_eq hplan hcur hreq hphase hkind
  · simpa [refMap] using
      refMapLine_sendGrant_nonrequester_acquirePerm_eq hfull htxnLine hplan hcur hreq hphase hkind hji

theorem refMapShared_sendGrant_block_branch_eq {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {i : Fin n}
    (hfull : fullInv n s) (hclean : cleanDataInv n s) (htxnLine : txnLineInv n s)
    (htxnData : txnDataInv n s) (hplan : txnPlanInv n s)
    (hcur : s.shared.currentTxn = some tx) (hreq : tx.requester = i.1)
    (hphase : tx.phase = .grantReady) (hrel : s.shared.pendingReleaseAck = none)
    (hkind : tx.kind = .acquireBlock)
    (hperm : tx.resultPerm = .B) :
    refMapShared n (sendGrantState s i tx) =
      { mem := (refMap n s).shared.mem
      , dir := TileLink.Atomic.syncDir (refMap n s).shared.dir
          (TileLink.Atomic.acquireBlockSharedLocals (refMap n s) i)
      , pendingGrantMeta := some (TileLink.Atomic.deliveredGrantMeta (absPendingGrantMeta tx))
      , pendingGrantAck := some i.1
      , pendingReleaseAck := none } := by
  have hfull0 := hfull
  rcases hfull with ⟨⟨_, hdir, _, _⟩, _, _⟩
  rw [TileLink.Atomic.HomeState.mk.injEq]
  constructor
  · simp [refMap, refMapShared, sendGrantState, sendGrantShared, hcur]
  constructor
  · funext k
    by_cases hk : k < n
    · let j : Fin n := ⟨k, hk⟩
      by_cases hji : j = i
      · subst hji
        have hreqk : tx.requester = k := by
          simpa [j] using hreq
        calc
          grantPendingDir n { tx with phase := .grantPendingAck } s.shared.dir k = tx.resultPerm := by
            simp [grantPendingDir, updateDirAt, hk, hreqk]
          _ = TLPerm.B := hperm
          _ = TileLink.Atomic.syncDir (refMap n s).shared.dir
                (TileLink.Atomic.acquireBlockSharedLocals (refMap n s) j) k := by
              simp [TileLink.Atomic.syncDir, TileLink.Atomic.acquireBlockSharedLocals, refMap, hk, j]
      · have hreqj : tx.requester ≠ j.1 := by
          intro h
          apply hji
          exact Fin.ext (h.symm.trans hreq)
        have hCnone : (s.locals j).chanC = none :=
          chanC_none_of_phase_ne_probing hfull0 hcur (by simp [hphase]) j
        have hdirj : s.shared.dir j.1 = (s.locals j).line.perm := hdir j hCnone
        have hlocalPerm :
            (TileLink.Atomic.acquireBlockSharedLocals (refMap n s) i j).perm =
              (s.locals j).line.perm := by
          have hlocals :=
            refMap_sendGrant_block_branch_locals_eq hfull0 hclean htxnLine htxnData hplan hcur
              hreq hphase hkind hperm
          have hlineEq :
              refMapLine (sendGrantState s i tx) j = (s.locals j).line := by
            simp [refMapLine, sendGrantState, sendGrantShared, sendGrantLocals, hji, hreqj]
          have hpermEq :=
            congrArg CacheLine.perm (congrFun hlocals j)
          have hpermEq' :
              (s.locals j).line.perm =
                (TileLink.Atomic.acquireBlockSharedLocals (refMap n s) i j).perm := by
            simpa [refMap, hlineEq] using hpermEq
          simpa using hpermEq'.symm
        have hktx : k ≠ tx.requester := by
          exact fun h => hreqj h.symm
        have hki : k ≠ i.1 := by
          intro h
          apply hji
          exact Fin.ext h
        calc
          grantPendingDir n { tx with phase := .grantPendingAck } s.shared.dir k = s.shared.dir k := by
            simp [grantPendingDir, updateDirAt, hk, hreq, hki]
          _ = (s.locals j).line.perm := hdirj
          _ = (TileLink.Atomic.acquireBlockSharedLocals (refMap n s) i j).perm := hlocalPerm.symm
          _ = TileLink.Atomic.syncDir (refMap n s).shared.dir
                (TileLink.Atomic.acquireBlockSharedLocals (refMap n s) i) k := by
              simpa [TileLink.Atomic.syncDir, hk, j]
    · have hki : k ≠ i.1 := by
        intro hkiEq
        apply hk
        simpa [hkiEq] using i.is_lt
      simp [refMap, refMapShared, sendGrantState, sendGrantShared, grantPendingDir,
        TileLink.Atomic.syncDir, preTxnDir, updateDirAt, hcur, hreq, hphase, hk, hki]
  constructor
  · simp [refMapShared, sendGrantState, sendGrantShared, absPendingGrantMeta,
      TileLink.Atomic.deliveredGrantMeta, hcur, hphase]
  constructor
  · simp [refMapShared, sendGrantState, sendGrantShared, hcur, hreq]
  · simp [refMapShared, sendGrantState, sendGrantShared, hcur, hrel]

theorem refMapShared_sendGrant_block_tip_eq {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {i : Fin n}
    (hfull : fullInv n s) (htxnLine : txnLineInv n s)
    (htxnData : txnDataInv n s) (hplan : txnPlanInv n s)
    (hcur : s.shared.currentTxn = some tx) (hreq : tx.requester = i.1)
    (hphase : tx.phase = .grantReady) (hrel : s.shared.pendingReleaseAck = none)
    (hkind : tx.kind = .acquireBlock)
    (hperm : tx.resultPerm = .T) :
    refMapShared n (sendGrantState s i tx) =
      { mem := (refMap n s).shared.mem
      , dir := TileLink.Atomic.syncDir (refMap n s).shared.dir
          (setFn (refMap n s).locals i (TileLink.Atomic.tipLine (refMap n s).shared.mem))
      , pendingGrantMeta := some (TileLink.Atomic.deliveredGrantMeta (absPendingGrantMeta tx))
      , pendingGrantAck := some i.1
      , pendingReleaseAck := none } := by
  have hfull0 := hfull
  rcases hfull with ⟨⟨_, hdir, _, _⟩, _, _⟩
  have hallInvalid : snapshotAllOthersInvalid n tx :=
    (txnPlanInv_acquireBlock_tip hplan hcur hkind hperm).1
  have hmask : tx.probesNeeded = TileLink.Atomic.noProbeMask :=
    (txnPlanInv_acquireBlock_tip hplan hcur hkind hperm).2
  rw [TileLink.Atomic.HomeState.mk.injEq]
  constructor
  · simp [refMap, refMapShared, sendGrantState, sendGrantShared, hcur]
  constructor
  · funext k
    by_cases hk : k < n
    · let j : Fin n := ⟨k, hk⟩
      by_cases hji : j = i
      · subst hji
        have hreqk : tx.requester = k := by
          simpa [j] using hreq
        calc
          grantPendingDir n { tx with phase := .grantPendingAck } s.shared.dir k = tx.resultPerm := by
            simp [grantPendingDir, updateDirAt, hk, hreqk]
          _ = TLPerm.T := hperm
          _ = TileLink.Atomic.syncDir (refMap n s).shared.dir
                (setFn (refMap n s).locals j (TileLink.Atomic.tipLine (refMap n s).shared.mem)) k := by
              simp [TileLink.Atomic.syncDir, setFn, hk, j]
      · have hreqj : tx.requester ≠ j.1 := by
          intro h
          apply hji
          exact Fin.ext (h.symm.trans hreq)
        have hCnone : (s.locals j).chanC = none :=
          chanC_none_of_phase_ne_probing hfull0 hcur (by simp [hphase]) j
        have hdirj : s.shared.dir j.1 = (s.locals j).line.perm := hdir j hCnone
        have hpreN : (tx.preLines j.1).perm = .N := hallInvalid j hreqj.symm
        have hprobe : tx.probesNeeded j.1 = false := by
          rw [hmask]
          simp [TileLink.Atomic.noProbeMask]
        have hlinej : (s.locals j).line = tx.preLines j.1 := by
          have hsnap := txnSnapshotLine_eq_of_grantReady hfull0 htxnLine hcur hphase j
          rw [hsnap, hprobe]
          simp
        have hrefj : (refMap n s).locals j = tx.preLines j.1 := by
          simp [refMap, refMapLine, hcur, hphase]
        have hki : k ≠ i.1 := by
          intro h
          apply hji
          exact Fin.ext h
        calc
          grantPendingDir n { tx with phase := .grantPendingAck } s.shared.dir k = s.shared.dir k := by
            simp [grantPendingDir, updateDirAt, hk, hreq, hki]
          _ = (s.locals j).line.perm := hdirj
          _ = .N := by simpa [hlinej] using hpreN
          _ = (setFn (refMap n s).locals i (TileLink.Atomic.tipLine (refMap n s).shared.mem) j).perm := by
            simp [setFn, hji, hrefj, hpreN]
          _ = TileLink.Atomic.syncDir (refMap n s).shared.dir
                (setFn (refMap n s).locals i (TileLink.Atomic.tipLine (refMap n s).shared.mem)) k := by
              simpa [TileLink.Atomic.syncDir, hk, j]
    · have hki : k ≠ i.1 := by
        intro hkiEq
        apply hk
        simpa [hkiEq] using i.is_lt
      simp [refMap, refMapShared, sendGrantState, sendGrantShared, grantPendingDir,
        TileLink.Atomic.syncDir, preTxnDir, updateDirAt, hcur, hreq, hphase, hk, hki]
  constructor
  · simp [refMapShared, sendGrantState, sendGrantShared, absPendingGrantMeta,
      TileLink.Atomic.deliveredGrantMeta, hcur, hphase]
  constructor
  · simp [refMapShared, sendGrantState, sendGrantShared, hcur, hreq]
  · simp [refMapShared, sendGrantState, sendGrantShared, hcur, hrel]

theorem refMapShared_sendGrant_acquirePerm_eq {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {i : Fin n}
    (hfull : fullInv n s) (htxnLine : txnLineInv n s)
    (htxnData : txnDataInv n s) (hplan : txnPlanInv n s)
    (hcur : s.shared.currentTxn = some tx) (hreq : tx.requester = i.1)
    (hphase : tx.phase = .grantReady) (hrel : s.shared.pendingReleaseAck = none)
    (hkind : tx.kind = .acquirePerm) :
    refMapShared n (sendGrantState s i tx) =
      { mem := (refMap n s).shared.mem
      , dir := TileLink.Atomic.syncDir (refMap n s).shared.dir
          (TileLink.Atomic.acquirePermLocals (refMap n s) i)
      , pendingGrantMeta := some (TileLink.Atomic.deliveredGrantMeta (absPendingGrantMeta tx))
      , pendingGrantAck := some i.1
      , pendingReleaseAck := none } := by
  have hfull0 := hfull
  rcases hfull with ⟨⟨_, hdir, _, _⟩, _, _⟩
  rw [TileLink.Atomic.HomeState.mk.injEq]
  constructor
  · simp [refMap, refMapShared, sendGrantState, sendGrantShared, hcur]
  constructor
  · funext k
    by_cases hk : k < n
    · let j : Fin n := ⟨k, hk⟩
      by_cases hji : j = i
      · subst hji
        have hreqk : tx.requester = k := by
          simpa [j] using hreq
        calc
          grantPendingDir n { tx with phase := .grantPendingAck } s.shared.dir k = tx.resultPerm := by
            simp [grantPendingDir, updateDirAt, hk, hreqk]
          _ = TLPerm.T := (txnPlanInv_acquirePerm hplan hcur hkind).1
          _ = TileLink.Atomic.syncDir (refMap n s).shared.dir
                (TileLink.Atomic.acquirePermLocals (refMap n s) j) k := by
              simp [TileLink.Atomic.syncDir, TileLink.Atomic.acquirePermLocals, refMap, hk, j]
      · have hreqj : tx.requester ≠ j.1 := by
          intro h
          apply hji
          exact Fin.ext (h.symm.trans hreq)
        have hCnone : (s.locals j).chanC = none :=
          chanC_none_of_phase_ne_probing hfull0 hcur (by simp [hphase]) j
        have hdirj : s.shared.dir j.1 = (s.locals j).line.perm := hdir j hCnone
        have hlocalPerm :
            (TileLink.Atomic.acquirePermLocals (refMap n s) i j).perm =
              (s.locals j).line.perm := by
          have hlocals :=
            refMap_sendGrant_acquirePerm_locals_eq hfull0 htxnLine hplan hcur hreq hphase hkind
          have hlineEq :
              refMapLine (sendGrantState s i tx) j = (s.locals j).line := by
            simp [refMapLine, sendGrantState, sendGrantShared, sendGrantLocals, hji, hreqj]
          have hpermEq := congrArg CacheLine.perm (congrFun hlocals j)
          have hpermEq' :
              (s.locals j).line.perm =
                (TileLink.Atomic.acquirePermLocals (refMap n s) i j).perm := by
            simpa [refMap, hlineEq] using hpermEq
          simpa using hpermEq'.symm
        have hki : k ≠ i.1 := by
          intro h
          apply hji
          exact Fin.ext h
        calc
          grantPendingDir n { tx with phase := .grantPendingAck } s.shared.dir k = s.shared.dir k := by
            simp [grantPendingDir, updateDirAt, hk, hreq, hki]
          _ = (s.locals j).line.perm := hdirj
          _ = (TileLink.Atomic.acquirePermLocals (refMap n s) i j).perm := hlocalPerm.symm
          _ = TileLink.Atomic.syncDir (refMap n s).shared.dir
                (TileLink.Atomic.acquirePermLocals (refMap n s) i) k := by
              simpa [TileLink.Atomic.syncDir, hk, j]
    · have hki : k ≠ i.1 := by
        intro hkiEq
        apply hk
        simpa [hkiEq] using i.is_lt
      simp [refMap, refMapShared, sendGrantState, sendGrantShared, grantPendingDir,
        TileLink.Atomic.syncDir, preTxnDir, updateDirAt, hcur, hreq, hphase, hk, hki]
  constructor
  · simp [refMapShared, sendGrantState, sendGrantShared, absPendingGrantMeta,
      TileLink.Atomic.deliveredGrantMeta, hcur, hphase]
  constructor
  · simp [refMapShared, sendGrantState, sendGrantShared, hcur, hreq]
  · simp [refMapShared, sendGrantState, sendGrantShared, hcur, hrel]

end TileLink.Messages
