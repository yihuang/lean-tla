import Leslie.Examples.CacheCoherence.TileLink.Messages.Refinement.SimGrant

namespace TileLink.Messages

open TLA TileLink SymShared Classical

theorem refMap_init (n : Nat) (s : SymState HomeState NodeState n)
    (hs : (tlMessages.toSpec n).init s) :
    (TileLink.Atomic.tlAtomic.toSpec n).init (refMap n s) := by
  simp [SymSharedSpec.toSpec] at hs ⊢
  rcases hs with ⟨⟨hmem, hdir, htxn, hgrant, hrel, _⟩, hloc⟩
  constructor
  · -- init_shared for refMapShared
    simp [refMap, refMapShared, htxn, hrel, hgrant]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- mem = 0: no dirty (all dirty = false), no release in flight, so mem = s.shared.mem = 0
      have hnd : ¬∃ j : Fin n, (s.locals j).line.dirty = true := by
        intro ⟨j, hd⟩
        have := (hloc j).1
        rw [this] at hd; simp at hd
      rw [dif_neg hnd]
      have hnorel : findDirtyReleaseVal n s = none := by
        apply findDirtyReleaseVal_none_of_all_chanC_none
        intro j; exact (hloc j).2.2.2.1
      rw [hnorel]; exact hmem
    · -- dir k = .N
      intro k
      by_cases hk : k < n
      · simp [TileLink.Atomic.syncDir, hk]
        have := (hloc ⟨k, hk⟩).1
        rw [this]
      · simp [TileLink.Atomic.syncDir, hk]; exact hdir k
    · rfl  -- pendingGrantMeta = none
    · rfl  -- pendingGrantAck = none
    · -- pendingReleaseAck = none
      simp
      apply queuedReleaseIdx_eq_none_of_all_chanC_none
      intro j; exact (hloc j).2.2.2.1
  · -- init_local for refMapLine
    intro i
    simp [refMap, refMapLine, htxn]
    have := (hloc i).1
    rw [this]
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem refMap_sendAcquireBlock_eq {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n} {grow : GrowParam} {source : SourceId}
    (hstep : SendAcquireBlock s s' i grow source) :
    refMap n s' = refMap n s := by
  rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
  rw [hs']
  exact refMap_eq_of_invisible_local_change
    (fun j => by simp [setFn]; split <;> simp_all)
    (fun j => by simp [setFn]; split <;> simp_all)
    (fun j => by simp [setFn]; split <;> simp_all)

theorem refMap_sendAcquirePerm_eq {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n} {grow : GrowParam} {source : SourceId}
    (hstep : SendAcquirePerm s s' i grow source) :
    refMap n s' = refMap n s := by
  rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
  rw [hs']
  exact refMap_eq_of_invisible_local_change
    (fun j => by simp [setFn]; split <;> simp_all)
    (fun j => by simp [setFn]; split <;> simp_all)
    (fun j => by simp [setFn]; split <;> simp_all)

theorem atomic_writableProbeMask_refMap_eq {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n)
    (htxn : s.shared.currentTxn = none) :
    TileLink.Atomic.writableProbeMask (refMap n s) i = writableProbeMask s i := by
  funext k
  by_cases hk : k < n
  · let j : Fin n := ⟨k, hk⟩
    unfold TileLink.Atomic.writableProbeMask writableProbeMask
    simp [hk, refMap, refMapLine, htxn]
  · simp [TileLink.Atomic.writableProbeMask, writableProbeMask, hk]

theorem atomic_cachedProbeMask_refMap_eq {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n)
    (htxn : s.shared.currentTxn = none) :
    TileLink.Atomic.cachedProbeMask (refMap n s) i = cachedProbeMask s i := by
  funext k
  by_cases hk : k < n
  · let j : Fin n := ⟨k, hk⟩
    unfold TileLink.Atomic.cachedProbeMask cachedProbeMask
    simp [hk, refMap, refMapLine, htxn]
  · simp [TileLink.Atomic.cachedProbeMask, cachedProbeMask, hk]

theorem atomic_not_hasDirtyOther_of_noDirty {n : Nat}
    {s : SymState HomeState NodeState n} {i : Fin n}
    (hnoDirty : noDirtyInv n s)
    (htxn : s.shared.currentTxn = none) :
    ¬ TileLink.Atomic.hasDirtyOther n i (refMap n s) := by
  intro h
  rcases h with ⟨j, hji, hdirty⟩
  have hdirty' : (s.locals j).line.dirty = true := by
    simpa [TileLink.Atomic.hasDirtyOther, refMap, refMapLine, htxn] using hdirty
  rw [hnoDirty j] at hdirty'
  contradiction

theorem atomic_not_hasDirtyOther_of_not_hasDirtyOther {n : Nat}
    {s : SymState HomeState NodeState n} {i : Fin n}
    (hnd : ¬hasDirtyOther s i)
    (htxn : s.shared.currentTxn = none) :
    ¬ TileLink.Atomic.hasDirtyOther n i (refMap n s) := by
  intro h
  rcases h with ⟨j, hji, hdirty⟩
  have hdirty' : (s.locals j).line.dirty = true := by
    simpa [TileLink.Atomic.hasDirtyOther, refMap, refMapLine, htxn] using hdirty
  exact hnd ⟨j, hji, hdirty'⟩

theorem atomic_hasCachedOther_refMap_iff {n : Nat}
    {s : SymState HomeState NodeState n} {i : Fin n}
    (htxn : s.shared.currentTxn = none) :
    TileLink.Atomic.hasCachedOther n i (refMap n s) ↔ hasCachedOther s i := by
  simp [TileLink.Atomic.hasCachedOther, hasCachedOther, refMap, refMapLine, htxn]

theorem atomic_allOthersInvalid_refMap_iff {n : Nat}
    {s : SymState HomeState NodeState n} {i : Fin n}
    (htxn : s.shared.currentTxn = none) :
    TileLink.Atomic.allOthersInvalid n i (refMap n s) ↔ allOthersInvalid s i := by
  simp [TileLink.Atomic.allOthersInvalid, allOthersInvalid, refMap, refMapLine, htxn]

theorem atomic_not_hasDirtyOther_of_preNoDirty {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {i : Fin n}
    (hused : usedDirtySourceInv n s)
    (hcur : s.shared.currentTxn = some tx) (hreq : tx.requester = i.1)
    (hphase : tx.phase ≠ .grantPendingAck) (hclean : tx.usedDirtySource = false) :
    ¬ TileLink.Atomic.hasDirtyOther n i (refMap n s) := by
  intro ⟨j, hji, hdirty⟩
  have hjreq : j.1 ≠ tx.requester := fun h => hji (Fin.ext (h.trans hreq))
  have hdirty' : (tx.preLines j.1).dirty = true := by
    simpa [refMap, refMapLine, hcur, hphase] using hdirty
  have := hused tx hcur hclean j.1 j.isLt hjreq
  rw [this] at hdirty'
  exact absurd hdirty' (by simp)

theorem atomic_hasCachedOther_refMap_snapshot_iff {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {i : Fin n}
    (hcur : s.shared.currentTxn = some tx) (hreq : tx.requester = i.1)
    (hphase : tx.phase ≠ .grantPendingAck) :
    TileLink.Atomic.hasCachedOther n i (refMap n s) ↔ snapshotHasCachedOther n tx := by
  constructor
  · intro h
    rcases h with ⟨j, hji, hperm⟩
    refine ⟨j, ?_, ?_⟩
    · exact fun h => hji (Fin.ext (h.trans hreq))
    · simpa [refMap, refMapLine, hcur, hphase] using hperm
  · intro h
    rcases h with ⟨j, hji, hperm⟩
    refine ⟨j, ?_, ?_⟩
    · intro h
      apply hji
      exact (congrArg Fin.val h).trans hreq.symm
    · simpa [TileLink.Atomic.hasCachedOther, refMap, refMapLine, hcur, hphase]
        using hperm

theorem atomic_allOthersInvalid_refMap_snapshot_iff {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {i : Fin n}
    (hcur : s.shared.currentTxn = some tx) (hreq : tx.requester = i.1)
    (hphase : tx.phase ≠ .grantPendingAck) :
    TileLink.Atomic.allOthersInvalid n i (refMap n s) ↔ snapshotAllOthersInvalid n tx := by
  constructor
  · intro h j hji
    have hji' : j ≠ i := by
      intro hEq
      apply hji
      exact (congrArg Fin.val hEq).trans hreq.symm
    have hN := h j hji'
    simpa [refMap, refMapLine, hcur, hphase] using hN
  · intro h j hji
    have hji' : j.1 ≠ tx.requester := by
      exact fun hEq => hji (Fin.ext (hEq.trans hreq))
    have hN := h j hji'
    simpa [TileLink.Atomic.allOthersInvalid, refMap, refMapLine, hcur, hphase] using hN

theorem atomic_writableProbeMask_refMap_snapshot_eq {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {i : Fin n}
    (hcur : s.shared.currentTxn = some tx) (hreq : tx.requester = i.1)
    (hphase : tx.phase ≠ .grantPendingAck) :
    TileLink.Atomic.writableProbeMask (refMap n s) i = snapshotWritableProbeMask n tx := by
  funext k
  by_cases hk : k < n
  · let j : Fin n := ⟨k, hk⟩
    by_cases hki : k = i.1
    · have hji : j = i := Fin.ext hki
      simp [TileLink.Atomic.writableProbeMask, snapshotWritableProbeMask, refMap, refMapLine,
        hcur, hphase, hreq, hk, hki, hji, j]
    · have hji : j ≠ i := by
        intro h
        apply hki
        simpa [j] using congrArg Fin.val h
      simp [TileLink.Atomic.writableProbeMask, snapshotWritableProbeMask, refMap, refMapLine,
        hcur, hphase, hreq, hk, hki, hji, j]
  · simp [TileLink.Atomic.writableProbeMask, snapshotWritableProbeMask, hk]

theorem atomic_cachedProbeMask_refMap_snapshot_eq {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn} {i : Fin n}
    (hcur : s.shared.currentTxn = some tx) (hreq : tx.requester = i.1)
    (hphase : tx.phase ≠ .grantPendingAck) :
    TileLink.Atomic.cachedProbeMask (refMap n s) i = snapshotCachedProbeMask n tx := by
  funext k
  by_cases hk : k < n
  · let j : Fin n := ⟨k, hk⟩
    by_cases hki : k = i.1
    · have hji : j = i := Fin.ext hki
      simp [TileLink.Atomic.cachedProbeMask, snapshotCachedProbeMask, refMap, refMapLine,
        hcur, hphase, hreq, hk, hki, hji, j]
    · have hji : j ≠ i := by
        intro h
        apply hki
        simpa [j] using congrArg Fin.val h
      simp [TileLink.Atomic.cachedProbeMask, snapshotCachedProbeMask, refMap, refMapLine,
        hcur, hphase, hreq, hk, hki, hji, j]
  · simp [TileLink.Atomic.cachedProbeMask, snapshotCachedProbeMask, hk]

theorem refMap_sendGrant_block_branch_next {n : Nat}
    {s s' : SymState HomeState NodeState n} {i : Fin n}
    (hfull : fullInv n s) (hclean : cleanDataInv n s) (htxnLine : txnLineInv n s)
    (hpre : preLinesNoDirtyInv n s) (htxnData : txnDataInv n s) (hplan : txnPlanInv n s)
    (husedDirty : usedDirtySourceInv n s) (hpreWF : preLinesWFInv n s)
    (hreqPerm : preLinesReqPermInv n s)
    (hstep : SendGrantToRequester s s' i) :
    ∀ {tx : ManagerTxn}, s.shared.currentTxn = some tx → tx.kind = .acquireBlock →
      tx.resultPerm = .B →
      (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n s') := by
  intro tx hcur hkind hperm
  rcases hstep with ⟨tx', hcur', hreq, hphase, hgrant, hrel, _, _, _, hs'⟩
  rw [hcur] at hcur'; cases hcur'
  simp only [SymSharedSpec.toSpec, TileLink.Atomic.tlAtomic]
  have hreqLt : tx.requester < n := by
    rcases (by simpa [txnPlanInv, hcur] using hplan) with ⟨hlt, _⟩; exact hlt
  let req : Fin n := ⟨tx.requester, hreqLt⟩
  have hreqi : req = i := Fin.ext hreq
  have hplanB := txnPlanInv_acquireBlock_branch hplan hcur hkind hperm
  have htxnD := by simpa [txnDataInv, hcur] using htxnData
  have hnotGPA : tx.phase ≠ .grantPendingAck := by simp [hphase]
  refine ⟨req, .finishGrant, ?_⟩
  let pg := absPendingGrantMeta tx
  refine ⟨pg, ?_, ?_, ?_, ?_, ?_⟩
  · simp [refMap, pg, hcur]
  · simp [refMap, hgrant]
  · simp [refMap, refMapShared, hcur, hrel, hnotGPA]
  · simp [pg, absPendingGrantMeta, req]
  · -- Case split on usedDirtySource
    cases husedDS : tx.usedDirtySource with
    | false =>
      -- Block-shared (2nd disjunct): ¬hasDirtyOther, hasCachedOther, usedDirtySource = false
      right; left
      have hwfPre := by simpa [preLinesWFInv, hcur] using hpreWF
      have hNoDirty : ¬TileLink.Atomic.hasDirtyOther n req (refMap n s) := by
        intro ⟨j, hji, hdj⟩
        simp only [refMap, refMapLine, hcur, hnotGPA, ite_false] at hdj
        have hpermT := (hwfPre j.1 j.is_lt).1 hdj |>.1
        by_cases hjr : j.1 = tx.requester
        · rw [hjr] at hpermT; exact absurd hpermT (by rw [hreqPerm tx hcur hkind]; exact TLPerm.noConfusion)
        · have huds := by simpa [usedDirtySourceInv, hcur] using husedDirty
          rw [huds husedDS j.1 j.is_lt hjr] at hdj; cases hdj
      refine ⟨hNoDirty, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- hasCachedOther
        rw [hreqi]; rw [atomic_hasCachedOther_refMap_snapshot_iff hcur hreq hnotGPA]
        exact hplanB.1
      · simp [pg, absPendingGrantMeta, absGrantKind, hkind]
      · simp [pg, absPendingGrantMeta, hperm]
      · simp [pg, absPendingGrantMeta, husedDS]
      · -- transferVal = mem
        simp only [pg, absPendingGrantMeta, refMap, refMapShared, hcur, hnotGPA, ite_false, husedDS]
        exact htxnD.1 husedDS
      · -- probesNeeded = writableProbeMask
        simp only [pg, absPendingGrantMeta]; rw [hreqi, hplanB.2]
        exact (atomic_writableProbeMask_refMap_snapshot_eq hcur hreq hnotGPA).symm
      · -- probesRemaining = writableProbeMask
        simp only [pg, absPendingGrantMeta, hnotGPA, ite_false]; rw [hreqi, hplanB.2]
        exact (atomic_writableProbeMask_refMap_snapshot_eq hcur hreq hnotGPA).symm
      · -- s' = finishGrantBlockSharedState
        rw [hs', hreqi]
        apply SymState.ext
        · exact refMapShared_sendGrant_block_branch_eq hfull hclean htxnLine htxnData hplan hcur hreq hphase hrel hkind hperm
        · exact refMap_sendGrant_block_branch_locals_eq hfull hclean htxnLine htxnData hplan hcur hreq hphase hkind hperm
    | true =>
      -- Block-dirty (1st disjunct): ∃ dirty j, usedDirtySource = true
      left
      obtain ⟨k, hklt, hk_dirty, htv_k⟩ := htxnD.2.1 husedDS
      have hwfPre := by simpa [preLinesWFInv, hcur] using hpreWF
      have hkne : k ≠ tx.requester := by
        intro heq
        have hpermT := (hwfPre k hklt).1 hk_dirty |>.1
        rw [heq] at hpermT; exact absurd hpermT (by rw [hreqPerm tx hcur hkind]; exact TLPerm.noConfusion)
      let j : Fin n := ⟨k, hklt⟩
      have hji : j ≠ req := by intro h; exact hkne (congrArg Fin.val h)
      have hpnd := by simpa [preLinesNoDirtyInv, hcur] using hpre
      -- probesNeeded = singleProbeMask k (SWMR: j is unique .T owner)
      have hpermT := (hwfPre k hklt).1 hk_dirty |>.1
      have hmask : snapshotWritableProbeMask n tx = TileLink.Atomic.singleProbeMask k := by
        funext m
        simp only [snapshotWritableProbeMask, TileLink.Atomic.singleProbeMask]
        by_cases hm : m < n
        · by_cases hmreq : m = tx.requester
          · simp [hm, hmreq]; omega
          · simp [hm, hmreq]
            by_cases hmk : m = k
            · subst hmk; simp [hpermT]
            · simp [hmk]; intro h; exact absurd h (by rw [hpnd k m hklt hm (Ne.symm hmk) hk_dirty]; decide)
        · simp [hm]; intro hmk; subst hmk; omega
      -- finishGrantBlockDirtyState = finishGrantBlockSharedState (j.data = mem at grantReady)
      have hmem_eq : ((refMap n s).locals j).data = (refMap n s).shared.mem := by
        simp only [refMap, refMapLine, refMapShared, hcur, hnotGPA, ite_false, husedDS, ite_true]
        exact htv_k.symm
      have hlocals_eq : TileLink.Atomic.acquireBlockDirtyLocals (refMap n s) i j =
          TileLink.Atomic.acquireBlockSharedLocals (refMap n s) i := by
        funext m
        simp only [TileLink.Atomic.acquireBlockDirtyLocals, TileLink.Atomic.acquireBlockSharedLocals]
        by_cases hmi : m = i
        · simp [hmi, hmem_eq]
        · by_cases hmj : m = j
          · -- m = j (dirty owner): dirty gives branchLine j.data, shared gives branchLine mem (perm .T)
            subst hmj; simp only [hmi, ite_false, ite_true]
            rw [hmem_eq]
            have : ((refMap n s).locals j).perm = .T := by
              simp [refMap, refMapLine, hcur, hnotGPA]; exact hpermT
            simp [this]
          · -- m ≠ i ∧ m ≠ j: both give s.locals m (perm ≠ .T from SWMR)
            simp only [hmi, hmj, ite_false]
            have : ((refMap n s).locals m).perm ≠ .T := by
              simp only [refMap, refMapLine, hcur, hnotGPA, ite_false]
              intro hpT
              exact absurd (hpnd k m.1 hklt m.is_lt (fun h => hmj (Fin.ext h.symm)) hk_dirty)
                (by rw [hpT]; exact TLPerm.noConfusion)
            simp [this]
      have hstate_eq : TileLink.Atomic.finishGrantBlockDirtyState (refMap n s) i j pg =
          TileLink.Atomic.finishGrantBlockSharedState (refMap n s) i pg := by
        simp only [TileLink.Atomic.finishGrantBlockDirtyState, TileLink.Atomic.finishGrantBlockSharedState,
          hmem_eq, hlocals_eq]
      refine ⟨j, hji, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [refMap, refMapLine, hcur, hnotGPA, ite_false]; exact hk_dirty
      · simp [pg, absPendingGrantMeta, absGrantKind, hkind]
      · simp [pg, absPendingGrantMeta, hperm]
      · simp [pg, absPendingGrantMeta, husedDS]
      · simp only [pg, absPendingGrantMeta, refMap, refMapLine, hcur, hnotGPA, ite_false]; exact htv_k
      · simp only [pg, absPendingGrantMeta]; rw [hplanB.2, hmask]
      · simp only [pg, absPendingGrantMeta, hnotGPA, ite_false]; rw [hplanB.2, hmask]
      · rw [hs', hreqi, hstate_eq]
        apply SymState.ext
        · exact refMapShared_sendGrant_block_branch_eq hfull hclean htxnLine htxnData hplan hcur hreq hphase hrel hkind hperm
        · exact refMap_sendGrant_block_branch_locals_eq hfull hclean htxnLine htxnData hplan hcur hreq hphase hkind hperm

theorem refMap_sendGrant_block_tip_next {n : Nat}
    {s s' : SymState HomeState NodeState n} {i : Fin n}
    (hfull : fullInv n s) (htxnLine : txnLineInv n s)
    (htxnData : txnDataInv n s) (hplan : txnPlanInv n s)
    (hreqPerm : preLinesReqPermInv n s)
    (hstep : SendGrantToRequester s s' i) :
    ∀ {tx : ManagerTxn}, s.shared.currentTxn = some tx → tx.kind = .acquireBlock →
      tx.resultPerm = .T →
      (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n s') := by
  intro tx hcur hkind hperm
  rcases hstep with ⟨tx', hcur', hreq, hphase, hgrant, hrel, _, _, _, hs'⟩
  rw [hcur] at hcur'; cases hcur'
  -- Exhibit the atomic finishGrant step with block-tip sub-case
  simp only [SymSharedSpec.toSpec, TileLink.Atomic.tlAtomic]
  -- Build the requester Fin n
  have hreqLt : tx.requester < n := by
    rcases (by simpa [txnPlanInv, hcur] using hplan) with ⟨hlt, _⟩; exact hlt
  let req : Fin n := ⟨tx.requester, hreqLt⟩
  have hreqi : req = i := Fin.ext hreq
  refine ⟨req, .finishGrant, ?_⟩
  -- The pg witness is absPendingGrantMeta tx
  let pg := absPendingGrantMeta tx
  refine ⟨pg, ?_, ?_, ?_, ?_, ?_⟩
  · -- pendingGrantMeta = some pg
    simp [refMap, pg, hcur]
  · -- pendingGrantAck = none
    simp [refMap, hgrant]
  · -- pendingReleaseAck = none
    simp [refMap, refMapShared, hcur, hrel, show tx.phase ≠ .grantPendingAck from by simp [hphase]]
  · -- pg.requester = req.1
    simp [pg, absPendingGrantMeta, req]
  · -- Block-tip sub-case (3rd disjunct)
    right; right; left
    -- allOthersInvalid n req (refMap n s)
    have hallInvalid : snapshotAllOthersInvalid n tx :=
      (txnPlanInv_acquireBlock_tip hplan hcur hkind hperm).1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- allOthersInvalid
      rw [hreqi]
      rw [atomic_allOthersInvalid_refMap_snapshot_iff hcur hreq (by simp [hphase])]
      exact hallInvalid
    · -- pg.kind = .block
      simp [pg, absPendingGrantMeta, absGrantKind, hkind]
    · -- pg.requesterPerm = .T
      simp [pg, absPendingGrantMeta, hperm]
    · -- pg.usedDirtySource = false
      simp only [pg, absPendingGrantMeta]
      -- Case split on usedDirtySource
      cases husedDirty : tx.usedDirtySource with
      | false => rfl
      | true =>
        -- usedDirtySource = true → ∃ dirty preLine k (from txnDataInv), but all preLines
        -- have perm .N (hallInvalid + hreqPerm), and WellFormed gives perm .N → dirty = false.
        exfalso
        have htxnD := by simpa [txnDataInv, hcur] using htxnData
        obtain ⟨k, hk, hkdirty, _⟩ := htxnD.2.1 husedDirty
        -- All preLines have perm = .N
        have hreqPermN := hreqPerm tx hcur hkind
        have hpermN_k : (tx.preLines k).perm = .N := by
          by_cases hkeq : k = tx.requester
          · rw [hkeq]; exact hreqPermN
          · exact hallInvalid ⟨k, hk⟩ hkeq
        -- Derive WellFormed: at grantReady with noProbeMask, live line = preLines
        have hmask := (txnPlanInv_acquireBlock_tip hplan hcur hkind hperm).2
        have hsnap := txnSnapshotLine_eq_of_grantReady hfull htxnLine hcur hphase ⟨k, hk⟩
        simp [show tx.probesNeeded k = false from by rw [hmask]; simp [TileLink.Atomic.noProbeMask]]
          at hsnap
        have hwf : (s.locals ⟨k, hk⟩).line.WellFormed := hfull.1.1 ⟨k, hk⟩
        rw [hsnap] at hwf
        -- WellFormed + perm .N → dirty = false, contradicting hkdirty
        exact absurd hkdirty (by rw [(hwf.2.2 hpermN_k).2]; decide)
    · -- pg.transferVal = (refMap n s).shared.mem
      have htxnD := by simpa [txnDataInv, hcur] using htxnData
      simp [pg, absPendingGrantMeta, refMap, refMapShared, hcur, hphase]
      exact htxnD.1
    · -- pg.probesNeeded = noProbeMask
      simp [pg, absPendingGrantMeta]
      exact (txnPlanInv_acquireBlock_tip hplan hcur hkind hperm).2
    · -- pg.probesRemaining = noProbeMask
      simp [pg, absPendingGrantMeta, hphase]
      exact (txnPlanInv_acquireBlock_tip hplan hcur hkind hperm).2
    · -- s' = finishGrantBlockTipState (refMap n s) req pg
      rw [hs', hreqi]
      apply SymState.ext
      · exact refMapShared_sendGrant_block_tip_eq hfull htxnLine htxnData hplan hcur hreq hphase hrel hkind hperm
      · exact refMap_sendGrant_block_tip_locals_eq hfull htxnLine htxnData hplan hcur hreq hphase hkind hperm

theorem refMap_sendGrant_acquirePerm_next {n : Nat}
    {s s' : SymState HomeState NodeState n} {i : Fin n}
    (hfull : fullInv n s) (hpre : preLinesNoDirtyInv n s)
    (htxnLine : txnLineInv n s) (htxnData : txnDataInv n s) (hplan : txnPlanInv n s)
    (husedDirty : usedDirtySourceInv n s) (hpreWF : preLinesWFInv n s)
    (hstep : SendGrantToRequester s s' i) :
    ∀ {tx : ManagerTxn}, s.shared.currentTxn = some tx → tx.kind = .acquirePerm →
      (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n s') := by
  intro tx hcur hkind
  rcases hstep with ⟨tx', hcur', hreq, hphase, hgrant, hrel, _, _, _, hs'⟩
  rw [hcur] at hcur'; cases hcur'
  simp only [SymSharedSpec.toSpec, TileLink.Atomic.tlAtomic]
  have hreqLt : tx.requester < n := by
    rcases (by simpa [txnPlanInv, hcur] using hplan) with ⟨hlt, _⟩; exact hlt
  let req : Fin n := ⟨tx.requester, hreqLt⟩
  have hreqi : req = i := Fin.ext hreq
  have hplanP := txnPlanInv_acquirePerm hplan hcur hkind
  have htxnD := by simpa [txnDataInv, hcur] using htxnData
  refine ⟨req, .finishGrant, ?_⟩
  let pg := absPendingGrantMeta tx
  refine ⟨pg, ?_, ?_, ?_, ?_, ?_⟩
  · simp [refMap, pg, hcur]
  · simp [refMap, hgrant]
  · simp [refMap, refMapShared, hcur, hrel, show tx.phase ≠ .grantPendingAck from by simp [hphase]]
  · simp [pg, absPendingGrantMeta, req]
  · -- Case split on usedDirtySource for perm sub-case
    have hnotGPA : tx.phase ≠ .grantPendingAck := by simp [hphase]
    cases husedDS : tx.usedDirtySource with
    | false =>
      -- Perm-clean (5th disjunct): ¬hasDirtyOther, usedDirtySource = false
      right; right; right; right
      have hNoDirty : ¬TileLink.Atomic.hasDirtyOther n req (refMap n s) := by
        intro ⟨j, hji, hdj⟩
        simp only [refMap, refMapLine, hcur, hnotGPA, ite_false] at hdj
        -- hdj : (tx.preLines j.1).dirty = true
        have hwf := by simpa [preLinesWFInv, hcur] using hpreWF
        have hpermT := (hwf j.1 j.is_lt).1 hdj |>.1
        by_cases hjr : j.1 = tx.requester
        · -- requester: perm ≠ .T contradicts dirty → perm .T
          rw [hjr] at hpermT; exact absurd hpermT hplanP.2.2
        · -- non-requester: usedDirtySourceInv → dirty = false
          have huds := by simpa [usedDirtySourceInv, hcur] using husedDirty
          rw [huds husedDS j.1 j.is_lt hjr] at hdj; cases hdj
      refine ⟨hNoDirty, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [pg, absPendingGrantMeta, absGrantKind, hkind]
      · simp [pg, absPendingGrantMeta, hplanP.1]
      · simp [pg, absPendingGrantMeta, husedDS]
      · -- transferVal = mem
        simp only [pg, absPendingGrantMeta, refMap, refMapShared, hcur, hnotGPA, ite_false, husedDS]
        exact htxnD.1 husedDS
      · -- probesNeeded = cachedProbeMask
        simp only [pg, absPendingGrantMeta]; rw [hreqi, hplanP.2.1]
        exact (atomic_cachedProbeMask_refMap_snapshot_eq hcur hreq hnotGPA).symm
      · -- probesRemaining = cachedProbeMask
        simp only [pg, absPendingGrantMeta, hnotGPA, ite_false]; rw [hreqi, hplanP.2.1]
        exact (atomic_cachedProbeMask_refMap_snapshot_eq hcur hreq hnotGPA).symm
      · -- s' = finishGrantPermCleanState
        rw [hs', hreqi]
        apply SymState.ext
        · exact refMapShared_sendGrant_acquirePerm_eq hfull htxnLine htxnData hplan hcur hreq hphase hrel hkind
        · exact refMap_sendGrant_acquirePerm_locals_eq hfull htxnLine hplan hcur hreq hphase hkind
    | true =>
      -- Perm-dirty (4th disjunct): ∃ dirty j, usedDirtySource = true
      right; right; right; left
      obtain ⟨k, hklt, hk_dirty, htv_k⟩ := htxnD.2.1 husedDS
      -- k ≠ requester (dirty → perm .T, but requester perm ≠ .T)
      have hwf_pre := by simpa [preLinesWFInv, hcur] using hpreWF
      have hkne : k ≠ tx.requester := by
        intro heq
        have hpermT := (hwf_pre k hklt).1 hk_dirty |>.1
        rw [heq] at hpermT; exact absurd hpermT hplanP.2.2
      let j : Fin n := ⟨k, hklt⟩
      have hji : j ≠ req := by intro h; exact hkne (congrArg Fin.val h)
      refine ⟨j, hji, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- (refMap n s).locals j dirty
        simp only [refMap, refMapLine, hcur, hnotGPA, ite_false]; exact hk_dirty
      · simp [pg, absPendingGrantMeta, absGrantKind, hkind]
      · simp [pg, absPendingGrantMeta, hplanP.1]
      · simp [pg, absPendingGrantMeta, husedDS]
      · -- transferVal = (refMap n s).locals j .data
        simp only [pg, absPendingGrantMeta, refMap, refMapLine, hcur, hnotGPA, ite_false]
        exact htv_k
      · -- probesNeeded = cachedProbeMask
        simp only [pg, absPendingGrantMeta]; rw [hreqi, hplanP.2.1]
        exact (atomic_cachedProbeMask_refMap_snapshot_eq hcur hreq hnotGPA).symm
      · -- probesRemaining = cachedProbeMask
        simp only [pg, absPendingGrantMeta, hnotGPA, ite_false]; rw [hreqi, hplanP.2.1]
        exact (atomic_cachedProbeMask_refMap_snapshot_eq hcur hreq hnotGPA).symm
      · -- s' = finishGrantPermDirtyState
        rw [hs', hreqi]
        -- Key: (refMap n s).shared.mem = ((refMap n s).locals j).data at grantReady+dirty
        have hmem_eq : (refMap n s).shared.mem = ((refMap n s).locals j).data := by
          simp only [refMap, refMapShared, refMapLine, hcur, hnotGPA, ite_false, husedDS, ite_true]
          exact htv_k
        apply SymState.ext
        · -- shared: unfold finishGrantPermDirtyState, rewrite mem to match acquirePerm_eq
          have h := refMapShared_sendGrant_acquirePerm_eq hfull htxnLine htxnData hplan hcur hreq hphase hrel hkind
          simp only [TileLink.Atomic.finishGrantPermDirtyState, ← hmem_eq]; exact h
        · exact refMap_sendGrant_acquirePerm_locals_eq hfull htxnLine hplan hcur hreq hphase hkind

theorem cachedProbeMask_eq_noProbeMask_of_allOthersInvalid {n : Nat}
    {s : SymState HomeState NodeState n} {i : Fin n}
    (hallInvalid : allOthersInvalid s i) :
    cachedProbeMask s i = noProbeMask := by
  funext k
  by_cases hk : k < n
  · by_cases hki : (⟨k, hk⟩ : Fin n) = i
    · simp [cachedProbeMask, noProbeMask, hk, hki]
    · have hpermN : (s.locals ⟨k, hk⟩).line.perm = .N := hallInvalid ⟨k, hk⟩ hki
      simp [cachedProbeMask, noProbeMask, hk, hki, hpermN]
  · simp [cachedProbeMask, noProbeMask, hk]

theorem refMap_recvAcquireState_locals_eq {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n) (kind : ReqKind) (grow : GrowParam) (source : SourceId)
    (htxn : s.shared.currentTxn = none) :
    (refMap n (recvAcquireState s i kind grow source)).locals = (refMap n s).locals := by
  funext j
  simp [refMap, refMapLine, recvAcquireState, recvAcquireShared, plannedTxn, htxn]

theorem absPendingGrantMeta_tx_update_eq
    (tx : ManagerTxn) (phase : TxnPhase) (probesRemaining : Nat → Bool)
    (htx : tx.phase ≠ .grantPendingAck)
    (hphase : phase ≠ .grantPendingAck) :
    absPendingGrantMeta { tx with phase := phase, probesRemaining := probesRemaining } =
      absPendingGrantMeta tx := by
  simp [absPendingGrantMeta, htx, hphase]

theorem refMapShared_recvAcquireState_eq_absPending {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n) (kind : ReqKind) (grow : GrowParam) (source : SourceId)
    (hnoDirty : noDirtyInv n s)
    (htxn : s.shared.currentTxn = none)
    (hrel : s.shared.pendingReleaseAck = none)
    (hallC : ∀ j : Fin n, (s.locals j).chanC = none) :
    refMapShared n (recvAcquireState s i kind grow source) =
      { mem := (refMap n s).shared.mem
      , dir := (refMap n s).shared.dir
      , pendingGrantMeta := some (absPendingGrantMeta (plannedTxn s i kind grow source))
      , pendingGrantAck := none
      , pendingReleaseAck := none } := by
  have hnd_all : ¬∃ j : Fin n, j ≠ i ∧ (s.locals j).line.dirty = true :=
    fun ⟨j, _, hd⟩ => absurd hd (by simp [hnoDirty j])
  have hdo : dirtyOwnerOpt s i = none := by unfold dirtyOwnerOpt; simp [hnd_all]
  have hud : (plannedTxn s i kind grow source).usedDirtySource = false := by
    simp [plannedTxn, plannedUsedDirtySource, hdo]
  have hnd : ¬∃ j : Fin n, (s.locals j).line.dirty = true :=
    fun ⟨j, hd⟩ => absurd hd (by simp [hnoDirty j])
  have hfdrv := findDirtyReleaseVal_none_of_all_chanC_none' s hallC
  have hcur_post : (recvAcquireState s i kind grow source).shared.currentTxn =
      some (plannedTxn s i kind grow source) := by simp [recvAcquireState, recvAcquireShared]
  have hphase : (plannedTxn s i kind grow source).phase ≠ .grantPendingAck := by simp [plannedTxn]
  ext
  · -- mem: both sides = s.shared.mem
    simp [refMapShared, recvAcquireState, recvAcquireShared, hud, htxn, hrel, hnd, hfdrv, refMap]
  · -- dir: preTxnDir = syncDir (via existing lemma)
    simp [refMapShared, recvAcquireState, recvAcquireShared, hphase, htxn, refMap]
    exact congrFun (preTxnDir_plannedTxn_eq_syncDir s i kind grow source) _
  · -- pendingGrantMeta
    simp [refMapShared, recvAcquireState, recvAcquireShared]
  · -- pendingGrantAck
    simp [refMapShared, recvAcquireState, recvAcquireShared]
  · -- pendingReleaseAck
    simp [refMapShared, recvAcquireState, recvAcquireShared, hrel]

theorem absPendingGrantMeta_planned_acquireBlock_branch_eq {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n) (grow : GrowParam) (source : SourceId)
    (hnoDirty : noDirtyInv n s)
    (htxn : s.shared.currentTxn = none)
    (hresult : grow.result = .B) :
    absPendingGrantMeta (plannedTxn s i .acquireBlock grow source) =
      { requester := i.1
      , kind := .block
      , requesterPerm := .B
      , usedDirtySource := false
      , transferVal := s.shared.mem
      , probesNeeded := TileLink.Atomic.writableProbeMask (refMap n s) i
      , probesRemaining := TileLink.Atomic.writableProbeMask (refMap n s) i } := by
  rcases plannedTxn_clean s i hnoDirty with ⟨hdirtySrc, htransfer⟩
  simp [absPendingGrantMeta, plannedTxn, hdirtySrc, htransfer, hresult, probeMaskForResult]
  rw [atomic_writableProbeMask_refMap_eq s i htxn]
  simp [absGrantKind]

theorem absPendingGrantMeta_planned_acquireBlock_tip_eq {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n) (grow : GrowParam) (source : SourceId)
    (hnoDirty : noDirtyInv n s)
    (hallInvalid : allOthersInvalid s i)
    (hresult : grow.result = .T) :
    absPendingGrantMeta (plannedTxn s i .acquireBlock grow source) =
      { requester := i.1
      , kind := .block
      , requesterPerm := .T
      , usedDirtySource := false
      , transferVal := s.shared.mem
      , probesNeeded := TileLink.Atomic.noProbeMask
      , probesRemaining := TileLink.Atomic.noProbeMask } := by
  rcases plannedTxn_clean s i hnoDirty with ⟨hdirtySrc, htransfer⟩
  simp [absPendingGrantMeta, plannedTxn, hdirtySrc, htransfer, hresult, probeMaskForResult,
    cachedProbeMask_eq_noProbeMask_of_allOthersInvalid hallInvalid]
  have hmask : noProbeMask = TileLink.Atomic.noProbeMask := rfl
  rw [hmask]
  simp [absGrantKind, TileLink.Atomic.noProbeMask, noProbeMask]

theorem absPendingGrantMeta_planned_acquirePerm_eq {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n) (grow : GrowParam) (source : SourceId)
    (hnoDirty : noDirtyInv n s)
    (htxn : s.shared.currentTxn = none)
    (hresult : grow.result = .T) :
    absPendingGrantMeta (plannedTxn s i .acquirePerm grow source) =
      { requester := i.1
      , kind := .perm
      , requesterPerm := .T
      , usedDirtySource := false
      , transferVal := s.shared.mem
      , probesNeeded := TileLink.Atomic.cachedProbeMask (refMap n s) i
      , probesRemaining := TileLink.Atomic.cachedProbeMask (refMap n s) i } := by
  rcases plannedTxn_clean s i hnoDirty with ⟨hdirtySrc, htransfer⟩
  simp [absPendingGrantMeta, plannedTxn, hdirtySrc, htransfer, hresult, probeMaskForResult]
  rw [atomic_cachedProbeMask_refMap_eq s i htxn]
  simp [absGrantKind]

theorem acquirePerm_requester_not_T {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n) (grow : GrowParam)
    (hlegal : grow.legalFrom (s.locals i).line.perm)
    (htxn : s.shared.currentTxn = none)
    (hresult : grow.result = .T) :
    ((refMap n s).locals i).perm ≠ .T := by
  have hperm : (s.locals i).line.perm ≠ .T := by
    cases grow
    · simp [GrowParam.result] at hresult
    · simp [GrowParam.legalFrom, GrowParam.source] at hlegal
      simpa [hlegal]
    · simp [GrowParam.legalFrom, GrowParam.source] at hlegal
      simpa [hlegal]
  simpa [refMap, refMapLine, htxn] using hperm

/-! ### Helpers using ¬hasDirtyOther (weaker than noDirtyInv) -/

theorem refMapShared_recvAcquireState_eq_absPending' {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n) (kind : ReqKind) (grow : GrowParam) (source : SourceId)
    (hnd : ¬hasDirtyOther s i)
    (hperm : (s.locals i).line.perm = .N)
    (hlineWF : lineWFInv n s)
    (htxn : s.shared.currentTxn = none)
    (hrel : s.shared.pendingReleaseAck = none)
    (hallC : ∀ j : Fin n, (s.locals j).chanC = none) :
    refMapShared n (recvAcquireState s i kind grow source) =
      { mem := (refMap n s).shared.mem
      , dir := (refMap n s).shared.dir
      , pendingGrantMeta := some (absPendingGrantMeta (plannedTxn s i kind grow source))
      , pendingGrantAck := none
      , pendingReleaseAck := none } := by
  -- Derive noDirtyInv from ¬hasDirtyOther + perm = .N + lineWF
  have hnoDirty : noDirtyInv n s := by
    intro j
    by_cases hji : j = i
    · subst hji
      -- i has perm .N → dirty = false (from lineWF: dirty → perm = .T)
      by_contra hd; simp only [Bool.not_eq_false] at hd
      have hpT := (hlineWF j).1 hd; rw [hperm] at hpT; exact absurd hpT (by simp [TLPerm.noConfusion])
    · -- j ≠ i → not dirty (from ¬hasDirtyOther)
      by_contra hd; simp only [Bool.not_eq_false] at hd
      exact hnd ⟨j, hji, hd⟩
  exact refMapShared_recvAcquireState_eq_absPending s i kind grow source hnoDirty htxn hrel hallC

theorem absPendingGrantMeta_planned_acquireBlock_branch_eq' {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n) (grow : GrowParam) (source : SourceId)
    (hnd : ¬hasDirtyOther s i)
    (htxn : s.shared.currentTxn = none)
    (hresult : grow.result = .B) :
    absPendingGrantMeta (plannedTxn s i .acquireBlock grow source) =
      { requester := i.1
      , kind := .block
      , requesterPerm := .B
      , usedDirtySource := false
      , transferVal := s.shared.mem
      , probesNeeded := TileLink.Atomic.writableProbeMask (refMap n s) i
      , probesRemaining := TileLink.Atomic.writableProbeMask (refMap n s) i } := by
  rcases plannedTxn_clean_of_not_hasDirtyOther s i hnd with ⟨hdirtySrc, htransfer⟩
  simp [absPendingGrantMeta, plannedTxn, hdirtySrc, htransfer, hresult, probeMaskForResult]
  rw [atomic_writableProbeMask_refMap_eq s i htxn]
  simp [absGrantKind]

theorem absPendingGrantMeta_planned_acquireBlock_tip_eq' {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n) (grow : GrowParam) (source : SourceId)
    (hnd : ¬hasDirtyOther s i)
    (hallInvalid : allOthersInvalid s i)
    (hresult : grow.result = .T) :
    absPendingGrantMeta (plannedTxn s i .acquireBlock grow source) =
      { requester := i.1
      , kind := .block
      , requesterPerm := .T
      , usedDirtySource := false
      , transferVal := s.shared.mem
      , probesNeeded := TileLink.Atomic.noProbeMask
      , probesRemaining := TileLink.Atomic.noProbeMask } := by
  rcases plannedTxn_clean_of_not_hasDirtyOther s i hnd with ⟨hdirtySrc, htransfer⟩
  simp [absPendingGrantMeta, plannedTxn, hdirtySrc, htransfer, hresult, probeMaskForResult,
    cachedProbeMask_eq_noProbeMask_of_allOthersInvalid hallInvalid]
  have hmask : noProbeMask = TileLink.Atomic.noProbeMask := rfl
  rw [hmask]
  simp [absGrantKind, TileLink.Atomic.noProbeMask, noProbeMask]

theorem absPendingGrantMeta_planned_acquirePerm_eq' {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n) (grow : GrowParam) (source : SourceId)
    (hnd : ¬hasDirtyOther s i)
    (htxn : s.shared.currentTxn = none)
    (hresult : grow.result = .T) :
    absPendingGrantMeta (plannedTxn s i .acquirePerm grow source) =
      { requester := i.1
      , kind := .perm
      , requesterPerm := .T
      , usedDirtySource := false
      , transferVal := s.shared.mem
      , probesNeeded := TileLink.Atomic.cachedProbeMask (refMap n s) i
      , probesRemaining := TileLink.Atomic.cachedProbeMask (refMap n s) i } := by
  rcases plannedTxn_clean_of_not_hasDirtyOther s i hnd with ⟨hdirtySrc, htransfer⟩
  simp [absPendingGrantMeta, plannedTxn, hdirtySrc, htransfer, hresult, probeMaskForResult]
  rw [atomic_cachedProbeMask_refMap_eq s i htxn]
  simp [absGrantKind]

/-! ### Dirty-source acquire helpers -/

/-- Under dirtyExclusiveInv + lineWFInv, the dirty owner has perm = .T. -/
private theorem dirty_owner_perm_T {n : Nat}
    {s : SymState HomeState NodeState n} {i j : Fin n}
    (hlineWF : lineWFInv n s)
    (hji : j ≠ i)
    (hdirty : (s.locals j).line.dirty = true) :
    (s.locals j).line.perm = .T :=
  ((hlineWF j).1 hdirty).1

/-- Under permSwmrInv + lineWFInv, if j is dirty then writableProbeMask s i = singleProbeMask j.1.
    Since j is the unique .T node, only j.1 appears in the writable mask. -/
private theorem writableProbeMask_eq_singleProbeMask_of_dirty {n : Nat}
    {s : SymState HomeState NodeState n} {i j : Fin n}
    (hlineWF : lineWFInv n s)
    (hSwmr : permSwmrInv n s)
    (hji : j ≠ i)
    (hdirty : (s.locals j).line.dirty = true) :
    writableProbeMask s i = TileLink.Atomic.singleProbeMask j.1 := by
  have hpermT : (s.locals j).line.perm = .T := dirty_owner_perm_T hlineWF hji hdirty
  funext k
  unfold writableProbeMask TileLink.Atomic.singleProbeMask
  by_cases hk : k < n
  · simp only [hk, ↓reduceDIte]
    by_cases hpj : k = j.1
    · -- k = j.1: writable because perm = .T, and j ≠ i
      subst hpj
      have hpi : (⟨j.1, hk⟩ : Fin n) = j := Fin.ext rfl
      rw [hpi]
      simp [hji, hpermT]
    · -- k ≠ j.1: perm = .N from SWMR, so not writable
      have hpne : (⟨k, hk⟩ : Fin n) ≠ j := fun h => hpj (congrArg Fin.val h)
      have hpermN : (s.locals ⟨k, hk⟩).line.perm = .N :=
        hSwmr j ⟨k, hk⟩ (Ne.symm hpne) hpermT
      simp [hpj, hpermN]
  · simp [hk, show ¬(k = j.1) from fun h => hk (h ▸ j.isLt)]

theorem refMap_recvAcquireBlock_branch_next {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n} {grow : GrowParam} {source : SourceId}
    (hinv : refinementInv n s)
    (hstep : RecvAcquireBlockAtManager s s' i grow source)
    (hNoDirty : ¬hasDirtyOther s i)
    (hbranch : hasCachedOther s i ∧ grow.result = .B) :
    (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n s') := by
  rcases hstep with ⟨htxn, hpga, hpra, hallC, _, _, hpermN, _, _, _, hs'⟩
  subst hs'
  simp only [SymSharedSpec.toSpec]
  refine ⟨i, .acquireBlock, ?_, ?_, ?_, ?_, ?_⟩
  · -- pendingGrantMeta = none
    simp [refMap, refMapShared, htxn]
  · -- pendingGrantAck = none
    simp [refMap, refMapShared, hpga]
  · -- pendingReleaseAck = none
    simp [refMap, refMapShared, htxn, hpra]
    exact queuedReleaseIdx_eq_none_of_all_chanC_none s hallC
  · -- perm = .N
    simp [refMap, refMapLine, htxn, hpermN]
  · -- sub-case: ¬hasDirtyOther ∧ hasCachedOther ∧ s' = acquireBlockSharedState
    right; left
    refine ⟨atomic_not_hasDirtyOther_of_not_hasDirtyOther hNoDirty htxn,
            (atomic_hasCachedOther_refMap_iff htxn).mpr hbranch.1, ?_⟩
    -- s' = acquireBlockSharedState (refMap n s) i
    have hShared := refMapShared_recvAcquireState_eq_absPending' s i .acquireBlock grow source
      hNoDirty hpermN hinv.full.1.1 htxn hpra hallC
    have hPG := absPendingGrantMeta_planned_acquireBlock_branch_eq' s i grow source
      hNoDirty htxn hbranch.2
    have hLocals := refMap_recvAcquireState_locals_eq s i .acquireBlock grow source htxn
    have hDir := refMapShared_dir_none htxn
    -- Derive noDirtyInv for mem lemma
    have hnoDirty : noDirtyInv n s := by
      intro j; by_cases hji : j = i
      · subst hji; by_contra hd; simp only [Bool.not_eq_false] at hd
        have := (hinv.full.1.1 j).1 hd; rw [hpermN] at this; simp [TLPerm.noConfusion] at this
      · by_contra hd; simp only [Bool.not_eq_false] at hd; exact hNoDirty ⟨j, hji, hd⟩
    have hMemEq : (refMapShared n s).mem = s.shared.mem := by
      rw [refMapShared_mem_none htxn]
      have hnd : ¬∃ j : Fin n, (s.locals j).line.dirty = true :=
        fun ⟨j, hd⟩ => absurd hd (by simp [hnoDirty j])
      simp [hnd, findDirtyReleaseVal_none_of_all_chanC_none' s hallC]
    simp only [refMap] at hShared hLocals ⊢
    have hSharedEq : refMapShared n (recvAcquireState s i .acquireBlock grow source) =
        (TileLink.Atomic.acquireBlockSharedState
          { shared := refMapShared n s, locals := refMapLine s } i).shared := by
      rw [hShared]
      simp only [TileLink.Atomic.acquireBlockSharedState, hPG, hDir, ← hMemEq]
      simp only [refMap]
    exact SymState.ext hSharedEq hLocals

theorem refMap_recvAcquireBlock_tip_next {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n} {grow : GrowParam} {source : SourceId}
    (hinv : refinementInv n s)
    (hstep : RecvAcquireBlockAtManager s s' i grow source)
    (htip : allOthersInvalid s i ∧ grow.result = .T) :
    (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n s') := by
  rcases hstep with ⟨htxn, hpga, hpra, hallC, _, _, hpermN, _, _, _, hs'⟩
  subst hs'
  have hNoDirty : ¬hasDirtyOther s i := by
    intro ⟨j, hji, hd⟩
    have hpN := htip.1 j hji
    have hpT := (hinv.full.1.1 j).1 hd
    rw [hpN] at hpT; exact absurd hpT.1 (by simp)
  simp only [SymSharedSpec.toSpec]
  refine ⟨i, .acquireBlock, ?_, ?_, ?_, ?_, ?_⟩
  · simp [refMap, refMapShared, htxn]
  · simp [refMap, refMapShared, hpga]
  · simp [refMap, refMapShared, htxn, hpra]
    exact queuedReleaseIdx_eq_none_of_all_chanC_none s hallC
  · simp [refMap, refMapLine, htxn, hpermN]
  · -- sub-case: allOthersInvalid ∧ s' = acquireBlockInvalidState
    right; right
    refine ⟨(atomic_allOthersInvalid_refMap_iff htxn).mpr htip.1, ?_⟩
    have hShared := refMapShared_recvAcquireState_eq_absPending' s i .acquireBlock grow source
      hNoDirty hpermN hinv.full.1.1 htxn hpra hallC
    have hPG := absPendingGrantMeta_planned_acquireBlock_tip_eq' s i grow source
      hNoDirty htip.1 htip.2
    have hLocals := refMap_recvAcquireState_locals_eq s i .acquireBlock grow source htxn
    have hDir := refMapShared_dir_none htxn
    have hnoDirty : noDirtyInv n s := by
      intro j; by_cases hji : j = i
      · subst hji; by_contra hd; simp only [Bool.not_eq_false] at hd
        have := (hinv.full.1.1 j).1 hd; rw [hpermN] at this; simp at this
      · by_contra hd; simp only [Bool.not_eq_false] at hd; exact hNoDirty ⟨j, hji, hd⟩
    have hMemEq : (refMapShared n s).mem = s.shared.mem := by
      rw [refMapShared_mem_none htxn]
      have hnd : ¬∃ j : Fin n, (s.locals j).line.dirty = true :=
        fun ⟨j, hd⟩ => absurd hd (by simp [hnoDirty j])
      simp [hnd, findDirtyReleaseVal_none_of_all_chanC_none' s hallC]
    simp only [refMap] at hShared hLocals ⊢
    have hSharedEq : refMapShared n (recvAcquireState s i .acquireBlock grow source) =
        (TileLink.Atomic.acquireBlockInvalidState
          { shared := refMapShared n s, locals := refMapLine s } i).shared := by
      rw [hShared]
      simp only [TileLink.Atomic.acquireBlockInvalidState, hPG, hDir, ← hMemEq]
    exact SymState.ext hSharedEq hLocals

theorem refMap_recvAcquirePerm_next {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n} {grow : GrowParam} {source : SourceId}
    (hinv : refinementInv n s)
    (hstep : RecvAcquirePermAtManager s s' i grow source) :
    (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n s') := by
  rcases hstep with ⟨htxn, hpga, hpra, hallC, hrelIF, hchanA, hlegal, hresT, hBs, hs'⟩
  subst hs'
  simp only [SymSharedSpec.toSpec]
  -- perm ≠ .T: from legalFrom, perm = grow.source. For BtoT: source = .B ≠ .T.
  have hpermNeT : (s.locals i).line.perm ≠ .T := by
    rw [GrowParam.legalFrom] at hlegal
    rw [hlegal]; cases grow <;> simp [GrowParam.source, GrowParam.result] at hresT ⊢
  by_cases hDirty : hasDirtyOther s i
  · -- Dirty case: exhibit acquirePerm with dirty sub-case
    obtain ⟨j, hji, hdj⟩ := hDirty
    refine ⟨i, .acquirePerm, ?_, ?_, ?_, ?_, ?_⟩
    · simp [refMap, refMapShared, htxn]
    · simp [refMap, refMapShared, hpga]
    · simp [refMap, refMapShared, htxn, hpra]
      exact queuedReleaseIdx_eq_none_of_all_chanC_none s hallC
    · -- perm ≠ .T at abstract level
      simp [refMap, refMapLine, htxn]; exact hpermNeT
    · -- dirty sub-case (first disjunct)
      left
      refine ⟨j, hji, ?_, ?_⟩
      · simp [refMap, refMapLine, htxn]; exact hdj
      · -- s' = acquirePermDirtyState (refMap n s) i j
        apply SymState.ext
        · -- shared: simp should close (same pattern as acquireBlock dirty)
          simp only [TileLink.Atomic.acquirePermDirtyState]
          rw [TileLink.Atomic.HomeState.mk.injEq]
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · -- mem
            simp [refMap, refMapShared, refMapLine, recvAcquireState, recvAcquireShared, plannedTxn, htxn]
          · -- dir
            simp [refMap, refMapShared, refMapLine, recvAcquireState, recvAcquireShared, plannedTxn, htxn]
          · simp [refMapShared, recvAcquireState, recvAcquireShared, htxn]
          · simp [refMapShared, recvAcquireState, recvAcquireShared, hpga]
          · simp [refMapShared, recvAcquireState, recvAcquireShared, htxn, hpra,
              findDirtyReleaseVal_none_of_all_chanC_none' s hallC,
              queuedReleaseIdx_eq_none_of_all_chanC_none s hallC]
        · exact refMap_recvAcquireState_locals_eq s i .acquirePerm grow source htxn
  · -- Clean case: ¬hasDirtyOther → acquirePermCleanState
    refine ⟨i, .acquirePerm, ?_, ?_, ?_, ?_, ?_⟩
    · simp [refMap, refMapShared, htxn]
    · simp [refMap, refMapShared, hpga]
    · simp [refMap, refMapShared, htxn, hpra]
      exact queuedReleaseIdx_eq_none_of_all_chanC_none s hallC
    · simp [refMap, refMapLine, htxn]; exact hpermNeT
    · right
      refine ⟨(atomic_not_hasDirtyOther_of_not_hasDirtyOther hDirty htxn), ?_⟩
      apply SymState.ext
      · simp only [TileLink.Atomic.acquirePermCleanState]
        rw [TileLink.Atomic.HomeState.mk.injEq]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · simp [refMap, refMapShared, refMapLine, recvAcquireState, recvAcquireShared, plannedTxn, htxn]
        · simp [refMap, refMapShared, refMapLine, recvAcquireState, recvAcquireShared, plannedTxn, htxn]
        · simp [refMapShared, recvAcquireState, recvAcquireShared, htxn]
        · simp [refMapShared, recvAcquireState, recvAcquireShared, hpga]
        · simp [refMapShared, recvAcquireState, recvAcquireShared, htxn, hpra,
            findDirtyReleaseVal_none_of_all_chanC_none' s hallC,
            queuedReleaseIdx_eq_none_of_all_chanC_none s hallC]
      · exact refMap_recvAcquireState_locals_eq s i .acquirePerm grow source htxn

theorem refMap_recvAcquireAtManager_next {n : Nat}
    {s s' : SymState HomeState NodeState n}
    {i : Fin n}
    (hinv : refinementInv n s)
    (hstep : RecvAcquireAtManager s s' i) :
    (TileLink.Atomic.tlAtomic.toSpec n).next (refMap n s) (refMap n s') := by
  rcases hstep with ⟨grow, source, hblock⟩ | ⟨grow, source, hperm⟩
  · -- RecvAcquireBlockAtManager
    rcases hblock with ⟨htxn, hpga, hpra, hallC, hrelIF, hchanA, hpermN, hlegal, hcases, hBs, hs'⟩
    rcases hcases with ⟨hDirty, hresB⟩ | ⟨hNoDirty, hCached, hresB⟩ | ⟨hAllInv, hresT⟩
    · -- dirty case: hasDirtyOther, grow.result = .B
      obtain ⟨j, hji, hdj⟩ := hDirty
      subst hs'
      simp only [SymSharedSpec.toSpec]
      refine ⟨i, .acquireBlock, ?_, ?_, ?_, ?_, ?_⟩
      · simp [refMap, refMapShared, htxn]
      · simp [refMap, refMapShared, hpga]
      · simp [refMap, refMapShared, htxn, hpra]
        exact queuedReleaseIdx_eq_none_of_all_chanC_none s hallC
      · simp [refMap, refMapLine, htxn, hpermN]
      · -- dirty sub-case (first disjunct)
        left
        refine ⟨j, hji, ?_, ?_⟩
        · simp [refMap, refMapLine, htxn]; exact hdj
        · -- s' = acquireBlockDirtyState (refMap n s) i j
          apply SymState.ext
          · -- shared equality: refMapShared (recvAcquireState ...) = (acquireBlockDirtyState ...).shared
            -- Key facts:
            -- 1. mem: refMapShared.mem = tx.transferVal (usedDirtySource=true) = j.data
            --    AND (refMap n s).shared.mem = j.data (dirty j → dite chooses j)
            -- 2. dir: preTxnDir = syncDir (pre-state dir with lines)
            -- 3. pendingGrantMeta: absPendingGrantMeta of planned txn
            -- 4. pendingGrantAck: none, pendingReleaseAck: none
            simp only [TileLink.Atomic.acquireBlockDirtyState]
            rw [TileLink.Atomic.HomeState.mk.injEq]
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · -- mem: (refMap n s).locals j).data = refMapShared.mem
              -- Both equal (s.locals j).line.data
              simp [refMap, refMapShared, refMapLine, recvAcquireState, recvAcquireShared,
                plannedTxn, htxn]
              -- Goal should involve plannedTransferVal and dite on dirty
              -- plannedTransferVal = dirtyOwnerOpt.data when dirty exists
              -- (refMap n s).shared.mem with dirty j = (choose ...).data
              -- By SWMR: choose = j (unique dirty) → same data
              -- (closed by simp above)
            · -- dir
              -- (closed by simp above)
            · -- pendingGrantMeta
              simp [refMapShared, recvAcquireState, recvAcquireShared, htxn]
            · -- pendingGrantAck
              simp [refMapShared, recvAcquireState, recvAcquireShared, hpga]
            · -- pendingReleaseAck
              simp [refMapShared, recvAcquireState, recvAcquireShared, htxn, hpra,
                findDirtyReleaseVal_none_of_all_chanC_none' s hallC,
                queuedReleaseIdx_eq_none_of_all_chanC_none s hallC]
          · exact refMap_recvAcquireState_locals_eq s i .acquireBlock grow source htxn
    · -- branch case: ¬hasDirtyOther ∧ hasCachedOther ∧ result = .B
      exact refMap_recvAcquireBlock_branch_next hinv
        ⟨htxn, hpga, hpra, hallC, hrelIF, hchanA, hpermN, hlegal,
          Or.inr (Or.inl ⟨hNoDirty, hCached, hresB⟩), hBs, hs'⟩
        hNoDirty ⟨hCached, hresB⟩
    · -- tip case: allOthersInvalid ∧ result = .T
      exact refMap_recvAcquireBlock_tip_next hinv
        ⟨htxn, hpga, hpra, hallC, hrelIF, hchanA, hpermN, hlegal,
          Or.inr (Or.inr ⟨hAllInv, hresT⟩), hBs, hs'⟩
        ⟨hAllInv, hresT⟩
  · -- RecvAcquirePermAtManager
    exact refMap_recvAcquirePerm_next hinv hperm

end TileLink.Messages
