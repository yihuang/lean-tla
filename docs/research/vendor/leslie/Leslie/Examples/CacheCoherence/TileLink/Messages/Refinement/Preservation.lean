import Leslie.Examples.CacheCoherence.TileLink.Messages.Refinement.Invariants
import Leslie.Examples.CacheCoherence.TileLink.Messages.Refinement.Preservation.TransferInv
import Leslie.Gadgets.ActionCases

namespace TileLink.Messages

open TLA TileLink SymShared Classical

/-- Helper: if all lines are unchanged between s and s', dirtyExclusiveInv transfers. -/
private theorem probedLine_dirty (line : CacheLine) (cap : CapParam) :
    (probedLine line cap).dirty = false := by
  cases cap <;> simp [probedLine, invalidatedLine, branchAfterProbe, tipAfterProbe]

private theorem releasedLine_dirty (line : CacheLine) (perm : TLPerm) :
    (releasedLine line perm).dirty = false := by
  cases perm <;> simp [releasedLine, invalidatedLine, branchAfterProbe, tipAfterProbe]

private theorem grantLine_dirty (line : CacheLine) (tx : ManagerTxn) :
    (grantLine line tx).dirty = false := by
  unfold grantLine
  cases tx.grantHasData <;> cases tx.resultPerm <;> simp [invalidatedLine]

/-- probedLine with probeCapOfResult never produces perm .T -/
private theorem probedLine_probeCapOfResult_perm_ne_T (line : CacheLine) (resultPerm : TLPerm) :
    (probedLine line (probeCapOfResult resultPerm)).perm ≠ .T := by
  cases resultPerm <;> simp [probeCapOfResult, probedLine, invalidatedLine, branchAfterProbe]

/-- probeSnapshotLine never produces dirty = true when preLinesNoDirty holds. -/
private theorem probeSnapshotLine_not_dirty {n : Nat}
    (tx : ManagerTxn) (node : NodeState) (p : Fin n)
    (hpreNoDirty : ∀ k : Nat, k < n → (tx.preLines k).dirty = false) :
    (probeSnapshotLine tx node p).dirty = false := by
  unfold probeSnapshotLine
  split
  · split
    · exact hpreNoDirty p.1 p.2
    · exact probedLine_dirty _ _
  · exact hpreNoDirty p.1 p.2

/-- During a transaction, no non-requester node can have dirty = true (given txnLineInv
    and preLinesNoDirtyInv). -/
private theorem absurd_dirty_nonrequester {n : Nat}
    (s : SymState HomeState NodeState n) (tx : ManagerTxn) (p : Fin n)
    (htxn : s.shared.currentTxn = some tx)
    (hphase : tx.phase = .grantReady ∨ tx.phase = .grantPendingAck)
    (htxnCore : txnCoreInv n s)
    (hwf : lineWFInv n s)
    (htxnLine : txnLineInv n s)
    (htxnPlan : txnPlanInv n s)
    (hp_ne : p.1 ≠ tx.requester)
    (hdirty : (s.locals p).line.dirty = true) : False := by
  simp only [txnCoreInv, htxn] at htxnCore
  simp only [txnLineInv, htxn] at htxnLine
  -- All probes resolved: probesRemaining p = false
  have hprobesNone : tx.probesRemaining p.1 = false := by
    rcases hphase with hgr | hgpa
    · exact htxnCore.2.2.2.2.2.2.1 hgr p
    · exact htxnCore.2.2.2.2.2.2.2 hgpa p
  -- txnLineInv: line = txnSnapshotLine = probeSnapshotLine (non-requester)
  have hline := htxnLine p
  have hsnap : txnSnapshotLine tx (s.locals p) p = probeSnapshotLine tx (s.locals p) p := by
    unfold txnSnapshotLine; split
    · next h => exact absurd h.2.symm hp_ne
    · rfl
  rw [hsnap] at hline
  unfold probeSnapshotLine at hline
  by_cases hneeded : tx.probesNeeded p.1 = true
  · -- probesNeeded = true, probesRemaining = false → snapshot = probedLine (dirty = false)
    simp [hneeded, hprobesNone] at hline
    rw [hline] at hdirty; exact absurd (probedLine_dirty _ _) (by rw [hdirty]; simp)
  · -- probesNeeded = false → snapshot = preLines p
    simp [show tx.probesNeeded p.1 = false from by
      cases h : tx.probesNeeded p.1 <;> simp_all] at hline
    -- preLines p is dirty with perm .T (from lineWF)
    have hpermT : (tx.preLines p.1).perm = .T := by
      have := hwf p; rw [hline] at this hdirty; exact (this.1 hdirty).1
    -- txnPlanInv: perm .T at non-requester → probesNeeded = true (contradiction)
    simp only [txnPlanInv, htxn] at htxnPlan
    have ⟨_, _, hkind⟩ := htxnPlan
    match hk : tx.kind with
    | .acquireBlock =>
      rw [hk] at hkind
      cases hres : tx.resultPerm with
      | N => exact absurd htxnCore.2.2.1 (by rw [hres]; cases tx.grow <;> simp [GrowParam.result])
      | B =>
        have ⟨_, hmask⟩ := hkind.1 hres; rw [hmask] at hneeded
        simp [snapshotWritableProbeMask, p.2, hp_ne, hpermT] at hneeded
      | T =>
        have ⟨hallN, _⟩ := hkind.2 hres
        exact absurd (hallN p hp_ne) (by rw [hpermT]; decide)
    | .acquirePerm =>
      rw [hk] at hkind
      have ⟨_, hmask, _⟩ := hkind; rw [hmask] at hneeded
      simp [snapshotCachedProbeMask, p.2, hp_ne, hpermT] at hneeded

/-- During probing, if probesRemaining i = true and chanC = none and the node has
    perm = .N, derive False from the txn invariants. The probe mask always requires
    perm ≠ .N (cachedMask) or perm = .T (writableMask) for probed nodes. -/
private theorem absurd_probed_permN {n : Nat}
    (s : SymState HomeState NodeState n) (tx : ManagerTxn) (i : Fin n)
    (htxn : s.shared.currentTxn = some tx)
    (hphase : tx.phase = .probing)
    (htxnCore : txnCoreInv n s)
    (htxnLine : txnLineInv n s)
    (htxnPlan : txnPlanInv n s)
    (hprobesRem : tx.probesRemaining i.1 = true)
    (hchanC : (s.locals i).chanC = none)
    (hpermN : (s.locals i).line.perm = .N) : False := by
  simp only [txnCoreInv, htxn] at htxnCore
  have hreq := htxnCore.1
  have hprobesNeeded : tx.probesNeeded i.1 = true := htxnCore.2.2.2.2.2.1 i.1 hprobesRem
  simp only [txnLineInv, htxn] at htxnLine
  have hline := htxnLine i
  -- i is not the requester (probesNeeded requester = false)
  have hi_ne : i.1 ≠ tx.requester := by
    intro h; rw [h] at hprobesNeeded
    have := htxnCore.2.2.2.2.1
    rw [this] at hprobesNeeded; simp at hprobesNeeded
  -- txnSnapshotLine for non-requester during probing = probeSnapshotLine
  have hsnap : txnSnapshotLine tx (s.locals i) i = probeSnapshotLine tx (s.locals i) i := by
    unfold txnSnapshotLine
    split
    · next h => exact absurd h.2.symm hi_ne
    · rfl
  rw [hsnap] at hline
  -- probeSnapshotLine with probesNeeded = true, probesRemaining = true, chanC = none = preLines
  have hpre : probeSnapshotLine tx (s.locals i) i = tx.preLines i.1 := by
    unfold probeSnapshotLine
    simp [hprobesNeeded, hprobesRem, hchanC]
  rw [hpre] at hline
  -- So (s.locals i).line = tx.preLines i, hence preLines perm = .N
  have hPrePermN : (tx.preLines i.1).perm = .N := by rw [← hline]; exact hpermN
  -- From txnPlanInv, probesNeeded i = true implies preLines i perm ≠ .N
  simp only [txnPlanInv, htxn] at htxnPlan
  have ⟨_, _, hkind⟩ := htxnPlan
  match hk : tx.kind with
  | .acquireBlock =>
    rw [hk] at hkind
    cases hres : tx.resultPerm with
    | N =>
      -- resultPerm = grow.result which is .B or .T, never .N
      have hResEq : tx.resultPerm = tx.grow.result := htxnCore.2.2.1
      rw [hres] at hResEq
      exact absurd hResEq (by cases tx.grow <;> simp [GrowParam.result])
    | B =>
      have ⟨_, hmask⟩ := hkind.1 hres
      rw [hmask] at hprobesNeeded
      simp [snapshotWritableProbeMask, i.2, hi_ne] at hprobesNeeded
      -- hprobesNeeded says (tx.preLines i).perm = .T, but we know it's .N
      exact absurd hprobesNeeded (by rw [hPrePermN]; decide)
    | T =>
      have ⟨_, hmask⟩ := hkind.2 hres
      rw [hmask] at hprobesNeeded
      simp [TileLink.Atomic.noProbeMask] at hprobesNeeded
  | .acquirePerm =>
    rw [hk] at hkind
    have ⟨_, hmask, _⟩ := hkind
    rw [hmask] at hprobesNeeded
    simp [snapshotCachedProbeMask, i.2, hi_ne] at hprobesNeeded
    -- hprobesNeeded : (tx.preLines i).perm ≠ .N
    exact hprobesNeeded hPrePermN

/-- During grantPendingAck, no non-requester node has perm = .T. -/
private theorem absurd_permT_during_grant {n : Nat}
    (s : SymState HomeState NodeState n) (tx : ManagerTxn) (p : Fin n)
    (htxn : s.shared.currentTxn = some tx)
    (hphase : tx.phase = .grantPendingAck)
    (htxnCore : txnCoreInv n s)
    (htxnLine : txnLineInv n s)
    (htxnPlan : txnPlanInv n s)
    (hpreNoDirty : preLinesNoDirtyInv n s)
    (hp_ne : p.1 ≠ tx.requester)
    (hpermT : (s.locals p).line.perm = .T) : False := by
  simp only [txnCoreInv, htxn] at htxnCore
  simp only [txnLineInv, htxn] at htxnLine
  simp only [txnPlanInv, htxn] at htxnPlan
  simp only [preLinesNoDirtyInv, htxn] at hpreNoDirty
  have hline := htxnLine p
  -- p is not requester, so txnSnapshotLine = probeSnapshotLine
  have hsnap : txnSnapshotLine tx (s.locals p) p = probeSnapshotLine tx (s.locals p) p := by
    unfold txnSnapshotLine
    split
    · next h => exact absurd h.2.symm hp_ne
    · rfl
  rw [hsnap] at hline
  -- During grantPendingAck, probesRemaining = false for all nodes
  have hRemFalse : tx.probesRemaining p.1 = false := by
    have hAllDone := htxnCore.2.2.2.2.2.2.2 hphase p
    exact hAllDone
  -- Case split on probesNeeded
  by_cases hNeeded : tx.probesNeeded p.1 = true
  · -- probesNeeded = true, probesRemaining = false → probeSnapshotLine = probedLine
    have hprobedLine : (s.locals p).line =
        probedLine (tx.preLines p.1) (probeCapOfResult tx.resultPerm) := by
      rw [hline]; unfold probeSnapshotLine
      simp [hNeeded, hRemFalse]
    rw [hprobedLine] at hpermT
    exact absurd hpermT (probedLine_probeCapOfResult_perm_ne_T _ _)
  · -- probesNeeded = false → probeSnapshotLine = preLines
    simp at hNeeded
    have hPreLines : (s.locals p).line = tx.preLines p.1 := by
      rw [hline]; unfold probeSnapshotLine; simp [hNeeded]
    -- (s.locals p).line = tx.preLines p, so preLines perm = .T
    have hPrePermT : (tx.preLines p.1).perm = .T := by rw [← hPreLines]; exact hpermT
    -- But txnPlanInv says this is impossible for non-requester with probesNeeded = false
    have ⟨_, _, hkind⟩ := htxnPlan
    match hk : tx.kind with
    | .acquireBlock =>
      rw [hk] at hkind
      cases hres : tx.resultPerm with
      | N =>
        have hResEq : tx.resultPerm = tx.grow.result := htxnCore.2.2.1
        rw [hres] at hResEq
        exact absurd hResEq (by cases tx.grow <;> simp [GrowParam.result])
      | B =>
        have ⟨_, hmask⟩ := hkind.1 hres
        rw [hmask] at hNeeded
        simp [snapshotWritableProbeMask, p.2, hp_ne] at hNeeded
        exact hNeeded hPrePermT
      | T =>
        have ⟨hallN, _⟩ := hkind.2 hres
        exact absurd (hallN p hp_ne) (by rw [hPrePermT]; simp)
    | .acquirePerm =>
      rw [hk] at hkind
      have ⟨_, hmask, _⟩ := hkind
      rw [hmask] at hNeeded
      simp [snapshotCachedProbeMask, p.2, hp_ne] at hNeeded
      rw [hPrePermT] at hNeeded; exact absurd hNeeded (by decide)

/-- During grantPendingAck with resultPerm = .T, all non-requester nodes have perm = .N. -/
private theorem all_others_permN_during_grant {n : Nat}
    (s : SymState HomeState NodeState n) (tx : ManagerTxn) (q : Fin n)
    (htxn : s.shared.currentTxn = some tx)
    (hphase : tx.phase = .grantPendingAck)
    (htxnCore : txnCoreInv n s)
    (htxnLine : txnLineInv n s)
    (htxnPlan : txnPlanInv n s)
    (hq_ne : q.1 ≠ tx.requester)
    (hresT : tx.resultPerm = .T) :
    (s.locals q).line.perm = .N := by
  simp only [txnCoreInv, htxn] at htxnCore
  simp only [txnLineInv, htxn] at htxnLine
  simp only [txnPlanInv, htxn] at htxnPlan
  have hline := htxnLine q
  have hsnap : txnSnapshotLine tx (s.locals q) q = probeSnapshotLine tx (s.locals q) q := by
    unfold txnSnapshotLine
    split
    · next h => exact absurd h.2.symm hq_ne
    · rfl
  rw [hsnap] at hline
  have hRemFalse : tx.probesRemaining q.1 = false :=
    htxnCore.2.2.2.2.2.2.2 hphase q
  have ⟨_, _, hkind⟩ := htxnPlan
  by_cases hNeeded : tx.probesNeeded q.1 = true
  · -- probed node: probedLine with probeCapOfResult .T = .toN = invalidatedLine → perm .N
    have hEq : (s.locals q).line =
        probedLine (tx.preLines q.1) (probeCapOfResult tx.resultPerm) := by
      rw [hline]; unfold probeSnapshotLine; simp [hNeeded, hRemFalse]
    rw [hEq, hresT]; simp [probeCapOfResult, probedLine, invalidatedLine]
  · -- not probed: probeSnapshotLine = preLines
    simp at hNeeded
    have hEq : (s.locals q).line = tx.preLines q.1 := by
      rw [hline]; unfold probeSnapshotLine; simp [hNeeded]
    rw [hEq]
    match hk : tx.kind with
    | .acquireBlock =>
      rw [hk] at hkind
      exact (hkind.2 hresT).1 q hq_ne
    | .acquirePerm =>
      rw [hk] at hkind
      have ⟨_, hmask, _⟩ := hkind
      rw [hmask] at hNeeded
      simp [snapshotCachedProbeMask, q.2, hq_ne] at hNeeded
      exact hNeeded

/-- Helper: if all lines are unchanged between s and s', dirtyExclusiveInv transfers. -/
private theorem dirtyExclusiveInv_of_same_lines (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hdirtyEx : dirtyExclusiveInv n s)
    (hlines : ∀ j : Fin n, (s'.locals j).line = (s.locals j).line) :
    dirtyExclusiveInv n s' := by
  intro p q hpq hdirtyP
  rw [hlines p] at hdirtyP; rw [hlines q]
  exact hdirtyEx p q hpq hdirtyP

theorem dirtyExclusiveInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hinv : strongRefinementInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    dirtyExclusiveInv n s' := by
  rcases hinv with ⟨⟨hfull, hdirtyEx, hSwmr, _, _, _, _⟩, htxnLine, _, hpreNoDirty, htxnPlan⟩
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  match a with
  | .sendAcquireBlock grow source =>
      exact dirtyExclusiveInv_of_same_lines n s s' hdirtyEx
        (fun j => sendAcquireBlock_line hstep)
  | .sendAcquirePerm grow source =>
      exact dirtyExclusiveInv_of_same_lines n s s' hdirtyEx
        (fun j => sendAcquirePerm_line hstep)
  | .recvAcquireAtManager =>
      -- recvAcquire doesn't change lines
      rcases hstep with hblk | hperm
      · rcases hblk with ⟨grow, source, _, _, _, _, _, _, _, _, _, _, hs'⟩
        exact dirtyExclusiveInv_of_same_lines n s s' hdirtyEx
          (fun j => by rw [hs']; simp [recvAcquireState, recvAcquireLocals_line])
      · rcases hperm with ⟨grow, source, _, _, _, _, _, _, _, _, _, hs'⟩
        exact dirtyExclusiveInv_of_same_lines n s s' hdirtyEx
          (fun j => by rw [hs']; simp [recvAcquireState, recvAcquireLocals_line])
  | .recvProbeAtMaster =>
      -- probedLine always sets dirty=false
      rcases hstep with ⟨tx, msg, htxn, hphase, hprobesRem, _, _, _, _, _, hchanC, hs'⟩
      intro p q hpq hdirtyP
      rw [hs'] at hdirtyP ⊢
      by_cases hpi : p = i
      · subst hpi
        simp only [recvProbeState, recvProbeLocals, recvProbeLocal, setFn, ite_true] at hdirtyP
        rw [probedLine_dirty] at hdirtyP; cases hdirtyP
      · simp [recvProbeState, recvProbeLocals, setFn, hpi] at hdirtyP
        by_cases hqi : q = i
        · -- q = i. dirty p → perm q = .N (from dirtyExclusiveInv). But probing a .N-perm node
          -- contradicts txnPlanInv (probe masks exclude .N-perm nodes).
          rw [hqi]
          have hpermN : (s.locals i).line.perm = .N := hdirtyEx p i (by rw [← hqi]; exact hpq) hdirtyP
          exact (absurd_probed_permN s tx i htxn hphase
            (hfull.1.2.2.2) htxnLine htxnPlan hprobesRem hchanC hpermN).elim
        · simp [recvProbeState, recvProbeLocals, setFn, hqi]
          exact hdirtyEx p q hpq hdirtyP
  | .recvProbeAckAtManager =>
      -- recvProbeAck clears chanC, doesn't change lines
      rcases hstep with ⟨tx, msg, _, _, _, _, _, _, _, hs'⟩
      exact dirtyExclusiveInv_of_same_lines n s s' hdirtyEx (fun j => by
        rw [hs']
        by_cases hji : j = i
        · subst hji; simp [recvProbeAckState, recvProbeAckLocals, recvProbeAckLocal, setFn]
        · simp [recvProbeAckState, recvProbeAckLocals, setFn, hji])
  | .sendGrantToRequester =>
      -- sendGrant doesn't change lines
      rcases hstep with ⟨tx, _, _, _, _, _, _, _, _, hs'⟩
      exact dirtyExclusiveInv_of_same_lines n s s' hdirtyEx
        (fun j => by rw [hs']; exact sendGrantState_line s i j tx)
  | .recvGrantAtMaster =>
      -- grantLine always sets dirty=false
      rcases hstep with ⟨tx, msg, htxn, hreq, hphase, _, _, _, _, _, _, hs'⟩
      rw [hs']
      intro p q hpq hdirtyP
      by_cases hpi : p = i
      · subst hpi
        simp only [recvGrantState, recvGrantLocals, recvGrantLocal, setFn, ite_true] at hdirtyP
        rw [grantLine_dirty] at hdirtyP; cases hdirtyP
      · simp [recvGrantState, recvGrantLocals, setFn, hpi] at hdirtyP
        by_cases hqi : q = i
        · -- dirty p (p ≠ i) during grantPendingAck: contradicts txn invariants
          -- (non-requester nodes can't be dirty during a transaction)
          have hp_ne : p.1 ≠ tx.requester := by
            intro h; rw [hreq] at h; exact hpi (Fin.ext h)
          exact (absurd_dirty_nonrequester s tx p htxn
            (Or.inr hphase) (hfull.1.2.2.2) hfull.1.1 htxnLine htxnPlan
            hp_ne hdirtyP).elim
        · simp [recvGrantState, recvGrantLocals, setFn, hqi]
          exact hdirtyEx p q hpq hdirtyP
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, hs'⟩
      exact dirtyExclusiveInv_of_same_lines n s s' hdirtyEx
        (fun j => by rw [hs']; exact recvGrantAckState_line s i j)
  | .sendRelease param =>
      -- releasedLine always sets dirty=false
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hlegal, _, htail⟩
      rcases htail with ⟨_, hs'⟩
      rw [hs']
      intro p q hpq hdirtyP
      by_cases hpi : p = i
      · subst hpi
        simp only [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, ite_true] at hdirtyP
        rw [releasedLine_dirty] at hdirtyP; cases hdirtyP
      · simp [sendReleaseState, sendReleaseLocals, setFn, hpi] at hdirtyP
        by_cases hqi : q = i
        · rw [hqi]
          simp only [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, ite_true]
          have hpermN : (s.locals i).line.perm = .N := hdirtyEx p i (by rw [← hqi]; exact hpq) hdirtyP
          rw [hpermN] at hlegal
          cases param <;>
            simp [PruneReportParam.legalFrom, PruneReportParam.source] at hlegal <;>
            simp [releasedLine, invalidatedLine, PruneReportParam.result]
        · simp [sendReleaseState, sendReleaseLocals, setFn, hqi]
          exact hdirtyEx p q hpq hdirtyP
  | .sendReleaseData param =>
      -- releasedLine always sets dirty=false; SendReleaseData guard has dirty=true
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hdirtyI, hs'⟩
      rw [hs']
      intro p q hpq hdirtyP
      by_cases hpi : p = i
      · subst hpi
        simp only [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, ite_true] at hdirtyP
        rw [releasedLine_dirty] at hdirtyP; cases hdirtyP
      · simp [sendReleaseState, sendReleaseLocals, setFn, hpi] at hdirtyP
        by_cases hqi : q = i
        · -- dirty i = true in pre, dirty p = true in pre (p ≠ i)
          -- dirtyExclusiveInv i p: dirty i → perm p = .N
          -- dirty p = true → perm p = .T (from lineWF in fullInv) → contradiction
          rw [hqi]
          simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn]
          have hpermPN := hdirtyEx i p (Ne.symm hpi) hdirtyI
          rcases hfull with ⟨⟨hlineWF, _, _, _⟩, _, _⟩
          exact absurd ((hlineWF p).1 hdirtyP).1 (by rw [hpermPN]; simp)
        · simp [sendReleaseState, sendReleaseLocals, setFn, hqi]
          exact hdirtyEx p q hpq hdirtyP
  | .recvReleaseAtManager =>
      -- recvRelease doesn't change lines (only chanC/chanD)
      rcases hstep with ⟨msg, param, _, _, _, _, _, _, _, _, _, _, hs'⟩
      exact dirtyExclusiveInv_of_same_lines n s s' hdirtyEx (fun j => by
        rw [hs']
        by_cases hji : j = i
        · subst hji; simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn]
        · simp [recvReleaseState, recvReleaseLocals, setFn, hji])
  | .recvReleaseAckAtMaster =>
      -- doesn't change lines
      rcases hstep with ⟨msg, _, _, _, _, _, _, hs'⟩
      exact dirtyExclusiveInv_of_same_lines n s s' hdirtyEx (fun j => by
        rw [hs']
        by_cases hji : j = i
        · subst hji; simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn]
        · simp [recvReleaseAckState, recvReleaseAckLocals, setFn, hji])
  | .store v =>
      -- Store sets dirty=true at node i (perm=.T guard), others unchanged
      rcases hstep with ⟨hcur, _, _, _, hperm, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      intro p q hpq hdirtyP
      by_cases hpi : p = i
      · -- p = i, perm i = .T (store guard). By SWMR: perm q = .N for q ≠ i.
        have hqi : q ≠ i := by intro h; exact hpq (by rw [hpi, h])
        simp [setFn, hqi]
        exact hSwmr i q hqi.symm hperm
      · -- p ≠ i: dirty p unchanged. q = i → store guard perm i = .T but
        -- dirtyExclusiveInv says perm i = .N, contradiction.
        simp [setFn, hpi] at hdirtyP
        by_cases hqi : q = i
        · rw [hqi]; simp [setFn, storeLocal]
          have hpermIN := hdirtyEx p i hpi hdirtyP
          rw [hperm] at hpermIN; cases hpermIN
        · simp [setFn, hqi]
          exact hdirtyEx p q hpq hdirtyP
  | .read =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩
      exact hdirtyEx
  | .uncachedGet source =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
      exact dirtyExclusiveInv_of_same_lines n s _ hdirtyEx
        (fun j => by simp [setFn]; split <;> simp_all)
  | .uncachedPut source v =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩
      exact dirtyExclusiveInv_of_same_lines n s _ hdirtyEx
        (fun j => by simp [setFn]; split <;> simp_all)
  | .recvUncachedAtManager =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩
      exact dirtyExclusiveInv_of_same_lines n s _ hdirtyEx
        (fun j => by simp [setFn]; split <;> simp_all)
  | .recvAccessAckAtMaster =>
      rcases hstep with ⟨_, _, _, rfl⟩
      exact dirtyExclusiveInv_of_same_lines n s _ hdirtyEx
        (fun j => by simp [setFn]; split <;> simp_all)

theorem txnDataInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hfull : fullInv n s) (hdirtyEx : dirtyExclusiveInv n s)
    (htxnData : txnDataInv n s) (hcleanC : cleanChanCInv n s)
    (hpreNoDirty : preLinesNoDirtyInv n s) (husedDirty : usedDirtySourceInv n s)
    (hdirtyOwner : dirtyOwnerExistsInv n s) (hpreWF : preLinesWFInv n s)
    (htxnTM : txnTransferMemInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    txnDataInv n s' := by
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  match a with
  | .sendAcquireBlock grow source =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [txnDataInv]
  | .sendAcquirePerm grow source =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [txnDataInv]
  | .recvAcquireAtManager =>
      rcases hstep with hblk | hperm
      · rcases hblk with ⟨grow, source, _, _, _, _, _, _, _, _, _, _, hs'⟩
        rw [hs']
        simp only [txnDataInv, recvAcquireState, recvAcquireShared]
        refine ⟨(plannedTxn_txnDataInv s i .acquireBlock grow source).1,
               (plannedTxn_txnDataInv s i .acquireBlock grow source).2,
               fun h => by simp [plannedTxn] at h⟩
      · rcases hperm with ⟨grow, source, _, _, _, _, _, _, _, _, _, hs'⟩
        rw [hs']
        simp only [txnDataInv, recvAcquireState, recvAcquireShared]
        refine ⟨(plannedTxn_txnDataInv s i .acquirePerm grow source).1,
               (plannedTxn_txnDataInv s i .acquirePerm grow source).2,
               fun h => by simp [plannedTxn] at h⟩
  | .recvProbeAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, _, hs'⟩
      rcases hs' with ⟨_, hs'⟩
      rw [hs']
      simpa [txnDataInv, hcur, recvProbeState] using htxnData
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨tx, msg, hcur, hphase, hrem, _, hC, _, _, hs'⟩
      rw [hs']
      simp only [txnDataInv, hcur, recvProbeAckState, recvProbeAckShared]
      have htd := by simpa [txnDataInv, hcur] using htxnData
      -- From chanCInv: msg.data = probeAckDataOfLine (tx.preLines i.1)
      rcases hfull with ⟨⟨_, _, _, htxnCore⟩, ⟨_, _, hchanC, _, _⟩, _⟩
      simp only [txnCoreInv, hcur] at htxnCore
      specialize hchanC i; rw [hC] at hchanC
      rcases hchanC with ⟨tx', hcur', _, _, _, _, _, _, hdata⟩ | ⟨_, hcurNone, _⟩
      · rw [hcur] at hcur'; cases hcur'
        -- i ≠ requester
        have hi_ne : i.1 ≠ tx.requester := by
          intro h
          have hneeded := htxnCore.2.2.2.2.2.1 i.1 hrem
          rw [h] at hneeded; rw [htxnCore.2.2.2.2.1] at hneeded; simp at hneeded
        refine ⟨?_, htd.2.1, ?_⟩
        · -- Part 1: usedDirtySource = false → transferVal = newMem
          intro huds
          rw [hdata]; simp [probeAckDataOfLine]
          split
          · next hdirtyPre =>
            -- preLines i dirty + usedDirtySource = false → contradiction via usedDirtySourceInv
            exfalso
            have := husedDirty tx hcur huds i.1 i.isLt hi_ne
            rw [this] at hdirtyPre; simp at hdirtyPre
          · exact htd.1 huds
        · -- Part 3: grantReady ∨ grantPendingAck → transferVal = newMem
          intro hgr
          rw [hdata]; simp only [probeAckDataOfLine]
          by_cases hdirtyPre : (tx.preLines i.1).dirty = true
          · -- Dirty probeAck: both sides reduce to preLines[i].data
            simp [hdirtyPre]
            -- Goal: tx.transferVal = (tx.preLines i.1).data
            by_cases huds : tx.usedDirtySource = true
            · obtain ⟨k, hk, _, hk_dirty, htv⟩ := hdirtyOwner tx hcur huds
              have hpreWF' := by simpa [preLinesWFInv, hcur] using hpreWF
              have hpreND' := by simpa [preLinesNoDirtyInv, hcur] using hpreNoDirty
              by_cases hki : k = i.1
              · rw [hki] at htv; exact htv
              · exfalso
                have hpermT_k := (hpreWF' k hk).1 hk_dirty |>.1
                have hpermN_k := hpreND' i.1 k i.is_lt hk (Ne.symm hki) hdirtyPre
                rw [hpermT_k] at hpermN_k; cases hpermN_k
            · exfalso
              have huds_false : tx.usedDirtySource = false := by
                cases h : tx.usedDirtySource <;> simp_all
              exact absurd hdirtyPre (by
                have := husedDirty tx hcur huds_false i.1 i.isLt hi_ne; rw [this]; simp)
          · -- Clean probeAck: transferVal and mem unchanged
            have hdirtyFalse : (tx.preLines i.1).dirty = false := by
              cases h : (tx.preLines i.1).dirty <;> simp_all
            simp [probeAckDataOfLine, hdirtyFalse]
            -- Need tx.transferVal = s.shared.mem
            by_cases huds_pre : tx.usedDirtySource = true
            · -- Use txnTransferMemInv
              simp only [txnTransferMemInv, hcur] at htxnTM
              apply htxnTM huds_pre
              -- Show all dirty nodes had probesRemaining = false in pre-state
              intro k hk hdirty
              -- k ≠ i (preLines[i] clean)
              have hki : k ≠ i.1 := by
                intro heq; rw [heq] at hdirty; rw [hdirtyFalse] at hdirty; cases hdirty
              -- From hgr: grantReady → all post remaining false → pre remaining[k] false
              rcases hgr with hgr | hgr
              · unfold probeAckPhase at hgr
                split at hgr
                · rename_i hall_rem
                  have := hall_rem ⟨k, hk⟩
                  simp [clearProbeIdx, hki] at this
                  exact this
                · cases hgr
              · unfold probeAckPhase at hgr
                split at hgr <;> cases hgr
            · -- usedDirtySource = false: Part 1 gives transferVal = mem
              simp only [Bool.not_eq_true] at huds_pre
              exact htd.1 huds_pre
      · rw [hcur] at hcurNone; simp at hcurNone
  | .sendGrantToRequester =>
      rcases hstep with ⟨tx, hcur, _, hphase, _, _, _, _, _, hs'⟩
      rw [hs']
      simp only [txnDataInv, hcur, sendGrantState, sendGrantShared]
      have htd := by simpa [txnDataInv, hcur] using htxnData
      exact ⟨htd.1, htd.2.1, fun _ => htd.2.2 (Or.inl hphase)⟩
  | .recvGrantAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [txnDataInv, hcur, recvGrantState, recvGrantShared] using htxnData
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨tx, msg, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnDataInv, recvGrantAckState, recvGrantAckShared]
  | .sendRelease param =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, htail⟩
      rcases htail with ⟨_, hs'⟩
      rw [hs']
      simp [txnDataInv, hcur, sendReleaseState]
  | .sendReleaseData param =>
      -- currentTxn = none in guard, stays none → txnDataInv trivially True
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnDataInv, hcur, sendReleaseState]
  | .recvReleaseAtManager =>
      rcases hstep with ⟨msg, param, hcur, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnDataInv, hcur, recvReleaseState, recvReleaseShared]
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨msg, hcur, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnDataInv, hcur, recvReleaseAckState, recvReleaseAckShared]
  | .store v =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [txnDataInv, hcur]
  | .read =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩
      exact htxnData
  | .uncachedGet source =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, rfl⟩
      simp [txnDataInv, hcur]
  | .uncachedPut source v =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, rfl⟩
      simp [txnDataInv, hcur]
  | .recvUncachedAtManager =>
      rcases hstep with ⟨hcur, _, _, _, _, _, rfl⟩
      simp [txnDataInv, hcur]
  | .recvAccessAckAtMaster =>
      rcases hstep with ⟨_, _, _, rfl⟩
      exact htxnData

theorem preLinesNoDirtyInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hfull : fullInv n s) (hdirtyEx : dirtyExclusiveInv n s)
    (hSwmr : permSwmrInv n s) (hpre : preLinesNoDirtyInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    preLinesNoDirtyInv n s' := by
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  match a with
  | .sendAcquireBlock _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [preLinesNoDirtyInv]
  | .sendAcquirePerm _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [preLinesNoDirtyInv]
  | .recvAcquireAtManager =>
      rcases hstep with hblk | hperm
      · -- Block acquire: preLines = snapshot of current lines → dirtyExclusiveInv
        rcases hblk with ⟨grow, source, _, _, _, _, _, _, _, _, _, _, hs'⟩
        rw [hs']
        simp only [preLinesNoDirtyInv, recvAcquireState, recvAcquireShared, plannedTxn]
        intro k1 k2 hk1 hk2 hne hdirty
        simp [hk1] at hdirty
        have hperm := hdirtyEx ⟨k1, hk1⟩ ⟨k2, hk2⟩ (by intro h; exact hne (Fin.ext_iff.mp h)) hdirty
        simp [hk2]
        exact hperm
      · -- Perm acquire: preLines = snapshot of current lines → dirtyExclusiveInv
        rcases hperm with ⟨grow, source, _, _, _, _, _, _, _, _, _, hs'⟩
        rw [hs']
        simp only [preLinesNoDirtyInv, recvAcquireState, recvAcquireShared, plannedTxn]
        intro k1 k2 hk1 hk2 hne hdirty
        simp [hk1] at hdirty
        have hperm := hdirtyEx ⟨k1, hk1⟩ ⟨k2, hk2⟩ (by intro h; exact hne (Fin.ext_iff.mp h)) hdirty
        simp [hk2]
        exact hperm
  | .recvProbeAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [preLinesNoDirtyInv, hcur, recvProbeState]
        using hpre
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [preLinesNoDirtyInv, hcur, recvProbeAckState, recvProbeAckShared]
        using hpre
  | .sendGrantToRequester =>
      rcases hstep with ⟨tx, hcur, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [preLinesNoDirtyInv, hcur, sendGrantState, sendGrantShared]
        using hpre
  | .recvGrantAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [preLinesNoDirtyInv, hcur, recvGrantState, recvGrantShared]
        using hpre
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨tx, msg, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [preLinesNoDirtyInv, recvGrantAckState, recvGrantAckShared]
  | .sendRelease _ =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, htail⟩
      rcases htail with ⟨_, hs'⟩
      rw [hs']
      simp [preLinesNoDirtyInv, hcur, sendReleaseState]
  | .sendReleaseData _ =>
      -- currentTxn = none → preLinesNoDirtyInv trivially True
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [preLinesNoDirtyInv, hcur, sendReleaseState]
  | .recvReleaseAtManager =>
      rcases hstep with ⟨msg, param, hcur, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [preLinesNoDirtyInv, hcur, recvReleaseState, recvReleaseShared]
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨msg, hcur, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [preLinesNoDirtyInv, hcur, recvReleaseAckState, recvReleaseAckShared]
  | .store v =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [preLinesNoDirtyInv, hcur]
  | .read =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩
      exact hpre
  | .uncachedGet source =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, rfl⟩
      simp [preLinesNoDirtyInv, hcur]
  | .uncachedPut source v =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, rfl⟩
      simp [preLinesNoDirtyInv, hcur]
  | .recvUncachedAtManager =>
      rcases hstep with ⟨hcur, _, _, _, _, _, rfl⟩
      simp [preLinesNoDirtyInv, hcur]
  | .recvAccessAckAtMaster =>
      rcases hstep with ⟨_, _, _, rfl⟩
      exact hpre

theorem preLinesCleanInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hfull : fullInv n s) (hclean : dataCoherenceInv n s) (hpre : preLinesCleanInv n s)
    (hcleanC : cleanChanCInv n s) (hpreNoDirty : preLinesNoDirtyInv n s)
    (hpreWF : preLinesWFInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    preLinesCleanInv n s' := by
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  match a with
  | .sendAcquireBlock _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [preLinesCleanInv]
  | .sendAcquirePerm _ _ =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [preLinesCleanInv]
  | .recvAcquireAtManager =>
      rcases hstep with hblk | hperm
      · rcases hblk with ⟨grow, source, htxn, _, _, _, hnoFlight, _, _, _, _, hrest⟩
        rcases hrest with ⟨_, hs'⟩
        rw [hs']
        intro k hk hpermK hdirty
        have hpermNeN : (s.locals ⟨k, hk⟩).line.perm ≠ .N := by simpa [plannedTxn, hk] using hpermK
        have hdirtyK : (s.locals ⟨k, hk⟩).line.dirty = false := by simpa [plannedTxn, hk] using hdirty
        have hflightK : (s.locals ⟨k, hk⟩).releaseInFlight = false := hnoFlight ⟨k, hk⟩
        have hdata := hclean htxn ⟨k, hk⟩ hflightK hpermNeN hdirtyK
        simpa [plannedTxn, hk] using hdata
      · rcases hperm with ⟨grow, source, htxn, _, _, _, hnoFlight, _, _, _, hrest⟩
        rcases hrest with ⟨_, hs'⟩
        rw [hs']
        intro k hk hpermK hdirty
        have hpermNeN : (s.locals ⟨k, hk⟩).line.perm ≠ .N := by simpa [plannedTxn, hk] using hpermK
        have hdirtyK : (s.locals ⟨k, hk⟩).line.dirty = false := by simpa [plannedTxn, hk] using hdirty
        have hflightK : (s.locals ⟨k, hk⟩).releaseInFlight = false := hnoFlight ⟨k, hk⟩
        have hdata := hclean htxn ⟨k, hk⟩ hflightK hpermNeN hdirtyK
        simpa [plannedTxn, hk] using hdata
  | .recvProbeAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [preLinesCleanInv, hcur, recvProbeState]
        using hpre
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, hC, _, _, hs'⟩
      rw [hs']
      -- From chanCInv: msg.data = probeAckDataOfLine (tx.preLines i.1)
      rcases hfull with ⟨_, ⟨_, _, hchanC, _, _⟩, _⟩
      specialize hchanC i; rw [hC] at hchanC
      rcases hchanC with ⟨tx', hcur', _, _, _, _, _, _, hdata⟩ | ⟨_, hcurNone, _⟩
      · rw [hcur] at hcur'; cases hcur'
        cases hdirtyI : (tx.preLines i.1).dirty
        · -- Clean probeAck: msg.data = none → mem unchanged → preserved from hpre
          have hmsg : msg.data = none := by simp [hdata, probeAckDataOfLine, hdirtyI]
          simpa [preLinesCleanInv, hcur, recvProbeAckState, recvProbeAckShared, hmsg]
            using hpre
        · -- Dirty probeAck: vacuously true — no valid+clean preLines besides dirty node
          simp only [preLinesCleanInv, hcur, recvProbeAckState, recvProbeAckShared]
          have hmsg : msg.data = some (tx.preLines i.1).data := by
            simp [hdata, probeAckDataOfLine, hdirtyI]
          simp only [hmsg]
          intro k hk hvalid hdirty
          -- From preLinesNoDirtyInv: dirty node i → perm k = .N for k ≠ i
          exfalso
          have hpnd := by simpa [preLinesNoDirtyInv, hcur] using hpreNoDirty
          by_cases hki : i.1 = k
          · -- k = i: preLines i is dirty, contradicts hdirty (dirty = false)
            rw [← hki] at hdirty; rw [hdirtyI] at hdirty; cases hdirty
          · -- k ≠ i: perm k = .N → contradicts perm ≠ .N premise
            exact absurd (hpnd i.1 k i.is_lt hk hki hdirtyI) hvalid
      · rw [hcur] at hcurNone; simp at hcurNone
  | .sendGrantToRequester =>
      rcases hstep with ⟨tx, hcur, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [preLinesCleanInv, hcur, sendGrantState, sendGrantShared]
        using hpre
  | .recvGrantAtMaster =>
      rcases hstep with ⟨tx, msg, hcur, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simpa [preLinesCleanInv, hcur, recvGrantState, recvGrantShared]
        using hpre
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨tx, msg, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [preLinesCleanInv, recvGrantAckState, recvGrantAckShared]
  | .sendRelease _ =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, htail⟩
      rcases htail with ⟨_, hs'⟩
      rw [hs']
      simp [preLinesCleanInv, hcur, sendReleaseState]
  | .sendReleaseData _ =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [preLinesCleanInv, hcur, sendReleaseState]
  | .recvReleaseAtManager =>
      rcases hstep with ⟨msg, param, hcur, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [preLinesCleanInv, hcur, recvReleaseState, recvReleaseShared]
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨msg, hcur, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [preLinesCleanInv, hcur, recvReleaseAckState, recvReleaseAckShared]
  | .store v =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      simp [preLinesCleanInv, hcur]
  | .read =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩
      exact hpre
  | .uncachedGet source =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, rfl⟩
      simp [preLinesCleanInv, hcur]
  | .uncachedPut source v =>
      rcases hstep with ⟨hcur, _, _, _, _, _, _, _, _, _, _, rfl⟩
      simp [preLinesCleanInv, hcur]
  | .recvUncachedAtManager =>
      rcases hstep with ⟨hcur, _, _, _, _, _, rfl⟩
      simp [preLinesCleanInv, hcur]
  | .recvAccessAckAtMaster =>
      rcases hstep with ⟨_, _, _, rfl⟩
      exact hpre


theorem cleanChanCInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hfull : fullInv n s) (hdirtyEx : dirtyExclusiveInv n s)
    (hclean : cleanChanCInv n s) (hrelUniq : releaseUniqueInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    cleanChanCInv n s' := by
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  intro htxn' j hflightJ msg hCj
  match a with
  | .sendAcquireBlock grow source =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      rw [hs'] at htxn' hCj hflightJ
      simp at htxn'
      by_cases hji : j = i
      · subst j; simp [setFn] at hCj hflightJ; exact hclean htxn' i hflightJ msg hCj
      · simp [setFn, hji] at hCj hflightJ; exact hclean htxn' j hflightJ msg hCj
  | .sendAcquirePerm grow source =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      rw [hs'] at htxn' hCj hflightJ
      simp at htxn'
      by_cases hji : j = i
      · subst j; simp [setFn] at hCj hflightJ; exact hclean htxn' i hflightJ msg hCj
      · simp [setFn, hji] at hCj hflightJ; exact hclean htxn' j hflightJ msg hCj
  | .recvAcquireAtManager =>
      -- Post: currentTxn = some, so htxn' (currentTxn = none) is contradicted
      rcases hstep with hblk | hperm
      · rcases hblk with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
        rw [hs'] at htxn'; simp [recvAcquireState, recvAcquireShared] at htxn'
      · rcases hperm with ⟨_, _, _, _, _, _, _, _, _, _, _, hs'⟩
        rw [hs'] at htxn'; simp [recvAcquireState, recvAcquireShared] at htxn'
  | .recvProbeAtMaster =>
      -- recvProbe requires currentTxn = some. Post currentTxn = some. Contradiction with htxn'.
      rcases hstep with ⟨_, _, hcur, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs'] at htxn'; simp [recvProbeState] at htxn'; rw [htxn'] at hcur; cases hcur
  | .recvProbeAckAtManager =>
      -- Post: currentTxn = some. Contradiction with htxn'.
      rcases hstep with ⟨_, _, hcur, _, _, _, _, _, _, hs'⟩
      rw [hs'] at htxn'
      simp [recvProbeAckState, recvProbeAckShared] at htxn'
  | .sendGrantToRequester =>
      -- Post: currentTxn = some (grantPendingAck). Contradiction with htxn'.
      rcases hstep with ⟨_, hcur, _, _, _, _, _, _, _, hs'⟩
      rw [hs'] at htxn'
      simp [sendGrantState, sendGrantShared] at htxn'
  | .recvGrantAtMaster =>
      -- Post: currentTxn = some. Contradiction with htxn'.
      rcases hstep with ⟨_, _, hcur, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs'] at htxn'; simp [recvGrantState, recvGrantShared] at htxn'; rw [htxn'] at hcur; cases hcur
  | .recvGrantAckAtManager =>
      -- Post: currentTxn = none. Pre had currentTxn = some tx, phase = grantPendingAck.
      -- From chanCInv: all chanC must be none (neither probing nor currentTxn=none holds).
      rcases hstep with ⟨tx, _, hcur, _, hphase, _, _, _, _, _, hs'⟩
      -- From chanCInv (in fullInv), chanC j = some msg leads to contradiction
      rcases hfull with ⟨_, ⟨_, _, hchanC, _, _⟩, _⟩
      specialize hchanC j
      -- In post-state, chanC j is unchanged by recvGrantAck (only chanE and pendingSink change)
      rw [hs'] at hCj
      by_cases hji : j = i
      · subst j
        simp [recvGrantAckState, recvGrantAckLocals, recvGrantAckLocal, setFn] at hCj
        -- hCj : (s.locals i).chanC = some msg
        rw [hCj] at hchanC
        rcases hchanC with ⟨tx', hcur', hprobing, _, _, _, _, _, _⟩ | ⟨_, htxnNone, _⟩
        · rw [hcur] at hcur'; injection hcur' with htx; subst htx; rw [hphase] at hprobing; cases hprobing
        · rw [hcur] at htxnNone; cases htxnNone
      · simp [recvGrantAckState, recvGrantAckLocals, recvGrantAckLocal, setFn, hji] at hCj
        -- hCj : (s.locals j).chanC = some msg
        rw [hCj] at hchanC
        rcases hchanC with ⟨tx', hcur', hprobing, _, _, _, _, _, _⟩ | ⟨_, htxnNone, _⟩
        · rw [hcur] at hcur'; injection hcur' with htx; subst htx; rw [hphase] at hprobing; cases hprobing
        · rw [hcur] at htxnNone; cases htxnNone
  | .sendRelease param =>
      rcases hstep with ⟨htxn, _, _, _, _, _, _, _, _, _, _, _, _, _, htail⟩
      rcases htail with ⟨_, hs'⟩
      rw [hs'] at htxn' hCj hflightJ
      have htxn_s : s.shared.currentTxn = none := htxn'
      by_cases hji : j = i
      · subst j
        simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn] at hCj
        subst hCj
        simp [releaseMsg, releaseDataPayload]
      · simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] at hCj hflightJ
        exact hclean htxn_s j hflightJ msg hCj
  | .sendReleaseData param =>
      rcases hstep with ⟨htxn, _, _, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs'] at htxn' hflightJ hCj
      simp only [sendReleaseState] at htxn' hflightJ hCj
      by_cases hji : j = i
      · subst j
        -- Node i has releaseInFlight = true after sendReleaseData, contradicting hflightJ
        simp [sendReleaseLocals, sendReleaseLocal, setFn] at hflightJ
      · simp [sendReleaseLocals, sendReleaseLocal, setFn, hji] at hflightJ hCj
        exact hclean htxn' j hflightJ msg hCj
  | .recvReleaseAtManager =>
      rcases hstep with ⟨_, _, htxn_s, _, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs'] at hCj hflightJ htxn'
      simp [recvReleaseState, recvReleaseShared] at htxn'
      by_cases hji : j = i
      · subst j; simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn] at hCj
      · simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn, hji] at hCj hflightJ
        exact hclean htxn_s j hflightJ msg hCj
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨_, htxn_s, _, hrelAck, _, _, _, hs'⟩
      -- From releaseUniqueInv: pendingReleaseAck ≠ none → all chanC = none
      have hallCNone := (hrelUniq htxn_s).1 (by rw [hrelAck]; exact Option.some_ne_none _)
      rw [hs'] at hCj
      by_cases hji : j = i
      · subst j; simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn] at hCj
        -- hCj : (s.locals i).chanC = some msg, but hallCNone says chanC i = none
        rw [hallCNone i] at hCj; cases hCj
      · simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn, hji] at hCj
        rw [hallCNone j] at hCj; cases hCj
  | .store v =>
      rcases hstep with ⟨htxn_s, _, _, _, _, _, _, hCi, _, _, _, _, hs'⟩
      rw [hs'] at hCj hflightJ htxn'
      simp at htxn'
      by_cases hji : j = i
      · subst j; simp [setFn] at hCj; rw [hCi] at hCj; simp at hCj
      · simp [setFn, hji] at hCj hflightJ; exact hclean htxn_s j hflightJ msg hCj
  | .read =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩
      exact hclean htxn' j hflightJ msg hCj
  | .uncachedGet source =>
      rcases hstep with ⟨htxn_s, _, _, _, _, _, _, _, _, _, rfl⟩
      by_cases hji : j = i
      · subst j; simp [setFn] at hCj hflightJ; exact hclean htxn_s i hflightJ msg hCj
      · simp [setFn, hji] at hCj hflightJ; exact hclean htxn_s j hflightJ msg hCj
  | .uncachedPut source v =>
      rcases hstep with ⟨htxn_s, _, _, _, _, _, _, _, _, _, _, rfl⟩
      by_cases hji : j = i
      · subst j; simp [setFn] at hCj hflightJ; exact hclean htxn_s i hflightJ msg hCj
      · simp [setFn, hji] at hCj hflightJ; exact hclean htxn_s j hflightJ msg hCj
  | .recvUncachedAtManager =>
      rcases hstep with ⟨htxn_s, _, _, _, _, _, rfl⟩
      by_cases hji : j = i
      · subst j; simp [setFn] at hCj hflightJ; exact hclean htxn_s i hflightJ msg hCj
      · simp [setFn, hji] at hCj hflightJ; exact hclean htxn_s j hflightJ msg hCj
  | .recvAccessAckAtMaster =>
      rcases hstep with ⟨_, _, _, rfl⟩
      by_cases hji : j = i
      · subst j; simp [setFn] at hCj hflightJ; exact hclean htxn' i hflightJ msg hCj
      · simp [setFn, hji] at hCj hflightJ; exact hclean htxn' j hflightJ msg hCj

theorem releaseUniqueInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hfull : fullInv n s) (hdirtyEx : dirtyExclusiveInv n s) (hrelUniq : releaseUniqueInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    releaseUniqueInv n s' := by
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  intro htxn'
  match a with
  | .sendAcquireBlock grow source =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      rw [hs'] at htxn' ⊢; simp at htxn'
      have h := hrelUniq htxn'
      exact ⟨fun hrel j => by
          have := h.1 hrel j
          by_cases hji : j = i <;> simp_all [setFn],
        fun p q hpq hp => by
          have hp' : (s.locals p).chanC ≠ none := by
            by_cases hpi : p = i <;> simp_all [setFn]
          have := h.2 p q hpq hp'
          by_cases hqi : q = i <;> simp_all [setFn]⟩
  | .sendAcquirePerm grow source =>
      rcases hstep with ⟨_, _, _, _, _, _, _, hs'⟩
      rw [hs'] at htxn' ⊢; simp at htxn'
      have h := hrelUniq htxn'
      exact ⟨fun hrel j => by
          have := h.1 hrel j
          by_cases hji : j = i <;> simp_all [setFn],
        fun p q hpq hp => by
          have hp' : (s.locals p).chanC ≠ none := by
            by_cases hpi : p = i <;> simp_all [setFn]
          have := h.2 p q hpq hp'
          by_cases hqi : q = i <;> simp_all [setFn]⟩
  | .recvAcquireAtManager =>
      -- Post: currentTxn = some, so the invariant is vacuously true
      rcases hstep with hblk | hperm
      · rcases hblk with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hs'⟩
        rw [hs'] at htxn'; simp [recvAcquireState, recvAcquireShared] at htxn'
      · rcases hperm with ⟨_, _, _, _, _, _, _, _, _, _, _, hs'⟩
        rw [hs'] at htxn'; simp [recvAcquireState, recvAcquireShared] at htxn'
  | .recvProbeAtMaster =>
      -- currentTxn stays some (guard requires some)
      rcases hstep with ⟨_, _, hcur, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs'] at htxn'; simp [recvProbeState] at htxn'; rw [htxn'] at hcur; cases hcur
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨_, _, hcur, _, _, _, _, _, _, hs'⟩
      rw [hs'] at htxn'; simp [recvProbeAckState, recvProbeAckShared] at htxn'
  | .sendGrantToRequester =>
      rcases hstep with ⟨_, hcur, _, _, _, _, _, _, _, hs'⟩
      rw [hs'] at htxn'; simp [sendGrantState, sendGrantShared] at htxn'
  | .recvGrantAtMaster =>
      rcases hstep with ⟨_, _, hcur, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs'] at htxn'; simp [recvGrantState, recvGrantShared] at htxn'; rw [htxn'] at hcur; cases hcur
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨tx, msg, hcur, hreq, hphase, hpendGrant, hD, hE, hSink, hmsg, hs'⟩
      rw [hs']
      rcases hfull with ⟨_, ⟨_, _, hchanC, _, _⟩, _⟩
      have hAllCNone : ∀ j : Fin n, (s.locals j).chanC = none := by
        intro j; specialize hchanC j
        cases hCj : (s.locals j).chanC with
        | none => rfl
        | some cmsg =>
            rw [hCj] at hchanC
            rcases hchanC with ⟨tx0, hcur0, hprobing, _, _, _, _, _, _⟩ | ⟨_, hcur0, _, _, _, _, _, _⟩
            · rw [hcur] at hcur0; injection hcur0 with htx; subst htx; rw [hphase] at hprobing; cases hprobing
            · rw [hcur] at hcur0; cases hcur0
      constructor
      · intro _ j
        by_cases hji : j = i
        · subst j; simp [recvGrantAckState, recvGrantAckLocals, recvGrantAckLocal, setFn, hAllCNone i]
        · simp [recvGrantAckState, recvGrantAckLocals, recvGrantAckLocal, setFn, hji, hAllCNone j]
      · intro p q _ hp
        by_cases hpi : p = i
        · subst p; simp [recvGrantAckState, recvGrantAckLocals, recvGrantAckLocal, setFn] at hp
          exact absurd (hAllCNone i) hp
        · simp [recvGrantAckState, recvGrantAckLocals, recvGrantAckLocal, setFn, hpi] at hp
          exact absurd (hAllCNone p) hp
  | .sendRelease param =>
      rcases hstep with ⟨htxn, hgrant, hrel, hCother, _, _, hCi, _, _, _, _, hflight, _, _, _, hs'⟩
      rw [hs']
      constructor
      · intro hrel'
        simp [sendReleaseState] at hrel'
        exact absurd hrel' (by simp [hrel])
      · intro p q hpq hp
        by_cases hpi : p = i
        · subst p
          by_cases hqi : q = i
          · exact absurd hqi (Ne.symm hpq)
          · simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hqi]
            exact hCother q hqi
        · simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hpi] at hp
          exact absurd (hCother p hpi) hp
  | .sendReleaseData param =>
      -- SendReleaseData: guard has currentTxn = none, dirty = true
      -- Post: chanC[i] set with data, others unchanged, currentTxn still none
      rcases hstep with ⟨htxn, hgrant, hrel, hCother, _, _, hCi, _, _, _, _, hflight, _, _, hs'⟩
      rw [hs']
      constructor
      · intro hrel'
        simp [sendReleaseState] at hrel'
        exact absurd hrel' (by simp [hrel])
      · intro p q hpq hp
        by_cases hpi : p = i
        · subst p
          by_cases hqi : q = i
          · exact absurd hqi (Ne.symm hpq)
          · simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hqi]
            exact hCother q hqi
        · simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hpi] at hp
          exact absurd (hCother p hpi) hp
  | .recvReleaseAtManager =>
      rcases hstep with ⟨msg, param, htxn, hgrant, hrel, hflight, hC, _, _, _, _, _, hs'⟩
      rw [hs']
      have hpre := hrelUniq htxn
      constructor
      · intro _ j
        by_cases hji : j = i
        · subst j; simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn]
        · simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn, hji]
          have : (s.locals i).chanC ≠ none := by rw [hC]; simp
          exact hpre.2 i j (Ne.symm hji) this
      · intro p q hpq hp
        by_cases hpi : p = i
        · subst p; simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn] at hp
        · simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn, hpi] at hp
          have : (s.locals i).chanC ≠ none := by rw [hC]; simp
          exact absurd (hpre.2 i p (Ne.symm hpi) this) hp
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨msg, htxn, hgrant, hrel, hflight, hD, hmsg, hs'⟩
      rw [hs']
      have hpre := hrelUniq htxn
      have hAllCNone := hpre.1 (by rw [hrel]; simp)
      constructor
      · intro hrel' j
        simp [recvReleaseAckState, recvReleaseAckShared] at hrel'
      · intro p q hpq hp
        by_cases hpi : p = i
        · subst p; simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn] at hp
          exact absurd (hAllCNone i) hp
        · simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn, hpi] at hp
          exact absurd (hAllCNone p) hp
  | .store v =>
      rcases hstep with ⟨hcur, _, hrel, _, _, _, _, hCi, _, _, _, _, hs'⟩
      have hpre := hrelUniq hcur
      rw [hs']
      constructor
      · intro hrel'
        rw [hrel] at hrel'
        simp at hrel'
      · intro p q hpq hp
        by_cases hpi : p = i
        · subst p; simp [setFn, storeLocal] at hp; rw [hCi] at hp; simp at hp
        · have hp' : (s.locals p).chanC ≠ none := by
            simp [setFn, hpi] at hp; exact hp
          have := hpre.2 p q hpq hp'
          by_cases hqi : q = i
          · subst q; simp [setFn, storeLocal, hCi]
          · simp [setFn, hqi]; exact this
  | .read =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩
      exact hrelUniq htxn'
  | .uncachedGet source =>
      rcases hstep with ⟨htxn_s, _, _, _, _, _, _, _, _, _, rfl⟩
      have hpre := hrelUniq htxn_s
      constructor
      · intro hrel j
        have := hpre.1 hrel j
        by_cases hji : j = i <;> simp_all [setFn]
      · intro p q hpq hp
        have hp' : (s.locals p).chanC ≠ none := by
          by_cases hpi : p = i <;> simp_all [setFn]
        have := hpre.2 p q hpq hp'
        by_cases hqi : q = i <;> simp_all [setFn]
  | .uncachedPut source v =>
      rcases hstep with ⟨htxn_s, _, _, _, _, _, _, _, _, _, _, rfl⟩
      have hpre := hrelUniq htxn_s
      constructor
      · intro hrel j
        have := hpre.1 (by simpa using hrel) j
        by_cases hji : j = i <;> simp_all [setFn]
      · intro p q hpq hp
        have hp' : (s.locals p).chanC ≠ none := by
          by_cases hpi : p = i <;> simp_all [setFn]
        have := hpre.2 p q hpq hp'
        by_cases hqi : q = i <;> simp_all [setFn]
  | .recvUncachedAtManager =>
      rcases hstep with ⟨htxn_s, _, _, _, _, _, rfl⟩
      have hpre := hrelUniq htxn_s
      constructor
      · intro hrel j
        have := hpre.1 hrel j
        by_cases hji : j = i <;> simp_all [setFn]
      · intro p q hpq hp
        have hp' : (s.locals p).chanC ≠ none := by
          by_cases hpi : p = i <;> simp_all [setFn]
        have := hpre.2 p q hpq hp'
        by_cases hqi : q = i <;> simp_all [setFn]
  | .recvAccessAckAtMaster =>
      rcases hstep with ⟨_, _, _, rfl⟩
      have hpre := hrelUniq htxn'
      constructor
      · intro hrel j
        have := hpre.1 hrel j
        by_cases hji : j = i <;> simp_all [setFn]
      · intro p q hpq hp
        have hp' : (s.locals p).chanC ≠ none := by
          by_cases hpi : p = i <;> simp_all [setFn]
        have := hpre.2 p q hpq hp'
        by_cases hqi : q = i <;> simp_all [setFn]

/-- Helper: if all lines are unchanged between s and s', permSwmrInv transfers. -/
private theorem permSwmrInv_of_same_lines (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hSwmr : permSwmrInv n s)
    (hlines : ∀ j : Fin n, (s'.locals j).line = (s.locals j).line) :
    permSwmrInv n s' := by
  intro p q hpq hpermP
  rw [hlines p] at hpermP; rw [hlines q]
  exact hSwmr p q hpq hpermP

theorem permSwmrInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hinv : strongRefinementInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    permSwmrInv n s' := by
  rcases hinv with ⟨⟨hfull, _, hSwmr, _, _, _, _⟩, htxnLine, _, hpreNoDirty, htxnPlan⟩
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  match a with
  | .sendAcquireBlock grow source =>
      exact permSwmrInv_of_same_lines n s s' hSwmr
        (fun j => sendAcquireBlock_line hstep)
  | .sendAcquirePerm grow source =>
      exact permSwmrInv_of_same_lines n s s' hSwmr
        (fun j => sendAcquirePerm_line hstep)
  | .recvAcquireAtManager =>
      rcases hstep with hblk | hperm
      · rcases hblk with ⟨grow, source, _, _, _, _, _, _, _, _, _, _, hs'⟩
        exact permSwmrInv_of_same_lines n s s' hSwmr
          (fun j => by rw [hs']; simp [recvAcquireState, recvAcquireLocals_line])
      · rcases hperm with ⟨grow, source, _, _, _, _, _, _, _, _, _, hs'⟩
        exact permSwmrInv_of_same_lines n s s' hSwmr
          (fun j => by rw [hs']; simp [recvAcquireState, recvAcquireLocals_line])
  | .recvProbeAtMaster =>
      -- probedLine with probeCapOfResult never gives perm .T
      rcases hstep with ⟨tx, msg, htxn, hphase, hprobesRem, _, _, _, _, hparam, hchanC, hs'⟩
      rw [hs']
      intro p q hpq hpermP
      by_cases hpi : p = i
      · -- p = i (probed node): post perm is probedLine ≠ .T
        rw [hpi] at hpermP
        simp only [recvProbeState, recvProbeLocals, recvProbeLocal, setFn, ite_true] at hpermP
        exact absurd hpermP (by rw [hparam]; exact probedLine_probeCapOfResult_perm_ne_T _ _)
      · -- p ≠ i: line p unchanged
        simp [recvProbeState, recvProbeLocals, setFn, hpi] at hpermP
        by_cases hqi : q = i
        · -- perm p = .T → perm i = .N (SWMR). But probing a .N-perm node
          -- contradicts txnPlanInv.
          have hpermN : (s.locals i).line.perm = .N := hSwmr p i hpi hpermP
          exact (absurd_probed_permN s tx i htxn hphase
            (hfull.1.2.2.2) htxnLine htxnPlan hprobesRem hchanC hpermN).elim
        · -- q ≠ i: line q unchanged
          simp [recvProbeState, recvProbeLocals, setFn, hqi]
          exact hSwmr p q hpq hpermP
  | .recvProbeAckAtManager =>
      rcases hstep with ⟨tx, msg, _, _, _, _, _, _, _, hs'⟩
      exact permSwmrInv_of_same_lines n s s' hSwmr (fun j => by
        rw [hs']
        by_cases hji : j = i
        · subst hji; simp [recvProbeAckState, recvProbeAckLocals, recvProbeAckLocal, setFn]
        · simp [recvProbeAckState, recvProbeAckLocals, setFn, hji])
  | .sendGrantToRequester =>
      rcases hstep with ⟨tx, _, _, _, _, _, _, _, _, hs'⟩
      exact permSwmrInv_of_same_lines n s s' hSwmr
        (fun j => by rw [hs']; exact sendGrantState_line s i j tx)
  | .recvGrantAtMaster =>
      -- grantLine changes perm at node i. Needs protocol reasoning.
      rcases hstep with ⟨tx, msg, htxn, hreq, hphase, _, _, _, _, _, _, hs'⟩
      rw [hs']
      intro p q hpq hpermP
      by_cases hpi : p = i
      · -- p = i (requester): grantLine gives .T → need all others .N
        rw [hpi] at hpermP hpq
        simp only [recvGrantState, recvGrantLocals, recvGrantLocal, setFn, ite_true] at hpermP
        -- grantLine gives .T only when resultPerm = .T
        have hresT : tx.resultPerm = .T := by
          unfold grantLine at hpermP
          cases hdata : tx.grantHasData <;> simp [hdata] at hpermP
          · -- grantHasData = false → resultPerm = .T (from txnCoreInv)
            have htxnCore := hfull.1.2.2.2
            simp only [txnCoreInv, htxn] at htxnCore
            exact htxnCore.2.2.2.1 hdata
          · -- grantHasData = true → depends on resultPerm
            cases hres : tx.resultPerm <;> simp_all [invalidatedLine]
        have hqi : q ≠ i := fun h => hpq (h.symm)
        simp [recvGrantState, recvGrantLocals, setFn, hqi]
        have hq_ne : q.1 ≠ tx.requester := by
          intro h; rw [hreq] at h; exact hqi (Fin.ext h)
        exact all_others_permN_during_grant s tx q htxn hphase
          (hfull.1.2.2.2) htxnLine htxnPlan hq_ne hresT
      · -- p ≠ i: line p unchanged, perm p = .T
        simp [recvGrantState, recvGrantLocals, setFn, hpi] at hpermP
        by_cases hqi : q = i
        · -- p has perm .T during grantPendingAck: contradicts txn invariants
          have hp_ne : p.1 ≠ tx.requester := by
            intro h; rw [hreq] at h; exact hpi (Fin.ext h)
          exact (absurd_permT_during_grant s tx p htxn hphase
            (hfull.1.2.2.2) htxnLine htxnPlan hpreNoDirty
            hp_ne hpermP).elim
        · simp [recvGrantState, recvGrantLocals, setFn, hqi]
          exact hSwmr p q hpq hpermP
  | .recvGrantAckAtManager =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, hs'⟩
      exact permSwmrInv_of_same_lines n s s' hSwmr
        (fun j => by rw [hs']; exact recvGrantAckState_line s i j)
  | .sendRelease param =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hlegal, _, htail⟩
      rcases htail with ⟨_, hs'⟩
      rw [hs']
      intro p q hpq hpermP
      by_cases hpi : p = i
      · -- p = i: post perm = param.result. If .T → param.source = .T → pre perm = .T.
        rw [hpi] at hpermP hpq
        simp only [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, ite_true] at hpermP
        rw [releasedLine_perm] at hpermP
        have hpermIT : (s.locals i).line.perm = .T := by
          rw [PruneReportParam.legalFrom] at hlegal; rw [hlegal]
          cases param <;> simp [PruneReportParam.result] at hpermP <;>
            simp [PruneReportParam.source]
        have hqi : q ≠ i := fun h => hpq (h.symm)
        simp [sendReleaseState, sendReleaseLocals, setFn, hqi]
        exact hSwmr i q hqi.symm hpermIT
      · -- p ≠ i: line p unchanged
        simp [sendReleaseState, sendReleaseLocals, setFn, hpi] at hpermP
        by_cases hqi : q = i
        · rw [hqi]
          simp only [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, ite_true]
          rw [releasedLine_perm]
          have hpermIN : (s.locals i).line.perm = .N := hSwmr p i hpi hpermP
          rw [PruneReportParam.legalFrom] at hlegal; rw [hpermIN] at hlegal
          cases param <;> simp [PruneReportParam.source] at hlegal
          simp [PruneReportParam.result]
        · simp [sendReleaseState, sendReleaseLocals, setFn, hqi]
          exact hSwmr p q hpq hpermP
  | .sendReleaseData param =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hlegal, _, hs'⟩
      rw [hs']
      intro p q hpq hpermP
      by_cases hpi : p = i
      · rw [hpi] at hpermP hpq
        simp only [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, ite_true] at hpermP
        rw [releasedLine_perm] at hpermP
        have hpermIT : (s.locals i).line.perm = .T := by
          rw [PruneReportParam.legalFrom] at hlegal; rw [hlegal]
          cases param <;> simp [PruneReportParam.result] at hpermP <;>
            simp [PruneReportParam.source]
        have hqi : q ≠ i := fun h => hpq (h.symm)
        simp [sendReleaseState, sendReleaseLocals, setFn, hqi]
        exact hSwmr i q hqi.symm hpermIT
      · simp [sendReleaseState, sendReleaseLocals, setFn, hpi] at hpermP
        by_cases hqi : q = i
        · rw [hqi]
          simp only [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, ite_true]
          rw [releasedLine_perm]
          have hpermIN : (s.locals i).line.perm = .N := hSwmr p i hpi hpermP
          rw [PruneReportParam.legalFrom] at hlegal; rw [hpermIN] at hlegal
          cases param <;> simp [PruneReportParam.source] at hlegal
          simp [PruneReportParam.result]
        · simp [sendReleaseState, sendReleaseLocals, setFn, hqi]
          exact hSwmr p q hpq hpermP
  | .recvReleaseAtManager =>
      rcases hstep with ⟨msg, param, _, _, _, _, _, _, _, _, _, _, hs'⟩
      exact permSwmrInv_of_same_lines n s s' hSwmr (fun j => by
        rw [hs']
        by_cases hji : j = i
        · subst hji; simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn]
        · simp [recvReleaseState, recvReleaseLocals, setFn, hji])
  | .recvReleaseAckAtMaster =>
      rcases hstep with ⟨msg, _, _, _, _, _, _, hs'⟩
      exact permSwmrInv_of_same_lines n s s' hSwmr (fun j => by
        rw [hs']
        by_cases hji : j = i
        · subst hji; simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn]
        · simp [recvReleaseAckState, recvReleaseAckLocals, setFn, hji])
  | .store v =>
      rcases hstep with ⟨_, _, _, _, hperm, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      intro p q hpq hpermP
      by_cases hpi : p = i
      · -- p = i: pre perm i = .T. By SWMR, all q ≠ i have .N. Post: q ≠ i unchanged.
        rw [hpi] at hpermP hpq
        have hqi : q ≠ i := fun h => hpq (h.symm)
        simp [setFn, hqi]
        exact hSwmr i q hqi.symm hperm
      · -- p ≠ i: line p unchanged
        simp [setFn, hpi] at hpermP
        by_cases hqi : q = i
        · -- q = i: pre perm p = .T and perm i = .T (guard). SWMR says perm i = .N. Contradiction.
          rw [hqi]; simp [setFn, storeLocal]
          have hpermIN := hSwmr p i hpi hpermP
          rw [hperm] at hpermIN; cases hpermIN
        · simp [setFn, hqi]
          exact hSwmr p q hpq hpermP
  | .read =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩
      exact hSwmr
  | .uncachedGet source =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
      exact permSwmrInv_of_same_lines n s _ hSwmr
        (fun j => by simp [setFn]; split <;> simp_all)
  | .uncachedPut source v =>
      rcases hstep with ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩
      exact permSwmrInv_of_same_lines n s _ hSwmr
        (fun j => by simp [setFn]; split <;> simp_all)
  | .recvUncachedAtManager =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩
      exact permSwmrInv_of_same_lines n s _ hSwmr
        (fun j => by simp [setFn]; split <;> simp_all)
  | .recvAccessAckAtMaster =>
      rcases hstep with ⟨_, _, _, rfl⟩
      exact permSwmrInv_of_same_lines n s _ hSwmr
        (fun j => by simp [setFn]; split <;> simp_all)

private theorem pruneReport_source_N_result_N (param : PruneReportParam)
    (h : param.source = .N) : param.result = .N := by
  cases param <;> simp_all [PruneReportParam.source, PruneReportParam.result]

theorem dirtyReleaseExclusiveInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hfull : fullInv n s) (hdirtyEx : dirtyExclusiveInv n s)
    (hSwmr : permSwmrInv n s)
    (hdirtyRelEx : dirtyReleaseExclusiveInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    dirtyReleaseExclusiveInv n s' := by
  simp only [SymSharedSpec.toSpec, tlMessages] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  match a with
  | .sendAcquireBlock grow source =>
      rcases hstep with ⟨_, _, _, _, hrelI, _, _, hs'⟩
      rw [hs']
      intro htxn' k hrel ⟨msg, hC, hdata⟩ j hji
      by_cases hki : k = i
      · subst k; simp [setFn] at hrel; rw [hrelI] at hrel; cases hrel
      · have hrel' : (s.locals k).releaseInFlight = true := by
          simp [setFn, hki] at hrel; exact hrel
        have ⟨msg', hC', hdata'⟩ : ∃ msg, (s.locals k).chanC = some msg ∧ msg.data ≠ none := by
          simp [setFn, hki] at hC; exact ⟨msg, hC, hdata⟩
        have := hdirtyRelEx htxn' k hrel' ⟨msg', hC', hdata'⟩ j hji
        by_cases hji' : j = i
        · subst j; simp [setFn]; exact this
        · simp [setFn, hji']; exact this
  | .sendAcquirePerm grow source =>
      rcases hstep with ⟨_, _, _, _, hrelI, _, _, hs'⟩
      rw [hs']
      intro htxn' k hrel ⟨msg, hC, hdata⟩ j hji
      by_cases hki : k = i
      · subst k; simp [setFn] at hrel; rw [hrelI] at hrel; cases hrel
      · have hrel' : (s.locals k).releaseInFlight = true := by
          simp [setFn, hki] at hrel; exact hrel
        have ⟨msg', hC', hdata'⟩ : ∃ msg, (s.locals k).chanC = some msg ∧ msg.data ≠ none := by
          simp [setFn, hki] at hC; exact ⟨msg, hC, hdata⟩
        have := hdirtyRelEx htxn' k hrel' ⟨msg', hC', hdata'⟩ j hji
        by_cases hji' : j = i
        · subst j; simp [setFn]; exact this
        · simp [setFn, hji']; exact this
  | .recvAcquireAtManager =>
      -- Post: currentTxn = some → guard fails → vacuous
      intro htxn'
      rcases hstep with ⟨_, _, hblk⟩ | ⟨_, _, hperm⟩
      · have hs' := hblk.2.2.2.2.2.2.2.2.2.2
        rw [hs'] at htxn'; simp [recvAcquireState, recvAcquireShared] at htxn'
      · have hs' := hperm.2.2.2.2.2.2.2.2.2
        rw [hs'] at htxn'; simp [recvAcquireState, recvAcquireShared] at htxn'
  | .recvProbeAtMaster =>
      -- currentTxn stays some → vacuous
      intro htxn'
      rcases hstep with ⟨tx, msg, hcur, hstep'⟩
      have hs' := hstep'.2.2.2.2.2.2.2.2
      rw [hs'] at htxn'; simp [recvProbeState] at htxn'; rw [htxn'] at hcur; cases hcur
  | .recvProbeAckAtManager =>
      -- currentTxn stays some → vacuous
      intro htxn'
      rcases hstep with ⟨tx, msg, hcur, hstep'⟩
      have hs' := hstep'.2.2.2.2.2.2
      rw [hs'] at htxn'; simp [recvProbeAckState, recvProbeAckShared] at htxn'
  | .sendGrantToRequester =>
      -- currentTxn stays some → vacuous
      intro htxn'
      rcases hstep with ⟨tx, hcur, hstep'⟩
      have hs' := hstep'.2.2.2.2.2.2.2
      rw [hs'] at htxn'; simp [sendGrantState, sendGrantShared] at htxn'
  | .recvGrantAtMaster =>
      -- currentTxn stays some → vacuous
      intro htxn'
      rcases hstep with ⟨tx, msg, hcur, hstep'⟩
      have hs' := hstep'.2.2.2.2.2.2.2.2
      rw [hs'] at htxn'; simp [recvGrantState, recvGrantShared] at htxn'; rw [htxn'] at hcur; cases hcur
  | .recvGrantAckAtManager =>
      -- Post: currentTxn = none. During grantPendingAck all chanC were none (from chanCInv).
      rcases hstep with ⟨tx, msg, hcur, _, hphase, _, _, _, _, _, hs'⟩
      rw [hs']
      rcases hfull with ⟨_, ⟨_, _, hchanC, _, _⟩, _⟩
      intro _ k hrel ⟨cmsg, hC, hdata⟩ j hji
      have hAllCNone : ∀ j : Fin n, (s.locals j).chanC = none := by
        intro j; specialize hchanC j
        cases hCj : (s.locals j).chanC with
        | none => rfl
        | some cm =>
            rw [hCj] at hchanC
            rcases hchanC with ⟨tx0, hcur0, hprobing, _, _, _, _, _, _⟩ | ⟨_, hcur0, _, _, _, _, _, _⟩
            · rw [hcur] at hcur0; injection hcur0 with htx; subst htx; rw [hphase] at hprobing; cases hprobing
            · rw [hcur] at hcur0; cases hcur0
      by_cases hki : k = i
      · subst k
        have := hAllCNone i
        simp [recvGrantAckState, recvGrantAckLocals, recvGrantAckLocal, setFn] at hC
        exact absurd this (by rw [hC]; simp)
      · have := hAllCNone k
        simp [recvGrantAckState, recvGrantAckLocals, recvGrantAckLocal, setFn, hki] at hC
        exact absurd this (by rw [hC]; simp)
  | .sendRelease param =>
      -- Clean release: msg.data = none → data ≠ none condition fails for sender.
      rcases hstep with ⟨htxn, _, _, hCother, _, _, hCi, _, _, _, _, hflight, hlegal, hdirty, _, hs'⟩
      rw [hs']
      intro htxn' k hrel ⟨cmsg, hC, hdata⟩ j hji
      by_cases hki : k = i
      · subst k
        simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn] at hC
        rcases hC with rfl
        -- releaseMsg with withData=false has data = none
        simp [releaseMsg, releaseDataPayload] at hdata
      · simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hki] at hrel hC
        have ⟨cmsg', hC', hdata'⟩ : ∃ msg, (s.locals k).chanC = some msg ∧ msg.data ≠ none :=
          ⟨cmsg, hC, hdata⟩
        have hpre := hdirtyRelEx htxn k hrel ⟨cmsg', hC', hdata'⟩
        by_cases hji' : j = i
        · subst j
          have hpermI := hpre i (Ne.symm hki)
          simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, releasedLine_perm]
          rw [PruneReportParam.legalFrom] at hlegal
          rw [hpermI] at hlegal
          exact pruneReport_source_N_result_N param hlegal.symm
        · simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji']
          exact hpre j hji
  | .sendReleaseData param =>
      -- The key case: new dirty release.
      rcases hstep with ⟨htxn, _, _, hCother, _, _, hCi, _, _, _, _, hflight, _, hdirty, hs'⟩
      rw [hs']
      intro htxn' k hrel ⟨cmsg, hC, hdata⟩ j hji
      by_cases hki : k = i
      · subst k
        -- Sender: dirty=true, so by dirtyExclusiveInv all others have .N
        have hne : i ≠ j := Ne.symm hji
        simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hji] at hC ⊢
        exact hdirtyEx i j hne hdirty
      · -- Other node k ≠ i: chanC was none by hCother, contradiction
        simp [sendReleaseState, sendReleaseLocals, sendReleaseLocal, setFn, hki] at hC
        exact absurd (hCother k hki) (by rw [hC]; simp)
  | .recvReleaseAtManager =>
      -- Node i's chanC cleared → condition fails for i. Others: chanC unchanged → use pre-state.
      rcases hstep with ⟨msg, param', htxn, _, _, hflight, hC, _, _, _, _, _, hs'⟩
      rw [hs']
      intro htxn' k hrel ⟨cmsg, hCk, hdata⟩ j hji
      simp [recvReleaseState, recvReleaseShared] at htxn'
      by_cases hki : k = i
      · subst k
        simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn] at hCk
      · simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn, hki] at hrel hCk
        have ⟨cmsg', hC', hdata'⟩ : ∃ msg, (s.locals k).chanC = some msg ∧ msg.data ≠ none :=
          ⟨cmsg, hCk, hdata⟩
        have hpre := hdirtyRelEx htxn k hrel ⟨cmsg', hC', hdata'⟩
        by_cases hji' : j = i
        · subst j; simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn]
          exact hpre i (Ne.symm hki)
        · simp [recvReleaseState, recvReleaseLocals, recvReleaseLocal, setFn, hji']
          exact hpre j hji
  | .recvReleaseAckAtMaster =>
      -- Node i's releaseInFlight cleared → condition fails for i.
      rcases hstep with ⟨msg, htxn, _, _, hflight, _, _, hs'⟩
      rw [hs']
      intro htxn' k hrel ⟨cmsg, hCk, hdata⟩ j hji
      simp [recvReleaseAckState, recvReleaseAckShared] at htxn'
      by_cases hki : k = i
      · subst k
        simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn] at hrel
      · simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn, hki] at hrel hCk
        have ⟨cmsg', hC', hdata'⟩ : ∃ msg, (s.locals k).chanC = some msg ∧ msg.data ≠ none :=
          ⟨cmsg, hCk, hdata⟩
        have hpre := hdirtyRelEx htxn k hrel ⟨cmsg', hC', hdata'⟩
        by_cases hji' : j = i
        · subst j; simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn]
          exact hpre i (Ne.symm hki)
        · simp [recvReleaseAckState, recvReleaseAckLocals, recvReleaseAckLocal, setFn, hji']
          exact hpre j hji
  | .store v =>
      -- Store requires all chanC = none (guard). Contradiction with chanC = some.
      rcases hstep with ⟨hcur, _, _, hCallNone, _, _, _, _, _, _, _, _, hs'⟩
      rw [hs']
      intro htxn' k hrel ⟨cmsg, hCk, hdata⟩ j hji
      by_cases hki : k = i
      · subst k
        have := hCallNone i
        simp [setFn, storeLocal] at hCk
        exact absurd this (by rw [hCk]; simp)
      · have := hCallNone k
        simp [setFn, hki] at hCk
        exact absurd this (by rw [hCk]; simp)
  | .read =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩
      exact hdirtyRelEx
  | .uncachedGet source =>
      rcases hstep with ⟨htxn_s, _, _, _, _, _, _, _, _, _, rfl⟩
      intro _ k hrel ⟨cmsg, hCk, hdata⟩ j hji
      have hrel' : (s.locals k).releaseInFlight = true := by
        by_cases hki : k = i <;> simp_all [setFn]
      have ⟨cmsg', hC', hdata'⟩ : ∃ msg : CMsg, (s.locals k).chanC = some msg ∧ msg.data ≠ none := by
        by_cases hki : k = i <;> simp_all [setFn]
      have := hdirtyRelEx htxn_s k hrel' ⟨cmsg', hC', hdata'⟩ j hji
      by_cases hji' : j = i
      · subst j; simp [setFn]; exact this
      · simp [setFn, hji']; exact this
  | .uncachedPut source v =>
      rcases hstep with ⟨htxn_s, _, _, _, _, _, _, _, _, _, _, rfl⟩
      intro _ k hrel ⟨cmsg, hCk, hdata⟩ j hji
      have hrel' : (s.locals k).releaseInFlight = true := by
        by_cases hki : k = i <;> simp_all [setFn]
      have ⟨cmsg', hC', hdata'⟩ : ∃ msg : CMsg, (s.locals k).chanC = some msg ∧ msg.data ≠ none := by
        by_cases hki : k = i <;> simp_all [setFn]
      have := hdirtyRelEx htxn_s k hrel' ⟨cmsg', hC', hdata'⟩ j hji
      by_cases hji' : j = i
      · subst j; simp [setFn]; exact this
      · simp [setFn, hji']; exact this
  | .recvUncachedAtManager =>
      rcases hstep with ⟨htxn_s, _, _, _, _, _, rfl⟩
      intro _ k hrel ⟨cmsg, hCk, hdata⟩ j hji
      have hrel' : (s.locals k).releaseInFlight = true := by
        by_cases hki : k = i <;> simp_all [setFn]
      have ⟨cmsg', hC', hdata'⟩ : ∃ msg : CMsg, (s.locals k).chanC = some msg ∧ msg.data ≠ none := by
        by_cases hki : k = i <;> simp_all [setFn]
      have := hdirtyRelEx htxn_s k hrel' ⟨cmsg', hC', hdata'⟩ j hji
      by_cases hji' : j = i
      · subst j; simp [setFn]; exact this
      · simp [setFn, hji']; exact this
  | .recvAccessAckAtMaster =>
      rcases hstep with ⟨_, _, _, rfl⟩
      intro htxn' k hrel ⟨cmsg, hCk, hdata⟩ j hji
      have hrel' : (s.locals k).releaseInFlight = true := by
        by_cases hki : k = i <;> simp_all [setFn]
      have ⟨cmsg', hC', hdata'⟩ : ∃ msg : CMsg, (s.locals k).chanC = some msg ∧ msg.data ≠ none := by
        by_cases hki : k = i <;> simp_all [setFn]
      have := hdirtyRelEx htxn' k hrel' ⟨cmsg', hC', hdata'⟩ j hji
      by_cases hji' : j = i
      · subst j; simp [setFn]; exact this
      · simp [setFn, hji']; exact this

theorem refinementInv_preserved (n : Nat)
    (s s' : SymState HomeState NodeState n)
    (hinv : strongRefinementInv n s)
    (hpreWF : preLinesWFInv n s) (htxnTM : txnTransferMemInv n s)
    (hnext : (tlMessages.toSpec n).next s s') :
    refinementInv n s' := by
  rcases hinv with ⟨⟨hfull, hdirtyEx, hSwmr, htxnData, hcleanRel, hrelUniq, hdirtyRelEx⟩, htxnLine, hpreClean, hpreNoDirty, htxnPlan, husedDirty, hdirtyOwner⟩
  have hfwd : strongRefinementInv n s := ⟨⟨hfull, hdirtyEx, hSwmr, htxnData, hcleanRel, hrelUniq, hdirtyRelEx⟩, htxnLine, hpreClean, hpreNoDirty, htxnPlan, husedDirty, hdirtyOwner⟩
  exact ⟨fullInv_preserved_with_release n s s' hfull htxnLine hnext,
    dirtyExclusiveInv_preserved n s s' hfwd hnext,
    permSwmrInv_preserved n s s' hfwd hnext,
    txnDataInv_preserved n s s' hfull hdirtyEx htxnData hcleanRel hpreNoDirty husedDirty hdirtyOwner hpreWF htxnTM hnext,
    cleanChanCInv_preserved n s s' hfull hdirtyEx hcleanRel hrelUniq hnext,
    releaseUniqueInv_preserved n s s' hfull hdirtyEx hrelUniq hnext,
    dirtyReleaseExclusiveInv_preserved n s s' hfull hdirtyEx hSwmr hdirtyRelEx hnext⟩

end TileLink.Messages
