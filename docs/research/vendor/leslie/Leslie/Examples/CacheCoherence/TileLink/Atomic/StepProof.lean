import Leslie.Examples.CacheCoherence.TileLink.Atomic.Invariant

namespace TileLink.Atomic

open TLA TileLink SymShared

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

private theorem swmr_preserved (n : Nat)
    (s s' : SymState HomeState CacheLine n)
    (hswmr : swmr n s) (hwf : lineWF n s)
    (hnext : (tlAtomic.toSpec n).next s s') :
    swmr n s' := by
  simp only [SymSharedSpec.toSpec, tlAtomic] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  intro p q hpq hpT
  match a with
  | .acquireBlock =>
      rcases hstep with ⟨_, _, _, _, hcases⟩
      rcases hcases with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩
      all_goals
        exact hswmr p q hpq hpT
  | .acquirePerm =>
      rcases hstep with ⟨_, _, _, _, hcases⟩
      rcases hcases with ⟨_, _, _, rfl⟩ | ⟨_, rfl⟩
      all_goals
        exact hswmr p q hpq hpT
  | .finishGrant =>
      rcases hstep with ⟨pg, _, _, _, hreq, hcases⟩
      rcases hcases with
        ⟨j, hji, hjdirty, _, _, _, _, _, _, rfl⟩ |
        ⟨_, _, _, _, _, _, _, _, rfl⟩ |
        ⟨hallN, _, _, _, _, _, _, rfl⟩ |
        ⟨j, hji, hjdirty, _, _, _, _, _, _, rfl⟩ |
        ⟨_, _, _, _, _, _, _, rfl⟩
      ·
        by_cases hpi : p = i
        · simp [acquireBlockDirtyLocals, hpi] at hpT
        · by_cases hpj : p = j
          · simp [acquireBlockDirtyLocals, hpj] at hpT
          · have hpTpre : (s.locals p).perm = .T := by
              simpa [acquireBlockDirtyLocals, hpi, hpj] using hpT
            have hjT : (s.locals j).perm = .T := (hwf j).1 hjdirty |>.1
            have hpN : (s.locals p).perm = .N := hswmr j p (fun h => hpj h.symm) hjT
            rw [hpN] at hpTpre
            cases hpTpre
      ·
        by_cases hpi : p = i
        · simp [acquireBlockSharedLocals, hpi] at hpT
        · have hpTpre_or_false : False := by
            by_cases hpTip : (s.locals p).perm = .T
            · have : (branchLine s.shared.mem).perm = .T := by
                simpa [acquireBlockSharedLocals, hpi, hpTip] using hpT
              simp at this
            · have : (s.locals p).perm = .T := by
                simpa [acquireBlockSharedLocals, hpi, hpTip] using hpT
              exact hpTip this
          exact False.elim hpTpre_or_false
      ·
        by_cases hpi : p = i
        · have hqi : q ≠ i := by
            intro h
            exact hpq (hpi ▸ h.symm)
          simpa [setFn, hqi] using hallN q hqi
        · have hpN : (s.locals p).perm = .N := hallN p hpi
          have hpTpre : (s.locals p).perm = .T := by
            simpa [setFn, hpi] using hpT
          rw [hpN] at hpTpre
          cases hpTpre
      ·
        by_cases hpi : p = i
        · have hqi : q ≠ i := by
            intro h
            exact hpq (hpi ▸ h.symm)
          simp [acquirePermLocals, hqi]
        · have hpTfalse : False := by
            have hpTpre : (invalidateLine (s.locals p)).perm = .T := by
              simpa [acquirePermLocals, hpi] using hpT
            simp at hpTpre
          exact False.elim hpTfalse
      ·
        by_cases hpi : p = i
        · have hqi : q ≠ i := by
            intro h
            exact hpq (hpi ▸ h.symm)
          simp [acquirePermLocals, hqi]
        · have hpTfalse : False := by
            have hpTpre : (invalidateLine (s.locals p)).perm = .T := by
              simpa [acquirePermLocals, hpi] using hpT
            simp at hpTpre
          exact False.elim hpTfalse
  | .store v =>
      rcases hstep with ⟨_, _, _, hpreT, rfl⟩
      by_cases hpi : p = i
      · have hqi : q ≠ i := by
          intro h
          exact hpq (hpi ▸ h.symm)
        simp [setFn, hqi]
        exact hswmr i q (fun h => hqi h.symm) hpreT
      · have hpTpre : (s.locals p).perm = .T := by
          simpa [setFn, hpi] using hpT
        have hpN : (s.locals p).perm = .N := by
          exact hswmr i p (fun h => hpi h.symm) hpreT
        rw [hpN] at hpTpre
        cases hpTpre
  | .grantAck =>
      rcases hstep with ⟨_, rfl⟩
      exact hswmr p q hpq hpT
  | .release param =>
      rcases hstep with ⟨_, _, _, hlegal, hclean, _, rfl⟩
      by_cases hpi : p = i
      · have hqi : q ≠ i := by
          intro h
          exact hpq (hpi ▸ h.symm)
        have hresT : param.result = .T := by
          have : (releasedLine (s.locals i) param.result).perm = .T := by
            simpa [setFn, hpi] using hpT
          simpa using this
        cases param <;> simp [PruneReportParam.result] at hresT
        · have hiT : (s.locals i).perm = .T := by
            simpa [PruneReportParam.legalFrom, PruneReportParam.source] using hlegal
          simpa [setFn, hqi, releasedLine] using hswmr i q (fun h => hqi h.symm) hiT
      · have hpTpre : (s.locals p).perm = .T := by
          simpa [setFn, hpi, releasedLine] using hpT
        by_cases hqi : q = i
        · have hiN : (s.locals i).perm = .N := by
            exact hswmr p i (by
              intro h
              exact hpq (h.trans hqi.symm)) hpTpre
          have hresN : param.result = .N := by
            cases param with
            | TtoB =>
                simp [PruneReportParam.legalFrom, PruneReportParam.source, hiN] at hlegal
            | TtoN =>
                simp [PruneReportParam.legalFrom, PruneReportParam.source, hiN] at hlegal
            | BtoN =>
                simp [PruneReportParam.legalFrom, PruneReportParam.source, hiN] at hlegal
            | TtoT =>
                simp [PruneReportParam.legalFrom, PruneReportParam.source, hiN] at hlegal
            | BtoB =>
                simp [PruneReportParam.legalFrom, PruneReportParam.source, hiN] at hlegal
            | NtoN =>
                rfl
          simpa [setFn, hqi, releasedLine, hresN]
        · simpa [setFn, hqi, releasedLine] using hswmr p q hpq hpTpre
  | .releaseData param =>
      rcases hstep with ⟨_, _, _, hlegal, hdirty, rfl⟩
      by_cases hpi : p = i
      · have hqi : q ≠ i := by
          intro h
          exact hpq (hpi ▸ h.symm)
        have hresT : param.result = .T := by
          have : (releasedLine (s.locals i) param.result).perm = .T := by
            simpa [setFn, hpi] using hpT
          simpa using this
        have hiT : (s.locals i).perm = .T := (hwf i).1 hdirty |>.1
        cases param <;> simp [PruneReportParam.result, PruneReportParam.legalFrom, PruneReportParam.source] at hresT hlegal
        simpa [setFn, hqi, releasedLine] using hswmr i q (fun h => hqi h.symm) hiT
      · have hpTpre : (s.locals p).perm = .T := by
          simpa [setFn, hpi, releasedLine] using hpT
        by_cases hqi : q = i
        · have hiN : (s.locals i).perm = .N := by
            exact hswmr p i (by
              intro h
              exact hpq (h.trans hqi.symm)) hpTpre
          have hiT : (s.locals i).perm = .T := (hwf i).1 hdirty |>.1
          rw [hiN] at hiT
          cases hiT
        · simpa [setFn, hqi, releasedLine] using hswmr p q hpq hpTpre
  | .releaseAck =>
      rcases hstep with ⟨_, rfl⟩
      exact hswmr p q hpq hpT
  | .uncachedWrite v =>
      rcases hstep with ⟨_, _, hallN, rfl⟩
      have hpN : (s.locals p).perm = .N := hallN p
      rw [hpN] at hpT; cases hpT

private theorem pendingInv_preserved (n : Nat)
    (s s' : SymState HomeState CacheLine n)
    (hpending : pendingInv n s)
    (hnext : (tlAtomic.toSpec n).next s s') :
    pendingInv n s' := by
  simp only [SymSharedSpec.toSpec, tlAtomic] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  rcases hpending with ⟨hgrant, hrel, hnone⟩
  match a with
  | .acquireBlock =>
      rcases hstep with ⟨_, hgrantNone, hrelNone, _, hcases⟩
      rcases hcases with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩
      all_goals
        refine ⟨?_, ?_, Or.inl (by simpa using hgrantNone)⟩
        · intro p hp
          simp [hgrantNone] at hp
        · intro p hp
          simp [hrelNone] at hp
  | .acquirePerm =>
      rcases hstep with ⟨_, hgrantNone, hrelNone, _, hcases⟩
      rcases hcases with ⟨_, _, _, rfl⟩ | ⟨_, rfl⟩
      all_goals
        refine ⟨?_, ?_, Or.inl (by simpa using hgrantNone)⟩
        · intro p hp
          simp [hgrantNone] at hp
        · intro p hp
          simp [hrelNone] at hp
  | .finishGrant =>
      rcases hstep with ⟨pg, _, hgrantNone, hrelNone, hreq, hcases⟩
      rcases hcases with
        ⟨j, _, _, _, _, _, _, _, _, rfl⟩ |
        ⟨_, _, _, _, _, _, _, _, rfl⟩ |
        ⟨_, _, _, _, _, _, _, rfl⟩ |
        ⟨j, _, _, _, _, _, _, _, _, rfl⟩ |
        ⟨_, _, _, _, _, _, _, rfl⟩
      all_goals
        refine ⟨?_, ?_, Or.inr (by simpa using hrelNone)⟩
        · intro p hp
          have hpi : p = i := by
            apply Fin.ext
            simpa using hp.symm
          subst hpi
          simp [acquireBlockDirtyLocals, acquireBlockSharedLocals, acquirePermLocals, setFn]
        · intro p hp
          simp [hrelNone] at hp
  | .store v =>
      rcases hstep with ⟨_, hgrantNone, hrelNone, _, rfl⟩
      refine ⟨?_, ?_, Or.inl hgrantNone⟩
      · intro p hp
        have : False := by
          simp [hgrantNone] at hp
        exact False.elim this
      · intro p hp
        have : False := by
          simp [hrelNone] at hp
        exact False.elim this
  | .grantAck =>
      rcases hstep with ⟨hgrantSome, rfl⟩
      have hrelNone : s.shared.pendingReleaseAck = none := by
        cases hnone with
        | inl h =>
            have : False := by rw [h] at hgrantSome; simp at hgrantSome
            exact False.elim this
        | inr h => exact h
      refine ⟨?_, ?_, Or.inl rfl⟩
      · intro p hp
        simp at hp
      · intro p hp
        exact hrel p hp
  | .release param =>
      rcases hstep with ⟨_, hgrantNone, hrelNone, _, _, _, _, rfl⟩
      refine ⟨?_, ?_, Or.inl rfl⟩
      · intro p hp
        simp at hp
      · intro p hp
        have hpi : p = i := by
          apply Fin.ext
          simp at hp
          exact hp.symm
        subst hpi
        have hdirty := releasedLine_dirty (s.locals p) param.result
        simpa [setFn] using hdirty
  | .releaseData param =>
      rcases hstep with ⟨_, hgrantNone, hrelNone, _, _, _, rfl⟩
      refine ⟨?_, ?_, Or.inl rfl⟩
      · intro p hp
        simp at hp
      · intro p hp
        have hpi : p = i := by
          apply Fin.ext
          simp at hp
          exact hp.symm
        subst hpi
        have hdirty := releasedLine_dirty (s.locals p) param.result
        simpa [setFn] using hdirty
  | .releaseAck =>
      rcases hstep with ⟨hrelSome, rfl⟩
      refine ⟨?_, ?_, Or.inr rfl⟩
      · intro p hp
        exact hgrant p hp
      · intro p hp
        simp at hp
  | .uncachedWrite v =>
      rcases hstep with ⟨_, hgrantNone, _, rfl⟩
      refine ⟨?_, ?_, Or.inl (by simpa using hgrantNone)⟩
      · intro p hp; simp [hgrantNone] at hp
      · intro p hp; exact hrel p hp

private theorem dirInv_preserved (n : Nat)
    (s s' : SymState HomeState CacheLine n)
    (hdir : dirInv n s)
    (hnext : (tlAtomic.toSpec n).next s s') :
    dirInv n s' := by
  simp only [SymSharedSpec.toSpec, tlAtomic] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  intro p
  match a with
  | .acquireBlock =>
      rcases hstep with ⟨_, _, _, _, hcases⟩
      rcases hcases with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩
      all_goals
        exact hdir p
  | .acquirePerm =>
      rcases hstep with ⟨_, _, _, _, hcases⟩
      rcases hcases with ⟨_, _, _, rfl⟩ | ⟨_, rfl⟩
      all_goals
        exact hdir p
  | .finishGrant =>
      rcases hstep with ⟨pg, _, _, _, _, hcases⟩
      rcases hcases with
        ⟨j, _, _, _, _, _, _, _, _, rfl⟩ |
        ⟨_, _, _, _, _, _, _, _, rfl⟩ |
        ⟨_, _, _, _, _, _, _, rfl⟩ |
        ⟨_, _, _, _, _, _, _, _, _, rfl⟩ |
        ⟨_, _, _, _, _, _, _, rfl⟩
      all_goals
        simp [syncDir_apply_fin]
  | .store v =>
      rcases hstep with ⟨_, _, _, hpreT, rfl⟩
      by_cases hpi : p = i
      · simpa [hpi, hpreT] using hdir p
      · simpa [setFn, hpi] using hdir p
  | .grantAck =>
      rcases hstep with ⟨_, rfl⟩
      exact hdir p
  | .release param =>
      rcases hstep with ⟨_, _, _, _, _, _, _, rfl⟩
      simp [syncDir_apply_fin]
  | .releaseData param =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩
      simp [syncDir_apply_fin]
  | .releaseAck =>
      rcases hstep with ⟨_, rfl⟩
      exact hdir p
  | .uncachedWrite v =>
      rcases hstep with ⟨_, _, _, rfl⟩
      exact hdir p

private theorem lineWF_preserved (n : Nat)
    (s s' : SymState HomeState CacheLine n)
    (hwf : lineWF n s) (hnext : (tlAtomic.toSpec n).next s s') :
    lineWF n s' := by
  simp only [SymSharedSpec.toSpec, tlAtomic] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  intro p
  match a with
  | .acquireBlock =>
      rcases hstep with ⟨_, _, _, _, hcases⟩
      rcases hcases with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩
      all_goals
        exact hwf p
  | .acquirePerm =>
      rcases hstep with ⟨_, _, _, _, hcases⟩
      rcases hcases with ⟨_, _, _, rfl⟩ | ⟨_, rfl⟩
      all_goals
        exact hwf p
  | .finishGrant =>
      rcases hstep with ⟨pg, _, _, _, _, hcases⟩
      rcases hcases with
        ⟨j, _, _, _, _, _, _, _, _, rfl⟩ |
        ⟨_, _, _, _, _, _, _, _, rfl⟩ |
        ⟨_, _, _, _, _, _, _, rfl⟩ |
        ⟨_, _, _, _, _, _, _, _, _, rfl⟩ |
        ⟨_, _, _, _, _, _, _, rfl⟩
      · by_cases hpi : p = i
        · simp [acquireBlockDirtyLocals, hpi]
        · by_cases hpj : p = j
          · simp [acquireBlockDirtyLocals, hpj]
          · simpa [acquireBlockDirtyLocals, hpi, hpj] using hwf p
      · by_cases hpi : p = i
        · simp [acquireBlockSharedLocals, hpi]
        · by_cases hpTip : (s.locals p).perm = .T
          · simp [acquireBlockSharedLocals, hpi, hpTip]
          · simpa [acquireBlockSharedLocals, hpi, hpTip] using hwf p
      · by_cases hpi : p = i
        · simp [setFn, hpi]
        · simpa [setFn, hpi] using hwf p
      · by_cases hpi : p = i
        · simp [acquirePermLocals, hpi]
        · simp [acquirePermLocals, hpi]
      · by_cases hpi : p = i
        · simp [acquirePermLocals, hpi]
        · simp [acquirePermLocals, hpi]
  | .store v =>
      rcases hstep with ⟨_, _, _, _, rfl⟩
      by_cases hpi : p = i
      · simp [setFn, hpi]
      · simpa [setFn, hpi] using hwf p
  | .grantAck =>
      rcases hstep with ⟨_, rfl⟩
      exact hwf p
  | .release param =>
      rcases hstep with ⟨_, _, _, _, _, _, _, rfl⟩
      by_cases hpi : p = i
      · have hwf' := releasedLine_wf (s.locals i) param.result
        simpa [setFn, hpi] using hwf'
      · simpa [setFn, hpi] using hwf p
  | .releaseData param =>
      rcases hstep with ⟨_, _, _, _, _, _, rfl⟩
      by_cases hpi : p = i
      · have hwf' := releasedLine_wf (s.locals i) param.result
        simpa [setFn, hpi] using hwf'
      · simpa [setFn, hpi] using hwf p
  | .releaseAck =>
      rcases hstep with ⟨_, rfl⟩
      exact hwf p
  | .uncachedWrite v =>
      rcases hstep with ⟨_, _, _, rfl⟩
      exact hwf p

private theorem cleanDataInv_preserved (n : Nat)
    (s s' : SymState HomeState CacheLine n)
    (hcleanData : cleanDataInv n s) (hswmr : swmr n s) (hwf : lineWF n s)
    (hnext : (tlAtomic.toSpec n).next s s') :
    cleanDataInv n s' := by
  simp only [SymSharedSpec.toSpec, tlAtomic] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  intro p hpvalid hpclean
  match a with
  | .acquireBlock =>
      rcases hstep with ⟨_, _, _, _, hcases⟩
      rcases hcases with ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩
      all_goals
        exact hcleanData p hpvalid hpclean
  | .acquirePerm =>
      rcases hstep with ⟨_, _, _, _, hcases⟩
      rcases hcases with ⟨_, _, _, rfl⟩ | ⟨_, rfl⟩
      all_goals
        exact hcleanData p hpvalid hpclean
  | .finishGrant =>
      rcases hstep with ⟨pg, _, _, _, hreq, hcases⟩
      rcases hcases with
        ⟨j, hji, hjdirty, _, _, _, _, _, _, rfl⟩ |
        ⟨_, _, _, _, _, _, _, _, rfl⟩ |
        ⟨hallN, _, _, _, _, _, _, rfl⟩ |
        ⟨j, hji, hjdirty, _, _, _, _, _, _, rfl⟩ |
        ⟨_, _, _, _, _, _, _, rfl⟩
      ·
        by_cases hpi : p = i
        · subst hpi
          simp [acquireBlockDirtyLocals]
        · by_cases hpj : p = j
          · subst hpj
            simp [acquireBlockDirtyLocals]
          · have hjT : (s.locals j).perm = .T := (hwf j).1 hjdirty |>.1
            have hpN : (s.locals p).perm = .N := hswmr j p (fun h => hpj h.symm) hjT
            have hpvalidPre : (s.locals p).valid = true := by
              simpa [acquireBlockDirtyLocals, hpi, hpj] using hpvalid
            have hpvalidFalse : (s.locals p).valid = false := (hwf p).2.2 hpN |>.1
            rw [hpvalidFalse] at hpvalidPre
            cases hpvalidPre
      ·
        by_cases hpi : p = i
        · subst hpi
          simp [acquireBlockSharedLocals]
        · by_cases hpTip : (s.locals p).perm = .T
          · simp [acquireBlockSharedLocals, hpi, hpTip]
          · have hpvalidPre : (s.locals p).valid = true := by
              simpa [acquireBlockSharedLocals, hpi, hpTip] using hpvalid
            have hpcleanPre : (s.locals p).dirty = false := by
              simpa [acquireBlockSharedLocals, hpi, hpTip] using hpclean
            simpa [acquireBlockSharedLocals, hpi, hpTip] using hcleanData p hpvalidPre hpcleanPre
      ·
        by_cases hpi : p = i
        · subst hpi
          simp [setFn]
        · have hpN : (s.locals p).perm = .N := hallN p hpi
          have hpvalidPre : (s.locals p).valid = true := by
            simpa [setFn, hpi] using hpvalid
          have hpvalidFalse : (s.locals p).valid = false := (hwf p).2.2 hpN |>.1
          rw [hpvalidFalse] at hpvalidPre
          cases hpvalidPre
      ·
        by_cases hpi : p = i
        · have : False := by
            simpa [acquirePermLocals, hpi] using hpvalid
          exact False.elim this
        · have : False := by
            simpa [acquirePermLocals, hpi] using hpvalid
          exact False.elim this
      ·
        by_cases hpi : p = i
        · have : False := by
            simpa [acquirePermLocals, hpi] using hpvalid
          exact False.elim this
        · have : False := by
            simpa [acquirePermLocals, hpi] using hpvalid
          exact False.elim this
  | .store v =>
      rcases hstep with ⟨_, _, _, hpreT, rfl⟩
      by_cases hpi : p = i
      · have : False := by
          simpa [setFn, hpi] using hpclean
        exact False.elim this
      · -- p ≠ i: under SWMR, perm p = .N so not valid — contradiction
        have hpN : (s.locals p).perm = .N := hswmr i p (fun h => hpi h.symm) hpreT
        have hpvalidFalse : (s.locals p).valid = false := (hwf p).2.2 hpN |>.1
        have hpvalidPre : (s.locals p).valid = true := by
          simpa [setFn, hpi] using hpvalid
        rw [hpvalidFalse] at hpvalidPre; cases hpvalidPre
  | .grantAck =>
      rcases hstep with ⟨_, rfl⟩
      exact hcleanData p hpvalid hpclean
  | .release param =>
      rcases hstep with ⟨_, _, _, _, hcleanPre, hvalidOrN, rfl⟩
      by_cases hpi : p = i
      · subst hpi
        have hvalidPre : (s.locals p).valid = true := by
          rcases hvalidOrN with hvalidPre | hresN
          · exact hvalidPre
          · have : False := by
              simp [setFn, releasedLine, hresN] at hpvalid
            exact False.elim this
        have hdata : (s.locals p).data = s.shared.mem := hcleanData p hvalidPre hcleanPre
        cases hres : param.result <;> simpa [setFn, releasedLine, hres] using hdata
      · have hpvalidPre : (s.locals p).valid = true := by
          simpa [setFn, hpi] using hpvalid
        have hpcleanPre : (s.locals p).dirty = false := by
          simpa [setFn, hpi] using hpclean
        simpa [setFn, hpi] using hcleanData p hpvalidPre hpcleanPre
  | .releaseData param =>
      rcases hstep with ⟨_, _, _, _, hdirty, rfl⟩
      by_cases hpi : p = i
      · subst hpi
        simpa [setFn, releasedLine] using releasedLine_data (s.locals p) param.result
      · have hiT : (s.locals i).perm = .T := (hwf i).1 hdirty |>.1
        have hpN : (s.locals p).perm = .N := hswmr i p (fun h => hpi h.symm) hiT
        have hpvalidPre : (s.locals p).valid = true := by
          simpa [setFn, hpi] using hpvalid
        have hpvalidFalse : (s.locals p).valid = false := (hwf p).2.2 hpN |>.1
        rw [hpvalidFalse] at hpvalidPre
        cases hpvalidPre
  | .releaseAck =>
      rcases hstep with ⟨_, rfl⟩
      exact hcleanData p hpvalid hpclean
  | .uncachedWrite v =>
      rcases hstep with ⟨_, _, hallN, rfl⟩
      have hpN : (s.locals p).perm = .N := hallN p
      have hpvalidFalse : (s.locals p).valid = false := (hwf p).2.2 hpN |>.1
      rw [hpvalidFalse] at hpvalid; cases hpvalid

private theorem grantMetaInv_preserved (n : Nat)
    (s s' : SymState HomeState CacheLine n)
    (hmetaInv : grantMetaInv n s) (hnext : (tlAtomic.toSpec n).next s s') :
    grantMetaInv n s' := by
  simp only [SymSharedSpec.toSpec, tlAtomic] at hnext
  obtain ⟨i, a, hstep⟩ := hnext
  match a with
  | .acquireBlock =>
      rcases hstep with ⟨_, hgrantNone, hrelNone, _, hcases⟩
      rcases hcases with ⟨j, hji, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩
      · refine ⟨i.is_lt, by simpa using hrelNone, ?_, ?_, Or.inl ?_⟩
        · simp [grantMetaShape]
        · simp [singleProbeMask]
          intro h
          exact hji (Fin.ext h.symm)
        · refine ⟨by simpa using hgrantNone, ?_, trivial⟩
          intro k
          simp [singleProbeMask]
      · refine ⟨i.is_lt, by simpa using hrelNone, ?_, ?_, Or.inl ?_⟩
        · simp [grantMetaShape]
        · simp [writableProbeMask]
        · refine ⟨by simpa using hgrantNone, ?_, trivial⟩
          intro k
          simp [writableProbeMask]
      · refine ⟨i.is_lt, by simpa using hrelNone, ?_, ?_, Or.inl ?_⟩
        · simp [grantMetaShape]
        · simp
        · refine ⟨by simpa using hgrantNone, ?_, trivial⟩
          intro k
          simp
  | .acquirePerm =>
      rcases hstep with ⟨_, hgrantNone, hrelNone, _, hcases⟩
      rcases hcases with ⟨_, _, _, rfl⟩ | ⟨_, rfl⟩
      all_goals
        refine ⟨i.is_lt, by simpa using hrelNone, ?_, ?_, Or.inl ?_⟩
        · simp [grantMetaShape]
        · simp [cachedProbeMask]
        · refine ⟨by simpa using hgrantNone, ?_, trivial⟩
          intro k
          simp [cachedProbeMask]
  | .finishGrant =>
      rcases hstep with ⟨pg, hmetaSome, hgrantNone, hrelNone, hreq, hcases⟩
      rcases hcases with
        ⟨j, hji, _, hkind, hperm, _, _, hneed, _, rfl⟩ |
        ⟨_, _, hkind, hperm, _, _, hneed, _, rfl⟩ |
        ⟨_, hkind, hperm, _, _, hneed, _, rfl⟩ |
        ⟨j, hji, _, hkind, hperm, _, _, hneed, _, rfl⟩ |
        ⟨_, hkind, hperm, _, _, hneed, _, rfl⟩
      · refine ⟨by simpa [deliveredGrantMeta, hreq] using i.is_lt,
          by simpa using hrelNone,
          by simpa [deliveredGrantMeta, grantMetaShape, hkind, hperm],
          ?_, Or.inr ?_⟩
        · simp [deliveredGrantMeta, hneed, hreq, singleProbeMask]
          intro h
          exact hji (Fin.ext h.symm)
        · refine ⟨by simpa [deliveredGrantMeta, hreq], ?_, trivial⟩
          intro k
          simp [deliveredGrantMeta, noProbeMask]
      · refine ⟨by simpa [deliveredGrantMeta, hreq] using i.is_lt,
          by simpa using hrelNone,
          by simpa [deliveredGrantMeta, grantMetaShape, hkind, hperm],
          by simp [deliveredGrantMeta, hneed, hreq, writableProbeMask],
          Or.inr ?_⟩
        refine ⟨by simpa [deliveredGrantMeta, hreq], ?_, trivial⟩
        intro k
        simp [deliveredGrantMeta, noProbeMask]
      · refine ⟨by simpa [deliveredGrantMeta, hreq] using i.is_lt,
          by simpa using hrelNone,
          by simpa [deliveredGrantMeta, grantMetaShape, hkind, hperm],
          by simp [deliveredGrantMeta, hneed, hreq],
          Or.inr ?_⟩
        refine ⟨by simpa [deliveredGrantMeta, hreq], ?_, trivial⟩
        intro k
        simp [deliveredGrantMeta, noProbeMask]
      · refine ⟨by simpa [deliveredGrantMeta, hreq] using i.is_lt,
          by simpa using hrelNone,
          by simpa [deliveredGrantMeta, grantMetaShape, hkind, hperm],
          by simp [deliveredGrantMeta, hneed, hreq, cachedProbeMask],
          Or.inr ?_⟩
        refine ⟨by simpa [deliveredGrantMeta, hreq], ?_, trivial⟩
        intro k
        simp [deliveredGrantMeta, noProbeMask]
      · refine ⟨by simpa [deliveredGrantMeta, hreq] using i.is_lt,
          by simpa using hrelNone,
          by simpa [deliveredGrantMeta, grantMetaShape, hkind, hperm],
          by simp [deliveredGrantMeta, hneed, hreq, cachedProbeMask],
          Or.inr ?_⟩
        refine ⟨by simpa [deliveredGrantMeta, hreq], ?_, trivial⟩
        intro k
        simp [deliveredGrantMeta, noProbeMask]
  | .store v =>
      rcases hstep with ⟨hmetaNone, hgrantNone, _, _, rfl⟩
      simpa [grantMetaInv, hmetaNone, hgrantNone]
  | .grantAck =>
      rcases hstep with ⟨_, rfl⟩
      simp [grantMetaInv]
  | .release param =>
      rcases hstep with ⟨hmetaNone, hgrantNone, _, _, _, _, _, rfl⟩
      simpa [grantMetaInv, hmetaNone, hgrantNone]
  | .releaseData param =>
      rcases hstep with ⟨hmetaNone, hgrantNone, _, _, _, _, rfl⟩
      simpa [grantMetaInv, hmetaNone, hgrantNone]
  | .releaseAck =>
      rcases hstep with ⟨hrelSome, rfl⟩
      cases hmeta : s.shared.pendingGrantMeta with
      | none =>
          simpa [grantMetaInv, hmeta] using hmetaInv
      | some pg =>
          have : False := by
            rw [grantMetaInv, hmeta] at hmetaInv
            rcases hmetaInv with ⟨_, hrelNone, _⟩
            rw [hrelSome] at hrelNone
            simp at hrelNone
          exact False.elim this
  | .uncachedWrite v =>
      rcases hstep with ⟨hmetaNone, _, _, rfl⟩
      simpa [grantMetaInv, hmetaNone] using hmetaInv

def atomicInv (n : Nat) (s : SymState HomeState CacheLine n) : Prop :=
  swmr n s ∧ pendingInv n s ∧ grantMetaInv n s ∧ dirInv n s ∧ lineWF n s ∧ cleanDataInv n s

theorem atomicInv_preserved (n : Nat)
    (s s' : SymState HomeState CacheLine n)
    (hinv : atomicInv n s) (hnext : (tlAtomic.toSpec n).next s s') :
    atomicInv n s' := by
  rcases hinv with ⟨hswmr, hpending, hmetaInv, hdir, hwf, hcleanData⟩
  exact ⟨swmr_preserved n s s' hswmr hwf hnext,
         pendingInv_preserved n s s' hpending hnext,
         grantMetaInv_preserved n s s' hmetaInv hnext,
         dirInv_preserved n s s' hdir hnext,
         lineWF_preserved n s s' hwf hnext,
         cleanDataInv_preserved n s s' hcleanData hswmr hwf hnext⟩

end TileLink.Atomic
