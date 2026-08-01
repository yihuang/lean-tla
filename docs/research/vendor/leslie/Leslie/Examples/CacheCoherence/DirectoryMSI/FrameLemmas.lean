import Leslie.Examples.CacheCoherence.DirectoryMSI.InitProof

namespace DirectoryMSI

/-! ## Frame Lemmas

    For each invariant component, a theorem stating: "if the fields this component
    reads are equal between s and s', the component is preserved."

    These eliminate the trivial cases in StepProof -- any action whose footprint
    is disjoint from a component's read-set is closed by the appropriate theorem here.
-/

-- Group A: components that read only `cache`

theorem ctrlProp_preserved_of_cache_eq {n : Nat} {s s' : MState n}
    (hc : s'.cache = s.cache) (h : ctrlProp n s) : ctrlProp n s' := by
  intro i j hij; rw [hc]; exact h i j hij

theorem ackImpliesInvalid_preserved_of_c2dChan_cache_eq {n : Nat} {s s' : MState n}
    (hc2d : s'.c2dChan = s.c2dChan) (hca : s'.cache = s.cache)
    (h : ackImpliesInvalid n s) : ackImpliesInvalid n s' := by
  intro i hi; rw [hc2d] at hi; rw [hca]; exact h i hi

-- Group B: components that read `cache`, `dirSt`

theorem exclusiveExcludesShared_preserved_of_cache_dirSt_d2cChan_eq {n : Nat} {s s' : MState n}
    (hca : s'.cache = s.cache) (hd : s'.dirSt = s.dirSt) (hd2c : s'.d2cChan = s.d2cChan)
    (h : exclusiveExcludesShared n s) : exclusiveExcludesShared n s' := by
  intro hExcl i hi; rw [hca] at hi; rw [hd] at hExcl; rw [hd2c]; exact h hExcl i hi

theorem uncachedMeansAllInvalid_preserved_of_cache_dirSt_eq {n : Nat} {s s' : MState n}
    (hca : s'.cache = s.cache) (hd : s'.dirSt = s.dirSt)
    (h : uncachedMeansAllInvalid n s) : uncachedMeansAllInvalid n s' := by
  intro hUnc i; rw [hca]; rw [hd] at hUnc; exact h hUnc i

-- Group C: components that read `cache`, `dirSt`, `exNode`

theorem mImpliesExclusive_preserved_of_cache_dirSt_exNode_eq {n : Nat} {s s' : MState n}
    (hca : s'.cache = s.cache) (hd : s'.dirSt = s.dirSt) (he : s'.exNode = s.exNode)
    (h : mImpliesExclusive n s) : mImpliesExclusive n s' := by
  intro i hi; rw [hca] at hi; obtain ⟨hd', he'⟩ := h i hi
  exact ⟨hd.symm ▸ hd', he.symm ▸ he'⟩

-- Group D: components that read `cache`, `shrSet`

theorem sImpliesShrSet_preserved_of_cache_shrSet_curCmd_curNode_d2cChan_eq {n : Nat} {s s' : MState n}
    (hca : s'.cache = s.cache) (hs : s'.shrSet = s.shrSet)
    (hcc : s'.curCmd = s.curCmd) (hcn : s'.curNode = s.curNode)
    (hd2c : s'.d2cChan = s.d2cChan)
    (h : sImpliesShrSet n s) : sImpliesShrSet n s' := by
  intro i hi; rw [hca] at hi; rw [hs, hcc, hcn, hd2c]; exact h i hi

theorem invSetSubsetShrSet_preserved_of_invSet_shrSet_eq {n : Nat} {s s' : MState n}
    (hi : s'.invSet = s.invSet) (hs : s'.shrSet = s.shrSet)
    (h : invSetSubsetShrSet n s) : invSetSubsetShrSet n s' := by
  intro i hii; rw [hi] at hii; rw [hs]; exact h i hii

-- Group E: components that read `d2cChan`, `auxData`

theorem gntSDataProp_preserved_of_d2cChan_auxData_eq {n : Nat} {s s' : MState n}
    (hd2c : s'.d2cChan = s.d2cChan) (ha : s'.auxData = s.auxData)
    (h : gntSDataProp n s) : gntSDataProp n s' := by
  intro i hi; rw [hd2c] at hi; rw [hd2c, ha]; exact h i hi

theorem gntEDataProp_preserved_of_d2cChan_auxData_eq {n : Nat} {s s' : MState n}
    (hd2c : s'.d2cChan = s.d2cChan) (ha : s'.auxData = s.auxData)
    (h : gntEDataProp n s) : gntEDataProp n s' := by
  intro i hi; rw [hd2c] at hi; rw [hd2c, ha]; exact h i hi

-- Group F: components that read `d2cChan`, `curCmd`

theorem invImpliesCurCmd_preserved_of_d2cChan_curCmd_eq {n : Nat} {s s' : MState n}
    (hd2c : s'.d2cChan = s.d2cChan) (hcc : s'.curCmd = s.curCmd)
    (h : invImpliesCurCmd n s) : invImpliesCurCmd n s' := by
  intro i hi; rw [hd2c] at hi; rw [hcc]; exact h i hi

-- Group G: components that read `d2cChan`, `dirSt`

theorem sharedNoGntE_preserved_of_d2cChan_dirSt_eq {n : Nat} {s s' : MState n}
    (hd2c : s'.d2cChan = s.d2cChan) (hd : s'.dirSt = s.dirSt)
    (h : sharedNoGntE n s) : sharedNoGntE n s' := by
  intro hSh i; rw [hd2c]; rw [hd] at hSh; exact h hSh i

-- Group H: components that read `d2cChan`, `dirSt`, `exNode`

theorem gntEImpliesExclusive_preserved_of_d2cChan_dirSt_exNode_eq {n : Nat} {s s' : MState n}
    (hd2c : s'.d2cChan = s.d2cChan) (hd : s'.dirSt = s.dirSt) (he : s'.exNode = s.exNode)
    (h : gntEImpliesExclusive n s) : gntEImpliesExclusive n s' := by
  intro i hi; rw [hd2c] at hi; obtain ⟨hd', he'⟩ := h i hi
  exact ⟨hd.symm ▸ hd', he.symm ▸ he'⟩

theorem exclusiveNoDuplicateGrant_preserved_of_d2cChan_dirSt_exNode_eq {n : Nat} {s s' : MState n}
    (hd2c : s'.d2cChan = s.d2cChan) (hd : s'.dirSt = s.dirSt) (he : s'.exNode = s.exNode)
    (h : exclusiveNoDuplicateGrant n s) : exclusiveNoDuplicateGrant n s' := by
  intro hExcl i hne; rw [hd2c]; rw [hd] at hExcl; rw [he] at hne; exact h hExcl i hne

theorem fetchImpliesCurCmdGetS_preserved_of_d2cChan_curCmd_dirSt_exNode_eq {n : Nat} {s s' : MState n}
    (hd2c : s'.d2cChan = s.d2cChan) (hcc : s'.curCmd = s.curCmd)
    (hd : s'.dirSt = s.dirSt) (he : s'.exNode = s.exNode)
    (h : fetchImpliesCurCmdGetS n s) : fetchImpliesCurCmdGetS n s' := by
  intro i hi; rw [hd2c] at hi
  obtain ⟨hcc', hd', he'⟩ := h i hi
  exact ⟨hcc.symm ▸ hcc', hd.symm ▸ hd', he.symm ▸ he'⟩

-- Group I: curNodeNotInInvSet

theorem curNodeNotInInvSet_preserved_of_curCmd_dirSt_invSet_curNode_eq {n : Nat} {s s' : MState n}
    (hcc : s'.curCmd = s.curCmd) (hd : s'.dirSt = s.dirSt)
    (hi : s'.invSet = s.invSet) (hcn : s'.curNode = s.curNode)
    (h : curNodeNotInInvSet n s) : curNodeNotInInvSet n s' := by
  intro hgm hsh
  rw [hcc] at hgm; rw [hd] at hsh; rw [hi, hcn]; exact h hgm hsh

-- Group J: ackDataProp

theorem ackDataProp_preserved_of_c2dChan_cache_dirSt_auxData_eq {n : Nat} {s s' : MState n}
    (hc2d : s'.c2dChan = s.c2dChan) (hca : s'.cache = s.cache)
    (hd : s'.dirSt = s.dirSt) (ha : s'.auxData = s.auxData)
    (h : ackDataProp n s) : ackDataProp n s' := by
  intro i hi hcond
  rw [hc2d] at hi; rw [hca, hd] at hcond; rw [hc2d, ha]; exact h i hi hcond

-- Group K: ackImpliesInvSetFalse reads c2dChan, invSet

theorem ackImpliesInvSetFalse_preserved_of_c2dChan_invSet_eq {n : Nat} {s s' : MState n}
    (hc2d : s'.c2dChan = s.c2dChan) (hi : s'.invSet = s.invSet)
    (h : ackImpliesInvSetFalse n s) : ackImpliesInvSetFalse n s' := by
  intro i hack; rw [hc2d] at hack; rw [hi]; exact h i hack

-- Group L: invSetImpliesCurCmdGetM reads invSet, curCmd

theorem invSetImpliesCurCmdGetM_preserved_of_invSet_curCmd_eq {n : Nat} {s s' : MState n}
    (hi : s'.invSet = s.invSet) (hcc : s'.curCmd = s.curCmd)
    (h : invSetImpliesCurCmdGetM n s) : invSetImpliesCurCmdGetM n s' := by
  intro i hii; rw [hi] at hii; rw [hcc]; exact h i hii

-- Group M: ackImpliesCurCmdNotEmpty reads c2dChan, curCmd

theorem ackImpliesCurCmdNotEmpty_preserved_of_c2dChan_curCmd_eq {n : Nat} {s s' : MState n}
    (hc2d : s'.c2dChan = s.c2dChan) (hcc : s'.curCmd = s.curCmd)
    (h : ackImpliesCurCmdNotEmpty n s) : ackImpliesCurCmdNotEmpty n s' := by
  intro i hack; rw [hc2d] at hack; rw [hcc]; exact h i hack

-- Group N: getSAckProp reads c2dChan, curCmd, dirSt, exNode

theorem getSAckProp_preserved_of_c2dChan_curCmd_dirSt_exNode_eq {n : Nat} {s s' : MState n}
    (hc2d : s'.c2dChan = s.c2dChan) (hcc : s'.curCmd = s.curCmd)
    (hd : s'.dirSt = s.dirSt) (he : s'.exNode = s.exNode)
    (h : getSAckProp n s) : getSAckProp n s' := by
  intro i hack hgetS; rw [hc2d] at hack; rw [hcc] at hgetS
  obtain ⟨hd', he'⟩ := h i hack hgetS
  exact ⟨hd.symm ▸ hd', he.symm ▸ he'⟩

-- Group O: invAckExclusive reads d2cChan, c2dChan

theorem invAckExclusive_preserved_of_d2cChan_c2dChan_eq {n : Nat} {s s' : MState n}
    (hd2c : s'.d2cChan = s.d2cChan) (hc2d : s'.c2dChan = s.c2dChan)
    (h : invAckExclusive n s) : invAckExclusive n s' := by
  intro i hinv; rw [hd2c] at hinv; rw [hc2d]; exact h i hinv

-- Group P: invSetImpliesDirShared reads invSet, dirSt

theorem invSetImpliesDirShared_preserved_of_invSet_dirSt_eq {n : Nat} {s s' : MState n}
    (hi : s'.invSet = s.invSet) (hd : s'.dirSt = s.dirSt)
    (h : invSetImpliesDirShared n s) : invSetImpliesDirShared n s' := by
  intro i hii; rw [hi] at hii; rw [hd]; exact h i hii

-- Group Q: invMsgImpliesShrSet reads d2cChan, dirSt, shrSet

theorem invMsgImpliesShrSet_preserved_of_d2cChan_dirSt_shrSet_eq {n : Nat} {s s' : MState n}
    (hd2c : s'.d2cChan = s.d2cChan) (hd : s'.dirSt = s.dirSt) (hs : s'.shrSet = s.shrSet)
    (h : invMsgImpliesShrSet n s) : invMsgImpliesShrSet n s' := by
  intro i hinv hsh; rw [hd2c] at hinv; rw [hd] at hsh; rw [hs]; exact h i hinv hsh

-- Group R: ackSharedImpliesShrSet reads c2dChan, dirSt, shrSet

theorem ackSharedImpliesShrSet_preserved_of_c2dChan_dirSt_shrSet_eq {n : Nat} {s s' : MState n}
    (hc2d : s'.c2dChan = s.c2dChan) (hd : s'.dirSt = s.dirSt) (hs : s'.shrSet = s.shrSet)
    (h : ackSharedImpliesShrSet n s) : ackSharedImpliesShrSet n s' := by
  intro i hack hsh; rw [hc2d] at hack; rw [hd] at hsh; rw [hs]; exact h i hack hsh

-- Group S: invExclOnlyAtExNode reads d2cChan, dirSt, exNode

theorem invExclOnlyAtExNode_preserved_of_d2cChan_dirSt_exNode_eq {n : Nat} {s s' : MState n}
    (hd2c : s'.d2cChan = s.d2cChan) (hd : s'.dirSt = s.dirSt) (he : s'.exNode = s.exNode)
    (h : invExclOnlyAtExNode n s) : invExclOnlyAtExNode n s' := by
  intro i hinv hexcl; rw [hd2c] at hinv; rw [hd] at hexcl; rw [he]; exact h i hinv hexcl

-- Group T: ackExclOnlyAtExNode reads c2dChan, dirSt, exNode

theorem ackExclOnlyAtExNode_preserved_of_c2dChan_dirSt_exNode_eq {n : Nat} {s s' : MState n}
    (hc2d : s'.c2dChan = s.c2dChan) (hd : s'.dirSt = s.dirSt) (he : s'.exNode = s.exNode)
    (h : ackExclOnlyAtExNode n s) : ackExclOnlyAtExNode n s' := by
  intro i hack hexcl; rw [hc2d] at hack; rw [hd] at hexcl; rw [he]; exact h i hack hexcl

-- Group U: ackImpliesDirNotUncached reads c2dChan, dirSt

theorem ackImpliesDirNotUncached_preserved_of_c2dChan_dirSt_eq {n : Nat} {s s' : MState n}
    (hc2d : s'.c2dChan = s.c2dChan) (hd : s'.dirSt = s.dirSt)
    (h : ackImpliesDirNotUncached n s) : ackImpliesDirNotUncached n s' := by
  intro i hack; rw [hc2d] at hack; rw [hd]; exact h i hack

-- Group V: invImpliesDirNotUncached reads d2cChan, dirSt

theorem invImpliesDirNotUncached_preserved_of_d2cChan_dirSt_eq {n : Nat} {s s' : MState n}
    (hd2c : s'.d2cChan = s.d2cChan) (hd : s'.dirSt = s.dirSt)
    (h : invImpliesDirNotUncached n s) : invImpliesDirNotUncached n s' := by
  intro i hinv; rw [hd2c] at hinv; rw [hd]; exact h i hinv

-- Group W: ackImpliesD2cEmpty reads c2dChan, d2cChan

theorem ackImpliesD2cEmpty_preserved_of_c2dChan_d2cChan_eq {n : Nat} {s s' : MState n}
    (hc2d : s'.c2dChan = s.c2dChan) (hd2c : s'.d2cChan = s.d2cChan)
    (h : ackImpliesD2cEmpty n s) : ackImpliesD2cEmpty n s' := by
  intro i hack; rw [hc2d] at hack; rw [hd2c]; exact h i hack

-- Group X: gntSProp reads d2cChan, shrSet, curCmd, curNode

theorem gntSProp_preserved_of_d2cChan_shrSet_curCmd_curNode_eq {n : Nat} {s s' : MState n}
    (hd2c : s'.d2cChan = s.d2cChan) (hs : s'.shrSet = s.shrSet)
    (hcc : s'.curCmd = s.curCmd) (hcn : s'.curNode = s.curNode)
    (h : gntSProp n s) : gntSProp n s' := by
  intro i hgntS; rw [hd2c] at hgntS; rw [hs, hcc, hcn]; exact h i hgntS

-- Group Y: gntSImpliesDirShared reads d2cChan, dirSt

theorem gntSImpliesDirShared_preserved_of_d2cChan_dirSt_eq {n : Nat} {s s' : MState n}
    (hd2c : s'.d2cChan = s.d2cChan) (hd : s'.dirSt = s.dirSt)
    (h : gntSImpliesDirShared n s) : gntSImpliesDirShared n s' := by
  intro i hgntS; rw [hd2c] at hgntS; rw [hd]; exact h i hgntS

-- Group Z: invImpliesInvSetFalse reads d2cChan, invSet

theorem invImpliesInvSetFalse_preserved_of_d2cChan_invSet_eq {n : Nat} {s s' : MState n}
    (hd2c : s'.d2cChan = s.d2cChan) (hiv : s'.invSet = s.invSet)
    (h : invImpliesInvSetFalse n s) : invImpliesInvSetFalse n s' := by
  intro i hinv; rw [hd2c] at hinv; rw [hiv]; exact h i hinv

-- Vacuity helpers: invariant components that are trivially true when
-- dirSt or curCmd takes a specific value

theorem exclusiveConsistent_of_not_exclusive {n : Nat} {s : MState n}
    (h : s.dirSt ≠ .Exclusive) : exclusiveConsistent n s :=
  fun hex => absurd hex h

theorem uncachedMeansAllInvalid_of_not_uncached {n : Nat} {s : MState n}
    (h : s.dirSt ≠ .Uncached) : uncachedMeansAllInvalid n s :=
  fun hunc => absurd hunc h

theorem sharedNoGntE_of_not_shared {n : Nat} {s : MState n}
    (h : s.dirSt ≠ .Shared) : sharedNoGntE n s :=
  fun hsh => absurd hsh h

theorem exclusiveNoDuplicateGrant_of_not_exclusive {n : Nat} {s : MState n}
    (h : s.dirSt ≠ .Exclusive) : exclusiveNoDuplicateGrant n s :=
  fun hex => absurd hex h

theorem curNodeNotInInvSet_of_not_getM {n : Nat} {s : MState n}
    (h : s.curCmd ≠ .getM) : curNodeNotInInvSet n s :=
  fun hgm => absurd hgm h

theorem exclusiveExcludesShared_of_not_exclusive {n : Nat} {s : MState n}
    (h : s.dirSt ≠ .Exclusive) : exclusiveExcludesShared n s :=
  fun hex _ _ => absurd hex h

-- Compound: reqChan-only frame (covers SendGetS, SendGetM)

/-- If only reqChan changed, the full strong invariant is preserved. -/
theorem fullStrongInvariant_preserved_of_reqChan_only {n : Nat} {s s' : MState n}
    (hca  : s'.cache   = s.cache)
    (hd2c : s'.d2cChan = s.d2cChan)
    (hc2d : s'.c2dChan = s.c2dChan)
    (hd   : s'.dirSt   = s.dirSt)
    (hsh  : s'.shrSet  = s.shrSet)
    (he   : s'.exNode  = s.exNode)
    (hcc  : s'.curCmd  = s.curCmd)
    (hcn  : s'.curNode = s.curNode)
    (hiv  : s'.invSet  = s.invSet)
    (hm   : s'.memData = s.memData)
    (ha   : s'.auxData = s.auxData)
    (h    : fullStrongInvariant n s) : fullStrongInvariant n s' := by
  obtain ⟨⟨⟨hctrl, hdata⟩, hexclCons, hmImpl, hsShr, hexclExcl, huncInv,
      hgntSD, hgntED, hinvSub⟩,
      hackD, hcurNot, hexclNoDup, hshrNoE, hgntEImpl, hfetchImpl, hinvImpl, hackInv,
      hackInvSet, hinvSetCmd, hackCmdNotEmpty, hgetSAck,
      hInvAckExcl, hInvSetDirSh, hInvMsgShr, hAckShShr, hInvExclEx, hAckExclEx,
      hAckDirNotUnc, hInvDirNotUnc, hAckD2cEmpty, hGntSProp, hGntSDirSh, hInvInvSet⟩ := h
  exact ⟨⟨⟨ctrlProp_preserved_of_cache_eq hca hctrl,
      by unfold dataProp at *; rw [hd, hm, ha, hca]; exact hdata⟩,
      by unfold exclusiveConsistent at *; rw [hd, hca, hd2c, hc2d, he]; exact hexclCons,
      mImpliesExclusive_preserved_of_cache_dirSt_exNode_eq hca hd he hmImpl,
      sImpliesShrSet_preserved_of_cache_shrSet_curCmd_curNode_d2cChan_eq hca hsh hcc hcn hd2c hsShr,
      exclusiveExcludesShared_preserved_of_cache_dirSt_d2cChan_eq hca hd hd2c hexclExcl,
      uncachedMeansAllInvalid_preserved_of_cache_dirSt_eq hca hd huncInv,
      gntSDataProp_preserved_of_d2cChan_auxData_eq hd2c ha hgntSD,
      gntEDataProp_preserved_of_d2cChan_auxData_eq hd2c ha hgntED,
      invSetSubsetShrSet_preserved_of_invSet_shrSet_eq hiv hsh hinvSub⟩,
      ackDataProp_preserved_of_c2dChan_cache_dirSt_auxData_eq hc2d hca hd ha hackD,
      curNodeNotInInvSet_preserved_of_curCmd_dirSt_invSet_curNode_eq hcc hd hiv hcn hcurNot,
      exclusiveNoDuplicateGrant_preserved_of_d2cChan_dirSt_exNode_eq hd2c hd he hexclNoDup,
      sharedNoGntE_preserved_of_d2cChan_dirSt_eq hd2c hd hshrNoE,
      gntEImpliesExclusive_preserved_of_d2cChan_dirSt_exNode_eq hd2c hd he hgntEImpl,
      fetchImpliesCurCmdGetS_preserved_of_d2cChan_curCmd_dirSt_exNode_eq hd2c hcc hd he hfetchImpl,
      invImpliesCurCmd_preserved_of_d2cChan_curCmd_eq hd2c hcc hinvImpl,
      ackImpliesInvalid_preserved_of_c2dChan_cache_eq hc2d hca hackInv,
      ackImpliesInvSetFalse_preserved_of_c2dChan_invSet_eq hc2d hiv hackInvSet,
      invSetImpliesCurCmdGetM_preserved_of_invSet_curCmd_eq hiv hcc hinvSetCmd,
      ackImpliesCurCmdNotEmpty_preserved_of_c2dChan_curCmd_eq hc2d hcc hackCmdNotEmpty,
      getSAckProp_preserved_of_c2dChan_curCmd_dirSt_exNode_eq hc2d hcc hd he hgetSAck,
      invAckExclusive_preserved_of_d2cChan_c2dChan_eq hd2c hc2d hInvAckExcl,
      invSetImpliesDirShared_preserved_of_invSet_dirSt_eq hiv hd hInvSetDirSh,
      invMsgImpliesShrSet_preserved_of_d2cChan_dirSt_shrSet_eq hd2c hd hsh hInvMsgShr,
      ackSharedImpliesShrSet_preserved_of_c2dChan_dirSt_shrSet_eq hc2d hd hsh hAckShShr,
      invExclOnlyAtExNode_preserved_of_d2cChan_dirSt_exNode_eq hd2c hd he hInvExclEx,
      ackExclOnlyAtExNode_preserved_of_c2dChan_dirSt_exNode_eq hc2d hd he hAckExclEx,
      ackImpliesDirNotUncached_preserved_of_c2dChan_dirSt_eq hc2d hd hAckDirNotUnc,
      invImpliesDirNotUncached_preserved_of_d2cChan_dirSt_eq hd2c hd hInvDirNotUnc,
      ackImpliesD2cEmpty_preserved_of_c2dChan_d2cChan_eq hc2d hd2c hAckD2cEmpty,
      gntSProp_preserved_of_d2cChan_shrSet_curCmd_curNode_eq hd2c hsh hcc hcn hGntSProp,
      gntSImpliesDirShared_preserved_of_d2cChan_dirSt_eq hd2c hd hGntSDirSh,
      invImpliesInvSetFalse_preserved_of_d2cChan_invSet_eq hd2c hiv hInvInvSet⟩

end DirectoryMSI
