import Leslie.Examples.CacheCoherence.DirectoryMSI.FrameLemmas

namespace DirectoryMSI

/-! ## Tier 1 Step Proofs

    Actions with small footprints: RecvGetS_Shared, RecvGetM_Shared,
    RecvAck_GetM_Shared, SendGntS_AfterFetch.
-/

-- ── RecvGetS_Shared ──────────────────────────────────────────────────────
-- Modifies: d2cChan[i] (gntS), shrSet[i] (true), reqChan[i] (clear)
-- Guards: reqChan[i]=getS, curCmd=empty, dirSt=Shared, d2cChan[i]=empty

theorem fullStrongInvariant_preserved_RecvGetS_Shared
    {n : Nat} {s s' : MState n}
    (h : fullStrongInvariant n s)
    (hact : ∃ i, RecvGetS_Shared s s' i) :
    fullStrongInvariant n s' := by
  obtain ⟨i, _hreq, hcurCmd, hdirSt, hd2cEmpty, hs'⟩ := hact; subst hs'
  obtain ⟨⟨⟨hctrl, hdataF, hdataS⟩, hexclCons, hmImpl, hsShr, hexclExcl, huncInv,
    hgntSD, hgntED, hinvSub⟩,
    hackD, hcurNot, hexclNoDup, hshrNoE, hgntEImpl, hfetchImpl, hinvImpl, hackInv,
    hackInvSet, hinvSetCmd, hackCmdNotEmpty, hgetSAck,
    hInvAckExcl, _hInvSetDirSh, hInvMsgShr, hAckShShr, _hInvExclEx, _hAckExclEx,
    hAckDirNotUnc, hInvDirNotUnc, _hAckD2cEmpty, _hGntSProp, _hGntSDirSh, _hInvInvSet⟩ := h
  have hsharedDat : s.memData = s.auxData := hdataF (by rw [hdirSt]; decide)
  simp only [fullStrongInvariant, strongInvariant, invariant, ctrlProp, dataProp,
    exclusiveConsistent, mImpliesExclusive, sImpliesShrSet, exclusiveExcludesShared,
    uncachedMeansAllInvalid, gntSDataProp, gntEDataProp, invSetSubsetShrSet,
    curNodeNotInInvSet, exclusiveNoDuplicateGrant, sharedNoGntE, gntEImpliesExclusive,
    fetchImpliesCurCmdGetS, invImpliesCurCmd, ackDataProp, ackImpliesInvalid,
    ackImpliesInvSetFalse, invSetImpliesCurCmdGetM, getSAckProp,
    invAckExclusive, invSetImpliesDirShared, invMsgImpliesShrSet,
    ackSharedImpliesShrSet, invExclOnlyAtExNode, ackExclOnlyAtExNode,
    ackImpliesDirNotUncached, invImpliesDirNotUncached,
    ackImpliesD2cEmpty, gntSProp, gntSImpliesDirShared,
    recvGetS_SharedState_cache, recvGetS_SharedState_c2dChan,
    recvGetS_SharedState_dirSt, recvGetS_SharedState_exNode,
    recvGetS_SharedState_curCmd, recvGetS_SharedState_curNode,
    recvGetS_SharedState_invSet, recvGetS_SharedState_memData,
    recvGetS_SharedState_auxData]
  -- dirSt=Shared is preserved; d2cChan[i]=gntS, shrSet[i]=true
  refine ⟨⟨⟨hctrl, hdataF, hdataS⟩,
    fun hex => absurd hex (by rw [hdirSt]; decide), -- exclusiveConsistent: Shared≠Exclusive
    hmImpl, -- mImpliesExclusive: cache,dirSt,exNode unchanged
    fun j hj => ?_, -- sImpliesShrSet
    fun hex _ _ => absurd hex (by rw [hdirSt]; decide), -- exclusiveExcludesShared: Shared≠Exclusive
    huncInv,   -- uncachedMeansAllInvalid: cache,dirSt unchanged
    fun k hgntS => ?_, fun k hgntE => ?_, -- gntSDataProp, gntEDataProp
    fun k hk => ?_⟩, -- invSetSubsetShrSet
    hackD, -- ackDataProp: c2dChan,cache,dirSt,auxData unchanged
    hcurNot, -- curNodeNotInInvSet: curCmd,dirSt,invSet,curNode unchanged
    fun hex => absurd hex (by rw [hdirSt]; decide), -- exclusiveNoDuplicateGrant: Shared≠Exclusive
    fun hSh k => ?_, -- sharedNoGntE
    fun k hgntE => ?_, -- gntEImpliesExclusive
    fun k hfetch => ?_, -- fetchImpliesCurCmdGetS
    fun k hk => ?_, -- invImpliesCurCmd
    hackInv, -- ackImpliesInvalid: c2dChan,cache unchanged
    hackInvSet, -- ackImpliesInvSetFalse: c2dChan,invSet unchanged
    hinvSetCmd, -- invSetImpliesCurCmdGetM: invSet,curCmd unchanged
    hackCmdNotEmpty, -- ackImpliesCurCmdNotEmpty: c2dChan,curCmd unchanged
    fun k hk hgetS => absurd hgetS (by rw [hcurCmd]; decide), -- getSAckProp: curCmd=empty≠getS
    fun k hinv => ?_, -- invAckExclusive: d2cChan changes
    _hInvSetDirSh, -- invSetImpliesDirShared: invSet,dirSt unchanged
    fun k hinv hsh => ?_, -- invMsgImpliesShrSet: d2cChan,shrSet change
    fun k hack hsh => ?_, -- ackSharedImpliesShrSet: c2dChan unchanged, shrSet changes
    fun k hinv hexcl => absurd hexcl (by rw [hdirSt]; decide), -- invExclOnlyAtExNode: Shared≠Excl
    fun k hack hexcl => absurd hexcl (by rw [hdirSt]; decide), -- ackExclOnlyAtExNode: Shared≠Excl
    fun k hack => hAckDirNotUnc k hack, -- ackImpliesDirNotUncached: c2dChan,dirSt unchanged
    fun k hinv => ?_, -- invImpliesDirNotUncached: d2cChan changes
    fun k hack => ?_, -- ackImpliesD2cEmpty: d2cChan changes
    fun k hgntS => ?_, -- gntSProp: d2cChan changes
    fun k hgntS => ?_, -- gntSImpliesDirShared: d2cChan changes, dirSt unchanged (Shared)
    ?_⟩ -- invImpliesInvSetFalse
  · -- sImpliesShrSet (weakened: cache unchanged, shrSet[i]=true, curCmd/curNode unchanged)
    by_cases hji : j = i
    · subst hji; exact Or.inl (by simp [recvGetS_SharedState_shrSet_self])
    · rw [recvGetS_SharedState_shrSet_ne s i j hji]
      rcases hsShr j hj with h | ⟨hc, _⟩ | hgntE
      · exact Or.inl h
      · exact absurd hc (by rw [hcurCmd]; decide)
      · exact Or.inr (Or.inr (by rw [recvGetS_SharedState_d2cChan_ne s i j hji]; exact hgntE))
  · -- gntSDataProp
    by_cases hki : k = i
    · subst hki; simp only [recvGetS_SharedState_d2cChan_self] at hgntS ⊢; exact hsharedDat
    · simp only [recvGetS_SharedState_d2cChan_ne s i k hki] at hgntS ⊢; exact hgntSD k hgntS
  · -- gntEDataProp
    by_cases hki : k = i
    · subst hki; simp only [recvGetS_SharedState_d2cChan_self] at hgntE; exact absurd hgntE (by decide)
    · simp only [recvGetS_SharedState_d2cChan_ne s i k hki] at hgntE ⊢; exact hgntED k hgntE
  · -- invSetSubsetShrSet: invSet unchanged, shrSet[i]=true (only grew)
    by_cases hki : k = i
    · subst hki; simp [recvGetS_SharedState_shrSet_self]
    · rw [recvGetS_SharedState_shrSet_ne s i k hki]; exact hinvSub k hk
  · -- sharedNoGntE
    by_cases hki : k = i
    · subst hki; simp [recvGetS_SharedState_d2cChan_self]
    · rw [recvGetS_SharedState_d2cChan_ne s i k hki]; exact hshrNoE hSh k
  · -- gntEImpliesExclusive
    by_cases hki : k = i
    · subst hki; simp only [recvGetS_SharedState_d2cChan_self] at hgntE; exact absurd hgntE (by decide)
    · simp only [recvGetS_SharedState_d2cChan_ne s i k hki] at hgntE; exact hgntEImpl k hgntE
  · -- fetchImpliesCurCmdGetS
    by_cases hki : k = i
    · subst hki; simp only [recvGetS_SharedState_d2cChan_self] at hfetch; exact absurd hfetch (by decide)
    · rw [recvGetS_SharedState_d2cChan_ne s i k hki] at hfetch; exact hfetchImpl k hfetch
  · -- invImpliesCurCmd
    by_cases hki : k = i
    · subst hki; simp only [recvGetS_SharedState_d2cChan_self] at hk; exact absurd hk (by decide)
    · rw [recvGetS_SharedState_d2cChan_ne s i k hki] at hk; exact hinvImpl k hk
  · -- invAckExclusive
    by_cases hki : k = i
    · subst hki; simp only [recvGetS_SharedState_d2cChan_self] at hinv; exact absurd hinv (by decide)
    · rw [recvGetS_SharedState_d2cChan_ne s i k hki] at hinv; exact hInvAckExcl k hinv
  · -- invMsgImpliesShrSet
    by_cases hki : k = i
    · subst hki; simp only [recvGetS_SharedState_d2cChan_self] at hinv; exact absurd hinv (by decide)
    · rw [recvGetS_SharedState_d2cChan_ne s i k hki] at hinv
      rw [recvGetS_SharedState_shrSet_ne s i k hki]; exact hInvMsgShr k hinv hsh
  · -- ackSharedImpliesShrSet: c2dChan unchanged, shrSet[i]→true
    by_cases hki : k = i
    · subst hki; simp [recvGetS_SharedState_shrSet_self]
    · rw [recvGetS_SharedState_shrSet_ne s i k hki]; exact hAckShShr k hack hsh
  · -- invImpliesDirNotUncached: dirSt=Shared≠Uncached
    by_cases hki : k = i
    · subst hki; simp only [recvGetS_SharedState_d2cChan_self] at hinv; exact absurd hinv (by decide)
    · rw [recvGetS_SharedState_d2cChan_ne s i k hki] at hinv; exact hInvDirNotUnc k hinv
  · -- ackImpliesD2cEmpty: no acks (curCmd=empty)
    exact absurd (hackCmdNotEmpty k hack) (by rw [hcurCmd]; decide)
  · -- gntSProp: d2cChan[i]→gntS, shrSet[i]→true
    by_cases hki : k = i
    · subst hki; exact Or.inl (by simp [recvGetS_SharedState_shrSet_self])
    · rw [recvGetS_SharedState_d2cChan_ne s i k hki] at hgntS
      rw [recvGetS_SharedState_shrSet_ne s i k hki]
      rcases _hGntSProp k hgntS with h | h
      · exact Or.inl h
      · exact Or.inr h
  · -- gntSImpliesDirShared: dirSt unchanged (Shared). d2cChan[i]→gntS.
    -- k=i: dirSt=Shared ✓. k≠i: pre gntS → Shared (hGntSDirSh pre, but dirSt=Shared already).
    by_cases hki : k = i
    · subst hki; exact hdirSt
    · rw [recvGetS_SharedState_d2cChan_ne s i k hki] at hgntS; exact _hGntSDirSh k hgntS
  · -- invImpliesInvSetFalse: d2cChan changes, invSet unchanged
    unfold invImpliesInvSetFalse; intro k hinv
    by_cases hki : k = i
    · subst hki; simp [recvGetS_SharedState_d2cChan_self] at hinv
    · rw [recvGetS_SharedState_d2cChan_ne s i k hki] at hinv; exact _hInvInvSet k hinv

-- ── RecvGetM_Shared ──────────────────────────────────────────────────────
-- Modifies: curCmd (getM), curNode (i), invSet (copy shrSet with i=false),
--           shrSet[i] (false), reqChan[i] (clear)
-- Guards: reqChan[i]=getM, curCmd=empty, dirSt=Shared

theorem fullStrongInvariant_preserved_RecvGetM_Shared
    {n : Nat} {s s' : MState n}
    (h : fullStrongInvariant n s)
    (hact : ∃ i, RecvGetM_Shared s s' i) :
    fullStrongInvariant n s' := by
  obtain ⟨i, _hreq, hcurCmd, hdirSt, hs'⟩ := hact; subst hs'
  obtain ⟨⟨⟨hctrl, hdataF, hdataS⟩, hexclCons, hmImpl, hsShr, hexclExcl, huncInv,
    hgntSD, hgntED, hinvSub⟩,
    hackD, _hcurNot, hexclNoDup, hshrNoE, hgntEImpl, hfetchImpl, hinvImpl, hackInv,
    hackInvSet2, _hinvSetCmd, hackCmdNotEmpty, _hgetSAck,
    _hInvAckExcl2, _hInvSetDirSh, _hInvMsgShr, _hAckShShr, _hInvExclEx, _hAckExclEx,
    hAckDirNotUnc, hInvDirNotUnc, _hAckD2cEmpty, _hGntSProp, _hGntSDirSh, _hInvInvSet⟩ := h
  simp only [fullStrongInvariant, strongInvariant, invariant, ctrlProp, dataProp,
    exclusiveConsistent, mImpliesExclusive, sImpliesShrSet, exclusiveExcludesShared,
    uncachedMeansAllInvalid, gntSDataProp, gntEDataProp, invSetSubsetShrSet,
    curNodeNotInInvSet, exclusiveNoDuplicateGrant, sharedNoGntE, gntEImpliesExclusive,
    fetchImpliesCurCmdGetS, invImpliesCurCmd, ackDataProp, ackImpliesInvalid,
    ackImpliesInvSetFalse, invSetImpliesCurCmdGetM, getSAckProp,
    invAckExclusive, invSetImpliesDirShared, invMsgImpliesShrSet,
    ackSharedImpliesShrSet, invExclOnlyAtExNode, ackExclOnlyAtExNode,
    ackImpliesDirNotUncached, invImpliesDirNotUncached,
    ackImpliesD2cEmpty, gntSProp, gntSImpliesDirShared,
    recvGetM_SharedState_cache, recvGetM_SharedState_d2cChan,
    recvGetM_SharedState_c2dChan, recvGetM_SharedState_dirSt,
    recvGetM_SharedState_exNode, recvGetM_SharedState_curCmd,
    recvGetM_SharedState_curNode, recvGetM_SharedState_memData,
    recvGetM_SharedState_auxData]
  -- cache, d2cChan, c2dChan, dirSt, exNode, memData, auxData unchanged
  refine ⟨⟨⟨hctrl, hdataF, hdataS⟩,
    fun hex => absurd hex (by rw [hdirSt]; decide), -- exclusiveConsistent
    hmImpl, -- mImpliesExclusive
    fun j hj => ?_, -- sImpliesShrSet
    fun hex _ _ => absurd hex (by rw [hdirSt]; decide), -- Shared≠Exclusive
    huncInv, hgntSD, hgntED, -- unchanged fields
    fun k hk => ?_⟩, -- invSetSubsetShrSet
    hackD, -- ackDataProp
    fun _hgm _hsh => by simp [recvGetM_SharedState_invSet_self, recvGetM_SharedState_curNode],
    fun hex => absurd hex (by rw [hdirSt]; decide), -- exclusiveNoDuplicateGrant
    hshrNoE, -- sharedNoGntE: d2cChan,dirSt unchanged
    hgntEImpl, -- gntEImpliesExclusive: d2cChan,dirSt,exNode unchanged
    fun k hfetch => ?_, -- fetchImpliesCurCmdGetS
    fun k hk => by decide, -- invImpliesCurCmd: curCmd'=getM
    hackInv, -- ackImpliesInvalid
    fun k hack => absurd (hackCmdNotEmpty k hack) (by rw [hcurCmd]; decide),
    fun k hk => ?_, -- invSetImpliesCurCmdGetM
    fun k hack => absurd (hackCmdNotEmpty k hack) (by rw [hcurCmd]; decide),
    fun k hk hgetS => absurd hgetS (by decide), -- getSAckProp: curCmd'=getM≠getS
    _hInvAckExcl2, -- invAckExclusive: d2cChan,c2dChan unchanged
    fun k hk => ?_, -- invSetImpliesDirShared: invSet changes, dirSt=Shared
    fun k hinv _ => absurd (hinvImpl k hinv) (by rw [hcurCmd]; decide), -- no invs (curCmd=empty)
    fun k hack _ => absurd (hackCmdNotEmpty k hack) (by rw [hcurCmd]; decide), -- no acks
    fun k hinv hexcl => absurd hexcl (by rw [hdirSt]; decide), -- Shared≠Exclusive
    fun k hack hexcl => absurd hexcl (by rw [hdirSt]; decide), -- Shared≠Exclusive
    hAckDirNotUnc, -- ackImpliesDirNotUncached: c2dChan unchanged
    hInvDirNotUnc, -- invImpliesDirNotUncached: d2cChan,dirSt unchanged
    _hAckD2cEmpty, -- ackImpliesD2cEmpty: c2dChan unchanged, d2cChan unchanged
    fun k hgntS => ?_, -- gntSProp: shrSet[i], curCmd, curNode change
    fun k hgntS => ?_, -- gntSImpliesDirShared: d2cChan unchanged, dirSt unchanged (Shared)
    by unfold invImpliesInvSetFalse; intro k hinv; exact absurd (hinvImpl k hinv) (by rw [hcurCmd]; decide)⟩ -- invImpliesInvSetFalse
  · -- sImpliesShrSet: NEEDS STRENGTHENING
    by_cases hji : j = i
    · subst hji; exact Or.inr (Or.inl ⟨by simp [recvGetM_SharedState_curCmd],
        by simp [recvGetM_SharedState_curNode]⟩)
    · rw [recvGetM_SharedState_shrSet_ne s i j hji]
      rcases hsShr j hj with h | ⟨hc, _⟩ | hgntE
      · exact Or.inl h
      · exact absurd hc (by rw [hcurCmd]; decide)
      · exact Or.inr (Or.inr hgntE) -- d2cChan unchanged
  · -- invSetSubsetShrSet: invSet'[k] = shrSet[k] for k≠i, invSet'[i]=false
    by_cases hki : k = i
    · subst hki; simp [recvGetM_SharedState_invSet_self] at hk
    · rw [recvGetM_SharedState_invSet_ne s i k hki] at hk
      rw [recvGetM_SharedState_shrSet_ne s i k hki]; exact hk
  · -- fetchImpliesCurCmdGetS: old fetch → curCmd=getS, but curCmd=empty → contradiction
    obtain ⟨hcc', _, _⟩ := hfetchImpl k hfetch
    exact absurd hcc' (by rw [hcurCmd]; decide)
  · -- invSetImpliesCurCmdGetM: curCmd'=getM, so trivially true
    trivial
  · -- invSetImpliesDirShared: dirSt'=Shared, so conclusion trivially holds
    exact hdirSt
  · -- gntSProp: d2cChan unchanged, shrSet[i]→false, curCmd→getM, curNode→i
    by_cases hki : k = i
    · subst hki; right; constructor
      · simp [recvGetM_SharedState_curCmd]
      · simp [recvGetM_SharedState_curNode]
    · rw [recvGetM_SharedState_shrSet_ne s i k hki]
      rcases _hGntSProp k hgntS with h | ⟨hc, _⟩
      · exact Or.inl h
      · exact absurd hc (by rw [hcurCmd]; decide)
  · -- gntSImpliesDirShared: d2cChan unchanged, dirSt unchanged (Shared)
    exact _hGntSDirSh k hgntS

-- ── RecvAck_GetM_Shared ──────────────────────────────────────────────────
-- Modifies: c2dChan[j] (clear), shrSet[j] (false)
-- Guards: c2dChan[j]=ack, curCmd=getM, dirSt=Shared

theorem fullStrongInvariant_preserved_RecvAck_GetM_Shared
    {n : Nat} {s s' : MState n}
    (h : fullStrongInvariant n s)
    (hact : ∃ j, RecvAck_GetM_Shared s s' j) :
    fullStrongInvariant n s' := by
  obtain ⟨j, hc2d, hcurCmd, hdirSt, hs'⟩ := hact; subst hs'
  obtain ⟨⟨⟨hctrl, hdataF, hdataS⟩, hexclCons, hmImpl, hsShr, hexclExcl, huncInv,
    hgntSD, hgntED, hinvSub⟩,
    hackD, hcurNot, hexclNoDup, hshrNoE, hgntEImpl, hfetchImpl, hinvImpl, hackInv,
    hackInvSet, hinvSetCmd, hackCmdNotEmpty, hgetSAck,
    hInvAckExcl, _hInvSetDirSh, hInvMsgShr, hAckShShr, _hInvExclEx, _hAckExclEx,
    hAckDirNotUnc, _hInvDirNotUnc, _hAckD2cEmpty, _hGntSProp, _hGntSDirSh, _hInvInvSet⟩ := h
  have hackJ : (s.cache j).state = .I := hackInv j hc2d
  simp only [fullStrongInvariant, strongInvariant, invariant, ctrlProp, dataProp,
    exclusiveConsistent, mImpliesExclusive, sImpliesShrSet, exclusiveExcludesShared,
    uncachedMeansAllInvalid, gntSDataProp, gntEDataProp, invSetSubsetShrSet,
    curNodeNotInInvSet, exclusiveNoDuplicateGrant, sharedNoGntE, gntEImpliesExclusive,
    fetchImpliesCurCmdGetS, invImpliesCurCmd, ackDataProp, ackImpliesInvalid,
    ackImpliesInvSetFalse, invSetImpliesCurCmdGetM, getSAckProp,
    invAckExclusive, invSetImpliesDirShared, invMsgImpliesShrSet,
    ackSharedImpliesShrSet, invExclOnlyAtExNode, ackExclOnlyAtExNode,
    ackImpliesDirNotUncached, invImpliesDirNotUncached,
    ackImpliesD2cEmpty, gntSProp, gntSImpliesDirShared,
    recvAck_GetM_SharedState_cache, recvAck_GetM_SharedState_d2cChan,
    recvAck_GetM_SharedState_dirSt, recvAck_GetM_SharedState_exNode,
    recvAck_GetM_SharedState_curCmd, recvAck_GetM_SharedState_curNode,
    recvAck_GetM_SharedState_invSet, recvAck_GetM_SharedState_memData,
    recvAck_GetM_SharedState_auxData]
  -- cache, d2cChan, dirSt, exNode, curCmd, curNode, invSet, memData, auxData unchanged
  refine ⟨⟨⟨hctrl, hdataF, hdataS⟩,
    fun hex => absurd hex (by rw [hdirSt]; decide), -- exclusiveConsistent: Shared≠Exclusive
    hmImpl,
    fun k hk => ?_, -- sImpliesShrSet
    fun hex _ _ => absurd hex (by rw [hdirSt]; decide), -- Shared≠Exclusive
    huncInv, hgntSD, hgntED,
    fun k hk => ?_⟩, -- invSetSubsetShrSet
    fun k hk hcond => ?_, -- ackDataProp
    hcurNot, -- curNodeNotInInvSet
    fun hex => absurd hex (by rw [hdirSt]; decide), -- exclusiveNoDuplicateGrant
    hshrNoE, hgntEImpl, hfetchImpl, hinvImpl,
    fun k hk => ?_, -- ackImpliesInvalid
    fun k hk => ?_, -- ackImpliesInvSetFalse
    hinvSetCmd, -- invSetImpliesCurCmdGetM: invSet,curCmd unchanged
    fun k hk => ?_,  -- ackImpliesCurCmdNotEmpty
    fun k hk hgetS => absurd hgetS (by rw [hcurCmd]; decide), -- getSAckProp: curCmd=getM≠getS
    fun k hinv => ?_, -- invAckExclusive: c2dChan[j]→empty
    _hInvSetDirSh, -- invSetImpliesDirShared: invSet,dirSt unchanged
    fun k hinv hsh => ?_, -- invMsgImpliesShrSet: shrSet[j]→false
    fun k hack hsh => ?_, -- ackSharedImpliesShrSet: c2dChan[j]→empty
    fun k hinv hexcl => absurd hexcl (by rw [hdirSt]; decide), -- Shared≠Exclusive
    fun k hack hexcl => absurd hexcl (by rw [hdirSt]; decide), -- Shared≠Exclusive
    fun k hack => ?_, -- ackImpliesDirNotUncached
    _hInvDirNotUnc, -- invImpliesDirNotUncached: d2cChan,dirSt unchanged
    fun k hack => ?_, -- ackImpliesD2cEmpty: c2dChan[j] cleared
    fun k hgntS => ?_, -- gntSProp: shrSet[j] changes
    fun k hgntS => ?_, -- gntSImpliesDirShared: d2cChan,dirSt unchanged
    invImpliesInvSetFalse_preserved_of_d2cChan_invSet_eq rfl rfl _hInvInvSet⟩ -- invImpliesInvSetFalse
  · -- sImpliesShrSet: cache[j]=I, so j can't be S → premise false for j
    by_cases hkj : k = j
    · subst hkj; rw [hackJ] at hk; exact absurd hk (by decide)
    · rw [recvAck_GetM_SharedState_shrSet_ne s j k hkj]; exact hsShr k hk
  · -- invSetSubsetShrSet: invSet unchanged, shrSet[j]=false
    by_cases hkj : k = j
    · subst hkj; have := hackInvSet k hc2d; simp [this] at hk
    · rw [recvAck_GetM_SharedState_shrSet_ne s j k hkj]; exact hinvSub k hk
  · -- ackDataProp: c2dChan[j] cleared
    by_cases hkj : k = j
    · subst hkj; simp [recvAck_GetM_SharedState_c2dChan_self] at hk
    · simp only [recvAck_GetM_SharedState_c2dChan_ne s j k hkj] at hk hcond ⊢
      exact hackD k hk hcond
  · -- ackImpliesInvalid: c2dChan[j] cleared
    by_cases hkj : k = j
    · subst hkj; simp [recvAck_GetM_SharedState_c2dChan_self] at hk
    · simp only [recvAck_GetM_SharedState_c2dChan_ne s j k hkj] at hk; exact hackInv k hk
  · -- ackImpliesInvSetFalse: c2dChan[j] cleared, invSet unchanged
    by_cases hkj : k = j
    · subst hkj; simp [recvAck_GetM_SharedState_c2dChan_self] at hk
    · simp only [recvAck_GetM_SharedState_c2dChan_ne s j k hkj] at hk
      exact hackInvSet k hk
  · -- ackImpliesCurCmdNotEmpty: c2dChan[j] cleared, curCmd unchanged
    by_cases hkj : k = j
    · subst hkj; simp [recvAck_GetM_SharedState_c2dChan_self] at hk
    · simp only [recvAck_GetM_SharedState_c2dChan_ne s j k hkj] at hk
      exact hackCmdNotEmpty k hk
  · -- invAckExclusive: c2dChan[j]→empty, d2cChan unchanged
    by_cases hkj : k = j
    · subst hkj; simp [recvAck_GetM_SharedState_c2dChan_self]
    · simp only [recvAck_GetM_SharedState_c2dChan_ne s j k hkj]; exact hInvAckExcl k hinv
  · -- invMsgImpliesShrSet: d2cChan unchanged, shrSet[j]→false
    by_cases hkj : k = j
    · subst hkj
      -- d2cChan[j]=inv → c2dChan[j]≠ack by invAckExclusive. But c2dChan[j]=ack. Contradiction.
      exact absurd hc2d (hInvAckExcl k hinv)
    · rw [recvAck_GetM_SharedState_shrSet_ne s j k hkj]; exact hInvMsgShr k hinv hsh
  · -- ackSharedImpliesShrSet: c2dChan[j]→empty
    by_cases hkj : k = j
    · subst hkj; simp [recvAck_GetM_SharedState_c2dChan_self] at hack
    · simp only [recvAck_GetM_SharedState_c2dChan_ne s j k hkj] at hack
      rw [recvAck_GetM_SharedState_shrSet_ne s j k hkj]; exact hAckShShr k hack hsh
  · -- ackImpliesDirNotUncached: c2dChan[j]→empty, dirSt=Shared≠Uncached
    by_cases hkj : k = j
    · subst hkj; simp [recvAck_GetM_SharedState_c2dChan_self] at hack
    · simp only [recvAck_GetM_SharedState_c2dChan_ne s j k hkj] at hack
      exact hAckDirNotUnc k hack
  · -- ackImpliesD2cEmpty: c2dChan[j]→empty, d2cChan unchanged
    by_cases hkj : k = j
    · subst hkj; simp [recvAck_GetM_SharedState_c2dChan_self] at hack
    · simp only [recvAck_GetM_SharedState_c2dChan_ne s j k hkj] at hack
      exact _hAckD2cEmpty k hack
  · -- gntSProp: d2cChan unchanged, shrSet[j]→false
    by_cases hkj : k = j
    · subst hkj
      -- gntS at j with c2dChan[j]=ack → by ackImpliesD2cEmpty, d2cChan[j]=empty≠gntS
      exact absurd (_hAckD2cEmpty k hc2d) (by rw [hgntS]; decide)
    · rw [recvAck_GetM_SharedState_shrSet_ne s j k hkj]
      exact _hGntSProp k hgntS
  · -- gntSImpliesDirShared: d2cChan,dirSt unchanged (Shared)
    exact _hGntSDirSh k hgntS

-- ── SendGntS_AfterFetch ──────────────────────────────────────────────────
-- Modifies: d2cChan[curNode] (gntS with memData), dirSt (Shared),
--           shrSet[curNode] (true), curCmd (empty)
-- Guards: curCmd=getS, dirSt=Uncached, d2cChan[curNode]=empty

theorem fullStrongInvariant_preserved_SendGntS_AfterFetch
    {n : Nat} {s s' : MState n}
    (h : fullStrongInvariant n s)
    (hact : SendGntS_AfterFetch s s') :
    fullStrongInvariant n s' := by
  obtain ⟨hcurCmd, hdirSt, _hd2c, hs'⟩ := hact; subst hs'
  obtain ⟨⟨⟨hctrl, hdataF, hdataS⟩, _hexclCons, _hmImpl, hsShr, _hexclExcl, huncInv,
    hgntSD, hgntED, hinvSub⟩,
    hackD, _hcurNot, _hexclNoDup, _hshrNoE, hgntEImpl, hfetchImpl, hinvImpl, hackInv,
    _hackInvSet, _hinvSetCmd, hackCmdNotEmpty, hgetSAck,
    hInvAckExcl, _hInvSetDirSh, _hInvMsgShr, _hAckShShr, _hInvExclEx, _hAckExclEx,
    _hAckDirNotUnc, hInvDirNotUnc, _hAckD2cEmpty2, _hGntSProp, _hGntSDirSh, _hInvInvSet2⟩ := h
  have hAllI : ∀ k : Fin n, (s.cache k).state = .I := huncInv hdirSt
  have hmemEqAux : s.memData = s.auxData := hdataF (by rw [hdirSt]; decide)
  simp only [fullStrongInvariant, strongInvariant, invariant, ctrlProp, dataProp,
    exclusiveConsistent, mImpliesExclusive, sImpliesShrSet, exclusiveExcludesShared,
    uncachedMeansAllInvalid, gntSDataProp, gntEDataProp, invSetSubsetShrSet,
    curNodeNotInInvSet, exclusiveNoDuplicateGrant, sharedNoGntE, gntEImpliesExclusive,
    fetchImpliesCurCmdGetS, invImpliesCurCmd, ackDataProp, ackImpliesInvalid,
    ackImpliesInvSetFalse, invSetImpliesCurCmdGetM, getSAckProp,
    invAckExclusive, invSetImpliesDirShared, invMsgImpliesShrSet,
    ackSharedImpliesShrSet, invExclOnlyAtExNode, ackExclOnlyAtExNode,
    ackImpliesDirNotUncached, invImpliesDirNotUncached,
    ackImpliesD2cEmpty, gntSProp, gntSImpliesDirShared,
    sendGntS_AfterFetchState_cache, sendGntS_AfterFetchState_c2dChan,
    sendGntS_AfterFetchState_dirSt, sendGntS_AfterFetchState_exNode,
    sendGntS_AfterFetchState_curCmd, sendGntS_AfterFetchState_curNode,
    sendGntS_AfterFetchState_invSet, sendGntS_AfterFetchState_memData,
    sendGntS_AfterFetchState_auxData]
  refine ⟨⟨⟨hctrl,
    fun _ => hmemEqAux, hdataS⟩,
    fun hex => absurd hex (by decide), -- exclusiveConsistent: Shared≠Exclusive
    fun j hjM => absurd (hAllI j) (by rw [hjM]; decide), -- mImpliesExclusive: all I
    fun j hj => absurd (hAllI j) (by rw [hj]; decide), -- sImpliesShrSet: all I
    fun hex _ _ => absurd hex (by decide), -- exclusiveExcludesShared: Shared≠Exclusive
    fun hunc => absurd hunc (by decide), -- uncachedMeansAllInvalid: Shared≠Uncached
    fun k hgntS => ?_, fun k hgntE => ?_, -- gntSDataProp, gntEDataProp
    fun k hk => ?_⟩, -- invSetSubsetShrSet
    fun k hk hcond => hackD k hk (hcond.imp id (fun h => absurd h (by decide))),
    fun hgetM => absurd hgetM (by decide), -- curNodeNotInInvSet: curCmd'=empty≠getM
    fun hex => absurd hex (by decide), -- exclusiveNoDuplicateGrant: Shared≠Exclusive
    fun _hSh k => ?_, -- sharedNoGntE
    fun k hgntE => ?_, -- gntEImpliesExclusive
    fun k hfetch => ?_, -- fetchImpliesCurCmdGetS
    fun k hinv => ?_, -- invImpliesCurCmd
    hackInv, -- ackImpliesInvalid
    _hackInvSet, -- ackImpliesInvSetFalse: c2dChan unchanged, invSet unchanged
    fun k hk => ?_, -- invSetImpliesCurCmdGetM
    fun k hack => by
      -- curCmd'=empty, need curCmd'≠empty. By getSAckProp: ack ∧ curCmd=getS → dirSt=Exclusive.
      -- But dirSt=Uncached, contradiction. So no acks exist.
      exact absurd (hgetSAck k hack hcurCmd).1 (by rw [hdirSt]; decide),
    fun k hack hgetS => absurd hgetS (by decide), -- getSAckProp: curCmd'=empty≠getS
    fun k hinv => ?_, -- invAckExclusive: d2cChan changes
    fun _ _ => trivial, -- invSetImpliesDirShared: dirSt'=Shared, trivially true
    fun k hinv hsh => ?_, -- invMsgImpliesShrSet: d2cChan changes, dirSt→Shared
    fun k hack hsh => ?_, -- ackSharedImpliesShrSet: c2dChan unchanged, dirSt→Shared
    fun k hinv hexcl => absurd hexcl (by decide), -- invExclOnlyAtExNode: Shared≠Exclusive
    fun k hack hexcl => absurd hexcl (by decide), -- ackExclOnlyAtExNode: Shared≠Exclusive
    fun k hack => ?_, -- ackImpliesDirNotUncached: dirSt→Shared≠Uncached
    fun k hinv => ?_, -- invImpliesDirNotUncached: dirSt→Shared≠Uncached
    fun k hack => ?_, -- ackImpliesD2cEmpty: no acks (curCmd=getS, dirSt=Uncached)
    fun k hgntS => ?_, -- gntSProp: d2cChan[curNode]→gntS, shrSet[curNode]→true
    fun k hgntS => ?_, -- gntSImpliesDirShared: d2cChan changes, dirSt→Shared
    ?_⟩ -- invImpliesInvSetFalse
  · -- gntSDataProp
    by_cases hk : k = s.curNode
    · subst hk; simp only [sendGntS_AfterFetchState_d2cChan_curNode]; exact hmemEqAux
    · rw [sendGntS_AfterFetchState_d2cChan_ne s k hk] at hgntS ⊢; exact hgntSD k hgntS
  · -- gntEDataProp
    by_cases hk : k = s.curNode
    · subst hk; simp only [sendGntS_AfterFetchState_d2cChan_curNode] at hgntE
      exact absurd hgntE (by decide)
    · rw [sendGntS_AfterFetchState_d2cChan_ne s k hk] at hgntE ⊢; exact hgntED k hgntE
  · -- invSetSubsetShrSet
    by_cases hki : k = s.curNode
    · subst hki; simp [sendGntS_AfterFetchState_shrSet_curNode]
    · rw [sendGntS_AfterFetchState_shrSet_ne s k hki]; exact hinvSub k hk
  · -- sharedNoGntE: no gntE when dirSt was Uncached
    by_cases hk : k = s.curNode
    · subst hk; simp [sendGntS_AfterFetchState_d2cChan_curNode]
    · rw [sendGntS_AfterFetchState_d2cChan_ne s k hk]
      intro hgntE; exact absurd (hgntEImpl k hgntE).1 (by rw [hdirSt]; decide)
  · -- gntEImpliesExclusive
    by_cases hk : k = s.curNode
    · subst hk; simp only [sendGntS_AfterFetchState_d2cChan_curNode] at hgntE
      exact absurd hgntE (by decide)
    · rw [sendGntS_AfterFetchState_d2cChan_ne s k hk] at hgntE
      exact absurd (hgntEImpl k hgntE).1 (by rw [hdirSt]; decide)
  · -- fetchImpliesCurCmdGetS
    by_cases hk : k = s.curNode
    · subst hk; simp only [sendGntS_AfterFetchState_d2cChan_curNode] at hfetch
      exact absurd hfetch (by decide)
    · rw [sendGntS_AfterFetchState_d2cChan_ne s k hk] at hfetch
      exact absurd (hfetchImpl k hfetch).2.1 (by rw [hdirSt]; decide)
  · -- invImpliesCurCmd: curCmd'=empty, need curCmd'≠empty. inv can't exist when dirSt=Uncached.
    by_cases hkc : k = s.curNode
    · subst hkc; simp only [sendGntS_AfterFetchState_d2cChan_curNode] at hinv
      exact absurd hinv (by decide)
    · rw [sendGntS_AfterFetchState_d2cChan_ne s k hkc] at hinv
      exact absurd (hinvImpl k hinv) (by rw [hcurCmd]; decide)
  · -- invSetImpliesCurCmdGetM: invSet unchanged, curCmd'=empty. No invSet entries exist.
    exact absurd (_hinvSetCmd k hk) (by rw [hcurCmd]; decide)
  · -- invAckExclusive: d2cChan[curNode]→gntS, gntS≠inv
    by_cases hk : k = s.curNode
    · subst hk; simp only [sendGntS_AfterFetchState_d2cChan_curNode] at hinv
      exact absurd hinv (by decide)
    · rw [sendGntS_AfterFetchState_d2cChan_ne s k hk] at hinv; exact hInvAckExcl k hinv
  · -- invMsgImpliesShrSet: no invs (curCmd=getS, invImpliesCurCmd→getM, contradiction)
    by_cases hk : k = s.curNode
    · subst hk; simp only [sendGntS_AfterFetchState_d2cChan_curNode] at hinv
      exact absurd hinv (by decide)
    · rw [sendGntS_AfterFetchState_d2cChan_ne s k hk] at hinv
      exact absurd (hinvImpl k hinv) (by rw [hcurCmd]; decide)
  · -- ackSharedImpliesShrSet: no acks (getSAckProp→Exclusive, dirSt=Uncached)
    exact absurd (hgetSAck k hack hcurCmd).1 (by rw [hdirSt]; decide)
  · -- ackImpliesDirNotUncached: dirSt'=Shared≠Uncached
    intro hunc; exact absurd hunc (by decide)
  · -- invImpliesDirNotUncached: dirSt'=Shared≠Uncached
    by_cases hk : k = s.curNode
    · subst hk; simp only [sendGntS_AfterFetchState_d2cChan_curNode] at hinv
      exact absurd hinv (by decide)
    · rw [sendGntS_AfterFetchState_d2cChan_ne s k hk] at hinv
      intro hunc; exact absurd hunc (by decide)
  · -- ackImpliesD2cEmpty: no acks (getSAckProp→Exclusive, dirSt=Uncached, contradiction)
    exact absurd (hgetSAck k hack hcurCmd).1 (by rw [hdirSt]; decide)
  · -- gntSProp: d2cChan[curNode]→gntS, shrSet[curNode]→true
    by_cases hk : k = s.curNode
    · subst hk; exact Or.inl (by simp [sendGntS_AfterFetchState_shrSet_curNode])
    · rw [sendGntS_AfterFetchState_d2cChan_ne s k hk] at hgntS
      rw [sendGntS_AfterFetchState_shrSet_ne s k hk]
      -- Pre: curCmd=getS. gntSProp pre: gntS → shrSet=true ∨ (curCmd=getM ∧ curNode=k)
      -- curCmd=getS≠getM. So shrSet=true.
      rcases _hGntSProp k hgntS with h | ⟨hc, _⟩
      · exact Or.inl h
      · exact absurd hc (by rw [hcurCmd]; decide)
  · -- gntSImpliesDirShared: dirSt'=Shared. d2cChan[curNode]→gntS.
    -- k=curNode: dirSt'=Shared ✓. k≠curNode: pre gntS → Shared (_hGntSDirSh).
    -- But pre dirSt=Uncached. gntS at k≠curNode pre → _hGntSDirSh → Shared. Uncached≠Shared.
    by_cases hk : k = s.curNode
    · subst hk; trivial
    · rw [sendGntS_AfterFetchState_d2cChan_ne s k hk] at hgntS
      exact absurd (_hGntSDirSh k hgntS) (by rw [hdirSt]; decide)
  · -- invImpliesInvSetFalse
    unfold invImpliesInvSetFalse; intro k hinv
    by_cases hk : k = s.curNode
    · subst hk; simp only [sendGntS_AfterFetchState_d2cChan_curNode] at hinv; exact absurd hinv (by decide)
    · rw [sendGntS_AfterFetchState_d2cChan_ne s k hk] at hinv; exact _hInvInvSet2 k hinv

end DirectoryMSI
