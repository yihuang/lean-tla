import Leslie.Examples.CacheCoherence.DirectoryMSI.FrameLemmas

namespace DirectoryMSI

/-! ## Tier 2 Step Proofs

    Directory-side actions that do NOT modify cache or c2dChan:
    SendInv, RecvGetS_Exclusive, RecvGetM_Exclusive, RecvGetM_Uncached,
    SendGntE_AfterShared, SendGntE_AfterExclusive.
-/

-- ── SendInv ─────────────────────────────────────────────────────────────
-- Modifies: d2cChan[j] (→{inv,0}), invSet[j] (→false)
-- Guards: invSet[j]=true, d2cChan[j].cmd=empty

theorem fullStrongInvariant_preserved_SendInv
    {n : Nat} {s s' : MState n}
    (h : fullStrongInvariant n s)
    (hact : ∃ j, SendInv s s' j) :
    fullStrongInvariant n s' := by
  obtain ⟨j, hinvJ, hd2cEmpty, hs'⟩ := hact; subst hs'
  obtain ⟨⟨⟨hctrl, hdataF, hdataS⟩, hexclCons, hmImpl, hsShr, hexclExcl, huncInv,
    hgntSD, hgntED, hinvSub⟩,
    hackD, hcurNot, hexclNoDup, hshrNoE, hgntEImpl, hfetchImpl, hinvImpl, hackInv,
    hackInvSet, hinvSetCmd, hackCmdNotEmpty, hgetSAck,
    hInvAckExcl, hInvSetDirSh, hInvMsgShr, hAckShShr, hInvExclEx, hAckExclEx,
    hAckDirNotUnc, hInvDirNotUnc, hAckD2cEmpty, hGntSProp, hGntSDirSh, hInvInvSet⟩ := h
  have hcurCmdGetM : s.curCmd = .getM := hinvSetCmd j hinvJ
  simp only [fullStrongInvariant, strongInvariant, invariant, ctrlProp, dataProp,
    exclusiveConsistent, mImpliesExclusive, sImpliesShrSet, exclusiveExcludesShared,
    uncachedMeansAllInvalid, gntSDataProp, gntEDataProp, invSetSubsetShrSet,
    curNodeNotInInvSet, exclusiveNoDuplicateGrant, sharedNoGntE, gntEImpliesExclusive,
    fetchImpliesCurCmdGetS, invImpliesCurCmd, ackDataProp, ackImpliesInvalid,
    ackImpliesInvSetFalse, invSetImpliesCurCmdGetM, ackImpliesCurCmdNotEmpty, getSAckProp,
    invAckExclusive, invSetImpliesDirShared, invMsgImpliesShrSet,
    ackSharedImpliesShrSet, invExclOnlyAtExNode, ackExclOnlyAtExNode,
    ackImpliesDirNotUncached, invImpliesDirNotUncached,
    ackImpliesD2cEmpty, gntSProp, gntSImpliesDirShared,
    sendInvState_cache, sendInvState_c2dChan, sendInvState_dirSt,
    sendInvState_shrSet, sendInvState_exNode, sendInvState_curCmd,
    sendInvState_curNode, sendInvState_memData, sendInvState_auxData]
  refine ⟨⟨⟨hctrl, hdataF, hdataS⟩,
    fun hexcl => ?_, -- exclusiveConsistent
    hmImpl, fun k hk => ?_, fun hex k hkS => ?_, huncInv, -- sImpliesShrSet, exclusiveExcludesShared
    fun k hgntS => ?_, -- gntSDataProp
    fun k hgntE => ?_, -- gntEDataProp
    fun k hk => ?_⟩,  -- invSetSubsetShrSet
    hackD, -- ackDataProp: c2dChan,cache,dirSt,auxData unchanged
    fun hgetM hdirSh => ?_, -- curNodeNotInInvSet
    fun hexcl k hne => ?_, -- exclusiveNoDuplicateGrant
    fun hsh k => ?_, -- sharedNoGntE
    fun k hgntE => ?_, -- gntEImpliesExclusive
    fun k hfetch => ?_, -- fetchImpliesCurCmdGetS
    fun k hk => ?_, -- invImpliesCurCmd
    hackInv, -- ackImpliesInvalid: c2dChan,cache unchanged
    fun k hack => ?_, -- ackImpliesInvSetFalse
    fun k hk => ?_, -- invSetImpliesCurCmdGetM
    hackCmdNotEmpty, -- ackImpliesCurCmdNotEmpty: c2dChan,curCmd unchanged
    hgetSAck, -- getSAckProp: curCmd=getM≠getS so vacuous
    fun k hinv => ?_, -- invAckExclusive
    fun k hk => ?_, -- invSetImpliesDirShared
    fun k hinv hsh => ?_, -- invMsgImpliesShrSet
    hAckShShr, -- ackSharedImpliesShrSet: c2dChan,dirSt,shrSet unchanged
    fun k hinv hexcl => ?_, -- invExclOnlyAtExNode
    hAckExclEx, -- ackExclOnlyAtExNode: c2dChan,dirSt,exNode unchanged
    hAckDirNotUnc, -- ackImpliesDirNotUncached: c2dChan,dirSt unchanged
    fun k hinv => ?_, -- invImpliesDirNotUncached: d2cChan[j] changes
    fun k hack => ?_, -- ackImpliesD2cEmpty: d2cChan[j] changes
    fun k hgntS => ?_, -- gntSProp: d2cChan[j] changes
    fun k hgntS => ?_, -- gntSImpliesDirShared: d2cChan[j] changes
    ?_⟩ -- invImpliesInvSetFalse
  · -- exclusiveConsistent
    obtain ⟨hMorGntE, hallI⟩ := hexclCons hexcl
    constructor
    · by_cases hjex : j = s.exNode
      · subst hjex
        -- d2cChan[exNode] was empty (guard), post = inv.
        -- Pre: M ∨ gntE ∨ ack. gntE was empty. So M or ack.
        rcases hMorGntE with hM | hgntE | hack
        · exact Or.inl hM
        · rw [hd2cEmpty] at hgntE; exact absurd hgntE (by decide)
        · exact Or.inr (Or.inr hack)
      · rw [sendInvState_d2cChan_ne s j s.exNode (Ne.symm hjex)]
        rcases hMorGntE with hM | hgntE | hack
        · exact Or.inl hM
        · exact Or.inr (Or.inl hgntE)
        · exact Or.inr (Or.inr hack)
    · exact hallI
  · -- sImpliesShrSet: d2cChan[j]→inv, cache/shrSet/curCmd/curNode unchanged
    rcases hsShr k hk with hshr | hgetM | hgntE
    · exact Or.inl hshr
    · exact Or.inr (Or.inl hgetM)
    · -- gntE pre at k: k=j contradicts d2cChan[j]=empty; k≠j gives post gntE
      by_cases hkj : k = j
      · subst hkj; rw [hd2cEmpty] at hgntE; exact absurd hgntE (by decide)
      · exact Or.inr (Or.inr (by rw [sendInvState_d2cChan_ne s j k hkj]; exact hgntE))
  · -- exclusiveExcludesShared: S → gntE. d2cChan[j] changed but k=j contradicts guard.
    by_cases hkj : k = j
    · subst hkj; have := hexclExcl hex k hkS; rw [hd2cEmpty] at this; exact absurd this (by decide)
    · rw [sendInvState_d2cChan_ne s j k hkj]; exact hexclExcl hex k hkS
  · -- gntSDataProp
    by_cases hkj : k = j
    · subst hkj; simp only [sendInvState_d2cChan_self] at hgntS; exact absurd hgntS (by decide)
    · rw [sendInvState_d2cChan_ne s j k hkj] at hgntS ⊢; exact hgntSD k hgntS
  · -- gntEDataProp
    by_cases hkj : k = j
    · subst hkj; simp only [sendInvState_d2cChan_self] at hgntE; exact absurd hgntE (by decide)
    · rw [sendInvState_d2cChan_ne s j k hkj] at hgntE ⊢; exact hgntED k hgntE
  · -- invSetSubsetShrSet
    by_cases hkj : k = j
    · subst hkj; simp only [sendInvState_invSet_self] at hk; exact absurd hk (by decide)
    · rw [sendInvState_invSet_ne s j k hkj] at hk; exact hinvSub k hk
  · -- curNodeNotInInvSet
    by_cases hcj : s.curNode = j
    · subst hcj; simp [sendInvState_invSet_self]
    · rw [sendInvState_invSet_ne s j s.curNode hcj]; exact hcurNot hgetM hdirSh
  · -- exclusiveNoDuplicateGrant
    by_cases hkj : k = j
    · subst hkj; simp only [sendInvState_d2cChan_self]; decide
    · rw [sendInvState_d2cChan_ne s j k hkj]; exact hexclNoDup hexcl k hne
  · -- sharedNoGntE
    by_cases hkj : k = j
    · subst hkj; simp only [sendInvState_d2cChan_self]; decide
    · rw [sendInvState_d2cChan_ne s j k hkj]; exact hshrNoE hsh k
  · -- gntEImpliesExclusive
    by_cases hkj : k = j
    · subst hkj; simp only [sendInvState_d2cChan_self] at hgntE; exact absurd hgntE (by decide)
    · rw [sendInvState_d2cChan_ne s j k hkj] at hgntE; exact hgntEImpl k hgntE
  · -- fetchImpliesCurCmdGetS
    by_cases hkj : k = j
    · subst hkj; simp only [sendInvState_d2cChan_self] at hfetch; exact absurd hfetch (by decide)
    · rw [sendInvState_d2cChan_ne s j k hkj] at hfetch; exact hfetchImpl k hfetch
  · -- invImpliesCurCmd
    by_cases hkj : k = j
    · subst hkj; exact hcurCmdGetM
    · rw [sendInvState_d2cChan_ne s j k hkj] at hk; exact hinvImpl k hk
  · -- ackImpliesInvSetFalse
    by_cases hkj : k = j
    · subst hkj; simp [sendInvState_invSet_self]
    · rw [sendInvState_invSet_ne s j k hkj]; exact hackInvSet k hack
  · -- invSetImpliesCurCmdGetM
    by_cases hkj : k = j
    · subst hkj; simp only [sendInvState_invSet_self] at hk; exact absurd hk (by decide)
    · rw [sendInvState_invSet_ne s j k hkj] at hk; exact hinvSetCmd k hk
  · -- invAckExclusive
    by_cases hkj : k = j
    · -- POST d2cChan[j]=inv. Need c2dChan[j]≠ack. c2dChan unchanged.
      -- From hackInvSet: ack → invSet=false. But invSet[j]=true (guard). So ≠ack.
      subst hkj; intro hack; exact absurd (hackInvSet k hack) (by rw [hinvJ]; decide)
    · rw [sendInvState_d2cChan_ne s j k hkj] at hinv; exact hInvAckExcl k hinv
  · -- invSetImpliesDirShared
    by_cases hkj : k = j
    · subst hkj; simp only [sendInvState_invSet_self] at hk; exact absurd hk (by decide)
    · rw [sendInvState_invSet_ne s j k hkj] at hk; exact hInvSetDirSh k hk
  · -- invMsgImpliesShrSet
    by_cases hkj : k = j
    · -- d2cChan'[j]=inv, dirSt=Shared → shrSet[j]=true
      -- Pre: invSet[j]=true → shrSet[j]=true (invSetSubsetShrSet)
      subst hkj; exact hinvSub k hinvJ
    · rw [sendInvState_d2cChan_ne s j k hkj] at hinv; exact hInvMsgShr k hinv hsh
  · -- invExclOnlyAtExNode
    by_cases hkj : k = j
    · -- d2cChan'[j]=inv, dirSt=Exclusive → j=exNode
      subst hkj
      -- Pre: invSetImpliesDirShared: invSet[j]=true → dirSt=Shared
      have := hInvSetDirSh k hinvJ
      rw [this] at hexcl; exact absurd hexcl (by decide)
    · rw [sendInvState_d2cChan_ne s j k hkj] at hinv; exact hInvExclEx k hinv hexcl
  · -- invImpliesDirNotUncached: d2cChan[j]→inv, dirSt unchanged
    by_cases hkj : k = j
    · intro hunc; rw [hInvSetDirSh k (hkj ▸ hinvJ)] at hunc; exact absurd hunc (by decide)
    · rw [sendInvState_d2cChan_ne s j k hkj] at hinv; exact hInvDirNotUnc k hinv
  · -- ackImpliesD2cEmpty: c2dChan unchanged, d2cChan[j] changes
    by_cases hkj : k = j
    · subst hkj; exact absurd hack (by intro h; exact absurd (hackInvSet k h) (by rw [hinvJ]; decide))
    · rw [sendInvState_d2cChan_ne s j k hkj]; exact hAckD2cEmpty k hack
  · -- gntSProp: d2cChan[j] changes, shrSet/curCmd/curNode unchanged
    by_cases hkj : k = j
    · subst hkj; simp only [sendInvState_d2cChan_self] at hgntS; exact absurd hgntS (by decide)
    · rw [sendInvState_d2cChan_ne s j k hkj] at hgntS; exact hGntSProp k hgntS
  · -- gntSImpliesDirShared: d2cChan[j]→inv (not gntS), dirSt unchanged
    by_cases hkj : k = j
    · subst hkj; simp only [sendInvState_d2cChan_self] at hgntS; exact absurd hgntS (by decide)
    · rw [sendInvState_d2cChan_ne s j k hkj] at hgntS; exact hGntSDirSh k hgntS
  · -- invImpliesInvSetFalse: d2cChan[j]→inv, invSet[j]→false
    unfold invImpliesInvSetFalse; intro k hinv
    by_cases hkj : k = j
    · subst hkj; simp [sendInvState_invSet_self]
    · rw [sendInvState_d2cChan_ne s j k hkj] at hinv
      rw [sendInvState_invSet_ne s j k hkj]; exact hInvInvSet k hinv

-- ── RecvGetS_Exclusive ──────────────────────────────────────────────────
-- Modifies: d2cChan[exNode] (→{fetch,0}), curCmd (→getS), curNode (→i), reqChan[i]
-- Guards: reqChan[i]=getS, curCmd=empty, dirSt=Exclusive, d2cChan[exNode]=empty

theorem fullStrongInvariant_preserved_RecvGetS_Exclusive
    {n : Nat} {s s' : MState n}
    (h : fullStrongInvariant n s)
    (hact : ∃ i, RecvGetS_Exclusive s s' i) :
    fullStrongInvariant n s' := by
  obtain ⟨i, _hreq, hcurCmd, hdirSt, hd2cExEmpty, hs'⟩ := hact; subst hs'
  obtain ⟨⟨⟨hctrl, hdataF, hdataS⟩, hexclCons, hmImpl, hsShr, hexclExcl, huncInv,
    hgntSD, hgntED, hinvSub⟩,
    hackD, _hcurNot, hexclNoDup, _hshrNoE, hgntEImpl, hfetchImpl, hinvImpl, hackInv,
    hackInvSet, hinvSetCmd, hackCmdNotEmpty, _hgetSAck,
    hInvAckExcl, hInvSetDirSh, hInvMsgShr, hAckShShr, hInvExclEx, hAckExclEx,
    hAckDirNotUnc, hInvDirNotUnc, hAckD2cEmpty, hGntSProp, hGntSDirSh, _hInvInvSet⟩ := h
  -- Key: curCmd=empty → no acks, no invSet entries, no inv/fetch messages
  have hNoInvSet : ∀ k, s.invSet k = false := by
    intro k; by_contra h; rw [Bool.not_eq_false] at h; exact absurd (hinvSetCmd k h) (by rw [hcurCmd]; decide)
  have hNoAck : ∀ k, (s.c2dChan k).cmd ≠ .ack := by
    intro k h; exact absurd (hackCmdNotEmpty k h) (by rw [hcurCmd]; decide)
  have hNoFetch : ∀ k, (s.d2cChan k).cmd ≠ .fetch := by
    intro k h; exact absurd (hfetchImpl k h).1 (by rw [hcurCmd]; decide)
  have hNoInv : ∀ k, (s.d2cChan k).cmd ≠ .inv := by
    intro k h; exact absurd (hinvImpl k h) (by rw [hcurCmd]; decide)
  simp only [fullStrongInvariant, strongInvariant, invariant, ctrlProp, dataProp,
    exclusiveConsistent, mImpliesExclusive, sImpliesShrSet, exclusiveExcludesShared,
    uncachedMeansAllInvalid, gntSDataProp, gntEDataProp, invSetSubsetShrSet,
    curNodeNotInInvSet, exclusiveNoDuplicateGrant, sharedNoGntE, gntEImpliesExclusive,
    fetchImpliesCurCmdGetS, invImpliesCurCmd, ackDataProp, ackImpliesInvalid,
    ackImpliesInvSetFalse, invSetImpliesCurCmdGetM, ackImpliesCurCmdNotEmpty, getSAckProp,
    invAckExclusive, invSetImpliesDirShared, invMsgImpliesShrSet,
    ackSharedImpliesShrSet, invExclOnlyAtExNode, ackExclOnlyAtExNode,
    ackImpliesDirNotUncached, invImpliesDirNotUncached,
    ackImpliesD2cEmpty, gntSProp, gntSImpliesDirShared,
    recvGetS_ExclusiveState_cache, recvGetS_ExclusiveState_c2dChan,
    recvGetS_ExclusiveState_dirSt, recvGetS_ExclusiveState_shrSet,
    recvGetS_ExclusiveState_exNode, recvGetS_ExclusiveState_curCmd,
    recvGetS_ExclusiveState_curNode, recvGetS_ExclusiveState_invSet,
    recvGetS_ExclusiveState_memData, recvGetS_ExclusiveState_auxData]
  refine ⟨⟨⟨hctrl, hdataF, hdataS⟩,
    fun hexcl => ?_, -- exclusiveConsistent
    hmImpl, -- mImpliesExclusive: cache,dirSt,exNode unchanged
    fun k hk => ?_, -- sImpliesShrSet (curCmd→getS, curNode→i)
    fun hex k hkS => ?_, -- exclusiveExcludesShared: d2cChan[exNode] changes
    huncInv, -- uncachedMeansAllInvalid: cache,dirSt unchanged
    fun k hgntS => ?_, -- gntSDataProp
    fun k hgntE => ?_, -- gntEDataProp
    hinvSub⟩, -- invSetSubsetShrSet: invSet,shrSet unchanged
    hackD, -- ackDataProp: c2dChan,cache,dirSt,auxData unchanged
    fun hgetM => absurd hgetM (by decide), -- curNodeNotInInvSet: getS≠getM
    fun hexcl k hne => ?_, -- exclusiveNoDuplicateGrant
    fun hsh => absurd hsh (by rw [hdirSt]; decide), -- sharedNoGntE: Exclusive≠Shared
    fun k hgntE => ?_, -- gntEImpliesExclusive
    fun k hfetch => ?_, -- fetchImpliesCurCmdGetS
    fun k hk => ?_, -- invImpliesCurCmd
    hackInv, -- ackImpliesInvalid: c2dChan,cache unchanged
    hackInvSet, -- ackImpliesInvSetFalse: c2dChan,invSet unchanged
    fun k hk => absurd (hinvSetCmd k hk) (by rw [hcurCmd]; decide), -- invSetImpliesCurCmdGetM: no invSet entries
    fun k hack => absurd hack (hNoAck k), -- ackImpliesCurCmdNotEmpty: no acks
    fun k hack hgetS => absurd hack (hNoAck k), -- getSAckProp: no acks
    fun k hinv => ?_, -- invAckExclusive
    fun k hk => hInvSetDirSh k hk, -- invSetImpliesDirShared: invSet,dirSt unchanged
    fun k hinv hsh => ?_, -- invMsgImpliesShrSet
    fun k hack hsh => absurd hack (hNoAck k), -- ackSharedImpliesShrSet: no acks
    fun k hinv hexcl => ?_, -- invExclOnlyAtExNode
    fun k hack hexcl => absurd hack (hNoAck k), -- ackExclOnlyAtExNode: no acks
    fun k hack => absurd hack (hNoAck k), -- ackImpliesDirNotUncached: no acks
    fun k hinv hunc => by -- invImpliesDirNotUncached: d2cChan[exNode]→fetch
      by_cases hkex : k = s.exNode
      · simp [hkex, recvGetS_ExclusiveState_d2cChan_exNode] at hinv
      · rw [recvGetS_ExclusiveState_d2cChan_ne s i k hkex] at hinv
        exact absurd hunc (hInvDirNotUnc k hinv),
    fun k hack => absurd hack (hNoAck k), -- ackImpliesD2cEmpty: no acks
    fun k hgntS => by -- gntSProp: d2cChan[exNode]→fetch
      by_cases hkex : k = s.exNode
      · simp [hkex, recvGetS_ExclusiveState_d2cChan_exNode] at hgntS
      · rw [recvGetS_ExclusiveState_d2cChan_ne s i k hkex] at hgntS
        rcases hGntSProp k hgntS with hshr | ⟨hcmd, _⟩
        · exact Or.inl hshr
        · rw [hcurCmd] at hcmd; exact absurd hcmd (by decide),
    fun k hgntS => by -- gntSImpliesDirShared: d2cChan[exNode]→fetch, dirSt unchanged
      by_cases hkex : k = s.exNode
      · simp [hkex, recvGetS_ExclusiveState_d2cChan_exNode] at hgntS
      · rw [recvGetS_ExclusiveState_d2cChan_ne s i k hkex] at hgntS
        exact hGntSDirSh k hgntS,
    by unfold invImpliesInvSetFalse; intro k hinv
       by_cases hkex : k = s.exNode
       · simp [hkex, recvGetS_ExclusiveState_d2cChan_exNode] at hinv
       · rw [recvGetS_ExclusiveState_d2cChan_ne s i k hkex] at hinv
         exact absurd hinv (hNoInv k)⟩
  · -- exclusiveConsistent
    obtain ⟨hMorGntE, hallI⟩ := hexclCons hexcl
    constructor
    · -- d2cChan[exNode]→fetch. Pre: M ∨ gntE ∨ ack.
      -- gntE was empty (guard) so d2cChan[exNode].cmd=empty.
      -- So M or ack (not gntE).
      rcases hMorGntE with hM | hgntE | hack
      · exact Or.inl hM
      · rw [hd2cExEmpty] at hgntE; exact absurd hgntE (by decide)
      · exact Or.inr (Or.inr hack)
    · exact hallI
  · -- sImpliesShrSet: curCmd→getS, curNode→i, d2cChan changes at exNode
    rcases hsShr k hk with hshr | ⟨hcmd, _⟩ | hgntE
    · exact Or.inl hshr
    · rw [hcurCmd] at hcmd; exact absurd hcmd (by decide)
    · -- gntE at k: k=exNode contradicts d2cChan[exNode]=empty; k≠exNode gives post gntE
      by_cases hkex : k = s.exNode
      · subst hkex; rw [hd2cExEmpty] at hgntE; exact absurd hgntE (by decide)
      · exact Or.inr (Or.inr (by rw [recvGetS_ExclusiveState_d2cChan_ne s i k hkex]; exact hgntE))
  · -- exclusiveExcludesShared: S at k → d2cChan'[k]=gntE
    have hpre := hexclExcl hex k hkS -- pre: d2cChan[k]=gntE
    by_cases hkex : k = s.exNode
    · rw [hkex] at hpre; rw [hd2cExEmpty] at hpre; exact absurd hpre (by decide)
    · rw [recvGetS_ExclusiveState_d2cChan_ne s i k hkex]; exact hpre
  · -- gntSDataProp
    by_cases hkex : k = s.exNode
    · subst hkex; simp only [recvGetS_ExclusiveState_d2cChan_exNode] at hgntS; exact absurd hgntS (by decide)
    · rw [recvGetS_ExclusiveState_d2cChan_ne s i k hkex] at hgntS ⊢; exact hgntSD k hgntS
  · -- gntEDataProp
    by_cases hkex : k = s.exNode
    · subst hkex; simp only [recvGetS_ExclusiveState_d2cChan_exNode] at hgntE; exact absurd hgntE (by decide)
    · rw [recvGetS_ExclusiveState_d2cChan_ne s i k hkex] at hgntE ⊢; exact hgntED k hgntE
  · -- exclusiveNoDuplicateGrant
    by_cases hkex : k = s.exNode
    · subst hkex; simp only [recvGetS_ExclusiveState_d2cChan_exNode]; decide
    · rw [recvGetS_ExclusiveState_d2cChan_ne s i k hkex]; exact hexclNoDup hexcl k hne
  · -- gntEImpliesExclusive
    by_cases hkex : k = s.exNode
    · subst hkex; simp only [recvGetS_ExclusiveState_d2cChan_exNode] at hgntE; exact absurd hgntE (by decide)
    · rw [recvGetS_ExclusiveState_d2cChan_ne s i k hkex] at hgntE; exact hgntEImpl k hgntE
  · -- fetchImpliesCurCmdGetS: NEW fetch at exNode
    by_cases hkex : k = s.exNode
    · subst hkex; exact ⟨trivial, hdirSt, rfl⟩
    · rw [recvGetS_ExclusiveState_d2cChan_ne s i k hkex] at hfetch; exact absurd hfetch (hNoFetch k)
  · -- invImpliesCurCmd
    by_cases hkex : k = s.exNode
    · subst hkex; simp only [recvGetS_ExclusiveState_d2cChan_exNode] at hk; exact absurd hk (by decide)
    · rw [recvGetS_ExclusiveState_d2cChan_ne s i k hkex] at hk; exact absurd hk (hNoInv k)
  · -- invAckExclusive
    by_cases hkex : k = s.exNode
    · subst hkex; simp only [recvGetS_ExclusiveState_d2cChan_exNode] at hinv; exact absurd hinv (by decide)
    · rw [recvGetS_ExclusiveState_d2cChan_ne s i k hkex] at hinv; exact absurd hinv (hNoInv k)
  · -- invMsgImpliesShrSet
    by_cases hkex : k = s.exNode
    · subst hkex; simp only [recvGetS_ExclusiveState_d2cChan_exNode] at hinv; exact absurd hinv (by decide)
    · rw [recvGetS_ExclusiveState_d2cChan_ne s i k hkex] at hinv; exact absurd hinv (hNoInv k)
  · -- invExclOnlyAtExNode
    by_cases hkex : k = s.exNode
    · subst hkex; simp only [recvGetS_ExclusiveState_d2cChan_exNode] at hinv; exact absurd hinv (by decide)
    · rw [recvGetS_ExclusiveState_d2cChan_ne s i k hkex] at hinv; exact absurd hinv (hNoInv k)

-- ── RecvGetM_Exclusive ──────────────────────────────────────────────────
-- Modifies: d2cChan[exNode] (→{inv,0}), curCmd (→getM), curNode (→i), reqChan[i]
-- Guards: reqChan[i]=getM, curCmd=empty, dirSt=Exclusive, exNode≠i, d2cChan[exNode]=empty

theorem fullStrongInvariant_preserved_RecvGetM_Exclusive
    {n : Nat} {s s' : MState n}
    (h : fullStrongInvariant n s)
    (hact : ∃ i, RecvGetM_Exclusive s s' i) :
    fullStrongInvariant n s' := by
  obtain ⟨i, _hreq, hcurCmd, hdirSt, hexNe, hd2cExEmpty, hs'⟩ := hact; subst hs'
  obtain ⟨⟨⟨hctrl, hdataF, hdataS⟩, hexclCons, hmImpl, hsShr, hexclExcl, huncInv,
    hgntSD, hgntED, hinvSub⟩,
    hackD, _hcurNot, hexclNoDup, _hshrNoE, hgntEImpl, hfetchImpl, hinvImpl, hackInv,
    hackInvSet, hinvSetCmd, hackCmdNotEmpty, _hgetSAck,
    hInvAckExcl, hInvSetDirSh, hInvMsgShr, hAckShShr, hInvExclEx, hAckExclEx,
    hAckDirNotUnc, hInvDirNotUnc, hAckD2cEmpty, hGntSProp, hGntSDirSh, _hInvInvSet⟩ := h
  -- Key: curCmd=empty → no acks, no invSet entries, no inv/fetch messages
  have hNoInvSet : ∀ k, s.invSet k = false := by
    intro k; by_contra h; rw [Bool.not_eq_false] at h; exact absurd (hinvSetCmd k h) (by rw [hcurCmd]; decide)
  have hNoAck : ∀ k, (s.c2dChan k).cmd ≠ .ack := by
    intro k h; exact absurd (hackCmdNotEmpty k h) (by rw [hcurCmd]; decide)
  have hNoFetch : ∀ k, (s.d2cChan k).cmd ≠ .fetch := by
    intro k h; exact absurd (hfetchImpl k h).1 (by rw [hcurCmd]; decide)
  have hNoInv : ∀ k, (s.d2cChan k).cmd ≠ .inv := by
    intro k h; exact absurd (hinvImpl k h) (by rw [hcurCmd]; decide)
  simp only [fullStrongInvariant, strongInvariant, invariant, ctrlProp, dataProp,
    exclusiveConsistent, mImpliesExclusive, sImpliesShrSet, exclusiveExcludesShared,
    uncachedMeansAllInvalid, gntSDataProp, gntEDataProp, invSetSubsetShrSet,
    curNodeNotInInvSet, exclusiveNoDuplicateGrant, sharedNoGntE, gntEImpliesExclusive,
    fetchImpliesCurCmdGetS, invImpliesCurCmd, ackDataProp, ackImpliesInvalid,
    ackImpliesInvSetFalse, invSetImpliesCurCmdGetM, ackImpliesCurCmdNotEmpty, getSAckProp,
    invAckExclusive, invSetImpliesDirShared, invMsgImpliesShrSet,
    ackSharedImpliesShrSet, invExclOnlyAtExNode, ackExclOnlyAtExNode,
    ackImpliesDirNotUncached, invImpliesDirNotUncached,
    ackImpliesD2cEmpty, gntSProp, gntSImpliesDirShared,
    recvGetM_ExclusiveState_cache, recvGetM_ExclusiveState_c2dChan,
    recvGetM_ExclusiveState_dirSt, recvGetM_ExclusiveState_shrSet,
    recvGetM_ExclusiveState_exNode, recvGetM_ExclusiveState_curCmd,
    recvGetM_ExclusiveState_curNode, recvGetM_ExclusiveState_invSet,
    recvGetM_ExclusiveState_memData, recvGetM_ExclusiveState_auxData]
  refine ⟨⟨⟨hctrl, hdataF, hdataS⟩,
    fun hexcl => ?_, -- exclusiveConsistent
    hmImpl, -- mImpliesExclusive: cache,dirSt,exNode unchanged
    fun k hk => ?_, -- sImpliesShrSet (curCmd→getM, curNode→i)
    fun hex k hkS => ?_, -- exclusiveExcludesShared: d2cChan[exNode] changes
    huncInv, -- uncachedMeansAllInvalid: cache,dirSt unchanged
    fun k hgntS => ?_, -- gntSDataProp
    fun k hgntE => ?_, -- gntEDataProp
    hinvSub⟩, -- invSetSubsetShrSet: invSet,shrSet unchanged
    hackD, -- ackDataProp: c2dChan,cache,dirSt,auxData unchanged
    fun _ hdirSh => absurd hdirSh (by rw [hdirSt]; decide), -- curNodeNotInInvSet: Exclusive≠Shared
    fun hexcl k hne => ?_, -- exclusiveNoDuplicateGrant
    fun hsh => absurd hsh (by rw [hdirSt]; decide), -- sharedNoGntE: Exclusive≠Shared
    fun k hgntE => ?_, -- gntEImpliesExclusive
    fun k hfetch => ?_, -- fetchImpliesCurCmdGetS
    fun k hk => ?_, -- invImpliesCurCmd
    hackInv, -- ackImpliesInvalid: c2dChan,cache unchanged
    hackInvSet, -- ackImpliesInvSetFalse: c2dChan,invSet unchanged
    fun k hk => absurd (hinvSetCmd k hk) (by rw [hcurCmd]; decide), -- invSetImpliesCurCmdGetM
    fun k hack => absurd hack (hNoAck k), -- ackImpliesCurCmdNotEmpty: no acks
    fun k hack _ => absurd hack (hNoAck k), -- getSAckProp: no acks
    fun k hinv => ?_, -- invAckExclusive
    fun k hk => hInvSetDirSh k hk, -- invSetImpliesDirShared: invSet,dirSt unchanged
    fun k hinv hsh => ?_, -- invMsgImpliesShrSet
    fun k hack hsh => absurd hack (hNoAck k), -- ackSharedImpliesShrSet: no acks
    fun k hinv hexcl => ?_, -- invExclOnlyAtExNode
    fun k hack hexcl => absurd hack (hNoAck k), -- ackExclOnlyAtExNode: no acks
    fun k hack => absurd hack (hNoAck k), -- ackImpliesDirNotUncached: no acks
    fun k hinv hunc => by -- invImpliesDirNotUncached: d2cChan[exNode]→inv
      by_cases hkex : k = s.exNode
      · rw [hdirSt] at hunc; exact absurd hunc (by decide)
      · rw [recvGetM_ExclusiveState_d2cChan_ne s i k hkex] at hinv
        exact absurd hunc (hInvDirNotUnc k hinv),
    fun k hack => absurd hack (hNoAck k), -- ackImpliesD2cEmpty: no acks
    fun k hgntS => by -- gntSProp: d2cChan[exNode]→inv
      by_cases hkex : k = s.exNode
      · simp [hkex, recvGetM_ExclusiveState_d2cChan_exNode] at hgntS
      · rw [recvGetM_ExclusiveState_d2cChan_ne s i k hkex] at hgntS
        rcases hGntSProp k hgntS with hshr | ⟨hcmd, _⟩
        · exact Or.inl hshr
        · rw [hcurCmd] at hcmd; exact absurd hcmd (by decide),
    fun k hgntS => by -- gntSImpliesDirShared: d2cChan[exNode]→inv, dirSt unchanged
      by_cases hkex : k = s.exNode
      · simp [hkex, recvGetM_ExclusiveState_d2cChan_exNode] at hgntS
      · rw [recvGetM_ExclusiveState_d2cChan_ne s i k hkex] at hgntS
        exact hGntSDirSh k hgntS,
    by unfold invImpliesInvSetFalse; intro k hinv
       by_cases hkex : k = s.exNode
       · subst hkex; exact hNoInvSet s.exNode
       · rw [recvGetM_ExclusiveState_d2cChan_ne s i k hkex] at hinv
         exact absurd hinv (hNoInv k)⟩
  · -- exclusiveConsistent
    obtain ⟨hMorGntE, hallI⟩ := hexclCons hexcl
    constructor
    · rcases hMorGntE with hM | hgntE | hack
      · exact Or.inl hM
      · rw [hd2cExEmpty] at hgntE; exact absurd hgntE (by decide)
      · exact Or.inr (Or.inr hack)
    · exact hallI
  · -- sImpliesShrSet: curCmd→getM, curNode→i
    rcases hsShr k hk with hshr | ⟨hcmd, _⟩ | hgntE
    · exact Or.inl hshr
    · rw [hcurCmd] at hcmd; exact absurd hcmd (by decide)
    · by_cases hkex : k = s.exNode
      · subst hkex; rw [hd2cExEmpty] at hgntE; exact absurd hgntE (by decide)
      · exact Or.inr (Or.inr (by rw [recvGetM_ExclusiveState_d2cChan_ne s i k hkex]; exact hgntE))
  · -- exclusiveExcludesShared: S at k → d2cChan'[k]=gntE
    have hpre := hexclExcl hex k hkS
    by_cases hkex : k = s.exNode
    · rw [hkex] at hpre; rw [hd2cExEmpty] at hpre; exact absurd hpre (by decide)
    · rw [recvGetM_ExclusiveState_d2cChan_ne s i k hkex]; exact hpre
  · -- gntSDataProp
    by_cases hkex : k = s.exNode
    · subst hkex; simp only [recvGetM_ExclusiveState_d2cChan_exNode] at hgntS; exact absurd hgntS (by decide)
    · rw [recvGetM_ExclusiveState_d2cChan_ne s i k hkex] at hgntS ⊢; exact hgntSD k hgntS
  · -- gntEDataProp
    by_cases hkex : k = s.exNode
    · subst hkex; simp only [recvGetM_ExclusiveState_d2cChan_exNode] at hgntE; exact absurd hgntE (by decide)
    · rw [recvGetM_ExclusiveState_d2cChan_ne s i k hkex] at hgntE ⊢; exact hgntED k hgntE
  · -- exclusiveNoDuplicateGrant
    by_cases hkex : k = s.exNode
    · subst hkex; simp only [recvGetM_ExclusiveState_d2cChan_exNode]; decide
    · rw [recvGetM_ExclusiveState_d2cChan_ne s i k hkex]; exact hexclNoDup hexcl k hne
  · -- gntEImpliesExclusive
    by_cases hkex : k = s.exNode
    · subst hkex; simp only [recvGetM_ExclusiveState_d2cChan_exNode] at hgntE; exact absurd hgntE (by decide)
    · rw [recvGetM_ExclusiveState_d2cChan_ne s i k hkex] at hgntE; exact hgntEImpl k hgntE
  · -- fetchImpliesCurCmdGetS
    by_cases hkex : k = s.exNode
    · subst hkex; simp only [recvGetM_ExclusiveState_d2cChan_exNode] at hfetch; exact absurd hfetch (by decide)
    · rw [recvGetM_ExclusiveState_d2cChan_ne s i k hkex] at hfetch; exact absurd hfetch (hNoFetch k)
  · -- invImpliesCurCmd: k=exNode: inv, curCmd'=getM ✓. k≠exNode: pre no invs.
    by_cases hkex : k = s.exNode
    · subst hkex; trivial
    · rw [recvGetM_ExclusiveState_d2cChan_ne s i k hkex] at hk; exact absurd hk (hNoInv k)
  · -- invAckExclusive
    by_cases hkex : k = s.exNode
    · -- d2cChan'[exNode]=inv. Need c2dChan[exNode]≠ack. From hNoAck.
      subst hkex; exact hNoAck s.exNode
    · rw [recvGetM_ExclusiveState_d2cChan_ne s i k hkex] at hinv; exact absurd hinv (hNoInv k)
  · -- invMsgImpliesShrSet
    by_cases hkex : k = s.exNode
    · subst hkex; rw [hdirSt] at hsh; exact absurd hsh (by decide)
    · rw [recvGetM_ExclusiveState_d2cChan_ne s i k hkex] at hinv; exact absurd hinv (hNoInv k)
  · -- invExclOnlyAtExNode: k=exNode: inv at exNode → exNode=exNode ✓
    by_cases hkex : k = s.exNode
    · exact hkex
    · rw [recvGetM_ExclusiveState_d2cChan_ne s i k hkex] at hinv; exact absurd hinv (hNoInv k)

-- ── RecvGetM_Uncached ───────────────────────────────────────────────────
-- Modifies: d2cChan[i] (→{gntE, memData}), exNode (→i), dirSt (→Exclusive),
--           reqChan[i], auxData (→memData)
-- Guards: reqChan[i]=getM, curCmd=empty, dirSt=Uncached, d2cChan[i]=empty

theorem fullStrongInvariant_preserved_RecvGetM_Uncached
    {n : Nat} {s s' : MState n}
    (h : fullStrongInvariant n s)
    (hact : ∃ i, RecvGetM_Uncached s s' i) :
    fullStrongInvariant n s' := by
  obtain ⟨i, _hreq, hcurCmd, hdirSt, hd2cEmpty, hs'⟩ := hact; subst hs'
  obtain ⟨⟨⟨hctrl, hdataF, hdataS⟩, _hexclCons, hmImpl, hsShr, _hexclExcl, huncInv,
    hgntSD, hgntED, hinvSub⟩,
    hackD, _hcurNot, _hexclNoDup, hshrNoE, hgntEImpl, hfetchImpl, hinvImpl, hackInv,
    hackInvSet, hinvSetCmd, hackCmdNotEmpty, _hgetSAck,
    hInvAckExcl, _hInvSetDirSh, _hInvMsgShr, _hAckShShr, _hInvExclEx, _hAckExclEx,
    _hAckDirNotUnc, _hInvDirNotUnc, _hAckD2cEmpty, _hGntSProp, _hGntSDirSh, _hInvInvSet⟩ := h
  -- Key: dirSt=Uncached → all cache=I, memData=auxData. curCmd=empty → no acks, etc.
  have hAllI : ∀ k, (s.cache k).state = .I := huncInv hdirSt
  have hMemAux : s.memData = s.auxData := hdataF (by rw [hdirSt]; decide)
  have hNoInvSet : ∀ k, s.invSet k = false := by
    intro k; by_contra h; rw [Bool.not_eq_false] at h; exact absurd (hinvSetCmd k h) (by rw [hcurCmd]; decide)
  have hNoAck : ∀ k, (s.c2dChan k).cmd ≠ .ack := by
    intro k h; exact absurd (hackCmdNotEmpty k h) (by rw [hcurCmd]; decide)
  have hNoGntE : ∀ k, (s.d2cChan k).cmd ≠ .gntE := by
    intro k h; have := (hgntEImpl k h).1; rw [hdirSt] at this; exact absurd this (by decide)
  have hNoFetch : ∀ k, (s.d2cChan k).cmd ≠ .fetch := by
    intro k h; exact absurd (hfetchImpl k h).1 (by rw [hcurCmd]; decide)
  have hNoInv : ∀ k, (s.d2cChan k).cmd ≠ .inv := by
    intro k h; exact absurd (hinvImpl k h) (by rw [hcurCmd]; decide)
  simp only [fullStrongInvariant, strongInvariant, invariant, ctrlProp, dataProp,
    exclusiveConsistent, mImpliesExclusive, sImpliesShrSet, exclusiveExcludesShared,
    uncachedMeansAllInvalid, gntSDataProp, gntEDataProp, invSetSubsetShrSet,
    curNodeNotInInvSet, exclusiveNoDuplicateGrant, sharedNoGntE, gntEImpliesExclusive,
    fetchImpliesCurCmdGetS, invImpliesCurCmd, ackDataProp, ackImpliesInvalid,
    ackImpliesInvSetFalse, invSetImpliesCurCmdGetM, ackImpliesCurCmdNotEmpty, getSAckProp,
    invAckExclusive, invSetImpliesDirShared, invMsgImpliesShrSet,
    ackSharedImpliesShrSet, invExclOnlyAtExNode, ackExclOnlyAtExNode,
    ackImpliesDirNotUncached, invImpliesDirNotUncached,
    ackImpliesD2cEmpty, gntSProp, gntSImpliesDirShared,
    recvGetM_UncachedState_cache, recvGetM_UncachedState_c2dChan,
    recvGetM_UncachedState_curCmd, recvGetM_UncachedState_curNode,
    recvGetM_UncachedState_shrSet, recvGetM_UncachedState_invSet,
    recvGetM_UncachedState_memData, recvGetM_UncachedState_dirSt,
    recvGetM_UncachedState_exNode, recvGetM_UncachedState_auxData]
  refine ⟨⟨⟨hctrl,
    fun h => absurd rfl h, -- dataProp fst: Exclusive≠Exclusive is False
    fun k hk => absurd (hAllI k) hk⟩, -- dataProp snd: all cache=I, so antecedent false
    fun _ => ?_, -- exclusiveConsistent (dirSt'=Exclusive, always fires)
    fun k hk => ?_, -- mImpliesExclusive
    fun k hk => ?_, -- sImpliesShrSet
    fun _ k hkS => ?_, -- exclusiveExcludesShared (dirSt'=Exclusive)
    fun hunc => absurd hunc (by decide), -- uncachedMeansAllInvalid: Exclusive≠Uncached
    fun k hgntS => ?_, -- gntSDataProp
    fun k hgntE => ?_, -- gntEDataProp
    hinvSub⟩, -- invSetSubsetShrSet: invSet,shrSet unchanged
    fun k hack hcond => absurd hack (hNoAck k), -- ackDataProp: no acks
    fun hgetM => absurd hgetM (by rw [hcurCmd]; decide), -- curNodeNotInInvSet: curCmd=empty≠getM
    fun _ k hne => ?_, -- exclusiveNoDuplicateGrant (dirSt'=Exclusive, exNode'=i)
    fun hsh => absurd hsh (by decide), -- sharedNoGntE: Exclusive≠Shared
    fun k hgntE => ?_, -- gntEImpliesExclusive (dirSt'=Exclusive, exNode'=i)
    fun k hfetch => ?_, -- fetchImpliesCurCmdGetS
    fun k hk => ?_, -- invImpliesCurCmd
    hackInv, -- ackImpliesInvalid: c2dChan,cache unchanged
    hackInvSet, -- ackImpliesInvSetFalse: c2dChan,invSet unchanged
    fun k hk => absurd (hinvSetCmd k hk) (by rw [hcurCmd]; decide), -- invSetImpliesCurCmdGetM
    fun k hack => absurd hack (hNoAck k), -- ackImpliesCurCmdNotEmpty
    fun k hack _ => absurd hack (hNoAck k), -- getSAckProp
    fun k hinv => ?_, -- invAckExclusive
    fun k hk => ?_, -- invSetImpliesDirShared (dirSt'=Exclusive)
    fun k hinv _ => ?_, -- invMsgImpliesShrSet
    fun k hack _ => absurd hack (hNoAck k), -- ackSharedImpliesShrSet
    fun k hinv _ => ?_, -- invExclOnlyAtExNode
    fun k hack _ => absurd hack (hNoAck k), -- ackExclOnlyAtExNode
    fun k hack => absurd hack (hNoAck k), -- ackImpliesDirNotUncached
    fun k hinv => ?_, -- invImpliesDirNotUncached
    fun k hack => absurd hack (hNoAck k), -- ackImpliesD2cEmpty: no acks
    fun k hgntS => ?_, -- gntSProp: d2cChan[i] changes
    fun k hgntS => ?_, -- gntSImpliesDirShared: dirSt'=Exclusive
    ?_⟩ -- invImpliesInvSetFalse
  · -- exclusiveConsistent: dirSt'=Exclusive, exNode'=i
    constructor
    · -- d2cChan'[i]=gntE → second disjunct
      exact Or.inr (Or.inl (by simp [recvGetM_UncachedState_d2cChan_self]))
    · -- ∀k≠i, cache[k]=I: all cache=I
      intro k _; exact hAllI k
  · -- mImpliesExclusive: all cache=I, so M is impossible
    rw [hAllI k] at hk; exact absurd hk (by decide)
  · -- sImpliesShrSet: all cache=I, so S is impossible
    rw [hAllI k] at hk; exact absurd hk (by decide)
  · -- exclusiveExcludesShared: all cache=I, so S is impossible
    exact absurd (hAllI k) (by rw [hkS]; decide)
  · -- gntSDataProp: auxData'=memData
    by_cases hki : k = i
    · subst hki; simp only [recvGetM_UncachedState_d2cChan_self] at hgntS; exact absurd hgntS (by decide)
    · rw [recvGetM_UncachedState_d2cChan_ne s i k hki] at hgntS ⊢
      rw [hMemAux]; exact hgntSD k hgntS
  · -- gntEDataProp: k=i: gntE, data=memData, auxData'=memData ✓. k≠i: pre no gntE.
    by_cases hki : k = i
    · subst hki; simp only [recvGetM_UncachedState_d2cChan_self] at hgntE ⊢
    · rw [recvGetM_UncachedState_d2cChan_ne s i k hki] at hgntE; exact absurd hgntE (hNoGntE k)
  · -- exclusiveNoDuplicateGrant: exNode'=i, ∀k≠i: pre no gntE
    by_cases hki : k = i
    · exact absurd hki hne
    · rw [recvGetM_UncachedState_d2cChan_ne s i k hki]; exact hNoGntE k
  · -- gntEImpliesExclusive: dirSt'=Exclusive, exNode'=i
    by_cases hki : k = i
    · subst hki; exact ⟨trivial, rfl⟩
    · rw [recvGetM_UncachedState_d2cChan_ne s i k hki] at hgntE; exact absurd hgntE (hNoGntE k)
  · -- fetchImpliesCurCmdGetS
    by_cases hki : k = i
    · subst hki; simp only [recvGetM_UncachedState_d2cChan_self] at hfetch; exact absurd hfetch (by decide)
    · rw [recvGetM_UncachedState_d2cChan_ne s i k hki] at hfetch; exact absurd hfetch (hNoFetch k)
  · -- invImpliesCurCmd
    by_cases hki : k = i
    · subst hki; simp only [recvGetM_UncachedState_d2cChan_self] at hk; exact absurd hk (by decide)
    · rw [recvGetM_UncachedState_d2cChan_ne s i k hki] at hk; exact absurd hk (hNoInv k)
  · -- invAckExclusive
    by_cases hki : k = i
    · subst hki; simp only [recvGetM_UncachedState_d2cChan_self] at hinv; exact absurd hinv (by decide)
    · rw [recvGetM_UncachedState_d2cChan_ne s i k hki] at hinv; exact absurd hinv (hNoInv k)
  · -- invSetImpliesDirShared: dirSt'=Exclusive, invSet unchanged, all false
    exact absurd (hNoInvSet k) (by rw [hk]; decide)
  · -- invMsgImpliesShrSet
    by_cases hki : k = i
    · subst hki; simp only [recvGetM_UncachedState_d2cChan_self] at hinv; exact absurd hinv (by decide)
    · rw [recvGetM_UncachedState_d2cChan_ne s i k hki] at hinv; exact absurd hinv (hNoInv k)
  · -- invExclOnlyAtExNode
    by_cases hki : k = i
    · subst hki; simp only [recvGetM_UncachedState_d2cChan_self] at hinv; exact absurd hinv (by decide)
    · rw [recvGetM_UncachedState_d2cChan_ne s i k hki] at hinv; exact absurd hinv (hNoInv k)
  · -- invImpliesDirNotUncached: dirSt'=Exclusive≠Uncached
    intro hunc; exact absurd hunc (by decide)
  · -- gntSProp: d2cChan[i]→gntE
    by_cases hki : k = i
    · subst hki; simp only [recvGetM_UncachedState_d2cChan_self] at hgntS; exact absurd hgntS (by decide)
    · rw [recvGetM_UncachedState_d2cChan_ne s i k hki] at hgntS
      exact _hGntSProp k hgntS
  · -- gntSImpliesDirShared: d2cChan[i]→gntE (not gntS for k=i), dirSt'=Exclusive
    by_cases hki : k = i
    · subst hki; simp only [recvGetM_UncachedState_d2cChan_self] at hgntS; exact absurd hgntS (by decide)
    · rw [recvGetM_UncachedState_d2cChan_ne s i k hki] at hgntS
      -- Pre: gntS at k → dirSt=Shared (hGntSDirSh not available since underscored).
      -- But dirSt=Uncached (hdirSt). gntSImpliesDirShared pre gives Shared. Uncached≠Shared.
      exact absurd (_hGntSDirSh k hgntS) (by rw [hdirSt]; decide)
  · -- invImpliesInvSetFalse
    unfold invImpliesInvSetFalse; intro k hinv
    by_cases hki : k = i
    · subst hki; simp only [recvGetM_UncachedState_d2cChan_self] at hinv; exact absurd hinv (by decide)
    · rw [recvGetM_UncachedState_d2cChan_ne s i k hki] at hinv; exact absurd hinv (hNoInv k)

-- ── SendGntE_AfterShared ────────────────────────────────────────────────
-- Modifies: d2cChan[curNode] (→{gntE,memData}), dirSt (→Exclusive),
--           exNode (→curNode), curCmd (→empty), auxData (→memData)
-- Guards: curCmd=getM, dirSt=Shared, ∀j shrSet[j]=false, ∀j invSet[j]=false,
--         d2cChan[curNode]=empty

/-- SendGntE_AfterShared preserves fullStrongInvariant.

NOTE: The sImpliesShrSet conjunct has a subtle interaction here.
When curCmd changes from getM to empty, a cache at curNode that was in S
(permitted by the `curCmd=getM ∧ curNode=k` exception) would violate
sImpliesShrSet post-transition. The proof must show that no cache is in S
when all shrSet entries are false and curCmd=getM. -/
theorem fullStrongInvariant_preserved_SendGntE_AfterShared
    {n : Nat} {s s' : MState n}
    (h : fullStrongInvariant n s)
    (hact : SendGntE_AfterShared s s') :
    fullStrongInvariant n s' := by
  obtain ⟨hcurCmd, hdirSt, hShrAll, hInvAll, hd2cEmpty, hs'⟩ := hact; subst hs'
  obtain ⟨⟨⟨hctrl, hdataF, hdataS⟩, hexclCons, hmImpl, hsShr, hexclExcl, huncInv,
    hgntSD, hgntED, hinvSub⟩,
    hackD, hcurNot, hexclNoDup, hshrNoE, hgntEImpl, hfetchImpl, hinvImpl, hackInv,
    hackInvSet, hinvSetCmd, hackCmdNotEmpty, hgetSAck,
    hInvAckExcl, hInvSetDirSh, hInvMsgShr, hAckShShr, hInvExclEx, hAckExclEx,
    hAckDirNotUnc, hInvDirNotUnc, hAckD2cEmpty, hGntSProp, hGntSDirSh, _hInvInvSet⟩ := h
  -- Key derived facts
  have hMemAux : s.memData = s.auxData := hdataF (by rw [hdirSt]; decide)
  have hNoInv : ∀ k, (s.d2cChan k).cmd ≠ .inv := by
    intro k h; have := hInvMsgShr k h hdirSt; rw [hShrAll k] at this; exact absurd this (by decide)
  have hNoAck : ∀ k, (s.c2dChan k).cmd ≠ .ack := by
    intro k h; have := hAckShShr k h hdirSt; rw [hShrAll k] at this; exact absurd this (by decide)
  have hNoGntE : ∀ k, (s.d2cChan k).cmd ≠ .gntE := hshrNoE hdirSt
  have hNoM : ∀ k, (s.cache k).state ≠ .M := by
    intro k h; have := (hmImpl k h).1; rw [hdirSt] at this; exact absurd this (by decide)
  -- S only possible at curNode (via second disjunct); for k≠curNode, cache=I
  have hSOnlyCur : ∀ k, (s.cache k).state = .S → k = s.curNode := by
    intro k hk
    rcases hsShr k hk with hshr | ⟨_, hcn⟩ | hgntE
    · rw [hShrAll k] at hshr; exact absurd hshr (by decide)
    · exact hcn.symm
    · exact absurd hgntE (hNoGntE k)
  have hNoFetch : ∀ k, (s.d2cChan k).cmd ≠ .fetch := by
    intro k h; have := (hfetchImpl k h).1; rw [hcurCmd] at this; exact absurd this (by decide)
  have hNeCurI : ∀ k, k ≠ s.curNode → (s.cache k).state = .I := by
    intro k hne
    by_contra hni
    match hst : (s.cache k).state with
    | .I => exact hni hst
    | .S => exact absurd (hSOnlyCur k hst) hne
    | .M => exact absurd hst (hNoM k)
  simp only [fullStrongInvariant, strongInvariant, invariant, ctrlProp, dataProp,
    exclusiveConsistent, mImpliesExclusive, sImpliesShrSet, exclusiveExcludesShared,
    uncachedMeansAllInvalid, gntSDataProp, gntEDataProp, invSetSubsetShrSet,
    curNodeNotInInvSet, exclusiveNoDuplicateGrant, sharedNoGntE, gntEImpliesExclusive,
    fetchImpliesCurCmdGetS, invImpliesCurCmd, ackDataProp, ackImpliesInvalid,
    ackImpliesInvSetFalse, invSetImpliesCurCmdGetM, ackImpliesCurCmdNotEmpty, getSAckProp,
    invAckExclusive, invSetImpliesDirShared, invMsgImpliesShrSet,
    ackSharedImpliesShrSet, invExclOnlyAtExNode, ackExclOnlyAtExNode,
    ackImpliesDirNotUncached, invImpliesDirNotUncached,
    ackImpliesD2cEmpty, gntSProp, gntSImpliesDirShared,
    sendGntE_AfterSharedState_cache, sendGntE_AfterSharedState_c2dChan,
    sendGntE_AfterSharedState_curNode, sendGntE_AfterSharedState_shrSet,
    sendGntE_AfterSharedState_invSet, sendGntE_AfterSharedState_memData,
    sendGntE_AfterSharedState_dirSt, sendGntE_AfterSharedState_exNode,
    sendGntE_AfterSharedState_curCmd, sendGntE_AfterSharedState_auxData]
  refine ⟨⟨⟨hctrl,
    fun h => absurd rfl h, -- dataProp fst: Exclusive≠Exclusive is False
    fun k hk => by rw [hdataS k hk, hMemAux]⟩, -- dataProp snd: auxData'=memData=auxData
    fun _ => ?_, -- exclusiveConsistent (dirSt'=Exclusive, always fires)
    fun k hk => ?_, -- mImpliesExclusive
    fun k hk => ?_, -- sImpliesShrSet
    fun _ k hkS => ?_, -- exclusiveExcludesShared (dirSt'=Exclusive)
    fun hunc => absurd hunc (by decide), -- uncachedMeansAllInvalid: Exclusive≠Uncached
    fun k hgntS => ?_, -- gntSDataProp
    fun k hgntE => ?_, -- gntEDataProp
    fun k hk => ?_⟩, -- invSetSubsetShrSet
    fun k hack hcond => absurd hack (hNoAck k), -- ackDataProp: no acks
    fun hgetM => absurd hgetM (by decide), -- curNodeNotInInvSet: empty≠getM
    fun _ k hne => ?_, -- exclusiveNoDuplicateGrant (dirSt'=Exclusive, exNode'=curNode)
    fun hsh => absurd hsh (by decide), -- sharedNoGntE: Exclusive≠Shared
    fun k hgntE => ?_, -- gntEImpliesExclusive (dirSt'=Exclusive, exNode'=curNode)
    fun k hfetch => ?_, -- fetchImpliesCurCmdGetS
    fun k hk => ?_, -- invImpliesCurCmd
    hackInv, -- ackImpliesInvalid: c2dChan,cache unchanged
    hackInvSet, -- ackImpliesInvSetFalse: c2dChan,invSet unchanged
    fun k hk => absurd hk (by rw [hInvAll k]; decide), -- invSetImpliesCurCmdGetM: all invSet false
    fun k hack => absurd hack (hNoAck k), -- ackImpliesCurCmdNotEmpty
    fun k hack _ => absurd hack (hNoAck k), -- getSAckProp
    fun k hinv => ?_, -- invAckExclusive
    fun k hk => absurd hk (by rw [hInvAll k]; decide), -- invSetImpliesDirShared: all invSet false
    fun k hinv _ => ?_, -- invMsgImpliesShrSet
    fun k hack _ => absurd hack (hNoAck k), -- ackSharedImpliesShrSet
    fun k hinv _ => ?_, -- invExclOnlyAtExNode
    fun k hack _ => absurd hack (hNoAck k), -- ackExclOnlyAtExNode
    fun k hack => absurd hack (hNoAck k), -- ackImpliesDirNotUncached
    fun k hinv => ?_, -- invImpliesDirNotUncached
    fun k hack => ?_, -- ackImpliesD2cEmpty
    fun k hgntS => ?_, -- gntSProp
    fun k hgntS => ?_, -- gntSImpliesDirShared
    ?_⟩ -- invImpliesInvSetFalse
  · -- exclusiveConsistent: dirSt'=Exclusive, exNode'=curNode
    constructor
    · exact Or.inr (Or.inl (by simp [sendGntE_AfterSharedState_d2cChan_curNode]))
    · intro k hne; exact hNeCurI k hne
  · -- mImpliesExclusive: no M
    exact absurd hk (hNoM k)
  · -- sImpliesShrSet: S only at curNode, d2cChan'[curNode]=gntE → third disjunct
    have hkcur := hSOnlyCur k hk; subst hkcur
    exact Or.inr (Or.inr (by simp [sendGntE_AfterSharedState_d2cChan_curNode]))
  · -- exclusiveExcludesShared: S at k → d2cChan'[k]=gntE
    have hkcur := hSOnlyCur k hkS; subst hkcur
    simp [sendGntE_AfterSharedState_d2cChan_curNode]
  · -- gntSDataProp: auxData'=memData
    by_cases hki : k = s.curNode
    · subst hki; simp only [sendGntE_AfterSharedState_d2cChan_curNode] at hgntS; exact absurd hgntS (by decide)
    · rw [sendGntE_AfterSharedState_d2cChan_ne s k hki] at hgntS ⊢
      rw [hMemAux]; exact hgntSD k hgntS
  · -- gntEDataProp: k=curNode: gntE, data=memData, auxData'=memData ✓. k≠curNode: pre no gntE.
    by_cases hki : k = s.curNode
    · subst hki; simp only [sendGntE_AfterSharedState_d2cChan_curNode] at hgntE ⊢
    · rw [sendGntE_AfterSharedState_d2cChan_ne s k hki] at hgntE; exact absurd hgntE (hNoGntE k)
  · -- invSetSubsetShrSet
    exact hinvSub k (by rwa [hInvAll k] at hk ⊢)
  · -- exclusiveNoDuplicateGrant: exNode'=curNode, ∀k≠curNode: pre no gntE
    by_cases hki : k = s.curNode
    · exact absurd hki hne
    · rw [sendGntE_AfterSharedState_d2cChan_ne s k hki]; exact hNoGntE k
  · -- gntEImpliesExclusive: dirSt'=Exclusive, exNode'=curNode
    by_cases hki : k = s.curNode
    · subst hki; exact ⟨trivial, rfl⟩
    · rw [sendGntE_AfterSharedState_d2cChan_ne s k hki] at hgntE; exact absurd hgntE (hNoGntE k)
  · -- fetchImpliesCurCmdGetS
    by_cases hki : k = s.curNode
    · subst hki; simp only [sendGntE_AfterSharedState_d2cChan_curNode] at hfetch; exact absurd hfetch (by decide)
    · rw [sendGntE_AfterSharedState_d2cChan_ne s k hki] at hfetch; exact absurd hfetch (hNoFetch k)
  · -- invImpliesCurCmd
    by_cases hki : k = s.curNode
    · subst hki; simp only [sendGntE_AfterSharedState_d2cChan_curNode] at hk; exact absurd hk (by decide)
    · rw [sendGntE_AfterSharedState_d2cChan_ne s k hki] at hk; exact absurd hk (hNoInv k)
  · -- invAckExclusive
    by_cases hki : k = s.curNode
    · subst hki; simp only [sendGntE_AfterSharedState_d2cChan_curNode] at hinv; exact absurd hinv (by decide)
    · rw [sendGntE_AfterSharedState_d2cChan_ne s k hki] at hinv; exact absurd hinv (hNoInv k)
  · -- invMsgImpliesShrSet
    by_cases hki : k = s.curNode
    · subst hki; simp only [sendGntE_AfterSharedState_d2cChan_curNode] at hinv; exact absurd hinv (by decide)
    · rw [sendGntE_AfterSharedState_d2cChan_ne s k hki] at hinv; exact absurd hinv (hNoInv k)
  · -- invExclOnlyAtExNode
    by_cases hki : k = s.curNode
    · subst hki; simp only [sendGntE_AfterSharedState_d2cChan_curNode] at hinv; exact absurd hinv (by decide)
    · rw [sendGntE_AfterSharedState_d2cChan_ne s k hki] at hinv; exact absurd hinv (hNoInv k)
  · -- invImpliesDirNotUncached: dirSt'=Exclusive≠Uncached
    intro hunc; exact absurd hunc (by decide)
  · -- ackImpliesD2cEmpty: no acks
    exact absurd hack (hNoAck k)
  · -- gntSProp
    by_cases hki : k = s.curNode
    · subst hki; simp only [sendGntE_AfterSharedState_d2cChan_curNode] at hgntS; exact absurd hgntS (by decide)
    · rw [sendGntE_AfterSharedState_d2cChan_ne s k hki] at hgntS
      rcases hGntSProp k hgntS with hshr | ⟨_, hcn⟩
      · exact Or.inl hshr
      · exact absurd hcn.symm hki
  · -- gntSImpliesDirShared
    by_cases hki : k = s.curNode
    · subst hki; simp only [sendGntE_AfterSharedState_d2cChan_curNode] at hgntS; exact absurd hgntS (by decide)
    · rw [sendGntE_AfterSharedState_d2cChan_ne s k hki] at hgntS
      rcases hGntSProp k hgntS with hshr | ⟨_, hcn⟩
      · exact absurd (hShrAll k) (by rw [hshr]; decide)
      · exact absurd hcn.symm hki
  · -- invImpliesInvSetFalse
    unfold invImpliesInvSetFalse; intro k hinv
    by_cases hki : k = s.curNode
    · subst hki; simp only [sendGntE_AfterSharedState_d2cChan_curNode] at hinv; exact absurd hinv (by decide)
    · rw [sendGntE_AfterSharedState_d2cChan_ne s k hki] at hinv; exact absurd hinv (hNoInv k)

-- ── SendGntE_AfterExclusive ─────────────────────────────────────────────
-- Modifies: d2cChan[curNode] (→{gntE,memData}), dirSt (→Exclusive),
--           exNode (→curNode), curCmd (→empty)
-- Guards: curCmd=getM, dirSt=Uncached, d2cChan[curNode]=empty

/-- SendGntE_AfterExclusive preserves fullStrongInvariant.

NOTE: Same sImpliesShrSet subtlety as SendGntE_AfterShared applies here:
when curCmd transitions from getM to empty, caches in S at curNode
(previously excused by the getM exception) could violate sImpliesShrSet.
The proof must show no such cache exists when dirSt=Uncached. -/
theorem fullStrongInvariant_preserved_SendGntE_AfterExclusive
    {n : Nat} {s s' : MState n}
    (h : fullStrongInvariant n s)
    (hact : SendGntE_AfterExclusive s s') :
    fullStrongInvariant n s' := by
  obtain ⟨hcurCmd, hdirSt, hd2cEmpty, hs'⟩ := hact; subst hs'
  obtain ⟨⟨⟨hctrl, hdataF, hdataS⟩, _hexclCons, hmImpl, hsShr, _hexclExcl, huncInv,
    hgntSD, hgntED, hinvSub⟩,
    hackD, hcurNot, hexclNoDup, hshrNoE, hgntEImpl, hfetchImpl, hinvImpl, hackInv,
    hackInvSet, hinvSetCmd, hackCmdNotEmpty, hgetSAck,
    hInvAckExcl, hInvSetDirSh, hInvMsgShr, hAckShShr, hInvExclEx, hAckExclEx,
    hAckDirNotUnc, hInvDirNotUnc, hAckD2cEmpty, hGntSProp, hGntSDirSh, _hInvInvSet⟩ := h
  -- Key derived facts
  have hAllI : ∀ k, (s.cache k).state = .I := huncInv hdirSt
  have hMemAux : s.memData = s.auxData := hdataF (by rw [hdirSt]; decide)
  have hNoAck : ∀ k, (s.c2dChan k).cmd ≠ .ack := by
    intro k h; have := hAckDirNotUnc k h; rw [hdirSt] at this; exact absurd rfl this
  have hNoInv : ∀ k, (s.d2cChan k).cmd ≠ .inv := by
    intro k h; have := hInvDirNotUnc k h; rw [hdirSt] at this; exact absurd rfl this
  have hNoGntE : ∀ k, (s.d2cChan k).cmd ≠ .gntE := by
    intro k h; have := (hgntEImpl k h).1; rw [hdirSt] at this; exact absurd this (by decide)
  have hNoFetch : ∀ k, (s.d2cChan k).cmd ≠ .fetch := by
    intro k h; exact absurd (hfetchImpl k h).1 (by rw [hcurCmd]; decide)
  have hNoInvSet : ∀ k, s.invSet k = false := by
    intro k; by_contra h; rw [Bool.not_eq_false] at h
    have := hInvSetDirSh k h; rw [hdirSt] at this; exact absurd this (by decide)
  simp only [fullStrongInvariant, strongInvariant, invariant, ctrlProp, dataProp,
    exclusiveConsistent, mImpliesExclusive, sImpliesShrSet, exclusiveExcludesShared,
    uncachedMeansAllInvalid, gntSDataProp, gntEDataProp, invSetSubsetShrSet,
    curNodeNotInInvSet, exclusiveNoDuplicateGrant, sharedNoGntE, gntEImpliesExclusive,
    fetchImpliesCurCmdGetS, invImpliesCurCmd, ackDataProp, ackImpliesInvalid,
    ackImpliesInvSetFalse, invSetImpliesCurCmdGetM, ackImpliesCurCmdNotEmpty, getSAckProp,
    invAckExclusive, invSetImpliesDirShared, invMsgImpliesShrSet,
    ackSharedImpliesShrSet, invExclOnlyAtExNode, ackExclOnlyAtExNode,
    ackImpliesDirNotUncached, invImpliesDirNotUncached,
    ackImpliesD2cEmpty, gntSProp, gntSImpliesDirShared,
    sendGntE_AfterExclusiveState_cache, sendGntE_AfterExclusiveState_c2dChan,
    sendGntE_AfterExclusiveState_curNode, sendGntE_AfterExclusiveState_shrSet,
    sendGntE_AfterExclusiveState_invSet, sendGntE_AfterExclusiveState_memData,
    sendGntE_AfterExclusiveState_dirSt, sendGntE_AfterExclusiveState_exNode,
    sendGntE_AfterExclusiveState_curCmd, sendGntE_AfterExclusiveState_auxData]
  refine ⟨⟨⟨hctrl,
    fun h => absurd rfl h, -- dataProp fst: Exclusive≠Exclusive is False
    fun k hk => absurd (hAllI k) hk⟩, -- dataProp snd: all cache=I, so antecedent false
    fun _ => ?_, -- exclusiveConsistent (dirSt'=Exclusive, always fires)
    fun k hk => ?_, -- mImpliesExclusive
    fun k hk => ?_, -- sImpliesShrSet
    fun _ k hkS => ?_, -- exclusiveExcludesShared (dirSt'=Exclusive)
    fun hunc => absurd hunc (by decide), -- uncachedMeansAllInvalid: Exclusive≠Uncached
    fun k hgntS => ?_, -- gntSDataProp
    fun k hgntE => ?_, -- gntEDataProp
    hinvSub⟩, -- invSetSubsetShrSet: invSet,shrSet unchanged
    fun k hack hcond => absurd hack (hNoAck k), -- ackDataProp: no acks
    fun hgetM => absurd hgetM (by decide), -- curNodeNotInInvSet: empty≠getM
    fun _ k hne => ?_, -- exclusiveNoDuplicateGrant (dirSt'=Exclusive, exNode'=curNode)
    fun hsh => absurd hsh (by decide), -- sharedNoGntE: Exclusive≠Shared
    fun k hgntE => ?_, -- gntEImpliesExclusive (dirSt'=Exclusive, exNode'=curNode)
    fun k hfetch => ?_, -- fetchImpliesCurCmdGetS
    fun k hk => ?_, -- invImpliesCurCmd
    hackInv, -- ackImpliesInvalid: c2dChan,cache unchanged
    hackInvSet, -- ackImpliesInvSetFalse: c2dChan,invSet unchanged
    fun k hk => absurd hk (by rw [hNoInvSet k]; decide), -- invSetImpliesCurCmdGetM: all invSet false
    fun k hack => absurd hack (hNoAck k), -- ackImpliesCurCmdNotEmpty
    fun k hack _ => absurd hack (hNoAck k), -- getSAckProp
    fun k hinv => ?_, -- invAckExclusive
    fun k hk => absurd hk (by rw [hNoInvSet k]; decide), -- invSetImpliesDirShared: all invSet false
    fun k hinv _ => ?_, -- invMsgImpliesShrSet
    fun k hack _ => absurd hack (hNoAck k), -- ackSharedImpliesShrSet
    fun k hinv _ => ?_, -- invExclOnlyAtExNode
    fun k hack _ => absurd hack (hNoAck k), -- ackExclOnlyAtExNode
    fun k hack => absurd hack (hNoAck k), -- ackImpliesDirNotUncached
    fun k hinv => ?_, -- invImpliesDirNotUncached
    fun k hack => ?_, -- ackImpliesD2cEmpty
    fun k hgntS => ?_, -- gntSProp
    fun k hgntS => ?_, -- gntSImpliesDirShared: dirSt'=Exclusive
    ?_⟩ -- invImpliesInvSetFalse
  · -- exclusiveConsistent: dirSt'=Exclusive, exNode'=curNode
    constructor
    · exact Or.inr (Or.inl (by simp [sendGntE_AfterExclusiveState_d2cChan_curNode]))
    · intro k _; exact hAllI k
  · -- mImpliesExclusive: all cache=I, so M impossible
    rw [hAllI k] at hk; exact absurd hk (by decide)
  · -- sImpliesShrSet: all cache=I, so S impossible
    rw [hAllI k] at hk; exact absurd hk (by decide)
  · -- exclusiveExcludesShared: all cache=I, so S impossible
    exact absurd (hAllI k) (by rw [hkS]; decide)
  · -- gntSDataProp
    by_cases hki : k = s.curNode
    · subst hki; simp only [sendGntE_AfterExclusiveState_d2cChan_curNode] at hgntS; exact absurd hgntS (by decide)
    · rw [sendGntE_AfterExclusiveState_d2cChan_ne s k hki] at hgntS ⊢
      exact hgntSD k hgntS
  · -- gntEDataProp: k=curNode: gntE, data=memData ✓. k≠curNode: pre no gntE.
    by_cases hki : k = s.curNode
    · subst hki; simp only [sendGntE_AfterExclusiveState_d2cChan_curNode] at hgntE ⊢
      exact hMemAux
    · rw [sendGntE_AfterExclusiveState_d2cChan_ne s k hki] at hgntE; exact absurd hgntE (hNoGntE k)
  · -- exclusiveNoDuplicateGrant: exNode'=curNode, ∀k≠curNode: pre no gntE
    by_cases hki : k = s.curNode
    · exact absurd hki hne
    · rw [sendGntE_AfterExclusiveState_d2cChan_ne s k hki]; exact hNoGntE k
  · -- gntEImpliesExclusive: dirSt'=Exclusive, exNode'=curNode
    by_cases hki : k = s.curNode
    · subst hki; exact ⟨trivial, rfl⟩
    · rw [sendGntE_AfterExclusiveState_d2cChan_ne s k hki] at hgntE; exact absurd hgntE (hNoGntE k)
  · -- fetchImpliesCurCmdGetS
    by_cases hki : k = s.curNode
    · subst hki; simp only [sendGntE_AfterExclusiveState_d2cChan_curNode] at hfetch; exact absurd hfetch (by decide)
    · rw [sendGntE_AfterExclusiveState_d2cChan_ne s k hki] at hfetch; exact absurd hfetch (hNoFetch k)
  · -- invImpliesCurCmd
    by_cases hki : k = s.curNode
    · subst hki; simp only [sendGntE_AfterExclusiveState_d2cChan_curNode] at hk; exact absurd hk (by decide)
    · rw [sendGntE_AfterExclusiveState_d2cChan_ne s k hki] at hk; exact absurd hk (hNoInv k)
  · -- invAckExclusive
    by_cases hki : k = s.curNode
    · subst hki; simp only [sendGntE_AfterExclusiveState_d2cChan_curNode] at hinv; exact absurd hinv (by decide)
    · rw [sendGntE_AfterExclusiveState_d2cChan_ne s k hki] at hinv; exact absurd hinv (hNoInv k)
  · -- invMsgImpliesShrSet
    by_cases hki : k = s.curNode
    · subst hki; simp only [sendGntE_AfterExclusiveState_d2cChan_curNode] at hinv; exact absurd hinv (by decide)
    · rw [sendGntE_AfterExclusiveState_d2cChan_ne s k hki] at hinv; exact absurd hinv (hNoInv k)
  · -- invExclOnlyAtExNode
    by_cases hki : k = s.curNode
    · subst hki; simp only [sendGntE_AfterExclusiveState_d2cChan_curNode] at hinv; exact absurd hinv (by decide)
    · rw [sendGntE_AfterExclusiveState_d2cChan_ne s k hki] at hinv; exact absurd hinv (hNoInv k)
  · -- invImpliesDirNotUncached: dirSt'=Exclusive≠Uncached
    intro hunc; exact absurd hunc (by decide)
  · -- ackImpliesD2cEmpty: no acks
    exact absurd hack (hNoAck k)
  · -- gntSProp
    by_cases hki : k = s.curNode
    · subst hki; simp only [sendGntE_AfterExclusiveState_d2cChan_curNode] at hgntS; exact absurd hgntS (by decide)
    · rw [sendGntE_AfterExclusiveState_d2cChan_ne s k hki] at hgntS
      rcases hGntSProp k hgntS with h | ⟨_, hcn⟩
      · exact Or.inl h
      · exact absurd hcn.symm hki
  · -- gntSImpliesDirShared: d2cChan[curNode]→gntE, dirSt'=Exclusive
    by_cases hki : k = s.curNode
    · subst hki; simp only [sendGntE_AfterExclusiveState_d2cChan_curNode] at hgntS; exact absurd hgntS (by decide)
    · rw [sendGntE_AfterExclusiveState_d2cChan_ne s k hki] at hgntS
      exact absurd (hGntSDirSh k hgntS) (by rw [hdirSt]; decide)
  · -- invImpliesInvSetFalse
    unfold invImpliesInvSetFalse; intro k hinv
    by_cases hki : k = s.curNode
    · subst hki; simp only [sendGntE_AfterExclusiveState_d2cChan_curNode] at hinv; exact absurd hinv (by decide)
    · rw [sendGntE_AfterExclusiveState_d2cChan_ne s k hki] at hinv; exact absurd hinv (hNoInv k)

end DirectoryMSI
