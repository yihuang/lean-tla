import Leslie.Examples.CacheCoherence.DirectoryMSI.FrameLemmas

namespace DirectoryMSI

/-! ## StepTier3A — RecvAck_GetS and RecvAck_GetM_Exclusive

    Both actions consume a writeback ack from c2dChan[j], store its data into
    memData and auxData, clear c2dChan[j], and set dirSt to Uncached.
    The resulting Uncached state makes many Exclusive/Shared-gated invariants
    vacuously true.
-/

-- ── RecvAck_GetS ────────────────────────────────────────────────────────

theorem fullStrongInvariant_preserved_RecvAck_GetS
    {n : Nat} {s s' : MState n} {j : Fin n}
    (h : fullStrongInvariant n s)
    (hact : RecvAck_GetS s s' j) :
    fullStrongInvariant n s' := by
  obtain ⟨hc2dJ, hcurCmd, hs'⟩ := hact; subst hs'
  obtain ⟨⟨⟨hctrl, _hdataF, _hdataS⟩, hexclCons, _hmImpl, _hsShr, _hexclExcl, _huncInv,
    hgntSD, hgntED, hinvSub⟩,
    hackD, _hcurNot, hexclNoDup, _hshrNoE, hgntEImpl, hfetchImpl, hinvImpl, hackInv,
    hackInvSet, hinvSetCmd, hackCmdNotEmpty, hgetSAck,
    hInvAckExcl, hInvSetDirSh, _hInvMsgShr, _hAckShShr, _hInvExclEx, _hAckExclEx,
    _hAckDirNotUnc, _hInvDirNotUnc, hAckD2cEmpty, hGntSProp, hGntSDirSh, _hInvInvSet⟩ := h
  -- Key derived facts
  have ⟨hdirStExcl, hjExNode⟩ := hgetSAck j hc2dJ hcurCmd
  -- hjExNode : s.exNode = j
  have hAllI : ∀ k, (s.cache k).state = .I := by
    intro k
    by_cases hkj : k = j
    · subst hkj; exact hackInv k hc2dJ
    · exact ((hexclCons hdirStExcl).2 k (by rw [hjExNode]; exact hkj))
  have hAckData := hackD j hc2dJ (Or.inr hdirStExcl)
  -- hAckData : (s.c2dChan j).data = s.auxData
  have hNoOtherAck : ∀ k, k ≠ j → (s.c2dChan k).cmd ≠ .ack := by
    intro k hne hack
    have := (hgetSAck k hack hcurCmd).2
    rw [hjExNode] at this; exact hne this.symm
  -- No gntE anywhere: at exNode=j, d2cChan[j] empty (ackImpliesD2cEmpty).
  -- At k≠exNode, exclusiveNoDuplicateGrant.
  have hD2cJEmpty := hAckD2cEmpty j hc2dJ
  have hNoGntE : ∀ k, (s.d2cChan k).cmd ≠ .gntE := by
    intro k hgntE
    by_cases hkj : k = j
    · subst hkj; rw [hD2cJEmpty] at hgntE; exact absurd hgntE (by decide)
    · exact absurd hgntE (hexclNoDup hdirStExcl k (by rw [hjExNode]; exact hkj))
  -- No fetch: fetchImpliesCurCmdGetS gives curCmd=getS ∧ dirSt=Exclusive ∧ exNode=k.
  -- d2cChan[exNode]=d2cChan[j] is empty, so fetch at j impossible.
  -- For k≠j: fetch→exNode=k, but exNode=j, contradiction.
  have hNoFetch : ∀ k, (s.d2cChan k).cmd ≠ .fetch := by
    intro k hfetch
    have ⟨_, _, hfEx⟩ := hfetchImpl k hfetch
    by_cases hkj : k = j
    · subst hkj; rw [hD2cJEmpty] at hfetch; exact absurd hfetch (by decide)
    · rw [hjExNode] at hfEx; exact hkj hfEx.symm
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
    recvAck_GetSState_cache, recvAck_GetSState_d2cChan, recvAck_GetSState_shrSet,
    recvAck_GetSState_exNode, recvAck_GetSState_curCmd, recvAck_GetSState_curNode,
    recvAck_GetSState_invSet, recvAck_GetSState_memData, recvAck_GetSState_auxData,
    recvAck_GetSState_dirSt]
  refine ⟨⟨⟨hctrl,
    -- dataProp fst: Uncached≠Exclusive simplifies to True, but wrapped in →
    fun _ => trivial,
    -- dataProp snd: all cache=I, antecedent false
    fun k hk => absurd (hAllI k) hk⟩,
    -- exclusiveConsistent: Uncached≠Exclusive → vacuous
    fun hex => absurd hex (by decide),
    -- mImpliesExclusive: all cache=I, M impossible
    fun k hk => absurd (hAllI k) (by rw [hk]; decide),
    -- sImpliesShrSet: all cache=I, S impossible
    fun k hk => absurd (hAllI k) (by rw [hk]; decide),
    -- exclusiveExcludesShared: Uncached≠Exclusive → vacuous
    fun hex => absurd hex (by decide),
    -- uncachedMeansAllInvalid: Uncached, all I
    fun _ k => hAllI k,
    -- gntSDataProp: d2cChan unchanged, goal: d2cChan[k].data = c2dChan[j].data
    fun k hgntS => by rw [hgntSD k hgntS, hAckData],
    -- gntEDataProp: no gntE exists
    fun k hgntE => absurd hgntE (hNoGntE k),
    -- invSetSubsetShrSet: invSet,shrSet unchanged
    hinvSub⟩,
    -- ackDataProp: by_cases k=j. k=j: empty. k≠j: no other ack.
    fun k hack _ => by
      by_cases hkj : k = j
      · subst hkj; simp at hack
      · exact absurd hack (by rw [recvAck_GetSState_c2dChan_ne s j k hkj]; exact hNoOtherAck k hkj),
    -- curNodeNotInInvSet: dirSt'=Uncached≠Shared
    fun _ hsh => absurd hsh (by decide),
    -- exclusiveNoDuplicateGrant: Uncached≠Exclusive → vacuous
    fun hex => absurd hex (by decide),
    -- sharedNoGntE: Uncached≠Shared → vacuous
    fun hsh => absurd hsh (by decide),
    -- gntEImpliesExclusive: no gntE exists
    fun k hgntE => absurd hgntE (hNoGntE k),
    -- fetchImpliesCurCmdGetS: no fetch exists
    fun k hfetch => absurd hfetch (hNoFetch k),
    -- invImpliesCurCmd: d2cChan unchanged, curCmd unchanged
    hinvImpl,
    -- ackImpliesInvalid: by_cases k=j
    fun k hack => by
      by_cases hkj : k = j
      · subst hkj; simp at hack
      · rw [recvAck_GetSState_c2dChan_ne s j k hkj] at hack; exact hackInv k hack,
    -- ackImpliesInvSetFalse: by_cases k=j
    fun k hack => by
      by_cases hkj : k = j
      · subst hkj; simp at hack
      · rw [recvAck_GetSState_c2dChan_ne s j k hkj] at hack; exact hackInvSet k hack,
    -- invSetImpliesCurCmdGetM: invSet,curCmd unchanged
    hinvSetCmd,
    -- ackImpliesCurCmdNotEmpty: by_cases k=j
    fun k hack => by
      by_cases hkj : k = j
      · subst hkj; simp at hack
      · rw [recvAck_GetSState_c2dChan_ne s j k hkj] at hack; exact hackCmdNotEmpty k hack,
    -- getSAckProp: dirSt'=Uncached. k=j: empty. k≠j: hNoOtherAck.
    fun k hack _ => by
      by_cases hkj : k = j
      · subst hkj; simp at hack
      · exact absurd hack (by rw [recvAck_GetSState_c2dChan_ne s j k hkj]; exact hNoOtherAck k hkj),
    -- invAckExclusive: d2cChan unchanged, by_cases k=j
    fun k hinv hack => by
      by_cases hkj : k = j
      · subst hkj; simp at hack
      · rw [recvAck_GetSState_c2dChan_ne s j k hkj] at hack; exact hInvAckExcl k hinv hack,
    -- invSetImpliesDirShared: invSet unchanged, pre-state Exclusive≠Shared
    fun k hk => by
      have := hInvSetDirSh k hk  -- s.dirSt = .Shared
      rw [hdirStExcl] at this; exact absurd this (by decide),
    -- invMsgImpliesShrSet: dirSt'=Uncached≠Shared
    fun _ _ hsh => absurd hsh (by decide),
    -- ackSharedImpliesShrSet: dirSt'=Uncached≠Shared
    fun _ _ hsh => absurd hsh (by decide),
    -- invExclOnlyAtExNode: dirSt'=Uncached≠Exclusive
    fun _ _ hex => absurd hex (by decide),
    -- ackExclOnlyAtExNode: dirSt'=Uncached≠Exclusive
    fun _ _ hex => absurd hex (by decide),
    -- ackImpliesDirNotUncached: dirSt'=Uncached. k=j: empty. k≠j: no other ack.
    fun k hack => by
      by_cases hkj : k = j
      · subst hkj; simp at hack
      · exact absurd hack (by rw [recvAck_GetSState_c2dChan_ne s j k hkj]; exact hNoOtherAck k hkj),
    -- invImpliesDirNotUncached: d2cChan unchanged. invImpliesCurCmd→getM, curCmd=getS.
    fun k hinv _ => by
      have := hinvImpl k hinv
      rw [hcurCmd] at this; exact absurd this (by decide),
    -- ackImpliesD2cEmpty: d2cChan unchanged, by_cases k=j
    fun k hack => by
      by_cases hkj : k = j
      · subst hkj; simp at hack
      · rw [recvAck_GetSState_c2dChan_ne s j k hkj] at hack; exact hAckD2cEmpty k hack,
    -- gntSProp: d2cChan,shrSet,curCmd,curNode unchanged
    hGntSProp,
    -- gntSImpliesDirShared: d2cChan unchanged, dirSt'=Uncached. Pre: gntS→Shared.
    -- If gntS at k: hGntSDirSh→dirSt=Shared. But dirSt was Exclusive (hdirStExcl). Contradiction.
    fun k hgntS => by
      have := hGntSDirSh k hgntS; rw [hdirStExcl] at this; exact absurd this (by decide),
    -- invImpliesInvSetFalse: d2cChan unchanged, invSet unchanged
    invImpliesInvSetFalse_preserved_of_d2cChan_invSet_eq rfl rfl _hInvInvSet⟩

-- ── RecvAck_GetM_Exclusive ──────────────────────────────────────────────

theorem fullStrongInvariant_preserved_RecvAck_GetM_Exclusive
    {n : Nat} {s s' : MState n} {j : Fin n}
    (h : fullStrongInvariant n s)
    (hact : RecvAck_GetM_Exclusive s s' j) :
    fullStrongInvariant n s' := by
  obtain ⟨hc2dJ, hcurCmd, hdirSt, hs'⟩ := hact; subst hs'
  obtain ⟨⟨⟨hctrl, _hdataF, _hdataS⟩, hexclCons, _hmImpl, _hsShr, _hexclExcl, _huncInv,
    hgntSD, hgntED, hinvSub⟩,
    hackD, _hcurNot, hexclNoDup, _hshrNoE, hgntEImpl, hfetchImpl, _hinvImpl, hackInv,
    hackInvSet, hinvSetCmd, hackCmdNotEmpty, _hgetSAck,
    hInvAckExcl, hInvSetDirSh, _hInvMsgShr, _hAckShShr, hInvExclEx, hAckExclEx,
    _hAckDirNotUnc, _hInvDirNotUnc, hAckD2cEmpty, hGntSProp, hGntSDirSh, _hInvInvSet⟩ := h
  -- Key derived facts
  have hjExNode := hAckExclEx j hc2dJ hdirSt  -- j = s.exNode
  have hAllI : ∀ k, (s.cache k).state = .I := by
    intro k
    by_cases hkj : k = j
    · subst hkj; exact hackInv k hc2dJ
    · exact ((hexclCons hdirSt).2 k (by rw [← hjExNode]; exact hkj))
  have hAckData := hackD j hc2dJ (Or.inr hdirSt)
  -- hAckData : (s.c2dChan j).data = s.auxData
  have hNoOtherAck : ∀ k, k ≠ j → (s.c2dChan k).cmd ≠ .ack := by
    intro k hne hack
    have := hAckExclEx k hack hdirSt
    rw [← hjExNode] at this; exact hne this
  have hNoInv : ∀ k, (s.d2cChan k).cmd ≠ .inv := by
    intro k hinv
    have hkex := hInvExclEx k hinv hdirSt  -- k = exNode
    rw [← hjExNode] at hkex; rw [hkex] at hinv; exact hInvAckExcl j hinv hc2dJ
  -- No gntE anywhere
  have hD2cJEmpty := hAckD2cEmpty j hc2dJ
  have hNoGntE : ∀ k, (s.d2cChan k).cmd ≠ .gntE := by
    intro k hgntE
    by_cases hkj : k = j
    · subst hkj; rw [hD2cJEmpty] at hgntE; exact absurd hgntE (by decide)
    · exact absurd hgntE (hexclNoDup hdirSt k (by rw [← hjExNode]; exact hkj))
  -- No fetch
  have hNoFetch : ∀ k, (s.d2cChan k).cmd ≠ .fetch := by
    intro k hfetch
    have := (hfetchImpl k hfetch).1
    rw [hcurCmd] at this; exact absurd this (by decide)
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
    recvAck_GetM_ExclusiveState_cache, recvAck_GetM_ExclusiveState_d2cChan,
    recvAck_GetM_ExclusiveState_shrSet, recvAck_GetM_ExclusiveState_exNode,
    recvAck_GetM_ExclusiveState_curCmd, recvAck_GetM_ExclusiveState_curNode,
    recvAck_GetM_ExclusiveState_invSet, recvAck_GetM_ExclusiveState_memData,
    recvAck_GetM_ExclusiveState_auxData, recvAck_GetM_ExclusiveState_dirSt]
  refine ⟨⟨⟨hctrl,
    -- dataProp fst: Uncached≠Exclusive simplifies to True, but wrapped in →
    fun _ => trivial,
    -- dataProp snd: all cache=I, antecedent false
    fun k hk => absurd (hAllI k) hk⟩,
    -- exclusiveConsistent: Uncached≠Exclusive → vacuous
    fun hex => absurd hex (by decide),
    -- mImpliesExclusive: all cache=I, M impossible
    fun k hk => absurd (hAllI k) (by rw [hk]; decide),
    -- sImpliesShrSet: all cache=I, S impossible
    fun k hk => absurd (hAllI k) (by rw [hk]; decide),
    -- exclusiveExcludesShared: Uncached≠Exclusive → vacuous
    fun hex => absurd hex (by decide),
    -- uncachedMeansAllInvalid: Uncached, all I
    fun _ k => hAllI k,
    -- gntSDataProp: d2cChan unchanged, goal: d2cChan[k].data = c2dChan[j].data
    fun k hgntS => by rw [hgntSD k hgntS, hAckData],
    -- gntEDataProp: no gntE exists
    fun k hgntE => absurd hgntE (hNoGntE k),
    -- invSetSubsetShrSet: invSet,shrSet unchanged
    hinvSub⟩,
    -- ackDataProp: by_cases k=j. k=j: empty. k≠j: no other ack.
    fun k hack _ => by
      by_cases hkj : k = j
      · subst hkj; simp at hack
      · exact absurd hack (by rw [recvAck_GetM_ExclusiveState_c2dChan_ne s j k hkj]; exact hNoOtherAck k hkj),
    -- curNodeNotInInvSet: dirSt'=Uncached≠Shared
    fun _ hsh => absurd hsh (by decide),
    -- exclusiveNoDuplicateGrant: Uncached≠Exclusive → vacuous
    fun hex => absurd hex (by decide),
    -- sharedNoGntE: Uncached≠Shared → vacuous
    fun hsh => absurd hsh (by decide),
    -- gntEImpliesExclusive: no gntE exists
    fun k hgntE => absurd hgntE (hNoGntE k),
    -- fetchImpliesCurCmdGetS: no fetch exists
    fun k hfetch => absurd hfetch (hNoFetch k),
    -- invImpliesCurCmd: no invs
    fun k hinv => absurd hinv (hNoInv k),
    -- ackImpliesInvalid: by_cases k=j
    fun k hack => by
      by_cases hkj : k = j
      · subst hkj; simp at hack
      · rw [recvAck_GetM_ExclusiveState_c2dChan_ne s j k hkj] at hack; exact hackInv k hack,
    -- ackImpliesInvSetFalse: by_cases k=j
    fun k hack => by
      by_cases hkj : k = j
      · subst hkj; simp at hack
      · rw [recvAck_GetM_ExclusiveState_c2dChan_ne s j k hkj] at hack; exact hackInvSet k hack,
    -- invSetImpliesCurCmdGetM: invSet,curCmd unchanged
    hinvSetCmd,
    -- ackImpliesCurCmdNotEmpty: by_cases k=j
    fun k hack => by
      by_cases hkj : k = j
      · subst hkj; simp at hack
      · rw [recvAck_GetM_ExclusiveState_c2dChan_ne s j k hkj] at hack; exact hackCmdNotEmpty k hack,
    -- getSAckProp: curCmd'=getM≠getS → vacuous
    fun k hack hgetS => by rw [hcurCmd] at hgetS; exact absurd hgetS (by decide),
    -- invAckExclusive: no invs
    fun k hinv _ => absurd hinv (hNoInv k),
    -- invSetImpliesDirShared: invSet unchanged, pre-state Exclusive≠Shared
    fun k hk => by
      have := hInvSetDirSh k hk  -- s.dirSt = .Shared
      rw [hdirSt] at this; exact absurd this (by decide),
    -- invMsgImpliesShrSet: dirSt'=Uncached≠Shared
    fun _ _ hsh => absurd hsh (by decide),
    -- ackSharedImpliesShrSet: dirSt'=Uncached≠Shared
    fun _ _ hsh => absurd hsh (by decide),
    -- invExclOnlyAtExNode: dirSt'=Uncached≠Exclusive
    fun _ _ hex => absurd hex (by decide),
    -- ackExclOnlyAtExNode: dirSt'=Uncached≠Exclusive
    fun _ _ hex => absurd hex (by decide),
    -- ackImpliesDirNotUncached: dirSt'=Uncached. k=j: empty. k≠j: no other ack.
    fun k hack => by
      by_cases hkj : k = j
      · subst hkj; simp at hack
      · exact absurd hack (by rw [recvAck_GetM_ExclusiveState_c2dChan_ne s j k hkj]; exact hNoOtherAck k hkj),
    -- invImpliesDirNotUncached: no invs
    fun k hinv _ => absurd hinv (hNoInv k),
    -- ackImpliesD2cEmpty: d2cChan unchanged, by_cases k=j
    fun k hack => by
      by_cases hkj : k = j
      · subst hkj; simp at hack
      · rw [recvAck_GetM_ExclusiveState_c2dChan_ne s j k hkj] at hack; exact hAckD2cEmpty k hack,
    -- gntSProp: d2cChan,shrSet,curCmd,curNode unchanged
    hGntSProp,
    -- gntSImpliesDirShared: d2cChan unchanged, dirSt'=Uncached. Pre: gntS→Shared.
    -- If gntS at k: hGntSDirSh→dirSt=Shared. But dirSt=Exclusive (hdirSt). Contradiction.
    fun k hgntS => by
      have := hGntSDirSh k hgntS; rw [hdirSt] at this; exact absurd this (by decide),
    -- invImpliesInvSetFalse: d2cChan unchanged, invSet unchanged
    invImpliesInvSetFalse_preserved_of_d2cChan_invSet_eq rfl rfl _hInvInvSet⟩

end DirectoryMSI
