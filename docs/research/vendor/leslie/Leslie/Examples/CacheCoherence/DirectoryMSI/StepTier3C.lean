import Leslie.Examples.CacheCoherence.DirectoryMSI.FrameLemmas

namespace DirectoryMSI

/-! ## StepTier3C — RecvInv and RecvFetch

    Both actions consume a d2cChan message (inv/fetch) at node i, set cache[i] → I,
    send c2dChan[i] → {ack, cache[i].data}, and clear d2cChan[i] → empty.
-/

-- ── RecvInv ────────────────────────────────────────────────────────────

theorem fullStrongInvariant_preserved_RecvInv
    {n : Nat} {s s' : MState n} {i : Fin n}
    (h : fullStrongInvariant n s)
    (hact : RecvInv s s' i) :
    fullStrongInvariant n s' := by
  obtain ⟨hd2cInv, hc2dEmpty, hs'⟩ := hact; subst hs'
  obtain ⟨⟨⟨hctrl, hdataF, hdataS⟩, hexclCons, hmImpl, hsShr, hexclExcl, huncInv,
    hgntSD, hgntED, hinvSub⟩,
    hackD, hcurNot, hexclNoDup, hshrNoE, hgntEImpl, hfetchImpl, hinvImpl, hackInv,
    hackInvSet, hinvSetCmd, hackCmdNotEmpty, hgetSAck,
    hInvAckExcl, hInvSetDirSh, hInvMsgShr, hAckShShr, hInvExclEx, hAckExclEx,
    hAckDirNotUnc, hInvDirNotUnc, hAckD2cEmpty, hGntSProp, hGntSDirSh, hInvInvSet⟩ := h
  -- Key derived facts
  have hCurCmdGetM := hinvImpl i hd2cInv -- curCmd = getM
  have hInvSetI := hInvInvSet i hd2cInv -- invSet[i] = false
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
    recvInvState_dirSt, recvInvState_shrSet,
    recvInvState_exNode, recvInvState_curCmd, recvInvState_curNode,
    recvInvState_invSet, recvInvState_memData, recvInvState_auxData]
  refine ⟨⟨⟨
    -- ctrlProp
    fun p q hpq => ?_,
    -- dataProp fst
    hdataF,
    -- dataProp snd
    fun k hk => ?_⟩,
    -- exclusiveConsistent
    fun hex => ?_,
    -- mImpliesExclusive
    fun k hk => ?_,
    -- sImpliesShrSet
    fun k hk => ?_,
    -- exclusiveExcludesShared
    fun hex k hkS => ?_,
    -- uncachedMeansAllInvalid
    fun hunc k => ?_,
    -- gntSDataProp
    fun k hgntS => ?_,
    -- gntEDataProp
    fun k hgntE => ?_,
    -- invSetSubsetShrSet
    hinvSub⟩,
    -- ackDataProp
    fun k hack hcond => ?_,
    -- curNodeNotInInvSet
    hcurNot,
    -- exclusiveNoDuplicateGrant
    fun hex k hne => ?_,
    -- sharedNoGntE
    fun hsh k => ?_,
    -- gntEImpliesExclusive
    fun k hgntE => ?_,
    -- fetchImpliesCurCmdGetS
    fun k hfetch => ?_,
    -- invImpliesCurCmd
    fun k hk => ?_,
    -- ackImpliesInvalid
    fun k hack => ?_,
    -- ackImpliesInvSetFalse
    fun k hack => ?_,
    -- invSetImpliesCurCmdGetM
    hinvSetCmd,
    -- ackImpliesCurCmdNotEmpty
    fun k hack => ?_,
    -- getSAckProp
    fun k hack hgetS => ?_,
    -- invAckExclusive
    fun k hinv hack => ?_,
    -- invSetImpliesDirShared
    hInvSetDirSh,
    -- invMsgImpliesShrSet
    fun k hinv hsh => ?_,
    -- ackSharedImpliesShrSet
    fun k hack hsh => ?_,
    -- invExclOnlyAtExNode
    fun k hinv hexcl => ?_,
    -- ackExclOnlyAtExNode
    fun k hack hexcl => ?_,
    -- ackImpliesDirNotUncached
    fun k hack => ?_,
    -- invImpliesDirNotUncached
    fun k hinv => ?_,
    -- ackImpliesD2cEmpty
    fun k hack => ?_,
    -- gntSProp
    fun k hgntS => ?_,
    -- gntSImpliesDirShared
    fun k hgntS => ?_,
    ?_⟩ -- invImpliesInvSetFalse
  -- ctrlProp
  · constructor
    · intro hpM
      by_cases hpi : p = i
      · subst hpi; simp [recvInvState_cache_state_self] at hpM
      · rw [recvInvState_cache_state_ne s i p hpi] at hpM
        by_cases hqi : q = i
        · subst hqi; simp [recvInvState_cache_state_self]
        · rw [recvInvState_cache_state_ne s i q hqi]; exact (hctrl p q hpq).1 hpM
    · intro hpS hqM
      by_cases hqi : q = i
      · subst hqi; simp [recvInvState_cache_state_self] at hqM
      · rw [recvInvState_cache_state_ne s i q hqi] at hqM
        by_cases hpi : p = i
        · subst hpi; simp [recvInvState_cache_state_self] at hpS
        · rw [recvInvState_cache_state_ne s i p hpi] at hpS; exact (hctrl p q hpq).2 hpS hqM
  -- dataProp snd
  · by_cases hki : k = i
    · subst hki; simp [recvInvState_cache_state_self] at hk
    · rw [recvInvState_cache_state_ne s i k hki] at hk
      rw [recvInvState_cache_data_ne s i k hki]; exact hdataS k hk
  -- exclusiveConsistent
  · constructor
    · rcases (hexclCons hex).1 with hcM | hgntE | hack
      · by_cases hei : s.exNode = i
        · right; right; rw [hei]; simp [recvInvState_c2dChan_self]
        · left; rw [recvInvState_cache_state_ne s i s.exNode hei]; exact hcM
      · by_cases hei : s.exNode = i
        · rw [hei] at hgntE; exact absurd hgntE (by rw [hd2cInv]; decide)
        · right; left; rw [recvInvState_d2cChan_ne s i s.exNode hei]; exact hgntE
      · by_cases hei : s.exNode = i
        · rw [hei] at hack; exact absurd hack (by rw [hc2dEmpty]; decide)
        · right; right; rw [recvInvState_c2dChan_ne s i s.exNode hei]; exact hack
    · intro j hji
      by_cases hji2 : j = i
      · subst hji2; simp [recvInvState_cache_state_self]
      · rw [recvInvState_cache_state_ne s i j hji2]; exact (hexclCons hex).2 j hji
  -- mImpliesExclusive
  · by_cases hki : k = i
    · subst hki; simp [recvInvState_cache_state_self] at hk
    · rw [recvInvState_cache_state_ne s i k hki] at hk; exact hmImpl k hk
  -- sImpliesShrSet
  · by_cases hki : k = i
    · subst hki; simp [recvInvState_cache_state_self] at hk
    · rw [recvInvState_cache_state_ne s i k hki] at hk
      rcases hsShr k hk with h | h | hgntE
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (by rw [recvInvState_d2cChan_ne s i k hki]; exact hgntE))
  -- exclusiveExcludesShared
  · by_cases hki : k = i
    · subst hki; simp [recvInvState_cache_state_self] at hkS
    · rw [recvInvState_cache_state_ne s i k hki] at hkS
      rw [recvInvState_d2cChan_ne s i k hki]; exact hexclExcl hex k hkS
  -- uncachedMeansAllInvalid
  · by_cases hki : k = i
    · subst hki; simp [recvInvState_cache_state_self]
    · rw [recvInvState_cache_state_ne s i k hki]; exact huncInv hunc k
  -- gntSDataProp
  · by_cases hki : k = i
    · subst hki; simp [recvInvState_d2cChan_self] at hgntS
    · rw [recvInvState_d2cChan_ne s i k hki] at hgntS ⊢; exact hgntSD k hgntS
  -- gntEDataProp
  · by_cases hki : k = i
    · subst hki; simp [recvInvState_d2cChan_self] at hgntE
    · rw [recvInvState_d2cChan_ne s i k hki] at hgntE ⊢; exact hgntED k hgntE
  -- ackDataProp
  · by_cases hki : k = i
    · subst hki
      -- c2dChan[i] post = {ack, (s.cache i).data}. Goal: data = auxData.
      -- Need (s.cache i).data = auxData.
      -- From inv at i and dirSt=Exclusive (if that's the case):
      --   invExclOnlyAtExNode → i=exNode, exclusiveConsistent → cache[i]=M (since gntE/ack impossible)
      --   dataProp snd → data=auxData.
      -- If cache[i]=M (from hcond): dataProp snd directly.
      simp [recvInvState_c2dChan_self]
      rcases hcond with hM | hexcl
      · simp [recvInvState_cache_state_self] at hM
      · have hei := hInvExclEx k hd2cInv hexcl
        rcases (hexclCons hexcl).1 with hcM | hgntE | hack2
        · rw [← hei] at hcM; exact hdataS k (by rw [hcM]; decide)
        · rw [← hei] at hgntE; exact absurd hgntE (by rw [hd2cInv]; decide)
        · rw [← hei] at hack2; exact absurd hack2 (by rw [hc2dEmpty]; decide)
    · rw [recvInvState_c2dChan_ne s i k hki] at hack
      rw [recvInvState_c2dChan_ne s i k hki]
      rcases hcond with hM | hexcl
      · rw [recvInvState_cache_state_ne s i k hki] at hM
        exact hackD k hack (Or.inl hM)
      · exact hackD k hack (Or.inr hexcl)
  -- exclusiveNoDuplicateGrant
  · by_cases hki : k = i
    · subst hki; simp [recvInvState_d2cChan_self]
    · rw [recvInvState_d2cChan_ne s i k hki]; exact hexclNoDup hex k hne
  -- sharedNoGntE
  · by_cases hki : k = i
    · subst hki; simp [recvInvState_d2cChan_self]
    · rw [recvInvState_d2cChan_ne s i k hki]; exact hshrNoE hsh k
  -- gntEImpliesExclusive
  · by_cases hki : k = i
    · subst hki; simp [recvInvState_d2cChan_self] at hgntE
    · rw [recvInvState_d2cChan_ne s i k hki] at hgntE; exact hgntEImpl k hgntE
  -- fetchImpliesCurCmdGetS
  · by_cases hki : k = i
    · subst hki; simp [recvInvState_d2cChan_self] at hfetch
    · rw [recvInvState_d2cChan_ne s i k hki] at hfetch; exact hfetchImpl k hfetch
  -- invImpliesCurCmd
  · by_cases hki : k = i
    · subst hki; simp [recvInvState_d2cChan_self] at hk
    · rw [recvInvState_d2cChan_ne s i k hki] at hk; exact hinvImpl k hk
  -- ackImpliesInvalid
  · by_cases hki : k = i
    · subst hki
      simp [recvInvState_c2dChan_self] at hack
      simp [recvInvState_cache_state_self]
    · rw [recvInvState_c2dChan_ne s i k hki] at hack
      rw [recvInvState_cache_state_ne s i k hki]; exact hackInv k hack
  -- ackImpliesInvSetFalse
  · by_cases hki : k = i
    · subst hki; exact hInvSetI
    · rw [recvInvState_c2dChan_ne s i k hki] at hack; exact hackInvSet k hack
  -- ackImpliesCurCmdNotEmpty
  · by_cases hki : k = i
    · subst hki; rw [hCurCmdGetM]; decide
    · rw [recvInvState_c2dChan_ne s i k hki] at hack; exact hackCmdNotEmpty k hack
  -- getSAckProp
  · by_cases hki : k = i
    · subst hki
      simp [recvInvState_c2dChan_self] at hack
      exact absurd hgetS (by rw [hCurCmdGetM]; decide)
    · rw [recvInvState_c2dChan_ne s i k hki] at hack; exact hgetSAck k hack hgetS
  -- invAckExclusive
  · by_cases hki : k = i
    · subst hki; simp [recvInvState_d2cChan_self] at hinv
    · rw [recvInvState_d2cChan_ne s i k hki] at hinv
      rw [recvInvState_c2dChan_ne s i k hki] at hack
      exact hInvAckExcl k hinv hack
  -- invMsgImpliesShrSet
  · by_cases hki : k = i
    · subst hki; simp [recvInvState_d2cChan_self] at hinv
    · rw [recvInvState_d2cChan_ne s i k hki] at hinv; exact hInvMsgShr k hinv hsh
  -- ackSharedImpliesShrSet
  · by_cases hki : k = i
    · subst hki
      simp [recvInvState_c2dChan_self] at hack
      exact hInvMsgShr k hd2cInv hsh
    · rw [recvInvState_c2dChan_ne s i k hki] at hack; exact hAckShShr k hack hsh
  -- invExclOnlyAtExNode
  · by_cases hki : k = i
    · subst hki; simp [recvInvState_d2cChan_self] at hinv
    · rw [recvInvState_d2cChan_ne s i k hki] at hinv; exact hInvExclEx k hinv hexcl
  -- ackExclOnlyAtExNode
  · by_cases hki : k = i
    · subst hki
      simp [recvInvState_c2dChan_self] at hack
      exact hInvExclEx k hd2cInv hexcl
    · rw [recvInvState_c2dChan_ne s i k hki] at hack; exact hAckExclEx k hack hexcl
  -- ackImpliesDirNotUncached
  · by_cases hki : k = i
    · subst hki
      simp [recvInvState_c2dChan_self] at hack
      exact hInvDirNotUnc k hd2cInv
    · rw [recvInvState_c2dChan_ne s i k hki] at hack; exact hAckDirNotUnc k hack
  -- invImpliesDirNotUncached
  · by_cases hki : k = i
    · subst hki; simp [recvInvState_d2cChan_self] at hinv
    · rw [recvInvState_d2cChan_ne s i k hki] at hinv; exact hInvDirNotUnc k hinv
  -- ackImpliesD2cEmpty
  · by_cases hki : k = i
    · subst hki; simp [recvInvState_d2cChan_self]
    · rw [recvInvState_c2dChan_ne s i k hki] at hack
      rw [recvInvState_d2cChan_ne s i k hki]; exact hAckD2cEmpty k hack
  -- gntSProp
  · by_cases hki : k = i
    · subst hki; simp [recvInvState_d2cChan_self] at hgntS
    · rw [recvInvState_d2cChan_ne s i k hki] at hgntS; exact hGntSProp k hgntS
  -- gntSImpliesDirShared
  · by_cases hki : k = i
    · subst hki; simp [recvInvState_d2cChan_self] at hgntS
    · rw [recvInvState_d2cChan_ne s i k hki] at hgntS; exact hGntSDirSh k hgntS
  -- invImpliesInvSetFalse
  · unfold invImpliesInvSetFalse; intro k hinv
    by_cases hki : k = i
    · subst hki; simp [recvInvState_d2cChan_self] at hinv
    · rw [recvInvState_d2cChan_ne s i k hki] at hinv; exact hInvInvSet k hinv

-- ── RecvFetch ──────────────────────────────────────────────────────────

theorem fullStrongInvariant_preserved_RecvFetch
    {n : Nat} {s s' : MState n} {i : Fin n}
    (h : fullStrongInvariant n s)
    (hact : RecvFetch s s' i) :
    fullStrongInvariant n s' := by
  obtain ⟨hd2cFetch, hc2dEmpty, hs'⟩ := hact; subst hs'
  obtain ⟨⟨⟨hctrl, hdataF, hdataS⟩, hexclCons, hmImpl, hsShr, hexclExcl, huncInv,
    hgntSD, hgntED, hinvSub⟩,
    hackD, hcurNot, hexclNoDup, hshrNoE, hgntEImpl, hfetchImpl, hinvImpl, hackInv,
    hackInvSet, hinvSetCmd, hackCmdNotEmpty, hgetSAck,
    hInvAckExcl, hInvSetDirSh, hInvMsgShr, hAckShShr, hInvExclEx, hAckExclEx,
    hAckDirNotUnc, hInvDirNotUnc, hAckD2cEmpty, hGntSProp, hGntSDirSh, hInvInvSet⟩ := h
  -- Key derived facts
  have ⟨hCurCmdGetS, hDirExcl, hExNodeI⟩ := hfetchImpl i hd2cFetch
  -- cache[i]=M: exNode=i, d2cChan[i]=fetch≠gntE, c2dChan[i]=empty≠ack
  have hCacheIM : (s.cache i).state = .M := by
    rcases (hexclCons hDirExcl).1 with hcM | hgntE | hack
    · exact hExNodeI ▸ hcM
    · exact absurd (hExNodeI ▸ hgntE) (by rw [hd2cFetch]; decide)
    · exact absurd (hExNodeI ▸ hack) (by rw [hc2dEmpty]; decide)
  -- All other caches are I
  have hOtherI : ∀ k, k ≠ i → (s.cache k).state = .I := by
    intro k hki; exact (hexclCons hDirExcl).2 k (by rw [hExNodeI]; exact hki)
  -- cache[i].data = auxData
  have hDataI := hdataS i (by rw [hCacheIM]; decide)
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
    recvFetchState_dirSt, recvFetchState_shrSet,
    recvFetchState_exNode, recvFetchState_curCmd, recvFetchState_curNode,
    recvFetchState_invSet, recvFetchState_memData, recvFetchState_auxData]
  refine ⟨⟨⟨
    fun p q hpq => ?_, hdataF, fun k hk => ?_⟩,
    fun hex => ?_, fun k hk => ?_, fun k hk => ?_, fun hex k hkS => ?_,
    fun hunc => absurd hunc (by rw [hDirExcl]; decide),
    fun k hgntS => ?_, fun k hgntE => ?_, hinvSub⟩,
    fun k hack hcond => ?_, hcurNot, fun hex k hne => ?_,
    fun hsh => absurd hsh (by rw [hDirExcl]; decide),
    fun k hgntE => ?_, fun k hfetch => ?_, fun k hk => ?_,
    fun k hack => ?_, fun k hack => ?_, hinvSetCmd,
    fun k hack => ?_, fun k hack hgetS => ?_, fun k hinv hack => ?_,
    hInvSetDirSh, fun k hinv hsh => ?_, fun k hack hsh => ?_,
    fun k hinv hexcl => ?_, fun k hack hexcl => ?_,
    fun k hack => ?_, fun k hinv => ?_, fun k hack => ?_,
    fun k hgntS => ?_, fun k hgntS => ?_, ?_⟩
  -- ctrlProp
  · constructor
    · intro hpM
      by_cases hpi : p = i
      · subst hpi; simp [recvFetchState_cache_state_self] at hpM
      · rw [recvFetchState_cache_state_ne s i p hpi] at hpM
        by_cases hqi : q = i
        · subst hqi; simp [recvFetchState_cache_state_self]
        · rw [recvFetchState_cache_state_ne s i q hqi]; exact (hctrl p q hpq).1 hpM
    · intro hpS hqM
      by_cases hqi : q = i
      · subst hqi; simp [recvFetchState_cache_state_self] at hqM
      · rw [recvFetchState_cache_state_ne s i q hqi] at hqM
        by_cases hpi : p = i
        · subst hpi; simp [recvFetchState_cache_state_self] at hpS
        · rw [recvFetchState_cache_state_ne s i p hpi] at hpS; exact (hctrl p q hpq).2 hpS hqM
  -- dataProp snd
  · by_cases hki : k = i
    · subst hki; simp [recvFetchState_cache_state_self] at hk
    · rw [recvFetchState_cache_state_ne s i k hki] at hk
      rw [recvFetchState_cache_data_ne s i k hki]; exact hdataS k hk
  -- exclusiveConsistent
  · constructor
    · right; right; rw [hExNodeI]; simp [recvFetchState_c2dChan_self]
    · intro j hji
      by_cases hji2 : j = i
      · subst hji2; simp [recvFetchState_cache_state_self]
      · rw [recvFetchState_cache_state_ne s i j hji2]; exact hOtherI j hji2
  -- mImpliesExclusive
  · by_cases hki : k = i
    · subst hki; simp [recvFetchState_cache_state_self] at hk
    · rw [recvFetchState_cache_state_ne s i k hki] at hk; exact hmImpl k hk
  -- sImpliesShrSet
  · by_cases hki : k = i
    · subst hki; simp [recvFetchState_cache_state_self] at hk
    · rw [recvFetchState_cache_state_ne s i k hki] at hk
      rcases hsShr k hk with h | h | hgntE
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (by rw [recvFetchState_d2cChan_ne s i k hki]; exact hgntE))
  -- exclusiveExcludesShared
  · by_cases hki : k = i
    · subst hki; simp [recvFetchState_cache_state_self] at hkS
    · rw [recvFetchState_cache_state_ne s i k hki] at hkS
      rw [recvFetchState_d2cChan_ne s i k hki]; exact hexclExcl hex k hkS
  -- gntSDataProp
  · by_cases hki : k = i
    · subst hki; simp [recvFetchState_d2cChan_self] at hgntS
    · rw [recvFetchState_d2cChan_ne s i k hki] at hgntS ⊢; exact hgntSD k hgntS
  -- gntEDataProp
  · by_cases hki : k = i
    · subst hki; simp [recvFetchState_d2cChan_self] at hgntE
    · rw [recvFetchState_d2cChan_ne s i k hki] at hgntE ⊢; exact hgntED k hgntE
  -- ackDataProp
  · by_cases hki : k = i
    · subst hki
      simp [recvFetchState_c2dChan_self]
      exact hDataI
    · rw [recvFetchState_c2dChan_ne s i k hki] at hack
      rw [recvFetchState_c2dChan_ne s i k hki]
      rcases hcond with hM | hexcl2
      · rw [recvFetchState_cache_state_ne s i k hki] at hM
        exact hackD k hack (Or.inl hM)
      · exact hackD k hack (Or.inr hexcl2)
  -- exclusiveNoDuplicateGrant
  · by_cases hki : k = i
    · subst hki; simp [recvFetchState_d2cChan_self]
    · rw [recvFetchState_d2cChan_ne s i k hki]; exact hexclNoDup hex k hne
  -- gntEImpliesExclusive
  · by_cases hki : k = i
    · subst hki; simp [recvFetchState_d2cChan_self] at hgntE
    · rw [recvFetchState_d2cChan_ne s i k hki] at hgntE; exact hgntEImpl k hgntE
  -- fetchImpliesCurCmdGetS
  · by_cases hki : k = i
    · subst hki; simp [recvFetchState_d2cChan_self] at hfetch
    · rw [recvFetchState_d2cChan_ne s i k hki] at hfetch; exact hfetchImpl k hfetch
  -- invImpliesCurCmd
  · by_cases hki : k = i
    · subst hki; simp [recvFetchState_d2cChan_self] at hk
    · rw [recvFetchState_d2cChan_ne s i k hki] at hk; exact hinvImpl k hk
  -- ackImpliesInvalid
  · by_cases hki : k = i
    · subst hki
      simp [recvFetchState_c2dChan_self] at hack
      simp [recvFetchState_cache_state_self]
    · rw [recvFetchState_c2dChan_ne s i k hki] at hack
      rw [recvFetchState_cache_state_ne s i k hki]; exact hackInv k hack
  -- ackImpliesInvSetFalse
  · by_cases hki : k = i
    · subst hki
      -- invSet[k] must be false: if true, invSetImpliesCurCmdGetM → curCmd=getM.
      -- But curCmd=getS. Contradiction. So invSet[k]=false.
      by_contra hne
      have hTrue : s.invSet k = true := by
        cases h2 : s.invSet k <;> simp_all
      exact absurd (hinvSetCmd k hTrue) (by rw [hCurCmdGetS]; decide)
    · rw [recvFetchState_c2dChan_ne s i k hki] at hack; exact hackInvSet k hack
  -- ackImpliesCurCmdNotEmpty
  · by_cases hki : k = i
    · subst hki; rw [hCurCmdGetS]; decide
    · rw [recvFetchState_c2dChan_ne s i k hki] at hack; exact hackCmdNotEmpty k hack
  -- getSAckProp
  · by_cases hki : k = i
    · subst hki
      simp [recvFetchState_c2dChan_self] at hack
      exact ⟨hDirExcl, hExNodeI⟩
    · rw [recvFetchState_c2dChan_ne s i k hki] at hack; exact hgetSAck k hack hgetS
  -- invAckExclusive
  · by_cases hki : k = i
    · subst hki; simp [recvFetchState_d2cChan_self] at hinv
    · rw [recvFetchState_d2cChan_ne s i k hki] at hinv
      rw [recvFetchState_c2dChan_ne s i k hki] at hack
      exact hInvAckExcl k hinv hack
  -- invMsgImpliesShrSet
  · by_cases hki : k = i
    · subst hki; simp [recvFetchState_d2cChan_self] at hinv
    · rw [recvFetchState_d2cChan_ne s i k hki] at hinv; exact hInvMsgShr k hinv hsh
  -- ackSharedImpliesShrSet
  · by_cases hki : k = i
    · subst hki
      simp [recvFetchState_c2dChan_self] at hack
      exact absurd hsh (by rw [hDirExcl]; decide)
    · rw [recvFetchState_c2dChan_ne s i k hki] at hack; exact hAckShShr k hack hsh
  -- invExclOnlyAtExNode
  · by_cases hki : k = i
    · subst hki; simp [recvFetchState_d2cChan_self] at hinv
    · rw [recvFetchState_d2cChan_ne s i k hki] at hinv; exact hInvExclEx k hinv hexcl
  -- ackExclOnlyAtExNode
  · by_cases hki : k = i
    · subst hki
      simp [recvFetchState_c2dChan_self] at hack
      exact hExNodeI.symm
    · rw [recvFetchState_c2dChan_ne s i k hki] at hack; exact hAckExclEx k hack hexcl
  -- ackImpliesDirNotUncached
  · by_cases hki : k = i
    · subst hki
      simp [recvFetchState_c2dChan_self] at hack
      rw [hDirExcl]; decide
    · rw [recvFetchState_c2dChan_ne s i k hki] at hack; exact hAckDirNotUnc k hack
  -- invImpliesDirNotUncached
  · by_cases hki : k = i
    · subst hki; simp [recvFetchState_d2cChan_self] at hinv
    · rw [recvFetchState_d2cChan_ne s i k hki] at hinv; exact hInvDirNotUnc k hinv
  -- ackImpliesD2cEmpty
  · by_cases hki : k = i
    · subst hki; simp [recvFetchState_d2cChan_self]
    · rw [recvFetchState_c2dChan_ne s i k hki] at hack
      rw [recvFetchState_d2cChan_ne s i k hki]; exact hAckD2cEmpty k hack
  -- gntSProp
  · by_cases hki : k = i
    · subst hki; simp [recvFetchState_d2cChan_self] at hgntS
    · rw [recvFetchState_d2cChan_ne s i k hki] at hgntS; exact hGntSProp k hgntS
  -- gntSImpliesDirShared
  · by_cases hki : k = i
    · subst hki; simp [recvFetchState_d2cChan_self] at hgntS
    · rw [recvFetchState_d2cChan_ne s i k hki] at hgntS; exact hGntSDirSh k hgntS
  -- invImpliesInvSetFalse
  · unfold invImpliesInvSetFalse; intro k hinv
    by_cases hki : k = i
    · subst hki; simp [recvFetchState_d2cChan_self] at hinv
    · rw [recvFetchState_d2cChan_ne s i k hki] at hinv; exact hInvInvSet k hinv

end DirectoryMSI
