import Leslie.Examples.CacheCoherence.DirectoryMSI.FrameLemmas

namespace DirectoryMSI

/-! ## StepTier3B — RecvGntS and RecvGntE

    Both actions consume a grant from d2cChan[i] and update cache[i].
    RecvGntS: cache[i] → {state:=S, data:=d2cChan[i].data}, d2cChan[i] → empty.
    RecvGntE: cache[i] → {state:=M, data:=d2cChan[i].data}, d2cChan[i] → empty.
-/

-- ── RecvGntS ────────────────────────────────────────────────────────────

theorem fullStrongInvariant_preserved_RecvGntS
    {n : Nat} {s s' : MState n} {i : Fin n}
    (h : fullStrongInvariant n s)
    (hact : RecvGntS s s' i) :
    fullStrongInvariant n s' := by
  obtain ⟨hd2cGntS, hs'⟩ := hact; subst hs'
  obtain ⟨⟨⟨hctrl, hdataF, hdataS⟩, hexclCons, hmImpl, hsShr, hexclExcl, huncInv,
    hgntSD, hgntED, hinvSub⟩,
    hackD, hcurNot, hexclNoDup, hshrNoE, hgntEImpl, hfetchImpl, hinvImpl, hackInv,
    hackInvSet, hinvSetCmd, hackCmdNotEmpty, hgetSAck,
    hInvAckExcl, hInvSetDirSh, hInvMsgShr, hAckShShr, hInvExclEx, hAckExclEx,
    hAckDirNotUnc, hInvDirNotUnc, hAckD2cEmpty, hGntSProp, hGntSDirSh, hInvInvSet⟩ := h
  -- Key derived facts
  have hGntSData := hgntSD i hd2cGntS  -- (s.d2cChan i).data = s.auxData
  have hDirShared := hGntSDirSh i hd2cGntS -- s.dirSt = .Shared
  -- No M caches: if cache[q]=M → mImpliesExclusive → Exclusive. But dirSt=Shared. Contradiction.
  have hNoM : ∀ k, (s.cache k).state ≠ .M := by
    intro k hk; have := (hmImpl k hk).1; rw [hDirShared] at this; exact absurd this (by decide)
  -- No gntE: sharedNoGntE → Shared → no gntE.
  have hNoGntE : ∀ k, (s.d2cChan k).cmd ≠ .gntE := hshrNoE hDirShared
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
    recvGntSState_c2dChan, recvGntSState_dirSt, recvGntSState_shrSet,
    recvGntSState_exNode, recvGntSState_curCmd, recvGntSState_curNode,
    recvGntSState_invSet, recvGntSState_memData, recvGntSState_auxData]
  refine ⟨⟨⟨
    -- ctrlProp
    fun p q hpq => ?_,
    -- dataProp fst: dirSt unchanged (Shared≠Exclusive)
    hdataF,
    -- dataProp snd: cache[k]≠I → data=auxData
    fun k hk => ?_⟩,
    -- exclusiveConsistent: Shared≠Exclusive → vacuous
    fun hex => absurd hex (by rw [hDirShared]; decide),
    -- mImpliesExclusive
    fun k hk => ?_,
    -- sImpliesShrSet
    fun k hk => ?_,
    -- exclusiveExcludesShared: Shared≠Exclusive → vacuous
    fun hex => absurd hex (by rw [hDirShared]; decide),
    -- uncachedMeansAllInvalid: Shared≠Uncached → vacuous
    fun hunc => absurd hunc (by rw [hDirShared]; decide),
    -- gntSDataProp: d2cChan[i]→empty
    fun k hgntS => ?_,
    -- gntEDataProp: no gntE
    fun k hgntE => ?_,
    -- invSetSubsetShrSet: invSet,shrSet unchanged
    hinvSub⟩,
    -- ackDataProp: c2dChan,cache(data only for non-I),dirSt,auxData
    fun k hack hcond => ?_,
    -- curNodeNotInInvSet: curCmd,dirSt,invSet,curNode unchanged
    hcurNot,
    -- exclusiveNoDuplicateGrant: Shared≠Exclusive → vacuous
    fun hex => absurd hex (by rw [hDirShared]; decide),
    -- sharedNoGntE: d2cChan[i]→empty, dirSt unchanged
    fun hsh k => ?_,
    -- gntEImpliesExclusive: d2cChan[i]→empty
    fun k hgntE => ?_,
    -- fetchImpliesCurCmdGetS: d2cChan[i]→empty
    fun k hfetch => ?_,
    -- invImpliesCurCmd: d2cChan[i]→empty
    fun k hk => ?_,
    -- ackImpliesInvalid: c2dChan,cache unchanged for j≠i. For j=i: cache→S≠I needs justification.
    fun k hack => ?_,
    -- ackImpliesInvSetFalse: c2dChan,invSet unchanged
    hackInvSet,
    -- invSetImpliesCurCmdGetM: invSet,curCmd unchanged
    hinvSetCmd,
    -- ackImpliesCurCmdNotEmpty: c2dChan,curCmd unchanged
    hackCmdNotEmpty,
    -- getSAckProp: c2dChan,curCmd,dirSt,exNode unchanged
    hgetSAck,
    -- invAckExclusive: d2cChan[i]→empty
    fun k hinv hack => ?_,
    -- invSetImpliesDirShared: invSet,dirSt unchanged
    hInvSetDirSh,
    -- invMsgImpliesShrSet: d2cChan[i]→empty, dirSt,shrSet unchanged
    fun k hinv hsh => ?_,
    -- ackSharedImpliesShrSet: c2dChan,dirSt,shrSet unchanged
    hAckShShr,
    -- invExclOnlyAtExNode: d2cChan[i]→empty, dirSt,exNode unchanged
    fun k hinv hexcl => ?_,
    -- ackExclOnlyAtExNode: c2dChan,dirSt,exNode unchanged
    hAckExclEx,
    -- ackImpliesDirNotUncached: c2dChan,dirSt unchanged
    hAckDirNotUnc,
    -- invImpliesDirNotUncached: d2cChan[i]→empty, dirSt unchanged
    fun k hinv => ?_,
    -- ackImpliesD2cEmpty: c2dChan unchanged, d2cChan[i]→empty
    fun k hack => ?_,
    -- gntSProp: d2cChan[i]→empty, shrSet,curCmd,curNode unchanged
    fun k hgntS => ?_,
    -- gntSImpliesDirShared: d2cChan[i]→empty, dirSt unchanged
    fun k hgntS => ?_,
    ?_⟩ -- invImpliesInvSetFalse
  · -- ctrlProp: ∀ p q, p ≠ q → (M at p → I at q) ∧ (S at p → ¬M at q)
    constructor
    · -- M at p → I at q
      intro hpM
      by_cases hpi : p = i
      · subst hpi; simp [recvGntSState_cache_state_self] at hpM
      · -- p≠i: cache'[p]=cache[p]=M. But hNoM says no M. Contradiction.
        rw [recvGntSState_cache_state_ne s i p hpi] at hpM
        exact absurd hpM (hNoM p)
    · -- S at p → ¬M at q
      intro hpS hqM
      by_cases hqi : q = i
      · subst hqi; simp [recvGntSState_cache_state_self] at hqM
      · -- q≠i: cache'[q]=cache[q]=M. But hNoM. Contradiction.
        rw [recvGntSState_cache_state_ne s i q hqi] at hqM
        exact absurd hqM (hNoM q)
  · -- dataProp snd: cache'[k]≠I → data=auxData
    by_cases hki : k = i
    · subst hki; simp [recvGntSState_cache_data_self, hGntSData]
    · rw [recvGntSState_cache_state_ne s i k hki] at hk
      rw [recvGntSState_cache_data_ne s i k hki]; exact hdataS k hk
  · -- mImpliesExclusive: cache'[k]=M → dirSt=Exclusive ∧ exNode=k
    by_cases hki : k = i
    · subst hki; simp [recvGntSState_cache_state_self] at hk
    · rw [recvGntSState_cache_state_ne s i k hki] at hk; exact hmImpl k hk
  · -- sImpliesShrSet: cache'[k]=S → shrSet[k]=true ∨ (getM∧curNode=k) ∨ gntE at k
    by_cases hki : k = i
    · -- k=i: cache'[i]=S. gntSProp: gntS at i → shrSet[i]=true ∨ (getM∧curNode=i).
      subst hki
      rcases hGntSProp _ hd2cGntS with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · -- k≠i: cache'[k]=cache[k], d2cChan'[k]=d2cChan[k]
      rw [recvGntSState_cache_state_ne s i k hki] at hk
      rcases hsShr k hk with h | h | hgntE
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (by rw [recvGntSState_d2cChan_ne s i k hki]; exact hgntE))
  · -- gntSDataProp: d2cChan'[k]=gntS → data=auxData
    by_cases hki : k = i
    · subst hki; simp [recvGntSState_d2cChan_self] at hgntS
    · rw [recvGntSState_d2cChan_ne s i k hki] at hgntS ⊢; exact hgntSD k hgntS
  · -- gntEDataProp: no gntE in pre
    by_cases hki : k = i
    · subst hki; simp [recvGntSState_d2cChan_self] at hgntE
    · rw [recvGntSState_d2cChan_ne s i k hki] at hgntE; exact absurd hgntE (hNoGntE k)
  · -- ackDataProp: c2dChan unchanged. cache data unchanged for non-I (j≠i unchanged; j=i: was I?).
    -- dirSt unchanged. auxData unchanged.
    -- hackD needs: hack → (cache[k].state=M ∨ dirSt=Exclusive) → data=auxData.
    -- Post: hack (c2dChan unchanged). (cache'[k].state=M ∨ dirSt=Exclusive).
    -- If dirSt=Exclusive: but dirSt=Shared. False from hcond.
    -- If cache'[k].state=M: k≠i (cache'[i]=S). cache[k]=M. But hNoM. Contradiction.
    rcases hcond with hM | hexcl
    · by_cases hki : k = i
      · subst hki; simp [recvGntSState_cache_state_self] at hM
      · rw [recvGntSState_cache_state_ne s i k hki] at hM; exact absurd hM (hNoM k)
    · exact absurd hexcl (by rw [hDirShared]; decide)
  · -- sharedNoGntE: Shared → ∀k, d2cChan'[k]≠gntE
    by_cases hki : k = i
    · subst hki; simp
    · rw [recvGntSState_d2cChan_ne s i k hki]; exact hshrNoE hsh k
  · -- gntEImpliesExclusive: d2cChan'[k]=gntE → dirSt=Exclusive ∧ exNode=k
    by_cases hki : k = i
    · subst hki; simp at hgntE
    · rw [recvGntSState_d2cChan_ne s i k hki] at hgntE; exact hgntEImpl k hgntE
  · -- fetchImpliesCurCmdGetS
    by_cases hki : k = i
    · subst hki; simp at hfetch
    · rw [recvGntSState_d2cChan_ne s i k hki] at hfetch; exact hfetchImpl k hfetch
  · -- invImpliesCurCmd
    by_cases hki : k = i
    · subst hki; simp at hk
    · rw [recvGntSState_d2cChan_ne s i k hki] at hk; exact hinvImpl k hk
  · -- ackImpliesInvalid: c2dChan[k]=ack → cache'[k]=I
    -- k=i: ackImpliesD2cEmpty → d2cChan[i]=empty. But d2cChan[i]=gntS≠empty. Contradiction.
    -- So k≠i if ack exists at i (but actually ack at k, not necessarily i).
    by_cases hki : k = i
    · subst hki
      -- c2dChan[i]=ack. ackImpliesD2cEmpty: d2cChan[i]=empty. But d2cChan[i]=gntS. Contradiction.
      exact absurd (hAckD2cEmpty k hack) (by rw [hd2cGntS]; decide)
    · rw [recvGntSState_cache_state_ne s i k hki]; exact hackInv k hack
  · -- invAckExclusive: d2cChan'[k]=inv → c2dChan[k]≠ack
    by_cases hki : k = i
    · subst hki; simp at hinv
    · rw [recvGntSState_d2cChan_ne s i k hki] at hinv; exact hInvAckExcl k hinv hack
  · -- invMsgImpliesShrSet: d2cChan'[k]=inv ∧ Shared → shrSet[k]
    by_cases hki : k = i
    · subst hki; simp at hinv
    · rw [recvGntSState_d2cChan_ne s i k hki] at hinv; exact hInvMsgShr k hinv hsh
  · -- invExclOnlyAtExNode: d2cChan'[k]=inv ∧ Exclusive → k=exNode
    by_cases hki : k = i
    · subst hki; simp at hinv
    · rw [recvGntSState_d2cChan_ne s i k hki] at hinv; exact hInvExclEx k hinv hexcl
  · -- invImpliesDirNotUncached: d2cChan'[k]=inv → dirSt≠Uncached
    by_cases hki : k = i
    · subst hki; simp at hinv
    · rw [recvGntSState_d2cChan_ne s i k hki] at hinv; exact hInvDirNotUnc k hinv
  · -- ackImpliesD2cEmpty: c2dChan unchanged, d2cChan[i]→empty
    by_cases hki : k = i
    · subst hki; simp
    · rw [recvGntSState_d2cChan_ne s i k hki]; exact hAckD2cEmpty k hack
  · -- gntSProp: d2cChan[i]→empty, shrSet,curCmd,curNode unchanged
    by_cases hki : k = i
    · subst hki; simp at hgntS
    · rw [recvGntSState_d2cChan_ne s i k hki] at hgntS; exact hGntSProp k hgntS
  · -- gntSImpliesDirShared: d2cChan[i]→empty, dirSt unchanged
    by_cases hki : k = i
    · subst hki; simp at hgntS
    · rw [recvGntSState_d2cChan_ne s i k hki] at hgntS; exact hGntSDirSh k hgntS
  · -- invImpliesInvSetFalse
    unfold invImpliesInvSetFalse; intro k hinv
    by_cases hki : k = i
    · subst hki; simp at hinv
    · rw [recvGntSState_d2cChan_ne s i k hki] at hinv; exact hInvInvSet k hinv

-- ── RecvGntE ────────────────────────────────────────────────────────────

theorem fullStrongInvariant_preserved_RecvGntE
    {n : Nat} {s s' : MState n} {i : Fin n}
    (h : fullStrongInvariant n s)
    (hact : RecvGntE s s' i) :
    fullStrongInvariant n s' := by
  obtain ⟨hd2cGntE, hs'⟩ := hact; subst hs'
  obtain ⟨⟨⟨hctrl, hdataF, hdataS⟩, hexclCons, hmImpl, hsShr, hexclExcl, huncInv,
    hgntSD, hgntED, hinvSub⟩,
    hackD, hcurNot, hexclNoDup, hshrNoE, hgntEImpl, hfetchImpl, hinvImpl, hackInv,
    hackInvSet, hinvSetCmd, hackCmdNotEmpty, hgetSAck,
    hInvAckExcl, hInvSetDirSh, hInvMsgShr, hAckShShr, hInvExclEx, hAckExclEx,
    hAckDirNotUnc, hInvDirNotUnc, hAckD2cEmpty, hGntSProp, hGntSDirSh, hInvInvSet⟩ := h
  -- Key derived facts
  have ⟨hDirExcl, hExNodeI⟩ := hgntEImpl i hd2cGntE
  -- hDirExcl : s.dirSt = .Exclusive, hExNodeI : s.exNode = i
  have hGntEData := hgntED i hd2cGntE -- (s.d2cChan i).data = s.auxData
  -- All other caches are I (from exclusiveConsistent)
  have hOtherI : ∀ k, k ≠ i → (s.cache k).state = .I := by
    intro k hki; exact (hexclCons hDirExcl).2 k (by rw [hExNodeI]; exact hki)
  -- No gntE at other nodes (exclusiveNoDuplicateGrant)
  have hNoOtherGntE : ∀ k, k ≠ i → (s.d2cChan k).cmd ≠ .gntE :=
    fun k hki => hexclNoDup hDirExcl k (by rw [hExNodeI]; exact hki)
  -- d2cChan[i]=gntE, so no ack at i (invAckExclusive contrapositive: if d2cChan=gntE≠inv)
  -- Actually: ackImpliesD2cEmpty: ack at k → d2cChan[k]=empty. d2cChan[i]=gntE≠empty. So no ack at i.
  have hNoAckI : (s.c2dChan i).cmd ≠ .ack := by
    intro hack; exact absurd (hAckD2cEmpty i hack) (by rw [hd2cGntE]; decide)
  -- No gntS anywhere: gntSImpliesDirShared → Shared. But dirSt=Exclusive. Contradiction.
  have hNoGntS : ∀ k, (s.d2cChan k).cmd ≠ .gntS := by
    intro k hgntS; exact absurd (hGntSDirSh k hgntS) (by rw [hDirExcl]; decide)
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
    recvGntEState_c2dChan, recvGntEState_dirSt, recvGntEState_shrSet,
    recvGntEState_exNode, recvGntEState_curCmd, recvGntEState_curNode,
    recvGntEState_invSet, recvGntEState_memData, recvGntEState_auxData]
  refine ⟨⟨⟨?_, hdataF, ?_⟩, ?_, ?_, ?_, ?_,
    fun hunc => absurd hunc (by rw [hDirExcl]; decide), ?_, ?_, hinvSub⟩,
    ?_, hcurNot, ?_, fun hsh => absurd hsh (by rw [hDirExcl]; decide),
    ?_, ?_, ?_, ?_, hackInvSet, hinvSetCmd, hackCmdNotEmpty, hgetSAck,
    ?_, hInvSetDirSh, ?_, hAckShShr, ?_, hAckExclEx, hAckDirNotUnc, ?_, ?_, ?_, ?_, ?_⟩
  -- ctrlProp
  · intro k q hpq; constructor
    · intro hpM
      by_cases hpi : k = i
      · have hne : q ≠ i := hpi ▸ (Ne.symm hpq)
        rw [recvGntEState_cache_state_ne s i q hne]; exact hOtherI q hne
      · rw [recvGntEState_cache_state_ne s i k hpi] at hpM
        by_cases hqi : q = i
        · subst hqi; have := (hmImpl k hpM).2; rw [hExNodeI] at this; exact absurd this.symm hpi
        · rw [recvGntEState_cache_state_ne s i q hqi]; exact (hctrl k q hpq).1 hpM
    · intro hpS hqM
      by_cases hqi : q = i
      · have hne : k ≠ i := fun h => hpq (h ▸ hqi ▸ rfl)
        rw [recvGntEState_cache_state_ne s i k hne] at hpS
        exact absurd (hOtherI k hne) (by rw [hpS]; decide)
      · rw [recvGntEState_cache_state_ne s i q hqi] at hqM
        by_cases hpi : k = i
        · subst hpi; simp [recvGntEState_cache_state_self] at hpS
        · rw [recvGntEState_cache_state_ne s i k hpi] at hpS; exact (hctrl k q hpq).2 hpS hqM
  -- dataProp snd
  · intro k hk
    by_cases hki : k = i
    · subst hki; simp [recvGntEState_cache_data_self, hGntEData]
    · rw [recvGntEState_cache_state_ne s i k hki] at hk
      rw [recvGntEState_cache_data_ne s i k hki]; exact hdataS k hk
  -- exclusiveConsistent
  · intro _; constructor
    · rw [hExNodeI]; exact Or.inl (by simp [recvGntEState_cache_state_self])
    · intro j hji; rw [hExNodeI] at hji
      rw [recvGntEState_cache_state_ne s i j hji]; exact hOtherI j hji
  -- mImpliesExclusive
  · intro k hk
    by_cases hki : k = i
    · subst hki; exact ⟨hDirExcl, hExNodeI⟩
    · rw [recvGntEState_cache_state_ne s i k hki] at hk; exact hmImpl k hk
  -- sImpliesShrSet
  · intro k hk
    by_cases hki : k = i
    · subst hki; simp [recvGntEState_cache_state_self] at hk
    · rw [recvGntEState_cache_state_ne s i k hki] at hk
      rcases hsShr k hk with h | h | hgntE
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (by rw [recvGntEState_d2cChan_ne s i k hki]; exact hgntE))
  -- exclusiveExcludesShared
  · intro _ k hkS
    by_cases hki : k = i
    · subst hki; simp [recvGntEState_cache_state_self] at hkS
    · rw [recvGntEState_cache_state_ne s i k hki] at hkS
      rw [recvGntEState_d2cChan_ne s i k hki]; exact hexclExcl hDirExcl k hkS
  -- gntSDataProp: no gntS
  · intro k hgntS
    by_cases hki : k = i
    · subst hki; simp [recvGntEState_d2cChan_self] at hgntS
    · rw [recvGntEState_d2cChan_ne s i k hki] at hgntS; exact absurd hgntS (hNoGntS k)
  -- gntEDataProp
  · intro k hgntE
    by_cases hki : k = i
    · subst hki; simp [recvGntEState_d2cChan_self] at hgntE
    · rw [recvGntEState_d2cChan_ne s i k hki] at hgntE ⊢; exact hgntED k hgntE
  -- ackDataProp
  · intro k hack hcond
    by_cases hki : k = i
    · subst hki; exact absurd hack hNoAckI
    · exact hackD k hack (Or.inr hDirExcl)
  -- exclusiveNoDuplicateGrant
  · intro _ k hne
    by_cases hki : k = i
    · subst hki; simp [recvGntEState_d2cChan_self]
    · rw [recvGntEState_d2cChan_ne s i k hki]; exact hexclNoDup hDirExcl k hne
  -- gntEImpliesExclusive
  · intro k hgntE
    by_cases hki : k = i
    · subst hki; simp [recvGntEState_d2cChan_self] at hgntE
    · rw [recvGntEState_d2cChan_ne s i k hki] at hgntE; exact hgntEImpl k hgntE
  -- fetchImpliesCurCmdGetS
  · intro k hfetch
    by_cases hki : k = i
    · subst hki; simp [recvGntEState_d2cChan_self] at hfetch
    · rw [recvGntEState_d2cChan_ne s i k hki] at hfetch; exact hfetchImpl k hfetch
  -- invImpliesCurCmd
  · intro k hinvK
    by_cases hki : k = i
    · subst hki; simp [recvGntEState_d2cChan_self] at hinvK
    · rw [recvGntEState_d2cChan_ne s i k hki] at hinvK; exact hinvImpl k hinvK
  -- ackImpliesInvalid
  · intro k hack
    by_cases hki : k = i
    · subst hki; exact absurd hack hNoAckI
    · rw [recvGntEState_cache_state_ne s i k hki]; exact hackInv k hack
  -- invAckExclusive
  · intro k hinvK hack
    by_cases hki : k = i
    · subst hki; simp [recvGntEState_d2cChan_self] at hinvK
    · rw [recvGntEState_d2cChan_ne s i k hki] at hinvK; exact hInvAckExcl k hinvK hack
  -- invMsgImpliesShrSet
  · intro k hinvK hsh
    by_cases hki : k = i
    · subst hki; simp [recvGntEState_d2cChan_self] at hinvK
    · rw [recvGntEState_d2cChan_ne s i k hki] at hinvK; exact hInvMsgShr k hinvK hsh
  -- invExclOnlyAtExNode
  · intro k hinvK hexcl
    by_cases hki : k = i
    · subst hki; simp [recvGntEState_d2cChan_self] at hinvK
    · rw [recvGntEState_d2cChan_ne s i k hki] at hinvK; exact hInvExclEx k hinvK hexcl
  -- invImpliesDirNotUncached
  · intro k hinvK
    by_cases hki : k = i
    · subst hki; simp [recvGntEState_d2cChan_self] at hinvK
    · rw [recvGntEState_d2cChan_ne s i k hki] at hinvK; exact hInvDirNotUnc k hinvK
  -- ackImpliesD2cEmpty
  · intro k hack
    by_cases hki : k = i
    · subst hki; simp [recvGntEState_d2cChan_self]
    · rw [recvGntEState_d2cChan_ne s i k hki]; exact hAckD2cEmpty k hack
  -- gntSProp
  · intro k hgntS
    by_cases hki : k = i
    · subst hki; simp [recvGntEState_d2cChan_self] at hgntS
    · rw [recvGntEState_d2cChan_ne s i k hki] at hgntS; exact absurd hgntS (hNoGntS k)
  -- gntSImpliesDirShared
  · intro k hgntS
    by_cases hki : k = i
    · subst hki; simp [recvGntEState_d2cChan_self] at hgntS
    · rw [recvGntEState_d2cChan_ne s i k hki] at hgntS; exact hGntSDirSh k hgntS
  -- invImpliesInvSetFalse
  · unfold invImpliesInvSetFalse; intro k hinvK
    by_cases hki : k = i
    · subst hki; simp [recvGntEState_d2cChan_self] at hinvK
    · rw [recvGntEState_d2cChan_ne s i k hki] at hinvK; exact hInvInvSet k hinvK

end DirectoryMSI
