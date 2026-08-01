import Leslie.Examples.CacheCoherence.DirectoryMSI.StepTier1
import Leslie.Examples.CacheCoherence.DirectoryMSI.StepTier2
import Leslie.Examples.CacheCoherence.DirectoryMSI.StepTier3A
import Leslie.Examples.CacheCoherence.DirectoryMSI.StepTier3B
import Leslie.Examples.CacheCoherence.DirectoryMSI.StepTier3C

namespace DirectoryMSI

/-! ## Step Preservation Proofs

    Proof that `fullStrongInvariant` is preserved by every action in the
    directory-based MSI cache coherence protocol.

    Tier 1 proofs (RecvGetS_Shared, RecvGetM_Shared, RecvAck_GetM_Shared,
    SendGntS_AfterFetch) are in StepTier1.lean.
-/

-- Action 1: SendGetS only modifies reqChan[i], no invariant reads reqChan.
private theorem step_SendGetS {n : Nat} {s s' : MState n}
    (h : fullStrongInvariant n s) (hact : ∃ i, SendGetS s s' i) :
    fullStrongInvariant n s' := by
  obtain ⟨_i, _hreq, _hcache, hs'⟩ := hact; subst hs'; exact h

-- Action 2: SendGetM only modifies reqChan[i], no invariant reads reqChan.
private theorem step_SendGetM {n : Nat} {s s' : MState n}
    (h : fullStrongInvariant n s) (hact : ∃ i, SendGetM s s' i) :
    fullStrongInvariant n s' := by
  obtain ⟨_i, _hreq, _hcache, hs'⟩ := hact; subst hs'; exact h

-- Action 3: RecvGetS_Uncached
private theorem step_RecvGetS_Uncached {n : Nat} {s s' : MState n}
    (h : fullStrongInvariant n s) (hact : ∃ i, RecvGetS_Uncached s s' i) :
    fullStrongInvariant n s' := by
  obtain ⟨i, _hreq, hcurCmd, hdirSt, _hd2c, hs'⟩ := hact; subst hs'
  obtain ⟨⟨⟨hctrl, hdataF, hdataS⟩, _hexclCons, _hmImpl, hsShr, _hexclExcl, huncInv,
    hgntSD, hgntED, hinvSub⟩,
    hackD, _hcurNot, _hexclNoDup, _hshrNoE, hgntEImpl, hfetchImpl, hinvImpl, hackInv,
    _hackInvSet, _hinvSetCmd, hackCmdNotEmpty, _hgetSAck,
    _hInvAckExcl, _hInvSetDirSh, _hInvMsgShr, _hAckShShr, _hInvExclEx, _hAckExclEx,
    _hAckDirNotUnc, _hInvDirNotUnc, _hAckD2cEmpty, _hGntSProp, _hGntSDirSh, _hInvInvSet⟩ := h
  have huncDat : s.memData = s.auxData := hdataF (by rw [hdirSt]; decide)
  have hAllI : ∀ k : Fin n, (s.cache k).state = .I := huncInv hdirSt
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
    recvGetS_UncachedState_cache, recvGetS_UncachedState_c2dChan,
    recvGetS_UncachedState_dirSt, recvGetS_UncachedState_exNode,
    recvGetS_UncachedState_curCmd, recvGetS_UncachedState_curNode,
    recvGetS_UncachedState_invSet, recvGetS_UncachedState_memData,
    recvGetS_UncachedState_auxData]
  refine ⟨⟨⟨hctrl, fun _ => huncDat, hdataS⟩,
    fun hex => absurd hex (by decide),
    fun j hjM => absurd (hAllI j) (by rw [hjM]; decide),
    fun j hj => ?_,
    fun hex _ _ => absurd hex (by decide),
    fun hex => absurd hex (by decide),
    fun k hgntS => ?_, fun k hgntE => ?_, fun k hk => ?_⟩,
    fun k hk hcond => hackD k hk (hcond.imp id (fun h => absurd h (by decide))),
    fun hgetM _ => absurd hgetM (by rw [hcurCmd]; decide),
    fun hex => absurd hex (by decide),
    fun _ k => ?_,
    fun k hgntE => ?_, fun k hfetch => ?_, fun k hk => ?_, hackInv,
    fun k hack => absurd (hackCmdNotEmpty k hack) (by rw [hcurCmd]; decide),
    fun k hk => absurd (_hinvSetCmd k hk) (by rw [hcurCmd]; decide),
    fun k hack => absurd (hackCmdNotEmpty k hack) (by rw [hcurCmd]; decide),
    fun k hack hgetS => absurd hgetS (by rw [hcurCmd]; decide), -- getSAckProp: curCmd=empty≠getS
    fun k hinv => ?_, -- invAckExclusive: d2cChan changes
    fun k hk => absurd (_hInvSetDirSh k hk) (by rw [hdirSt]; decide), -- invSetImpliesDirShared
    fun k hinv hsh => ?_, -- invMsgImpliesShrSet
    fun k hack _ => absurd (hackCmdNotEmpty k hack) (by rw [hcurCmd]; decide), -- no acks
    fun k hinv hexcl => absurd hexcl (by decide), -- invExclOnlyAtExNode: Shared≠Exclusive
    fun k hack hexcl => absurd hexcl (by decide), -- ackExclOnlyAtExNode: Shared≠Exclusive
    fun k hack => absurd (hackCmdNotEmpty k hack) (by rw [hcurCmd]; decide), -- ackImpliesDirNotUncached
    fun k hinv => ?_, -- invImpliesDirNotUncached: d2cChan changes
    fun k hack => absurd (hackCmdNotEmpty k hack) (by rw [hcurCmd]; decide), -- ackImpliesD2cEmpty: no acks
    fun k hgntS => ?_, -- gntSProp: d2cChan[i]→gntS, shrSet[i]→true
    fun k hgntS => ?_, -- gntSImpliesDirShared: d2cChan[i]→gntS, dirSt'=Shared
    ?_⟩ -- invImpliesInvSetFalse
  · -- sImpliesShrSet (weakened)
    by_cases hji : j = i
    · subst hji; exact Or.inl (by simp [recvGetS_UncachedState_shrSet_self])
    · exact absurd (hAllI j) (by rw [hj]; decide)
  · by_cases hki : k = i
    · subst hki; simp only [recvGetS_UncachedState_d2cChan_self]; exact huncDat
    · simp only [recvGetS_UncachedState_d2cChan_ne s i k hki] at hgntS ⊢; exact hgntSD k hgntS
  · by_cases hki : k = i
    · subst hki; simp [recvGetS_UncachedState_d2cChan_self] at hgntE
    · simp only [recvGetS_UncachedState_d2cChan_ne s i k hki] at hgntE ⊢; exact hgntED k hgntE
  · by_cases hki : k = i
    · subst hki; simp [recvGetS_UncachedState_shrSet_self]
    · rw [recvGetS_UncachedState_shrSet_ne s i k hki]; exact hinvSub k hk
  · by_cases hki : k = i
    · subst hki; simp [recvGetS_UncachedState_d2cChan_self]
    · rw [recvGetS_UncachedState_d2cChan_ne s i k hki]
      intro hgntE; exact absurd (hgntEImpl k hgntE).1 (by rw [hdirSt]; decide)
  · by_cases hki : k = i
    · subst hki; simp [recvGetS_UncachedState_d2cChan_self] at hgntE
    · simp only [recvGetS_UncachedState_d2cChan_ne s i k hki] at hgntE ⊢
      exact absurd (hgntEImpl k hgntE).1 (by rw [hdirSt]; decide)
  · by_cases hki : k = i
    · subst hki; simp [recvGetS_UncachedState_d2cChan_self] at hfetch
    · rw [recvGetS_UncachedState_d2cChan_ne s i k hki] at hfetch
      exact absurd (hfetchImpl k hfetch).2.1 (by rw [hdirSt]; decide)
  · by_cases hki : k = i
    · subst hki; simp [recvGetS_UncachedState_d2cChan_self] at hk
    · rw [recvGetS_UncachedState_d2cChan_ne s i k hki] at hk; exact hinvImpl k hk
  · -- invAckExclusive
    by_cases hki : k = i
    · subst hki; simp [recvGetS_UncachedState_d2cChan_self] at hinv
    · rw [recvGetS_UncachedState_d2cChan_ne s i k hki] at hinv; exact _hInvAckExcl k hinv
  · -- invMsgImpliesShrSet: no invs (curCmd=empty → invImpliesCurCmd→getM, contradiction)
    by_cases hki : k = i
    · subst hki; simp [recvGetS_UncachedState_d2cChan_self] at hinv
    · rw [recvGetS_UncachedState_d2cChan_ne s i k hki] at hinv
      exact absurd (hinvImpl k hinv) (by rw [hcurCmd]; decide)
  · -- invImpliesDirNotUncached: dirSt'=Shared≠Uncached
    intro hunc; exact absurd hunc (by decide)
  · -- gntSProp: d2cChan[i]→gntS, shrSet[i]→true
    by_cases hki : k = i
    · subst hki; exact Or.inl (by simp [recvGetS_UncachedState_shrSet_self])
    · rw [recvGetS_UncachedState_d2cChan_ne s i k hki] at hgntS
      rw [recvGetS_UncachedState_shrSet_ne s i k hki]
      -- curCmd=empty → gntSProp pre gives shrSet=true ∨ (empty=getM, false) → shrSet=true
      rcases _hGntSProp k hgntS with h | ⟨hc, _⟩
      · exact Or.inl h
      · exact absurd hc (by rw [hcurCmd]; decide)
  · -- gntSImpliesDirShared: dirSt'=Shared. d2cChan[i]→gntS.
    -- k=i: dirSt'=Shared ✓. k≠i: pre gntS → pre dirSt=Shared (if hGntSDirSh available).
    -- But pre dirSt=Uncached. gntS at k≠i pre → _hGntSDirSh → Shared. Uncached≠Shared. Contradiction.
    by_cases hki : k = i
    · subst hki; simp [recvGetS_UncachedState_dirSt]
    · rw [recvGetS_UncachedState_d2cChan_ne s i k hki] at hgntS
      exact absurd (_hGntSDirSh k hgntS) (by rw [hdirSt]; decide)
  · -- invImpliesInvSetFalse
    unfold invImpliesInvSetFalse; intro k hinv
    by_cases hki : k = i
    · subst hki; simp [recvGetS_UncachedState_d2cChan_self] at hinv
    · rw [recvGetS_UncachedState_d2cChan_ne s i k hki] at hinv; exact _hInvInvSet k hinv

-- Main theorem: dispatch to per-action cases

theorem fullStrongInvariant_preserved (n : Nat) (s s' : MState n)
    (h : fullStrongInvariant n s) (hstep : next n s s') :
    fullStrongInvariant n s' := by
  unfold next at hstep
  rcases hstep with
    ⟨i, hact⟩ | ⟨i, hact⟩ | ⟨i, hact⟩ | ⟨i, hact⟩ | ⟨i, hact⟩ |
    ⟨i, hact⟩ | ⟨i, hact⟩ | ⟨i, hact⟩ | ⟨j, hact⟩ | hact |
    ⟨i, hact⟩ | ⟨i, hact⟩ | ⟨i, hact⟩ | ⟨i, hact⟩ |
    ⟨j, hact⟩ | ⟨j, hact⟩ | hact | ⟨j, hact⟩ | hact
  · exact step_SendGetS h ⟨i, hact⟩
  · exact step_SendGetM h ⟨i, hact⟩
  · exact step_RecvGetS_Uncached h ⟨i, hact⟩
  · exact fullStrongInvariant_preserved_RecvGetS_Shared h ⟨i, hact⟩
  · exact fullStrongInvariant_preserved_RecvGetS_Exclusive h ⟨i, hact⟩
  · exact fullStrongInvariant_preserved_RecvGetM_Uncached h ⟨i, hact⟩
  · exact fullStrongInvariant_preserved_RecvGetM_Shared h ⟨i, hact⟩
  · exact fullStrongInvariant_preserved_RecvGetM_Exclusive h ⟨i, hact⟩
  · exact fullStrongInvariant_preserved_SendInv h ⟨j, hact⟩
  · exact fullStrongInvariant_preserved_SendGntE_AfterShared h hact
  · exact fullStrongInvariant_preserved_RecvGntS h hact
  · exact fullStrongInvariant_preserved_RecvGntE h hact
  · exact fullStrongInvariant_preserved_RecvInv h hact
  · exact fullStrongInvariant_preserved_RecvFetch h hact
  · exact fullStrongInvariant_preserved_RecvAck_GetM_Shared h ⟨j, hact⟩
  · exact fullStrongInvariant_preserved_RecvAck_GetM_Exclusive h hact
  · exact fullStrongInvariant_preserved_SendGntE_AfterExclusive h hact
  · exact fullStrongInvariant_preserved_RecvAck_GetS h hact
  · exact fullStrongInvariant_preserved_SendGntS_AfterFetch h hact

end DirectoryMSI
