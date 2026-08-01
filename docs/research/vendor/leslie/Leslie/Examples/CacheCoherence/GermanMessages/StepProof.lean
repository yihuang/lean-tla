import Leslie.Examples.CacheCoherence.GermanMessages.InitProof

namespace GermanMessages

/-! ## Step Preservation Proofs

    Proof that `fullStrongInvariant` is preserved by every action.
-/

-- ── Helper lemmas ─────────────────────────────────────────────────────────

private theorem strongInvariant_preserved_sendReqS
    {n : Nat} {s s' : MState n} {i : Fin n}
    (hs : strongInvariant n s)
    (hstep : (s.chan1 i).cmd = .empty ∧ (s.cache i).state = .I ∧
      s' = { s with chan1 := setFn s.chan1 i { (s.chan1 i) with cmd := .reqS } }) :
    strongInvariant n s' := by
  rcases hstep with ⟨_, _, rfl⟩
  simpa [strongInvariant, invariant, ctrlProp, dataProp, cacheInShrSet, grantDataProp,
    invAckDataProp, noExclusiveWhenFalse, invSetSubsetShrSet, exclusiveImpliesExGntd,
    noSharedWhenExGntd, chanImpliesShrSet, uniqueShrSetWhenExGntd] using hs

private theorem strongInvariant_preserved_sendReqE
    {n : Nat} {s s' : MState n} {i : Fin n}
    (hs : strongInvariant n s)
    (hstep : (s.chan1 i).cmd = .empty ∧ ((s.cache i).state = .I ∨ (s.cache i).state = .S) ∧
      s' = { s with chan1 := setFn s.chan1 i { (s.chan1 i) with cmd := .reqE } }) :
    strongInvariant n s' := by
  rcases hstep with ⟨_, _, rfl⟩
  simpa [strongInvariant, invariant, ctrlProp, dataProp, cacheInShrSet, grantDataProp,
    invAckDataProp, noExclusiveWhenFalse, invSetSubsetShrSet, exclusiveImpliesExGntd,
    noSharedWhenExGntd, chanImpliesShrSet, uniqueShrSetWhenExGntd] using hs

private theorem strongInvariant_preserved_recvReqS
    {n : Nat} {s s' : MState n} {i : Fin n}
    (hs : strongInvariant n s)
    (hstep : s.curCmd = .empty ∧ (s.chan1 i).cmd = .reqS ∧
      s' = { s with
              curCmd := .reqS
              curPtr := i
              chan1 := setFn s.chan1 i { (s.chan1 i) with cmd := .empty }
              invSet := fun j => s.shrSet j }) :
    strongInvariant n s' := by
  rcases hs with ⟨hinv, hcacheShr, hgrant, hinvAck, hnoExFalse, hinvSub, hexImpl, hnoSharedEx, hchanShr, huniqShr⟩
  rcases hstep with ⟨_, _, rfl⟩
  refine ⟨hinv, hcacheShr, hgrant, hinvAck, hnoExFalse, ?_, hexImpl, hnoSharedEx, hchanShr, huniqShr⟩
  intro j hj
  simpa using hj

private theorem strongInvariant_preserved_recvReqE
    {n : Nat} {s s' : MState n} {i : Fin n}
    (hs : strongInvariant n s)
    (hstep : s.curCmd = .empty ∧ (s.chan1 i).cmd = .reqE ∧
      s' = { s with
              curCmd := .reqE
              curPtr := i
              chan1 := setFn s.chan1 i { (s.chan1 i) with cmd := .empty }
              invSet := fun j => s.shrSet j }) :
    strongInvariant n s' := by
  rcases hs with ⟨hinv, hcacheShr, hgrant, hinvAck, hnoExFalse, hinvSub, hexImpl, hnoSharedEx, hchanShr, huniqShr⟩
  rcases hstep with ⟨_, _, rfl⟩
  refine ⟨hinv, hcacheShr, hgrant, hinvAck, hnoExFalse, ?_, hexImpl, hnoSharedEx, hchanShr, huniqShr⟩
  intro j hj
  simpa using hj

private theorem strongInvariant_preserved_sendInv
    {n : Nat} {s s' : MState n} {i : Fin n}
    (hs : strongInvariant n s)
    (hstep : (s.chan2 i).cmd = .empty ∧ s.invSet i = true ∧
      (s.curCmd = .reqE ∨ (s.curCmd = .reqS ∧ s.exGntd = true)) ∧
      s' = { s with
              chan2 := setFn s.chan2 i { (s.chan2 i) with cmd := .inv }
              invSet := setFn s.invSet i false }) :
    strongInvariant n s' := by
  rcases hs with ⟨hinv, hcacheShr, hgrant, hinvAck, hnoExFalse, hinvSub, hexImpl, hnoSharedEx, hchanShr, huniqShr⟩
  rcases hstep with ⟨hchan2i, hinvi, _, rfl⟩
  refine ⟨hinv, hcacheShr, ?_, hinvAck, ?_, ?_, ?_, ?_, ?_, huniqShr⟩
  · intro j hj
    by_cases hji : j = i
    · subst hji
      simp [setFn] at hj
    · have hj' : (s.chan2 j).cmd = .gntS ∨ (s.chan2 j).cmd = .gntE := by
        simpa [setFn, hji] using hj
      simpa [setFn, hji] using hgrant j hj'
  · intro hexFalse j
    by_cases hji : j = i
    · subst hji
      constructor
      · exact (hnoExFalse hexFalse j).1
      · simp [setFn]
    · simpa [setFn, hji] using hnoExFalse hexFalse j
  · intro j hj
    by_cases hji : j = i
    · subst hji
      simp [setFn] at hj
    · have := hinvSub j
      simp [setFn, hji] at hj ⊢
      exact this hj
  · intro j hj
    by_cases hji : j = i
    · subst hji
      have hj' : (s.cache j).state = .E ∨ (s.chan2 j).cmd = .gntE := by
        simp [setFn] at hj
        exact Or.inl hj
      exact hexImpl j hj'
    · have hj' : (s.cache j).state = .E ∨ (s.chan2 j).cmd = .gntE := by
        simpa [setFn, hji] using hj
      exact hexImpl j hj'
  · intro hexTrue j
    by_cases hji : j = i
    · subst hji
      constructor
      · exact (hnoSharedEx hexTrue j).1
      · simp [setFn]
    · simpa [setFn, hji] using hnoSharedEx hexTrue j
  · intro j hj
    by_cases hji : j = i
    · subst hji
      rcases hj with hj | hj | hj | hj
      · exact hinvSub j hinvi
      · simp [setFn] at hj
      · simp [setFn] at hj
      · have hj' : (s.chan3 j).cmd = .invAck := by simpa using hj
        exact hchanShr j (Or.inr <| Or.inr <| Or.inr hj')
    · have hj' : ((s.chan2 j).cmd = .inv) ∨
        ((s.chan2 j).cmd = .gntS) ∨
        ((s.chan2 j).cmd = .gntE) ∨
        ((s.chan3 j).cmd = .invAck) := by
          simpa [setFn, hji] using hj
      exact hchanShr j hj'

private theorem strongInvariant_preserved_sendGntS
    {n : Nat} {s s' : MState n} {i : Fin n}
    (hs : strongInvariant n s)
    (hstep : s.curCmd = .reqS ∧ s.curPtr = i ∧ (s.chan2 i).cmd = .empty ∧ s.exGntd = false ∧
      s' = { s with
              chan2 := setFn s.chan2 i { cmd := .gntS, data := s.memData }
              shrSet := setFn s.shrSet i true
              curCmd := .empty }) :
    strongInvariant n s' := by
  rcases hs with ⟨hinv, hcacheShr, hgrant, hinvAck, hnoExFalse, hinvSub, hexImpl, hnoSharedEx, hchanShr, huniqShr⟩
  rcases hstep with ⟨_, _, hchan2i, hexFalse, rfl⟩
  refine ⟨hinv, ?_, ?_, hinvAck, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    by_cases hji : j = i
    · subst hji
      simp [setFn]
    · simpa [setFn, hji] using hcacheShr j hj
  · intro j hj
    by_cases hji : j = i
    · subst hji
      simp [setFn]
      exact hinv.2.1 hexFalse
    · have hj' : (s.chan2 j).cmd = .gntS ∨ (s.chan2 j).cmd = .gntE := by
        simpa [setFn, hji] using hj
      simpa [setFn, hji] using hgrant j hj'
  · intro hexFalse' j
    by_cases hji : j = i
    · subst hji
      constructor
      · exact (hnoExFalse hexFalse j).1
      · simp [setFn]
    · simpa [setFn, hji] using hnoExFalse hexFalse j
  · intro j hj
    have := hinvSub j hj
    by_cases hji : j = i
    · subst hji
      simp [setFn]
    · simpa [setFn, hji] using this
  · intro j hj
    by_cases hji : j = i
    · subst hji
      have hnotE : (s.cache j).state ≠ .E := (hnoExFalse hexFalse j).1
      simp [setFn] at hj
      exact (hnotE hj).elim
    · have hj' : (s.cache j).state = .E ∨ (s.chan2 j).cmd = .gntE := by
        simpa [setFn, hji] using hj
      exact hexImpl j hj'
  · intro hexTrue
    simp [hexFalse] at hexTrue
  · intro j hj
    by_cases hji : j = i
    · subst hji
      rcases hj with hj | hj | hj | hj
      · simp [setFn] at hj
      · simp [setFn]
      · simp [setFn] at hj
      · simp [setFn]
    · have hj' : ((s.chan2 j).cmd = .inv) ∨
        ((s.chan2 j).cmd = .gntS) ∨
        ((s.chan2 j).cmd = .gntE) ∨
        ((s.chan3 j).cmd = .invAck) := by
          simpa [setFn, hji] using hj
      simpa [setFn, hji] using hchanShr j hj'
  · intro hexTrue
    simp [hexFalse] at hexTrue

private theorem cache_I_of_shr_false
    {n : Nat} {s : MState n}
    (hs : strongInvariant n s)
    (hshrFalse : ∀ j, s.shrSet j = false) :
    ∀ j, (s.cache j).state = .I := by
  rcases hs with ⟨_, hcacheShr, _, _, _, _, _, _, _, _⟩
  intro j
  by_contra hne
  have hjShr : s.shrSet j = true := hcacheShr j hne
  rw [hshrFalse j] at hjShr
  simp at hjShr

private theorem no_chan_msg_of_shr_false
    {n : Nat} {s : MState n}
    (hs : strongInvariant n s)
    (hshrFalse : ∀ j, s.shrSet j = false) :
    ∀ j, (s.chan2 j).cmd ≠ .inv ∧ (s.chan2 j).cmd ≠ .gntS ∧
      (s.chan2 j).cmd ≠ .gntE ∧ (s.chan3 j).cmd ≠ .invAck := by
  rcases hs with ⟨_, _, _, _, _, _, _, _, hchanShr, _⟩
  intro j
  constructor
  · intro h
    have hjShr : s.shrSet j = true := hchanShr j (Or.inl h)
    rw [hshrFalse j] at hjShr
    simp at hjShr
  constructor
  · intro h
    have hjShr : s.shrSet j = true := hchanShr j (Or.inr <| Or.inl h)
    rw [hshrFalse j] at hjShr
    simp at hjShr
  constructor
  · intro h
    have hjShr : s.shrSet j = true := hchanShr j (Or.inr <| Or.inr <| Or.inl h)
    rw [hshrFalse j] at hjShr
    simp at hjShr
  · intro h
    have hjShr : s.shrSet j = true := hchanShr j (Or.inr <| Or.inr <| Or.inr h)
    rw [hshrFalse j] at hjShr
    simp at hjShr

private theorem cache_I_of_unique_sharer
    {n : Nat} {s : MState n} {i j : Fin n}
    (hs : strongInvariant n s)
    (hexTrue : s.exGntd = true)
    (hshrI : s.shrSet i = true)
    (hij : i ≠ j) :
    (s.cache j).state = .I := by
  rcases hs with ⟨_, hcacheShr, _, _, _, _, _, _, _, huniqShr⟩
  have hjFalse : s.shrSet j = false := huniqShr hexTrue i j hij hshrI
  by_contra hjNotI
  have hjShr : s.shrSet j = true := hcacheShr j hjNotI
  rw [hjFalse] at hjShr
  simp at hjShr

private theorem no_shared_cache_of_exclusive
    {n : Nat} {s : MState n} {j : Fin n}
    (hs : strongInvariant n s)
    (hexTrue : s.exGntd = true) :
    (s.cache j).state ≠ .S := by
  rcases hs with ⟨_, _, _, _, _, _, _, hnoSharedEx, _, _⟩
  exact (hnoSharedEx hexTrue j).1

private theorem no_gntS_when_exclusive
    {n : Nat} {s : MState n} {j : Fin n}
    (hs : strongInvariant n s)
    (hexTrue : s.exGntd = true) :
    (s.chan2 j).cmd ≠ .gntS := by
  rcases hs with ⟨_, _, _, _, _, _, _, hnoSharedEx, _, _⟩
  exact (hnoSharedEx hexTrue j).2

private theorem strongInvariant_preserved_sendGntE
    {n : Nat} {s s' : MState n} {i : Fin n}
    (hs : strongInvariant n s)
    (hstep : s.curCmd = .reqE ∧ s.curPtr = i ∧ (s.chan2 i).cmd = .empty ∧ s.exGntd = false ∧
      (∀ j, s.shrSet j = false) ∧
      s' = { s with
              chan2 := setFn s.chan2 i { cmd := .gntE, data := s.memData }
              shrSet := setFn s.shrSet i true
              exGntd := true
              curCmd := .empty }) :
    strongInvariant n s' := by
  have hs0 := hs
  rcases hs with ⟨hinv, hcacheShr, hgrant, hinvAck, hnoExFalse, hinvSub, hexImpl, hnoSharedEx, hchanShr, huniqShr⟩
  rcases hstep with ⟨_, _, hchan2i, hexFalse, hshrFalse, rfl⟩
  have hcacheI := cache_I_of_shr_false hs0 hshrFalse
  have hnochan := no_chan_msg_of_shr_false hs0 hshrFalse
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · simpa [ctrlProp] using hinv.1
    · constructor
      · intro hfalse
        cases hfalse
      · intro j hjNotI
        have hjI : (s.cache j).state = .I := hcacheI j
        exact (hjNotI (by simpa [setFn] using hjI)).elim
  · intro j hjNotI
    have hjI : (s.cache j).state = .I := hcacheI j
    exact (hjNotI (by simpa [setFn] using hjI)).elim
  · intro j hjGrant
    by_cases hji : j = i
    · subst hji
      simp [setFn]
      exact hinv.2.1 hexFalse
    · have hjGrant' : (s.chan2 j).cmd = .gntS ∨ (s.chan2 j).cmd = .gntE := by
        simpa [setFn, hji] using hjGrant
      rcases hjGrant' with hjGntS | hjGntE
      · exact ((hnochan j).2.1 hjGntS).elim
      · exact ((hnochan j).2.2.1 hjGntE).elim
  · intro j hexTrue hjAck
    by_cases hji : j = i
    · subst hji
      have hjAck' : (s.chan3 j).cmd = .invAck := by simpa [setFn] using hjAck
      exact ((hnochan j).2.2.2 hjAck').elim
    · have hjAck' : (s.chan3 j).cmd = .invAck := by simpa [setFn, hji] using hjAck
      exact ((hnochan j).2.2.2 hjAck').elim
  · intro hfalse
    cases hfalse
  · intro j hjInv
    have hshr : s.shrSet j = true := hinvSub j hjInv
    rw [hshrFalse j] at hshr
    simp at hshr
  · intro j hjEx
    simp
  · intro hexTrue j
    constructor
    · have hjI : (s.cache j).state = .I := hcacheI j
      intro hjS
      cases hjS.symm.trans hjI
    · by_cases hji : j = i
      · subst hji
        simp [setFn]
      · intro hjGntS
        have hjGntS' : (s.chan2 j).cmd = .gntS := by simpa [setFn, hji] using hjGntS
        exact (hnochan j).2.1 hjGntS'
  · intro j hjMsg
    by_cases hji : j = i
    · subst hji
      rcases hjMsg with hjInv | hjRest
      · simp [setFn] at hjInv
      · rcases hjRest with hjGntS | hjRest
        · simp [setFn] at hjGntS
        · rcases hjRest with hjGntE | hjAck
          · simp [setFn]
          · have hjAck' : (s.chan3 j).cmd = .invAck := by simpa [setFn] using hjAck
            exact ((hnochan j).2.2.2 hjAck').elim
    · have hjMsg' : ((s.chan2 j).cmd = .inv) ∨
        ((s.chan2 j).cmd = .gntS) ∨
        ((s.chan2 j).cmd = .gntE) ∨
        ((s.chan3 j).cmd = .invAck) := by
          simpa [setFn, hji] using hjMsg
      rcases hjMsg' with hjInv | hjRest
      · exact ((hnochan j).1 hjInv).elim
      · rcases hjRest with hjGntS | hjRest
        · exact ((hnochan j).2.1 hjGntS).elim
        · rcases hjRest with hjGntE | hjAck
          · exact ((hnochan j).2.2.1 hjGntE).elim
          · exact ((hnochan j).2.2.2 hjAck).elim
  · intro hexTrue j k hjk hjShr
    by_cases hji : j = i
    · subst hji
      by_cases hki : k = j
      · exact False.elim (hjk hki.symm)
      · have hkFalse : s.shrSet k = false := hshrFalse k
        simp [setFn, hki, hkFalse]
    · have hjShr' : s.shrSet j = true := by simpa [setFn, hji] using hjShr
      rw [hshrFalse j] at hjShr'
      simp at hjShr'

private theorem strongInvariant_preserved_recvGntS
    {n : Nat} {s s' : MState n} {i : Fin n}
    (hs : strongInvariant n s)
    (hstep : (s.chan2 i).cmd = .gntS ∧
      s' = { s with
              cache := setFn s.cache i { state := .S, data := (s.chan2 i).data }
              chan2 := setFn s.chan2 i { (s.chan2 i) with cmd := .empty } }) :
    strongInvariant n s' := by
  rcases hs with ⟨hinv, hcacheShr, hgrant, hinvAck, hnoExFalse, hinvSub, hexImpl, hnoSharedEx, hchanShr, huniqShr⟩
  rcases hstep with ⟨hchan2i, rfl⟩
  have hexFalse : s.exGntd = false := by
    by_contra hexTrue
    exact (hnoSharedEx (by simpa using hexTrue) i).2 hchan2i
  have hshrI : s.shrSet i = true := hchanShr i (Or.inr <| Or.inl hchan2i)
  have hdataI : (s.chan2 i).data = s.auxData := hgrant i (Or.inl hchan2i)
  refine ⟨?_, ?_, ?_, hinvAck, ?_, hinvSub, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro j k hjk
      constructor
      · intro hjE
        by_cases hji : j = i
        · subst hji
          have : False := by
            simp [setFn] at hjE
          exact False.elim this
        · have hjE' : (s.cache j).state = .E := by simpa [setFn, hji] using hjE
          have : False := (hnoExFalse hexFalse j).1 hjE'
          exact False.elim this
      · intro hjS
        by_cases hji : j = i
        · subst hji
          by_cases hki : k = j
          · exact False.elim (hjk hki.symm)
          · have hkNotE : (s.cache k).state ≠ .E := (hnoExFalse hexFalse k).1
            cases hstate : (s.cache k).state
            · left
              simp [setFn, hki, hstate]
            · right
              simp [setFn, hki, hstate]
            · exfalso
              exact hkNotE hstate
        · have hjS' : (s.cache j).state = .S := by simpa [setFn, hji] using hjS
          have hkIS := (hinv.1 j k hjk).2 hjS'
          by_cases hki : k = i
          · subst hki
            right
            simp [setFn]
          · simpa [setFn, hki] using hkIS
    · constructor
      · intro hfalse
        exact hinv.2.1 hfalse
      · intro j hjNotI
        by_cases hji : j = i
        · subst hji
          simpa [setFn] using hdataI
        · have hjNotI' : (s.cache j).state ≠ .I := by simpa [setFn, hji] using hjNotI
          simpa [setFn, hji] using hinv.2.2 j hjNotI'
  · intro j hjNotI
    by_cases hji : j = i
    · subst hji
      simpa [setFn] using hshrI
    · have hjNotI' : (s.cache j).state ≠ .I := by simpa [setFn, hji] using hjNotI
      simpa [setFn, hji] using hcacheShr j hjNotI'
  · intro j hjGrant
    by_cases hji : j = i
    · subst hji
      simp [setFn] at hjGrant
    · have hjGrant' : (s.chan2 j).cmd = .gntS ∨ (s.chan2 j).cmd = .gntE := by
        simpa [setFn, hji] using hjGrant
      simpa [setFn, hji] using hgrant j hjGrant'
  · intro hfalse j
    by_cases hji : j = i
    · subst hji
      constructor
      · simp [setFn]
      · simp [setFn]
    · simpa [setFn, hji] using hnoExFalse hfalse j
  · intro j hjEx
    by_cases hji : j = i
    · subst hji
      rcases hjEx with hjE | hjGntE
      · simp [setFn] at hjE
      · simp [setFn] at hjGntE
    · have hjEx' : (s.cache j).state = .E ∨ (s.chan2 j).cmd = .gntE := by
        simpa [setFn, hji] using hjEx
      exact hexImpl j hjEx'
  · intro hexTrue
    simp [hexFalse] at hexTrue
  · intro j hjMsg
    by_cases hji : j = i
    · subst hji
      rcases hjMsg with hjInv | hjRest
      · simp [setFn] at hjInv
      · rcases hjRest with hjGntS | hjRest
        · simp [setFn] at hjGntS
        · rcases hjRest with hjGntE | hjAck
          · simp [setFn] at hjGntE
          · simpa [setFn] using hchanShr j (Or.inr <| Or.inr <| Or.inr hjAck)
    · have hjMsg' : ((s.chan2 j).cmd = .inv) ∨
        ((s.chan2 j).cmd = .gntS) ∨
        ((s.chan2 j).cmd = .gntE) ∨
        ((s.chan3 j).cmd = .invAck) := by
          simpa [setFn, hji] using hjMsg
      simpa [setFn, hji] using hchanShr j hjMsg'
  · intro hexTrue
    simp [hexFalse] at hexTrue

private theorem strongInvariant_preserved_recvGntE
    {n : Nat} {s : MState n} {i : Fin n}
    (hs : strongInvariant n s)
    (hstep : (s.chan2 i).cmd = .gntE) :
    strongInvariant n (recvGntEState s i) := by
  have hs0 := hs
  rcases hs with ⟨hinv, hcacheShr, hgrant, hinvAck, hnoExFalse, hinvSub, hexImpl, hnoSharedEx, hchanShr, huniqShr⟩
  have hexTrue : s.exGntd = true := hexImpl i (Or.inr hstep)
  have hshrI : s.shrSet i = true := hchanShr i (Or.inr <| Or.inr <| Or.inl hstep)
  have hdataI : (s.chan2 i).data = s.auxData := hgrant i (Or.inr hstep)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro j k hjk
      constructor
      · intro hjE
        by_cases hji : j = i
        · subst hji
          have hik : j ≠ k := hjk
          have hkI : (s.cache k).state = .I := cache_I_of_unique_sharer (i := j) hs0 hexTrue hshrI hik
          by_cases hki : k = j
          · exact False.elim (hjk hki.symm)
          · simpa [recvGntEState, hki] using hkI
        · have hij : i ≠ j := by
            intro hj
            exact hji hj.symm
          have hjI : (s.cache j).state = .I := cache_I_of_unique_sharer hs0 hexTrue hshrI hij
          have hjE' : (s.cache j).state = .E := by simpa [recvGntEState, hji] using hjE
          exact False.elim (by cases hjE'.symm.trans hjI)
      · intro hjS
        by_cases hji : j = i
        · subst hji
          simp [recvGntEState] at hjS
        · have hjS' : (s.cache j).state = .S := by simpa [recvGntEState, hji] using hjS
          exact ((no_shared_cache_of_exclusive (j := j) hs0 hexTrue) hjS').elim
    · constructor
      · intro hfalse
        have : s.exGntd = false := by simpa [recvGntEState] using hfalse
        exfalso
        rw [hexTrue] at this
        simp at this
      · intro j hjNotI
        by_cases hji : j = i
        · subst hji
          simp [recvGntEState, hdataI]
        · have hjNotI' : (s.cache j).state ≠ .I := by simpa [recvGntEState, hji] using hjNotI
          simpa [recvGntEState, hji] using hinv.2.2 j hjNotI'
  · intro j hjNotI
    by_cases hji : j = i
    · subst hji
      simpa using hshrI
    · have hjNotI' : (s.cache j).state ≠ .I := by simpa [recvGntEState, hji] using hjNotI
      simpa [recvGntEState, hji] using hcacheShr j hjNotI'
  · intro j hjGrant
    by_cases hji : j = i
    · subst hji
      simp [recvGntEState] at hjGrant
    · have hjGrant' : (s.chan2 j).cmd = .gntS ∨ (s.chan2 j).cmd = .gntE := by
        simpa [recvGntEState, hji] using hjGrant
      simpa [recvGntEState, hji] using hgrant j hjGrant'
  · intro j hexTrue' hjAck
    simpa [recvGntEState] using hinvAck j hexTrue' hjAck
  · intro hfalse
    have : s.exGntd = false := by simpa [recvGntEState] using hfalse
    exfalso
    rw [hexTrue] at this
    simp at this
  · simpa [recvGntEState]
  · intro j hjEx
    simpa [recvGntEState] using hexTrue
  · intro hexTrue' j
    constructor
    · by_cases hji : j = i
      · subst hji
        simp [recvGntEState]
      · intro hjS
        have hjS' : (s.cache j).state = .S := by simpa [recvGntEState, hji] using hjS
        exact (no_shared_cache_of_exclusive (j := j) hs0 hexTrue) hjS'
    · by_cases hji : j = i
      · subst hji
        simp [recvGntEState]
      · intro hjGntS
        have hjGntS' : (s.chan2 j).cmd = .gntS := by simpa [recvGntEState, hji] using hjGntS
        exact (no_gntS_when_exclusive (j := j) hs0 hexTrue) hjGntS'
  · intro j hjMsg
    by_cases hji : j = i
    · subst hji
      rcases hjMsg with hjInv | hjRest
      · simp [recvGntEState] at hjInv
      · rcases hjRest with hjGntS | hjRest
        · simp [recvGntEState] at hjGntS
        · rcases hjRest with hjGntE | hjAck
          · simp [recvGntEState] at hjGntE
          · simpa [recvGntEState] using hchanShr j (Or.inr <| Or.inr <| Or.inr hjAck)
    · have hjMsg' : ((s.chan2 j).cmd = .inv) ∨
        ((s.chan2 j).cmd = .gntS) ∨
        ((s.chan2 j).cmd = .gntE) ∨
        ((s.chan3 j).cmd = .invAck) := by
          simpa [recvGntEState, hji] using hjMsg
      simpa [recvGntEState, hji] using hchanShr j hjMsg'
  · simpa [recvGntEState] using huniqShr

private theorem strongInvariant_preserved_store_of_clean_self
    {n : Nat} {s : MState n} {i : Fin n} {d : Val}
    (hs : strongInvariant n s)
    (hcacheE : (s.cache i).state = .E)
    (hnoGntS : (s.chan2 i).cmd ≠ .gntS)
    (hnoGntE : (s.chan2 i).cmd ≠ .gntE)
    (hnoAck : (s.chan3 i).cmd ≠ .invAck) :
    strongInvariant n (storeState s i d) := by
  have hs0 := hs
  rcases hs with ⟨hinv, hcacheShr, hgrant, hinvAck, hnoExFalse, hinvSub, hexImpl, hnoSharedEx, hchanShr, huniqShr⟩
  have hexTrue : s.exGntd = true := hexImpl i (Or.inl hcacheE)
  have hcacheNotI : (s.cache i).state ≠ .I := by
    rw [hcacheE]
    simp
  have hshrI : s.shrSet i = true := hcacheShr i hcacheNotI
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro j k hjk
      constructor
      · intro hjE
        by_cases hji : j = i
        · subst hji
          have hik : j ≠ k := hjk
          have hkI : (s.cache k).state = .I := cache_I_of_unique_sharer (i := j) hs0 hexTrue hshrI hik
          by_cases hki : k = j
          · exact False.elim (hjk hki.symm)
          · simpa [storeState, hki] using hkI
        · have hij : i ≠ j := by
            intro hj
            exact hji hj.symm
          have hjI : (s.cache j).state = .I := cache_I_of_unique_sharer hs0 hexTrue hshrI hij
          have hjE' : (s.cache j).state = .E := by simpa [storeState, hji] using hjE
          exact False.elim (by cases hjE'.symm.trans hjI)
      · intro hjS
        by_cases hji : j = i
        · subst hji
          simp [storeState, hcacheE] at hjS
        · have hjS' : (s.cache j).state = .S := by simpa [storeState, hji] using hjS
          exact ((no_shared_cache_of_exclusive (j := j) hs0 hexTrue) hjS').elim
    · constructor
      · intro hfalse
        have : s.exGntd = false := by simpa [storeState] using hfalse
        exfalso
        rw [hexTrue] at this
        simp at this
      · intro j hjNotI
        by_cases hji : j = i
        · subst hji
          simp [storeState]
        · have hij : i ≠ j := by
            intro hj
            exact hji hj.symm
          have hjI : (s.cache j).state = .I := cache_I_of_unique_sharer hs0 hexTrue hshrI hij
          have hjNotI' : ((storeState s i d).cache j).state ≠ .I := hjNotI
          have : ((storeState s i d).cache j).state = .I := by simpa [storeState, hji] using hjI
          exact False.elim (hjNotI' this)
  · intro j hjNotI
    by_cases hji : j = i
    · subst hji
      simpa [storeState] using hshrI
    · have hij : i ≠ j := by
        intro hj
        exact hji hj.symm
      have hjI : (s.cache j).state = .I := cache_I_of_unique_sharer hs0 hexTrue hshrI hij
      have : ((storeState s i d).cache j).state = .I := by simpa [storeState, hji] using hjI
      exact False.elim (hjNotI this)
  · intro j hjGrant
    by_cases hji : j = i
    · subst hji
      rcases hjGrant with hjGntS | hjGntE
      · exact (hnoGntS hjGntS).elim
      · exact (hnoGntE hjGntE).elim
    · have hjGrant' : (s.chan2 j).cmd = .gntS ∨ (s.chan2 j).cmd = .gntE := by
        simpa [storeState, hji] using hjGrant
      have hjShr : s.shrSet j = true := by
        rcases hjGrant' with hjGntS | hjGntE
        · exact hchanShr j (Or.inr <| Or.inl hjGntS)
        · exact hchanShr j (Or.inr <| Or.inr <| Or.inl hjGntE)
      have hij : i ≠ j := by
        intro hj
        exact hji hj.symm
      have hjFalse : s.shrSet j = false := huniqShr hexTrue i j hij hshrI
      rw [hjFalse] at hjShr
      simp at hjShr
  · intro j hexTrue' hjAck
    by_cases hji : j = i
    · subst hji
      exact (hnoAck hjAck).elim
    · have hjAck' : (s.chan3 j).cmd = .invAck := by simpa [storeState, hji] using hjAck
      have hjShr : s.shrSet j = true := hchanShr j (Or.inr <| Or.inr <| Or.inr hjAck')
      have hij : i ≠ j := by
        intro hj
        exact hji hj.symm
      have hjFalse : s.shrSet j = false := huniqShr hexTrue i j hij hshrI
      rw [hjFalse] at hjShr
      simp at hjShr
  · intro hfalse
    have : s.exGntd = false := by simpa [storeState] using hfalse
    exfalso
    rw [hexTrue] at this
    simp at this
  · simpa [storeState]
  · intro j hjEx
    simpa [storeState] using hexTrue
  · intro hexTrue' j
    constructor
    · by_cases hji : j = i
      · subst hji
        simp [storeState, hcacheE]
      · intro hjS
        have hjS' : (s.cache j).state = .S := by simpa [storeState, hji] using hjS
        exact (no_shared_cache_of_exclusive (j := j) hs0 hexTrue) hjS'
    · by_cases hji : j = i
      · subst hji
        intro hjGntS
        exact (hnoGntS hjGntS).elim
      · intro hjGntS
        have hjGntS' : (s.chan2 j).cmd = .gntS := by simpa [storeState, hji] using hjGntS
        exact (no_gntS_when_exclusive (j := j) hs0 hexTrue) hjGntS'
  · intro j hjMsg
    by_cases hji : j = i
    · subst hji
      rcases hjMsg with hjInv | hjRest
      · simpa [storeState] using hchanShr j (Or.inl hjInv)
      · rcases hjRest with hjGntS | hjRest
        · exact (hnoGntS hjGntS).elim
        · rcases hjRest with hjGntE | hjAck
          · exact (hnoGntE hjGntE).elim
          · exact (hnoAck hjAck).elim
    · have hjMsg' : ((s.chan2 j).cmd = .inv) ∨
        ((s.chan2 j).cmd = .gntS) ∨
        ((s.chan2 j).cmd = .gntE) ∨
        ((s.chan3 j).cmd = .invAck) := by
          simpa [storeState, hji] using hjMsg
      simpa [storeState] using hchanShr j hjMsg'
  · simpa [storeState] using huniqShr

private theorem exGntd_false_of_inv_not_E
    {n : Nat} {s : MState n} {i : Fin n}
    (hs : strongInvariant n s)
    (hExWit : exGntdWitness n s)
    (hchan2i : (s.chan2 i).cmd = .inv)
    (hchan3i : (s.chan3 i).cmd = .empty)
    (hcacheNotE : (s.cache i).state ≠ .E) :
    s.exGntd = false := by
  rcases hs with ⟨_, hcacheShr, _, _, _, _, _, _, hchanShr, huniqShr⟩
  by_contra hexTrue
  simp at hexTrue
  have hshrI : s.shrSet i = true := hchanShr i (Or.inl hchan2i)
  obtain ⟨j, hj⟩ := hExWit hexTrue
  by_cases hji : j = i
  · subst hji
    rcases hj with hjE | hjGntE | hjAck
    · exact hcacheNotE hjE
    · simp [hchan2i] at hjGntE
    · simp [hchan3i] at hjAck
  · have hjShrFalse := huniqShr hexTrue i j (Ne.symm hji) hshrI
    rcases hj with hjE | hjGntE | hjAck
    · exact absurd (hcacheShr j (by intro h; cases hjE.symm.trans h))
        (by simp [hjShrFalse])
    · exact absurd (hchanShr j (Or.inr <| Or.inr <| Or.inl hjGntE))
        (by simp [hjShrFalse])
    · exact absurd (hchanShr j (Or.inr <| Or.inr <| Or.inr hjAck))
        (by simp [hjShrFalse])

private theorem strongInvariant_preserved_sendInvAck
    {n : Nat} {s : MState n} {i : Fin n}
    (hs : strongInvariant n s)
    (hExWit : exGntdWitness n s)
    (hstep : (s.chan2 i).cmd = .inv ∧ (s.chan3 i).cmd = .empty) :
    strongInvariant n (sendInvAckState s i) := by
  have hs0 := hs
  rcases hs with ⟨hinv, hcacheShr, hgrant, hinvAck, hnoExFalse, hinvSub, hexImpl, hnoSharedEx, hchanShr, huniqShr⟩
  rcases hstep with ⟨hchan2i, hchan3i⟩
  have hshrI : s.shrSet i = true := hchanShr i (Or.inl hchan2i)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- invariant (ctrlProp ∧ dataProp)
    refine ⟨?_, ?_⟩
    · intro j k hjk
      constructor
      · intro hjE
        by_cases hji : j = i
        · simp [hji, sendInvAckState] at hjE
        · by_cases hki : k = i
          · simp [hki, sendInvAckState]
          · have hjE' : (s.cache j).state = .E := by simpa [sendInvAckState, hji] using hjE
            simpa [sendInvAckState, hki] using (hinv.1 j k hjk).1 hjE'
      · intro hjS
        by_cases hji : j = i
        · simp [hji, sendInvAckState] at hjS
        · by_cases hki : k = i
          · left; simp [hki, sendInvAckState]
          · have hjS' : (s.cache j).state = .S := by simpa [sendInvAckState, hji] using hjS
            have hkIS := (hinv.1 j k hjk).2 hjS'
            rcases hkIS with hkI | hkS
            · left; simpa [sendInvAckState, hki] using hkI
            · right; simpa [sendInvAckState, hki] using hkS
    · constructor
      · simpa [sendInvAckState] using hinv.2.1
      · intro j hjNotI
        by_cases hji : j = i
        · simp [hji, sendInvAckState] at hjNotI
        · have hjNotI' : (s.cache j).state ≠ .I := by simpa [sendInvAckState, hji] using hjNotI
          simpa [sendInvAckState, hji] using hinv.2.2 j hjNotI'
  · -- cacheInShrSet
    intro j hjNotI
    by_cases hji : j = i
    · simp [hji, sendInvAckState] at hjNotI
    · exact hcacheShr j (by simpa [sendInvAckState, hji] using hjNotI)
  · -- grantDataProp
    intro j hjGrant
    by_cases hji : j = i
    · simp [hji, sendInvAckState] at hjGrant
    · have hjGrant' : (s.chan2 j).cmd = .gntS ∨ (s.chan2 j).cmd = .gntE := by
        simpa [sendInvAckState, hji] using hjGrant
      simpa [sendInvAckState, hji] using hgrant j hjGrant'
  · -- invAckDataProp
    intro j hexTrue hjAck
    by_cases hji : j = i
    · -- j = i: chan3[i] has data from conditional on cache[i]=E
      by_cases hcacheE : (s.cache i).state = .E
      · have hdata := hinv.2.2 i (by rw [hcacheE]; exact fun h => by simp at h)
        simp [hji, sendInvAckState, hcacheE, hdata]
      · -- cache[i]≠E → exGntd=false → contradiction with hexTrue
        have hexFalse := exGntd_false_of_inv_not_E hs0 hExWit hchan2i hchan3i hcacheE
        simp [sendInvAckState] at hexTrue
        rw [hexFalse] at hexTrue; simp at hexTrue
    · have hjAck' : (s.chan3 j).cmd = .invAck := by simpa [sendInvAckState, hji] using hjAck
      simp [sendInvAckState] at hexTrue
      simpa [sendInvAckState, hji] using hinvAck j hexTrue hjAck'
  · -- noExclusiveWhenFalse
    intro hexFalse j
    simp [sendInvAckState] at hexFalse
    by_cases hji : j = i
    · exact ⟨by simp [hji, sendInvAckState], by simp [hji, sendInvAckState]⟩
    · exact ⟨by simpa [sendInvAckState, hji] using (hnoExFalse hexFalse j).1,
             by simpa [sendInvAckState, hji] using (hnoExFalse hexFalse j).2⟩
  · -- invSetSubsetShrSet
    exact hinvSub
  · -- exclusiveImpliesExGntd
    intro j hjEx
    by_cases hji : j = i
    · rcases hjEx with hjE | hjGntE
      · simp [hji, sendInvAckState] at hjE
      · simp [hji, sendInvAckState] at hjGntE
    · have hjEx' : (s.cache j).state = .E ∨ (s.chan2 j).cmd = .gntE := by
        simpa [sendInvAckState, hji] using hjEx
      exact hexImpl j hjEx'
  · -- noSharedWhenExGntd
    intro hexTrue j
    simp [sendInvAckState] at hexTrue
    by_cases hji : j = i
    · exact ⟨by simp [hji, sendInvAckState], by simp [hji, sendInvAckState]⟩
    · simpa [sendInvAckState, hji] using hnoSharedEx hexTrue j
  · -- chanImpliesShrSet
    intro j hjMsg
    by_cases hji : j = i
    · rcases hjMsg with hjInv | hjGntS | hjGntE | hjAck
      · simp [hji, sendInvAckState] at hjInv
      · simp [hji, sendInvAckState] at hjGntS
      · simp [hji, sendInvAckState] at hjGntE
      · simpa [hji, sendInvAckState] using hshrI
    · have hjMsg' : ((s.chan2 j).cmd = .inv) ∨
        ((s.chan2 j).cmd = .gntS) ∨
        ((s.chan2 j).cmd = .gntE) ∨
        ((s.chan3 j).cmd = .invAck) := by
          simpa [sendInvAckState, hji] using hjMsg
      exact hchanShr j hjMsg'
  · -- uniqueShrSetWhenExGntd
    exact huniqShr

private theorem strongInvariant_preserved_recvInvAck
    {n : Nat} {s s' : MState n} {i : Fin n}
    (hs : strongInvariant n s)
    (hackI : invAckImpliesInvalid n s)
    (hInvSetClean : invSetImpliesClean n s)
    (hackClears : invAckClearsGrant n s)
    (hstep : (s.chan3 i).cmd = .invAck ∧ s.curCmd ≠ .empty ∧
      (((s.exGntd = true) ∧ s' = { s with
              chan3 := setFn s.chan3 i { (s.chan3 i) with cmd := .empty }
              shrSet := setFn s.shrSet i false
              exGntd := false
              memData := (s.chan3 i).data }) ∨
       ((s.exGntd = false) ∧ s' = { s with
              chan3 := setFn s.chan3 i { (s.chan3 i) with cmd := .empty }
              shrSet := setFn s.shrSet i false }))) :
    strongInvariant n s' := by
  rcases hs with ⟨hinv, hcacheShr, hgrant, hinvAck, hnoExFalse, hinvSub, hexImpl, hnoSharedEx,
    hchanShr, huniqShr⟩
  rcases hstep with ⟨hchan3i, _, hcases⟩
  have hcacheI : (s.cache i).state = .I := hackI i hchan3i
  have hshrI : s.shrSet i = true := hchanShr i (Or.inr <| Or.inr <| Or.inr hchan3i)
  have hchan2I : (s.chan2 i).cmd = .empty := hackClears i hchan3i
  rcases hcases with ⟨hexTrue, rfl⟩ | ⟨hexFalse, rfl⟩
  · have hnoE : ∀ j : Fin n, (s.cache j).state ≠ .E := by
      intro j hjE
      by_cases hji : j = i
      · subst hji
        simp [hcacheI] at hjE
      · have hjShr : s.shrSet j = true := hcacheShr j (by simp [hjE])
        have hjFalse := huniqShr hexTrue i j (Ne.symm hji) hshrI
        simp [hjShr] at hjFalse
    have hnoGntE : ∀ j : Fin n, (s.chan2 j).cmd ≠ .gntE := by
      intro j hjGntE
      by_cases hji : j = i
      · subst hji
        simp [hchan2I] at hjGntE
      · have hjShr : s.shrSet j = true := hchanShr j (Or.inr <| Or.inr <| Or.inl hjGntE)
        have hjFalse := huniqShr hexTrue i j (Ne.symm hji) hshrI
        simp [hjShr] at hjFalse
    have hnoS : ∀ j : Fin n, (s.cache j).state ≠ .S := fun j => (hnoSharedEx hexTrue j).1
    have hcacheI_all : ∀ j : Fin n, (s.cache j).state = .I := by
      intro j
      cases hstate : (s.cache j).state with
      | I => rfl
      | S => exact False.elim (hnoS j hstate)
      | E => exact False.elim (hnoE j hstate)
    have hmemAux : (s.chan3 i).data = s.auxData := hinvAck i hexTrue hchan3i
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro j k hjk
        constructor
        · intro hjE
          simp [hcacheI_all j] at hjE
        · intro hjS
          simp [hcacheI_all j] at hjS
      · constructor
        · intro _
          exact hmemAux
        · intro j hjNotI
          simp [hcacheI_all j] at hjNotI
    · intro j hjNotI
      simp [hcacheI_all j] at hjNotI
    · intro j hjGrant
      exact hgrant j hjGrant
    · intro j hexFalse' hjAck
      simp at hexFalse'
    · intro _ j
      exact ⟨hnoE j, hnoGntE j⟩
    · intro j hj
      by_cases hji : j = i
      · subst hji
        exfalso
        have : (s.chan3 j).cmd = .empty := hInvSetClean j hj
        simp [hchan3i] at this
      · simpa [setFn, hji] using hinvSub j hj
    · intro j hjEx
      rcases hjEx with hjE | hjGntE
      · exact False.elim (hnoE j hjE)
      · exact False.elim (hnoGntE j hjGntE)
    · intro hexFalse' j
      simp at hexFalse'
    · intro j hjMsg
      by_cases hji : j = i
      · subst hji
        rcases hjMsg with hjInv | hjRest
        · simp [hchan2I] at hjInv
        · rcases hjRest with hjGntS | hjRest
          · simp [hchan2I] at hjGntS
          · rcases hjRest with hjGntE | hjAck
            · simp [hchan2I] at hjGntE
            · simp at hjAck
      · have hjMsg' : ((s.chan2 j).cmd = .inv) ∨ ((s.chan2 j).cmd = .gntS) ∨
            ((s.chan2 j).cmd = .gntE) ∨ ((s.chan3 j).cmd = .invAck) := by
          rcases hjMsg with h | h | h | h
          · exact Or.inl <| by simpa [setFn, hji] using h
          · exact Or.inr <| Or.inl <| by simpa [setFn, hji] using h
          · exact Or.inr <| Or.inr <| Or.inl <| by simpa [setFn, hji] using h
          · exact Or.inr <| Or.inr <| Or.inr <| by simpa [setFn, hji] using h
        simpa [setFn, hji] using hchanShr j hjMsg'
    · intro hexFalse'
      simp at hexFalse'
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hinv
    · intro j hjNotI
      by_cases hji : j = i
      · subst hji
        simp [hcacheI] at hjNotI
      · simpa [setFn, hji] using hcacheShr j hjNotI
    · exact hgrant
    · intro j hexFalse' hjAck
      simp [hexFalse] at hexFalse'
    · intro _ j
      exact hnoExFalse hexFalse j
    · intro j hj
      by_cases hji : j = i
      · subst hji
        exfalso
        have : (s.chan3 j).cmd = .empty := hInvSetClean j hj
        simp [hchan3i] at this
      · simpa [setFn, hji] using hinvSub j hj
    · intro j hjEx
      rcases hjEx with hjE | hjGntE
      · exact False.elim ((hnoExFalse hexFalse j).1 hjE)
      · exact False.elim ((hnoExFalse hexFalse j).2 hjGntE)
    · intro hexTrue' j
      simp [hexFalse] at hexTrue'
    · intro j hjMsg
      by_cases hji : j = i
      · subst hji
        rcases hjMsg with hjInv | hjRest
        · simp [hchan2I] at hjInv
        · rcases hjRest with hjGntS | hjRest
          · simp [hchan2I] at hjGntS
          · rcases hjRest with hjGntE | hjAck
            · simp [hchan2I] at hjGntE
            · simp at hjAck
      · have hjMsg' : ((s.chan2 j).cmd = .inv) ∨ ((s.chan2 j).cmd = .gntS) ∨
            ((s.chan2 j).cmd = .gntE) ∨ ((s.chan3 j).cmd = .invAck) := by
          rcases hjMsg with h | h | h | h
          · exact Or.inl <| by simpa [setFn, hji] using h
          · exact Or.inr <| Or.inl <| by simpa [setFn, hji] using h
          · exact Or.inr <| Or.inr <| Or.inl <| by simpa [setFn, hji] using h
          · exact Or.inr <| Or.inr <| Or.inr <| by simpa [setFn, hji] using h
        simpa [setFn, hji] using hchanShr j hjMsg'
    · intro hexTrue'
      simp [hexFalse] at hexTrue'

private theorem strongInvariant_preserved_store
    {n : Nat} {s s' : MState n} {i : Fin n} {d : Val}
    (hs : strongInvariant n s)
    (hexcl : exclusiveSelfClean n s)
    (hstep : (s.cache i).state = .E ∧
      s' = { s with
              cache := setFn s.cache i { (s.cache i) with data := d }
              auxData := d }) :
    strongInvariant n s' := by
  rcases hstep with ⟨hcacheE, rfl⟩
  have ⟨hnoGntS, hnoGntE, hnoAck⟩ := hexcl i hcacheE
  exact strongInvariant_preserved_store_of_clean_self hs hcacheE hnoGntS hnoGntE hnoAck

-- ── Main preservation theorem ─────────────────────────────────────────────

theorem fullStrongInvariant_preserved
    {n : Nat} {s s' : MState n}
    (hs : fullStrongInvariant n s)
    (hstep : next n s s') :
    fullStrongInvariant n s' := by
  rcases hs with ⟨hstrong, hexcl, hgrantExcl, hExWit, hackI, hgntSExcl, hclean, hinvReason,
    hackClears, hinvSetClean, hinvClears, hchan3, hinvReq⟩
  obtain ⟨a, ha⟩ := hstep
  cases a with
  | sendReqS i =>
      -- Only chan1[i] changes; all auxiliary predicates don't mention chan1
      rcases ha with ⟨_, _, rfl⟩
      exact ⟨strongInvariant_preserved_sendReqS hstrong ⟨by assumption, by assumption, rfl⟩,
             hexcl, hgrantExcl, hExWit, hackI, hgntSExcl, hclean, hinvReason,
             hackClears, hinvSetClean, hinvClears, hchan3, hinvReq⟩
  | sendReqE i =>
      -- Only chan1[i] changes; all auxiliary predicates don't mention chan1
      rcases ha with ⟨_, _, rfl⟩
      exact ⟨strongInvariant_preserved_sendReqE hstrong ⟨by assumption, by assumption, rfl⟩,
             hexcl, hgrantExcl, hExWit, hackI, hgntSExcl, hclean, hinvReason,
             hackClears, hinvSetClean, hinvClears, hchan3, hinvReq⟩
  | recvReqS i =>
      -- chan1[i] cleared, curCmd=reqS, curPtr=i, invSet=shrSet
      -- chan2/chan3/cache/exGntd/shrSet unchanged
      rcases ha with ⟨hcmd, hchan1, rfl⟩
      have hno_inv : ∀ j : Fin n, (s.chan2 j).cmd ≠ .inv := fun j h =>
        absurd hcmd (hinvReq j h)
      refine ⟨strongInvariant_preserved_recvReqS hstrong ⟨hcmd, hchan1, rfl⟩,
             hexcl, hgrantExcl, hExWit, hackI, hgntSExcl, ?_, ?_, hackClears, ?_, ?_, hchan3, ?_⟩
      · intro hcond j
        rcases hcond with hemp | ⟨_, hexF⟩
        · simp at hemp
        · exact hclean (Or.inl hcmd) j
      · intro j hjInv; exact absurd hjInv (hno_inv j)
      · intro j hj
        rcases hchan3 j with h | h
        · exact h
        · exact absurd h (hclean (Or.inl hcmd) j)
      · intro j hjInv; exact absurd hjInv (hno_inv j)
      · intro j hjInv; exact absurd hjInv (hno_inv j)
  | recvReqE i =>
      -- Same structure as recvReqS
      rcases ha with ⟨hcmd, hchan1, rfl⟩
      have hno_inv : ∀ j : Fin n, (s.chan2 j).cmd ≠ .inv := fun j h =>
        absurd hcmd (hinvReq j h)
      refine ⟨strongInvariant_preserved_recvReqE hstrong ⟨hcmd, hchan1, rfl⟩,
             hexcl, hgrantExcl, hExWit, hackI, hgntSExcl, ?_, ?_, hackClears, ?_, ?_, hchan3, ?_⟩
      · intro hcond j
        rcases hcond with hemp | ⟨_, _⟩
        · simp at hemp
        · exact hclean (Or.inl hcmd) j
      · intro j hjInv; exact absurd hjInv (hno_inv j)
      · intro j hj
        rcases hchan3 j with h | h
        · exact h
        · exact absurd h (hclean (Or.inl hcmd) j)
      · intro j hjInv; exact absurd hjInv (hno_inv j)
      · intro j hjInv; exact absurd hjInv (hno_inv j)
  | sendInv i =>
      -- chan2[i] changes to inv, invSet[i] becomes false; cache/chan3/exGntd unchanged
      rcases ha with ⟨hchan2i, hinvi, hcurCmd, rfl⟩
      have hchan3i_empty : (s.chan3 i).cmd = .empty := hinvSetClean i hinvi
      refine ⟨strongInvariant_preserved_sendInv hstrong ⟨hchan2i, hinvi, hcurCmd, rfl⟩,
             ?_, ?_, ?_, hackI, ?_, hclean, ?_, ?_, ?_, ?_, hchan3, ?_⟩
      · -- exclusiveSelfClean: cache/chan3 unchanged; chan2[i]=inv (not gntS/gntE)
        intro j hjE
        by_cases hji : j = i
        · subst hji
          exact ⟨fun hc => (hexcl j hjE).1 (by simp [setFn] at hc),
                 fun hc => (hexcl j hjE).2.1 (by simp [setFn] at hc),
                 (hexcl j hjE).2.2⟩
        · exact ⟨fun hc => (hexcl j hjE).1 (by simpa [setFn, hji] using hc),
                 fun hc => (hexcl j hjE).2.1 (by simpa [setFn, hji] using hc),
                 (hexcl j hjE).2.2⟩
      · -- grantExcludesInvAck: chan2[i]=inv (not gntE); chan3 unchanged
        intro j hgntE
        by_cases hji : j = i
        · subst hji; simp [setFn] at hgntE
        · exact hgrantExcl j (by simpa [setFn, hji] using hgntE)
      · -- exGntdWitness: exGntd/cache/chan3 unchanged; witness from hExWit still works
        intro hexT
        obtain ⟨j, hj⟩ := hExWit hexT
        exact ⟨j, by
          rcases hj with hjE | hjGntE | hjAck
          · exact Or.inl hjE
          · by_cases hji : j = i
            · subst hji; simp [hchan2i] at hjGntE
            · exact Or.inr (Or.inl (by simpa [setFn, hji] using hjGntE))
          · exact Or.inr (Or.inr hjAck)⟩
      · -- gntSExcludesInvAck: chan2[i]=inv (not gntS); chan3 unchanged
        intro j hgntS hj3
        by_cases hji : j = i
        · subst hji; simp [setFn] at hgntS
        · exact hgntSExcl j (by simpa [setFn, hji] using hgntS) hj3
      · -- invReasonProp: chan2[i]=inv now; others unchanged
        intro j hjInv
        by_cases hji : j = i
        · subst hji
          rcases hcurCmd with hreqE | ⟨_, hexGntd⟩
          · right; exact hreqE
          · left; exact hexGntd
        · exact hinvReason j (by simpa [setFn, hji] using hjInv)
      · -- invAckClearsGrant: chan3 unchanged; chan2[i]=inv
        -- For j=i: chan3[i]=empty (from hchan3i_empty), so vacuous
        -- For j≠i: chan2[j] unchanged, so hackClears j works
        intro j hjAck
        by_cases hji : j = i
        · subst hji; rw [hchan3i_empty] at hjAck; exact absurd hjAck (by simp)
        · simpa [setFn, hji] using hackClears j hjAck
      · -- invSetImpliesClean: invSet[i]=false now; others unchanged
        intro j hj
        by_cases hji : j = i
        · subst hji; simp [setFn] at hj
        · exact hinvSetClean j (by simpa [setFn, hji] using hj)
      · -- invClearsInvSet: chan2[i]=inv → invSet[i]=false (we set it)
        intro j hjInv
        by_cases hji : j = i
        · subst hji; simp [setFn]
        · simpa [setFn, hji] using hinvClears j (by simpa [setFn, hji] using hjInv)
      · -- invRequiresNonEmpty: chan2[i]=inv; curCmd from guard is reqE or reqS (≠empty)
        intro j hjInv
        by_cases hji : j = i
        · subst hji
          rcases hcurCmd with hreqE | ⟨hreqS, _⟩
          · rw [hreqE]; simp
          · rw [hreqS]; simp
        · exact hinvReq j (by simpa [setFn, hji] using hjInv)
  | sendInvAck i =>
      -- sendInvAckState: cache[i]=I, chan2[i]=empty, chan3[i]=invAck
      rcases ha with ⟨hchan2i, hchan3i, rfl⟩
      have hInvFalse : s.invSet i = false := hinvClears i hchan2i
      have hcurNE : s.curCmd ≠ .empty := hinvReq i hchan2i
      have hReason := hinvReason i hchan2i
      refine ⟨strongInvariant_preserved_sendInvAck hstrong hExWit ⟨hchan2i, hchan3i⟩,
             ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- exclusiveSelfClean: cache[i]=I so j≠i; for j≠i cache/chan2/chan3 unchanged
        intro j hjE
        by_cases hji : j = i
        · subst hji; simp [sendInvAckState] at hjE
        · have hjE' : (s.cache j).state = .E := by simpa [sendInvAckState, hji] using hjE
          exact ⟨fun h => (hexcl j hjE').1 (by simpa [sendInvAckState, hji] using h),
                 fun h => (hexcl j hjE').2.1 (by simpa [sendInvAckState, hji] using h),
                 fun h => (hexcl j hjE').2.2 (by simpa [sendInvAckState, hji] using h)⟩
      · -- grantExcludesInvAck: chan2[i]=empty (not gntE)
        intro j hgntE
        by_cases hji : j = i
        · subst hji; simp [sendInvAckState] at hgntE
        · intro hj3
          exact hgrantExcl j (by simpa [sendInvAckState, hji] using hgntE)
            (by simpa [sendInvAckState, hji] using hj3)
      · -- exGntdWitness: exGntd unchanged; chan3[i]=invAck is witness
        intro hexTrue
        simp [sendInvAckState] at hexTrue
        exact ⟨i, Or.inr (Or.inr (by simp [sendInvAckState]))⟩
      · -- invAckImpliesInvalid: cache[i]=I; for j≠i cache/chan3 unchanged
        intro j hjAck
        by_cases hji : j = i
        · subst hji; simp [sendInvAckState]
        · have hjAck' : (s.chan3 j).cmd = .invAck := by simpa [sendInvAckState, hji] using hjAck
          simpa [sendInvAckState, hji] using hackI j hjAck'
      · -- gntSExcludesInvAck: chan2[i]=empty (not gntS)
        intro j hgntS
        by_cases hji : j = i
        · subst hji; simp [sendInvAckState] at hgntS
        · intro hj3
          exact hgntSExcl j (by simpa [sendInvAckState, hji] using hgntS)
            (by simpa [sendInvAckState, hji] using hj3)
      · -- cleanChannelWhenReady: curCmd unchanged ≠ empty; condition impossible
        intro hcond j
        rcases hcond with hemp | ⟨hreqS, hexF⟩
        · simp [sendInvAckState] at hemp; exact absurd hemp hcurNE
        · simp [sendInvAckState] at hexF hreqS
          rcases hReason with hexTrue | hreqE
          · rw [hexTrue] at hexF; simp at hexF
          · rw [hreqE] at hreqS; simp at hreqS
      · -- invReasonProp: chan2[i]=empty now
        intro j hjInv
        by_cases hji : j = i
        · subst hji; simp [sendInvAckState] at hjInv
        · exact hinvReason j (by simpa [sendInvAckState, hji] using hjInv)
      · -- invAckClearsGrant: chan3[i]=invAck and chan2[i]=empty
        intro j hjAck
        by_cases hji : j = i
        · subst hji; simp [sendInvAckState]
        · have hjAck' : (s.chan3 j).cmd = .invAck := by simpa [sendInvAckState, hji] using hjAck
          simpa [sendInvAckState, hji] using hackClears j hjAck'
      · -- invSetImpliesClean: invSet[i]=false; for j≠i chan3[j] unchanged
        intro j hj
        by_cases hji : j = i
        · subst hji; simp [sendInvAckState, hInvFalse] at hj
        · have hj3 : (s.chan3 j).cmd = .empty := hinvSetClean j (by simpa [sendInvAckState] using hj)
          simpa [sendInvAckState, hji] using hj3
      · -- invClearsInvSet: chan2[i]=empty now
        intro j hjInv
        by_cases hji : j = i
        · subst hji; simp [sendInvAckState] at hjInv
        · exact hinvClears j (by simpa [sendInvAckState, hji] using hjInv)
      · -- chan3IsInvAck: chan3[i]=invAck; others unchanged
        intro j
        by_cases hji : j = i
        · subst hji; right; simp [sendInvAckState]
        · simpa [sendInvAckState, hji] using hchan3 j
      · -- invRequiresNonEmpty: chan2[i]=empty now
        intro j hjInv
        by_cases hji : j = i
        · subst hji; simp [sendInvAckState] at hjInv
        · exact hinvReq j (by simpa [sendInvAckState, hji] using hjInv)
  | recvInvAck i =>
      -- chan3[i] cleared, shrSet[i]=false; exGntd may become false
      rcases ha with ⟨hchan3i, hcurNE, hcases⟩
      have hchan2I : (s.chan2 i).cmd = .empty := hackClears i hchan3i
      have hshrI : s.shrSet i = true :=
        hstrong.2.2.2.2.2.2.2.2.1 i (Or.inr (Or.inr (Or.inr hchan3i)))
      -- Handle both branches of exGntd
      rcases hcases with ⟨hexTrue, rfl⟩ | ⟨hexFalse, rfl⟩
      · -- exGntd becomes false branch
        -- Key: uniqueShrSetWhenExGntd + chanImpliesShrSet → chan3[j]=empty for all j≠i
        have hnoAckOther : ∀ j : Fin n, j ≠ i → (s.chan3 j).cmd = .empty := by
          intro j hji
          rcases hchan3 j with h | h
          · exact h
          · have hjShr := hstrong.2.2.2.2.2.2.2.2.1 j (Or.inr (Or.inr (Or.inr h)))
            have hjFalse := hstrong.2.2.2.2.2.2.2.2.2 hexTrue i j (Ne.symm hji) hshrI
            simp [hjFalse] at hjShr
        -- Key: chan2[j]=inv impossible in old state
        have hnoInvAll : ∀ j : Fin n, (s.chan2 j).cmd ≠ .inv := by
          intro j hjInv
          have hjShr := hstrong.2.2.2.2.2.2.2.2.1 j (Or.inl hjInv)
          by_cases hji : j = i
          · subst hji; rw [hchan2I] at hjInv; exact absurd hjInv (by simp)
          · have hjFalse := hstrong.2.2.2.2.2.2.2.2.2 hexTrue i j (Ne.symm hji) hshrI
            simp [hjFalse] at hjShr
        refine ⟨strongInvariant_preserved_recvInvAck hstrong hackI hinvSetClean hackClears
                 ⟨hchan3i, hcurNE, Or.inl ⟨hexTrue, rfl⟩⟩,
               ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · -- exclusiveSelfClean: chan3[i]=empty, cache/chan2 unchanged
          intro j hjE
          exact ⟨(hexcl j hjE).1,
                 (hexcl j hjE).2.1,
                 fun hj3 => by
                   by_cases hji : j = i
                   · subst hji; simp [setFn] at hj3
                   · exact (hexcl j hjE).2.2 (by simpa [setFn, hji] using hj3)⟩
        · -- grantExcludesInvAck: chan3[i]=empty
          intro j hgntE hj3
          by_cases hji : j = i
          · subst hji; simp [setFn] at hj3
          · exact hgrantExcl j hgntE (by simpa [setFn, hji] using hj3)
        · -- exGntdWitness: exGntd=false now, vacuous
          intro hexTrue'; simp at hexTrue'
        · -- invAckImpliesInvalid: chan3[i]=empty
          intro j hjAck
          by_cases hji : j = i
          · subst hji; simp [setFn] at hjAck
          · exact hackI j (by simpa [setFn, hji] using hjAck)
        · -- gntSExcludesInvAck: chan3[i]=empty
          intro j hgntS hj3
          by_cases hji : j = i
          · subst hji; simp [setFn] at hj3
          · exact hgntSExcl j hgntS (by simpa [setFn, hji] using hj3)
        · -- cleanChannelWhenReady: use hnoAckOther for j≠i
          intro hcond j
          by_cases hji : j = i
          · subst hji; simp [setFn]
          · intro h; simp [setFn, hji, hnoAckOther j hji] at h
        · -- invReasonProp: vacuous since chan2[j]≠inv for all j
          intro j hjInv; exact absurd hjInv (hnoInvAll j)
        · -- invAckClearsGrant: chan3[i]=empty
          intro j hjAck
          by_cases hji : j = i
          · subst hji; simp [setFn] at hjAck
          · exact hackClears j (by simpa [setFn, hji] using hjAck)
        · -- invSetImpliesClean: for j=i, goal is chan3[i]=empty (from simp [setFn])
          intro j hj
          by_cases hji : j = i
          · subst hji; simp [setFn]
          · have hj' : s.invSet j = true := by simpa using hj
            simpa [setFn, hji] using hinvSetClean j hj'
        · -- invClearsInvSet: chan2 unchanged
          simpa [setFn] using hinvClears
        · -- chan3IsInvAck: chan3[i]=empty
          intro j
          by_cases hji : j = i
          · subst hji; left; simp [setFn]
          · simpa [setFn, hji] using hchan3 j
        · -- invRequiresNonEmpty: chan2/curCmd unchanged; vacuous since chan2[j]≠inv
          intro j hjInv; exact absurd hjInv (hnoInvAll j)
      · -- exGntd stays false branch
        refine ⟨strongInvariant_preserved_recvInvAck hstrong hackI hinvSetClean hackClears
                 ⟨hchan3i, hcurNE, Or.inr ⟨hexFalse, rfl⟩⟩,
               ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · -- exclusiveSelfClean: chan3[i]=empty
          intro j hjE
          exact ⟨(hexcl j hjE).1,
                 (hexcl j hjE).2.1,
                 fun hj3 => by
                   by_cases hji : j = i
                   · subst hji; simp [setFn] at hj3
                   · exact (hexcl j hjE).2.2 (by simpa [setFn, hji] using hj3)⟩
        · -- grantExcludesInvAck
          intro j hgntE hj3
          by_cases hji : j = i
          · subst hji; simp [setFn] at hj3
          · exact hgrantExcl j hgntE (by simpa [setFn, hji] using hj3)
        · -- exGntdWitness: exGntd=false, vacuous
          intro hexTrue'; simp [hexFalse] at hexTrue'
        · -- invAckImpliesInvalid
          intro j hjAck
          by_cases hji : j = i
          · subst hji; simp [setFn] at hjAck
          · exact hackI j (by simpa [setFn, hji] using hjAck)
        · -- gntSExcludesInvAck
          intro j hgntS hj3
          by_cases hji : j = i
          · subst hji; simp [setFn] at hj3
          · exact hgntSExcl j hgntS (by simpa [setFn, hji] using hj3)
        · -- cleanChannelWhenReady: curCmd/exGntd unchanged in branch2; convert hcond
          intro hcond j
          by_cases hji : j = i
          · subst hji; simp [setFn]
          · have hcond' : s.curCmd = .empty ∨ (s.curCmd = .reqS ∧ s.exGntd = false) := by
              rcases hcond with hemp | ⟨hreqS, hexF⟩
              · exact Or.inl hemp
              · exact Or.inr ⟨hreqS, by simp [hexFalse]⟩
            simpa [setFn, hji] using hclean hcond' j
        · -- invReasonProp: chan2/exGntd/curCmd unchanged
          intro j hjInv
          exact hinvReason j hjInv
        · -- invAckClearsGrant: chan3[i]=empty
          intro j hjAck
          by_cases hji : j = i
          · subst hji; simp [setFn] at hjAck
          · exact hackClears j (by simpa [setFn, hji] using hjAck)
        · -- invSetImpliesClean: invSet unchanged; for j=i prove goal directly
          intro j hj
          by_cases hji : j = i
          · subst hji; simp [setFn]
          · have hj' : s.invSet j = true := by simpa using hj
            simpa [setFn, hji] using hinvSetClean j hj'
        · -- invClearsInvSet
          exact hinvClears
        · -- chan3IsInvAck
          intro j
          by_cases hji : j = i
          · subst hji; left; simp [setFn]
          · simpa [setFn, hji] using hchan3 j
        · -- invRequiresNonEmpty
          exact hinvReq
  | sendGntS i =>
      -- chan2[i]=gntS, shrSet[i]=true, curCmd=empty
      rcases ha with ⟨hcurS, hcurPtr, hchan2i, hexFalse, rfl⟩
      have hno_inv : ∀ j : Fin n, (s.chan2 j).cmd ≠ .inv := fun j hjInv => by
        rcases hinvReason j hjInv with hexT | hreqE
        · rw [hexT] at hexFalse; simp at hexFalse
        · rw [hreqE] at hcurS; simp at hcurS
      refine ⟨strongInvariant_preserved_sendGntS hstrong ⟨hcurS, hcurPtr, hchan2i, hexFalse, rfl⟩,
             ?_, ?_, ?_, hackI, ?_, ?_, ?_, ?_, hinvSetClean, ?_, hchan3, ?_⟩
      · -- exclusiveSelfClean: exGntd=false → no cache[j].state=E; vacuous
        intro j hjE
        exfalso
        have hnoE := (hstrong.2.2.2.2.1 hexFalse j).1
        by_cases hji : j = i
        · exact hnoE (by simpa [setFn] using hjE)
        · exact hnoE (by simpa [setFn, hji] using hjE)
      · -- grantExcludesInvAck: chan2[i]=gntS (not gntE)
        intro j hgntE
        by_cases hji : j = i
        · subst hji; simp [setFn] at hgntE
        · exact hgrantExcl j (by simpa [setFn, hji] using hgntE)
      · -- exGntdWitness: exGntd unchanged=false, vacuous
        intro hexTrue; simp [hexFalse] at hexTrue
      · -- gntSExcludesInvAck: chan2[i]=gntS; chan3 unchanged
        intro j hgntS
        by_cases hji : j = i
        · subst hji
          simp [setFn] at hgntS
          exact hclean (Or.inr ⟨hcurS, hexFalse⟩) j
        · exact hgntSExcl j (by simpa [setFn, hji] using hgntS)
      · -- cleanChannelWhenReady: curCmd=empty now; all chan3[j]≠invAck
        intro _ j
        exact hclean (Or.inr ⟨hcurS, hexFalse⟩) j
      · -- invReasonProp: chan2[i]=gntS (not inv); for j≠i chan2[j] unchanged; curCmd=empty so vacuous
        intro j hjInv
        by_cases hji : j = i
        · subst hji; simp [setFn] at hjInv
        · exact absurd (by simpa [setFn, hji] using hjInv) (hno_inv j)
      · -- invAckClearsGrant: chan2[i]=gntS; chan3[i]≠invAck (from hclean); for j≠i unchanged
        intro j hjAck
        by_cases hji : j = i
        · subst hji
          exact absurd hjAck (hclean (Or.inr ⟨hcurS, hexFalse⟩) j)
        · simpa [setFn, hji] using hackClears j hjAck
      · -- invClearsInvSet: chan2[i]=gntS≠inv; for j≠i chan2[j] unchanged
        intro j hjInv
        by_cases hji : j = i
        · subst hji; simp [setFn] at hjInv
        · simpa [setFn, hji] using hinvClears j (by simpa [setFn, hji] using hjInv)
      · -- invRequiresNonEmpty: chan2[j]≠inv for all j (shown above)
        intro j hjInv
        by_cases hji : j = i
        · subst hji; simp [setFn] at hjInv
        · exact absurd (by simpa [setFn, hji] using hjInv) (hno_inv j)
  | sendGntE i =>
      -- chan2[i]=gntE, shrSet[i]=true, exGntd=true, curCmd=empty
      rcases ha with ⟨hcurE, hcurPtr, hchan2i, hexFalse, hshrFalse, rfl⟩
      have hno_chan : ∀ j : Fin n, (s.chan2 j).cmd ≠ .inv ∧ (s.chan2 j).cmd ≠ .gntS ∧
          (s.chan2 j).cmd ≠ .gntE ∧ (s.chan3 j).cmd ≠ .invAck :=
        no_chan_msg_of_shr_false hstrong hshrFalse
      have hno_inv : ∀ j : Fin n, (s.chan2 j).cmd ≠ .inv := fun j => (hno_chan j).1
      have hno_ack : ∀ j : Fin n, (s.chan3 j).cmd ≠ .invAck := fun j => (hno_chan j).2.2.2
      refine ⟨strongInvariant_preserved_sendGntE hstrong ⟨hcurE, hcurPtr, hchan2i, hexFalse, hshrFalse, rfl⟩,
             ?_, ?_, ?_, hackI, ?_, ?_, ?_, ?_, hinvSetClean, ?_, hchan3, ?_⟩
      · -- exclusiveSelfClean: exGntd_old=false → no cache[j].state=E; vacuous
        intro j hjE
        exfalso
        have hnoE := (hstrong.2.2.2.2.1 hexFalse j).1
        by_cases hji : j = i
        · exact hnoE (by simpa [setFn] using hjE)
        · exact hnoE (by simpa [setFn, hji] using hjE)
      · -- grantExcludesInvAck: chan2[i]=gntE → chan3[i]≠invAck (from hno_ack)
        intro j hgntE
        by_cases hji : j = i
        · subst hji; exact hno_ack j
        · exact hgrantExcl j (by simpa [setFn, hji] using hgntE)
      · -- exGntdWitness: exGntd=true; chan2[i]=gntE is witness
        intro _; exact ⟨i, Or.inr (Or.inl (by simp [setFn]))⟩
      · -- gntSExcludesInvAck: chan2[i]=gntE (not gntS); for j≠i old chan2[j]≠gntS
        intro j hgntS
        by_cases hji : j = i
        · subst hji; simp [setFn] at hgntS
        · exact hgntSExcl j (by simpa [setFn, hji] using hgntS)
      · -- cleanChannelWhenReady: curCmd=empty now; chan3[j]≠invAck (from hno_ack)
        intro _ j
        exact hno_ack j
      · -- invReasonProp: chan2[j]≠inv for all j
        intro j hjInv
        by_cases hji : j = i
        · subst hji; simp [setFn] at hjInv
        · exact absurd (by simpa [setFn, hji] using hjInv) (hno_inv j)
      · -- invAckClearsGrant: chan3[j]≠invAck (from hno_ack); so vacuous
        intro j hjAck
        exact absurd hjAck (hno_ack j)
      · -- invClearsInvSet: chan2[i]=gntE≠inv; for j≠i chan2[j]≠inv (from hno_inv)
        intro j hjInv
        by_cases hji : j = i
        · subst hji; simp [setFn] at hjInv
        · exact hinvClears j (by simpa [setFn, hji] using hjInv)
      · -- invRequiresNonEmpty: chan2[j]≠inv for all j
        intro j hjInv
        by_cases hji : j = i
        · subst hji; simp [setFn] at hjInv
        · exact absurd (by simpa [setFn, hji] using hjInv) (hno_inv j)
  | recvGntS i =>
      -- cache[i]=S, chan2[i]=empty; chan3/exGntd/invSet/shrSet/curCmd unchanged
      rcases ha with ⟨hchan2i, rfl⟩
      have hexFalse : s.exGntd = false := by
        by_contra hexTrue
        simp at hexTrue
        exact (hstrong.2.2.2.2.2.2.2.1 hexTrue i).2 hchan2i
      refine ⟨strongInvariant_preserved_recvGntS hstrong ⟨hchan2i, rfl⟩,
             ?_, ?_, ?_, ?_, ?_, hclean, ?_, ?_, hinvSetClean, ?_, hchan3, ?_⟩
      · -- exclusiveSelfClean: cache[i]=S (not E) so j≠i case; chan3 unchanged
        intro j hjE
        by_cases hji : j = i
        · subst hji; simp [setFn] at hjE
        · have hjE' : (s.cache j).state = .E := by simpa [setFn, hji] using hjE
          exact ⟨fun h => (hexcl j hjE').1 (by simpa [setFn, hji] using h),
                 fun h => (hexcl j hjE').2.1 (by simpa [setFn, hji] using h),
                 (hexcl j hjE').2.2⟩
      · -- grantExcludesInvAck: chan2[i]=empty
        intro j hgntE
        by_cases hji : j = i
        · subst hji; simp [setFn] at hgntE
        · exact hgrantExcl j (by simpa [setFn, hji] using hgntE)
      · -- exGntdWitness: exGntd=false, vacuous
        intro hexTrue; simp [hexFalse] at hexTrue
      · -- invAckImpliesInvalid: chan3[i]=invAck impossible (from gntSExcludesInvAck)
        intro j hjAck
        by_cases hji : j = i
        · exact absurd (hji ▸ hjAck) (hgntSExcl i hchan2i)
        · simpa [setFn, hji] using hackI j (by simpa [setFn, hji] using hjAck)
      · -- gntSExcludesInvAck: chan2[i]=empty
        intro j hgntS
        by_cases hji : j = i
        · subst hji; simp [setFn] at hgntS
        · exact hgntSExcl j (by simpa [setFn, hji] using hgntS)
      · -- invReasonProp: chan2[i]=empty; for j≠i chan2[j] unchanged
        intro j hjInv
        by_cases hji : j = i
        · subst hji; simp [setFn] at hjInv
        · exact hinvReason j (by simpa [setFn, hji] using hjInv)
      · -- invAckClearsGrant: chan3 unchanged; chan2[i]=empty
        intro j hjAck
        by_cases hji : j = i
        · exact absurd (hji ▸ hjAck) (hgntSExcl i hchan2i)
        · simpa [setFn, hji] using hackClears j hjAck
      · -- invClearsInvSet: chan2[i]=empty (not inv)
        intro j hjInv
        by_cases hji : j = i
        · subst hji; simp [setFn] at hjInv
        · exact hinvClears j (by simpa [setFn, hji] using hjInv)
      · -- invRequiresNonEmpty: chan2[i]=empty; curCmd unchanged
        intro j hjInv
        by_cases hji : j = i
        · subst hji; simp [setFn] at hjInv
        · exact hinvReq j (by simpa [setFn, hji] using hjInv)
  | recvGntE i =>
      -- recvGntEState: cache[i]=E, chan2[i]=empty; exGntd/chan3/invSet/shrSet/curCmd unchanged
      rcases ha with ⟨hchan2i, rfl⟩
      have hexTrue : s.exGntd = true :=
        hstrong.2.2.2.2.2.2.1 i (Or.inr hchan2i)
      refine ⟨strongInvariant_preserved_recvGntE hstrong hchan2i,
             ?_, ?_, ?_, ?_, ?_, hclean, ?_, ?_, hinvSetClean, ?_, hchan3, ?_⟩
      · -- exclusiveSelfClean: cache[i]=E now; chan2[i]=empty; chan3[i] unchanged
        intro j hjE
        by_cases hji : j = i
        · refine ⟨by rw [hji]; simp [recvGntEState],
                  by rw [hji]; simp [recvGntEState],
                  fun h => hgrantExcl i hchan2i (by rw [hji] at h; simpa [recvGntEState] using h)⟩
        · have hjE' : (s.cache j).state = .E := by simpa [recvGntEState, hji] using hjE
          exact ⟨fun h => (hexcl j hjE').1 (by simpa [recvGntEState, hji] using h),
                 fun h => (hexcl j hjE').2.1 (by simpa [recvGntEState, hji] using h),
                 (hexcl j hjE').2.2⟩
      · -- grantExcludesInvAck: chan2[i]=empty
        intro j hgntE
        by_cases hji : j = i
        · subst hji; simp [recvGntEState] at hgntE
        · exact hgrantExcl j (by simpa [recvGntEState, hji] using hgntE)
      · -- exGntdWitness: exGntd=true; cache[i]=E is witness
        intro _; exact ⟨i, Or.inl (by simp [recvGntEState])⟩
      · -- invAckImpliesInvalid: chan3[i]≠invAck (from grantExcludesInvAck)
        intro j hjAck
        by_cases hji : j = i
        · exact absurd (hji ▸ hjAck) (hgrantExcl i hchan2i)
        · simpa [recvGntEState, hji] using hackI j (by simpa [recvGntEState, hji] using hjAck)
      · -- gntSExcludesInvAck: chan2[i]=empty
        intro j hgntS
        by_cases hji : j = i
        · subst hji; simp [recvGntEState] at hgntS
        · exact hgntSExcl j (by simpa [recvGntEState, hji] using hgntS)
      · -- invReasonProp: chan2[i]=empty (not inv); for j≠i chan2[j] unchanged
        intro j hjInv
        by_cases hji : j = i
        · subst hji; simp [recvGntEState] at hjInv
        · exact hinvReason j (by simpa [recvGntEState, hji] using hjInv)
      · -- invAckClearsGrant: chan3 unchanged; chan2[i]=empty
        intro j hjAck
        by_cases hji : j = i
        · exact absurd (hji ▸ hjAck) (hgrantExcl i hchan2i)
        · simpa [recvGntEState, hji] using hackClears j hjAck
      · -- invClearsInvSet: chan2[i]=empty (not inv)
        intro j hjInv
        by_cases hji : j = i
        · subst hji; simp [recvGntEState] at hjInv
        · exact hinvClears j (by simpa [recvGntEState, hji] using hjInv)
      · -- invRequiresNonEmpty: chan2[i]=empty; curCmd unchanged
        intro j hjInv
        by_cases hji : j = i
        · subst hji; simp [recvGntEState] at hjInv
        · exact hinvReq j (by simpa [recvGntEState, hji] using hjInv)
  | store i d =>
      -- storeState: cache[i].data=d, auxData=d; cache[i].state/chan2/chan3/exGntd unchanged
      rcases ha with ⟨hcacheE, rfl⟩
      have hexTrue : s.exGntd = true :=
        hstrong.2.2.2.2.2.2.1 i (Or.inl hcacheE)
      refine ⟨strongInvariant_preserved_store hstrong hexcl ⟨hcacheE, rfl⟩,
             ?_, hgrantExcl, ?_, ?_, hgntSExcl, hclean, hinvReason, hackClears, hinvSetClean,
             hinvClears, hchan3, hinvReq⟩
      · -- exclusiveSelfClean: cache state/chan2/chan3 unchanged (only cache[i].data changes)
        intro j hjE
        by_cases hji : j = i
        · subst hji
          exact hexcl j (by simpa [storeState] using hjE)
        · exact hexcl j (by simpa [storeState, hji] using hjE)
      · -- exGntdWitness: exGntd unchanged; cache[i].state=E still
        intro hexTrue'
        obtain ⟨j, hj⟩ := hExWit hexTrue
        exact ⟨j, by
          rcases hj with hjE | hjGntE | hjAck
          · by_cases hji : j = i
            · subst hji; left; simpa [storeState] using hjE
            · left; simpa [storeState, hji] using hjE
          · exact Or.inr (Or.inl hjGntE)
          · exact Or.inr (Or.inr hjAck)⟩
      · -- invAckImpliesInvalid: chan3 unchanged; cache state unchanged
        intro j hjAck
        have := hackI j hjAck
        by_cases hji : j = i
        · subst hji; simpa [storeState] using this
        · simpa [storeState, hji] using this

end GermanMessages
