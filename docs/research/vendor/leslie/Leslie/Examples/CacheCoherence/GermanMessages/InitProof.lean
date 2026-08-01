import Leslie.Examples.CacheCoherence.GermanMessages.Invariant

namespace GermanMessages

/-! ## Init Proofs

    Proof that initial states satisfy `fullStrongInvariant`.
-/

theorem germanMessages_init_ctrlProp (n : Nat) :
    ∀ s : MState n, init n s → ctrlProp n s := by
  intro s hinit i j hij
  rcases hinit with ⟨hcache, _, _, _, _, _, _, _, _, _⟩
  constructor
  · intro hiE
    have hj := hcache j
    simp [hj]
  · intro hiS
    left
    have hj := hcache j
    simp [hj]

theorem germanMessages_init_dataProp (n : Nat) :
    ∀ s : MState n, init n s → dataProp n s := by
  intro s hinit
  rcases hinit with ⟨hcache, _, _, _, _, _, hex, _, hmem, haux⟩
  constructor
  · intro _
    rw [hmem, haux]
  · intro i hi
    have hc := hcache i
    simp [hc] at hi

theorem germanMessages_init_invariant (n : Nat) :
    ∀ s : MState n, init n s → invariant n s := by
  intro s hinit
  exact ⟨germanMessages_init_ctrlProp n s hinit, germanMessages_init_dataProp n s hinit⟩

theorem germanMessages_init_strongInvariant (n : Nat) :
    ∀ s : MState n, init n s → strongInvariant n s := by
  intro s hinit
  have hinit0 := hinit
  rcases hinit with ⟨hcache, _, hchan2, hchan3, hInv, hShr, hEx, _, _, hAux⟩
  refine ⟨germanMessages_init_invariant n s hinit0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have := hcache i
    simp [this] at hi
  · intro i hi
    have := hchan2 i
    simp [this] at hi
  · intro i hex hi
    simp [hEx] at hex
  · intro hex i
    have hc := hcache i
    have h2 := hchan2 i
    constructor <;> simp [hc, h2]
  · intro i hi
    simp [hInv i] at hi
  · intro i hi
    have hc := hcache i
    have h2 := hchan2 i
    simp [hc, h2] at hi
  · intro hex i
    simp [hEx] at hex
  · intro i hi
    have h2 := hchan2 i
    have h3 := hchan3 i
    simp [h2, h3] at hi
  · intro hex i j hij hi
    simp [hEx] at hex

theorem germanMessages_init_exclusiveSelfClean (n : Nat) :
    ∀ s : MState n, init n s → exclusiveSelfClean n s := by
  intro s hinit i hiE
  rcases hinit with ⟨hcache, _, hchan2, hchan3, _, _, _, _, _, _⟩
  have hc := hcache i
  simp [hc] at hiE

private theorem init_grantExcludesInvAck (n : Nat) :
    ∀ s : MState n, init n s → grantExcludesInvAck n s := by
  intro s hinit i hgntE
  rcases hinit with ⟨_, _, hchan2, _, _, _, _, _, _, _⟩
  simp [hchan2 i] at hgntE

private theorem init_exGntdWitness (n : Nat) :
    ∀ s : MState n, init n s → exGntdWitness n s := by
  intro s hinit hexTrue
  rcases hinit with ⟨_, _, _, _, _, _, hexGntd, _, _, _⟩
  simp [hexGntd] at hexTrue

private theorem init_invAckImpliesInvalid (n : Nat) :
    ∀ s : MState n, init n s → invAckImpliesInvalid n s := by
  intro s hinit i hack
  rcases hinit with ⟨_, _, _, hchan3, _, _, _, _, _, _⟩
  simp [hchan3 i] at hack

private theorem init_gntSExcludesInvAck (n : Nat) :
    ∀ s : MState n, init n s → gntSExcludesInvAck n s := by
  intro s hinit i hgntS
  rcases hinit with ⟨_, _, hchan2, _, _, _, _, _, _, _⟩
  simp [hchan2 i] at hgntS

private theorem init_cleanChannelWhenReady (n : Nat) :
    ∀ s : MState n, init n s → cleanChannelWhenReady n s := by
  intro s hinit _ i
  rcases hinit with ⟨_, _, _, hchan3, _, _, _, _, _, _⟩
  simp [hchan3 i]

private theorem init_invReasonProp (n : Nat) :
    ∀ s : MState n, init n s → invReasonProp n s := by
  intro s hinit i hinv
  rcases hinit with ⟨_, _, hchan2, _, _, _, _, _, _, _⟩
  simp [hchan2 i] at hinv

private theorem init_invAckClearsGrant (n : Nat) :
    ∀ s : MState n, init n s → invAckClearsGrant n s := by
  intro s hinit i hack
  rcases hinit with ⟨_, _, _, hchan3, _, _, _, _, _, _⟩
  simp [hchan3 i] at hack

private theorem init_invSetImpliesClean (n : Nat) :
    ∀ s : MState n, init n s → invSetImpliesClean n s := by
  intro s hinit i hinvSet
  rcases hinit with ⟨_, _, _, hchan3, hInvSet, _, _, _, _, _⟩
  simp [hInvSet i] at hinvSet

private theorem init_invClearsInvSet (n : Nat) :
    ∀ s : MState n, init n s → invClearsInvSet n s := by
  intro s hinit i hinv
  rcases hinit with ⟨_, _, hchan2, _, _, _, _, _, _, _⟩
  simp [hchan2 i] at hinv

private theorem init_chan3IsInvAck (n : Nat) :
    ∀ s : MState n, init n s → chan3IsInvAck n s := by
  intro s hinit i
  rcases hinit with ⟨_, _, _, hchan3, _, _, _, _, _, _⟩
  simp [hchan3 i]

private theorem init_invRequiresNonEmpty (n : Nat) :
    ∀ s : MState n, init n s → invRequiresNonEmpty n s := by
  intro s hinit i hinv
  rcases hinit with ⟨_, _, hchan2, _, _, _, _, _, _, _⟩
  simp [hchan2 i] at hinv

theorem init_fullStrongInvariant (n : Nat) :
    ∀ s : MState n, init n s → fullStrongInvariant n s := by
  intro s hinit
  exact ⟨germanMessages_init_strongInvariant n s hinit,
         germanMessages_init_exclusiveSelfClean n s hinit,
         init_grantExcludesInvAck n s hinit,
         init_exGntdWitness n s hinit,
         init_invAckImpliesInvalid n s hinit,
         init_gntSExcludesInvAck n s hinit,
         init_cleanChannelWhenReady n s hinit,
         init_invReasonProp n s hinit,
         init_invAckClearsGrant n s hinit,
         init_invSetImpliesClean n s hinit,
         init_invClearsInvSet n s hinit,
         init_chan3IsInvAck n s hinit,
         init_invRequiresNonEmpty n s hinit⟩

end GermanMessages
