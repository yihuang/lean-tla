import Leslie.Examples.CacheCoherence.DirectoryMSI.Invariant

namespace DirectoryMSI

/-! ## Init Proofs

    Proof that initial states satisfy `fullStrongInvariant`.
-/

-- Helper: cache i = {} implies (cache i).state = .I
private theorem cache_init_state {n} (s : MState n) (hcache : ∀ i, s.cache i = {}) (i : Fin n) :
    (s.cache i).state = .I := by
  have h := hcache i
  have : s.cache i = { state := .I, data := 0 } := h
  simp [this]

-- Helper: d2cChan i = {} implies (d2cChan i).cmd = .empty
private theorem d2cChan_init_cmd {n} (s : MState n) (hd2c : ∀ i, s.d2cChan i = {}) (i : Fin n) :
    (s.d2cChan i).cmd = .empty := by
  have h := hd2c i
  have : s.d2cChan i = { cmd := .empty, data := 0 } := h
  simp [this]

-- Helper: c2dChan i = {} implies (c2dChan i).cmd = .empty
private theorem c2dChan_init_cmd {n} (s : MState n) (hc2d : ∀ i, s.c2dChan i = {}) (i : Fin n) :
    (s.c2dChan i).cmd = .empty := by
  have h := hc2d i
  have : s.c2dChan i = { cmd := .empty, data := 0 } := h
  simp [this]

-- ── ctrlProp ─────────────────────────────────────────────────────────────────

private theorem init_ctrlProp (n : Nat) (s : MState n) (h : init n s) :
    ctrlProp n s := by
  obtain ⟨hcache, _, _, _, _, _, _, _, _⟩ := h
  intro i j _
  constructor
  · intro hiM
    have := cache_init_state s hcache i
    simp [this] at hiM
  · intro hiS
    have := cache_init_state s hcache i
    simp [this] at hiS

-- ── dataProp ─────────────────────────────────────────────────────────────────

private theorem init_dataProp (n : Nat) (s : MState n) (h : init n s) :
    dataProp n s := by
  obtain ⟨hcache, _, _, _, hdirSt, _, _, _, hmem⟩ := h
  constructor
  · intro _; exact hmem
  · intro i hne
    have := cache_init_state s hcache i
    simp [this] at hne

-- ── invariant ────────────────────────────────────────────────────────────────

private theorem init_invariant (n : Nat) (s : MState n) (h : init n s) :
    invariant n s :=
  ⟨init_ctrlProp n s h, init_dataProp n s h⟩

-- ── exclusiveConsistent ──────────────────────────────────────────────────────

private theorem init_exclusiveConsistent (n : Nat) (s : MState n) (h : init n s) :
    exclusiveConsistent n s := by
  obtain ⟨_, _, _, _, hdirSt, _, _, _, _⟩ := h
  intro hex
  rw [hdirSt] at hex
  exact absurd hex (by decide)

-- ── mImpliesExclusive ────────────────────────────────────────────────────────

private theorem init_mImpliesExclusive (n : Nat) (s : MState n) (h : init n s) :
    mImpliesExclusive n s := by
  obtain ⟨hcache, _, _, _, _, _, _, _, _⟩ := h
  intro i hiM
  have := cache_init_state s hcache i
  simp [this] at hiM

-- ── sImpliesShrSet ───────────────────────────────────────────────────────────

private theorem init_sImpliesShrSet (n : Nat) (s : MState n) (h : init n s) :
    sImpliesShrSet n s := by
  obtain ⟨hcache, _, _, _, _, _, _, _, _⟩ := h
  intro i hiS
  have := cache_init_state s hcache i
  simp [this] at hiS

-- ── exclusiveExcludesShared ──────────────────────────────────────────────────

private theorem init_exclusiveExcludesShared (n : Nat) (s : MState n) (h : init n s) :
    exclusiveExcludesShared n s := by
  obtain ⟨_, _, _, _, hdirSt, _, _, _, _⟩ := h
  intro hex
  rw [hdirSt] at hex
  exact absurd hex (by decide)

-- ── uncachedMeansAllInvalid ──────────────────────────────────────────────────

private theorem init_uncachedMeansAllInvalid (n : Nat) (s : MState n) (h : init n s) :
    uncachedMeansAllInvalid n s := by
  obtain ⟨hcache, _, _, _, _, _, _, _, _⟩ := h
  intro _ i
  exact cache_init_state s hcache i

-- ── gntSDataProp ─────────────────────────────────────────────────────────────

private theorem init_gntSDataProp (n : Nat) (s : MState n) (h : init n s) :
    gntSDataProp n s := by
  obtain ⟨_, _, hd2c, _, _, _, _, _, _⟩ := h
  intro i hgntS
  have := d2cChan_init_cmd s hd2c i
  simp [this] at hgntS

-- ── gntEDataProp ─────────────────────────────────────────────────────────────

private theorem init_gntEDataProp (n : Nat) (s : MState n) (h : init n s) :
    gntEDataProp n s := by
  obtain ⟨_, _, hd2c, _, _, _, _, _, _⟩ := h
  intro i hgntE
  have := d2cChan_init_cmd s hd2c i
  simp [this] at hgntE

-- ── invSetSubsetShrSet ───────────────────────────────────────────────────────

private theorem init_invSetSubsetShrSet (n : Nat) (s : MState n) (h : init n s) :
    invSetSubsetShrSet n s := by
  obtain ⟨_, _, _, _, _, _, hinv, _, _⟩ := h
  intro i hinvSet
  simp [hinv i] at hinvSet

-- ── strongInvariant ──────────────────────────────────────────────────────────

private theorem init_strongInvariant (n : Nat) (s : MState n) (h : init n s) :
    strongInvariant n s :=
  ⟨init_invariant n s h,
   init_exclusiveConsistent n s h,
   init_mImpliesExclusive n s h,
   init_sImpliesShrSet n s h,
   init_exclusiveExcludesShared n s h,
   init_uncachedMeansAllInvalid n s h,
   init_gntSDataProp n s h,
   init_gntEDataProp n s h,
   init_invSetSubsetShrSet n s h⟩

-- ── ackDataProp ──────────────────────────────────────────────────────────────

private theorem init_ackDataProp (n : Nat) (s : MState n) (h : init n s) :
    ackDataProp n s := by
  obtain ⟨_, _, _, hc2d, _, _, _, _, _⟩ := h
  intro i hack _
  have := c2dChan_init_cmd s hc2d i
  simp [this] at hack

-- ── curNodeNotInInvSet ───────────────────────────────────────────────────────

private theorem init_curNodeNotInInvSet (n : Nat) (s : MState n) (h : init n s) :
    curNodeNotInInvSet n s := by
  obtain ⟨_, _, _, _, _, _, hinv, hcurCmd, _⟩ := h
  intro hgetM _
  rw [hcurCmd] at hgetM
  exact absurd hgetM (by decide)

-- ── exclusiveNoDuplicateGrant ────────────────────────────────────────────────

private theorem init_exclusiveNoDuplicateGrant (n : Nat) (s : MState n) (h : init n s) :
    exclusiveNoDuplicateGrant n s := by
  obtain ⟨_, _, _, _, hdirSt, _, _, _, _⟩ := h
  intro hex
  rw [hdirSt] at hex
  exact absurd hex (by decide)

-- ── sharedNoGntE ─────────────────────────────────────────────────────────────

private theorem init_sharedNoGntE (n : Nat) (s : MState n) (h : init n s) :
    sharedNoGntE n s := by
  obtain ⟨_, _, _, _, hdirSt, _, _, _, _⟩ := h
  intro hshared
  rw [hdirSt] at hshared
  exact absurd hshared (by decide)

-- ── gntEImpliesExclusive ─────────────────────────────────────────────────────

private theorem init_gntEImpliesExclusive (n : Nat) (s : MState n) (h : init n s) :
    gntEImpliesExclusive n s := by
  obtain ⟨_, _, hd2c, _, _, _, _, _, _⟩ := h
  intro i hgntE
  have := d2cChan_init_cmd s hd2c i
  simp [this] at hgntE

-- ── fetchImpliesCurCmdGetS ───────────────────────────────────────────────────

private theorem init_fetchImpliesCurCmdGetS (n : Nat) (s : MState n) (h : init n s) :
    fetchImpliesCurCmdGetS n s := by
  obtain ⟨_, _, hd2c, _, _, _, _, _, _⟩ := h
  intro i hfetch
  have := d2cChan_init_cmd s hd2c i
  simp [this] at hfetch

-- ── invImpliesCurCmd ─────────────────────────────────────────────────────────

private theorem init_invImpliesCurCmd (n : Nat) (s : MState n) (h : init n s) :
    invImpliesCurCmd n s := by
  obtain ⟨_, _, hd2c, _, _, _, _, _, _⟩ := h
  intro i hinv
  have := d2cChan_init_cmd s hd2c i
  simp [this] at hinv

-- ── ackImpliesInvalid ────────────────────────────────────────────────────────

private theorem init_ackImpliesInvalid (n : Nat) (s : MState n) (h : init n s) :
    ackImpliesInvalid n s := by
  obtain ⟨_, _, _, hc2d, _, _, _, _, _⟩ := h
  intro i hack
  have := c2dChan_init_cmd s hc2d i
  simp [this] at hack

-- ── ackImpliesInvSetFalse ────────────────────────────────────────────────────

private theorem init_ackImpliesInvSetFalse (n : Nat) (s : MState n) (h : init n s) :
    ackImpliesInvSetFalse n s := by
  obtain ⟨_, _, _, hc2d, _, _, _, _, _⟩ := h
  intro i hack
  have := c2dChan_init_cmd s hc2d i
  simp [this] at hack

-- ── invSetImpliesCurCmdGetM ─────────────────────────────────────────────────

private theorem init_invSetImpliesCurCmdGetM (n : Nat) (s : MState n) (h : init n s) :
    invSetImpliesCurCmdGetM n s := by
  obtain ⟨_, _, _, _, _, _, hinvSet, _, _⟩ := h
  intro i hi
  have := hinvSet i
  simp [this] at hi

-- ── Top-level theorem ────────────────────────────────────────────────────────

theorem init_fullStrongInvariant (n : Nat) (s : MState n) (h : init n s) :
    fullStrongInvariant n s :=
  ⟨init_strongInvariant n s h,
   init_ackDataProp n s h,
   init_curNodeNotInInvSet n s h,
   init_exclusiveNoDuplicateGrant n s h,
   init_sharedNoGntE n s h,
   init_gntEImpliesExclusive n s h,
   init_fetchImpliesCurCmdGetS n s h,
   init_invImpliesCurCmd n s h,
   init_ackImpliesInvalid n s h,
   init_ackImpliesInvSetFalse n s h,
   init_invSetImpliesCurCmdGetM n s h,
   by intro i hack; obtain ⟨_, _, _, hc2d, _, _, _, _, _⟩ := h
      have := c2dChan_init_cmd s hc2d i; simp [this] at hack,
   by intro i hack; obtain ⟨_, _, _, hc2d, _, _, _, _, _⟩ := h
      have := c2dChan_init_cmd s hc2d i; simp [this] at hack,
   by intro i hinv; obtain ⟨_, _, hd2c, _, _, _, _, _, _⟩ := h
      have := d2cChan_init_cmd s hd2c i; simp [this] at hinv,
   by intro i hinv; obtain ⟨_, _, _, _, _, _, hinvSet, _, _⟩ := h
      simp [hinvSet i] at hinv,
   by intro i hinv; obtain ⟨_, _, hd2c, _, _, _, _, _, _⟩ := h
      have := d2cChan_init_cmd s hd2c i; simp [this] at hinv,
   by intro i hack; obtain ⟨_, _, _, hc2d, _, _, _, _, _⟩ := h
      have := c2dChan_init_cmd s hc2d i; simp [this] at hack,
   by intro i hinv; obtain ⟨_, _, hd2c, _, _, _, _, _, _⟩ := h
      have := d2cChan_init_cmd s hd2c i; simp [this] at hinv,
   by intro i hack; obtain ⟨_, _, _, hc2d, _, _, _, _, _⟩ := h
      have := c2dChan_init_cmd s hc2d i; simp [this] at hack,
   by intro i hack; obtain ⟨_, _, _, hc2d, _, _, _, _, _⟩ := h
      have := c2dChan_init_cmd s hc2d i; simp [this] at hack,
   by intro i hinv; obtain ⟨_, _, hd2c, _, _, _, _, _, _⟩ := h
      have := d2cChan_init_cmd s hd2c i; simp [this] at hinv,
   by intro i hack; obtain ⟨_, _, _, hc2d, _, _, _, _, _⟩ := h
      have := c2dChan_init_cmd s hc2d i; simp [this] at hack,
   by intro i hgntS; obtain ⟨_, _, hd2c, _, _, _, _, _, _⟩ := h
      have := d2cChan_init_cmd s hd2c i; simp [this] at hgntS,
   by intro i hgntS; obtain ⟨_, _, hd2c, _, _, _, _, _, _⟩ := h
      have := d2cChan_init_cmd s hd2c i; simp [this] at hgntS,
   by intro i hinv; obtain ⟨_, _, hd2c, _, _, _, _, _, _⟩ := h
      have := d2cChan_init_cmd s hd2c i; simp [this] at hinv⟩

end DirectoryMSI
