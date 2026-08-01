import Leslie.Examples.CacheCoherence.TileLink.Atomic.Model

namespace TileLink.Atomic

open TileLink SymShared

def swmr (n : Nat) (s : SymState HomeState CacheLine n) : Prop :=
  ∀ i j : Fin n, i ≠ j → (s.locals i).perm = .T → (s.locals j).perm = .N

def pendingInv (n : Nat) (s : SymState HomeState CacheLine n) : Prop :=
  (∀ i : Fin n, s.shared.pendingGrantAck = some i.1 → (s.locals i).perm ≠ .N) ∧
  (∀ i : Fin n, s.shared.pendingReleaseAck = some i.1 → (s.locals i).dirty = false) ∧
  (s.shared.pendingGrantAck = none ∨ s.shared.pendingReleaseAck = none)

def grantMetaShape (pg : PendingGrantMeta) : Prop :=
  match pg.kind with
  | .block => pg.requesterPerm = .B ∨ pg.requesterPerm = .T
  | .perm => pg.requesterPerm = .T

def scheduledGrantMatchesState (n : Nat) : SymState HomeState CacheLine n → PendingGrantMeta → Prop
  | _, _ => True

def deliveredGrantMatchesState (n : Nat) : SymState HomeState CacheLine n → PendingGrantMeta → Prop
  | _, _ => True

def grantMetaInv (n : Nat) (s : SymState HomeState CacheLine n) : Prop :=
  match s.shared.pendingGrantMeta with
  | none => s.shared.pendingGrantAck = none
  | some pg =>
      pg.requester < n ∧
      s.shared.pendingReleaseAck = none ∧
      grantMetaShape pg ∧
      pg.probesNeeded pg.requester = false ∧
      ((s.shared.pendingGrantAck = none ∧
        (∀ k : Nat, pg.probesRemaining k = pg.probesNeeded k) ∧
        scheduledGrantMatchesState n s pg) ∨
       (s.shared.pendingGrantAck = some pg.requester ∧
        (∀ k : Nat, pg.probesRemaining k = false) ∧
        deliveredGrantMatchesState n s pg))

def dirInv (n : Nat) (s : SymState HomeState CacheLine n) : Prop :=
  ∀ i : Fin n, s.shared.dir i.1 = (s.locals i).perm

def lineWF (n : Nat) (s : SymState HomeState CacheLine n) : Prop :=
  ∀ i : Fin n, (s.locals i).WellFormed

def cleanDataInv (n : Nat) (s : SymState HomeState CacheLine n) : Prop :=
  ∀ i : Fin n, (s.locals i).valid = true → (s.locals i).dirty = false →
    (s.locals i).data = s.shared.mem

noncomputable def logicalData (n : Nat) (s : SymState HomeState CacheLine n) : Val :=
  if hdirty : ∃ i : Fin n, (s.locals i).dirty = true then
    (s.locals (Classical.choose hdirty)).data
  else
    s.shared.mem

def dirtyExclusive (n : Nat) (s : SymState HomeState CacheLine n) : Prop :=
  ∀ i j : Fin n, i ≠ j →
    (s.locals i).dirty = true →
    (s.locals j).perm = .N

def dirtyOwnerDataInv (n : Nat) (s : SymState HomeState CacheLine n) : Prop :=
  ∀ i : Fin n, (s.locals i).dirty = true → logicalData n s = (s.locals i).data

theorem init_lineWF (n : Nat) :
    ∀ s : SymState HomeState CacheLine n, (tlAtomic.toSpec n).init s → lineWF n s := by
  intro s hinit i
  rcases hinit with ⟨_, hlocals⟩
  rcases hlocals i with ⟨hperm, hvalid, hdirty, _⟩
  refine ⟨?_, ?_, ?_⟩
  · intro hd
    simp [hdirty] at hd
  · intro hb
    simp [hperm] at hb
  · intro hn
    simp [hvalid, hdirty]

theorem init_dirInv (n : Nat) :
    ∀ s : SymState HomeState CacheLine n, (tlAtomic.toSpec n).init s → dirInv n s := by
  intro s hinit i
  rcases hinit with ⟨⟨_, hdir, _, _⟩, hlocals⟩
  rcases hlocals i with ⟨hperm, _, _, _⟩
  simpa [hperm] using hdir i.1

theorem init_swmr (n : Nat) :
    ∀ s : SymState HomeState CacheLine n, (tlAtomic.toSpec n).init s → swmr n s := by
  intro s hinit i j _ hT
  rcases hinit with ⟨_, hlocals⟩
  have hi := (hlocals i).1
  simp [hi] at hT

theorem init_pendingInv (n : Nat) :
    ∀ s : SymState HomeState CacheLine n, (tlAtomic.toSpec n).init s → pendingInv n s := by
  intro s hinit
  rcases hinit with ⟨⟨_, _, _, hgrant, hrel⟩, _⟩
  refine ⟨?_, ?_, Or.inl hgrant⟩
  · intro i hi
    simp [hgrant] at hi
  · intro i hi
    simp [hrel] at hi

theorem init_grantMetaInv (n : Nat) :
    ∀ s : SymState HomeState CacheLine n, (tlAtomic.toSpec n).init s → grantMetaInv n s := by
  intro s hinit
  rcases hinit with ⟨⟨_, _, hmeta, hgrant, _⟩, _⟩
  simpa [grantMetaInv, hmeta] using hgrant

theorem init_atomicInv (n : Nat) :
    ∀ s : SymState HomeState CacheLine n, (tlAtomic.toSpec n).init s →
      swmr n s ∧ pendingInv n s ∧ grantMetaInv n s ∧ dirInv n s ∧ lineWF n s ∧ cleanDataInv n s := by
  intro s hinit
  refine ⟨init_swmr n s hinit, init_pendingInv n s hinit, init_grantMetaInv n s hinit,
    init_dirInv n s hinit, init_lineWF n s hinit, ?_⟩
  intro i hvalid _
  rcases hinit with ⟨⟨_, _, _, _, _⟩, hlocals⟩
  rcases hlocals i with ⟨_, hlineValid, _, hdata⟩
  simp [hlineValid] at hvalid

theorem init_cleanDataInv (n : Nat) :
    ∀ s : SymState HomeState CacheLine n, (tlAtomic.toSpec n).init s → cleanDataInv n s := by
  intro s hinit
  rcases init_atomicInv n s hinit with ⟨_, _, _, _, _, hcleanData⟩
  exact hcleanData

theorem atomicInv_implies_dirtyExclusive (n : Nat) :
    ∀ s : SymState HomeState CacheLine n,
      (swmr n s ∧ pendingInv n s ∧ grantMetaInv n s ∧ dirInv n s ∧ lineWF n s ∧ cleanDataInv n s) →
      dirtyExclusive n s := by
  intro s hinv i j hij hdirty
  rcases hinv with ⟨hswmr, _, _, _, hwf, _⟩
  have hiT : (s.locals i).perm = .T := (hwf i).1 hdirty |>.1
  exact hswmr i j hij hiT

theorem atomicInv_implies_dirtyOwnerDataInv (n : Nat) :
    ∀ s : SymState HomeState CacheLine n,
      (swmr n s ∧ pendingInv n s ∧ grantMetaInv n s ∧ dirInv n s ∧ lineWF n s ∧ cleanDataInv n s) →
      dirtyOwnerDataInv n s := by
  classical
  intro s hinv i hdirty
  rcases hinv with ⟨hswmr, _, _, _, hwf, _⟩
  let hsome : ∃ j : Fin n, (s.locals j).dirty = true := ⟨i, hdirty⟩
  have hchooseDirty : (s.locals (Classical.choose hsome)).dirty = true := Classical.choose_spec hsome
  have hiT : (s.locals i).perm = .T := (hwf i).1 hdirty |>.1
  have hchooseT : (s.locals (Classical.choose hsome)).perm = .T :=
    (hwf (Classical.choose hsome)).1 hchooseDirty |>.1
  have hchooseEq : Classical.choose hsome = i := by
    by_contra hne
    have hiN : (s.locals i).perm = .N := hswmr (Classical.choose hsome) i hne hchooseT
    rw [hiT] at hiN
    cases hiN
  simp [logicalData, hsome, hchooseEq]

end TileLink.Atomic
