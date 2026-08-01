import Leslie.Examples.CacheCoherence.GermanMessages.Model

namespace GermanMessages

/-! ## Invariant Definitions

    Public safety predicates and the private strong/full inductive invariants
    used to prove the German cache coherence protocol.
-/

-- ── Public safety predicates ──────────────────────────────────────────────

/-- Control safety: at most one exclusive holder, and shared copies exclude exclusive ones. -/
def ctrlProp (n : Nat) (s : MState n) : Prop :=
  ∀ i j : Fin n, i ≠ j →
    ((s.cache i).state = .E → (s.cache j).state = .I) ∧
    ((s.cache i).state = .S → (s.cache j).state = .I ∨ (s.cache j).state = .S)

/-- Data safety: memory matches `auxData` when no exclusive grant is outstanding,
    and every valid cache copy matches `auxData`. -/
def dataProp (n : Nat) (s : MState n) : Prop :=
  ((s.exGntd = false) → s.memData = s.auxData) ∧
  (∀ i : Fin n, (s.cache i).state ≠ .I → (s.cache i).data = s.auxData)

def invariant (n : Nat) (s : MState n) : Prop :=
  ctrlProp n s ∧ dataProp n s

-- ── strongInvariant components ────────────────────────────────────────────

def cacheInShrSet (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.cache i).state ≠ .I → s.shrSet i = true

def grantDataProp (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, ((s.chan2 i).cmd = .gntS ∨ (s.chan2 i).cmd = .gntE) → (s.chan2 i).data = s.auxData

def invAckDataProp (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, s.exGntd = true → (s.chan3 i).cmd = .invAck → (s.chan3 i).data = s.auxData

def noExclusiveWhenFalse (n : Nat) (s : MState n) : Prop :=
  s.exGntd = false → ∀ i : Fin n, (s.cache i).state ≠ .E ∧ (s.chan2 i).cmd ≠ .gntE

def invSetSubsetShrSet (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, s.invSet i = true → s.shrSet i = true

def exclusiveImpliesExGntd (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, ((s.cache i).state = .E ∨ (s.chan2 i).cmd = .gntE) → s.exGntd = true

def noSharedWhenExGntd (n : Nat) (s : MState n) : Prop :=
  s.exGntd = true → ∀ i : Fin n, (s.cache i).state ≠ .S ∧ (s.chan2 i).cmd ≠ .gntS

def chanImpliesShrSet (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n,
    (((s.chan2 i).cmd = .inv) ∨
     ((s.chan2 i).cmd = .gntS) ∨
     ((s.chan2 i).cmd = .gntE) ∨
     ((s.chan3 i).cmd = .invAck)) →
    s.shrSet i = true

def uniqueShrSetWhenExGntd (n : Nat) (s : MState n) : Prop :=
  s.exGntd = true →
  ∀ i j : Fin n, i ≠ j → s.shrSet i = true → s.shrSet j = false

/-- Basic strong inductive invariant used for the core protocol proofs. -/
def strongInvariant (n : Nat) (s : MState n) : Prop :=
  invariant n s ∧
  cacheInShrSet n s ∧
  grantDataProp n s ∧
  invAckDataProp n s ∧
  noExclusiveWhenFalse n s ∧
  invSetSubsetShrSet n s ∧
  exclusiveImpliesExGntd n s ∧
  noSharedWhenExGntd n s ∧
  chanImpliesShrSet n s ∧
  uniqueShrSetWhenExGntd n s

-- ── Additional auxiliary predicates ──────────────────────────────────────

def exclusiveSelfClean (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.cache i).state = .E →
    (s.chan2 i).cmd ≠ .gntS ∧
    (s.chan2 i).cmd ≠ .gntE ∧
    (s.chan3 i).cmd ≠ .invAck

def grantExcludesInvAck (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.chan2 i).cmd = .gntE → (s.chan3 i).cmd ≠ .invAck

def exGntdWitness (n : Nat) (s : MState n) : Prop :=
  s.exGntd = true →
    ∃ j : Fin n, (s.cache j).state = .E ∨ (s.chan2 j).cmd = .gntE ∨ (s.chan3 j).cmd = .invAck

def invAckImpliesInvalid (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.chan3 i).cmd = .invAck → (s.cache i).state = .I

def invReasonProp (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.chan2 i).cmd = .inv → s.exGntd = true ∨ s.curCmd = .reqE

def cleanChannelWhenReady (n : Nat) (s : MState n) : Prop :=
  (s.curCmd = .empty ∨ (s.curCmd = .reqS ∧ s.exGntd = false)) →
    ∀ i : Fin n, (s.chan3 i).cmd ≠ .invAck

def gntSExcludesInvAck (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.chan2 i).cmd = .gntS → (s.chan3 i).cmd ≠ .invAck

def invAckClearsGrant (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.chan3 i).cmd = .invAck → (s.chan2 i).cmd = .empty

def invSetImpliesClean (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, s.invSet i = true → (s.chan3 i).cmd = .empty

def invClearsInvSet (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.chan2 i).cmd = .inv → s.invSet i = false

def chan3IsInvAck (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.chan3 i).cmd = .empty ∨ (s.chan3 i).cmd = .invAck

def invRequiresNonEmpty (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.chan2 i).cmd = .inv → s.curCmd ≠ .empty

/-- Full inductive invariant: strongInvariant + twelve auxiliary properties. -/
def fullStrongInvariant (n : Nat) (s : MState n) : Prop :=
  strongInvariant n s ∧
  exclusiveSelfClean n s ∧
  grantExcludesInvAck n s ∧
  exGntdWitness n s ∧
  invAckImpliesInvalid n s ∧
  gntSExcludesInvAck n s ∧
  cleanChannelWhenReady n s ∧
  invReasonProp n s ∧
  invAckClearsGrant n s ∧
  invSetImpliesClean n s ∧
  invClearsInvSet n s ∧
  chan3IsInvAck n s ∧
  invRequiresNonEmpty n s

end GermanMessages
