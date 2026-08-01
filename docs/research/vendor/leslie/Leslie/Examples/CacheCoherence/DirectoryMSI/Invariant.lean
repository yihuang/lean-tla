import Leslie.Examples.CacheCoherence.DirectoryMSI.Model

namespace DirectoryMSI

/-! ## Invariant Definitions

    Public safety predicates and the private strong/full inductive invariants
    used to prove the directory-based MSI cache coherence protocol.
-/

-- ── Public safety predicates ──────────────────────────────────────────────

/-- SWMR: at most one M-holder, and M excludes all S/M in others -/
def ctrlProp (n : Nat) (s : MState n) : Prop :=
  ∀ i j : Fin n, i ≠ j →
    ((s.cache i).state = .M → (s.cache j).state = .I) ∧
    ((s.cache i).state = .S → (s.cache j).state ≠ .M)

/-- Data integrity: memory is fresh when no exclusive grant outstanding;
    every non-Invalid cache holds the true value -/
def dataProp (n : Nat) (s : MState n) : Prop :=
  (s.dirSt ≠ .Exclusive → s.memData = s.auxData) ∧
  (∀ i : Fin n, (s.cache i).state ≠ .I → (s.cache i).data = s.auxData)

def invariant (n : Nat) (s : MState n) : Prop :=
  ctrlProp n s ∧ dataProp n s

-- ── Directory consistency with cache state ────────────────────────────────

/-- If dirSt = Exclusive, exNode holds M *or* has a gntE in flight (grant not yet applied)
    *or* an ack is in flight back to the directory (writeback being processed),
    and all other nodes are in I. The three-way disjunction covers the full lifecycle:
    1. cache[exNode].state = .M: M-holder has the data
    2. d2cChan[exNode].cmd = .gntE: grant is in flight to new exclusive holder
    3. c2dChan[exNode].cmd = .ack: writeback ack is in flight back to directory -/
def exclusiveConsistent (n : Nat) (s : MState n) : Prop :=
  s.dirSt = .Exclusive →
    ((s.cache s.exNode).state = .M ∨ (s.d2cChan s.exNode).cmd = .gntE ∨
     (s.c2dChan s.exNode).cmd = .ack) ∧
    ∀ j : Fin n, j ≠ s.exNode → (s.cache j).state = .I

/-- If a cache is in M, dirSt = Exclusive with that node as exNode -/
def mImpliesExclusive (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.cache i).state = .M → s.dirSt = .Exclusive ∧ s.exNode = i

/-- If a cache is in S, it is in shrSet — unless it is the getM requester
    (RecvGetM_Shared clears shrSet[curNode] while cache stays S briefly)
    or a gntE is in flight to it (SendGntE_After* sets curCmd=empty while
    the old S cache at curNode hasn't yet received the grant) -/
def sImpliesShrSet (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.cache i).state = .S →
    s.shrSet i = true ∨ (s.curCmd = .getM ∧ s.curNode = i) ∨
    (s.d2cChan i).cmd = .gntE

/-- If dirSt = Exclusive, a cache in S must have a gntE in flight to it
    (this happens briefly after SendGntE_After* before RecvGntE) -/
def exclusiveExcludesShared (n : Nat) (s : MState n) : Prop :=
  s.dirSt = .Exclusive → ∀ i : Fin n, (s.cache i).state = .S →
    (s.d2cChan i).cmd = .gntE

/-- If dirSt = Uncached, all caches are in I -/
def uncachedMeansAllInvalid (n : Nat) (s : MState n) : Prop :=
  s.dirSt = .Uncached → ∀ i : Fin n, (s.cache i).state = .I

-- ── Channel consistency ───────────────────────────────────────────────────

/-- A gntS in d2cChan carries auxData -/
def gntSDataProp (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.d2cChan i).cmd = .gntS → (s.d2cChan i).data = s.auxData

/-- A gntE in d2cChan carries auxData -/
def gntEDataProp (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.d2cChan i).cmd = .gntE → (s.d2cChan i).data = s.auxData

/-- An ack in c2dChan (from an M-holder) carries auxData -/
def ackDataProp (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.c2dChan i).cmd = .ack →
    ((s.cache i).state = .M ∨ s.dirSt = .Exclusive) →
    (s.c2dChan i).data = s.auxData

/-- invSet is a subset of shrSet -/
def invSetSubsetShrSet (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, s.invSet i = true → s.shrSet i = true

/-- If curCmd = getM and dirSt = Shared, then curNode is not in invSet -/
def curNodeNotInInvSet (n : Nat) (s : MState n) : Prop :=
  s.curCmd = .getM → s.dirSt = .Shared → s.invSet s.curNode = false

/-- When dirSt = Exclusive, no gntE is in d2cChan for a non-exNode -/
def exclusiveNoDuplicateGrant (n : Nat) (s : MState n) : Prop :=
  s.dirSt = .Exclusive →
    ∀ i : Fin n, i ≠ s.exNode → (s.d2cChan i).cmd ≠ .gntE

/-- When dirSt = Shared, no gntE is in d2cChan -/
def sharedNoGntE (n : Nat) (s : MState n) : Prop :=
  s.dirSt = .Shared → ∀ i : Fin n, (s.d2cChan i).cmd ≠ .gntE

/-- A gntE in d2cChan implies dirSt = Exclusive -/
def gntEImpliesExclusive (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.d2cChan i).cmd = .gntE → s.dirSt = .Exclusive ∧ s.exNode = i

/-- A fetch in d2cChan implies curCmd = getS and dirSt = Exclusive -/
def fetchImpliesCurCmdGetS (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.d2cChan i).cmd = .fetch →
    s.curCmd = .getS ∧ s.dirSt = .Exclusive ∧ s.exNode = i

/-- An inv in d2cChan implies curCmd = getM (inv only exists during getM flow) -/
def invImpliesCurCmd (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.d2cChan i).cmd = .inv → s.curCmd = .getM

/-- If ack is in c2dChan[i], then cache[i] is in I -/
def ackImpliesInvalid (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.c2dChan i).cmd = .ack → (s.cache i).state = .I

/-- If ack is in c2dChan[i], then invSet[i] is already cleared -/
def ackImpliesInvSetFalse (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.c2dChan i).cmd = .ack → s.invSet i = false

/-- invSet entries only exist during a getM flow -/
def invSetImpliesCurCmdGetM (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, s.invSet i = true → s.curCmd = .getM

/-- Acks only exist during active command processing -/
def ackImpliesCurCmdNotEmpty (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.c2dChan i).cmd = .ack → s.curCmd ≠ .empty

/-- During a getS flow, any ack must be from the exclusive owner (fetch response)
    and dirSt must still be Exclusive (not yet transitioned to Uncached) -/
def getSAckProp (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.c2dChan i).cmd = .ack → s.curCmd = .getS →
    s.dirSt = .Exclusive ∧ s.exNode = i

/-- An inv and an ack at the same node cannot coexist in channels -/
def invAckExclusive (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.d2cChan i).cmd = .inv → (s.c2dChan i).cmd ≠ .ack

/-- invSet entries only exist when dirSt = Shared -/
def invSetImpliesDirShared (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, s.invSet i = true → s.dirSt = .Shared

/-- An inv in d2cChan with dirSt=Shared implies shrSet is still set -/
def invMsgImpliesShrSet (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.d2cChan i).cmd = .inv → s.dirSt = .Shared → s.shrSet i = true

/-- An ack in c2dChan with dirSt=Shared implies shrSet is still set -/
def ackSharedImpliesShrSet (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.c2dChan i).cmd = .ack → s.dirSt = .Shared → s.shrSet i = true

/-- An inv in d2cChan with dirSt=Exclusive must be at exNode -/
def invExclOnlyAtExNode (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.d2cChan i).cmd = .inv → s.dirSt = .Exclusive → i = s.exNode

/-- An ack in c2dChan with dirSt=Exclusive must be at exNode -/
def ackExclOnlyAtExNode (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.c2dChan i).cmd = .ack → s.dirSt = .Exclusive → i = s.exNode

/-- No acks exist when dirSt = Uncached -/
def ackImpliesDirNotUncached (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.c2dChan i).cmd = .ack → s.dirSt ≠ .Uncached

/-- No inv messages exist when dirSt = Uncached -/
def invImpliesDirNotUncached (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.d2cChan i).cmd = .inv → s.dirSt ≠ .Uncached

/-- An ack at node k implies d2cChan[k] is empty (channel discipline:
    ack was created by RecvInv/RecvFetch which cleared d2cChan) -/
def ackImpliesD2cEmpty (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.c2dChan i).cmd = .ack → (s.d2cChan i).cmd = .empty

/-- A gntS at node k implies shrSet[k]=true or it's the getM requester
    (whose shrSet was cleared by RecvGetM_Shared) -/
def gntSProp (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.d2cChan i).cmd = .gntS →
    s.shrSet i = true ∨ (s.curCmd = .getM ∧ s.curNode = i)

/-- A gntS in d2cChan implies dirSt = Shared.
    gntS is only created by RecvGetS_Uncached (sets dirSt→Shared) and
    RecvGetS_Shared (keeps dirSt=Shared). While gntS exists, dirSt cannot
    leave Shared: SendGntE_AfterShared is blocked by shrSet (via gntSProp),
    and RecvAck_GetS/RecvAck_GetM_Exclusive require dirSt≠Shared. -/
def gntSImpliesDirShared (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.d2cChan i).cmd = .gntS → s.dirSt = .Shared

/-- An inv in d2cChan[k] implies invSet[k] is already false
    (SendInv sets d2cChan[j]:=inv and invSet[j]:=false simultaneously) -/
def invImpliesInvSetFalse (n : Nat) (s : MState n) : Prop :=
  ∀ i : Fin n, (s.d2cChan i).cmd = .inv → s.invSet i = false

-- ── Compound invariants ───────────────────────────────────────────────────

def strongInvariant (n : Nat) (s : MState n) : Prop :=
  invariant n s ∧
  exclusiveConsistent n s ∧
  mImpliesExclusive n s ∧
  sImpliesShrSet n s ∧
  exclusiveExcludesShared n s ∧
  uncachedMeansAllInvalid n s ∧
  gntSDataProp n s ∧
  gntEDataProp n s ∧
  invSetSubsetShrSet n s

def fullStrongInvariant (n : Nat) (s : MState n) : Prop :=
  strongInvariant n s ∧
  ackDataProp n s ∧
  curNodeNotInInvSet n s ∧
  exclusiveNoDuplicateGrant n s ∧
  sharedNoGntE n s ∧
  gntEImpliesExclusive n s ∧
  fetchImpliesCurCmdGetS n s ∧
  invImpliesCurCmd n s ∧
  ackImpliesInvalid n s ∧
  ackImpliesInvSetFalse n s ∧
  invSetImpliesCurCmdGetM n s ∧
  ackImpliesCurCmdNotEmpty n s ∧
  getSAckProp n s ∧
  invAckExclusive n s ∧
  invSetImpliesDirShared n s ∧
  invMsgImpliesShrSet n s ∧
  ackSharedImpliesShrSet n s ∧
  invExclOnlyAtExNode n s ∧
  ackExclOnlyAtExNode n s ∧
  ackImpliesDirNotUncached n s ∧
  invImpliesDirNotUncached n s ∧
  ackImpliesD2cEmpty n s ∧
  gntSProp n s ∧
  gntSImpliesDirShared n s ∧
  invImpliesInvSetFalse n s

end DirectoryMSI
