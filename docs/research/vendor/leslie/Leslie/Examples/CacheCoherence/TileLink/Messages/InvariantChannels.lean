import Leslie.Examples.CacheCoherence.TileLink.Messages.InvariantCore

namespace TileLink.Messages

open TileLink SymShared

def chanAInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ i : Fin n, match (s.locals i).chanA with
    | none => True
    | some msg =>
        (s.locals i).pendingSource = some msg.source ∧
        ((msg.opcode = .acquireBlock ∧ msg.param.legalFrom (s.locals i).line.perm) ∨
         (msg.opcode = .acquirePerm ∧ msg.param.legalFrom (s.locals i).line.perm ∧ msg.param.result = .T) ∨
         (msg.opcode = .get ∨ msg.opcode = .putFullData))

def chanBInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ i : Fin n, match (s.locals i).chanB with
    | none => True
    | some msg =>
        ∃ tx,
          s.shared.currentTxn = some tx ∧
          tx.phase = .probing ∧
          tx.probesRemaining i.1 = true ∧
          msg.source = tx.source ∧
          msg.opcode = probeOpcodeOfKind tx.kind ∧
          msg.param = probeCapOfResult tx.resultPerm

def chanCInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ i : Fin n, match (s.locals i).chanC with
    | none => True
    | some msg =>
        (∃ tx,
          s.shared.currentTxn = some tx ∧
          tx.phase = .probing ∧
          tx.probesRemaining i.1 = true ∧
          (s.locals i).chanA = none ∧
          (s.locals i).chanB = none ∧
          msg.source = i.1 ∧
          probeAckMsgWellFormed msg ∧
          msg.data = probeAckDataOfLine (tx.preLines i.1)) ∨
        (∃ param,
          s.shared.currentTxn = none ∧
          (s.locals i).releaseInFlight = true ∧
          (s.locals i).chanA = none ∧
          (s.locals i).chanB = none ∧
          msg.source = i.1 ∧
          msg.param = some param ∧
          (s.locals i).line.perm = param.result ∧
          releaseMsgWellFormed msg)

def chanDInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ i : Fin n, match (s.locals i).chanD with
    | none => True
    | some msg =>
        (∃ tx,
          s.shared.currentTxn = some tx ∧
          tx.requester = i.1 ∧
          tx.phase = .grantPendingAck ∧
          s.shared.pendingGrantAck = some i.1 ∧
          (s.locals i).pendingSink = some tx.sink ∧
          (s.locals i).chanE = none ∧
          msg = grantMsgOfTxn tx) ∨
        (s.shared.currentTxn = none ∧
          s.shared.pendingGrantAck = none ∧
          s.shared.pendingReleaseAck = some i.1 ∧
          (s.locals i).releaseInFlight = true ∧
          (s.locals i).chanC = none ∧
          (s.locals i).chanE = none ∧
          msg = releaseAckMsg i.1) ∨
        (msg.opcode = .accessAck ∨ msg.opcode = .accessAckData) ∧
          (s.locals i).pendingSource ≠ none ∧
          (s.locals i).chanA = none

def chanEInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ i : Fin n, match (s.locals i).chanE with
    | none => True
    | some msg =>
        ∃ tx,
          s.shared.currentTxn = some tx ∧
          tx.requester = i.1 ∧
          tx.phase = .grantPendingAck ∧
          s.shared.pendingGrantAck = some i.1 ∧
          (s.locals i).pendingSink = some tx.sink ∧
          (s.locals i).chanD = none ∧
          msg = ({ sink := tx.sink } : EMsg)

def channelInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  chanAInv n s ∧ chanBInv n s ∧ chanCInv n s ∧ chanDInv n s ∧ chanEInv n s

theorem init_chanAInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → chanAInv n s := by
  intro s hinit i
  rcases hinit with ⟨_, hlocals⟩
  rcases hlocals i with ⟨_, hA, _, _, _, hPendingSource, _, _, _⟩
  simp [hA]

theorem init_chanBInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → chanBInv n s := by
  intro s hinit i
  rcases hinit with ⟨_, hlocals⟩
  rcases hlocals i with ⟨_, _, hB, _, _, _, _, _, _⟩
  simp [hB]

theorem init_chanCInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → chanCInv n s := by
  intro s hinit i
  rcases hinit with ⟨_, hlocals⟩
  rcases hlocals i with ⟨_, _, _, hC, _, _, _, _, _⟩
  simp [hC]

theorem init_channelInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → channelInv n s := by
  intro s hinit
  refine ⟨init_chanAInv n s hinit, init_chanBInv n s hinit, init_chanCInv n s hinit, ?_, ?_⟩
  · intro i
    rcases hinit with ⟨_, hlocals⟩
    rcases hlocals i with ⟨_, _, _, _, hD, _, _, _, _⟩
    simp [hD]
  · intro i
    rcases hinit with ⟨_, hlocals⟩
    rcases hlocals i with ⟨_, _, _, _, _, hE, _, _, _⟩
    simp [hE]

end TileLink.Messages
