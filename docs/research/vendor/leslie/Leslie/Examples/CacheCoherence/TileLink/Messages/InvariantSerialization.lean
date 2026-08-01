import Leslie.Examples.CacheCoherence.TileLink.Messages.InvariantChannels

namespace TileLink.Messages

open TileLink SymShared

def grantSerializationInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ i : Nat, s.shared.pendingGrantAck = some i →
    ∃ tx,
      s.shared.currentTxn = some tx ∧
      tx.requester = i ∧
      tx.phase = .grantPendingAck ∧
      s.shared.pendingReleaseAck = none

def releaseSerializationInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ i : Nat, s.shared.pendingReleaseAck = some i →
    s.shared.currentTxn = none ∧
    s.shared.pendingGrantAck = none ∧
    ∃ fi : Fin n, fi.1 = i ∧ (s.locals fi).releaseInFlight = true

def grantChannelSerializationInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ i : Fin n, match (s.locals i).chanD with
    | none => True
    | some msg =>
        msg.opcode = .releaseAck →
          s.shared.currentTxn = none ∧
          s.shared.pendingReleaseAck = some i.1

def releaseChannelSerializationInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ i : Fin n, match (s.locals i).chanC with
    | none => True
    | some msg =>
        (msg.opcode = .release ∨ msg.opcode = .releaseData) →
          s.shared.currentTxn = none ∧
          (s.locals i).releaseInFlight = true

def serializationInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  grantSerializationInv n s ∧
  releaseSerializationInv n s ∧
  grantChannelSerializationInv n s ∧
  releaseChannelSerializationInv n s

theorem serializationInv_of_core_channel (n : Nat)
    (s : SymState HomeState NodeState n)
    (hcore : coreInv n s) (hchan : channelInv n s) :
    serializationInv n s := by
  rcases hcore with ⟨_, _, hpending, _⟩
  rcases hchan with ⟨_, _, hchanC, hchanD, _⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hgrant
    cases hcur : s.shared.currentTxn with
    | none =>
        simp [pendingInv, hcur] at hpending
        rcases hpending with ⟨hgrantNone, _⟩
        rw [hgrant] at hgrantNone
        simp at hgrantNone
    | some tx =>
        simp [pendingInv, hcur] at hpending
        rcases hpending with ⟨hrelNone, hpendingGrant⟩
        have hphase : tx.phase = .grantPendingAck := by
          by_cases hgp : tx.phase = .grantPendingAck
          · exact hgp
          · rw [if_neg hgp] at hpendingGrant
            rw [hgrant] at hpendingGrant
            simp at hpendingGrant
        refine ⟨tx, by simpa [hcur], ?_, hphase, hrelNone⟩
        rw [if_pos hphase] at hpendingGrant
        have hreq : some tx.requester = some i := by
          rw [← hpendingGrant, hgrant]
        exact Option.some.inj hreq
  · intro i hrel
    cases hcur : s.shared.currentTxn with
    | none =>
        simp [pendingInv, hcur] at hpending
        rcases hpending with ⟨hgrantNone, hpendingRel⟩
        rw [hrel] at hpendingRel
        rcases hpendingRel with ⟨_, fi, hfi, hflight⟩
        exact ⟨by simpa [hcur], hgrantNone, fi, hfi, hflight⟩
    | some tx =>
        simp [pendingInv, hcur] at hpending
        rcases hpending with ⟨hrelNone, _⟩
        rw [hrel] at hrelNone
        simp at hrelNone
  · intro i
    cases hD : (s.locals i).chanD with
    | none =>
        trivial
    | some msg =>
        intro hop
        specialize hchanD i
        rw [hD] at hchanD
        rcases hchanD with hgrantBranch | hrelBranch | haccBranch
        · rcases hgrantBranch with ⟨tx, hcur, _, _, _, _, _, hmsg⟩
          rw [hmsg] at hop
          cases hdata : tx.grantHasData <;> simp [grantMsgOfTxn, grantOpcodeOfTxn, hdata] at hop
        · rcases hrelBranch with ⟨hcur, _, hrel, _, _, _, hmsg⟩
          exact ⟨hcur, hrel⟩
        · rcases haccBranch with ⟨hacc, _, _⟩
          rcases hacc with hacc | hacc <;> rw [hacc] at hop <;> cases hop
  · intro i
    cases hC : (s.locals i).chanC with
    | none =>
        trivial
    | some msg =>
        intro hop
        specialize hchanC i
        rw [hC] at hchanC
        rcases hchanC with hprobe | hrel
        · rcases hprobe with ⟨tx, hcur, _, _, _, _, _, hwf, _⟩
          have hopcode : msg.opcode = .probeAck ∨ msg.opcode = .probeAckData := by
            cases hwf with
            | inl hprobeAck =>
                exact Or.inl hprobeAck.1
            | inr hprobeAckData =>
                exact Or.inr hprobeAckData.1
          cases hopcode with
          | inl hprobeAck =>
              cases hop with
              | inl hrelop => rw [hprobeAck] at hrelop; cases hrelop
              | inr hrelop => rw [hprobeAck] at hrelop; cases hrelop
          | inr hprobeAckData =>
              cases hop with
              | inl hrelop => rw [hprobeAckData] at hrelop; cases hrelop
              | inr hrelop => rw [hprobeAckData] at hrelop; cases hrelop
        · rcases hrel with ⟨param, hcur, hflight, _, _, _, _, _, _⟩
          exact ⟨hcur, hflight⟩

theorem init_serializationInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → serializationInv n s := by
  intro s hinit
  exact serializationInv_of_core_channel n s (init_coreInv n s hinit) (init_channelInv n s hinit)

end TileLink.Messages
