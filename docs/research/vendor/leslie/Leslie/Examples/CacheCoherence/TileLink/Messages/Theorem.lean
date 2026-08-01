import Leslie.Examples.CacheCoherence.TileLink.Messages.StepRelease

namespace TileLink.Messages

open TLA SymShared

-- fullInv invariant is proved as part of forwardSimInv in Refinement.lean.
-- The full proof chain: forwardSimInv → refinementInv → fullInv.

theorem grantPendingAck_other_channels_none_of_fullInv {n : Nat}
    {s : SymState HomeState NodeState n} {tx : ManagerTxn}
    (hinv : fullInv n s)
    (hcur : s.shared.currentTxn = some tx)
    (hphase : tx.phase = .grantPendingAck) :
    ∀ j : Fin n, j.1 ≠ tx.requester →
      (s.locals j).chanB = none ∧
      (s.locals j).chanC = none ∧
      ((s.locals j).chanD = none ∨
        ∃ msg, (s.locals j).chanD = some msg ∧
          (msg.opcode = .accessAck ∨ msg.opcode = .accessAckData) ∧
          (s.locals j).pendingSource ≠ none) ∧
      (s.locals j).chanE = none := by
  rcases hinv with ⟨_, hchan, _⟩
  rcases hchan with ⟨hchanA, hchanB, hchanC, hchanD, hchanE⟩
  intro j hreqj
  refine ⟨?_, ?_, ?_, ?_⟩
  · specialize hchanB j
    cases hB : (s.locals j).chanB with
    | none => exact rfl
    | some _ =>
        rw [hB] at hchanB
        rcases hchanB with ⟨tx0, hcur0, hprobing, _, _, _, _⟩
        rw [hcur] at hcur0
        injection hcur0 with htx
        subst htx
        rw [hphase] at hprobing
        cases hprobing
  · specialize hchanC j
    cases hC : (s.locals j).chanC with
    | none => exact rfl
    | some _ =>
        rw [hC] at hchanC
        rcases hchanC with hprobe | hrel
        · rcases hprobe with ⟨tx0, hcur0, hprobing, _, _, _, _, _, _⟩
          rw [hcur] at hcur0
          injection hcur0 with htx
          subst htx
          rw [hphase] at hprobing
          cases hprobing
        · rcases hrel with ⟨_, htxnNone, _, _, _, _, _, _⟩
          rw [hcur] at htxnNone
          simp at htxnNone
  · specialize hchanD j
    cases hD : (s.locals j).chanD with
    | none => exact Or.inl rfl
    | some msg =>
        rw [hD] at hchanD
        rcases hchanD with hgrant | hrel | ⟨hacc, hps, _⟩
        · rcases hgrant with ⟨tx0, hcur0, hreq0, hphase0, _, _, _, _⟩
          rw [hcur] at hcur0
          injection hcur0 with htx
          subst htx
          exact False.elim (hreqj hreq0.symm)
        · rcases hrel with ⟨htxnNone, _, _, _, _, _, _⟩
          rw [hcur] at htxnNone
          simp at htxnNone
        · exact Or.inr ⟨msg, rfl, hacc, hps⟩
  · specialize hchanE j
    cases hE : (s.locals j).chanE with
    | none => exact rfl
    | some _ =>
        rw [hE] at hchanE
        rcases hchanE with ⟨tx0, hcur0, hreq0, hphase0, _, _, _, _⟩
        rw [hcur] at hcur0
        injection hcur0 with htx
        subst htx
        exact False.elim (hreqj hreq0.symm)

end TileLink.Messages
