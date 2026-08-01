import Leslie.Examples.CacheCoherence.TileLink.Messages.InvariantSerialization

namespace TileLink.Messages

open TileLink SymShared

def fullInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  coreInv n s ∧ channelInv n s ∧ serializationInv n s

theorem init_fullInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → fullInv n s := by
  intro s hinit
  exact ⟨init_coreInv n s hinit, init_channelInv n s hinit, init_serializationInv n s hinit⟩

end TileLink.Messages
