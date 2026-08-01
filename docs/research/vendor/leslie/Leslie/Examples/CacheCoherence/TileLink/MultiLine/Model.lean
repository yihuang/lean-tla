import Leslie.Gadgets.ProductSpec
import Leslie.Examples.CacheCoherence.TileLink.Messages.Refinement.AccessPath

/-! ## Multi-Line TileLink Model

    The multi-line model is a product of `numAddrs` independent copies
    of the single-line message model. Each address runs the full TileLink
    protocol independently.

    This is a conservative abstraction: in real TileLink, channels are
    shared across addresses. The product gives each address its own
    channels, which allows MORE behaviors than the real system. Safety
    proved for the product therefore implies safety for the real system.
-/

namespace TileLink.MultiLine

open TLA SymShared TileLink.Messages ProductSpec

/-- Multi-line TileLink: `numAddrs` independent copies of the single-line model. -/
def tlMultiLine (numAddrs n : Nat) : Spec (Fin numAddrs → SymState HomeState NodeState n) :=
  product ((tlMessages.toSpec n)) numAddrs

/-- Per-address refinement invariant is an invariant of the multi-line model. -/
theorem multi_line_refinementInv (numAddrs n : Nat) (addr : Fin numAddrs) :
    pred_implies (tlMultiLine numAddrs n).safety
      [tlafml| □ ⌜ fun s => refinementInv n (s addr) ⌝] := by
  apply product_invariant_lift
  · intro s hinit
    exact init_refinementInv n s hinit
  · intro s s' hrefInv hnext
    exact refinementInv_preserved n s s' hrefInv hnext

/-- Per-address read coherence: a readable node at any address returns
    the logical value for that address. -/
theorem multi_line_read_coherence (numAddrs n : Nat) (addr : Fin numAddrs)
    (i : Fin n) :
    pred_implies (tlMultiLine numAddrs n).safety
      [tlafml| □ ⌜ fun s =>
        ForwardSimInv n (s addr) →
        (s addr |>.locals i).line.perm.allowsRead →
        (s addr |>.locals i).line.valid = true →
        (s addr |>.shared.currentTxn = none) →
        (s addr |>.locals i).releaseInFlight = false →
        (s addr |>.locals i).line.data = (refMap n (s addr)).shared.mem ⌝] := by
  apply product_invariant_lift
  · intro s hinit
    intro hfwd hperm hvalid htxn hflight
    exact read_returns_logical_data hfwd hperm hvalid htxn hflight
  · intro s s' hP hnext
    intro hfwd hperm hvalid htxn hflight
    exact read_returns_logical_data hfwd hperm hvalid htxn hflight

end TileLink.MultiLine
