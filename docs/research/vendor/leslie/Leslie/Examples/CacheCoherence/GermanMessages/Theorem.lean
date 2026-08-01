import Leslie.Examples.CacheCoherence.GermanMessages.StepProof

namespace GermanMessages

inductive Reachable (n : Nat) : MState n → Prop where
  | init : ∀ s, init n s → Reachable n s
  | step : ∀ s s', Reachable n s → next n s s' → Reachable n s'

private theorem fullStrongInvariant_inductive (n : Nat) :
    ∀ s, Reachable n s → fullStrongInvariant n s := by
  intro s hr
  induction hr with
  | init s hs => exact init_fullStrongInvariant n s hs
  | step s s' _ hstep ih => exact fullStrongInvariant_preserved ih hstep

theorem germanMessages_invariant (n : Nat) :
    ∀ s, Reachable n s → invariant n s :=
  fun s hr => (fullStrongInvariant_inductive n s hr).1.1

end GermanMessages
