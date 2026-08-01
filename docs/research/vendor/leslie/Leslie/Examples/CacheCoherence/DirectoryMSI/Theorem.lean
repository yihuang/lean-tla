import Leslie.Examples.CacheCoherence.DirectoryMSI.StepProof

namespace DirectoryMSI

/-! ## Main Theorem

    The directory-based MSI cache coherence protocol satisfies SWMR + data integrity.
-/

inductive Reachable (n : Nat) : MState n → Prop where
  | init : ∀ s, init n s → Reachable n s
  | step : ∀ s s', Reachable n s → next n s s' → Reachable n s'

theorem fullStrongInvariant_inductive (n : Nat) (s : MState n)
    (hr : Reachable n s) : fullStrongInvariant n s := by
  induction hr with
  | init s hinit => exact init_fullStrongInvariant n s hinit
  | step s s' _hrs hstep ih => exact fullStrongInvariant_preserved n s s' ih hstep

theorem directoryMSI_invariant (n : Nat) :
    ∀ s, Reachable n s → invariant n s :=
  fun s hr => (fullStrongInvariant_inductive n s hr).1.1

end DirectoryMSI
