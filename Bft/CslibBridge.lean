import Bft.Core
import Cslib.Foundations.Data.OmegaSequence.InfOcc
import Cslib.Foundations.Semantics.LTS.OmegaExecution

/-!
# Bft.CslibBridge — bridges to the existing CSLib layers

Research conclusion (docs/bft-design.md §2.2): CSLib already has three layers
that interface directly with this library — bridge them, don't rebuild them:

1. **`ωSequence.Temporal`** (`Step`/`LeadsTo`, pointwise + grind-annotated):
   the **state-level fragment** of this library's DSL is literally equivalent
   to it. Certificate-engine conclusions (`RelRankCert`) translate losslessly
   into `LeadsTo`; this is the shape of the upstream interface.
2. **`ωSequence.infOcc` / `∃ᶠ k in atTop`**: the "infinitely often enabled"
   of `SF`.
3. **`LTS.OmegaExecution` / `FLTS`**: the step function of the execution
   layer (`Bft.Exec`) is an `FLTS`, with `run = mtr`; a spec's behaviors are
   the `OmegaExecution`s of an implicit LTS (with `Unit` labels).
-/

namespace Bft

open Cslib Set Filter

/-! ## 1. State-level leads-to is equivalent to CSLib `LeadsTo` -/

/-- `leadsTo ⌜p⌝ ⌜q⌝` holds on a behavior `e` iff CSLib's
`e.LeadsTo {s | p s} {s | q s}` does. This connects certificate conclusions
to CSLib's grind-annotated API (`step_leadsTo`, `leadsTo_trans`,
`until_frequently_leadsTo_and`, etc. are directly reusable). -/
theorem leadsTo_statePred_iff {σ : Type u} (p q : StatePred σ) (e : Behavior σ) :
    leadsTo (statePred p) (statePred q) e ↔
      e.LeadsTo {s | p s} {s | q s} := by
  simp [leadsTo, always, tlaImp, eventually, statePred, Cslib.ωSequence.LeadsTo]
  constructor
  · intro h k hpk
    rcases h k hpk with ⟨m, hm⟩
    exact ⟨k + m, Nat.le_add_right k m, hm⟩
  · intro h k hpk
    rcases h k hpk with ⟨k', hk', hq⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk'
    exact ⟨m, hq⟩

/-- `Step` is CSLib's form of "single-step implication": same shape as the
step obligation of inductive-invariant proofs. -/
theorem step_iff {σ : Type u} (p q : StatePred σ) (e : Behavior σ) :
    e.Step {s | p s} {s | q s} ↔ ∀ k, p (e k) → q (e (k + 1)) :=
  Iff.rfl

/-! ## 2. SF and `∃ᶠ` -/

/-- The filter form of "infinitely often enabled" is equivalent to
`□◇ Enabled`. -/
theorem always_eventually_enabled_iff_frequently {σ : Type u} {α : Type v}
    (A : Action σ) (v : σ → α) (e : Behavior σ) :
    (always (eventually (statePred (Enabled (AngleAction A v))))) e ↔
      ∃ᶠ k in atTop, Enabled (AngleAction A v) (e k) := by
  simp [always, eventually, statePred, frequently_atTop]
  constructor
  · intro h m
    rcases h m with ⟨k, hk⟩
    exact ⟨m + k, Nat.le_add_right m k, hk⟩
  · intro h m
    rcases h m with ⟨k, hmk, hk⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmk
    exact ⟨d, hk⟩

/-! Hence `SF_v` can be stated as `∃ᶠ enabled → □◇ fires`. This is the
interface to the `infOcc` machinery (pigeonhole, strictMono extraction). -/

/-! ## 3. Behaviors as infinite executions of an LTS -/

/-- An action `next` generates an LTS with `Unit` labels. -/
def Action.toLTS {σ : Type u} (next : Action σ) : Cslib.LTS σ Unit where
  Tr s _ s' := next s s'

/-- `□⟨next⟩ e` iff `e` is an infinite execution of `next.toLTS`. This
connects a spec's transition structure to CSLib's LTS machinery
(simulation, bisimulation, trace equivalence). -/
theorem always_actionPred_iff_omegaExecution {σ : Type u} (next : Action σ)
    (e : Behavior σ) :
    (always (actionPred next)) e ↔
      (Action.toLTS next).OmegaExecution e (Cslib.ωSequence.const ()) := by
  simp [always, actionPred, Cslib.LTS.OmegaExecution, Action.toLTS]

end Bft
