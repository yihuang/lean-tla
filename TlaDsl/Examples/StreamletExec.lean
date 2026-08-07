import TlaDsl.Examples.Streamlet
import TlaDsl.LTSRefine
import Cslib.Foundations.Semantics.FLTS.FLTSToLTS

open scoped Tla

/-! # Streamlet is runnable: an executable step function

The roadmap's E1/E3 item: Streamlet's `Next` is a guarded disjunction of
`Vote`/`Notarize` steps, so it is a label-indexed deterministic step
function. A label is one protocol step (`Vote i b` or `Notarize b`); the
step function applies the update when the action's guard holds and is the
identity (a stutter) otherwise. Then every FLTS transition is a
`[Next n]_vars`-step of the spec — every `foldl` run of the step function
is a protocol behavior.

This is the same pattern as `RefinementLivenessLTS.lean`'s counter, at
the flagship protocol's scale: one label type per action, one guard, one
update — and the "is a behavior" theorem follows from the action
semantics, not a separate operational model.
-/

namespace TlaDsl.Examples.Streamlet

/-! ## The guards and updates -/

/-- The guard of `Vote i b`: the protocol's vote rule, without the frame
updates. -/
def VoteGuard (s : St) (i : Node) (b : Block) : Prop :=
  0 < b.epoch ∧ s.votes i b.epoch = none ∧
  (∀ e' : Epoch, b.epoch < e' → s.votes i e' = none) ∧
  s.seen i (b.length - 1) ∧
  (∀ k : Nat, s.seen i k → k ≤ b.length - 1)

/-- The update of `Vote i b`: record the vote. -/
def voteStep (s : St) (i : Node) (b : Block) : St :=
  { s with votes := Function.update s.votes i (Function.update (s.votes i) b.epoch (some b)) }

/-- The guard of `Notarize b`: a quorum has voted for `b`. -/
def NotarizeGuard (n : Nat) (s : St) (b : Block) : Prop :=
  ∃ Q : Finset Node, Quorum n Q ∧ (∀ i : Node, i ∈ Q → s.votes i b.epoch = some b)

/-- The update of `Notarize b`: `b`'s length becomes seen. -/
def notarizeStep (s : St) (b : Block) : St :=
  { s with seen := fun j k => s.seen j k ∨ k = b.length }

/-! ## The action equals the step function under the guard -/

lemma vote_step_fires (s : St) (i : Node) (b : Block) (hg : VoteGuard s i b) :
    Vote i b s (voteStep s i b) := by
  tla_unfold
  simp [voteStep, VoteGuard] at hg ⊢
  exact hg

lemma vote_step_det (s s' : St) (i : Node) (b : Block) (hs' : Vote i b s s') :
    s' = voteStep s i b := by
  tla_unfold
  cases s' with
  | mk votes' seen' =>
      cases s with
      | mk votes0 seen0 =>
          have hv : votes' = Function.update votes0 i (Function.update (votes0 i) b.epoch (some b)) :=
            hs'.2.2.2.2.2.1
          have hseen : seen' = seen0 := hs'.2.2.2.2.2.2
          simp [voteStep, hv, hseen]

lemma notarize_step_fires (n : Nat) (s : St) (b : Block) (hg : NotarizeGuard n s b) :
    Notarize n b s (notarizeStep s b) := by
  tla_unfold
  simp [notarizeStep, NotarizeGuard] at hg ⊢
  exact hg

lemma notarize_step_det (n : Nat) (s s' : St) (b : Block) (hs' : Notarize n b s s') :
    s' = notarizeStep s b := by
  tla_unfold
  cases s' with
  | mk votes' seen' =>
      cases s with
      | mk votes0 seen0 =>
          have hseen : seen' = fun j k => seen0 j k ∨ k = b.length := hs'.2.1
          have hv : votes' = votes0 := hs'.2.2
          simp [notarizeStep, hseen, hv]

/-! ## The step function and its LTS -/

/-- One protocol step: a vote or a notarization. -/
inductive Step where
  | vote (i : Node) (b : Block)
  | notarize (b : Block)

/-- The deterministic step function: apply the update if the guard holds,
stutter otherwise. -/
noncomputable def step (n : Nat) (s : St) : Step → St := by
  classical
  exact fun
    | .vote i b => if VoteGuard s i b then voteStep s i b else s
    | .notarize b => if NotarizeGuard n s b then notarizeStep s b else s

/-- The executable FLTS of Streamlet: one label per protocol step. -/
noncomputable def flts (n : Nat) : Cslib.FLTS St Step where
  tr := fun s l => step n s l

/-- Every FLTS transition is a `[Next n]_vars`-step of the spec: under the
guard the update fires the action, and without it the step is a stutter. -/
lemma step_spec_tr (n : Nat) (s : St) (l : Step) :
    (Tla.SpecLTS (Next n) vars).Tr s () (step n s l) := by
  cases l with
  | vote i b =>
      by_cases hg : VoteGuard s i b
      · -- the guard holds: the step is a Vote step
        have hstep : step n s (.vote i b) = voteStep s i b := by simp [step, hg]
        rw [hstep]
        simp [Tla.SpecLTS, Cslib.LTS.Relation.toLTS, Tla.StutAction]
        left
        refine ⟨i, b, Or.inl (vote_step_fires s i b hg)⟩
      · -- the guard fails: the step is the identity, a stutter
        have hstep : step n s (.vote i b) = s := by simp [step, hg]
        rw [hstep]
        simp [Tla.SpecLTS, Cslib.LTS.Relation.toLTS, Tla.StutAction]
  | notarize b =>
      by_cases hg : NotarizeGuard n s b
      · -- the guard holds: the step is a Notarize step
        have hstep : step n s (.notarize b) = notarizeStep s b := by simp [step, hg]
        rw [hstep]
        simp [Tla.SpecLTS, Cslib.LTS.Relation.toLTS, Tla.StutAction]
        left
        refine ⟨0, b, Or.inr (notarize_step_fires n s b hg)⟩
      · -- the guard fails: the step is the identity, a stutter
        have hstep : step n s (.notarize b) = s := by simp [step, hg]
        rw [hstep]
        simp [Tla.SpecLTS, Cslib.LTS.Relation.toLTS, Tla.StutAction]

end TlaDsl.Examples.Streamlet
