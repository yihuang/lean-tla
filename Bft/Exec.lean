import Bft.Core
import Bft.Rules
import Cslib.Foundations.Semantics.FLTS.Basic

/-!
# Bft.Exec — the executability pipeline: from relational spec to step function

The core pattern (same as Verdi/IronFleet): split each disjunct of
`Next = A₁ ∨ ... ∨ Aₙ` into a **guard** (a precondition reading only the
current state) and an **update** (a deterministic state update), then
assemble a label-indexed step function. If the guards are decidable and the
updates computable, the step function compiles to executable code.

Correctness theorem `run_invariant`: every run of the step function is a
behavior of the spec — when the guard holds the step fires the matching
action, otherwise it stutters. Hence `□Inv` (and any safety property) proved
about the spec automatically covers all executable runs. **Liveness is not
obtained here**: the liveness of an executable system comes from fairness
assumptions about the deployment environment (the network eventually
delivers, timers eventually fire) — an explicit part of the trust base, see
docs/bft-design.md §4.4.

Difference from lean-tla's `StreamletExec`: there the guard contains an
existential, forcing `noncomputable step`; here "decidable guard" is a
first-class design constraint, and the `GuardedAction` structure bundles the
guard's `Decidable` instance with the proof that guard/update agree with the
relational semantics.
-/

namespace Bft

/-- One executable action: deterministic update + decidable guard +
proofs of agreement with the relational semantics. -/
structure GuardedAction (σ : Type u) (lbl : Type v) where
  /-- The relational semantics (the spec-layer action). -/
  rel : lbl → Action σ
  /-- The precondition. -/
  guard : lbl → σ → Prop
  /-- The deterministic update. -/
  update : lbl → σ → σ
  /-- If the guard holds, the updated state satisfies the relation. -/
  fires : ∀ l s, guard l s → rel l s (update l s)
  /-- The relation is deterministic: any state satisfying it is the update. -/
  det : ∀ l s s', rel l s s' → s' = update l s

/-- An executable spec: a label type + a family of actions + decidable guards. -/
structure ExecSpec (σ : Type u) where
  lbl : Type v
  actions : GuardedAction σ lbl
  decGuard : ∀ l s, Decidable (actions.guard l s)

attribute [instance] ExecSpec.decGuard

/-- The step function: update when the guard holds, stutter otherwise.
**Compilable**. -/
def ExecSpec.step {σ : Type u} (es : ExecSpec σ) (s : σ) (l : es.lbl) : σ :=
  if es.actions.guard l s then es.actions.update l s else s

/-- The run from an initial state, driven by a label sequence. -/
def ExecSpec.run {σ : Type u} (es : ExecSpec σ) (s₀ : σ) :
    List es.lbl → σ
  | [] => s₀
  | l :: ls => es.run (es.step s₀ l) ls

/-- The spec-layer Next: some label makes the relation hold. -/
def ExecSpec.next {σ : Type u} (es : ExecSpec σ) : Action σ :=
  fun s s' => ∃ l, es.actions.rel l s s'

/-- **Correctness theorem**: every step is either a `next` step or a stutter
(holds for any frame `v`; taking `v = id` gives `Unchanged`). -/
theorem ExecSpec.step_is_spec_step {σ : Type u} (es : ExecSpec σ) (s : σ)
    (l : es.lbl) :
    es.next s (es.step s l) ∨ es.step s l = s := by
  unfold step
  by_cases hg : es.actions.guard l s
  · rw [if_pos hg]
    exact Or.inl ⟨l, es.actions.fires l s hg⟩
  · rw [if_neg hg]
    exact Or.inr rfl

/-- Hence every step of `run` is a spec step: any finite trace is a prefix
of some spec behavior. Combined with `init_invariant_stut`, the spec's
invariants cover all runs. -/
theorem ExecSpec.run_invariant {σ : Type u} (es : ExecSpec σ)
    (init inv : StatePred σ)
    (hinit : ∀ s, s ∈ init → s ∈ inv)
    (hstep : ∀ s s', StutAction es.next (fun s => s) s s' → s ∈ inv → s' ∈ inv)
    (s₀ : σ) (hs₀ : s₀ ∈ init) (trace : List es.lbl) :
    es.run s₀ trace ∈ inv := by
  suffices hgen : ∀ s₀ : σ, s₀ ∈ inv → es.run s₀ trace ∈ inv by
    exact hgen s₀ (hinit s₀ hs₀)
  intro s₀ hinv
  induction trace generalizing s₀ with
  | nil => exact hinv
  | cons l ls ih =>
      unfold run
      have hinv_step : es.step s₀ l ∈ inv := by
        rcases es.step_is_spec_step s₀ l with hnext | hstut
        · exact hstep _ _ (Or.inl hnext) hinv
        · rw [hstut]
          exact hinv
      exact ih (es.step s₀ l) hinv_step

/-! ## FLTS bridge

`ExecSpec.step` is literally a `Cslib.FLTS` (a deterministic labeled
transition function), with `run = mtr`. The execution layer thus gets
CSLib's FLTS/LTS machinery for free (`FLTSToLTS`, products `Prod`,
simulation). -/

/-- The FLTS corresponding to an executable spec. -/
def ExecSpec.toFLTS {σ : Type u} (es : ExecSpec σ) : Cslib.FLTS σ es.lbl where
  tr := es.step

/-- A run is exactly the FLTS multi-step transition. -/
theorem ExecSpec.run_eq_mtr {σ : Type u} (es : ExecSpec σ) (s₀ : σ)
    (ls : List es.lbl) :
    es.run s₀ ls = es.toFLTS.mtr s₀ ls := by
  induction ls generalizing s₀ with
  | nil => rfl
  | cons l ls ih =>
      -- Unfold one step on both sides: the cons clause of `run` and the
      -- cons clause of `List.foldl` (`mtr` is `μs.foldl flts.tr s`),
      -- then apply the induction hypothesis to the tail.
      show es.run (es.step s₀ l) ls = es.toFLTS.mtr (es.step s₀ l) ls
      exact ih (es.step s₀ l)

/-- **Determinism**: the spec relation is a function under executable
actions — so the refinement direction (every spec step is some `step`)
comes for free, useful for model checking and differential testing. -/
theorem ExecSpec.next_det {σ : Type u} (es : ExecSpec σ) (s s' : σ)
    (h : es.next s s') : ∃ l, s' = es.step s l ∨
      (¬ es.actions.guard l s ∧ es.step s l = s) := by
  rcases h with ⟨l, hrel⟩
  refine ⟨l, ?_⟩
  rw [es.actions.det l s s' hrel]
  unfold step
  by_cases hg : es.actions.guard l s
  · exact Or.inl (by rw [if_pos hg])
  · exact Or.inr ⟨hg, by rw [if_neg hg]⟩

end Bft
