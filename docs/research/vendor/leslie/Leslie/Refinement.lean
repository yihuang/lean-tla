import Leslie.Rules.Basic
import Leslie.Rules.StatePred
import Leslie.Tactics.Structural

/-! ## Refinement for TLA Specifications

    This file defines:
    - `Spec`: a TLA specification (init, next, fairness)
    - `exec.map`: mapping executions through a state function
    - `refines_via`: refinement between specifications via a mapping
    - The Abadi-Lamport refinement mapping theorem (safety)
    - Transitivity of refinement
    - Invariant-based refinement
-/

open Classical

namespace TLA

/-! ### Specifications -/

structure Spec (σ : Type u) where
  init : σ → Prop
  next : action σ
  fair : List (action σ) := []

def Spec.safety (spec : Spec σ) : pred σ :=
  [tlafml| ⌜ spec.init ⌝ ∧ □ ⟨spec.next⟩]

def Spec.formula (spec : Spec σ) : pred σ :=
  [tlafml| ⌜ spec.init ⌝ ∧ □ ⟨spec.next⟩ ∧ ⋀ a ∈ spec.fair, 𝒲ℱ a]

/-- The safety specification with stuttering: □[Next]_vars instead of □⟨Next⟩.
    This allows steps where the state doesn't change. -/
def Spec.safety_stutter (spec : Spec σ) : pred σ :=
  [tlafml| ⌜ spec.init ⌝ ∧ □ ⟨fun s s' => spec.next s s' ∨ s = s'⟩]

/-! ### Execution Mapping -/

def exec.map {σ : Type u} {τ : Type v} (f : σ → τ) (e : exec σ) : exec τ :=
  fun n => f (e n)

@[simp] theorem exec.map_apply {σ : Type u} {τ : Type v} (f : σ → τ) (e : exec σ) (n : Nat) :
    exec.map f e n = f (e n) := rfl

theorem exec.map_drop {σ : Type u} {τ : Type v} (f : σ → τ) (e : exec σ) (k : Nat) :
    (exec.map f e).drop k = exec.map f (e.drop k) := by
  funext n ; simp [exec.map, exec.drop]

theorem exec.map_comp {σ : Type u} {τ : Type v} {υ : Type w}
    (f : σ → τ) (g : τ → υ) (e : exec σ) :
    exec.map g (exec.map f e) = exec.map (g ∘ f) e := by
  funext n ; simp [exec.map]

/-! ### Refinement -/

/-- Concrete spec refines abstract spec via mapping `f`:
    every concrete behavior, mapped through `f`, is an abstract behavior. -/
def refines_via {σ : Type u} {τ : Type v}
    (f : σ → τ) (concrete : pred σ) (abstract : pred τ) : Prop :=
  ∀ e, concrete e → abstract (exec.map f e)

theorem refines_via_trans {σ : Type u} {τ : Type v} {υ : Type w}
    {f : σ → τ} {g : τ → υ} {p : pred σ} {q : pred τ} {r : pred υ}
    (h1 : refines_via f p q) (h2 : refines_via g q r) :
    refines_via (g ∘ f) p r := by
  intro e hp
  have hq := h1 e hp
  have hr := h2 (exec.map f e) hq
  rwa [exec.map_comp] at hr

/-! ### Helpers -/

/-- Extract `next (e k) (e (k+1))` from `□⟨next⟩`. -/
theorem always_action_at {σ : Type u} {next : action σ} {e : exec σ} (k : Nat)
    (h : e |=tla= □ ⟨next⟩) : next (e k) (e (k + 1)) := by
  have hk := h k
  simp [action_pred, exec.drop] at hk
  exact hk

/-- Key lemma: if every concrete step maps to an abstract step,
    then □⟨next_c⟩ on `e` implies □⟨next_a⟩ on `exec.map f e`. -/
private theorem map_always_next {σ : Type u} {τ : Type v}
    (next_c : action σ) (next_a : action τ)
    (f : σ → τ) (e : exec σ)
    (hn : e |=tla= □ ⟨next_c⟩)
    (hstep : ∀ s s', next_c s s' → next_a (f s) (f s')) :
    (exec.map f e) |=tla= □ ⟨next_a⟩ := by
  intro k
  rw [exec.map_drop]
  simp [action_pred, exec.drop, exec.map]
  exact hstep _ _ (always_action_at k hn)

private theorem map_always_next_or_stutter {σ : Type u} {τ : Type v}
    (next_c : action σ) (next_a : action τ)
    (f : σ → τ) (e : exec σ)
    (hn : e |=tla= □ ⟨next_c⟩)
    (hstep : ∀ s s', next_c s s' → next_a (f s) (f s') ∨ f s = f s') :
    (exec.map f e) |=tla= □ ⟨fun s s' => next_a s s' ∨ s = s'⟩ := by
  intro k
  rw [exec.map_drop]
  simp [action_pred, exec.drop, exec.map]
  exact hstep _ _ (always_action_at k hn)

/-- Variant with an invariant: the step condition may depend on an invariant. -/
private theorem map_always_next_inv {σ : Type u} {τ : Type v}
    (next_c : action σ) (next_a : action τ)
    (f : σ → τ) (e : exec σ)
    (inv : σ → Prop)
    (hinv : ∀ k, inv (e k))
    (hn : e |=tla= □ ⟨next_c⟩)
    (hstep : ∀ s s', inv s → next_c s s' → next_a (f s) (f s')) :
    (exec.map f e) |=tla= □ ⟨next_a⟩ := by
  intro k
  rw [exec.map_drop]
  simp [action_pred, exec.drop, exec.map]
  exact hstep _ _ (hinv k) (always_action_at k hn)

private theorem map_always_next_or_stutter_inv {σ : Type u} {τ : Type v}
    (next_c : action σ) (next_a : action τ)
    (f : σ → τ) (e : exec σ)
    (inv : σ → Prop)
    (hinv : ∀ k, inv (e k))
    (hn : e |=tla= □ ⟨next_c⟩)
    (hstep : ∀ s s', inv s → next_c s s' →
      next_a (f s) (f s') ∨ f s = f s') :
    (exec.map f e) |=tla= □ ⟨fun s s' => next_a s s' ∨ s = s'⟩ := by
  intro k
  rw [exec.map_drop]
  simp [action_pred, exec.drop, exec.map]
  exact hstep _ _ (hinv k) (always_action_at k hn)

/-! ### The Refinement Mapping Theorem (Safety, No Stuttering) -/

theorem refinement_mapping_nostutter {σ : Type u} {τ : Type v}
    (concrete : Spec σ) (abstract : Spec τ)
    (f : σ → τ)
    (hinit : ∀ s, concrete.init s → abstract.init (f s))
    (hnext : ∀ s s', concrete.next s s' → abstract.next (f s) (f s')) :
    refines_via f concrete.safety abstract.safety := by
  intro e ⟨hi, hn⟩
  exact ⟨hinit (e 0) hi, map_always_next _ _ f e hn hnext⟩

/-! ### The Refinement Mapping Theorem (Safety, With Stuttering) -/

theorem refinement_mapping_stutter {σ : Type u} {τ : Type v}
    (concrete : Spec σ) (abstract : Spec τ)
    (f : σ → τ)
    (hinit : ∀ s, concrete.init s → abstract.init (f s))
    (hnext : ∀ s s', concrete.next s s' →
      abstract.next (f s) (f s') ∨ f s = f s') :
    refines_via f concrete.safety abstract.safety_stutter := by
  intro e ⟨hi, hn⟩
  exact ⟨hinit (e 0) hi, map_always_next_or_stutter _ _ f e hn hnext⟩

/-! ### Refinement with Invariants -/

private theorem build_invariant {σ : Type u} {e : exec σ}
    {init : σ → Prop} {next : action σ} {inv : σ → Prop}
    (hi : e |=tla= ⌜ init ⌝) (hn : e |=tla= □ ⟨next⟩)
    (hinv_init : ∀ s, init s → inv s)
    (hinv_next : ∀ s s', inv s → next s s' → inv s') :
    ∀ k, inv (e k) := by
  intro k ; induction k with
  | zero => exact hinv_init _ hi
  | succ k ih => exact hinv_next _ _ ih (always_action_at k hn)

theorem refinement_mapping_with_invariant {σ : Type u} {τ : Type v}
    (concrete : Spec σ) (abstract : Spec τ)
    (f : σ → τ)
    (inv : σ → Prop)
    (hinv_init : ∀ s, concrete.init s → inv s)
    (hinv_next : ∀ s s', inv s → concrete.next s s' → inv s')
    (hinit : ∀ s, concrete.init s → abstract.init (f s))
    (hnext : ∀ s s', inv s → concrete.next s s' →
      abstract.next (f s) (f s')) :
    refines_via f concrete.safety abstract.safety := by
  intro e ⟨hi, hn⟩
  have hinv := build_invariant hi hn hinv_init hinv_next
  exact ⟨hinit (e 0) hi, map_always_next_inv _ _ f e _ hinv hn hnext⟩

theorem refinement_mapping_stutter_with_invariant {σ : Type u} {τ : Type v}
    (concrete : Spec σ) (abstract : Spec τ)
    (f : σ → τ)
    (inv : σ → Prop)
    (hinv_init : ∀ s, concrete.init s → inv s)
    (hinv_next : ∀ s s', inv s → concrete.next s s' → inv s')
    (hinit : ∀ s, concrete.init s → abstract.init (f s))
    (hnext : ∀ s s', inv s → concrete.next s s' →
      abstract.next (f s) (f s') ∨ f s = f s') :
    refines_via f concrete.safety abstract.safety_stutter := by
  intro e ⟨hi, hn⟩
  have hinv := build_invariant hi hn hinv_init hinv_next
  exact ⟨hinit (e 0) hi, map_always_next_or_stutter_inv _ _ f e _ hinv hn hnext⟩

/-! ### Safety and Safety-Stutter Relationship -/

/-- `safety` implies `safety_stutter`: every behavior satisfying Init ∧ □⟨Next⟩
    also satisfies Init ∧ □⟨Next ∨ id⟩. -/
theorem safety_implies_safety_stutter (spec : Spec σ) :
    pred_implies spec.safety spec.safety_stutter := by
  intro e ⟨hi, hn⟩
  exact ⟨hi, fun k => by have := hn k ; simp [action_pred, exec.drop] at * ; exact Or.inl this⟩

/-- Refinement mapping from `safety_stutter` to `safety_stutter`:
    if every concrete step (or stutter) maps to an abstract step or stutter,
    then stuttering safety refines stuttering safety. -/
theorem refinement_mapping_stutter_stutter {σ : Type u} {τ : Type v}
    (concrete : Spec σ) (abstract : Spec τ)
    (f : σ → τ)
    (hinit : ∀ s, concrete.init s → abstract.init (f s))
    (hnext : ∀ s s', concrete.next s s' →
      abstract.next (f s) (f s') ∨ f s = f s') :
    refines_via f concrete.safety_stutter abstract.safety_stutter := by
  intro e ⟨hi, hn⟩
  refine ⟨hinit (e 0) hi, ?_⟩
  intro k
  rw [exec.map_drop]
  simp only [action_pred, exec.drop, exec.map]
  have hk := hn k
  simp only [action_pred, exec.drop] at hk
  rcases hk with hstep | heq
  · exact hnext _ _ hstep
  · exact Or.inr (congrArg f heq)

/-! ### Refinement Preserves Safety Properties -/

theorem refines_preserves_invariant {σ : Type u} {τ : Type v}
    (f : σ → τ) (spec_c : Spec σ) (spec_a : Spec τ)
    (inv : τ → Prop)
    (href : refines_via f spec_c.safety spec_a.safety)
    (hinv : pred_implies spec_a.safety [tlafml| □ ⌜ inv ⌝]) :
    pred_implies spec_c.safety [tlafml| □ ⌜ inv ∘ f ⌝] := by
  intro e hc
  have ha := href e hc
  have hall := hinv _ ha
  intro k
  have hk := hall k
  rw [exec.map_drop] at hk
  simp [state_pred, exec.drop, exec.map, Function.comp] at *
  exact hk

theorem refines_stutter_preserves_invariant {σ : Type u} {τ : Type v}
    (f : σ → τ) (spec_c : Spec σ) (spec_a : Spec τ)
    (inv : τ → Prop)
    (href : refines_via f spec_c.safety spec_a.safety_stutter)
    (hinv : pred_implies spec_a.safety_stutter [tlafml| □ ⌜ inv ⌝]) :
    pred_implies spec_c.safety [tlafml| □ ⌜ inv ∘ f ⌝] := by
  intro e hc
  have ha := href e hc
  have hall := hinv _ ha
  intro k
  have hk := hall k
  rw [exec.map_drop] at hk
  simp [state_pred, exec.drop, exec.map, Function.comp] at *
  exact hk

/-! ### Reflexive Transitive Closure

    We define `Star r a b` as the reflexive transitive closure of a binary
    relation `r`: either `a = b` (zero steps), or there is an intermediate
    state `b` such that `r a b` and `Star r b c` (one-or-more steps). -/

/-- Reflexive transitive closure of a relation: zero or more `r`-steps. -/
inductive Star (r : α → α → Prop) : α → α → Prop where
  | refl : Star r a a
  | step : r a b → Star r b c → Star r a c

/-- A single `r`-step is a `Star r`-step. -/
theorem Star.single {r : α → α → Prop} (h : r a b) : Star r a b :=
  .step h .refl

/-- `Star r` is transitive: concatenation of two multi-step paths. -/
theorem Star.trans {r : α → α → Prop} (h1 : Star r a b) (h2 : Star r b c) : Star r a c := by
  induction h1 with
  | refl => exact h2
  | step hab _ ih => exact .step hab (ih h2)

/-- An invariant preserved by each `r`-step is preserved by `Star r`. -/
theorem Star.preserve_inv {r : α → α → Prop} {inv : α → Prop}
    (hinv : ∀ a b, inv a → r a b → inv b) {a b : α}
    (h : Star r a b) (ha : inv a) : inv b := by
  induction h with
  | refl => exact ha
  | step hab _ ih => exact ih (hinv _ _ ha hab)

/-! ### Forward Simulation via Relations

    A **forward simulation** (also called a **simulation relation**)
    generalizes refinement mappings.  Instead of a function `f : σ → τ`,
    we use a relation `R : σ → τ → Prop` between the concrete state space
    `σ` and the abstract state space `τ`.

    This extra generality is needed when:
    - The abstract state involves **nondeterministic** choices that cannot be
      expressed as a deterministic function of the concrete state (e.g. the
      set of accumulated snapshots in a snapshot object).
    - One concrete step must be simulated by a **sequence** of abstract steps
      (not just zero or one), expressed via `Star abstract.next`.

    **Conditions** (`SimulationRel`):
    1. *Init*: every concrete initial state has a related abstract initial state.
    2. *Step*: for every concrete step `s → s'` and abstract state `a` with
       `R s a`, there exists `a'` reachable from `a` via zero or more abstract
       steps (`Star abstract.next a a'`) such that `R s' a'`. -/

/-- A forward simulation relation between two TLA specs.
    Each concrete step is simulated by zero or more abstract steps. -/
structure SimulationRel (σ : Type u) (τ : Type v) where
  concrete : Spec σ
  abstract : Spec τ
  /-- The simulation relation between concrete and abstract states. -/
  R : σ → τ → Prop
  /-- Every concrete initial state has a related abstract initial state. -/
  init_sim : ∀ s, concrete.init s → ∃ a, abstract.init a ∧ R s a
  /-- Every concrete step from a related pair produces a related pair,
      with the abstract side taking zero or more steps. -/
  step_sim : ∀ s s' a, R s a → concrete.next s s' →
    ∃ a', Star abstract.next a a' ∧ R s' a'

/-- Build the abstract state witness at each concrete step `k`, by recursion.
    At step 0 we pick a witness from `init_sim`, and at step `k+1` we apply
    `step_sim` to the previous witness. Each witness is bundled with a proof
    that `R` relates the concrete state `e k` to it.  -/
private noncomputable def SimulationRel.build
    (sim : SimulationRel σ τ)
    (e : exec σ)
    (hinit : sim.concrete.init (e 0))
    (hnext : ∀ k, sim.concrete.next (e k) (e (k + 1)))
    : (k : Nat) → { a : τ // sim.R (e k) a }
  | 0 =>
    ⟨(sim.init_sim (e 0) hinit).choose,
     (sim.init_sim (e 0) hinit).choose_spec.2⟩
  | k + 1 =>
    let prev := sim.build e hinit hnext k
    let hex := sim.step_sim (e k) (e (k + 1)) prev.val prev.property (hnext k)
    ⟨hex.choose, hex.choose_spec.2⟩

/-- **Invariant transfer**: a simulation lets us transfer inductive invariants
    from the abstract spec to the concrete spec.

    If `inv` is an inductive invariant of the abstract (preserved by `init`
    and `next`), and `R s a ∧ inv a → P s`, then `P` is an invariant of the
    concrete.  This is the primary use of `SimulationRel`.

    The proof works by constructing a related abstract state at each concrete
    step (via `build`) and then showing, by induction, that `inv` holds at
    every abstract witness.  Because each concrete step may correspond to
    *multiple* abstract steps, the inductive step uses `Star.preserve_inv`
    to push `inv` through the entire multi-step abstract path. -/
theorem SimulationRel.preserves_invariant
    (sim : SimulationRel σ τ)
    (inv : τ → Prop)
    (hinv_init : ∀ a, sim.abstract.init a → inv a)
    (hinv_next : ∀ a a', inv a → sim.abstract.next a a' → inv a')
    (P : σ → Prop)
    (hRP : ∀ s a, sim.R s a → inv a → P s)
    : pred_implies sim.concrete.safety [tlafml| □ ⌜ P ⌝] := by
  intro e ⟨hinit, hnext⟩
  have hnext' : ∀ k, sim.concrete.next (e k) (e (k + 1)) :=
    fun k => always_action_at k hnext
  let build_k := sim.build e hinit hnext'
  -- It suffices to show the abstract invariant at every concrete step.
  suffices h : ∀ k, inv (build_k k).val from by
    intro k ; simp [state_pred, exec.drop]
    exact hRP _ _ (build_k k).property (h k)
  intro k ; induction k with
  | zero => exact hinv_init _ (sim.init_sim (e 0) hinit).choose_spec.1
  | succ k ih =>
    let prev := build_k k
    let hex := sim.step_sim (e k) (e (k + 1)) prev.val prev.property (hnext' k)
    -- The Star path from prev to hex.choose preserves inv:
    exact Star.preserve_inv hinv_next hex.choose_spec.1 ih

/-- **Full soundness** (statement only): a simulation implies that every
    concrete execution has a corresponding abstract execution satisfying
    `safety_stutter`, with a monotone time-mapping `f` such that states are
    related at corresponding points.

    The proof requires flattening the variable-length abstract step sequences
    into a single infinite execution. -/
theorem SimulationRel.soundness
    (sim : SimulationRel σ τ)
    : ∀ e, sim.concrete.safety e →
        ∃ ea, sim.abstract.safety_stutter ea ∧
          ∃ f : Nat → Nat, (∀ k, f k ≤ f (k + 1)) ∧ ∀ k, sim.R (e k) (ea (f k)) := by
  sorry

/-! ### Simulation with Concrete Invariant

    Sometimes the step-simulation condition only holds under an invariant
    on the *concrete* state (e.g. "versions are monotonic").
    `SimulationRelInv` lets us supply such an invariant alongside the
    simulation relation. -/

/-- Forward simulation with an auxiliary concrete invariant. -/
structure SimulationRelInv (σ : Type u) (τ : Type v) where
  concrete : Spec σ
  abstract : Spec τ
  R : σ → τ → Prop
  inv : σ → Prop
  inv_init : ∀ s, concrete.init s → inv s
  inv_next : ∀ s s', inv s → concrete.next s s' → inv s'
  init_sim : ∀ s, concrete.init s → ∃ a, abstract.init a ∧ R s a
  step_sim : ∀ s s' a, inv s → R s a → concrete.next s s' →
    ∃ a', Star abstract.next a a' ∧ R s' a'

/-- Fold the concrete invariant into the relation to obtain a plain
    `SimulationRel`. The new relation is `fun s a => inv s ∧ R s a`. -/
noncomputable def SimulationRelInv.toSimulationRel
    (sim : SimulationRelInv σ τ) : SimulationRel σ τ where
  concrete := sim.concrete
  abstract := sim.abstract
  R := fun s a => sim.inv s ∧ sim.R s a
  init_sim := fun s hs => by
    obtain ⟨a, ha, hr⟩ := sim.init_sim s hs
    exact ⟨a, ha, sim.inv_init s hs, hr⟩
  step_sim := fun s s' a ⟨hinv, hr⟩ hstep => by
    obtain ⟨a', haa', hr'⟩ := sim.step_sim s s' a hinv hr hstep
    exact ⟨a', haa', sim.inv_next s s' hinv hstep, hr'⟩

/-- Invariant transfer for `SimulationRelInv` (delegates to `SimulationRel`). -/
theorem SimulationRelInv.preserves_invariant
    (sim : SimulationRelInv σ τ)
    (inv_a : τ → Prop)
    (hinv_init : ∀ a, sim.abstract.init a → inv_a a)
    (hinv_next : ∀ a a', inv_a a → sim.abstract.next a a' → inv_a a')
    (P : σ → Prop)
    (hRP : ∀ s a, sim.R s a → inv_a a → P s)
    : pred_implies sim.concrete.safety [tlafml| □ ⌜ P ⌝] := by
  apply sim.toSimulationRel.preserves_invariant inv_a hinv_init hinv_next P
  intro s a ⟨_, hr⟩ hinv
  exact hRP s a hr hinv

/-! ### Backward Simulation via Relations

    A **backward simulation** reverses the quantifier order compared to
    a forward simulation: instead of "for every abstract pre-state `a`
    related to `s`, find a post-state `a'`," we say "for every abstract
    *post-state* `a'` related to `s'`, find a pre-state `a`."

    Backward simulations are useful when the linearization point of an
    operation is determined only *after* the operation completes (e.g.
    the successful `cmp_eq` in a double-collect snapshot determines that
    the linearization point was some earlier step).

    **Conditions** (`BackwardSimulationRel`):
    1. *Init*: every concrete initial state has a related abstract initial state.
    2. *Step* (backwards): for every concrete step `s → s'` and abstract
       state `a'` with `R s' a'`, there exists `a` with `R s a` such that
       `Star abstract.next a a'` (the abstract reaches `a'` from `a`
       in zero or more steps). -/

/-- A backward simulation relation between two TLA specs. -/
structure BackwardSimulationRel (σ : Type u) (τ : Type v) where
  concrete : Spec σ
  abstract : Spec τ
  /-- The simulation relation between concrete and abstract states. -/
  R : σ → τ → Prop
  /-- Every concrete initial state has a related abstract initial state. -/
  init_sim : ∀ s, concrete.init s → ∃ a, abstract.init a ∧ R s a
  /-- Backwards step condition: given a concrete step `s → s'` and an
      abstract post-state `a'` related to `s'`, find a pre-state `a`
      related to `s` from which the abstract can reach `a'`. -/
  step_sim : ∀ s s' a', R s' a' → concrete.next s s' →
    ∃ a, Star abstract.next a a' ∧ R s a

/-- Invariant transfer for backward simulations. -/
theorem BackwardSimulationRel.preserves_invariant
    (sim : BackwardSimulationRel σ τ)
    (inv : τ → Prop)
    (hinv_init : ∀ a, sim.abstract.init a → inv a)
    (hinv_next : ∀ a a', inv a → sim.abstract.next a a' → inv a')
    (P : σ → Prop)
    (hRP : ∀ s a, sim.R s a → inv a → P s)
    : pred_implies sim.concrete.safety [tlafml| □ ⌜ P ⌝] := by
  intro e ⟨hinit, hnext⟩
  have hnext' : ∀ k, sim.concrete.next (e k) (e (k + 1)) :=
    fun k => always_action_at k hnext
  -- Build abstract states backwards: at each step k, pick a_k related to e(k)
  -- such that Star next a_k a_{k+1}.
  -- We build by reverse induction: start from the initial state and propagate.
  -- Actually, we build forward: at step 0 pick a_0 from init_sim.
  -- At step k+1: we have a_k with R (e k) a_k.  The concrete takes a step
  -- e(k) → e(k+1).  We need a_{k+1} with R (e(k+1)) a_{k+1}.
  -- BUT the backward sim gives us: given a' with R (e(k+1)) a', find a with R (e k) a.
  -- This is the wrong direction for forward construction!
  --
  -- The standard approach: backward simulations preserve invariants under the
  -- assumption that every reachable concrete state has SOME related abstract state.
  -- We prove this by induction using step_sim applied in the correct direction.
  --
  -- Alternative: build the abstract witness sequence starting from e(0).
  -- At each step, we use step_sim "backwards" to ensure consistency.
  -- For invariant preservation, it suffices to show ∀ k, ∃ a, R (e k) a ∧ inv a.
  suffices h : ∀ k, ∃ a, sim.R (e k) a ∧ inv a from by
    intro k; simp [state_pred, exec.drop]
    obtain ⟨a, hr, hinv_a⟩ := h k
    exact hRP _ _ hr hinv_a
  intro k; induction k with
  | zero =>
    obtain ⟨a, ha_init, hr⟩ := sim.init_sim (e 0) hinit
    exact ⟨a, hr, hinv_init _ ha_init⟩
  | succ k ih =>
    obtain ⟨a_k1, hr_k1, hinv_k1⟩ := ih
    -- We have a_{k} with R (e k) a_{k} and inv a_{k}.
    -- We need a_{k+1} with R (e(k+1)) a_{k+1} and inv a_{k+1}.
    -- Use step_sim: we need an a' with R (e(k+1)) a'. But we don't have one yet!
    -- This is the circularity of backward simulation for invariant preservation.
    -- The standard resolution: backward simulations preserve invariants
    -- when combined with the assumption that R is "total on reachable states"
    -- (every reachable concrete state has some related abstract state).
    -- For now, we sorry this and note that the backward simulation itself is
    -- the main contribution; invariant transfer requires additional machinery.
    sorry

end TLA
