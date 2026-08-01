import Leslie.Refinement

/-! ## Gated Atomic Actions and Multi-Action Specifications

    This file defines:
    - `GatedAction`: an action with an explicit gate (precondition) and transition
    - `ActionSpec`: a specification with multiple named actions (indexed by `ι`)
    - Conversion to `Spec` and `action`
    - Action refinement: proving a concrete gated action refines an abstract one
    - Composition of action specs
-/

open Classical

namespace TLA

/-! ### Gated Atomic Actions -/

/-- A gated atomic action has an explicit precondition (gate) and a
    two-state transition relation (effect). The action fires only when
    the gate holds. -/
structure GatedAction (σ : Type u) where
  gate : σ → Prop
  transition : action σ

/-- The action fires: gate holds in pre-state and transition relates pre to post. -/
def GatedAction.fires (a : GatedAction σ) : action σ :=
  fun s s' => a.gate s ∧ a.transition s s'

/-- An action is enabled if the gate holds and some successor exists. -/
def GatedAction.is_enabled (a : GatedAction σ) (s : σ) : Prop :=
  a.gate s ∧ ∃ s', a.transition s s'

/-- Convert a gated action to a plain TLA action. -/
def GatedAction.toAction (a : GatedAction σ) : action σ := a.fires

/-- A gated action with no precondition (gate is always true). -/
def GatedAction.unguarded (t : action σ) : GatedAction σ where
  gate := fun _ => True
  transition := t

theorem GatedAction.unguarded_fires (t : action σ) :
    (GatedAction.unguarded t).fires = fun s s' => True ∧ t s s' := rfl

/-- Enabled for a gated action agrees with TLA enabled for the fired action. -/
theorem GatedAction.enabled_iff (a : GatedAction σ) (s : σ) :
    enabled a.toAction s ↔ a.is_enabled s := by
  simp [enabled, toAction, fires, is_enabled]

/-! ### Multi-Action Specifications -/

/-- A specification with multiple named actions, indexed by type `ι`.
    Each action is a gated atomic action. The overall next relation
    is the disjunction of all actions firing. -/
structure ActionSpec (σ : Type u) (ι : Type v) where
  init : σ → Prop
  actions : ι → GatedAction σ
  fair : List ι := []

/-- The overall next-state relation: some action fires. -/
def ActionSpec.next (spec : ActionSpec σ ι) : action σ :=
  fun s s' => ∃ i, (spec.actions i).fires s s'

/-- Convert an `ActionSpec` to a plain `Spec`. -/
def ActionSpec.toSpec (spec : ActionSpec σ ι) : Spec σ where
  init := spec.init
  next := spec.next
  fair := spec.fair.map (fun i => (spec.actions i).toAction)

/-- The safety formula of an `ActionSpec`. -/
def ActionSpec.safety (spec : ActionSpec σ ι) : pred σ :=
  spec.toSpec.safety

/-- The full formula with fairness. -/
def ActionSpec.formula (spec : ActionSpec σ ι) : pred σ :=
  spec.toSpec.formula

/-! ### Action Refinement -/

/-- A single concrete gated action refines an abstract gated action under
    mapping `f`: whenever the concrete action fires, either the abstract
    action fires on the mapped states, or the mapped state doesn't change. -/
def GatedAction.refines_action (f : σ → τ)
    (concrete : GatedAction σ) (abstract : GatedAction τ) : Prop :=
  ∀ s s', concrete.fires s s' →
    abstract.fires (f s) (f s') ∨ f s = f s'

/-- Stronger: the concrete action always maps to an abstract step (no stutter). -/
def GatedAction.refines_action_nostutter (f : σ → τ)
    (concrete : GatedAction σ) (abstract : GatedAction τ) : Prop :=
  ∀ s s', concrete.fires s s' → abstract.fires (f s) (f s')

/-! ### ActionSpec Refinement -/

/-- An `ActionSpec` refinement: each concrete action refines the corresponding
    abstract action (or stutters). -/
structure ActionSpecRefinement (σ : Type u) (τ : Type v) (ι : Type w) where
  concrete : ActionSpec σ ι
  abstract : ActionSpec τ ι
  mapping : σ → τ
  init_preserved : ∀ s, concrete.init s → abstract.init (mapping s)
  action_refines : ∀ i s s', (concrete.actions i).fires s s' →
    (abstract.actions i).fires (mapping s) (mapping s') ∨ mapping s = mapping s'

/-- An `ActionSpecRefinement` implies a `refines_via` on the safety formulas. -/
theorem ActionSpecRefinement.to_refines_via (r : ActionSpecRefinement σ τ ι) :
    refines_via r.mapping r.concrete.safety r.abstract.toSpec.safety_stutter := by
  apply refinement_mapping_stutter r.concrete.toSpec r.abstract.toSpec
  · exact r.init_preserved
  · intro s s' ⟨i, hfire⟩
    have := r.action_refines i s s' hfire
    rcases this with habs | hstutter
    · left ; exact ⟨i, habs⟩
    · right ; exact hstutter

/-- Variant with an invariant. -/
structure ActionSpecRefinementInv (σ : Type u) (τ : Type v) (ι : Type w) where
  concrete : ActionSpec σ ι
  abstract : ActionSpec τ ι
  mapping : σ → τ
  inv : σ → Prop
  inv_init : ∀ s, concrete.init s → inv s
  inv_next : ∀ i s s', inv s → (concrete.actions i).fires s s' → inv s'
  init_preserved : ∀ s, concrete.init s → abstract.init (mapping s)
  action_refines : ∀ i s s', inv s → (concrete.actions i).fires s s' →
    (abstract.actions i).fires (mapping s) (mapping s') ∨ mapping s = mapping s'

theorem ActionSpecRefinementInv.to_refines_via (r : ActionSpecRefinementInv σ τ ι) :
    refines_via r.mapping r.concrete.safety r.abstract.toSpec.safety_stutter := by
  apply refinement_mapping_stutter_with_invariant
    r.concrete.toSpec r.abstract.toSpec r.mapping r.inv
  · exact r.inv_init
  · intro s s' hinv ⟨i, hfire⟩
    exact r.inv_next i s s' hinv hfire
  · exact r.init_preserved
  · intro s s' hinv ⟨i, hfire⟩
    have := r.action_refines i s s' hinv hfire
    rcases this with habs | hstutter
    · left ; exact ⟨i, habs⟩
    · right ; exact hstutter

/-! ### Helpers for building ActionSpecs -/

/-- Build an `ActionSpec` from a list of gated actions. -/
def ActionSpec.fromList (init : σ → Prop)
    (actions : List (GatedAction σ))
    (fair : List (Fin actions.length) := []) : ActionSpec σ (Fin actions.length) where
  init := init
  actions := fun i => actions[i]
  fair := fair

/-- Strengthen the gate of an action with an additional precondition. -/
def GatedAction.strengthen_gate (a : GatedAction σ) (p : σ → Prop) : GatedAction σ where
  gate := fun s => a.gate s ∧ p s
  transition := a.transition

theorem GatedAction.strengthen_gate_fires (a : GatedAction σ) (p : σ → Prop) :
    (a.strengthen_gate p).fires = fun s s' => (a.gate s ∧ p s) ∧ a.transition s s' := by
  funext s s' ; simp [strengthen_gate, fires]

end TLA
