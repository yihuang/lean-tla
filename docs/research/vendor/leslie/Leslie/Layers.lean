import Leslie.Action

/-! ## CIVL-Style Layered Refinement

    This file defines:
    - `MoverType`: right, left, both, non-mover classifications
    - Commutativity conditions for actions
    - `Layer`: an `ActionSpec` annotated with mover types
    - `LayerRefinement`: refinement between adjacent layers
    - Composing multiple layer refinements
    - `Fragment`: yield-to-yield action sequences

    Reference: CIVL (Kragl & Qadeer), Lipton's reduction theorem.
-/

open Classical

namespace TLA

/-! ### Mover Types -/

/-- Classification of an action's commutativity with respect to other actions.
    - `right`: commutes to the right of concurrent actions
    - `left`: commutes to the left of concurrent actions
    - `both`: commutes in both directions
    - `nonmover`: does not commute -/
inductive MoverType where
  | right | left | both | nonmover
  deriving DecidableEq, Repr

/-- A both-mover is also a right-mover. -/
def MoverType.isRight : MoverType → Bool
  | .right | .both => true
  | _ => false

/-- A both-mover is also a left-mover. -/
def MoverType.isLeft : MoverType → Bool
  | .left | .both => true
  | _ => false

/-! ### Commutativity Conditions -/

/-- Right-commutativity: action `a` commutes to the right of action `b`.
    If `a` fires then `b` fires, there exists an equivalent execution
    where `b` fires first, then `a`. -/
def right_commutes (a b : GatedAction σ) : Prop :=
  ∀ s s₁ s₂, a.fires s s₁ → b.fires s₁ s₂ →
    ∃ s₁', b.fires s s₁' ∧ a.fires s₁' s₂

/-- Left-commutativity: action `a` commutes to the left of action `b`.
    If `b` fires then `a` fires, there exists an equivalent execution
    where `a` fires first, then `b`. -/
def left_commutes (a b : GatedAction σ) : Prop :=
  ∀ s s₁ s₂, b.fires s s₁ → a.fires s₁ s₂ →
    ∃ s₁', a.fires s s₁' ∧ b.fires s₁' s₂

/-- A both-mover commutes in both directions with the given action. -/
def both_commutes (a b : GatedAction σ) : Prop :=
  right_commutes a b ∧ left_commutes a b

/-- Validate that a claimed mover type is justified with respect to
    a set of environment actions (all other concurrent actions). -/
def valid_mover_type (a : GatedAction σ) (env : List (GatedAction σ))
    (mt : MoverType) : Prop :=
  match mt with
  | .both => (∀ b ∈ env, right_commutes a b) ∧ (∀ b ∈ env, left_commutes a b)
  | .right => ∀ b ∈ env, right_commutes a b
  | .left => ∀ b ∈ env, left_commutes a b
  | .nonmover => True

theorem valid_mover_both_implies_right {a : GatedAction σ} {env : List (GatedAction σ)} :
    valid_mover_type a env .both → valid_mover_type a env .right := by
  intro ⟨hr, _⟩ ; exact hr

theorem valid_mover_both_implies_left {a : GatedAction σ} {env : List (GatedAction σ)} :
    valid_mover_type a env .both → valid_mover_type a env .left := by
  intro ⟨_, hl⟩ ; exact hl

/-! ### Layers -/

/-- A layer: an `ActionSpec` annotated with mover types for each action. -/
structure Layer (σ : Type u) (ι : Type v) where
  spec : ActionSpec σ ι
  mover : ι → MoverType

/-- The underlying `Spec` of a layer. -/
def Layer.toSpec (l : Layer σ ι) : Spec σ := l.spec.toSpec

/-- The safety formula of a layer. -/
def Layer.safety (l : Layer σ ι) : pred σ := l.spec.safety

/-- All mover types in a layer are valid: each action's mover type is
    justified by commutativity with all other actions. -/
def Layer.movers_valid (l : Layer σ ι) : Prop :=
  ∀ i j, i ≠ j →
    (l.mover i).isRight = true → right_commutes (l.spec.actions i) (l.spec.actions j) ∧
    (l.mover i).isLeft = true → left_commutes (l.spec.actions i) (l.spec.actions j)

/-- Mover validity with thread-based partitioning. Actions only need to
    commute with actions of other threads. This is the standard CIVL
    condition: right-movers commute right past concurrent (other-thread)
    actions, left-movers commute left. -/
def Layer.movers_valid_threaded [DecidableEq θ]
    (l : Layer σ ι) (thread : ι → θ) : Prop :=
  ∀ i j, thread i ≠ thread j →
    ((l.mover i).isRight = true → right_commutes (l.spec.actions i) (l.spec.actions j)) ∧
    ((l.mover i).isLeft = true → left_commutes (l.spec.actions i) (l.spec.actions j))

/-! ### Layer Refinement -/

/-- Refinement between two layers (possibly with different state types).
    Each concrete action refines the corresponding abstract action
    (or stutters under the abstraction mapping). -/
structure LayerRefinement (σ_lo : Type u) (σ_hi : Type v) (ι : Type w) where
  lower : ActionSpec σ_lo ι
  upper : ActionSpec σ_hi ι
  abs : σ_lo → σ_hi
  init_preserved : ∀ s, lower.init s → upper.init (abs s)
  action_refines : ∀ i s s', (lower.actions i).fires s s' →
    (upper.actions i).fires (abs s) (abs s') ∨ abs s = abs s'

/-- A layer refinement implies spec-level refinement (safety). -/
theorem LayerRefinement.to_refines_via (lr : LayerRefinement σ_lo σ_hi ι) :
    refines_via lr.abs lr.lower.toSpec.safety lr.upper.toSpec.safety_stutter := by
  apply refinement_mapping_stutter lr.lower.toSpec lr.upper.toSpec
  · exact lr.init_preserved
  · intro s s' ⟨i, hfire⟩
    rcases lr.action_refines i s s' hfire with habs | hstutter
    · left ; exact ⟨i, habs⟩
    · right ; exact hstutter

/-- Layer refinement with an invariant on the lower layer. -/
structure LayerRefinementInv (σ_lo : Type u) (σ_hi : Type v) (ι : Type w) where
  lower : ActionSpec σ_lo ι
  upper : ActionSpec σ_hi ι
  abs : σ_lo → σ_hi
  inv : σ_lo → Prop
  inv_init : ∀ s, lower.init s → inv s
  inv_next : ∀ i s s', inv s → (lower.actions i).fires s s' → inv s'
  init_preserved : ∀ s, lower.init s → upper.init (abs s)
  action_refines : ∀ i s s', inv s → (lower.actions i).fires s s' →
    (upper.actions i).fires (abs s) (abs s') ∨ abs s = abs s'

theorem LayerRefinementInv.to_refines_via (lr : LayerRefinementInv σ_lo σ_hi ι) :
    refines_via lr.abs lr.lower.toSpec.safety lr.upper.toSpec.safety_stutter := by
  apply refinement_mapping_stutter_with_invariant
    lr.lower.toSpec lr.upper.toSpec lr.abs lr.inv
  · exact lr.inv_init
  · intro s s' hinv ⟨i, hfire⟩ ; exact lr.inv_next i s s' hinv hfire
  · exact lr.init_preserved
  · intro s s' hinv ⟨i, hfire⟩
    rcases lr.action_refines i s s' hinv hfire with habs | hstutter
    · left ; exact ⟨i, habs⟩
    · right ; exact hstutter

/-! ### Composing Layer Refinements -/

/-- A layer refinement also maps `safety_stutter` to `safety_stutter`.
    Stutter steps in the concrete (`s = s'`) map to stutter steps in the
    abstract (`abs s = abs s'`). -/
theorem LayerRefinement.to_refines_via_stutter (lr : LayerRefinement σ_lo σ_hi ι) :
    refines_via lr.abs lr.lower.toSpec.safety_stutter lr.upper.toSpec.safety_stutter := by
  apply refinement_mapping_stutter_stutter lr.lower.toSpec lr.upper.toSpec
  · exact lr.init_preserved
  · intro s s' ⟨i, hfire⟩
    rcases lr.action_refines i s s' hfire with habs | hstutter
    · left ; exact ⟨i, habs⟩
    · right ; exact hstutter

/-- Compose two layer refinements into a single spec refinement. -/
theorem LayerRefinement.compose
    (r1 : LayerRefinement σ₀ σ₁ ι)
    (r2 : LayerRefinement σ₁ σ₂ ι)
    (hcompat : r1.upper = r2.lower) :
    refines_via (r2.abs ∘ r1.abs)
      r1.lower.toSpec.safety r2.upper.toSpec.safety_stutter := by
  have h1 := r1.to_refines_via
  have h2 := r2.to_refines_via_stutter
  have heq : r1.upper.toSpec.safety_stutter = r2.lower.toSpec.safety_stutter := by
    rw [hcompat]
  rw [heq] at h1
  exact refines_via_trans h1 h2

/-- Compose three layer refinements. -/
theorem LayerRefinement.compose3
    (r1 : LayerRefinement σ₀ σ₁ ι)
    (r2 : LayerRefinement σ₁ σ₂ ι)
    (r3 : LayerRefinement σ₂ σ₃ ι)
    (h12 : r1.upper = r2.lower)
    (h23 : r2.upper = r3.lower) :
    refines_via (r3.abs ∘ r2.abs ∘ r1.abs)
      r1.lower.toSpec.safety r3.upper.toSpec.safety_stutter := by
  have h1 := r1.to_refines_via_stutter
  have h2 := r2.to_refines_via_stutter
  have h3 := r3.to_refines_via_stutter
  rw [h12] at h1
  rw [h23] at h2
  have h12' := refines_via_trans h1 h2
  have h123 := refines_via_trans h12' h3
  rw [show r3.abs ∘ r2.abs ∘ r1.abs = (r3.abs ∘ r2.abs) ∘ r1.abs from rfl]
  intro e he
  exact h123 e (safety_implies_safety_stutter _ e he)

/-! ### Yield-to-Yield Fragments (Lipton Reduction) -/

/-- A fragment is a sequence of actions with mover annotations,
    representing a yield-to-yield execution path. -/
structure Fragment (σ : Type u) where
  actions : List (GatedAction σ × MoverType)

/-- A fragment has the R*;N;L* shape required by Lipton's reduction. -/
def Fragment.well_formed (frag : Fragment σ) : Prop :=
  ∃ (rs : List (GatedAction σ)) (n : GatedAction σ) (ls : List (GatedAction σ)),
    frag.actions = (rs.map (·, .right)) ++ [(n, .nonmover)] ++ (ls.map (·, .left))

/-- A fragment has the R*;L* shape (no non-mover, all commuting). -/
def Fragment.fully_commuting (frag : Fragment σ) : Prop :=
  ∃ (rs : List (GatedAction σ)) (ls : List (GatedAction σ)),
    frag.actions = (rs.map (·, .right)) ++ (ls.map (·, .left))

/-- Sequential execution of a fragment: fold transitions left to right. -/
def Fragment.seq_execute : List (GatedAction σ) → action σ
  | [] => fun s s' => s = s'
  | [a] => a.fires
  | a :: rest => fun s s' => ∃ s_mid, a.fires s s_mid ∧ Fragment.seq_execute rest s_mid s'

/-- Execute a fragment sequentially (extract action list, then execute). -/
def Fragment.execute (frag : Fragment σ) : action σ :=
  Fragment.seq_execute (frag.actions.map Prod.fst)

/-! ### Lipton Reduction

    The core of Lipton's reduction theorem: right-movers can be swapped
    past environment steps, left-movers can absorb preceding environment
    steps. Together, this means a well-formed R*;N;L* fragment can be
    treated as atomic with respect to environment actions. -/

/-- Sequential composition of gated actions (simpler than `Fragment.seq_execute`
    for inductive proofs — no special case for singletons). -/
def seq_run : List (GatedAction σ) → action σ
  | [] => fun s s' => s = s'
  | a :: rest => fun s s' => ∃ s_mid, a.fires s s_mid ∧ seq_run rest s_mid s'

@[simp] theorem seq_run_nil : seq_run (σ := σ) [] s s' ↔ s = s' := Iff.rfl

theorem seq_run_cons (a : GatedAction σ) (rest : List (GatedAction σ)) :
    seq_run (a :: rest) s s' ↔ ∃ s_mid, a.fires s s_mid ∧ seq_run rest s_mid s' := Iff.rfl

theorem seq_run_singleton (a : GatedAction σ) :
    seq_run [a] s s' ↔ a.fires s s' :=
  ⟨fun ⟨_, hf, rfl⟩ => hf, fun hf => ⟨s', hf, rfl⟩⟩

theorem seq_run_append (xs ys : List (GatedAction σ)) :
    seq_run (xs ++ ys) s s' ↔ ∃ s_mid, seq_run xs s s_mid ∧ seq_run ys s_mid s' := by
  induction xs generalizing s with
  | nil => simp [seq_run]
  | cons a rest ih =>
    simp only [List.cons_append, seq_run_cons]
    constructor
    · rintro ⟨s₁, ha, hrest⟩
      rw [ih] at hrest
      obtain ⟨s₂, hrest', hys⟩ := hrest
      exact ⟨s₂, ⟨s₁, ha, hrest'⟩, hys⟩
    · rintro ⟨s₂, ⟨s₁, ha, hrest⟩, hys⟩
      exact ⟨s₁, ha, ih.mpr ⟨s₂, hrest, hys⟩⟩

/-- A sequence of right-movers can be swapped past one environment step.
    If `rs` executes from `s` to `s₁`, and `env` fires from `s₁` to `s₂`,
    then there exists `s₁'` such that `env` fires from `s` to `s₁'` and
    `rs` executes from `s₁'` to `s₂`. -/
theorem right_movers_swap (rs : List (GatedAction σ)) (env : GatedAction σ)
    (hrc : ∀ r ∈ rs, right_commutes r env) :
    ∀ s s₁ s₂, seq_run rs s s₁ → env.fires s₁ s₂ →
      ∃ s₁', env.fires s s₁' ∧ seq_run rs s₁' s₂ := by
  induction rs with
  | nil =>
    intro s s₁ s₂ hseq henv
    obtain rfl := hseq
    exact ⟨s₂, henv, rfl⟩
  | cons a rest ih =>
    intro s s₁ s₂ hseq henv
    obtain ⟨s_mid, ha, hrest⟩ := hseq
    obtain ⟨s₁', henv', hrest'⟩ := ih
      (fun r hr => hrc r (List.mem_cons_of_mem a hr)) s_mid s₁ s₂ hrest henv
    obtain ⟨s₁'', henv'', ha'⟩ :=
      hrc a List.mem_cons_self s s_mid s₁' ha henv'
    exact ⟨s₁'', henv'', s₁', ha', hrest'⟩

/-- A sequence of left-movers absorbs a preceding environment step.
    If `env` fires from `s` to `s₁`, and `ls` executes from `s₁` to `s₂`,
    then there exists `s₁'` such that `ls` executes from `s` to `s₁'` and
    `env` fires from `s₁'` to `s₂`. -/
theorem left_movers_absorb (ls : List (GatedAction σ)) (env : GatedAction σ)
    (hlc : ∀ l ∈ ls, left_commutes l env) :
    ∀ s s₁ s₂, env.fires s s₁ → seq_run ls s₁ s₂ →
      ∃ s₁', seq_run ls s s₁' ∧ env.fires s₁' s₂ := by
  induction ls with
  | nil =>
    intro s s₁ s₂ henv hseq
    obtain rfl := hseq
    exact ⟨s, rfl, henv⟩
  | cons a rest ih =>
    intro s s₁ s₂ henv hseq
    obtain ⟨s_mid, ha, hrest⟩ := hseq
    obtain ⟨s₁', ha', henv'⟩ :=
      hlc a List.mem_cons_self s s₁ s_mid henv ha
    obtain ⟨s₂', hrest', henv''⟩ := ih
      (fun l hl => hlc l (List.mem_cons_of_mem a hl)) s₁' s_mid s₂ henv' hrest
    exact ⟨s₂', ⟨s₁', ha', hrest'⟩, henv''⟩

/-- Right-reduction: an env step after a sequence of right-movers
    can be pushed before the entire fragment. -/
theorem fragment_right_reduction
    (rs rest : List (GatedAction σ)) (env : GatedAction σ)
    (hrc : ∀ r ∈ rs, right_commutes r env)
    {s s₁ s₂ s₃ : σ}
    (hrs : seq_run rs s s₁) (henv : env.fires s₁ s₂)
    (hrest : seq_run rest s₂ s₃) :
    ∃ s₁', env.fires s s₁' ∧ seq_run (rs ++ rest) s₁' s₃ := by
  obtain ⟨s₁', henv', hrs'⟩ := right_movers_swap rs env hrc s s₁ s₂ hrs henv
  exact ⟨s₁', henv', (seq_run_append rs rest).mpr ⟨_, hrs', hrest⟩⟩

/-- Left-reduction: an env step before a sequence of left-movers
    can be pushed after the entire fragment. -/
theorem fragment_left_reduction
    (prefix_ ls : List (GatedAction σ)) (env : GatedAction σ)
    (hlc : ∀ l ∈ ls, left_commutes l env)
    {s s₁ s₂ s₃ : σ}
    (hpre : seq_run prefix_ s s₁) (henv : env.fires s₁ s₂)
    (hls : seq_run ls s₂ s₃) :
    ∃ s₃', seq_run (prefix_ ++ ls) s s₃' ∧ env.fires s₃' s₃ := by
  obtain ⟨s₂', hls', henv'⟩ := left_movers_absorb ls env hlc s₁ s₂ s₃ henv hls
  exact ⟨s₂', (seq_run_append prefix_ ls).mpr ⟨s₁, hpre, hls'⟩, henv'⟩

/-- Lipton reduction (right): in a well-formed R*;N;L* fragment,
    an env step after the right-movers can be pushed before everything. -/
theorem lipton_reduction_right
    (rs : List (GatedAction σ)) (n : GatedAction σ) (ls : List (GatedAction σ))
    (env : GatedAction σ) (hrc : ∀ r ∈ rs, right_commutes r env)
    {s s₁ s₂ s₃ : σ}
    (hrs : seq_run rs s s₁) (henv : env.fires s₁ s₂)
    (hn_ls : seq_run (n :: ls) s₂ s₃) :
    ∃ s₁', env.fires s s₁' ∧ seq_run (rs ++ n :: ls) s₁' s₃ :=
  fragment_right_reduction rs (n :: ls) env hrc hrs henv hn_ls

/-- Lipton reduction (left): in a well-formed R*;N;L* fragment,
    an env step before the left-movers can be pushed after everything. -/
theorem lipton_reduction_left
    (rs : List (GatedAction σ)) (n : GatedAction σ) (ls : List (GatedAction σ))
    (env : GatedAction σ) (hlc : ∀ l ∈ ls, left_commutes l env)
    {s s₁ s₂ s₃ : σ}
    (hrs_n : seq_run (rs ++ [n]) s s₁) (henv : env.fires s₁ s₂)
    (hls : seq_run ls s₂ s₃) :
    ∃ s₃', seq_run (rs ++ [n] ++ ls) s s₃' ∧ env.fires s₃' s₃ :=
  fragment_left_reduction (rs ++ [n]) ls env hlc hrs_n henv hls

/-! ### Introducing and Hiding Actions -/

/-- A skip action: gate is always false, so it never fires. Used to model
    actions that don't exist at a particular layer. -/
def GatedAction.skip : GatedAction σ where
  gate := fun _ => False
  transition := fun _ _ => True

theorem GatedAction.skip_never_fires :
    ∀ s s', ¬ (GatedAction.skip (σ := σ)).fires s s' := by
  intro s s' ⟨hg, _⟩ ; exact hg

/-- An action is introduced at this layer (wasn't present before). At the
    lower layer it's a skip; at the upper layer it's the real action.
    This always refines: skip never fires, so the refinement condition
    is vacuously true. -/
theorem skip_refines_any (f : σ → τ) (a : GatedAction τ) :
    ∀ s s', (GatedAction.skip (σ := σ)).fires s s' →
      a.fires (f s) (f s') ∨ f s = f s' := by
  intro s s' hfire ; exact absurd hfire (GatedAction.skip_never_fires s s')

/-- An action is hidden at this layer (present below, gone above).
    Any action refines skip-or-stutter if it doesn't change the visible state. -/
theorem any_refines_skip_if_stutter (f : σ → τ) (a : GatedAction σ)
    (hstutter : ∀ s s', a.fires s s' → f s = f s') :
    ∀ s s', a.fires s s' →
      (GatedAction.skip (σ := τ)).fires (f s) (f s') ∨ f s = f s' := by
  intro s s' hfire ; exact Or.inr (hstutter s s' hfire)

end TLA
