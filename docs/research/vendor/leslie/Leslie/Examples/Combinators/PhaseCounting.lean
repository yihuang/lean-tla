import Batteries.Data.List.Lemmas

/-! # Phase-Counting Threshold Protocols (abstract framework)

    A protocol-agnostic bounded-unrolling skeleton for **phase-counting**
    transition systems: systems carrying a `Nat`-valued phase counter that

      1. starts at `0` in the initial state,
      2. is strictly monotonic along every step, and
      3. is bounded by some `bound : Nat` (possibly depending on
         protocol parameters like `n`, `m`).

    From these three facts we get, for free, the "bounded unrolling"
    equivalence: safety of all reachable states is equivalent to safety
    of all traces of length `≤ bound` starting from the initial state.

    This is a "bounded depth suffices" pattern in which the diameter
    bound is obtained from a monotone counter argument (as opposed to
    a safety-diameter fixpoint argument).

    ### Concrete instances

    The three Paxos files under `Leslie/Examples/Paxos/` are all
    phase-counting. Each instantiates this framework locally:

      * `Leslie/Examples/Paxos/BoundedSingleProposer.lean` — counter ≤ `2 * n`
      * `Leslie/Examples/Paxos/BoundedTwoProposer.lean`    — counter ≤ `4 * n + 2`
      * `Leslie/Examples/Paxos/BoundedMProposer.lean`      — counter ≤ `2 * m * n + n + m`

    Core Lean 4 + Batteries only; no Mathlib.
-/

namespace PhaseCounting

/-! ## Section 1: Abstract system -/

/-- A phase-counting transition system: carrier type `State`, action type
    `Action`, step relation, distinguished initial state, and a monotone
    bounded `phaseCounter`. The three side conditions are:

      * `init_zero`       — the counter starts at `0`,
      * `step_mono`       — every step strictly increases the counter
                            (in fact by at least one; we only need `<`),
      * `step_bounded`    — every step stays within `bound`; combined
                            with `init_zero` this gives reachability-wide
                            boundedness.

    The side conditions are quoted in "step-local" form (no reference to
    `Reachable`) so the structure is non-recursive. -/
structure PhaseCountingSystem where
  State        : Type
  Action       : Type
  step         : State → State → Action → Prop
  init         : State
  phaseCounter : State → Nat
  bound        : Nat
  init_zero    : phaseCounter init = 0
  step_mono    : ∀ s s' a, step s s' a → phaseCounter s < phaseCounter s'
  step_bounded : ∀ s s' a, step s s' a → phaseCounter s' ≤ bound

/-! ## Section 2: Reachability and stepped traces -/

variable (P : PhaseCountingSystem)

/-- Reachable states of `P`, built by transitive closure from `P.init`. -/
inductive Reachable : P.State → Prop where
  | init : Reachable P.init
  | step : ∀ {s s' : P.State} (a : P.Action),
             Reachable s → P.step s s' a → Reachable s'

/-- Multi-step traces with an explicit action list. `StepsFrom s₀ acts s`
    means the trace `s₀ —[acts]→ s` exists. -/
inductive StepsFrom : P.State → List P.Action → P.State → Prop where
  | nil  : ∀ s, StepsFrom s [] s
  | cons : ∀ {s s' s'' : P.State} (a : P.Action) (acts : List P.Action),
             P.step s s' a → StepsFrom s' acts s'' → StepsFrom s (a :: acts) s''

/-- `StepsFrom` is closed under right-append of a single step. -/
theorem StepsFrom.snoc {P : PhaseCountingSystem}
    {p q r : P.State} {as : List P.Action}
    (b : P.Action) (hpq : StepsFrom P p as q) (hqr : P.step q r b) :
    StepsFrom P p (as ++ [b]) r := by
  induction hpq with
  | nil s => exact StepsFrom.cons b [] hqr (StepsFrom.nil _)
  | @cons s₁ s₂ s₃ x xs hx _ ih =>
    exact StepsFrom.cons x (xs ++ [b]) hx (ih hqr)

/-- Reachability is closed under `StepsFrom`: if we reach `s₀` and there
    is a trace `s₀ —[acts]→ s`, then `s` is reachable too. -/
theorem stepsFrom_preserves_reachable {P : PhaseCountingSystem}
    {s₀ s : P.State} {acts : List P.Action}
    (h : StepsFrom P s₀ acts s) (h₀ : Reachable P s₀) : Reachable P s := by
  induction h with
  | nil s => exact h₀
  | @cons s₁ s₂ s₃ a acts hstep _ ih =>
    exact ih (Reachable.step a h₀ hstep)

/-- Equivalence: `s` is reachable iff there is a trace from the initial
    state reaching it. -/
theorem reachable_iff_stepsFrom (P : PhaseCountingSystem) (s : P.State) :
    Reachable P s ↔ ∃ acts, StepsFrom P P.init acts s := by
  constructor
  · intro h
    induction h with
    | init => exact ⟨[], StepsFrom.nil _⟩
    | step a _ hstep ih =>
      obtain ⟨acts, hfrom⟩ := ih
      exact ⟨acts ++ [a], StepsFrom.snoc a hfrom hstep⟩
  · rintro ⟨acts, hfrom⟩
    exact stepsFrom_preserves_reachable hfrom Reachable.init

/-! ## Section 3: Counter monotonicity along traces -/

/-- Along any trace, the phase counter increases by **at least** the
    trace length. Combined with the bound, this caps trace length. -/
theorem phaseCounter_after_steps {P : PhaseCountingSystem}
    {s s'' : P.State} {acts : List P.Action}
    (hs : StepsFrom P s acts s'') :
    P.phaseCounter s + acts.length ≤ P.phaseCounter s'' := by
  induction hs with
  | nil s => simp
  | @cons s₁ s₂ s₃ a acts hstep _ ih =>
    have h1 : P.phaseCounter s₁ < P.phaseCounter s₂ := P.step_mono _ _ _ hstep
    have h2 : P.phaseCounter s₁ + 1 ≤ P.phaseCounter s₂ := h1
    simp [List.length_cons]
    omega

/-- Auxiliary: if we start at a state whose counter is `≤ bound` and
    take any number of steps, the resulting state's counter stays `≤ bound`.
    (Trivially true for zero steps; for non-zero, use `step_bounded` on
    the first step and recurse.) -/
theorem stepsFrom_tail_bounded {P : PhaseCountingSystem}
    {s s' : P.State} {acts : List P.Action}
    (h : StepsFrom P s acts s') (hs : P.phaseCounter s ≤ P.bound) :
    P.phaseCounter s' ≤ P.bound := by
  induction h with
  | nil _ => exact hs
  | @cons s₁ s₂ s₃ _a _acts hstep _ ih =>
    exact ih (P.step_bounded _ _ _ hstep)

/-- Any trace reaching a state from the initial state has bounded length. -/
theorem stepsFrom_length_bounded {P : PhaseCountingSystem}
    {s : P.State} {acts : List P.Action}
    (h : StepsFrom P P.init acts s) : acts.length ≤ P.bound := by
  have hafter : P.phaseCounter P.init + acts.length ≤ P.phaseCounter s :=
    phaseCounter_after_steps h
  have h0 : P.phaseCounter P.init = 0 := P.init_zero
  have hsb : P.phaseCounter s ≤ P.bound :=
    stepsFrom_tail_bounded h (by rw [h0]; exact Nat.zero_le _)
  omega

/-! ## Section 4: The abstract bounded-unrolling theorem -/

/-- Safety of all reachable states. -/
def safeAll (P : PhaseCountingSystem) (Safe : P.State → Prop) : Prop :=
  ∀ s, Reachable P s → Safe s

/-- Safety of all traces of length `≤ k` from the initial state. -/
def safeUpTo (P : PhaseCountingSystem) (Safe : P.State → Prop) (k : Nat) : Prop :=
  ∀ acts : List P.Action, acts.length ≤ k →
    ∀ s, StepsFrom P P.init acts s → Safe s

/-- **Phase-counting bounded-unrolling theorem.** For any safety predicate
    `Safe`, `Safe` holds at every reachable state iff it holds along every
    trace of length `≤ P.bound` starting from the initial state.

    The `→` direction is immediate from `reachable_iff_stepsFrom`. The
    `←` direction uses `stepsFrom_length_bounded` to cap the trace. -/
theorem phase_counting_bounded_unrolling (P : PhaseCountingSystem)
    (Safe : P.State → Prop) :
    safeAll P Safe ↔ safeUpTo P Safe P.bound := by
  constructor
  · intro hall acts _ s hfrom
    exact hall s ((reachable_iff_stepsFrom P s).mpr ⟨acts, hfrom⟩)
  · intro hsmall s hreach
    obtain ⟨acts, hfrom⟩ := (reachable_iff_stepsFrom P s).mp hreach
    have hlen : acts.length ≤ P.bound := stepsFrom_length_bounded hfrom
    exact hsmall acts hlen s hfrom

/-! ## Section 5: Refinement — message loss, fail-stop crashes, any
      restriction of the step relation

    A *refinement* of a phase-counting system is one whose step relation
    is a sub-relation of the original's. Operationally, a refinement models
    environments that restrict which actions may fire: dropped messages
    (certain actions never fire), fail-stop crashes (a given process's
    actions stop firing from some point onward), fair schedulers
    (adversarial action choices subject to fairness), etc.

    The fundamental theorem of refinement: **every state reachable in the
    refinement is reachable in the original.** Consequently, any safety
    property proved at the original level automatically transfers to the
    refinement. This formalizes the "monotonicity / subset" argument that
    justifies proving Paxos (and other consensus) at the atomic-action
    level and getting lossy and crash-safe variants for free.

    **Scope.** This section covers only step-relation *restrictions*. It
    does NOT cover fail-recover crashes (which would allow state loss,
    an operation the framework's `step_mono` explicitly forbids because
    it would let `phaseCounter` decrease), nor Byzantine faults (which
    would admit transitions outside the original `step` relation
    entirely). For fail-recover, the acceptor's persistent fields
    (`promised`, `accepted`) would need to be stable-storage-modeled
    explicitly — a substantial model extension. For Byzantine, the model
    would need to be completely redesigned. Both are out of scope for
    this framework. -/

/-- A *refinement* of `P` by a restricted step relation. The refined
    step must be a sub-relation of `P.step` (every refined transition is
    a valid `P` transition). Everything else is inherited from `P`:
    states, actions, initial state, phase counter, and bound.

    The three `PhaseCountingSystem` obligations transfer automatically:
    `init_zero` is identical, and both `step_mono` and `step_bounded`
    follow from `P`'s versions applied to the containing step. -/
def refined (P : PhaseCountingSystem)
    (step' : P.State → P.State → P.Action → Prop)
    (h_sub : ∀ s s' a, step' s s' a → P.step s s' a) :
    PhaseCountingSystem where
  State        := P.State
  Action       := P.Action
  step         := step'
  init         := P.init
  phaseCounter := P.phaseCounter
  bound        := P.bound
  init_zero    := P.init_zero
  step_mono    := fun s s' a h => P.step_mono s s' a (h_sub s s' a h)
  step_bounded := fun s s' a h => P.step_bounded s s' a (h_sub s s' a h)

/-- **Reachability in any refinement is reachability in the original.**
    This is the trivial monotonicity statement: if a state is reachable by
    taking only a subset of the original steps, it is reachable by the
    original step relation too.

    Uses term-mode structural recursion rather than the `induction` tactic
    because `Reachable` takes its `PhaseCountingSystem` as a parameter (not
    an index), so `induction` cannot produce a motive that crosses the
    refined and original systems. The direct recursion works because `hr`
    is structurally smaller at each recursive call. -/
theorem Reachable.of_refined
    {P : PhaseCountingSystem}
    {step' : P.State → P.State → P.Action → Prop}
    (h_sub : ∀ s s' a, step' s s' a → P.step s s' a) :
    ∀ {s : P.State}, Reachable (refined P step' h_sub) s → Reachable P s
  | _, .init => Reachable.init
  | _, .step a hr hstep =>
      Reachable.step a (Reachable.of_refined h_sub hr) (h_sub _ _ _ hstep)

/-- **Safety transfer under refinement.** If `Safe` holds for every state
    reachable in `P`, then `Safe` holds for every state reachable in any
    refinement of `P`.

    Operational reading: once agreement is proved for atomic-action Paxos
    (our Paxos files), it automatically holds for every Paxos execution
    under arbitrary message loss, arbitrary fair/unfair scheduling, and
    fail-stop crashes — because any of these restrictions produces a
    refinement of the atomic model. -/
theorem safeAll_of_refined
    {P : PhaseCountingSystem}
    {step' : P.State → P.State → P.Action → Prop}
    (h_sub : ∀ s s' a, step' s s' a → P.step s s' a)
    {Safe : P.State → Prop}
    (h : safeAll P Safe) :
    safeAll (refined P step' h_sub) Safe := by
  intro s hr
  exact h s (Reachable.of_refined h_sub hr)

/-- **Bounded-unrolling transfers under refinement.** A corollary combining
    `phase_counting_bounded_unrolling` with `safeAll_of_refined`: if the
    abstract cutoff holds for `P`, then a BMC-bounded safety check on
    `P` (which is what the Paxos files verify at `n ≤ bound`) establishes
    safety for every refinement of `P`.

    In other words: the bounded-unrolling procedure is sound not just for
    the atomic model but for every environment that restricts the step
    relation — including any reasonable formal model of message loss and
    fail-stop crashes. -/
theorem safeUpTo_transfers_to_refinement
    {P : PhaseCountingSystem}
    {step' : P.State → P.State → P.Action → Prop}
    (h_sub : ∀ s s' a, step' s s' a → P.step s s' a)
    {Safe : P.State → Prop}
    (h : safeUpTo P Safe P.bound) :
    safeAll (refined P step' h_sub) Safe := by
  have hall : safeAll P Safe := (phase_counting_bounded_unrolling P Safe).mpr h
  exact safeAll_of_refined h_sub hall

/-! ### Illustrative refinements (no new proof content; documentation only)

    These are not used anywhere — they're `def`s that concretely describe
    how "message loss" and "fail-stop crashes" look as refinements of a
    phase-counting system, so readers can see how the abstract theorem
    applies. The actual verification is handled by `refined` +
    `safeAll_of_refined` for any user-chosen `step'`. -/

/-- **Message-loss refinement.** Each action has an environment-controlled
    "deliverable" predicate `deliverable : State → Action → Bool`.  An
    action fires only if the environment permits it.  Any realistic
    lossy-channel semantics (drop arbitrary messages, drop arbitrary
    percentages, drop messages only to certain receivers, etc.) factors
    through such a predicate. -/
def withLossyDelivery (P : PhaseCountingSystem)
    (deliverable : P.State → P.Action → Bool) : PhaseCountingSystem :=
  refined P
    (fun s s' a => P.step s s' a ∧ deliverable s a = true)
    (fun _ _ _ h => h.1)

/-- **Fail-stop refinement.** A set of "crashed" process-identifiers,
    possibly expanding over time, filters which actions may fire: once a
    process is in the crashed set, none of its actions fire.  Here we
    model this as a predicate `canAct : State → Action → Bool` that the
    environment controls. -/
def withFailStop (P : PhaseCountingSystem)
    (canAct : P.State → P.Action → Bool) : PhaseCountingSystem :=
  refined P
    (fun s s' a => P.step s s' a ∧ canAct s a = true)
    (fun _ _ _ h => h.1)

/-- Message loss and fail-stop crashes can be composed — the refinement
    of a refinement is itself a refinement. This follows by chasing
    `h_sub` through the two layers and applying `safeAll_of_refined`
    twice.

    This shows the bounded-unrolling result survives **both** lossy
    communication **and** fail-stop crashes simultaneously, so users
    need not choose one or the other when justifying the framework's
    applicability to real fault models. -/
theorem withLossyDelivery_withFailStop_safe
    (P : PhaseCountingSystem)
    (deliverable canAct : P.State → P.Action → Bool)
    {Safe : P.State → Prop}
    (h : safeAll P Safe) :
    safeAll (withLossyDelivery (withFailStop P canAct) deliverable) Safe :=
  safeAll_of_refined _ (safeAll_of_refined _ h)

end PhaseCounting
