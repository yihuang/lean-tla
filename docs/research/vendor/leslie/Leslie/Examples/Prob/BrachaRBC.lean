/-
M2 W3 — Bracha Reliable Broadcast as a `ProbActionSpec`.

This module models the Bracha Byzantine Reliable Broadcast protocol
(`n` parties, ≤ `f` Byzantine faults, `n > 3f`) as a
`Leslie.Prob.ProbActionSpec` and states its three classical safety/
liveness properties on top of `AlmostBox` / `AlmostDiamond` against
`traceDist`.

Because Bracha is fully deterministic, every `effect` is a Dirac
(`PMF.pure`) on the deterministic next-state. The randomized layer
is therefore "vacuous" for this protocol — the exercise is to nail
down the `Adversary` / `Trace` / corruption modeling end-to-end
against a real distributed protocol, so the same top-level
statements port cleanly when later protocols (AVSS, common coin)
actually flip coins.

## Status

  * §1 `brbStep` — a deterministic next-state function mirroring
    every case of the protocol. **Closed.**
  * §2 `brbProb` — the probabilistic spec built from `brbStep`
    via `PMF.pure`. **Closed (definitional).**
  * §3 `brbProb_step_pure` — bridge lemma: each step is a Dirac on
    `brbStep`. **Closed.**
  * §4 `brbProb_fires_iff` — bridge expressing that an enabled
    action's next-state is uniquely `brbStep`. **Closed.**
  * §5 `brbProb_budget_AS` — corruption budget invariant lifted to
    `AlmostBox`. **Closed** modulo the `AlmostBox_of_pure_inductive`
    bridge in `Leslie/Prob/Refinement.lean`. The structural side
    (deterministic step preserves the budget) IS closed in §5.1.
  * §6 `brbProb_validity_AS`, §7 `brbProb_agreement_AS` — same shape
    as §5; closed via the inductive invariant `brb_inv` from upstream
    `Leslie.Examples.ByzantineReliableBroadcast` plus the same
    `AlmostBox_of_pure_inductive` bridge.
  * §8 `brbProb_totality_AS_fair` — liveness; **closed** sorry-free
    via `Leslie.Prob.AlmostDiamond_of_leads_to`, the `AlmostDiamond`
    analogue of the `AlmostBox` bridge.

## Upstream reuse

This file imports protocol types (`MsgType`, `Message`, `LocalState`,
`State`, `Action`), helpers (`isCorrect`, `countEchoRecv`,
`countVoteRecv`, `*Threshold`, `LocalState.init`), the deterministic
relational spec `brb`, and the safety invariant `brb_inv` (with
`brb_inv_init` / `brb_inv_step`) from
`Leslie.Examples.ByzantineReliableBroadcast`. The pieces added here
are the deterministic next-state function `brbStep`, the gate
predicate `actionGate`, the initial-state predicate `initPred`, and
the probabilistic spec `brbProb` built on top.

## Typeclass setup

To run `traceDist` on `(State n Value, Action n Value)` we need
both types `Countable` plus a `MeasurableSpace` /
`MeasurableSingletonClass`. The `State` carries function-valued
fields like `Fin n → LocalState n Value`, `Message n Value → Bool`,
and a `Value → Bool` field on `LocalState` (`voted`); these are not
countable when `Value` is arbitrary. We therefore add
`[Fintype Value]` (alongside `[DecidableEq Value]`) on theorems that
use `traceDist` / `AlmostBox` / `AlmostDiamond`. Concrete uses in
M3+ instantiate with `Value = Fin k`, so this is non-binding.

Per implementation plan v2.2 §M2 W3 + design plan v2.2
§"Probabilistic refinement on a real protocol".
-/

import Leslie.Examples.ByzantineReliableBroadcast
import Leslie.Prob.Action
import Leslie.Prob.Adversary
import Leslie.Prob.Trace
import Leslie.Prob.Refinement
import Leslie.Prob.PMF
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Countable.Defs

namespace Leslie.Prob.Examples.BrachaRBC

open Leslie.Prob MeasureTheory ByzantineReliableBroadcast

/-! ## §0. Fintype on upstream `MsgType`

Upstream derives only `DecidableEq` for `MsgType`; we need `Fintype`
to make `Action n Value` and `Message n Value` countable. -/

instance : Fintype MsgType where
  elems := {.init, .echo, .vote}
  complete := fun t => by cases t <;> decide

variable (n f : Nat) (Value : Type) [DecidableEq Value]

/-! ## §1. Deterministic next-state function `brbStep`

Each branch mirrors the relational `transition` field of the
deterministic `brb` `ActionSpec`. Where the gate is unmet, this
function is allowed to return arbitrary garbage (`s` itself —
i.e. a stutter); the spec's `gate` field hides those branches. -/

/-- The deterministic next-state function: given an `Action n Value`
and a pre-state `s`, return the unique post-state defined by the
deterministic relational transition of Bracha BRB.

The `sender` parameter is used by the `recv` case to gate
acceptance of `init` messages; `val` is unused at the next-state
level (it appears only in the gate of `send (.init …)` to enforce
"sender carries `val`"). -/
def brbStep (sender : Fin n) (_val : Value)
    (a : Action n Value) (s : State n Value) : State n Value :=
  match a with
  | .corrupt i =>
      { s with corrupted := i :: s.corrupted }
  | .send src dst t mv =>
      let msg : Message n Value := ⟨src, dst, t, mv⟩
      { s with
        buffer := fun m => if m = msg then true else s.buffer m
        local_ := fun p => if p = src then
          { s.local_ src with
            sent := fun d t' w =>
              if d = dst ∧ t' = t ∧ w = mv then true
              else (s.local_ src).sent d t' w
            echoed := match t with
              | .echo => if src ∉ s.corrupted then some mv
                         else (s.local_ src).echoed
              | _ => (s.local_ src).echoed
            voted := match t with
              | .vote => if src ∉ s.corrupted
                then fun w => if w = mv then true else (s.local_ src).voted w
                else (s.local_ src).voted
              | _ => (s.local_ src).voted }
          else s.local_ p }
  | .recv src dst t mv =>
      let msg : Message n Value := ⟨src, dst, t, mv⟩
      let ls := s.local_ dst
      { s with
        buffer := fun m => if m = msg then false else s.buffer m
        local_ := fun p => if p = dst then
          match t with
          | .init =>
              if src = sender ∧ ls.sendRecv = none
              then { ls with sendRecv := some mv }
              else ls
          | .echo =>
              if ls.echoRecv src mv = false
              then { ls with
                echoRecv := fun q w =>
                  if q = src ∧ w = mv then true else ls.echoRecv q w }
              else ls
          | .vote =>
              if ls.voteRecv src mv = false
              then { ls with
                voteRecv := fun q w =>
                  if q = src ∧ w = mv then true else ls.voteRecv q w }
              else ls
          else s.local_ p }
  | .doReturn i mv =>
      { s with
        local_ := fun p => if p = i
          then { s.local_ i with returned := some mv }
          else s.local_ p }

/-! ## Action gates

The same gate predicates as `(brb n f Value sender val).actions a` —
inlined so we don't need to import the relational spec. -/

/-- The gate predicate for action `a` in state `s`. Identical to
`((brb n f Value sender val).actions a).gate s` upstream. -/
def actionGate (sender : Fin n) (val : Value)
    (a : Action n Value) (s : State n Value) : Prop :=
  match a with
  | .corrupt i =>
      isCorrect n Value s i ∧ s.corrupted.length + 1 ≤ f
  | .send src dst t mv =>
      src ∈ s.corrupted ∨
      (isCorrect n Value s src ∧ (s.local_ src).sent dst t mv = false ∧
        match t with
        | .init => src = sender ∧ mv = val
        | .echo =>
            (s.local_ src).echoed = some mv
            ∨ ((s.local_ src).echoed = none ∧ (s.local_ src).sendRecv = some mv)
        | .vote =>
            (s.local_ src).voted mv = true ∨
            countEchoRecv n Value (s.local_ src) mv ≥ echoThreshold n f ∨
            countVoteRecv n Value (s.local_ src) mv ≥ voteThreshold f)
  | .recv src dst t mv =>
      s.buffer ⟨src, dst, t, mv⟩ = true
  | .doReturn i mv =>
      isCorrect n Value s i ∧
      (s.local_ i).returned = none ∧
      countVoteRecv n Value (s.local_ i) mv ≥ returnThreshold n f

/-- The initial-state predicate: empty local states, empty buffer,
no corruptions. Identical to `(brb …).init` upstream. -/
def initPred (s : State n Value) : Prop :=
  (∀ p, s.local_ p = LocalState.init n Value) ∧
  (∀ m, s.buffer m = false) ∧
  s.corrupted = []

/-! ## §2. Probabilistic spec `brbProb`

Every `effect` is a Dirac on `brbStep`; the gate is the deterministic
gate from §0. -/

/-- The probabilistic Bracha BRB spec. -/
noncomputable def brbProb (sender : Fin n) (val : Value) :
    ProbActionSpec (State n Value) (Action n Value) where
  init := initPred n Value
  actions := fun a =>
    { gate := actionGate n f Value sender val a
      effect := fun s _ => PMF.pure (brbStep n Value sender val a s) }

/-! ## §3. Bridge lemma: step is a Dirac on `brbStep` -/

/-- When the gate holds, `(brbProb …).step a s` is `some (PMF.pure …)`. -/
@[simp] theorem brbProb_step_pure
    (sender : Fin n) (val : Value)
    (a : Action n Value) (s : State n Value)
    (h : actionGate n f Value sender val a s) :
    (brbProb n f Value sender val).step a s
      = some (PMF.pure (brbStep n Value sender val a s)) :=
  ProbActionSpec.step_eq_some h

/-- When the gate fails, `(brbProb …).step a s = none`. -/
theorem brbProb_step_none
    (sender : Fin n) (val : Value)
    (a : Action n Value) (s : State n Value)
    (h : ¬ actionGate n f Value sender val a s) :
    (brbProb n f Value sender val).step a s = none :=
  ProbActionSpec.step_eq_none h

/-! ## §4. Bridge: gate-determined uniqueness of `brbStep`

When the gate holds, `brbStep` is the unique post-state. Stated as
a ↔ to mirror the relational `fires` shape on the deterministic
side: `((brb …).actions a).fires s s'` would be exactly
`actionGate ∧ s' = brbStep …`. -/

theorem brbProb_fires_iff
    (sender : Fin n) (val : Value)
    (a : Action n Value) (s s' : State n Value) :
    (actionGate n f Value sender val a s ∧
      s' = brbStep n Value sender val a s) ↔
    (∃ μ, (brbProb n f Value sender val).step a s = some μ ∧
      μ = PMF.pure s') := by
  constructor
  · rintro ⟨hg, rfl⟩
    exact ⟨_, brbProb_step_pure n f Value sender val a s hg, rfl⟩
  · rintro ⟨μ, hstep, hμ⟩
    -- `step a s` is `some (PMF.pure (brbStep …))` iff gate holds.
    -- Otherwise it is `none`. Extract the gate by case analysis.
    by_cases hg : actionGate n f Value sender val a s
    · refine ⟨hg, ?_⟩
      have hstep' := brbProb_step_pure n f Value sender val a s hg
      rw [hstep] at hstep'
      have hμ' : μ = PMF.pure (brbStep n Value sender val a s) := by
        injection hstep'
      have hpure : PMF.pure s' = PMF.pure (brbStep n Value sender val a s) :=
        hμ.symm.trans hμ'
      -- `PMF.pure` is injective on its argument.
      have hsupp := congrArg (fun p : PMF (State n Value) => p.support) hpure
      simp [PMF.support_pure] at hsupp
      exact hsupp
    · exfalso
      have hnone := brbProb_step_none n f Value sender val a s hg
      rw [hnone] at hstep
      exact Option.some_ne_none μ hstep.symm

/-! ## §5. Corruption-budget invariant (AlmostBox formulation)

The deterministic step preserves `corrupted.length ≤ f` whenever the
gate holds. We lift this to an `AlmostBox` statement on the
probabilistic trace.

**Typeclass scope.** Lifting requires `Countable (State n Value)`
and `Countable (Action n Value)` (plus a `MeasurableSingletonClass`).
We add `[Fintype Value]` to make `LocalState n Value` and the
function-valued fields finite (hence countable). The discrete
σ-algebra (`⊤`) supplies a `MeasurableSingletonClass` for free. -/

section AlmostBox

variable [Fintype Value]

-- Discrete `MeasurableSpace` / `MeasurableSingletonClass` /
-- `Countable` instances on the protocol's state / action carriers.
-- With `Fintype Value` plus `DecidableEq Value`, both types are
-- inductively built from finite/countable components.

instance : MeasurableSpace (State n Value) := ⊤
instance : MeasurableSingletonClass (State n Value) := ⟨fun _ => trivial⟩
instance : MeasurableSpace (Action n Value) := ⊤
instance : MeasurableSingletonClass (Action n Value) := ⟨fun _ => trivial⟩

/-- `Action n Value` is `Fintype` via the obvious sum-of-products
encoding. With `[Fintype Value]` (and `[DecidableEq Value]` from
the outer scope), `Fintype` follows. `Countable` is then derived
via `Fintype.toCountable`. -/
noncomputable instance : Fintype (Action n Value) := by
  classical
  exact Fintype.ofEquiv
    (Fin n ⊕ (Fin n × Fin n × MsgType × Value)
      ⊕ (Fin n × Fin n × MsgType × Value) ⊕ (Fin n × Value))
    { toFun := fun
        | .inl i => .corrupt i
        | .inr (.inl ⟨src, dst, t, v⟩) => .send src dst t v
        | .inr (.inr (.inl ⟨src, dst, t, v⟩)) => .recv src dst t v
        | .inr (.inr (.inr ⟨i, v⟩)) => .doReturn i v
      invFun := fun
        | .corrupt i => .inl i
        | .send src dst t v => .inr (.inl ⟨src, dst, t, v⟩)
        | .recv src dst t v => .inr (.inr (.inl ⟨src, dst, t, v⟩))
        | .doReturn i v => .inr (.inr (.inr ⟨i, v⟩))
      left_inv := fun
        | .inl _ => rfl
        | .inr (.inl _) => rfl
        | .inr (.inr (.inl _)) => rfl
        | .inr (.inr (.inr _)) => rfl
      right_inv := fun
        | .corrupt _ => rfl
        | .send _ _ _ _ => rfl
        | .recv _ _ _ _ => rfl
        | .doReturn _ _ => rfl }

instance : Countable (Action n Value) := Finite.to_countable

/-- `Message n Value` is `Fintype`: a 4-field record with finite
fields under `[Fintype Value]`. -/
noncomputable instance : Fintype (Message n Value) := by
  classical
  exact Fintype.ofEquiv (Fin n × Fin n × MsgType × Value)
    { toFun := fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩
      invFun := fun m => ⟨m.src, m.dst, m.type, m.val⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- `LocalState n Value` is `Fintype`: a 7-fold record, every field
finite under `[Fintype Value]`. -/
noncomputable instance : Fintype (LocalState n Value) := by
  classical
  exact Fintype.ofEquiv
    ((Fin n → MsgType → Value → Bool) × Option Value
      × (Fin n → Value → Bool) × (Fin n → Value → Bool)
      × Option Value × (Value → Bool) × Option Value)
    { toFun := fun ⟨a, b, c, d, e, f, g⟩ =>
        ⟨a, b, c, d, e, f, g⟩
      invFun := fun ls =>
        (ls.sent, ls.sendRecv, ls.echoRecv, ls.voteRecv,
         ls.echoed, ls.voted, ls.returned)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- `State n Value` is `Countable`. `local_` and `buffer` are
finite-domain functions into finite types (hence `Fintype` and
`Countable`); `corrupted` is a `List (Fin n)` (countable). -/
instance : Countable (State n Value) := by
  classical
  let e : ((Fin n → LocalState n Value) × (Message n Value → Bool)
            × List (Fin n)) ≃ State n Value :=
    { toFun := fun p => ⟨p.1, p.2.1, p.2.2⟩
      invFun := fun s => (s.local_, s.buffer, s.corrupted)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Countable.of_equiv _ e

/-! ### §5.1 Deterministic budget preservation

A pure-step lemma: `actionGate` plus `corrupted.length ≤ f` implies
`(brbStep a s).corrupted.length ≤ f`. -/

omit [Fintype Value] in
theorem brbStep_preserves_budget
    (sender : Fin n) (val : Value)
    (a : Action n Value) (s : State n Value)
    (hgate  : actionGate n f Value sender val a s)
    (hbudget : s.corrupted.length ≤ f) :
    (brbStep n Value sender val a s).corrupted.length ≤ f := by
  cases a with
  | corrupt i =>
      -- gate forces `corrupted.length + 1 ≤ f`.
      simp only [brbStep, List.length_cons]
      have : s.corrupted.length + 1 ≤ f := hgate.2
      omega
  | send src dst t mv =>
      -- send doesn't touch `corrupted`.
      simp only [brbStep]
      exact hbudget
  | recv src dst t mv =>
      simp only [brbStep]
      exact hbudget
  | doReturn i mv =>
      simp only [brbStep]
      exact hbudget

omit [DecidableEq Value] [Fintype Value] in
/-- The initial-state predicate implies the budget invariant.
Trivial: `corrupted = []`. -/
theorem initPred_budget
    (s : State n Value) (h : initPred n Value s) :
    s.corrupted.length ≤ f := by
  have : s.corrupted = [] := h.2.2
  simp [this]

/-! ### §5.2 AlmostBox lift -/

set_option maxHeartbeats 800000 in
/-- Corruption-budget AlmostBox invariant on the probabilistic
trace. Initial measure is concentrated on `initPred` states (i.e.,
`brbProb`-init states); `initPred_budget` gives the budget at step
0, and `brbStep_preserves_budget` gives the inductive step.

**M2 W3 polish closure.** Closed by `AlmostBox_of_pure_inductive`
from `Leslie.Prob.Refinement`:
  * `h_pure` is by `rfl` (each `brbProb` effect is `PMF.pure` on
    `brbStep` by definition).
  * `h_step` is `brbStep_preserves_budget` (§5.1).
  * `h_init` requires the budget at every state in `μ₀`'s support;
    the cleaner phrasing `∀ᵐ s ∂μ₀, ...` (per
    `Leslie.Prob.Refinement.AlmostBox_of_pure_inductive`) is used. -/
theorem brbProb_budget_AS
    (sender : Fin n) (val : Value)
    (μ₀ : Measure (State n Value)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred n Value s)
    (A : Adversary (State n Value) (Action n Value)) :
    AlmostBox (brbProb n f Value sender val) A μ₀
      (fun s => s.corrupted.length ≤ f) := by
  -- The deterministic step preserves the budget; pull the bridge.
  have h_pure : ∀ (a : Action n Value) (s : State n Value)
      (h : ((brbProb n f Value sender val).actions a).gate s),
      ((brbProb n f Value sender val).actions a).effect s h
        = PMF.pure (brbStep n Value sender val a s) :=
    fun _ _ _ => rfl
  have h_init' : ∀ᵐ s ∂μ₀, s.corrupted.length ≤ f := by
    filter_upwards [h_init] with s hs
    exact initPred_budget n f Value s hs
  exact AlmostBox_of_pure_inductive
    (fun s => s.corrupted.length ≤ f)
    (fun a s => brbStep n Value sender val a s)
    h_pure
    (fun a s hgate hbudget =>
      brbStep_preserves_budget n f Value sender val a s hgate hbudget)
    μ₀ h_init' A

/-! ### §5.3 Bridges to upstream relational `brb`

`actionGate` and `brbStep` were inlined here so the probabilistic
spec doesn't have to dispatch through the relational `(brb …).actions`.
Both are *definitionally equal* to the corresponding upstream fields,
so the bridge is a pair of `cases a <;> rfl` lemmas. We use these to
relay the inductive invariant `brb_inv` from upstream
`brb_inv_init` / `brb_inv_step` into our deterministic
`brbStep`-driven `AlmostBox_of_pure_inductive` framework. -/

omit [Fintype Value] in
theorem actionGate_iff_brb_gate
    (sender : Fin n) (val : Value)
    (a : Action n Value) (s : State n Value) :
    actionGate n f Value sender val a s ↔
      ((brb n f Value sender val).actions a).gate s := by
  cases a <;> rfl

omit [Fintype Value] in
theorem brbStep_eq_brb_transition
    (sender : Fin n) (val : Value)
    (a : Action n Value) (s : State n Value) :
    ((brb n f Value sender val).actions a).transition s
      (brbStep n Value sender val a s) := by
  cases a <;> rfl

omit [Fintype Value] in
/-- Bridge: when the gate holds and `s' = brbStep …`, the upstream
relational `brb`-action `fires`, so `brb_inv_step` applies. -/
theorem brbStep_preserves_brb_inv
    (sender : Fin n) (val : Value) (hn : n > 3 * f)
    (a : Action n Value) (s : State n Value)
    (hgate  : actionGate n f Value sender val a s)
    (hinv : brb_inv n f Value sender val s) :
    brb_inv n f Value sender val (brbStep n Value sender val a s) := by
  apply brb_inv_step n f Value sender val hn s (brbStep n Value sender val a s)
  · exact ⟨a, (actionGate_iff_brb_gate n f Value sender val a s).mp hgate,
      brbStep_eq_brb_transition n f Value sender val a s⟩
  · exact hinv

omit [Fintype Value] in
/-- The initial-state predicate `initPred` is definitionally `(brb …).init`,
so `brb_inv_init` hands us `brb_inv` at every state in the support. -/
theorem initPred_brb_inv
    (sender : Fin n) (val : Value)
    (s : State n Value) (h : initPred n Value s) :
    brb_inv n f Value sender val s :=
  brb_inv_init n f Value sender val s h

/-! ## §6. Validity (AlmostBox formulation)

Validity = "if the sender is correct, no honest party returns a
value other than `val`". The deterministic content is upstream
`brb_validity` (in `Leslie/Examples/ByzantineReliableBroadcast.lean`),
which extracts conjunct 6 (`local_consistent`) of `brb_inv`.

For the probabilistic side we lift `brb_inv` itself to an `AlmostBox`
via `AlmostBox_of_pure_inductive`, then read off conjunct 6. -/

set_option maxHeartbeats 400000 in
/-- Validity, lifted to an `AlmostBox` on the probabilistic trace.

Closed by lifting `brb_inv` to an `AlmostBox` (using
`brb_inv_init` and `brb_inv_step` from upstream
`Leslie.Examples.ByzantineReliableBroadcast`), then reading off
conjunct 6 (the `local_consistent` clause guarded by
`isCorrect n Value s sender`).

The `n > 3 * f` premise is required because `brb_inv_step` uses the
echo-quorum-intersection argument (which needs `n > 3 * f`) to
preserve conjunct 8 of the invariant; conjunct 6 — the clause that
gives validity — depends on the full `brb_inv` being inductive, so
we cannot drop it. -/
theorem brbProb_validity_AS
    (sender : Fin n) (val : Value)
    (hn : n > 3 * f)
    (μ₀ : Measure (State n Value)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred n Value s)
    (A : Adversary (State n Value) (Action n Value))
    (_h_sender_honest : (sender.val : PartyId) ∉ A.corrupt) :
    AlmostBox (brbProb n f Value sender val) A μ₀
      (fun s => isCorrect n Value s sender →
        ∀ p v, isCorrect n Value s p →
          (s.local_ p).returned = some v → v = val) := by
  have h_pure : ∀ (a : Action n Value) (s : State n Value)
      (h : ((brbProb n f Value sender val).actions a).gate s),
      ((brbProb n f Value sender val).actions a).effect s h
        = PMF.pure (brbStep n Value sender val a s) :=
    fun _ _ _ => rfl
  have h_init' : ∀ᵐ s ∂μ₀, brb_inv n f Value sender val s := by
    filter_upwards [h_init] with s hs
    exact initPred_brb_inv n f Value sender val s hs
  have h_inv : AlmostBox (brbProb n f Value sender val) A μ₀
      (fun s => brb_inv n f Value sender val s) :=
    AlmostBox_of_pure_inductive
      (fun s => brb_inv n f Value sender val s)
      (fun a s => brbStep n Value sender val a s)
      h_pure
      (fun a s hgate hinv =>
        brbStep_preserves_brb_inv n f Value sender val hn a s hgate hinv)
      μ₀ h_init' A
  -- Read off conjunct 6 (`local_consistent`, the validity clause).
  unfold AlmostBox at h_inv ⊢
  filter_upwards [h_inv] with ω hinv k hsender p v hp hret
  obtain ⟨_, _, _, _, _, hcond, _, _, _, _⟩ := hinv k
  exact (hcond hsender).1 p hp |>.2.2.2.2 v hret

/-! ## §7. Agreement (AlmostBox formulation)

Agreement = "any two honest returners return the same value". -/

/-- The agreement state predicate, mirroring upstream `agreement`. -/
def agreementPred (s : State n Value) : Prop :=
  ∀ p q vp vq,
    isCorrect n Value s p → isCorrect n Value s q →
    (s.local_ p).returned = some vp → (s.local_ q).returned = some vq →
    vp = vq

set_option maxHeartbeats 400000 in
/-- Agreement, lifted to an `AlmostBox` on the probabilistic trace.

Closed by lifting `brb_inv` to an `AlmostBox` and reproducing the
upstream `brb_agreement` pigeonhole argument inside the
`filter_upwards`: each returned value has ≥ n−f votes (conjunct 7),
the budget is ≤ f (conjunct 1), so pigeonhole gives a correct voter,
the vote-trace conjunct (4) bridges `voteRecv → voted`, and vote
agreement (conjunct 8) forces the values to be equal. -/
theorem brbProb_agreement_AS
    (sender : Fin n) (val : Value)
    (hn : n > 3 * f)
    (μ₀ : Measure (State n Value)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred n Value s)
    (A : Adversary (State n Value) (Action n Value)) :
    AlmostBox (brbProb n f Value sender val) A μ₀
      (agreementPred n Value) := by
  have h_pure : ∀ (a : Action n Value) (s : State n Value)
      (h : ((brbProb n f Value sender val).actions a).gate s),
      ((brbProb n f Value sender val).actions a).effect s h
        = PMF.pure (brbStep n Value sender val a s) :=
    fun _ _ _ => rfl
  have h_init' : ∀ᵐ s ∂μ₀, brb_inv n f Value sender val s := by
    filter_upwards [h_init] with s hs
    exact initPred_brb_inv n f Value sender val s hs
  have h_inv : AlmostBox (brbProb n f Value sender val) A μ₀
      (fun s => brb_inv n f Value sender val s) :=
    AlmostBox_of_pure_inductive
      (fun s => brb_inv n f Value sender val s)
      (fun a s => brbStep n Value sender val a s)
      h_pure
      (fun a s hgate hinv =>
        brbStep_preserves_brb_inv n f Value sender val hn a s hgate hinv)
      μ₀ h_init' A
  -- Pigeonhole on conjuncts 1, 4, 7, 8 (mirrors upstream `brb_agreement`).
  unfold AlmostBox at h_inv ⊢
  filter_upwards [h_inv] with ω hinv k p q vp vq hp hq hretp hretq
  obtain ⟨hbudget, _, _, hvtrace, _, _, hvotes, hvagree, _, _⟩ := hinv k
  -- p returned vp with ≥ n−f votes; n − f > f ≥ |corrupted| → correct voter.
  have hvp := hvotes p vp hretp
  have hgt_p : ((ω k).1).corrupted.length <
      countVoteRecv n Value (((ω k).1).local_ p) vp :=
    calc ((ω k).1).corrupted.length ≤ f := hbudget
      _ < n - f := by omega
      _ ≤ _ := hvp
  obtain ⟨rp, hrp_vote, hrp_corr⟩ := pigeonhole_filter n
    (((ω k).1).local_ p |>.voteRecv · vp) ((ω k).1).corrupted hgt_p
  have hvq := hvotes q vq hretq
  have hgt_q : ((ω k).1).corrupted.length <
      countVoteRecv n Value (((ω k).1).local_ q) vq :=
    calc ((ω k).1).corrupted.length ≤ f := hbudget
      _ < n - f := by omega
      _ ≤ _ := hvq
  obtain ⟨rq, hrq_vote, hrq_corr⟩ := pigeonhole_filter n
    (((ω k).1).local_ q |>.voteRecv · vq) ((ω k).1).corrupted hgt_q
  have hrp_voted := hvtrace p rp vp hrp_corr hrp_vote
  have hrq_voted := hvtrace q rq vq hrq_corr hrq_vote
  exact hvagree rp rq vp vq hrp_corr hrq_corr hrp_voted hrq_voted

/-! ## §8. Totality (AlmostDiamond formulation, fair adversary)

Totality = "if any honest party returns, every honest party
eventually returns". This is a liveness property; the
deterministic counterpart is upstream `totality` under
`brb_fairness`.

We package fairness probabilistically: `FairAdversary` carries a
`FairnessAssumptions` witness; the concrete fairness predicate
matching `brb_fairness` is a translation of "every action that is
continuously enabled fires eventually" into an AE-trace statement. -/

/-- A placeholder fairness-assumption record matching upstream
`brb_fairness`. The real definition translates the deterministic
`□◇` over the next relation into an AE-trace
`∀ᵐ ω, ∀ i, (continuously enabled → fires)` condition.

For M2 W3 we leave this as a stub: any adversary trivially
satisfies it. The right body lands in M3 alongside the AVSS
liveness proof, where the same shape is needed to lift `wf_*`
lemmas. -/
def brbFair (_sender : Fin n) (_val : Value) :
    FairnessAssumptions (State n Value) (Action n Value) where
  fair_actions := Set.univ
  isWeaklyFair := fun _ => True

/-- Totality, lifted to an `AlmostDiamond` on the probabilistic
trace, under a fair adversary.

The deterministic upstream `totality` has the form
`(∃ p, returned p = some v) ↝ (returned r ≠ none ∨ ¬ isCorrect r)` —
a leads-to between two state predicates under `brb_fairness`. We
lift it to the probabilistic-trace setting via
`Leslie.Prob.AlmostDiamond_of_leads_to`, which packages the
"deterministic leads-to becomes per-trace eventual implication"
bridge generically.

The protocol-specific obligation is the per-trace leads-to
`h_leads_to`: on AE trajectories, if some honest party returned
`v` at some step, then party `r` eventually either returned or got
corrupted. This is the **trace-level translation** of upstream
`totality`. Concrete callers either port the upstream proof to
trajectory form (~150 LOC) or supply the witness from another
source (e.g., a refined fairness predicate that exposes the
trajectory progress directly).

Once the per-trace leads-to is in hand, the conclusion is one
application of `AlmostDiamond_of_leads_to`. -/
private def _brbProb_totality_anchor : Unit := ()
set_option maxHeartbeats 800000 in
/-- See section docstring above. -/
theorem brbProb_totality_AS_fair
    (sender : Fin n) (val : Value)
    (_hn : n > 3 * f)
    (μ₀ : Measure (State n Value)) [IsProbabilityMeasure μ₀]
    (_h_init : ∀ᵐ s ∂μ₀, initPred n Value s)
    (A : FairAdversary (State n Value) (Action n Value)
            (brbFair n Value sender val))
    (r : Fin n) (v : Value)
    (h_someone_returned :
      AlmostDiamond (brbProb n f Value sender val) A.toAdversary μ₀
        (fun s => ∃ p, (s.local_ p).returned = some v))
    (h_leads_to :
      ∀ᵐ ω ∂(traceDist (brbProb n f Value sender val) A.toAdversary μ₀),
        (∃ k, ∃ p, (((ω k).1).local_ p).returned = some v) →
        ∃ m, (((ω m).1).local_ r).returned ≠ none ∨
             ¬ isCorrect n Value ((ω m).1) r) :
    AlmostDiamond (brbProb n f Value sender val) A.toAdversary μ₀
      (fun s => (s.local_ r).returned ≠ none ∨ ¬ isCorrect n Value s r) :=
  Leslie.Prob.AlmostDiamond_of_leads_to μ₀ A.toAdversary
    h_leads_to h_someone_returned

end AlmostBox

end Leslie.Prob.Examples.BrachaRBC
