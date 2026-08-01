import Batteries.Data.List.Lemmas
import Leslie.Examples.Combinators.PhaseCounting

/-! # Single-Proposer Paxos: Bounded-Unrolling Feasibility Test

    A clean-slate minimal Paxos-lite model: one proposer with a fixed
    ballot and fixed value, `n` acceptors. This file is a feasibility
    test of the **phase-counting diameter argument** described in
    `docs/cutoff-theorems.md` §5.13.

    Unlike OTR / Majority (which are *phase absorbing* — one step locks
    in a value), single-proposer Paxos is *phase counting*: every action
    strictly increases a progress measure bounded by `2 * n`, so any
    trace has length at most `2 * n`.

    Safety (agreement) is trivial because there is only one proposer,
    hence only one value can ever be accepted. The interesting content
    is the **bounded-unrolling machinery**.

    The file is intentionally self-contained: it depends only on the
    abstract `PhaseCounting` framework in
    `Leslie/Examples/Combinators/PhaseCounting.lean`. Core Lean 4 only;
    no Mathlib.
-/

namespace SingleProposerPaxos

/-! ## Section 1: Model -/

/-- The set of possible proposer values. We pick `Fin 2` so enumeration
    of initial states is finite. -/
abbrev Val : Type := Fin 2

/-- Per-acceptor local state. -/
structure AcceptorState where
  promised : Bool
  accepted : Option Val
  deriving DecidableEq, Repr

/-- Global state: `n` acceptors plus the (fixed) proposer value. -/
structure PaxosState (n : Nat) where
  locals : Fin n → AcceptorState
  proposerValue : Val

/-- The two action kinds. -/
inductive Action (n : Nat) where
  | prepare : Fin n → Action n
  | accept  : Fin n → Action n

/-- Update function for `locals`. -/
def setLocal {n : Nat} (f : Fin n → AcceptorState) (i : Fin n)
    (a : AcceptorState) : Fin n → AcceptorState :=
  fun j => if j = i then a else f j

@[simp] theorem setLocal_self {n : Nat} (f : Fin n → AcceptorState) (i : Fin n)
    (a : AcceptorState) : setLocal f i a i = a := by
  simp [setLocal]

@[simp] theorem setLocal_ne {n : Nat} (f : Fin n → AcceptorState) (i j : Fin n)
    (a : AcceptorState) (h : j ≠ i) : setLocal f i a j = f j := by
  simp [setLocal, h]

/-- Result of a prepare action at acceptor `i`. -/
def preparedAt (a : AcceptorState) : AcceptorState :=
  { a with promised := true }

/-- Result of an accept action at acceptor `i` with value `v`. -/
def acceptedAt (a : AcceptorState) (v : Val) : AcceptorState :=
  { a with accepted := some v }

/-- One-step transition as a predicate on pre/post states and an action. -/
def step {n : Nat} (s s' : PaxosState n) (a : Action n) : Prop :=
  match a with
  | .prepare i =>
      (s.locals i).promised = false ∧
      s' = { s with locals := setLocal s.locals i (preparedAt (s.locals i)) }
  | .accept i =>
      (s.locals i).promised = true ∧
      (s.locals i).accepted = none ∧
      s' = { s with locals :=
              setLocal s.locals i (acceptedAt (s.locals i) s.proposerValue) }

/-- Reachability from the canonical initial state. -/
def initialState (n : Nat) (v : Val) : PaxosState n where
  locals := fun _ => { promised := false, accepted := none }
  proposerValue := v

inductive Reachable {n : Nat} : PaxosState n → Prop where
  | init : ∀ v, Reachable (initialState n v)
  | step : ∀ {s s'} a, Reachable s → step s s' a → Reachable s'

/-! ## Section 2: Phase counter and diameter bound -/

/-- Sum over a list of indices. -/
def listSum {α : Type _} (f : α → Nat) : List α → Nat
  | [] => 0
  | x :: xs => f x + listSum f xs

theorem listSum_le_const {α : Type _} (f : α → Nat) (k : Nat)
    (h : ∀ x, f x ≤ k) : ∀ (xs : List α), listSum f xs ≤ xs.length * k
  | [] => by simp [listSum]
  | x :: xs => by
      have hx := h x
      have hxs := listSum_le_const f k h xs
      simp [listSum, List.length_cons, Nat.succ_mul]
      omega

/-- Updating the function at a key not in the list leaves `listSum` unchanged. -/
theorem listSum_update_not_mem {α : Type _} [DecidableEq α]
    (f : α → Nat) (i : α) (v : Nat) (xs : List α) (hni : i ∉ xs) :
    listSum (fun j => if j = i then v else f j) xs = listSum f xs := by
  induction xs with
  | nil => simp [listSum]
  | cons y ys ih =>
    have hy : y ≠ i := by intro h; exact hni (by simp [h])
    have hys : i ∉ ys := fun h => hni (by simp [h])
    simp [listSum, if_neg hy, ih hys]

/-- Pointing-update lemma for `listSum` on a Nodup list containing `i`. -/
theorem listSum_update_mem {α : Type _} [DecidableEq α]
    (f : α → Nat) (i : α) (v : Nat) (xs : List α)
    (hmem : i ∈ xs) (hnd : xs.Nodup) :
    listSum (fun j => if j = i then v else f j) xs + f i = listSum f xs + v := by
  induction xs with
  | nil => cases hmem
  | cons x xs ih =>
    by_cases hx : x = i
    · -- `subst` may try to substitute `i` (a theorem param); rewrite instead.
      rw [hx] at hnd
      have hxni : i ∉ xs := (List.nodup_cons.mp hnd).1
      have hxs := listSum_update_not_mem f i v xs hxni
      show (if x = i then v else f x)
            + listSum (fun j => if j = i then v else f j) xs + f i
            = f x + listSum f xs + v
      rw [if_pos hx, hxs, hx]; omega
    · have hmem' : i ∈ xs := by
        cases hmem with
        | head => exact absurd rfl hx
        | tail _ h => exact h
      have hnd' : xs.Nodup := (List.nodup_cons.mp hnd).2
      have ih' := ih hmem' hnd'
      show (if x = i then v else f x)
            + listSum (fun j => if j = i then v else f j) xs + f i
            = f x + listSum f xs + v
      rw [if_neg hx]; omega

/-- Sum over `Fin n` of a `Nat`-valued function. -/
def finSum {n : Nat} (f : Fin n → Nat) : Nat :=
  listSum f (List.finRange n)

theorem finSum_le_const {n : Nat} (f : Fin n → Nat) (k : Nat)
    (h : ∀ i, f i ≤ k) : finSum f ≤ n * k := by
  unfold finSum
  have := listSum_le_const f k h (List.finRange n)
  rw [List.length_finRange] at this
  exact this

/-- Contribution of a single acceptor to the phase counter. -/
def acceptorPhase (a : AcceptorState) : Nat :=
  (if a.promised then 1 else 0) + (if a.accepted.isSome then 1 else 0)

theorem acceptorPhase_le_two (a : AcceptorState) : acceptorPhase a ≤ 2 := by
  unfold acceptorPhase
  by_cases h1 : a.promised <;> by_cases h2 : a.accepted.isSome <;> simp [h1, h2]

/-- Global phase counter. -/
def phaseCounter {n : Nat} (s : PaxosState n) : Nat :=
  finSum (fun i => acceptorPhase (s.locals i))

theorem phaseCounter_bounded {n : Nat} (s : PaxosState n) :
    phaseCounter s ≤ 2 * n := by
  unfold phaseCounter
  have := finSum_le_const (fun i => acceptorPhase (s.locals i)) 2
    (fun i => acceptorPhase_le_two _)
  omega

theorem listSum_zero {α : Type _} (f : α → Nat) (hf : ∀ x, f x = 0) :
    ∀ xs : List α, listSum f xs = 0
  | [] => by simp [listSum]
  | x :: xs => by simp [listSum, hf x, listSum_zero f hf xs]

theorem phaseCounter_initialState (n : Nat) (v : Val) :
    phaseCounter (initialState n v) = 0 := by
  unfold phaseCounter finSum
  apply listSum_zero
  intro i
  simp [initialState, acceptorPhase]

/-- Replacing one entry in a `finSum` shifts the sum by the delta. -/
theorem finSum_update {n : Nat} (f : Fin n → Nat) (i : Fin n) (v : Nat) :
    finSum (fun j => if j = i then v else f j) + f i = finSum f + v := by
  unfold finSum
  exact listSum_update_mem f i v (List.finRange n)
    (List.mem_finRange i) (List.nodup_finRange n)

/-- Any `prepare i` action strictly increases `phaseCounter` by 1. -/
theorem phaseCounter_prepare {n : Nat} (s s' : PaxosState n) (i : Fin n)
    (hstep : step s s' (.prepare i)) :
    phaseCounter s' = phaseCounter s + 1 := by
  obtain ⟨hprom, hs'⟩ := hstep
  subst hs'
  unfold phaseCounter
  have hrw : (fun j => acceptorPhase
      ((setLocal s.locals i (preparedAt (s.locals i))) j)) =
      (fun j => if j = i then acceptorPhase (preparedAt (s.locals i))
                else acceptorPhase (s.locals j)) := by
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [setLocal, h]
  show finSum _ = _
  rw [hrw]
  have hfu := finSum_update (fun j => acceptorPhase (s.locals j)) i
    (acceptorPhase (preparedAt (s.locals i)))
  have hold : acceptorPhase (s.locals i) =
      (if (s.locals i).accepted.isSome then 1 else 0) := by
    unfold acceptorPhase; rw [hprom]; simp
  have hnew : acceptorPhase (preparedAt (s.locals i)) =
      1 + (if (s.locals i).accepted.isSome then 1 else 0) := by
    unfold acceptorPhase preparedAt; simp
  omega

/-- Any `accept i` action strictly increases `phaseCounter` by 1. -/
theorem phaseCounter_accept {n : Nat} (s s' : PaxosState n) (i : Fin n)
    (hstep : step s s' (.accept i)) :
    phaseCounter s' = phaseCounter s + 1 := by
  obtain ⟨hprom, hacc, hs'⟩ := hstep
  subst hs'
  unfold phaseCounter
  have hrw : (fun j => acceptorPhase
      ((setLocal s.locals i (acceptedAt (s.locals i) s.proposerValue)) j)) =
      (fun j => if j = i
                then acceptorPhase (acceptedAt (s.locals i) s.proposerValue)
                else acceptorPhase (s.locals j)) := by
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [setLocal, h]
  show finSum _ = _
  rw [hrw]
  have hfu := finSum_update (fun j => acceptorPhase (s.locals j)) i
    (acceptorPhase (acceptedAt (s.locals i) s.proposerValue))
  have hold : acceptorPhase (s.locals i) = 1 := by
    unfold acceptorPhase; simp [hprom, hacc]
  have hnew : acceptorPhase (acceptedAt (s.locals i) s.proposerValue) = 2 := by
    unfold acceptorPhase acceptedAt; simp [hprom]
  omega

/-- **Monotonicity: every action strictly increases `phaseCounter` by 1.** -/
theorem phaseCounter_monotone {n : Nat} (s s' : PaxosState n) (a : Action n)
    (hstep : step s s' a) :
    phaseCounter s' = phaseCounter s + 1 := by
  cases a with
  | prepare i => exact phaseCounter_prepare s s' i hstep
  | accept  i => exact phaseCounter_accept  s s' i hstep

/-! ## Section 3: Safety (agreement) -/

/-- Agreement: any two accepted values agree. -/
def agreement {n : Nat} (s : PaxosState n) : Prop :=
  ∀ (i j : Fin n) (v w : Val),
    (s.locals i).accepted = some v →
    (s.locals j).accepted = some w →
    v = w

/-- Every reachable state satisfies `agreement`. Trivially, since only
    the single proposer value can ever be written. -/
theorem agreement_reachable {n : Nat} (s : PaxosState n) (h : Reachable s) :
    agreement s := by
  -- Strengthen: every accepted value equals `s.proposerValue`, and
  -- `proposerValue` is preserved along reachability.
  suffices hinv : (∀ i, (s.locals i).accepted = none ∨
                         (s.locals i).accepted = some s.proposerValue) by
    intro i j v w hv hw
    rcases hinv i with hi | hi
    · rw [hi] at hv; cases hv
    · rw [hi] at hv; cases hv
      rcases hinv j with hj | hj
      · rw [hj] at hw; cases hw
      · rw [hj] at hw; cases hw; rfl
  induction h with
  | init v =>
    intro i
    left
    simp [initialState]
  | step a _ hstep ih =>
    rename_i s₀ s₁
    intro i
    cases a with
    | prepare k =>
      obtain ⟨_, hs'⟩ := hstep
      subst hs'
      by_cases h : i = k
      · subst h
        simp [setLocal]
        -- new local has same .accepted as old
        rcases ih i with hi | hi
        · left; exact hi
        · right; exact hi
      · simp [setLocal, h]
        exact ih i
    | accept k =>
      obtain ⟨_, _, hs'⟩ := hstep
      subst hs'
      by_cases h : i = k
      · subst h
        right
        simp [setLocal, acceptedAt]
      · simp [setLocal, h]
        exact ih i

/-! ## Section 4: Bounded-unrolling theorem (via abstract framework)

    "Bounded-depth safety" is equivalent to "safety from the canonical
    initial state", because the initial state has `phaseCounter = 0`
    and any trace is at most `2n` long. The heavy lifting (`StepsFrom`,
    trace-length bound, bounded-unrolling iff) is done once, in
    `Leslie.Examples.Combinators.PhaseCountingThreshold`. -/

/-- Package single-proposer Paxos (at proposer value `v`) as a
    `PhaseCountingSystem`. -/
def singleProposerSystem (n : Nat) (v : Val) :
    PhaseCounting.PhaseCountingSystem where
  State        := PaxosState n
  Action       := Action n
  step         := step
  init         := initialState n v
  phaseCounter := phaseCounter
  bound        := 2 * n
  init_zero    := phaseCounter_initialState n v
  step_mono    := by
    intro s s' a hstep
    have := phaseCounter_monotone s s' a hstep
    omega
  step_bounded := by
    intro s s' _ _
    exact phaseCounter_bounded s'

/-- Helper: walking a framework `StepsFrom` for `singleProposerSystem n v`
    folds local `Reachable` along the trace. -/
private theorem reachable_of_stepsFrom {n : Nat} {v : Val} :
    ∀ (acts : List (Action n)) {s₀ s : PaxosState n},
      Reachable s₀ →
      PhaseCounting.StepsFrom (singleProposerSystem n v) s₀ acts s →
      Reachable s
  | [], s₀, s, hr₀, h => by
    -- nil case: h must be StepsFrom.nil, so s = s₀
    match h with
    | PhaseCounting.StepsFrom.nil _ => exact hr₀
  | a :: as, s₀, s, hr₀, h => by
    match h with
    | PhaseCounting.StepsFrom.cons _ _ hstep htail =>
      exact reachable_of_stepsFrom as (Reachable.step a hr₀ hstep) htail

/-- Adapter: the local `Reachable` predicate is equivalent to the
    framework's `Reachable` for `singleProposerSystem n v`, once we
    existentially quantify over the choice of initial proposer value. -/
theorem reachable_iff_framework {n : Nat} (s : PaxosState n) :
    Reachable s ↔ ∃ v, PhaseCounting.Reachable (singleProposerSystem n v) s := by
  constructor
  · intro h
    induction h with
    | init v => exact ⟨v, PhaseCounting.Reachable.init⟩
    | step a _ hstep ih =>
      obtain ⟨v, hr⟩ := ih
      exact ⟨v, PhaseCounting.Reachable.step (P := singleProposerSystem n v) a hr hstep⟩
  · rintro ⟨v, hr⟩
    obtain ⟨acts, hfrom⟩ := (PhaseCounting.reachable_iff_stepsFrom
      (singleProposerSystem n v) s).mp hr
    exact reachable_of_stepsFrom acts (Reachable.init v) hfrom

/-- Safety of all states reachable from `initialState n v` in ≤ `k` steps
    (expressed via the framework's abstract `StepsFrom`). -/
def safeUpTo (n : Nat) (k : Nat) : Prop :=
  ∀ v : Val, ∀ acts : List (Action n), acts.length ≤ k →
    ∀ s', PhaseCounting.StepsFrom (singleProposerSystem n v) (initialState n v) acts s' →
      agreement s'

/-- Safety of every reachable state. -/
def safeAll (n : Nat) : Prop :=
  ∀ s : PaxosState n, Reachable s → agreement s

/-- **Main theorem: Single-proposer Paxos bounded unrolling.** Derived
    from the abstract `phase_counting_bounded_unrolling` by ranging over
    the choice of proposer value. -/
theorem single_proposer_bounded_unrolling (n : Nat) :
    safeAll n ↔ safeUpTo n (2 * n) := by
  constructor
  · intro hall v acts _ s' hfrom
    apply hall
    refine (reachable_iff_framework s').mpr ⟨v, ?_⟩
    exact PhaseCounting.stepsFrom_preserves_reachable hfrom PhaseCounting.Reachable.init
  · intro hsmall s hreach
    obtain ⟨v, hr⟩ := (reachable_iff_framework s).mp hreach
    have hiff :=
      PhaseCounting.phase_counting_bounded_unrolling (singleProposerSystem n v)
        (fun s => agreement s)
    -- `safeAll` direction of the abstract iff reduces to per-v bounded safety.
    have hallV : PhaseCounting.safeAll (singleProposerSystem n v) (fun s => agreement s) := by
      refine hiff.mpr ?_
      intro acts hlen s' hfrom
      exact hsmall v acts hlen s' hfrom
    exact hallV s hr

/-- A corollary using reachability directly. -/
theorem agreement_bounded_unrolling (n : Nat) : safeAll n := by
  intro s hreach
  exact agreement_reachable s hreach

/-! ## Section 5: Executable demo at `n = 3` -/

/-- Decidable agreement check: collect all accepted values; all pairs must agree. -/
def agreementB {n : Nat} (s : PaxosState n) : Bool :=
  let accepted := (List.finRange n).filterMap (fun i => (s.locals i).accepted)
  accepted.all (fun v => accepted.all (fun w => v == w))

/-- Execute one action if enabled; returns `none` if disabled. -/
def stepB {n : Nat} (s : PaxosState n) (a : Action n) : Option (PaxosState n) :=
  match a with
  | .prepare i =>
    if (s.locals i).promised then none
    else
      let a' : AcceptorState := { (s.locals i) with promised := true }
      some { s with locals := setLocal s.locals i a' }
  | .accept i =>
    if (s.locals i).promised && (s.locals i).accepted.isNone then
      let a' : AcceptorState := { (s.locals i) with accepted := some s.proposerValue }
      some { s with locals := setLocal s.locals i a' }
    else none

/-- Enumerate all actions for a fixed `n`. -/
def allActions (n : Nat) : List (Action n) :=
  (List.finRange n).map Action.prepare ++ (List.finRange n).map Action.accept

/-- BFS up to depth `d`, checking agreement on every reachable state. -/
def bfsCheck {n : Nat} (d : Nat) (frontier : List (PaxosState n)) : Bool :=
  match d with
  | 0 => frontier.all agreementB
  | d+1 =>
    if frontier.all agreementB then
      let next := frontier.flatMap (fun s =>
        (allActions n).filterMap (fun a => stepB s a))
      bfsCheck d next
    else false

/-- Depth-6 agreement check at `n = 3` starting from both canonical
    initial states (proposer value 0 and 1). -/
def verifyN3 : Bool :=
  let s0 : PaxosState 3 := initialState 3 0
  let s1 : PaxosState 3 := initialState 3 1
  bfsCheck 6 [s0, s1]

theorem verifyN3_ok : verifyN3 = true := by native_decide

#eval verifyN3

/-- Sanity check: phase counter at `initialState` is 0. -/
example : phaseCounter (initialState 3 0) = 0 := by
  unfold phaseCounter finSum acceptorPhase initialState
  decide

/-- Sanity check: phase counter bound at `n = 3` gives ≤ 6. -/
example : ∀ (s : PaxosState 3), phaseCounter s ≤ 6 := by
  intro s
  have := phaseCounter_bounded s
  omega

end SingleProposerPaxos
