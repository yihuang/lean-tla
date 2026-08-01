import Leslie.Round

/-! ## Ben-Or's Randomized Binary Consensus (1983)

    This file models Ben-Or's binary consensus protocol for `n` processes
    (`Fin n`) in the Heard-Of style. Each process stores a current binary
    value, an optional witness from the report phase, and an optional
    decision.

    ### Model

    A logical round has two phases:

    **Phase 1 (Report).**
    Each process broadcasts its current value. A receiver witnesses `v`
    exactly when it sees value `v` from a strict majority of senders.

    **Phase 2 (Propose).**
    Each process broadcasts its witness. A receiver decides `v` exactly
    when it sees witness `v` from a strict majority of senders. If no
    witness has strict majority support, the process updates its value
    using the nondeterministic coin oracle.

    The coin is relevant for liveness, but not for the safety argument:
    the proof treats it as arbitrary nondeterminism.

    ### Assumptions

    The unrestricted spec `benOrSpec` models arbitrary HO sets and coin
    outcomes. That model is useful operationally, but its agreement
    theorem is false in general: under lossy communication, coin flips can
    destroy an existing majority and later allow a conflicting decision.

    The proved safety theorem in this file therefore targets
    `benOrReliableSpec`, which restricts every HO set to be fully reliable:
    every sent message is delivered to every receiver in both phases.

    Under this assumption:
    - a strict majority of holders of value `v` makes every process
      witness `v` in the report phase, and
    - a strict majority of witnesses for `v` makes every undecided process
      decide `v` in the propose phase.

    ### Proof outline

    The proof uses a combined invariant `benor_inv` with three pieces:

    1. `lock_inv`
       If some process has decided `v`, then a strict majority of all
       processes currently hold `v`.
    2. `decided_consistent`
       A decided process stores the decided value in its `val` field.
    3. `report_majority_inv`
       In phase 1, under reliable communication, a process witnesses `v`
       exactly when `v` already has a strict global holder majority.

    The invariant is easy in the initial state.

    For the report step:
    - `val` and `decided` are unchanged, so `lock_inv` and
      `decided_consistent` are preserved immediately.
    - reliability lets us identify local report counts with global holder
      counts, which proves `report_majority_inv`.

    For the propose step:
    - a new decision for `v` implies a strict global majority of witnesses
      for `v`, and `report_majority_inv` turns that into a strict global
      majority of holders of `v` in the pre-state;
    - once such a holder majority exists, reliability makes every process
      see witness-majority `v`, so every undecided process switches to `v`
      and every already-decided process is shown to already hold `v`;
    - therefore every process holds `v` after the step, which is stronger
      than the lock condition.

    Agreement then follows from a pigeonhole argument: two distinct
    decided values would require two disjoint strict majorities of
    holders, which is impossible.
-/

open TLA

namespace BenOr

variable (n : Nat)

/-! ### State and messages -/

/-- Local state of each process. -/
structure LState where
  /-- Current binary value: 0 or 1. -/
  val : Fin 2
  /-- Value witnessed in phase 1, if any. A process witnesses `v` if it
      receives `v` from a strict majority of senders. -/
  witnessed : Option (Fin 2)
  /-- Decided value, if any. Once set, decisions are permanent. -/
  decided : Option (Fin 2)
  deriving DecidableEq, Repr

/-- Global state of the protocol. -/
structure GState (n : Nat) where
  /-- Current round number (increments after each complete two-phase round). -/
  round : Nat
  /-- Current phase: 0 = Report, 1 = Propose. -/
  phase : Fin 2
  /-- Local state of each process. -/
  locals : Fin n → LState

/-! ### Counting utilities -/

/-- Count how many processes in the HO set of `p` sent value `v`. -/
def countVal (locals : Fin n → LState) (ho : HOCollection (Fin n))
    (p : Fin n) (v : Fin 2) : Nat :=
  ((List.finRange n).filter fun q => ho p q && ((locals q).val == v)).length

/-- Check if value `v` has strict majority support among messages received by `p`. -/
def hasValMajority (locals : Fin n → LState) (ho : HOCollection (Fin n))
    (p : Fin n) (v : Fin 2) : Bool :=
  countVal n locals ho p v * 2 > n

/-- Find the value (if any) that has majority support in p's received messages. -/
def findValMajority (locals : Fin n → LState) (ho : HOCollection (Fin n))
    (p : Fin n) : Option (Fin 2) :=
  (List.finRange 2).find? fun v => hasValMajority n locals ho p v

/-- Count how many processes in the HO set of `p` witnessed value `v`. -/
def countWitness (locals : Fin n → LState) (ho : HOCollection (Fin n))
    (p : Fin n) (v : Fin 2) : Nat :=
  ((List.finRange n).filter fun q =>
    ho p q && ((locals q).witnessed == some v)).length

/-- Check if witness `v` has strict majority support among messages received by `p`. -/
def hasWitnessMajority (locals : Fin n → LState) (ho : HOCollection (Fin n))
    (p : Fin n) (v : Fin 2) : Bool :=
  countWitness n locals ho p v * 2 > n

/-- Find the witness (if any) that has majority support in p's received proposals. -/
def findWitnessMajority (locals : Fin n → LState) (ho : HOCollection (Fin n))
    (p : Fin n) : Option (Fin 2) :=
  (List.finRange 2).find? fun v => hasWitnessMajority n locals ho p v

/-! ### Counting actual holders -/

/-- Number of processes holding value `v` in the current state. -/
def countHolding (v : Fin 2) (s : GState n) : Nat :=
  ((List.finRange n).filter fun p =>
    decide ((s.locals p).val = v)).length

/-- Number of processes that witnessed value `v` in the current state. -/
def countWitnessed (v : Fin 2) (s : GState n) : Nat :=
  ((List.finRange n).filter fun p =>
    decide ((s.locals p).witnessed = some v)).length

/-! ### Phase transitions -/

/-- Phase 1 (Report): Each process broadcasts its value. If a process
    receives the same value `v` from > n/2 senders, it witnesses `v`.
    Only `witnessed` is updated; `val` and `decided` are unchanged. -/
def stepReport (s s' : GState n) (ho : HOCollection (Fin n)) : Prop :=
  s.phase = 0 ∧ s'.phase = 1 ∧ s'.round = s.round ∧
  ∀ p, s'.locals p =
    { val := (s.locals p).val,
      witnessed := findValMajority n s.locals ho p,
      decided := (s.locals p).decided }

/-- Phase 2 (Propose): Each process broadcasts its witness. If a process
    receives the same witness `v` from > n/2 senders, it decides `v`.
    Otherwise, it flips a coin (the `coin` oracle provides a random bit).
    Decisions are permanent: once decided, a process keeps its decision. -/
def stepPropose (s s' : GState n) (ho : HOCollection (Fin n))
    (coin : Fin n → Fin 2) : Prop :=
  s.phase = 1 ∧ s'.phase = 0 ∧ s'.round = s.round + 1 ∧
  ∀ p, s'.locals p =
    if (s.locals p).decided.isSome then
      -- Already decided: keep state, but update witnessed for the new round
      { val := (s.locals p).val,
        witnessed := none,
        decided := (s.locals p).decided }
    else
      match findWitnessMajority n s.locals ho p with
      | some v =>
        -- Majority witness: decide v
        { val := v, witnessed := none, decided := some v }
      | none =>
        -- No majority witness: flip coin
        { val := coin p, witnessed := none, decided := none }

/-- The Ben-Or protocol specification. -/
def benOrSpec : Spec (GState n) where
  init := fun s =>
    s.round = 0 ∧ s.phase = 0 ∧
    ∀ p, (s.locals p).witnessed = none ∧ (s.locals p).decided = none
  next := fun s s' =>
    (∃ ho, stepReport n s s' ho) ∨
    (∃ ho coin, stepPropose n s s' ho coin)

/-- Reliable communication assumption for a single phase.

    Content: every sender `q` is heard by every receiver `p`.
    Purpose: this turns local HO counts into global counts, which is the
    bridge used throughout the safety proof.
    Proof idea: this is a definition, not a theorem; later lemmas rewrite
    filters using `ho p q = true` for all pairs. -/
def reliableHO (ho : HOCollection (Fin n)) : Prop :=
  ∀ p q, ho p q = true

/-- Ben-Or specialized to reliable communication in both phases.

    Content: this spec keeps the same initial states as `benOrSpec`, but
    only allows report/propose steps whose HO sets satisfy `reliableHO`.
    Purpose: this is the actual safety model proved in the file.
    Proof idea: this is a definitional restriction of the transition
    relation; the substantive work is in proving the invariant preserved
    under these restricted steps. -/
def benOrReliableSpec : Spec (GState n) where
  init := (benOrSpec n).init
  next := fun s s' =>
    (∃ ho, reliableHO n ho ∧ stepReport n s s' ho) ∨
    (∃ ho coin, reliableHO n ho ∧ stepPropose n s s' ho coin)

/-! ### Safety property -/

/-- Agreement: all decided processes agree on the same value. -/
def agreement (s : GState n) : Prop :=
  ∀ p q v w,
    (s.locals p).decided = some v →
    (s.locals q).decided = some w →
    v = w

/-! ### Pigeonhole: two majorities can't coexist -/

/-- Two disjoint strict majorities cannot coexist.

    Content: if predicates for values `v` and `w` are disjoint and both
    hold on more than half of the `n` processes, contradiction.
    Purpose: this is the core pigeonhole argument behind agreement.
    Proof outline: apply `filter_disjoint_length_le` to bound the sum of
    the two counts by `n`, then use arithmetic to show two strict
    majorities would force the sum to exceed `n`. -/
theorem majority_unique
    (f : Fin n → Fin 2) (v w : Fin 2) (hne : v ≠ w)
    (hv : ((List.finRange n).filter fun p => decide (f p = v)).length * 2 > n)
    (hw : ((List.finRange n).filter fun p => decide (f p = w)).length * 2 > n) :
    False := by
  have h_sum := filter_disjoint_length_le
    (fun p => decide (f p = v))
    (fun p => decide (f p = w))
    (List.finRange n)
    (by intro x ⟨h1, h2⟩
        simp [decide_eq_true_eq] at h1 h2
        rw [h1] at h2 ; exact hne h2)
  have h_len : (List.finRange n).length = n := List.length_finRange
  omega

/-! ### Helper lemmas -/

/-- `findValMajority` returning `some v` means `v` really has a report majority.

    Content: extracting the witness from `find?` yields a true
    `hasValMajority` test.
    Purpose: this connects the executable search procedure to the semantic
    majority predicate used in the proofs.
    Proof outline: unfold `findValMajority` and apply `List.find?_some`. -/
theorem findValMajority_hasValMajority
    {locals : Fin n → LState} {ho : HOCollection (Fin n)}
    {p : Fin n} {v : Fin 2}
    (h : findValMajority n locals ho p = some v) :
    hasValMajority n locals ho p v = true := by
  simp only [findValMajority] at h
  exact List.find?_some h

/-- `findWitnessMajority` returning `some v` means `v` really has a witness majority.

    Content: if the propose-phase majority search returns `v`, then the
    Boolean majority test for witness `v` is true.
    Purpose: this lets later proofs extract counting facts from a concrete
    decision step.
    Proof outline: identical to the report-phase version, using
    `List.find?_some`. -/
theorem findWitnessMajority_hasWitnessMajority
    {locals : Fin n → LState} {ho : HOCollection (Fin n)}
    {p : Fin n} {v : Fin 2}
    (h : findWitnessMajority n locals ho p = some v) :
    hasWitnessMajority n locals ho p v = true := by
  simp only [findWitnessMajority] at h
  exact List.find?_some h

/-- Under reliable communication, report counts equal global holder counts.

    Content: `countVal` at any receiver `p` equals `countHolding`.
    Purpose: this collapses a local HO-based count into a global one.
    Proof outline: unfold both counts and rewrite every `ho p q` to `true`,
    leaving the same filter predicate on `q`. -/
theorem countVal_reliable (s : GState n) (ho : HOCollection (Fin n))
    (hrel : reliableHO n ho) (p : Fin n) (v : Fin 2) :
    countVal n s.locals ho p v = countHolding n v s := by
  unfold countVal countHolding
  congr 1
  apply List.filter_congr
  intro q _
  rw [hrel p q]
  by_cases h : (s.locals q).val = v <;> simp [h]

/-- Under reliable communication, witness counts equal global witnessed counts.

    Content: `countWitness` at any receiver `p` equals `countWitnessed`.
    Purpose: this is the propose-phase analogue of `countVal_reliable`.
    Proof outline: same rewrite-by-reliability argument as for values. -/
theorem countWitness_reliable (s : GState n) (ho : HOCollection (Fin n))
    (hrel : reliableHO n ho) (p : Fin n) (v : Fin 2) :
    countWitness n s.locals ho p v = countWitnessed n v s := by
  unfold countWitness countWitnessed
  congr 1
  apply List.filter_congr
  intro q _
  rw [hrel p q]
  by_cases h : (s.locals q).witnessed = some v <;> simp [h]

/-- Under reliable communication, local report-majority detection is exactly global holder-majority.

    Content: `findValMajority ... = some v` iff `v` is held by a strict
    global majority.
    Purpose: this is the key semantic characterization of the report step.
    Proof outline:
    - forward direction: `findValMajority_hasValMajority` gives a local
      majority, then `countVal_reliable` turns it into a global one;
    - backward direction: on `Fin 2`, case split on `v = 0` or `v = 1`,
      show the chosen bit has majority, and rule out the other bit by
      `majority_unique`. -/
theorem findValMajority_reliable_iff (s : GState n) (ho : HOCollection (Fin n))
    (hrel : reliableHO n ho) (p : Fin n) (v : Fin 2) :
    findValMajority n s.locals ho p = some v ↔ countHolding n v s * 2 > n := by
  constructor
  · intro h
    have hv := findValMajority_hasValMajority (n := n) h
    unfold hasValMajority at hv
    rw [countVal_reliable (n := n) s ho hrel p v] at hv
    simpa using hv
  · intro hmaj
    rcases v with ⟨v, hvlt⟩
    have hv_cases : v = 0 ∨ v = 1 := by omega
    rcases hv_cases with rfl | rfl
    · have hmaj0 : countHolding n (0 : Fin 2) s * 2 > n := by
        simpa using hmaj
      have h0true : hasValMajority n s.locals ho p (0 : Fin 2) = true := by
        unfold hasValMajority
        rw [countVal_reliable (n := n) s ho hrel p (0 : Fin 2)]
        simp [hmaj0]
      change ([0, 1].find? (fun v => hasValMajority n s.locals ho p v) = some 0)
      simp [h0true]
    · have hnot0 : ¬ countHolding n ⟨0, by omega⟩ s * 2 > n := by
        intro h0
        have hne : (⟨0, by omega⟩ : Fin 2) ≠ ⟨1, hvlt⟩ := by
          intro h
          cases h
        exact majority_unique n (fun r => (s.locals r).val) ⟨0, by omega⟩ ⟨1, hvlt⟩ hne h0 hmaj
      have h0le : countHolding n (0 : Fin 2) s * 2 ≤ n := by
        have hnot0' : ¬ countHolding n (0 : Fin 2) s * 2 > n := by simpa using hnot0
        omega
      have hmaj1 : countHolding n (1 : Fin 2) s * 2 > n := by
        simpa using hmaj
      have h0false : hasValMajority n s.locals ho p (0 : Fin 2) = false := by
        unfold hasValMajority
        rw [countVal_reliable (n := n) s ho hrel p (0 : Fin 2)]
        simp [h0le]
      have h1true : hasValMajority n s.locals ho p (1 : Fin 2) = true := by
        unfold hasValMajority
        rw [countVal_reliable (n := n) s ho hrel p (1 : Fin 2)]
        simp [hmaj1]
      change ([0, 1].find? (fun v => hasValMajority n s.locals ho p v) = some 1)
      simp [h0false, h1true]

/-- Under reliable communication, local witness-majority detection is exactly global witnessed-majority.

    Content: `findWitnessMajority ... = some v` iff `v` has a strict
    global majority among witnessed values.
    Purpose: this lets the propose-phase proof reason globally about a
    local decision.
    Proof outline: identical to `findValMajority_reliable_iff`, but for
    `witnessed` instead of `val`. -/
theorem findWitnessMajority_reliable_iff (s : GState n) (ho : HOCollection (Fin n))
    (hrel : reliableHO n ho) (p : Fin n) (v : Fin 2) :
    findWitnessMajority n s.locals ho p = some v ↔ countWitnessed n v s * 2 > n := by
  constructor
  · intro h
    have hv := findWitnessMajority_hasWitnessMajority (n := n) h
    unfold hasWitnessMajority at hv
    rw [countWitness_reliable (n := n) s ho hrel p v] at hv
    simpa using hv
  · intro hmaj
    rcases v with ⟨v, hvlt⟩
    have hv_cases : v = 0 ∨ v = 1 := by omega
    rcases hv_cases with rfl | rfl
    · have hmaj0 : countWitnessed n (0 : Fin 2) s * 2 > n := by
        simpa using hmaj
      have h0true : hasWitnessMajority n s.locals ho p (0 : Fin 2) = true := by
        unfold hasWitnessMajority
        rw [countWitness_reliable (n := n) s ho hrel p (0 : Fin 2)]
        simp [hmaj0]
      change ([0, 1].find? (fun v => hasWitnessMajority n s.locals ho p v) = some 0)
      simp [h0true]
    · have hnot0 : ¬ countWitnessed n ⟨0, by omega⟩ s * 2 > n := by
        intro h0
        have h_sum := filter_disjoint_length_le
          (fun p => decide ((s.locals p).witnessed = some ⟨0, by omega⟩))
          (fun p => decide ((s.locals p).witnessed = some ⟨1, by omega⟩))
          (List.finRange n) (by
            intro x ⟨hx0, hx1⟩
            simp [decide_eq_true_eq] at hx0 hx1
            rw [hx0] at hx1
            cases hx1)
        have h_len : (List.finRange n).length = n := List.length_finRange
        unfold countWitnessed at h0 hmaj
        omega
      have h0le : countWitnessed n (0 : Fin 2) s * 2 ≤ n := by
        have hnot0' : ¬ countWitnessed n (0 : Fin 2) s * 2 > n := by simpa using hnot0
        omega
      have hmaj1 : countWitnessed n (1 : Fin 2) s * 2 > n := by
        simpa using hmaj
      have h0false : hasWitnessMajority n s.locals ho p (0 : Fin 2) = false := by
        unfold hasWitnessMajority
        rw [countWitness_reliable (n := n) s ho hrel p (0 : Fin 2)]
        simp [h0le]
      have h1true : hasWitnessMajority n s.locals ho p (1 : Fin 2) = true := by
        unfold hasWitnessMajority
        rw [countWitness_reliable (n := n) s ho hrel p (1 : Fin 2)]
        simp [hmaj1]
      change ([0, 1].find? (fun v => hasWitnessMajority n s.locals ho p v) = some 1)
      simp [h0false, h1true]

/-! ### Auxiliary invariant: the lock -/

/-- Lock invariant for agreement.

    Content: if some process has decided `v`, then strictly more than half
    the system currently holds `v`.
    Purpose: this is the main safety invariant projected to agreement.
    Proof idea: the heavy lifting is deferred to the step lemmas; once the
    invariant is available, agreement is immediate by pigeonhole. -/
def lock_inv (s : GState n) : Prop :=
  ∀ v, (∃ p : Fin n, (s.locals p).decided = some v) →
    countHolding n v s * 2 > n

/-- The lock invariant implies agreement.

    Content: from `lock_inv`, any two decided values must be equal.
    Purpose: this is the final projection from the invariant to the user
    visible safety property.
    Proof outline: instantiate `lock_inv` for both decided values and use
    `majority_unique` on the current `val` field. -/
theorem lock_inv_implies_agreement (s : GState n)
    (h : lock_inv n s) : agreement n s := by
  intro p q v w hv hw
  by_contra hne
  exact majority_unique n (fun r => (s.locals r).val) v w hne
    (h v ⟨p, hv⟩) (h w ⟨q, hw⟩)

/-! ### The lock invariant is inductive -/

/-- `lock_inv` holds initially.

    Content: the initial state has no decisions, so the implication in
    `lock_inv` is vacuous.
    Purpose: base case for the invariant proof.
    Proof outline: unfold the initializer and derive contradiction from a
    hypothetical initial decision. -/
theorem lock_inv_init :
    ∀ s, (benOrSpec n).init s → lock_inv n s := by
  intro s ⟨_, _, hinit⟩ v ⟨p, hp⟩
  have := (hinit p).2
  rw [this] at hp ; simp at hp

/-- Auxiliary consistency invariant tying `decided` to `val`.

    Content: if a process has decided `v`, then its current local value is
    also `v`.
    Purpose: the propose-phase proof needs this to show already-decided
    processes do not hold a conflicting value.
    Proof idea: the invariant is trivial initially and preserved because
    every transition either leaves `decided` alone or writes `val` and
    `decided` consistently. -/
def decided_consistent (s : GState n) : Prop :=
  ∀ p v, (s.locals p).decided = some v → (s.locals p).val = v

/-- `decided_consistent` holds initially.

    Content: there are no initial decisions.
    Purpose: base case for the auxiliary consistency invariant.
    Proof outline: unfold the initializer and rule out `some _` in the
    initial `decided` field. -/
theorem decided_consistent_init :
    ∀ s, (benOrSpec n).init s → decided_consistent n s := by
  intro s ⟨_, _, hinit⟩ p v hdec
  have := (hinit p).2
  rw [this] at hdec
  simp at hdec

/-- Report steps preserve `decided_consistent`.

    Content: a report step does not change `val` or `decided`.
    Purpose: preservation lemma for the auxiliary consistency invariant.
    Proof outline: rewrite with the step equation and reduce to the
    pre-state invariant. -/
theorem decided_consistent_report (s s' : GState n) (ho : HOCollection (Fin n))
    (hinv : decided_consistent n s) (hstep : stepReport n s s' ho) :
    decided_consistent n s' := by
  obtain ⟨_, _, _, hlocals⟩ := hstep
  intro p v hdec
  rw [hlocals p] at hdec ⊢
  simpa using hinv p v hdec

/-- Propose steps preserve `decided_consistent`.

    Content: if a process was already decided, it keeps its old `val`; if
    it newly decides `v`, the step writes both `val := v` and
    `decided := some v`.
    Purpose: this is the propose-phase preservation lemma for the
    auxiliary consistency invariant.
    Proof outline: case split on whether the process was already decided
    before the step and simplify the transition definition. -/
theorem decided_consistent_propose (s s' : GState n) (ho : HOCollection (Fin n))
    (coin : Fin n → Fin 2)
    (hinv : decided_consistent n s) (hstep : stepPropose n s s' ho coin) :
    decided_consistent n s' := by
  obtain ⟨_, _, _, hlocals⟩ := hstep
  intro p v hdec
  rw [hlocals p] at hdec ⊢
  by_cases hsome : (s.locals p).decided.isSome
  · simp [hsome] at hdec ⊢
    exact hinv p v hdec
  · simp [hsome] at hdec ⊢
    split at hdec <;> simp_all

/-- Phase-1 witness/majority correspondence invariant.

    Content: when the global phase is `1`, a process witnesses `v` iff `v`
    already has a strict global holder majority.
    Purpose: this turns phase-1 local witness data into the global
    majority fact needed in the propose-phase lock proof.
    Proof idea: under reliable communication, `findValMajority` is exactly
    characterized by `findValMajority_reliable_iff`. -/
def report_majority_inv (s : GState n) : Prop :=
  s.phase = 1 →
  ∀ p v, (s.locals p).witnessed = some v ↔ countHolding n v s * 2 > n

/-- `report_majority_inv` holds initially.

    Content: the invariant is conditional on phase `1`, but the initial
    state is phase `0`.
    Purpose: base case for the phase-specific invariant.
    Proof outline: rewrite the initial phase and discharge the impossible
    premise. -/
theorem report_majority_inv_init :
    ∀ s, (benOrSpec n).init s → report_majority_inv n s := by
  intro s hinit hph
  rcases hinit with ⟨_, hs_phase, _⟩
  rw [hs_phase] at hph
  simp at hph

/-- A reliable report step establishes `report_majority_inv`.

    Content: after a reliable report step, each receiver's `witnessed`
    field exactly reflects global majority ownership.
    Purpose: this is the bridge from reliable communication to the later
    lock proof for the propose phase.
    Proof outline: report steps copy `findValMajority` into `witnessed`;
    `findValMajority_reliable_iff` identifies that value with the global
    holder majority, and `countHolding` is unchanged across the report
    step because `val` is unchanged. -/
theorem report_majority_inv_report (s s' : GState n) (ho : HOCollection (Fin n))
    (hrel : reliableHO n ho) (hstep : stepReport n s s' ho) :
    report_majority_inv n s' := by
  obtain ⟨_, hs'_phase, _, hlocals⟩ := hstep
  intro hph p v
  rw [hs'_phase] at hph
  simp at hph
  rw [hlocals p]
  have hcount : countHolding n v s' = countHolding n v s := by
    unfold countHolding
    congr 1
    apply List.filter_congr
    intro q _
    rw [hlocals q]
  constructor
  · intro hw
    rw [hcount]
    exact (findValMajority_reliable_iff (n := n) s ho hrel p v).1 hw
  · intro hmaj
    rw [hcount] at hmaj
    exact (findValMajority_reliable_iff (n := n) s ho hrel p v).2 hmaj

/-- Propose steps preserve `report_majority_inv` trivially.

    Content: after a propose step the phase resets to `0`, so the phase-1
    conditional invariant is vacuous.
    Purpose: this closes the phase-specific invariant across the second
    half of the round.
    Proof outline: rewrite the post-state phase to `0` and eliminate the
    impossible `phase = 1` premise. -/
theorem report_majority_inv_propose (s s' : GState n) (ho : HOCollection (Fin n))
    (coin : Fin n → Fin 2) (hstep : stepPropose n s s' ho coin) :
    report_majority_inv n s' := by
  obtain ⟨_, hs'_phase, _, _⟩ := hstep
  intro hph
  rw [hs'_phase] at hph
  simp at hph

/-- Report steps preserve the lock invariant.

    Content: a report step does not change `val` or `decided`, so any
    existing holder majority for a decided value remains.
    Purpose: report-phase preservation lemma for the main safety invariant.
    Proof outline: transport a post-state decision back to the pre-state,
    invoke the pre-state lock invariant, and show `countHolding` is
    unchanged. -/
theorem lock_inv_report (s s' : GState n) (ho : HOCollection (Fin n))
    (hinv : lock_inv n s) (hstep : stepReport n s s' ho) :
    lock_inv n s' := by
  obtain ⟨_, _, _, hlocals⟩ := hstep
  intro v ⟨p, hp⟩
  -- p decided v in s' — but decided is unchanged from s
  have hp_loc := hlocals p
  rw [hp_loc] at hp ; simp only at hp
  -- So p decided v in s too
  have hp_s : (s.locals p).decided = some v := hp
  have hlock := hinv v ⟨p, hp_s⟩
  -- countHolding is unchanged because val is unchanged
  suffices countHolding n v s' = countHolding n v s by omega
  simp only [countHolding]
  congr 1
  apply List.filter_congr
  intro q _
  rw [hlocals q]

/-- New decisions in one propose step must agree.

    Content: if two previously undecided processes both decide in the same
    propose step, they decide the same bit.
    Purpose: this isolates the local combinatorial argument for the
    propose phase.
    Proof outline: extract witness-majority facts for both decisions using
    `findWitnessMajority_hasWitnessMajority`, observe that one process can
    witness at most one value, and use the same strict-majority pigeonhole
    argument as in `majority_unique`. -/
theorem propose_decisions_agree (s s' : GState n)
    (ho : HOCollection (Fin n)) (coin : Fin n → Fin 2)
    (hstep : stepPropose n s s' ho coin)
    (p q : Fin n) (v w : Fin 2)
    (hp : (s'.locals p).decided = some v)
    (hq : (s'.locals q).decided = some w)
    (hp_new : (s.locals p).decided.isNone)
    (hq_new : (s.locals q).decided.isNone) :
    v = w := by
  obtain ⟨_, _, _, hlocals⟩ := hstep
  have hp_loc := hlocals p ; rw [hp_loc] at hp
  have hq_loc := hlocals q ; rw [hq_loc] at hq
  simp [show (s.locals p).decided.isSome = false from by simp [hp_new]] at hp
  simp [show (s.locals q).decided.isSome = false from by simp [hq_new]] at hq
  have hp_find : findWitnessMajority n s.locals ho p = some v := by
    cases hfp : findWitnessMajority n s.locals ho p with
    | none => simp [hfp] at hp
    | some u =>
      simp [hfp] at hp
      simpa using hp
  have hq_find : findWitnessMajority n s.locals ho q = some w := by
    cases hfq : findWitnessMajority n s.locals ho q with
    | none => simp [hfq] at hq
    | some u =>
      simp [hfq] at hq
      simpa using hq
  have hp_maj : countWitness n s.locals ho p v * 2 > n := by
    have hv := findWitnessMajority_hasWitnessMajority (n := n) hp_find
    simpa [hasWitnessMajority] using hv
  have hq_maj : countWitness n s.locals ho q w * 2 > n := by
    have hw := findWitnessMajority_hasWitnessMajority (n := n) hq_find
    simpa [hasWitnessMajority] using hw
  by_contra hne
  have h_sum := filter_disjoint_length_le
    (fun r => ho p r && ((s.locals r).witnessed == some v))
    (fun r => ho q r && ((s.locals r).witnessed == some w))
    (List.finRange n) (by
      intro r ⟨hpw, hqw⟩
      simp at hpw hqw
      rw [hpw.2] at hqw
      exact hne (Option.some.inj hqw.2))
  have h_len : (List.finRange n).length = n := List.length_finRange
  unfold countWitness at hp_maj hq_maj
  omega

/-- Reliable propose steps preserve the lock invariant.

    Content: under reliable communication, if some process is decided as
    `v` after a propose step, then `v` still has a strict holder majority
    afterwards.
    Purpose: this is the hard preservation lemma for Ben-Or safety.
    Proof outline:
    - first show that the decided value `v` already had a strict holder
      majority before the step: either because the deciding process was
      already decided, or because a new witness-majority for `v` together
      with `report_majority_inv` yields a pre-state holder majority;
    - use `report_majority_inv` again to conclude every process witnessed
      `v` in phase 1;
    - under reliable communication, every undecided process now sees a
      witness-majority for `v` and switches to `v`;
    - already-decided processes are shown, via `decided_consistent` and
      `lock_inv`, to already hold `v`;
    - therefore all post-state holders are `v`, so in particular `v`
      still has a strict majority. -/
theorem lock_inv_propose (s s' : GState n) (ho : HOCollection (Fin n))
    (coin : Fin n → Fin 2)
    (hinv : lock_inv n s) (hstep : stepPropose n s s' ho coin)
    (reliable : reliableHO n ho)
    (hdec : decided_consistent n s)
    (hreport : report_majority_inv n s) :
    lock_inv n s' := by
  obtain ⟨hs_phase, _, _, hlocals⟩ := hstep
  have hreport1 := hreport hs_phase
  intro v ⟨p, hp⟩
  have hp_loc := hlocals p ; rw [hp_loc] at hp
  have hhold : countHolding n v s * 2 > n := by
    by_cases hp_old : (s.locals p).decided.isSome
    · -- p already decided v in s.
      simp [hp_old] at hp
      exact hinv v ⟨p, hp⟩
    · -- p newly decided v from a witness majority.
      simp [hp_old] at hp
      have hp_find : findWitnessMajority n s.locals ho p = some v := by
        cases hfp : findWitnessMajority n s.locals ho p with
        | none => simp [hfp] at hp
        | some u =>
          simp [hfp] at hp
          cases hp
          rfl
      have hwitMaj : countWitnessed n v s * 2 > n := by
        exact (findWitnessMajority_reliable_iff (n := n) s ho reliable p v).1 hp_find
      have h_nonempty : ((List.finRange n).filter fun q =>
          decide ((s.locals q).witnessed = some v)) ≠ [] := by
        intro hnil
        simp [countWitnessed, hnil] at hwitMaj
      obtain ⟨q, hq_mem⟩ := List.exists_mem_of_ne_nil _ h_nonempty
      simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at hq_mem
      exact (hreport1 q v).1 hq_mem
  have h_all_witnessed : ∀ q : Fin n, (s.locals q).witnessed = some v := by
    intro q
    exact (hreport1 q v).2 hhold
  have h_wit_all : countWitnessed n v s = n := by
    unfold countWitnessed
    have hfilter :
        (List.finRange n).filter (fun p => decide ((s.locals p).witnessed = some v)) =
          List.finRange n := by
      apply List.filter_eq_self.2
      intro p hp
      simp [h_all_witnessed p]
    rw [hfilter, List.length_finRange]
  have h_wit_majority : countWitnessed n v s * 2 > n := by
    rw [h_wit_all]
    have hn : 0 < n := by
      have hp_lt : p.val < n := p.isLt
      omega
    omega
  have h_all_hold' : ∀ q : Fin n, (s'.locals q).val = v := by
    intro q
    rw [hlocals q]
    by_cases hq_old : (s.locals q).decided.isSome
    · have hq_dec : ∃ w, (s.locals q).decided = some w := by
        simpa [Option.isSome_iff_exists] using hq_old
      obtain ⟨w, hqw⟩ := hq_dec
      have hqw_hold := hinv w ⟨q, hqw⟩
      have hw_eq : w = v := by
        by_contra hne
        exact majority_unique n (fun r => (s.locals r).val) w v hne hqw_hold hhold
      rw [show (s.locals q).val = w by exact hdec q w hqw, hw_eq]
      simp [hq_old]
    · have hq_find : findWitnessMajority n s.locals ho q = some v := by
        exact (findWitnessMajority_reliable_iff (n := n) s ho reliable q v).2 h_wit_majority
      simp [hq_old, hq_find]
  have h_all_hold : countHolding n v s' = n := by
    unfold countHolding
    have hfilter :
        (List.finRange n).filter (fun p => decide ((s'.locals p).val = v)) =
          List.finRange n := by
      apply List.filter_eq_self.2
      intro p hp
      simp [h_all_hold' p]
    rw [hfilter, List.length_finRange]
  rw [h_all_hold]
  have hn : 0 < n := by
    have hp_lt : p.val < n := p.isLt
    omega
  omega

/-- Combined invariant for the reliable-communication proof.

    Content: package together the lock invariant and the two supporting
    invariants needed in the propose-phase argument.
    Purpose: `init_invariant` is applied once to this combined predicate,
    and agreement is later projected from it.
    Proof idea: this is just a conjunction; the real work is in the
    preservation theorem below. -/
def benor_inv (s : GState n) : Prop :=
  lock_inv n s ∧ decided_consistent n s ∧ report_majority_inv n s

/-- Reliable steps preserve the combined Ben-Or invariant.

    Content: both reliable report and reliable propose steps map
    `benor_inv` states to `benor_inv` states.
    Purpose: this is the single step lemma fed to `init_invariant`.
    Proof outline: split on whether the next step is report or propose and
    compose the already-proved preservation lemmas for each conjunct. -/
theorem benor_inv_next (s s' : GState n) (hinv : benor_inv n s)
    (hnext : (benOrReliableSpec n).next s s') : benor_inv n s' := by
  rcases hinv with ⟨hlock, hdec, hreport⟩
  rcases hnext with ⟨ho, hrel, hstep⟩ | ⟨ho, coin, hrel, hstep⟩
  · exact ⟨lock_inv_report n s s' ho hlock hstep,
      decided_consistent_report n s s' ho hdec hstep,
      report_majority_inv_report n s s' ho hrel hstep⟩
  · exact ⟨lock_inv_propose n s s' ho coin hlock hstep hrel hdec hreport,
      decided_consistent_propose n s s' ho coin hdec hstep,
      report_majority_inv_propose n s s' ho coin hstep⟩

/-! ### Main safety theorem

    **Important caveat**: Ben-Or's safety requires a communication predicate.
    Under arbitrary HO sets, the protocol is NOT safe — a counterexample
    exists where coin flips break the value majority and a competing value
    gets decided in a later round.

    Ben-Or's randomization provides **liveness** (probabilistic termination)
    under unreliable communication, but **safety** (agreement) requires
    reliable enough communication that decided values propagate. The standard
    assumption is reliable broadcast among non-crashed processes with f < n/2.

    The proof below uses `lock_inv` as the inductive invariant, with sorry's
    for the Propose phase that requires reliable communication assumptions.
    The proof structure is correct; the sorry's isolate the communication
    predicate obligations. -/

/-- Agreement theorem for Ben-Or under reliable communication.

    Content: every behavior of `benOrReliableSpec` satisfies `□ agreement`.
    Purpose: this is the exported safety theorem for the model.
    Proof outline: use `init_invariant` to establish `□ benor_inv`, then
    project its `lock_inv` component and apply
    `lock_inv_implies_agreement`. -/
theorem benor_agreement :
    pred_implies (benOrReliableSpec n).safety
      [tlafml| □ ⌜agreement n⌝] := by
  apply pred_implies_trans (q := [tlafml| □ ⌜benor_inv n⌝])
  · apply init_invariant
    · intro s hinit
      exact ⟨lock_inv_init n s hinit,
        decided_consistent_init n s hinit,
        report_majority_inv_init n s hinit⟩
    · intro s s' hnext hinv
      exact benor_inv_next n s s' hinv hnext
  · apply always_monotone
    intro e h
    exact lock_inv_implies_agreement n (e 0) h.1

end BenOr
