import Leslie.Round

/-! ## OneThirdRule Consensus (Heard-Of Model)

    The simplest consensus algorithm in the HO model, from Charron-Bost
    and Schiper (2009).

    ### Algorithm

    There are `n` processes. Each process holds a natural number value.
    The protocol proceeds in synchronous rounds. In each round:

    1. Every process broadcasts its current value to all.
    2. Every process receives a subset of messages (determined by the
       heard-of set HO).
    3. If more than 2n/3 of the received messages carry the **same** value
       `v`, the process **adopts** `v` as its new value and **decides** `v`.
    4. Otherwise, the process keeps its current value (no decision).

    ### Communication predicate

    The protocol assumes the **two-thirds communication predicate**: in
    every round, every process hears from more than 2n/3 of the n
    processes. Messages may be lost, but each process always receives
    "enough" messages. This is formalized as `comm_two_thirds`.

    ### Safety property: Agreement

    **Theorem (`otr_agreement`):** If process p decided v and process q
    decided w, then v = w.

    ### Proof outline

    The proof proceeds in three layers:

    **Layer 1: The lock invariant (`lock_inv`)**

    We define: *if any process has decided value v, then more than 2n/3
    of all n processes currently hold value v.* This is the key inductive
    invariant. It says that a decision "locks in" a super-majority.

    **Layer 2: Lock implies agreement (`lock_inv_implies_agreement`)**

    If two values v ≠ w are both decided, then by the lock invariant,
    >2n/3 processes hold v AND >2n/3 processes hold w. But the sets of
    v-holders and w-holders are disjoint (a process holds exactly one
    value). By the **pigeonhole principle** (`super_majority_unique`),
    two disjoint subsets of n elements cannot both have size >2n/3
    (that would require >4n/3 > n elements). Contradiction.

    **Layer 3: The lock is inductive (`lock_inv_step`)**

    This is the heart of the proof. We show that if the lock holds in
    state s, it still holds in state s' after one round step. The
    argument has three parts:

    **(a) Establishing the lock in s:**
    Process p has `decided = some v` in s'. Either:
    - p **newly decided** v in this round: `findSuperMajority` returned
      `some v` for p's received messages, meaning >2n/3 of p's received
      messages carried v. Each such message came from a distinct sender
      who held v. So >2n/3 processes held v in s. (Uses `countOcc_le_countHolding`.)
    - p **already had** `decided = some v` from state s: the inductive
      hypothesis `hinv` directly gives >2n/3 processes held v in s.

    **(b) The lock is preserved — no competing value can emerge:**
    We show that every process q that held v in s still holds v in s'.
    Process q's new value is determined by `findSuperMajority` on q's
    received messages. We prove it cannot return `some w` for any w ≠ v:

    - Suppose for contradiction that w ≠ v has a super-majority in q's
      received messages, i.e., `countOcc w received_q * 3 > 2n`.
    - Received votes for w come from actual w-holders:
      `countOcc w received_q ≤ countHolding w s` (`countOcc_le_countHolding`).
    - The w-holders and v-holders are disjoint, so their counts sum to ≤ n:
      `countHolding v s + countHolding w s ≤ n` (`filter_disjoint_length_le`).
    - But we also have `countHolding v s * 3 > 2n` (the lock) and
      `countHolding w s * 3 > 2n` (from the chain above). Two disjoint
      subsets of size >2n/3 would need >4n/3 > n elements. Contradiction.
      (This is `no_other_supermajority`.)

    So `findSuperMajority` returns either `none` (q keeps v) or `some v`
    (q adopts v). Either way, q still holds v.

    **(c) Counting:**
    Since every v-holder in s is still a v-holder in s', we have
    `countHolding v s' ≥ countHolding v s > 2n/3` (`filter_length_mono`).

    ### Formal structure

    ```
    otr_agreement
    ├── lock_inv is inductive (round_invariant)
    │   ├── lock_inv_init (initially no decisions → vacuously true)
    │   └── lock_inv_step (lock preserved across rounds)
    │       ├── Step (a): lock_in_s
    │       │   ├── New decision → countOcc_le_countHolding
    │       │   └── Old decision → inductive hypothesis
    │       ├── Step (b): h_preserved (∀ q, q held v → q still holds v)
    │       │   └── no_other_supermajority (pigeonhole kills w ≠ v)
    │       │       ├── countOcc_le_countHolding (votes ≤ holders)
    │       │       └── filter_disjoint_length_le (v,w holders disjoint)
    │       └── Step (c): filter_length_mono (pointwise → count)
    └── lock_inv_implies_agreement
        └── super_majority_unique (pigeonhole: v,w can't both have >2n/3)
            └── filter_disjoint_length_le
    ```
-/

open TLA

namespace OneThirdRule

variable (n : Nat)

/-! ### State and messages -/

/-- Each process holds a value and optionally a decision. Once decided,
    a process keeps its decision forever (the update function only sets
    `decided` from `none` to `some v`, never overwrites). -/
structure LState where
  val : Nat
  decided : Option Nat
  deriving DecidableEq, Repr

/-! ### Counting and super-majority -/

def countOcc (v : Nat) (l : List Nat) : Nat :=
  (l.filter (· == v)).length

/-- A value has a super-majority if it appears more than 2n/3 times.
    We use `countOcc v l * 3 > 2 * n` to avoid natural number division. -/
def hasSuperMajority (v : Nat) (l : List Nat) : Bool :=
  countOcc v l * 3 > 2 * n

/-- Search the received values for one with a super-majority. At most one
    such value can exist (by `super_majority_unique`). -/
def findSuperMajority (l : List Nat) : Option Nat :=
  l.find? (fun v => hasSuperMajority n v l)

/-! ### Algorithm definition -/

/-- The OneThirdRule as a `RoundAlg`. No nondeterminism beyond the HO sets:
    - `send`: broadcast current value
    - `update`: adopt the super-majority value if one exists, else keep current -/
def otr_alg : RoundAlg (Fin n) LState Nat where
  init := fun _p s => s.decided = none
  send := fun _p s => s.val
  update := fun _p s msgs =>
    let received := (List.finRange n).filterMap msgs
    match findSuperMajority n received with
    | some v => { val := v, decided := some v }
    | none => s

/-! ### Communication predicate -/

/-- Every process hears from more than 2n/3 senders in every round. -/
def comm_two_thirds : CommPred (Fin n) :=
  fun _r ho => ∀ p : Fin n,
    ((List.finRange n).filter fun q => ho p q).length * 3 > 2 * n

def otr_spec : RoundSpec (Fin n) LState Nat where
  alg := otr_alg n
  comm := comm_two_thirds n

/-! ### Safety property -/

/-- Number of processes holding value `v` in global state `s`. -/
def countHolding (v : Nat) (s : RoundState (Fin n) LState) : Nat :=
  ((List.finRange n).filter fun p =>
    decide ((s.locals p).val = v)).length

/-- Agreement: all decided processes agree on the same value. -/
def agreement (s : RoundState (Fin n) LState) : Prop :=
  ∀ p q v w,
    (s.locals p).decided = some v →
    (s.locals q).decided = some w →
    v = w

/-! ### Pigeonhole: two super-majorities can't coexist

    If >2n/3 processes hold v and >2n/3 hold w with v ≠ w, then
    we'd need >4n/3 processes, but there are only n. -/

theorem super_majority_unique
    (f : Fin n → Nat) (v w : Nat) (hne : v ≠ w)
    (hv : ((List.finRange n).filter fun p => decide (f p = v)).length * 3 > 2 * n)
    (hw : ((List.finRange n).filter fun p => decide (f p = w)).length * 3 > 2 * n) :
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

/-! ### The lock invariant

    "If any process has decided v, then more than 2n/3 processes hold v."

    This is the key inductive invariant. Together with `super_majority_unique`,
    it implies agreement: two decided values would each need >2n/3 holders,
    but disjoint sets of that size can't fit in n processes. -/

def lock_inv (s : RoundState (Fin n) LState) : Prop :=
  ∀ v, (∃ p : Fin n, (s.locals p).decided = some v) →
    countHolding n v s * 3 > 2 * n

/-- Layer 2: lock_inv implies agreement. -/
theorem lock_inv_implies_agreement (s : RoundState (Fin n) LState)
    (h : lock_inv n s) : agreement n s := by
  intro p q v w hv hw
  by_contra hne
  exact super_majority_unique n (fun r => (s.locals r).val) v w hne
    (h v ⟨p, hv⟩) (h w ⟨q, hw⟩)

/-! ### Helper lemmas -/

/-- `findSuperMajority` returning `some v` implies `v` has a super-majority. -/
theorem findSuperMajority_hasSuperMajority {l : List Nat} {v : Nat}
    (h : findSuperMajority n l = some v) :
    hasSuperMajority n v l = true := by
  simp only [findSuperMajority] at h
  have := List.find?_some h
  exact this

/-- Votes for `w` in received messages ≤ total `w`-holders.
    Each received vote for `w` came from a sender who holds `w`,
    and senders are distinct. -/
theorem countOcc_le_countHolding
    (s : RoundState (Fin n) LState) (ho : HOCollection (Fin n))
    (q : Fin n) (w : Nat) :
    countOcc w ((List.finRange n).filterMap
      (fun r => if ho q r then some (s.locals r).val else none)) ≤
    countHolding n w s := by
  simp only [countOcc, countHolding]
  apply filterMap_filter_count_le
  intro r hr
  simp only [decide_eq_true_eq]
  by_cases hho : ho q r = true
  · simp [hho] at hr ; exact hr
  · have hf : ho q r = false := by revert hho ; cases ho q r <;> simp
    simp [hf] at hr

/-- No competing super-majority: if >2n/3 hold v, then no w ≠ v can
    have a super-majority in any process's received messages.

    Proof: w-votes ≤ w-holders (by `countOcc_le_countHolding`), and
    w-holders + v-holders ≤ n (disjoint). If v-holders > 2n/3, then
    w-holders < n/3, so w-votes < n/3 < 2n/3. -/
theorem no_other_supermajority
    (s : RoundState (Fin n) LState) (ho : HOCollection (Fin n))
    (q : Fin n) (v w : Nat) (hne : w ≠ v)
    (hlock : countHolding n v s * 3 > 2 * n) :
    ¬ (hasSuperMajority n w
        ((List.finRange n).filterMap
          (fun r => if ho q r then some (s.locals r).val else none)) = true) := by
  intro hsm
  simp only [hasSuperMajority] at hsm
  have hle_w := countOcc_le_countHolding n s ho q w
  have h_disj := filter_disjoint_length_le
    (fun r => decide ((s.locals r).val = v))
    (fun r => decide ((s.locals r).val = w))
    (List.finRange n)
    (by intro x ⟨h1, h2⟩
        simp [decide_eq_true_eq] at h1 h2
        rw [h1] at h2 ; exact hne h2.symm)
  have h_len : (List.finRange n).length = n := List.length_finRange
  simp only [countHolding] at hlock
  simp only [decide_eq_true_eq] at hsm
  have : countHolding n w s * 3 > 2 * n :=
    Nat.lt_of_lt_of_le hsm (Nat.mul_le_mul_right 3 hle_w)
  simp only [countHolding] at this
  omega

/-! ### Layer 3: The lock is inductive -/

/-- Initially no process has decided, so the lock holds vacuously. -/
theorem lock_inv_init :
    ∀ s, (otr_spec n).toSpec.init s → lock_inv n s := by
  intro s ⟨_, hinit⟩ v ⟨p, hp⟩
  have := hinit p
  simp only at this
  rw [this] at hp ; simp at hp

/-- **The lock is preserved across rounds.**

    Given: `lock_inv` holds in `s`, some process `p` has decided `v` in `s'`.
    Goal: `countHolding v s' * 3 > 2 * n`.

    Step (a) — Establish the lock in `s`:
      If p newly decided, trace votes back to holders via
      `countOcc_le_countHolding`. If p already decided, use the IH.

    Step (b) — Every v-holder in `s` is still a v-holder in `s'`:
      For each process q that held v, `findSuperMajority` on q's received
      messages returns either `none` (keeps v) or `some w`. If w ≠ v,
      `no_other_supermajority` gives a contradiction. So w = v.

    Step (c) — Count doesn't decrease:
      By `filter_length_mono`, pointwise preservation of the v-predicate
      implies `countHolding v s' ≥ countHolding v s > 2n/3`. -/
theorem lock_inv_step :
    ∀ s ho, lock_inv n s → (otr_spec n).comm s.round ho →
    ∀ s', round_step (otr_alg n) ho s s' → lock_inv n s' := by
  intro s ho hinv _hcomm s' ⟨_, hlocals⟩
  intro v ⟨p, hp⟩
  -- Simplify the delivered messages to: if ho q r then some (s.locals r).val else none
  have delivered_eq : ∀ q r, delivered (otr_alg n) s ho q r =
      (if ho q r then some (s.locals r).val else none) := by
    intro q r ; simp only [delivered, otr_alg]
  -- Expand hlocals into the fully simplified form
  have hlocals_expanded : ∀ q, s'.locals q =
      match findSuperMajority n ((List.finRange n).filterMap
        (fun r => if ho q r then some (s.locals r).val else none)) with
      | some w => { val := w, decided := some w }
      | none => s.locals q := by
    intro q
    have := hlocals q
    simp only [otr_alg] at this
    rw [this] ; congr 2
  -- ──── Step (a): Establish the lock in s ────
  have lock_in_s : countHolding n v s * 3 > 2 * n := by
    have hp' := hlocals_expanded p
    rw [hp'] at hp
    split at hp
    · -- p newly decided v' in this round
      case h_1 v' hfind =>
      simp only at hp
      have hv' : v' = v := Option.some.inj hp
      rw [← hv']
      -- v' had super-majority in p's received messages
      have hsm := findSuperMajority_hasSuperMajority n hfind
      simp only [hasSuperMajority, decide_eq_true_eq] at hsm
      -- Lift from received votes to actual holders
      exact Nat.lt_of_lt_of_le hsm (Nat.mul_le_mul_right 3
        (countOcc_le_countHolding n s ho p v'))
    · -- p already had decided = some v from state s
      case h_2 hfind =>
      exact hinv v ⟨p, hp⟩
  -- ──── Step (b): Every v-holder in s still holds v in s' ────
  have h_preserved : ∀ q : Fin n,
      (s.locals q).val = v → (s'.locals q).val = v := by
    intro q hq_val
    rw [hlocals_expanded q]
    split
    · -- findSuperMajority returned some w for q — show w = v
      case h_1 w hfind_q =>
      simp only
      by_contra hne
      -- w ≠ v but w has super-majority — contradicts lock via pigeonhole
      exact no_other_supermajority n s ho q v w hne lock_in_s
        (findSuperMajority_hasSuperMajority n hfind_q)
    · -- findSuperMajority returned none — q keeps its value v
      case h_2 hfind_q =>
      exact hq_val
  -- ──── Step (c): Count doesn't decrease ────
  have h_mono := filter_length_mono (List.finRange n)
    (fun q => decide ((s.locals q).val = v))
    (fun q => decide ((s'.locals q).val = v))
    (by intro q hq
        simp [decide_eq_true_eq] at hq ⊢
        exact h_preserved q hq)
  simp only [countHolding] at lock_in_s ⊢
  omega

/-! ### Main safety theorem -/

/-- **OneThirdRule satisfies agreement.**

    Proof: `lock_inv` is an inductive invariant (`round_invariant` with
    `lock_inv_init` and `lock_inv_step`), giving `□ lock_inv`. Then
    `lock_inv_implies_agreement` lifts it to `□ agreement` via
    `always_monotone`. -/
theorem otr_agreement :
    pred_implies (otr_spec n).toSpec.safety
      [tlafml| □ ⌜agreement n⌝] := by
  apply pred_implies_trans (q := [tlafml| □ ⌜lock_inv n⌝])
  · apply round_invariant
    · exact lock_inv_init n
    · exact lock_inv_step n
  · apply always_monotone
    intro e h
    exact lock_inv_implies_agreement n (e 0) h

/-! ### Validity: decided values come from the initial pool

    **Theorem (`validity`):** At any time t, every process's current value
    was the initial value of some process at time 0. In particular, any
    decided value was an initial value.

    This is NOT a single-state invariant — it relates the current state to
    time 0. We prove it by induction on the execution:

    **Base (t=0):** Every process's value is its own initial value.

    **Step (t→t+1):** The update function either keeps the old value
    (`findSuperMajority = none`) or adopts a value from the received
    messages (`findSuperMajority = some v`). In the latter case, `v`
    appears in the received list, which means some sender held `v` in
    state `e(t)`. By the IH, that sender's value at `e(t)` was some
    process's value at `e(0)`.

    ```
    validity
    ├── values_come_from_senders (one round step)
    │   ├── findSuperMajority_mem (found value is in the list)
    │   └── List.mem_filterMap (list element traces to a sender)
    └── Nat.rec (induction on time t)
    ```
-/

/-- If `findSuperMajority` returns `some v`, then `v` appears in the list. -/
theorem findSuperMajority_mem {l : List Nat} {v : Nat}
    (h : findSuperMajority n l = some v) : v ∈ l := by
  simp only [findSuperMajority] at h
  exact List.mem_of_find?_eq_some h

/-- In a single round step, every process's new value was some sender's
    old value. This is the key "values don't appear from nowhere" lemma. -/
theorem values_come_from_senders
    (s : RoundState (Fin n) LState) (ho : HOCollection (Fin n))
    (s' : RoundState (Fin n) LState)
    (hstep : round_step (otr_alg n) ho s s') :
    ∀ p : Fin n, ∃ q : Fin n, (s'.locals p).val = (s.locals q).val := by
  intro p
  obtain ⟨_, hlocals⟩ := hstep
  have hp := hlocals p
  simp only [otr_alg] at hp
  -- hp : s'.locals p = match findSuperMajority ... with | some v => ... | none => ...
  -- Simplify delivered to: fun r => if ho p r then some (s.locals r).val else none
  -- Expand to simplified form
  have hp_expanded : s'.locals p =
      match findSuperMajority n ((List.finRange n).filterMap
        (fun r => if ho p r then some (s.locals r).val else none)) with
      | some v => { val := v, decided := some v }
      | none => s.locals p := by
    rw [hp] ; congr 2
  rw [hp_expanded]
  split
  · -- findSuperMajority = some v: v came from a sender
    case h_1 received v hfind =>
    simp only
    have hv_mem := findSuperMajority_mem n hfind
    -- v ∈ (finRange n).filterMap (fun r => if ho p r then some (s.locals r).val else none)
    rw [List.mem_filterMap] at hv_mem
    obtain ⟨r, _, hr⟩ := hv_mem
    by_cases hho : ho p r = true
    · simp [hho] at hr ; exact ⟨r, hr.symm⟩
    · have hf : ho p r = false := by revert hho ; cases ho p r <;> simp
      simp [hf] at hr
  · -- findSuperMajority = none: p keeps old value
    case h_2 received hfind =>
    exact ⟨p, rfl⟩

/-- **Validity: all values trace back to time 0.**

    At every time `t` in an execution satisfying the OneThirdRule spec,
    every process's current value was the initial value of some process. -/
theorem validity
    (e : exec (RoundState (Fin n) LState))
    (hsafety : e |=tla= (otr_spec n).toSpec.safety) :
    ∀ t (p : Fin n), ∃ q : Fin n,
      ((e t).locals p).val = ((e 0).locals q).val := by
  obtain ⟨_, hnext⟩ := hsafety
  intro t
  induction t with
  | zero => intro p ; exact ⟨p, rfl⟩
  | succ t ih =>
    intro p
    -- e(t) →[next] e(t+1)
    have hstep : (otr_spec n).toSpec.next (e t) (e (t + 1)) := by
      have := hnext t
      simpa [action_pred, exec.drop] using this
    -- e(t) →[next] e(t+1) means ∃ ho, comm ∧ round_step
    obtain ⟨ho, _, hround⟩ := hstep
    -- p's value at t+1 was some sender r's value at t
    obtain ⟨r, hr⟩ := values_come_from_senders n (e t) ho (e (t + 1)) hround p
    -- By IH, r's value at t was some q's value at 0
    obtain ⟨q, hq⟩ := ih r
    exact ⟨q, hr.trans hq⟩

/-- **Corollary: decided values are initial values.**

    If process `p` decided value `v` at time `t`, then `v` was the initial
    value of some process. The proof combines `validity` (values trace to
    time 0) with the observation that `decided = some v` implies `val = v`
    (from the structure of the update function). -/
theorem decided_from_initial
    (e : exec (RoundState (Fin n) LState))
    (hsafety : e |=tla= (otr_spec n).toSpec.safety) :
    ∀ t (p : Fin n) v,
      ((e t).locals p).decided = some v →
      ∃ q : Fin n, v = ((e 0).locals q).val := by
  -- First prove: decided = some v → val = v (at all times)
  have h_dec_val : ∀ t (p : Fin n),
      ∀ v, ((e t).locals p).decided = some v → ((e t).locals p).val = v := by
    obtain ⟨hinit, hnext⟩ := hsafety
    intro t
    induction t with
    | zero =>
      intro p v hdec
      have := hinit
      simp [otr_spec, RoundSpec.toSpec, state_pred, otr_alg] at this
      rw [this.2 p] at hdec ; simp at hdec
    | succ t ih =>
      intro p v hdec
      have hstep : (otr_spec n).toSpec.next (e t) (e (t + 1)) := by
        have := hnext t
        simpa [action_pred, exec.drop] using this
      obtain ⟨ho, _, _, hlocals⟩ := hstep
      have hp := hlocals p
      simp only at hp
      have hp_expanded : (e (t + 1)).locals p =
          match findSuperMajority n ((List.finRange n).filterMap
            (fun r => if ho p r then some ((e t).locals r).val else none)) with
          | some v => { val := v, decided := some v }
          | none => (e t).locals p := by
        rw [hp] ; congr 2
      -- Derive decided = some v → val = v from the expanded form
      have key : ((e (t + 1)).locals p).decided = some v →
          ((e (t + 1)).locals p).val = v := by
        rw [hp_expanded]
        split
        · case h_1 w _ => intro h ; simp only at h ; exact Option.some.inj h
        · case h_2 _ => exact ih p v
      exact key hdec
  -- Combine: decided v → val = v, then use validity
  intro t p v hdec
  have hval := h_dec_val t p v hdec
  obtain ⟨q, hq⟩ := validity n e hsafety t p
  exact ⟨q, hval ▸ hq⟩

end OneThirdRule
