import Leslie.Cutoff

/-! ## OneThirdRule Lock Invariant via Cutoff

    ### Overview

    In `OneThirdRule.lean`, we proved the lock invariant (and hence
    agreement) for the OneThirdRule consensus algorithm by a manual
    inductive proof over the concrete round-based state. Here, we
    show the same result at the **configuration level** — abstracting
    away process identities and reasoning purely about counts.

    ### The lock invariant

    The lock invariant says: *if any process has decided value v, then
    more than 2n/3 of all n processes currently hold value v.*

    Once this lock is established, it persists — no other value can
    ever reach a super-majority — and agreement follows by pigeonhole.

    ### Extended configurations

    To express the lock invariant at the configuration level, we need
    to track not just which VALUE each process holds, but also whether
    it has DECIDED. We encode the local state as `Fin 4`:

    | Fin 4 | val | decided | Meaning                     |
    |-------|-----|---------|-----------------------------|
    | 0     | 0   | no      | Holding 0, undecided        |
    | 1     | 0   | yes     | Holding 0, decided on 0     |
    | 2     | 1   | no      | Holding 1, undecided        |
    | 3     | 1   | yes     | Holding 1, decided on 1     |

    ### Value threshold view

    The OneThirdRule update depends on **aggregated value counts**:
    "does value 0 have >2n/3 holders total (decided + undecided)?"
    This is a 2-bit **value threshold view**, independent of n.

    ### Configuration successor

    Under reliable communication, all processes see the same value
    threshold view. The successor is deterministic:
    - If value v has super-majority: everyone adopts v and decides.
    - If no value has super-majority: everyone keeps their state.

    We define `extSuccCounts` directly from the value threshold view,
    bypassing the `SymThreshAlg` framework (which uses per-state
    thresholds — a coarser abstraction than we need).

    ### The cutoff connection

    The inductive step of the lock invariant depends only on the
    2-bit value threshold view:
    - **(T, F)**: value 0 has super-majority → successor has all n
      in `decidedState 0` → lock holds.
    - **(F, T)**: symmetric for value 1.
    - **(F, F)**: no super-majority → no new decisions → if the lock
      held, it persists (values don't change). If no one was decided,
      no one becomes decided → lock vacuously holds.
    - **(T, T)**: unrealizable (pigeonhole).

    Since there are only 3 realizable threshold views, and the
    argument works the same way for each regardless of n, the proof
    is uniform in n. A model checker could verify this by checking
    the 3 cases; we prove it directly.
-/

open TLA

namespace OneThirdRuleCutoff

/-! ### Extended state encoding -/

/-- The value (0 or 1) held by each extended state. -/
def extVal : Fin 4 → Fin 2
  | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 1

/-- Whether the extended state represents a decided process. -/
def extDecided : Fin 4 → Bool
  | 0 => false | 1 => true | 2 => false | 3 => true

/-- The decided-and-holding-v extended state for value v. -/
def decidedState (v : Fin 2) : Fin 4 :=
  if v = 0 then 1 else 3

/-- The undecided-and-holding-v extended state for value v. -/
def undecidedState (v : Fin 2) : Fin 4 :=
  if v = 0 then 0 else 2

/-! ### Value counts and threshold view -/

/-- Total number of processes holding value v (decided + undecided). -/
def valCount (n : Nat) (c : Config 4 n) (v : Fin 2) : Nat :=
  c.counts (undecidedState v) + c.counts (decidedState v)

/-- The 2-bit value threshold view: which values have super-majority. -/
def valThreshView (n : Nat) (c : Config 4 n) : ThreshView 2 :=
  fun v => decide (valCount n c v * 3 > 2 * n)

/-! ### Configuration successor under reliable communication

    The successor counts are computed directly from the value threshold
    view. This is the correct abstraction for the OneThirdRule:
    the update depends on aggregated value counts, not per-state counts.

    Under reliable communication, all processes see the same threshold
    view. The update maps each extended state to its successor:
    - If value 0 has super-majority: all → decidedState 0 (state 1)
    - If value 1 has super-majority: all → decidedState 1 (state 3)
    - If neither: all keep their current state -/

/-- Extended update: new state given current state and value threshold view. -/
def extUpdate (s : Fin 4) (vtv : ThreshView 2) : Fin 4 :=
  if vtv 0 then decidedState 0
  else if vtv 1 then decidedState 1
  else s

/-- Compute successor counts from value threshold view.
    For each target state t, count how many source states map to t. -/
def extSuccCounts (n : Nat) (c : Config 4 n) : Fin 4 → Nat :=
  let vtv := valThreshView n c
  fun t => ((List.finRange 4).map fun s =>
    if extUpdate s vtv = t then c.counts s else 0).sum

/-- Successor counts sum to n. -/
theorem extSuccCounts_sum (n : Nat) (c : Config 4 n) :
    ((List.finRange 4).map (extSuccCounts n c)).sum = n := by
  simp only [extSuccCounts]
  have := weighted_partition_sum 4 (List.finRange 4) c.counts
    (fun s => extUpdate s (valThreshView n c))
  rw [c.sum_eq] at this ; exact this

/-- The successor configuration. -/
def extSucc (n : Nat) (c : Config 4 n) : Config 4 n :=
  ⟨extSuccCounts n c, extSuccCounts_sum n c⟩

/-! ### The lock invariant -/

/-- "If any process decided v, then >2n/3 hold value v." -/
def extLockInv (n : Nat) (c : Config 4 n) : Prop :=
  ∀ v : Fin 2,
    c.counts (decidedState v) > 0 →
    valCount n c v * 3 > 2 * n

/-! ### Initial condition -/

def isInitial (_n : Nat) (c : Config 4 _n) : Prop :=
  c.counts (decidedState 0) = 0 ∧ c.counts (decidedState 1) = 0

/-- The lock holds vacuously on initial configs (no decisions). -/
theorem lock_inv_init (n : Nat) (c : Config 4 n) (h : isInitial n c) :
    extLockInv n c := by
  intro v hv
  simp only [isInitial, decidedState] at h hv
  have : v = 0 ∨ v = 1 := by omega
  rcases this with rfl | rfl <;> simp_all

/-! ### The inductive step: lock is preserved by each round

    **Three cases** based on the value threshold view:

    **(T, F) — value 0 has super-majority:**
    `extUpdate` maps every state to `decidedState 0` (= state 1).
    Successor counts: state 1 gets all n, others get 0.
    Lock: decided-0 count = n > 0, valCount 0 = n, n * 3 > 2n (for n ≥ 1).
    For value 1: decided-1 count = 0, so vacuously true.

    **(F, T) — value 1 has super-majority:** Symmetric.

    **(F, F) — no super-majority:**
    `extUpdate` is the identity on all states. Successor = current config.
    If lock held before, it holds after (nothing changed).
    If no one was decided before, no one is decided after → vacuous.

    **(T, T) is unrealizable** by pigeonhole: counts for both values
    sum to n, but each would need >2n/3, requiring >4n/3 > n. -/

/-- Helper: if value v has super-majority, then extUpdate sends
    everything to decidedState v, so the successor count for
    decidedState v is n and all other counts are 0. -/
theorem extSucc_supermaj (n : Nat) (c : Config 4 n) (v : Fin 2)
    (hv : valThreshView n c v = true) :
    (extSucc n c).counts (decidedState v) = n := by
  simp only [extSucc, extSuccCounts]
  -- When vtv v = true, extUpdate maps every state to decidedState v
  -- (assuming the other value is NOT also above threshold — which we need)
  -- For v = 0: vtv 0 = true → extUpdate s vtv = decidedState 0 for all s
  -- For v = 1: vtv 0 = false (by pigeonhole) → vtv 1 = true → extUpdate s vtv = decidedState 1
  -- In both cases: every "if extUpdate s vtv = decidedState v" is true
  rw [show ((List.finRange 4).map fun s =>
      if extUpdate s (valThreshView n c) = decidedState v then c.counts s else 0) =
    (List.finRange 4).map c.counts from
    List.map_congr_left (fun s _ => by
      simp only [extUpdate, decidedState, valThreshView] at hv ⊢
      have : v = 0 ∨ v = 1 := by omega
      rcases this with rfl | rfl
      · simp [hv]
      · -- v = 1: need vtv 0 = false (pigeonhole)
        simp only [decide_eq_true_eq] at hv
        -- If vtv 0 were also true, both values > 2n/3 → contradiction
        by_cases h0 : decide (valCount n c 0 * 3 > 2 * n) = true
        · simp only [decide_eq_true_eq] at h0
          -- Both above threshold → sum > 4n/3 > n, contradiction with sum = n
          have h_sum := c.sum_eq ; simp [List.finRange] at h_sum
          simp [valCount, undecidedState, decidedState] at hv h0
          omega
        · simp [h0, hv])]
  exact c.sum_eq

/-- When no value has super-majority, the successor equals the current config
    (extUpdate is the identity). -/
theorem extSucc_no_supermaj (n : Nat) (c : Config 4 n)
    (h0 : valThreshView n c 0 = false) (h1 : valThreshView n c 1 = false) :
    ∀ i, (extSucc n c).counts i = c.counts i := by
  intro i
  simp only [extSucc, extSuccCounts, extUpdate, h0, h1]
  simp [List.finRange]
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> simp

/-- **The lock invariant is preserved by one round.**

    Proof by case analysis on the 2-bit value threshold view.
    Only 3 cases are realizable (TT is impossible by pigeonhole):
    - (T,F) or (F,T): one value dominates → all processes adopt it
    - (F,F): no change → lock trivially preserved -/
theorem lock_inv_step (n : Nat) (c : Config 4 n)
    (hinv : extLockInv n c) :
    extLockInv n (extSucc n c) := by
  intro v hv_dec
  -- Case 1: value v itself has super-majority
  by_cases hv : valThreshView n c v = true
  · -- Successor has decidedState v count = n (all processes adopt v)
    have h_succ := extSucc_supermaj n c v hv
    rw [h_succ] at hv_dec -- n > 0
    simp only [valCount, h_succ] ; omega
  · -- Case 2: value v does NOT have super-majority
    -- Sub-case: no value at all has super-majority
    -- Then successor counts = current counts (identity update)
    have hv' : v = 0 ∨ v = 1 := by omega
    -- Determine if the OTHER value w has super-majority
    have h_other : (valThreshView n c 0 = false ∧ valThreshView n c 1 = false) ∨
        (∃ w, w ≠ v ∧ valThreshView n c w = true) := by
      rcases hv' with rfl | rfl
      · by_cases h1 : valThreshView n c 1 = true
        · right ; exact ⟨1, by omega, h1⟩
        · left ; revert hv h1 ; cases valThreshView n c 0 <;> cases valThreshView n c 1 <;> simp
      · by_cases h0 : valThreshView n c 0 = true
        · right ; exact ⟨0, by omega, h0⟩
        · left ; revert hv h0 ; cases valThreshView n c 0 <;> cases valThreshView n c 1 <;> simp
    rcases h_other with ⟨h0, h1⟩ | ⟨w, hwne, hwv⟩
    · -- (F,F): identity update, lock preserved from current config
      have h_id := extSucc_no_supermaj n c h0 h1
      -- hv_dec : decided v count > 0 in SUCCESSOR = decided v count in CURRENT
      rw [h_id] at hv_dec
      -- Now hv_dec is about the current config
      have h_lock := hinv v hv_dec
      -- Transfer to successor using h_id
      simp only [valCount] at h_lock ⊢
      rw [h_id, h_id]
      exact h_lock
    · -- Other value w has super-majority: ALL n processes go to decidedState w
      -- But v ≠ w, so decidedState v gets 0 in the successor → hv_dec contradicts
      have h_all_w := extSucc_supermaj n c w hwv
      -- decidedState v count in successor: use the sum constraint
      -- Total = n, decidedState w = n → other 3 states sum to 0 → each is 0
      have h_sum := (extSucc n c).sum_eq
      simp [List.finRange] at h_sum
      -- decidedState v ≠ decidedState w
      simp only [decidedState] at h_all_w hv_dec ⊢
      have : w = 0 ∨ w = 1 := by omega
      rcases hv' with rfl | rfl <;> rcases ‹w = 0 ∨ w = 1› with rfl | rfl <;> simp_all <;> omega

/-! ### Agreement from the lock invariant -/

/-- If the lock holds and two values are both decided, they must be equal.
    Proof: each needs >2n/3 holders, but they're disjoint, can't both fit. -/
theorem agreement_via_lock (n : Nat) (c : Config 4 n)
    (h : extLockInv n c) (v w : Fin 2)
    (hv : c.counts (decidedState v) > 0)
    (hw : c.counts (decidedState w) > 0) :
    v = w := by
  by_contra hne
  have h_lock_v := h v hv
  have h_lock_w := h w hw
  have h_sum := c.sum_eq
  simp [List.finRange] at h_sum
  have h_disj : valCount n c v + valCount n c w ≤ n := by
    simp only [valCount, undecidedState, decidedState]
    have : v = 0 ∨ v = 1 := by omega
    have : w = 0 ∨ w = 1 := by omega
    rcases ‹v = 0 ∨ v = 1› with rfl | rfl <;> rcases ‹w = 0 ∨ w = 1› with rfl | rfl <;>
      simp_all <;> omega
  have : (valCount n c v + valCount n c w) * 3 =
      valCount n c v * 3 + valCount n c w * 3 := Nat.add_mul _ _ 3
  have : n * 3 ≤ 2 * n + 2 * n := by omega
  have : n * 3 < (valCount n c v + valCount n c w) * 3 := by
    calc n * 3 ≤ 2 * n + 2 * n := by omega
    _ < valCount n c v * 3 + valCount n c w * 3 := Nat.add_lt_add h_lock_v h_lock_w
    _ = (valCount n c v + valCount n c w) * 3 := (Nat.add_mul _ _ 3).symm
  exact absurd (Nat.lt_of_mul_lt_mul_right ‹n * 3 < _›) (Nat.not_lt.mpr h_disj)

/-! ## Unreliable communication

    ### The gap in the reliable-communication proof

    The `extSucc` transition and `lock_inv_step` above assume **reliable
    communication**: all processes see the same value threshold view, so
    the successor is deterministic. Under **unreliable communication**
    (the HO model with `comm_two_thirds`), different processes may receive
    different message subsets, leading to different per-process threshold
    views and a nondeterministic successor.

    ### Why the lock invariant still holds

    The lock preservation argument depends on one key fact:

    **No process can see a competing value above threshold.**

    If value v has >2n/3 holders, then value w ≠ v has <n/3 holders.
    Under ANY HO set, a process receives at most as many votes for w as
    there are w-holders (communication closure: received messages reflect
    the current state). So votes for w ≤ holders of w < n/3 < 2n/3.
    Therefore w cannot reach a super-majority in any process's received
    messages, regardless of the HO set.

    This means:
    - Every v-holder either keeps v (saw no super-majority) or adopts v
      (saw v above threshold). Either way, still holds v.
    - No process adopts w ≠ v.
    - The v-count can only increase (some non-v holders may adopt v).
    - New decisions are only for v (no new w-decisions created).

    The nondeterminism from HO sets affects WHICH processes adopt v
    vs. keep their state, but NOT whether the lock is preserved.

    ### Formal model

    We define a **valid unreliable successor** as any configuration c'
    reachable from c by allowing each process to independently either:
    (a) adopt v and decide (if it saw v above threshold in its HO set), or
    (b) keep its current state (if it saw no super-majority).

    The constraint from `comm_two_thirds`: no process sees w ≠ v above
    threshold (by the counting bound above). So (a) and (b) are the
    only possibilities.

    At the configuration level, a valid unreliable successor satisfies:
    - Value v's holder count doesn't decrease (v-holders keep v)
    - No new holders of w ≠ v appear (can't adopt w)
    - Decided-v count doesn't decrease (can't un-decide)
    - No new decided-w for w ≠ v (can't decide a non-super-majority value)
    - Total process count is preserved -/

/-- A configuration c' is a **valid unreliable successor** of c under
    the OneThirdRule with `comm_two_thirds` if three conditions hold.

    **Intuition**: Under unreliable communication, each process's HO set
    determines what threshold view it sees. Communication closure ensures
    received votes for value w ≤ total w-holders. Under `comm_two_thirds`,
    this means:
    - No process can see a value above threshold unless that value truly
      has a super-majority globally (votes ≤ holders, so can't "hallucinate"
      a super-majority that doesn't exist).
    - If a value v has a global super-majority, different processes may or
      may not see it above threshold (depending on their HO set), but none
      can see a COMPETING value above threshold.

    This yields three abstract constraints on valid successors:

    1. **Super-majorities are preserved**: if value v had >2n/3 holders
       in c, it still has >2n/3 in c'. (Because v-holders keep v — no
       competing value can lure them away — and some non-v holders may
       adopt v, only increasing the count.)

    2. **Decisions are monotone**: decided-v count doesn't decrease.
       (Processes can't un-decide. Under case (b) of the update — no
       super-majority seen — the process keeps its entire state.)

    3. **No phantom decisions**: if value v has no global super-majority,
       no new decisions for v are created. (No process can see v above
       threshold because votes for v ≤ holders of v ≤ 2n/3, which is
       NOT > 2n/3. Communication closure is the key: only current
       holders contribute votes, no stale messages inflate the count.) -/
def IsValidUnreliableSucc (n : Nat) (c c' : Config 4 n) : Prop :=
  -- [1] Super-majorities are preserved
  (∀ v : Fin 2, valCount n c v * 3 > 2 * n → valCount n c' v * 3 > 2 * n) ∧
  -- [2] Decisions are monotone (can't un-decide)
  (∀ v : Fin 2, c.counts (decidedState v) ≤ c'.counts (decidedState v)) ∧
  -- [3] No phantom decisions (no new decisions without global super-majority)
  (∀ v : Fin 2, ¬(valCount n c v * 3 > 2 * n) →
    c'.counts (decidedState v) = c.counts (decidedState v))

/-- Under the lock invariant, if value v has no super-majority, then no
    process has decided v. (Contrapositive of the lock: decided-v > 0 →
    super-majority, so no super-majority → decided-v = 0.) -/
theorem lock_no_supermaj_no_decided (n : Nat) (c : Config 4 n)
    (hinv : extLockInv n c) (v : Fin 2)
    (hv_f : valThreshView n c v = false) :
    c.counts (decidedState v) = 0 := by
  by_contra h
  have := hinv v (by omega)
  simp [valThreshView] at hv_f ; omega

/-- The reliable successor satisfies the unreliable constraints
    **when the lock invariant holds**.

    The lock invariant is needed because under reliable communication,
    if value w has a super-majority, ALL processes adopt w — including
    processes that had decided v ≠ w. This would violate constraint [2]
    (decisions monotone). But the lock invariant prevents this: if
    decided-v > 0, then v has a super-majority, and by pigeonhole no
    other value w can also have a super-majority. So the "w overwrites
    v's decisions" case cannot arise under the lock. -/
theorem extSucc_is_valid_unreliable (n : Nat) (c : Config 4 n)
    (hinv : extLockInv n c) :
    IsValidUnreliableSucc n c (extSucc n c) := by
  -- Helper: determine the value threshold view
  -- Either (T,F), (F,T), or (F,F). (T,T) is impossible by noTwoSuperMaj.
  have h_vtv : ∀ v : Fin 2, valThreshView n c v = true ∨ valThreshView n c v = false := by
    intro v ; cases valThreshView n c v <;> simp
  refine ⟨?_, ?_, ?_⟩
  · -- [1] Super-majorities preserved
    -- We already proved this as otr_succ_preserves_supermaj (for Config 2 n).
    -- Here for Config 4 n, the argument is the same: extSucc_supermaj gives
    -- decidedState v = n, so valCount v ≥ n, and n * 3 > 2n for n ≥ 1.
    intro v hv
    -- lock_inv_step already proved the lock is preserved by extSucc.
    -- The lock preservation implies super-majorities are preserved.
    -- Use lock_inv_step directly:
    -- If v has super-majority and decided-v > 0: lock gives it in successor.
    -- If v has super-majority and decided-v = 0: after reliable round,
    --   decided-v = n in successor (extSucc_supermaj), so lock holds.
    -- Either way, valCount v * 3 > 2n in successor.
    -- Simplest: use lock_inv_step (the reliable case) to show lock holds,
    -- then extract the super-majority from it.
    -- But lock_inv_step proves extLockInv, not directly valCount preservation.
    -- Let's use the direct argument: extSucc_supermaj gives decidedState v = n.
    have hv_tv : valThreshView n c v = true := by
      simp [valThreshView, decide_eq_true_eq] ; exact hv
    have h_n := extSucc_supermaj n c v hv_tv
    -- Goal becomes: (undecided-v count in succ + n) * 3 > 2n.
    -- This follows from n ≥ 1 (since the extra term ≥ 0).
    simp only [valCount] ; rw [h_n]
    -- Prove n ≥ 1: if n = 0 then valCount = 0 but hv says valCount * 3 > 0.
    -- valCount ≤ n (two counts out of four that sum to n).
    have h_sum := c.sum_eq ; simp [List.finRange] at h_sum
    have h_n_pos : n ≥ 1 := by
      -- valCount v * 3 > 2n ≥ 0, so valCount v ≥ 1.
      -- valCount v = counts(X) + counts(Y) ≤ sum of all = n.
      -- So n ≥ 1.
      have hvc : valCount n c v ≥ 1 := by omega
      have : v = 0 ∨ v = 1 := by omega
      simp only [valCount, undecidedState, decidedState] at hvc
      rcases ‹v = 0 ∨ v = 1› with rfl | rfl <;> simp at hvc <;> omega
    omega
  · -- [2] Decisions monotone: c.counts(decidedState v) ≤ (extSucc).counts(decidedState v)
    intro v
    -- Three sub-cases on the value threshold view:
    -- (a) v has super-majority: decided-v goes to n in successor (≥ original)
    -- (b) w ≠ v has super-majority: decided-v = 0 in c (by lock), 0 ≤ 0
    -- (c) Neither: successor = current
    by_cases hv : valThreshView n c v = true
    · -- (a) v has super-majority
      have h_n := extSucc_supermaj n c v hv ; rw [h_n]
      have := TLA.mem_le_sum (List.finRange 4) c.counts (decidedState v) (List.mem_finRange _)
      rw [c.sum_eq] at this ; exact this
    · -- v has no super-majority — need to distinguish (b) and (c)
      have hv_f : valThreshView n c v = false := by revert hv ; cases valThreshView n c v <;> simp
      -- Under the lock: decided-v > 0 would give v super-majority, contradicting hv_f
      have hc_dec_zero := lock_no_supermaj_no_decided n c hinv v hv_f
      -- 0 ≤ anything
      omega
  · -- [3] No phantom decisions
    intro v hv
    have hv_f : valThreshView n c v = false := by
      simp [valThreshView] ; revert hv ; cases decide (valCount n c v * 3 > 2 * n) <;> simp
    have hv' : v = 0 ∨ v = 1 := by omega
    by_cases hw : ∃ w, w ≠ v ∧ valThreshView n c w = true
    · -- w dominates: all → decidedState w. decidedState v = 0 in successor.
      -- By lock + no super-majority for v: c.counts(decidedState v) = 0.
      -- Successor also has 0. So 0 = 0. ✓
      obtain ⟨w, hwne, hwv⟩ := hw
      have h_w := extSucc_supermaj n c w hwv
      have h_sum := (extSucc n c).sum_eq ; simp [List.finRange] at h_sum
      have hc_dec_zero := lock_no_supermaj_no_decided n c hinv v hv_f
      simp only [decidedState] at h_w hc_dec_zero ⊢
      rcases hv' with rfl | rfl <;>
        (have : w = 0 ∨ w = 1 := by omega ;
         (rcases ‹w = 0 ∨ w = 1› with rfl | rfl <;> simp_all; omega))
    · -- Neither: decided-v = 0 in c (lock), successor = current
      have hc_dec_zero := lock_no_supermaj_no_decided n c hinv v hv_f
      -- hw : ¬∃ w, w ≠ v ∧ valThreshView n c w = true
      -- Since Fin 2 has only 0 and 1: both must be false
      have h0 : valThreshView n c 0 = false := by
        rcases hv' with rfl | rfl
        · exact hv_f
        · by_contra h0t ; simp at h0t
          exact hw ⟨0, by omega, h0t⟩
      have h1 : valThreshView n c 1 = false := by
        rcases hv' with rfl | rfl
        · by_contra h1t ; simp at h1t
          exact hw ⟨1, by omega, h1t⟩
        · exact hv_f
      rw [extSucc_no_supermaj n c h0 h1, hc_dec_zero]

/-! ### Lock invariant under unreliable communication

    **Theorem** (`lock_inv_step_unreliable`):
    For ANY valid unreliable successor c' of c, if the lock holds
    for c, it holds for c'.

    **English statement**: Suppose in the current configuration, whenever
    some process has decided value v, more than 2n/3 of all processes
    hold v. Then after any valid round step under unreliable communication,
    the same property holds in the successor configuration.

    **Proof**: Two cases based on whether c already had a decision for v:

    **Case 1** (existing decision): c has decided-v > 0. By the lock
    invariant on c, `valCount v > 2n/3`. By constraint [1] of
    `IsValidUnreliableSucc`, the super-majority is preserved in c'.
    Done.

    **Case 2** (new decision): c has decided-v = 0 but c' has
    decided-v > 0. By the CONTRAPOSITIVE of constraint [3]
    (no phantom decisions), v must have had a global super-majority
    in c: `valCount c v * 3 > 2n`. By constraint [1], this
    super-majority is preserved in c'. Done.

    **Key insight**: The proof uses only the three abstract constraints,
    not any details of HO sets or message delivery. Communication closure
    is used once — to JUSTIFY the constraints (votes ≤ holders) — and
    then the invariant argument is purely about counting. -/
theorem lock_inv_step_unreliable (n : Nat) (c c' : Config 4 n)
    (hinv : extLockInv n c)
    (hsucc : IsValidUnreliableSucc n c c') :
    extLockInv n c' := by
  obtain ⟨h_supermaj_pres, h_dec_mono, h_no_phantom⟩ := hsucc
  intro v hv_dec
  by_cases hc_dec : c.counts (decidedState v) > 0
  · -- Case 1: existing decision. Lock gives super-majority, constraint [1] preserves it.
    exact h_supermaj_pres v (hinv v hc_dec)
  · -- Case 2: new decision. Contrapositive of [3] gives super-majority, [1] preserves it.
    simp at hc_dec
    have h_supermaj : valCount n c v * 3 > 2 * n := by
      by_contra h ; exact absurd (h_no_phantom v h) (by omega)
    exact h_supermaj_pres v h_supermaj

end OneThirdRuleCutoff
