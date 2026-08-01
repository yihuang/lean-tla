import Leslie.Layers

/-! ## Ticket Lock: Layered Refinement Example

    A ticket lock protocol verified via CIVL-style layered refinement.

    **Layer 0** (concrete): Ticket-based mutual exclusion
      State: next ticket counter, serving counter, each thread's ticket
      Actions: acquire (fetch-and-increment), enter (when ticket = serving),
               leave (increment serving)

    **Layer 1** (abstract): Abstract lock
      State: lock holder (Option ThreadId)
      Actions: acquire-and-enter (atomic), leave

    We define both layers and the refinement between them.
    The key insight: at Layer 0, `acquire` is a right-mover and
    `enter` is a non-mover, so `acquire;enter` can be reduced to
    a single atomic action at Layer 1.
-/

open TLA

namespace TicketLock

/-! ### Thread identifiers -/

inductive ThreadId where | t1 | t2
  deriving DecidableEq, Repr

/-! ### Layer 0: Concrete ticket lock -/

structure L0State where
  nextTicket : Nat
  serving : Nat
  ticket1 : Option Nat   -- thread 1's ticket (None if not acquired)
  ticket2 : Option Nat   -- thread 2's ticket
  cs : Option ThreadId   -- who is in the critical section

inductive L0Action where
  | acquire1 | acquire2
  | enter1 | enter2
  | leave1 | leave2

def l0 : ActionSpec L0State L0Action where
  init := fun s =>
    s.nextTicket = 0 ∧ s.serving = 0 ∧
    s.ticket1 = none ∧ s.ticket2 = none ∧ s.cs = none
  actions := fun
    | .acquire1 => {
        gate := fun s => s.ticket1 = none
        transition := fun s s' =>
          s' = { s with nextTicket := s.nextTicket + 1, ticket1 := some s.nextTicket }
      }
    | .acquire2 => {
        gate := fun s => s.ticket2 = none
        transition := fun s s' =>
          s' = { s with nextTicket := s.nextTicket + 1, ticket2 := some s.nextTicket }
      }
    | .enter1 => {
        gate := fun s => s.ticket1 = some s.serving ∧ s.cs = none
        transition := fun s s' => s' = { s with cs := some .t1 }
      }
    | .enter2 => {
        gate := fun s => s.ticket2 = some s.serving ∧ s.cs = none
        transition := fun s s' => s' = { s with cs := some .t2 }
      }
    | .leave1 => {
        gate := fun s => s.cs = some .t1
        transition := fun s s' =>
          s' = { s with cs := none, serving := s.serving + 1, ticket1 := none }
      }
    | .leave2 => {
        gate := fun s => s.cs = some .t2
        transition := fun s s' =>
          s' = { s with cs := none, serving := s.serving + 1, ticket2 := none }
      }

/-! ### Layer 1: Abstract lock -/

structure L1State where
  cs : Option ThreadId

inductive L1Action where
  | enter1 | enter2
  | leave1 | leave2

def l1 : ActionSpec L1State L1Action where
  init := fun s => s.cs = none
  actions := fun
    | .enter1 => {
        gate := fun s => s.cs = none
        transition := fun _ s' => s' = { cs := some .t1 }
      }
    | .enter2 => {
        gate := fun s => s.cs = none
        transition := fun _ s' => s' = { cs := some .t2 }
      }
    | .leave1 => {
        gate := fun s => s.cs = some .t1
        transition := fun _ s' => s' = { cs := none }
      }
    | .leave2 => {
        gate := fun s => s.cs = some .t2
        transition := fun _ s' => s' = { cs := none }
      }

/-! ### Mover type annotations for Layer 0

    - acquire: right-mover (commutes right past other threads' actions)
    - enter: non-mover (the critical step)
    - leave: left-mover (commutes left past other threads' actions)

    These mover types justify the reduction:
    acquire;enter → atomic enter (Layer 1)
    leave stays as-is -/

def l0_movers : L0Action → MoverType
  | .acquire1 | .acquire2 => .right
  | .enter1 | .enter2 => .nonmover
  | .leave1 | .leave2 => .left

def layer0 : Layer L0State L0Action where
  spec := l0
  mover := l0_movers

/-! ### Refinement mapping: Layer 0 → Layer 1

    The abstraction projects away the ticket machinery,
    keeping only who is in the critical section.
    - acquire actions are stuttering steps (cs doesn't change)
    - enter/leave actions map directly -/

def abs_map : L0State → L1State :=
  fun s => { cs := s.cs }

/-! ### The refinement proof

    We show each L0 action either maps to an L1 action or stutters.
    Since L0 has 6 actions but L1 has 4, we need a mapping from
    L0 action indices to L1 action indices (acquire maps to stutter).

    Rather than using `LayerRefinement` (which requires matching index types),
    we use the more general `ActionSpecRefinement`-style approach with
    `refines_via` directly. -/

theorem ticket_lock_refinement :
    refines_via abs_map l0.toSpec.safety l1.toSpec.safety_stutter := by
  apply refinement_mapping_stutter l0.toSpec l1.toSpec abs_map
  · intro s ⟨_, _, _, _, hcs⟩ ; exact hcs
  · intro s s' ⟨i, hfire⟩
    simp [l0, GatedAction.fires] at hfire
    cases i <;> obtain ⟨hgate, htrans⟩ := hfire <;> subst htrans
    -- acquire1, acquire2: stuttering (cs unchanged)
    · right ; simp [abs_map]
    · right ; simp [abs_map]
    -- enter1: maps to l1.enter1
    · left ; exact ⟨.enter1, hgate.2, rfl⟩
    -- enter2: maps to l1.enter2
    · left ; exact ⟨.enter2, hgate.2, rfl⟩
    -- leave1: maps to l1.leave1
    · left ; exact ⟨.leave1, hgate, rfl⟩
    -- leave2: maps to l1.leave2
    · left ; exact ⟨.leave2, hgate, rfl⟩

/-! ### Mutual exclusion at Layer 0

    We prove mutual exclusion for the concrete ticket lock:
    threads t1 and t2 are never both in the critical section.
    The invariant says `cs` is at most one thread. -/

def l0_mutex (s : L0State) : Prop :=
  ¬ (s.cs = some .t1 ∧ s.cs = some .t2)

theorem l0_mutex_invariant :
    pred_implies l0.toSpec.safety [tlafml| □ ⌜ l0_mutex ⌝] := by
  apply init_invariant
  · intro s ⟨_, _, _, _, hcs⟩
    simp [l0_mutex, hcs]
  · intro s s' ⟨i, hfire⟩ hinv
    simp [l0_mutex] at *
    cases i <;> simp [l0, GatedAction.fires] at hfire <;>
      obtain ⟨hgate, htrans⟩ := hfire <;> subst htrans <;> simp_all

/-! ### Layer 0nd: Non-deterministic ticket lock

    To prove mover types are valid, we need acquire actions to commute.
    Deterministic fetch-and-increment doesn't commute (swapping two
    acquires gives different ticket values). The standard CIVL approach:
    introduce a layer with non-deterministic ticket allocation, which
    does commute, and show the deterministic version refines it.

    State: same as L0 but without `nextTicket` (tickets chosen freely). -/

@[ext]
structure L0ndState where
  serving : Nat
  ticket1 : Option Nat
  ticket2 : Option Nat
  cs : Option ThreadId

def l0nd : ActionSpec L0ndState L0Action where
  init := fun s =>
    s.serving = 0 ∧ s.ticket1 = none ∧ s.ticket2 = none ∧ s.cs = none
  actions := fun
    | .acquire1 => {
        gate := fun s => s.ticket1 = none
        transition := fun s s' => ∃ t, s' = { s with ticket1 := some t }
      }
    | .acquire2 => {
        gate := fun s => s.ticket2 = none
        transition := fun s s' => ∃ t, s' = { s with ticket2 := some t }
      }
    | .enter1 => {
        gate := fun s => s.ticket1 = some s.serving ∧ s.cs = none
        transition := fun s s' => s' = { s with cs := some .t1 }
      }
    | .enter2 => {
        gate := fun s => s.ticket2 = some s.serving ∧ s.cs = none
        transition := fun s s' => s' = { s with cs := some .t2 }
      }
    | .leave1 => {
        gate := fun s => s.cs = some .t1
        transition := fun s s' =>
          s' = { s with cs := none, serving := s.serving + 1, ticket1 := none }
      }
    | .leave2 => {
        gate := fun s => s.cs = some .t2
        transition := fun s s' =>
          s' = { s with cs := none, serving := s.serving + 1, ticket2 := none }
      }

/-! ### Thread assignment -/

def l0_thread : L0Action → ThreadId
  | .acquire1 | .enter1 | .leave1 => .t1
  | .acquire2 | .enter2 | .leave2 => .t2

def l0nd_movers : L0Action → MoverType
  | .acquire1 | .acquire2 => .right
  | .enter1 | .enter2 => .nonmover
  | .leave1 | .leave2 => .left

def layer0nd : Layer L0ndState L0Action where
  spec := l0nd
  mover := l0nd_movers

/-! ### Mover validity proof

    We prove that mover types are valid per-thread:
    - acquire (right-mover) commutes right past other thread's actions
    - leave (left-mover) commutes left past other thread's actions

    Key insight: with non-deterministic tickets, acquire1 and acquire2
    write to independent fields (ticket1 vs ticket2), so they commute. -/

-- Right-commutativity: acquire writes one ticket field, other action doesn't touch it.
-- After swapping, the intermediate state has the other action applied first.
-- The key property: struct updates on independent fields commute.
private theorem rc_acquire1_acquire2 :
    right_commutes (l0nd.actions .acquire1) (l0nd.actions .acquire2) := by
  intro s s₁ s₂ ⟨hga, t₁, hs₁⟩ ⟨hgb, t₂, hs₂⟩
  subst hs₁ hs₂
  exact ⟨{ s with ticket2 := some t₂ }, ⟨hgb, t₂, rfl⟩, ⟨hga, t₁, by ext <;> simp⟩⟩

private theorem rc_acquire1_enter2 :
    right_commutes (l0nd.actions .acquire1) (l0nd.actions .enter2) := by
  intro s s₁ s₂ ⟨hga, t₁, hs₁⟩ ⟨⟨hgb1, hgb2⟩, hs₂⟩
  subst hs₁ hs₂
  exact ⟨{ s with cs := some .t2 }, ⟨⟨hgb1, hgb2⟩, rfl⟩, ⟨hga, t₁, by ext <;> simp⟩⟩

private theorem rc_acquire1_leave2 :
    right_commutes (l0nd.actions .acquire1) (l0nd.actions .leave2) := by
  intro s s₁ s₂ ⟨hga, t₁, hs₁⟩ ⟨hgb, hs₂⟩
  subst hs₁ hs₂
  exact ⟨{ s with cs := none, serving := s.serving + 1, ticket2 := none },
    ⟨hgb, rfl⟩, ⟨hga, t₁, by ext <;> simp⟩⟩

private theorem rc_acquire2_acquire1 :
    right_commutes (l0nd.actions .acquire2) (l0nd.actions .acquire1) := by
  intro s s₁ s₂ ⟨hga, t₁, hs₁⟩ ⟨hgb, t₂, hs₂⟩
  subst hs₁ hs₂
  exact ⟨{ s with ticket1 := some t₂ }, ⟨hgb, t₂, rfl⟩, ⟨hga, t₁, by ext <;> simp⟩⟩

private theorem rc_acquire2_enter1 :
    right_commutes (l0nd.actions .acquire2) (l0nd.actions .enter1) := by
  intro s s₁ s₂ ⟨hga, t₁, hs₁⟩ ⟨⟨hgb1, hgb2⟩, hs₂⟩
  subst hs₁ hs₂
  exact ⟨{ s with cs := some .t1 }, ⟨⟨hgb1, hgb2⟩, rfl⟩, ⟨hga, t₁, by ext <;> simp⟩⟩

private theorem rc_acquire2_leave1 :
    right_commutes (l0nd.actions .acquire2) (l0nd.actions .leave1) := by
  intro s s₁ s₂ ⟨hga, t₁, hs₁⟩ ⟨hgb, hs₂⟩
  subst hs₁ hs₂
  exact ⟨{ s with cs := none, serving := s.serving + 1, ticket1 := none },
    ⟨hgb, rfl⟩, ⟨hga, t₁, by ext <;> simp⟩⟩

-- Left-commutativity: leave writes cs/serving/ticket, acquire writes the other ticket
private theorem lc_leave1_acquire2 :
    left_commutes (l0nd.actions .leave1) (l0nd.actions .acquire2) := by
  intro s s₁ s₂ ⟨hgb, t₁, hs₁⟩ ⟨hga, hs₂⟩
  subst hs₁ hs₂
  exact ⟨{ s with cs := none, serving := s.serving + 1, ticket1 := none },
    ⟨hga, rfl⟩, ⟨hgb, t₁, by ext <;> simp⟩⟩

-- leave1 vs enter2: vacuous — enter2 sets cs := some .t2, leave1 needs cs = some .t1
private theorem lc_leave1_enter2 :
    left_commutes (l0nd.actions .leave1) (l0nd.actions .enter2) := by
  intro s s₁ s₂ ⟨⟨_, _⟩, hs₁⟩ ⟨hga, _⟩
  subst hs₁ ; simp [l0nd] at hga

-- leave1 vs leave2: vacuous — leave2 sets cs := none, leave1 needs cs = some .t1
private theorem lc_leave1_leave2 :
    left_commutes (l0nd.actions .leave1) (l0nd.actions .leave2) := by
  intro s s₁ s₂ ⟨hg1, hs₁⟩ ⟨hga, _⟩
  subst hs₁ ; simp [l0nd] at hga

private theorem lc_leave2_acquire1 :
    left_commutes (l0nd.actions .leave2) (l0nd.actions .acquire1) := by
  intro s s₁ s₂ ⟨hgb, t₁, hs₁⟩ ⟨hga, hs₂⟩
  subst hs₁ hs₂
  exact ⟨{ s with cs := none, serving := s.serving + 1, ticket2 := none },
    ⟨hga, rfl⟩, ⟨hgb, t₁, by ext <;> simp⟩⟩

private theorem lc_leave2_enter1 :
    left_commutes (l0nd.actions .leave2) (l0nd.actions .enter1) := by
  intro s s₁ s₂ ⟨⟨_, _⟩, hs₁⟩ ⟨hga, _⟩
  subst hs₁ ; simp [l0nd] at hga

private theorem lc_leave2_leave1 :
    left_commutes (l0nd.actions .leave2) (l0nd.actions .leave1) := by
  intro s s₁ s₂ ⟨hg1, hs₁⟩ ⟨hga, _⟩
  subst hs₁ ; simp [l0nd] at hga

theorem layer0nd_movers_valid :
    layer0nd.movers_valid_threaded l0_thread := by
  intro i j hij ; constructor
  · intro hr
    cases i <;> cases j <;>
      simp [l0nd_movers, MoverType.isRight, layer0nd] at hr <;>
      simp [l0_thread] at hij
    · exact rc_acquire1_acquire2
    · exact rc_acquire1_enter2
    · exact rc_acquire1_leave2
    · exact rc_acquire2_acquire1
    · exact rc_acquire2_enter1
    · exact rc_acquire2_leave1
  · intro hl
    cases i <;> cases j <;>
      simp [l0nd_movers, MoverType.isLeft, layer0nd] at hl <;>
      simp [l0_thread] at hij
    · exact lc_leave1_acquire2
    · exact lc_leave1_enter2
    · exact lc_leave1_leave2
    · exact lc_leave2_acquire1
    · exact lc_leave2_enter1
    · exact lc_leave2_leave1

/-! ### Layer 0 refines Layer 0nd

    The deterministic fetch-and-increment is a special case of
    non-deterministic allocation (choose t = nextTicket). -/

def l0_to_l0nd (s : L0State) : L0ndState where
  serving := s.serving
  ticket1 := s.ticket1
  ticket2 := s.ticket2
  cs := s.cs

theorem l0_refines_l0nd :
    refines_via l0_to_l0nd l0.toSpec.safety l0nd.toSpec.safety_stutter := by
  apply refinement_mapping_stutter l0.toSpec l0nd.toSpec l0_to_l0nd
  · intro s ⟨_, hs, ht1, ht2, hcs⟩
    exact ⟨hs, ht1, ht2, hcs⟩
  · intro s s' ⟨i, hfire⟩
    cases i <;> simp [l0, GatedAction.fires] at hfire <;>
      obtain ⟨hgate, htrans⟩ := hfire <;> subst htrans
    -- acquire1: maps to l0nd.acquire1 with t = s.nextTicket
    · left ; exact ⟨.acquire1, hgate, s.nextTicket, by ext <;> simp [l0_to_l0nd]⟩
    -- acquire2
    · left ; exact ⟨.acquire2, hgate, s.nextTicket, by ext <;> simp [l0_to_l0nd]⟩
    -- enter1
    · left ; exact ⟨.enter1, ⟨hgate.1, hgate.2⟩, by ext <;> simp [l0_to_l0nd]⟩
    -- enter2
    · left ; exact ⟨.enter2, ⟨hgate.1, hgate.2⟩, by ext <;> simp [l0_to_l0nd]⟩
    -- leave1
    · left ; exact ⟨.leave1, hgate, by ext <;> simp [l0_to_l0nd]⟩
    -- leave2
    · left ; exact ⟨.leave2, hgate, by ext <;> simp [l0_to_l0nd]⟩

end TicketLock
