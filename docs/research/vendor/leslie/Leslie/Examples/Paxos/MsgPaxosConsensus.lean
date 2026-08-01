import Leslie.Action
import Leslie.Examples.Paxos.MessagePaxos

/-! ## Message-Passing Paxos Refines Consensus

    Proves that the message-passing Paxos model (`MessagePaxos.lean`)
    refines a Consensus specification via a refinement mapping based on
    `sentAccept` majority.

    Combined with `paxos_refines_consensus` from `Leslie.Examples.Paxos`,
    this establishes that **both** the atomic and message-passing models
    refine the same abstract Consensus specification.

    The key ingredients:
    - `cross_ballot_agreement`: at most one value is majority-accepted
    - `sentAccept` monotonicity: once a majority exists, it persists
    - The refinement mapping extracts the (unique) chosen value
-/

open TLA

namespace MessagePaxos

/-! ### Consensus specification (local, using MessagePaxos.Value) -/

structure ConsensusState where
  chosen : Option Value
  deriving DecidableEq

inductive ConsensusAction where
  | choose1 | choose2

def consensus : ActionSpec ConsensusState ConsensusAction where
  init := fun s => s.chosen = none
  actions := fun
    | .choose1 => {
        gate := fun s => s.chosen = none
        transition := fun _ s' => s' = { chosen := some .v1 }
      }
    | .choose2 => {
        gate := fun s => s.chosen = none
        transition := fun _ s' => s' = { chosen := some .v2 }
      }

/-! ### Message-passing Paxos as a TLA Spec -/

def msgPaxosSpec (n m : Nat) (ballot : Fin m → Nat) : Spec (MsgPaxosState n m) where
  init := fun s => s = initialMsgPaxos n m
  next := fun s s' => ∃ a, Step ballot s a s'

/-! ### "Chosen" predicate and refinement mapping -/

/-- A value `v` is chosen at ballot `b` when a majority of acceptors
    have `sentAccept` entries for `v` at `b`. -/
def isChosenAt {n : Nat} (s : MsgPaxosState n m) (b : Nat) (v : Value) : Bool :=
  majority (fun a => decide (s.sentAccept a b = some v))

/-- Some value `v` is chosen at any proposer's ballot. -/
def anyChosen {n m : Nat} (ballot : Fin m → Nat) (s : MsgPaxosState n m) (v : Value) : Bool :=
  (List.finRange m).any fun p => isChosenAt s (ballot p) v

/-- Extract the chosen value (if any). Since `Value` has exactly two
    constructors and `cross_ballot_agreement` ensures at most one is chosen,
    we just check v1 first, then v2. -/
def msgFirstChosen {n m : Nat} (ballot : Fin m → Nat) (s : MsgPaxosState n m) : Option Value :=
  if anyChosen ballot s .v1 then some .v1
  else if anyChosen ballot s .v2 then some .v2
  else none

/-- The refinement mapping from message-passing Paxos to Consensus. -/
def msgPaxosRef {n m : Nat} (ballot : Fin m → Nat) (s : MsgPaxosState n m) :
    ConsensusState where
  chosen := msgFirstChosen ballot s

/-! ### Helper lemmas -/

section Lemmas
variable {n m : Nat} {ballot : Fin m → Nat}

/-- `isChosenAt` on initial state is always false (no sentAccept entries). -/
theorem isChosenAt_initial {b : Nat} {v : Value} :
    isChosenAt (initialMsgPaxos n m) b v = false := by
  unfold isChosenAt majority countTrue initialMsgPaxos
  -- sentAccept = fun _ _ => none, so decide (none = some v) = false
  -- filter with constant false predicate is empty
  suffices h : (List.filter (fun (_ : Fin n) => false) (List.finRange n)).length = 0 by
    simp [h]
  induction (List.finRange n) with
  | nil => rfl
  | cons _ _ ih => simp [List.filter, ih]

/-- `anyChosen` on initial state is always false. -/
theorem anyChosen_initial {v : Value} :
    anyChosen ballot (initialMsgPaxos n m) v = false := by
  unfold anyChosen
  rw [List.any_eq_false]
  intro p _
  rw [isChosenAt_initial]
  decide

/-- `isChosenAt` is monotone: if `sentAccept` entries only grow,
    existing majorities persist. -/
theorem isChosenAt_mono {s s' : MsgPaxosState n m} {b : Nat} {v : Value}
    (hmono : ∀ a c w, s.sentAccept a c = some w → s'.sentAccept a c = some w)
    (h : isChosenAt s b v = true) : isChosenAt s' b v = true := by
  unfold isChosenAt majority at *
  simp only [decide_eq_true_eq] at *
  have hle : countTrue (fun a => decide (s.sentAccept a b = some v)) ≤
             countTrue (fun a => decide (s'.sentAccept a b = some v)) := by
    unfold countTrue
    exact filter_length_mono (List.finRange n)
      (fun a => decide (s.sentAccept a b = some v))
      (fun a => decide (s'.sentAccept a b = some v))
      (by intro a ha; simp only [decide_eq_true_eq] at *; exact hmono a b v ha)
  omega

/-- `anyChosen` is monotone. -/
theorem anyChosen_mono {s s' : MsgPaxosState n m} {v : Value}
    (hmono : ∀ a c w, s.sentAccept a c = some w → s'.sentAccept a c = some w)
    (h : anyChosen ballot s v = true) : anyChosen ballot s' v = true := by
  unfold anyChosen at *
  rw [List.any_eq_true] at *
  obtain ⟨p, hp_mem, hp_chosen⟩ := h
  exact ⟨p, hp_mem, isChosenAt_mono hmono hp_chosen⟩

/-- `msgFirstChosen` depends on `s` only through `s.sentAccept`. -/
theorem msgFirstChosen_congr {s s' : MsgPaxosState n m}
    (heq : s'.sentAccept = s.sentAccept) :
    msgFirstChosen ballot s' = msgFirstChosen ballot s := by
  unfold msgFirstChosen anyChosen isChosenAt; rw [heq]

/-- If both v1 and v2 are `anyChosen`, contradiction via `cross_ballot_agreement`. -/
theorem anyChosen_exclusive (h_inj : Function.Injective ballot)
    {s : MsgPaxosState n m} (hreach : Reachable ballot s) :
    ¬(anyChosen ballot s .v1 = true ∧ anyChosen ballot s .v2 = true) := by
  intro ⟨hv1, hv2⟩
  unfold anyChosen at hv1 hv2
  rw [List.any_eq_true] at hv1 hv2
  obtain ⟨p1, _, hp1⟩ := hv1
  obtain ⟨p2, _, hp2⟩ := hv2
  unfold isChosenAt at hp1 hp2
  have := cross_ballot_agreement h_inj hreach (ballot p1) (ballot p2) .v1 .v2 hp1 hp2
  exact absurd this (by decide)

/-- `msgFirstChosen` is monotone under reachable states. -/
theorem msgFirstChosen_mono (h_inj : Function.Injective ballot)
    {s s' : MsgPaxosState n m}
    (hreach' : Reachable ballot s')
    (hmono : ∀ i c w, s.sentAccept i c = some w → s'.sentAccept i c = some w)
    {v : Value} (h : msgFirstChosen ballot s = some v) :
    msgFirstChosen ballot s' = some v := by
  unfold msgFirstChosen at *
  cases v with
  | v1 =>
    split at h
    · -- anyChosen s v1 = true
      rename_i hv1
      simp [anyChosen_mono hmono hv1]
    · split at h <;> simp at h
  | v2 =>
    split at h
    · simp at h
    · rename_i hv1_not
      split at h
      · rename_i hv2
        simp at h
        have hv2' := anyChosen_mono hmono hv2
        -- If anyChosen s' v1, then both v1 and v2 chosen in s' → contradiction
        split
        · rename_i hv1'
          exact absurd ⟨hv1', hv2'⟩ (anyChosen_exclusive h_inj hreach')
        · simp
      · simp at h

/-! ### sentAccept monotonicity across steps -/

/-- Every `Step` preserves existing `sentAccept` entries. -/
theorem sentAccept_mono_step {s s' : MsgPaxosState n m} {act : MsgAction n m}
    (hinv : MsgPaxosInv ballot s) (hstep : Step ballot s act s') :
    ∀ i c w, s.sentAccept i c = some w → s'.sentAccept i c = some w := by
  intro i c w h
  cases hstep with
  | sendPrepare _ => exact h
  | recvPrepare _ _ _ _ _ _ => exact h
  | recvPromise _ _ _ _ _ _ => exact h
  | decidePropose _ _ _ _ _ _ => exact h
  | sendAccept _ _ _ _ _ => exact h
  | recvAccept a₀ _ b₀ v₀ _ hMem _ _ =>
    simp only [setSent]
    by_cases hc : i = a₀ ∧ c = b₀
    · rw [if_pos hc]
      obtain ⟨ha, hb⟩ := hc; subst ha; subst hb
      have := hinv.hSentAcceptNet i c w h _ v₀ (Target.acc i) hMem
      rw [this]
    · rw [if_neg hc]; exact h
  | dropMsg _ => exact h
  | crashProposer _ => exact h
  | crashAcceptor _ => exact h

/-- `sentAccept` monotonicity from `Reachable`. -/
theorem sentAccept_mono_reachable_step {s s' : MsgPaxosState n m}
    (h_inj : Function.Injective ballot)
    (hreach : Reachable ballot s) {act : MsgAction n m} (hstep : Step ballot s act s') :
    ∀ i c w, s.sentAccept i c = some w → s'.sentAccept i c = some w :=
  sentAccept_mono_step (msg_paxos_inv_reachable h_inj hreach) hstep

/-! ### Step simulation -/

/-- For non-recvAccept steps, `sentAccept` is unchanged. -/
private theorem sentAccept_eq_of_non_recvAccept {s s' : MsgPaxosState n m}
    {act : MsgAction n m} (hstep : Step ballot s act s')
    (h_not_recv : ∀ (a : Fin n) (p : Fin m) (b : Nat) (v : Value),
      act ≠ MsgAction.recvAccept a p b v) :
    s'.sentAccept = s.sentAccept := by
  cases hstep with
  | sendPrepare _ => rfl
  | recvPrepare _ _ _ _ _ _ => rfl
  | recvPromise _ _ _ _ _ _ => rfl
  | decidePropose _ _ _ _ _ _ => rfl
  | sendAccept _ _ _ _ _ => rfl
  | recvAccept a p b v _ _ _ _ => exact absurd rfl (h_not_recv a p b v)
  | dropMsg _ => rfl
  | crashProposer _ => rfl
  | crashAcceptor _ => rfl

/-- Main step simulation: each message-passing step either preserves
    the refinement mapping (stutter) or transitions from `none` to `some v`
    (consensus choose). -/
theorem msg_paxos_step_sim (h_inj : Function.Injective ballot)
    {s s' : MsgPaxosState n m}
    (hreach : Reachable ballot s) (hstep : ∃ act, Step ballot s act s') :
    (∃ i, (consensus.actions i).fires (msgPaxosRef ballot s) (msgPaxosRef ballot s')) ∨
    msgPaxosRef ballot s = msgPaxosRef ballot s' := by
  obtain ⟨act, hstep⟩ := hstep
  have hreach' : Reachable ballot s' := Reachable.step hreach hstep
  -- Case split: is this a recvAccept or not?
  by_cases h_recv : ∃ (a : Fin n) (p : Fin m) (b : Nat) (v : Value),
      act = MsgAction.recvAccept a p b v
  · -- recvAccept: sentAccept grows
    obtain ⟨_, _, _, _, rfl⟩ := h_recv
    have hmono := sentAccept_mono_reachable_step h_inj hreach hstep
    -- Case split on whether a value was already chosen
    by_cases h_already : msgFirstChosen ballot s = none
    · -- Not yet chosen
      by_cases h_now : msgFirstChosen ballot s' = none
      · -- Still not chosen → stutter
        right; simp only [msgPaxosRef, h_already, h_now]
      · -- Newly chosen → consensus choose
        left
        obtain ⟨v, hv'⟩ := Option.ne_none_iff_exists'.mp h_now
        cases v with
        | v1 =>
          exact ⟨.choose1, by
            constructor
            · show (msgPaxosRef ballot s).chosen = none; simp [msgPaxosRef, h_already]
            · show msgPaxosRef ballot s' = ⟨some .v1⟩; simp [msgPaxosRef, hv']⟩
        | v2 =>
          exact ⟨.choose2, by
            constructor
            · show (msgPaxosRef ballot s).chosen = none; simp [msgPaxosRef, h_already]
            · show msgPaxosRef ballot s' = ⟨some .v2⟩; simp [msgPaxosRef, hv']⟩
    · -- Already chosen: monotonicity preserves it → stutter
      right
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp h_already
      have hv' := msgFirstChosen_mono h_inj hreach' hmono hv
      simp only [msgPaxosRef, hv, hv']
  · -- Non-recvAccept: sentAccept unchanged → stutter
    right
    have h_recv' : ∀ (a : Fin n) (p : Fin m) (b : Nat) (v : Value),
        act ≠ MsgAction.recvAccept a p b v :=
      fun a p b v heq => h_recv ⟨a, p, b, v, heq⟩
    have heq : s'.sentAccept = s.sentAccept :=
      sentAccept_eq_of_non_recvAccept hstep h_recv'
    show msgPaxosRef ballot s = msgPaxosRef ballot s'
    simp only [msgPaxosRef, (msgFirstChosen_congr heq).symm]

/-! ### Init preservation -/

theorem msg_paxos_init_ref :
    ∀ s, s = initialMsgPaxos n m → consensus.init (msgPaxosRef ballot s) := by
  intro s hs; subst hs
  show (msgPaxosRef ballot (initialMsgPaxos n m)).chosen = none
  simp only [msgPaxosRef, msgFirstChosen, anyChosen_initial, Bool.false_eq_true, ite_false]

/-! ### Main refinement theorem -/

/-- The message-passing Paxos model refines the Consensus specification
    (with stuttering) via the `msgPaxosRef` mapping. -/
theorem msg_paxos_refines_consensus {n m : Nat} (ballot : Fin m → Nat)
    (h_inj : Function.Injective ballot) :
    refines_via (msgPaxosRef ballot) (msgPaxosSpec n m ballot).safety
      consensus.toSpec.safety_stutter := by
  apply refinement_mapping_stutter_with_invariant
    (msgPaxosSpec n m ballot) consensus.toSpec (msgPaxosRef ballot) (Reachable ballot)
  · -- inv_init
    intro s hs; subst hs; exact Reachable.init
  · -- inv_next
    intro s s' hr ⟨act, hstep⟩; exact Reachable.step hr hstep
  · -- init simulation
    intro s hs; exact msg_paxos_init_ref s hs
  · -- step simulation
    intro s s' hr hnext; exact msg_paxos_step_sim h_inj hr hnext

end Lemmas

end MessagePaxos
