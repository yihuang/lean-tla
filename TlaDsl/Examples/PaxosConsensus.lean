import TlaDsl.Basic
import TlaDsl.Notation
import TlaDsl.Coercion
import TlaDsl.Prime
import TlaDsl.Rules
import TlaDsl.Meta
import TlaDsl.Tactic
import TlaDsl.TlaVar
import TlaDsl.Examples.Paxos

open scoped Tla

/-! # Paxos implements Consensus

The refinement theorem at the end of `Voting.tla` (`Spec => C!Spec`), in the
typed DSL: the Paxos/Voting spec of `Paxos.lean` refines the abstract
**Consensus** spec, with the refinement mapping

```lean
chosenVal s = some v   iff   ∃ b, ChosenAt s b v   (for the fixed `n`)
```

i.e. the (unique, by agreement) value chosen by some ballot quorum. This is
the payoff of the agreement invariant: the mapping's well-definedness *is*
the Paxos safety property.

The abstract state is `Option Value`, which encodes `Consensus.tla`'s
"`chosen` is empty or a singleton, set at most once, then fixed" directly:
`Next` is enabled only when `chosen = none`, and `[Next]_chosen` allows
stuttering afterwards.

The step correspondence only holds on states satisfying the Paxos invariant
(`Inv n`), so we use the invariant-threading refinement rule
`Tla.refinement_mapping_inv` — the Abadi–Lamport theorem with an auxiliary
invariant.
-/

namespace TlaDsl.Examples.PaxosConsensus

open TlaDsl.Examples.Paxos

/-! ## The abstract Consensus spec -/

/-- The consensus state: the value chosen so far, if any. -/
structure CSt where
  chosen : Option Value

/-- The state function (defined by hand: `tla_var` would generate a `vars`
that collides with the Paxos one opened above). -/
@[simp] def chosenC : CSt → Option Value := CSt.chosen

/-- Initially no value is chosen. -/
@[simp] def CInit : Tla.StatePred CSt := [p| chosenC = none]

/-- A value can be chosen only while nothing has been chosen yet; once
chosen it never changes (the frame allows stuttering). -/
@[simp] def CNext : Tla.Action CSt :=
  [a| chosenC = none ∧ ∃ v : Value, chosenC' = some v]

@[simp] def CVars : CSt → Option Value := CSt.chosen

def CSpec : Tla.Pred CSt := [t| CInit ∧ □[CNext]_CVars]

/-! ## The refinement mapping -/

/-- The value chosen by some ballot quorum, if any. By agreement at most one
such value exists, so `Classical.choose` is canonical on reachable states. -/
noncomputable def chosenVal (n : Nat) (s : St) : Option Value :=
  by
    classical
    exact if h : ∃ v : Value, ∃ b : Ballot, ChosenAt s n b v then
      some (Classical.choose h)
    else none

/-- The refinement mapping from Paxos states to Consensus states. -/
noncomputable def f (n : Nat) : St → CSt := fun s => { chosen := chosenVal n s }

/-! ## The mapping is canonical (agreement) -/

/-- If a value is chosen at some ballot, the mapping records it. -/
lemma chosenVal_eq_of_chosenAt {n : Nat} {s : St} (hInv : Inv n s) {v : Value}
    (hv : ∃ b : Ballot, ChosenAt s n b v) : chosenVal n s = some v := by
  unfold chosenVal
  have hs : ∃ v : Value, ∃ b : Ballot, ChosenAt s n b v := ⟨v, hv⟩
  rw [dif_pos hs]
  congr
  rcases Classical.choose_spec hs with ⟨b0, hcv⟩
  exact agree_of_inv n s hInv (Classical.choose hs) v ⟨b0, hcv⟩ hv

/-- If the mapping records `v`, then `v` is chosen at some ballot. -/
lemma chosenAt_of_chosenVal {n : Nat} {s : St} {v : Value}
    (hv : chosenVal n s = some v) : ∃ b : Ballot, ChosenAt s n b v := by
  unfold chosenVal at hv
  by_cases hs : ∃ v : Value, ∃ b : Ballot, ChosenAt s n b v
  · rw [dif_pos hs] at hv
    have hc : Classical.choose hs = v := Option.some.inj hv
    rcases Classical.choose_spec hs with ⟨b0, hcv⟩
    rw [← hc]
    exact ⟨b0, hcv⟩
  · rw [dif_neg hs] at hv
    simp at hv

/-- The mapping only depends on the votes. -/
lemma chosenVal_eq_of_votes {n : Nat} {s s' : St} (hInv : Inv n s) (hInv' : Inv n s')
    (h : s'.votes = s.votes) : chosenVal n s' = chosenVal n s := by
  by_cases hs : chosenVal n s = none
  · -- nothing chosen in s, so nothing chosen in s' either
    have hs' : chosenVal n s' = none := by
      by_contra hne
      rcases Option.ne_none_iff_exists.mp hne with ⟨v, hv'⟩
      rcases chosenAt_of_chosenVal hv'.symm with ⟨b, hcv'⟩
      have hcv : ChosenAt s n b v := by simpa [ChosenAt, ← h] using hcv'
      have hval : chosenVal n s = some v := chosenVal_eq_of_chosenAt hInv ⟨b, hcv⟩
      simp [hval] at hs
    rw [hs', hs]
  · rcases Option.ne_none_iff_exists.mp hs with ⟨v, hv⟩
    rcases chosenAt_of_chosenVal hv.symm with ⟨b, hcv⟩
    have hcv' : ChosenAt s' n b v := by simpa [ChosenAt, h] using hcv
    rw [chosenVal_eq_of_chosenAt hInv' ⟨b, hcv'⟩, hv]

/-! ## Every Paxos step refines a Consensus step -/

/-- Votes survive a voting step (only `(a, b)` is written). -/
lemma votes_stable_vote {s : St} {a : Acceptor} {b : Ballot} {v : Value}
    (hNoVote : s.votes a b = none) {a0 : Acceptor} {b0 : Ballot} {w : Value}
    (hv : s.votes a0 b0 = some w) : (vote s a b v).votes a0 b0 = some w := by
  by_cases hb0 : b0 = b
  · subst b0
    by_cases ha0 : a0 = a
    · subst a0
      simp [hNoVote] at hv
    · simpa [vote, ha0] using hv
  · by_cases ha0 : a0 = a
    · subst a0
      simpa [vote, hb0] using hv
    · simpa [vote, ha0] using hv

/-- A choice already made survives a voting step. -/
lemma chosenAt_stable_vote {n : Nat} {s : St} {a : Acceptor} {b : Ballot} {v : Value}
    (hNoVote : s.votes a b = none) {b0 : Ballot} {w : Value}
    (hcv : ChosenAt s n b0 w) : ChosenAt (vote s a b v) n b0 w := by
  rcases hcv with ⟨Q, hQ, hQv⟩
  refine ⟨Q, hQ, ?_⟩
  intro a0 ha0
  exact votes_stable_vote hNoVote (hQv a0 ha0)

theorem init_refines (n : Nat) : ∀ s : St, Init s → CInit (f n s) := by
  intro s hs
  classical
  tla_unfold
  unfold f chosenVal
  have hno : ¬ ∃ v : Value, ∃ b : Ballot, ChosenAt s n b v := by
    rintro ⟨v, b, hcv⟩
    rcases hcv with ⟨Q, hQ, hQv⟩
    rcases quorum_nonempty hQ with ⟨a, ha⟩
    have hvote : s.votes a b = some v := hQv a ha
    simp [hs.1 a b] at hvote
  rw [dif_neg hno]

/-- The Paxos invariant is preserved by every step. -/
theorem step_inv (n : Nat) : ∀ s s' : St, (Next n s s' ∨ vars s' = vars s) →
    Inv n s → Inv n s' := by
  intro s s' hstep hInv
  rcases hstep with hnext | hstut
  · exact next_inv n s s' hnext hInv
  · exact stutter_inv n s s' hstut hInv

/-- The step correspondence, licensed by the invariant: every Paxos step
maps to a Consensus step, or leaves the mapped `chosen` unchanged. -/
theorem step_refines (n : Nat) : ∀ s s' : St,
    Inv n s → (Next n s s' ∨ vars s' = vars s) →
    (CNext (f n s) (f n s') ∨ CVars (f n s') = CVars (f n s)) := by
  intro s s' hInv hstep
  rcases hstep with hnext | hstut
  · unfold Next at hnext
    rcases hnext with ⟨a, b, hnext⟩
    rcases hnext with hinc | ⟨v, hvot⟩
    · -- IncreaseMaxBal: the votes, hence the mapping, are unchanged.
      have hVotes' : s'.votes = s.votes := by
        rcases hinc with ⟨_, _, hVotes'⟩
        exact hVotes'
      right
      exact chosenVal_eq_of_votes hInv (increase_inv hinc hInv) hVotes'
    · -- VoteFor: a value is chosen at most once.
      have hNoVote : s.votes a b = none := by
        rcases hvot with ⟨_, hNoVote, _, _, _, _⟩
        exact hNoVote
      have hVotes' : s'.votes = Function.update s.votes a (Function.update (s.votes a) b (some v)) := by
        rcases hvot with ⟨_, _, _, _, hVotes', _⟩
        exact hVotes'
      have hMaxBal' : s'.maxBal = Function.update s.maxBal a b := by
        rcases hvot with ⟨_, _, _, _, _, hMaxBal'⟩
        exact hMaxBal'
      have hs' : s' = vote s a b v := by
        ext <;> simp [vote, hVotes', hMaxBal']
      have hInv' : Inv n s' := vote_inv hvot hInv
      by_cases hchg : chosenVal n s' = chosenVal n s
      · right
        exact hchg
      · left
        have hvalNone : chosenVal n s = none := by
          by_contra hne
          rcases Option.ne_none_iff_exists.mp hne with ⟨w, hw⟩
          rcases chosenAt_of_chosenVal hw.symm with ⟨b0, hcv⟩
          have hcv' : ChosenAt s' n b0 w := by
            subst s'
            exact chosenAt_stable_vote hNoVote hcv
          have hw' : chosenVal n s' = some w := chosenVal_eq_of_chosenAt hInv' ⟨b0, hcv'⟩
          exact hchg (by rw [hw', hw])
        constructor
        · exact hvalNone
        · rcases Option.ne_none_iff_exists.mp
            (by intro hn; exact hchg (hn.trans hvalNone.symm)) with ⟨v', hv'⟩
          exact ⟨v', hv'.symm⟩
  · right
    have hs' : s' = s := by
      change s' = s at hstut
      exact hstut
    subst s'
    rfl

/-! ## The refinement theorem -/

/-- The Paxos spec refines the Consensus spec via the `chosen` mapping. -/
theorem voting_refines_consensus (n : Nat) : Tla.RefinesVia (f n) (Spec n) CSpec := by
  unfold Spec CSpec
  exact Tla.refinement_mapping_inv CInit CNext CVars Init (Next n) vars (Inv n) (f n)
    (init_refines n) (fun s hs => init_inv hs) (step_inv n) (step_refines n)

/-! ## Consensus safety, transferred through the refinement -/

/-- Consensus agreement: at most one value is ever chosen (trivial in the
typed encoding — the type itself says "empty or singleton"). -/
@[simp] def CAgree : Tla.StatePred CSt :=
  [p| ∀ v : Value, ∀ w : Value, chosenC = some v → chosenC = some w → v = w]

theorem c_spec_entails_agree : CSpec ⊢ □ ⌜ CAgree ⌝ := by
  apply Tla.init_invariant_stut
  · intro s _hs
    tla_unfold
    intro v w hv hw
    exact Option.some.inj (hv.symm.trans hw)
  · intro s s' _hstep _hAgree
    tla_unfold
    intro v w hv hw
    exact Option.some.inj (hv.symm.trans hw)

/-- The safety property transfers through the refinement: in every Paxos
behavior, the mapped `chosen` is a single value at every point. -/
theorem voting_chosen_agree (n : Nat) : ∀ e : Tla.Behavior St, Spec n e →
    ∀ k : Nat, ∀ v w : Value, chosenVal n (e k) = some v → chosenVal n (e k) = some w → v = w := by
  intro e he k v w hv hw
  have hC : CSpec (Cslib.ωSequence.map (f n) e) := voting_refines_consensus n e he
  have hAg : CAgree (f n (e k)) := by
    simpa [Tla.statePred, Tla.always, Cslib.ωSequence.map, Cslib.ωSequence.drop,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_zero]
      using (c_spec_entails_agree (Cslib.ωSequence.map (f n) e) hC k)
  change ∀ v w : Value, chosenVal n (e k) = some v → chosenVal n (e k) = some w → v = w at hAg
  exact hAg v w hv hw

end TlaDsl.Examples.PaxosConsensus
