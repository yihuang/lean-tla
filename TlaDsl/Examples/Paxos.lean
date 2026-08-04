import TlaDsl.Basic
import TlaDsl.Notation
import TlaDsl.Coercion
import TlaDsl.Prime
import TlaDsl.Rules
import TlaDsl.Tactic
import TlaDsl.TlaVar

open scoped Tla

/-! # Single-decree Paxos: agreement safety

The classic Paxos safety argument, in the typed DSL. We port Lamport's
abstract **Voting** spec (`PaxosHowToWinATuringAward/Voting.tla`) — the
spec that the message-passing `Paxos.tla` refines — rather than the
message-passing algorithm itself. Two observations motivate this:

1. The safety proof needs the *history* of votes (`votes : Acceptor → Ballot
   → Option Value`). Keeping only each acceptor's latest vote
   (`maxVBal`/`maxVal`) loses the fact that a value was chosen at an earlier
   ballot once later votes overwrite the record, so the coherence argument
   cannot even be stated. The abstract spec keeps exactly the right state.
2. `Voting.tla` is where Lamport's "heart of the algorithm" lives as a
   single theorem (`ShowsSafety`): if a quorum's phase-1 reports show `v`
   safe at ballot `b`, then no other value was or ever will be chosen in a
   lower ballot. We prove that theorem, use it as the enabling condition of
   the vote action, and derive the canonical safety property — two different
   values can never both be chosen.

Quorums are concrete: more than half of the first `n` acceptors
(`Quorum n Q := Q ⊆ range n ∧ 2 * card Q > n`), so the quorum-intersection
property is proved rather than assumed. The DSL layer (`tla_var`,
`[p| ...]`, `[a| ...]`, `[t| ...]`) is used for the protocol; the semantic
predicates (`SafeAt`, `ShowsSafeAt`, ...) are plain definitions with the
state as their first argument so the bracket elaborator can lift them.
-/

namespace TlaDsl.Examples.Paxos

/-- Acceptor identities. -/
abbrev Acceptor := Nat

/-- Ballot numbers (natural numbers; `0` is the lowest ballot). -/
abbrev Ballot := Nat

/-- The values the algorithm may choose. -/
abbrev Value := String

/-- The algorithm state: the full vote history and the promise levels. -/
@[ext]
structure St where
  votes : Acceptor → Ballot → Option Value
  maxBal : Acceptor → Ballot

tla_var St votes maxBal

/-- Quorums: more than half of the first `n` acceptors. -/
def Quorum (n : Nat) (Q : Finset Acceptor) : Prop :=
  Q ⊆ Finset.range n ∧ 2 * Q.card > n

/-- Any two quorums intersect. -/
theorem quorum_overlap {n : Nat} {Q1 Q2 : Finset Acceptor}
    (h1 : Quorum n Q1) (h2 : Quorum n Q2) : ∃ a : Acceptor, a ∈ Q1 ∧ a ∈ Q2 := by
  rcases h1 with ⟨h1sub, h1maj⟩
  rcases h2 with ⟨h2sub, h2maj⟩
  by_contra h
  have hinter : (Q1 ∩ Q2).card = 0 := by
    rw [Finset.card_eq_zero]
    ext a
    constructor
    · intro ha
      exfalso
      exact h ⟨a, (Finset.mem_inter.mp ha).1, (Finset.mem_inter.mp ha).2⟩
    · intro ha
      simp at ha
  have hsum : (Q1 ∪ Q2).card = Q1.card + Q2.card := by
    have h := Finset.card_union_add_card_inter Q1 Q2
    omega
  have hle : (Q1 ∪ Q2).card ≤ n := by
    have hsub : Q1 ∪ Q2 ⊆ Finset.range n := Finset.union_subset h1sub h2sub
    simpa [Finset.card_range] using Finset.card_le_card hsub
  have hgt : n < Q1.card + Q2.card := by omega
  omega

/-- A quorum is nonempty (for `n` accepting the majority condition). -/
theorem quorum_nonempty {n : Nat} {Q : Finset Acceptor} (h : Quorum n Q) :
    ∃ a : Acceptor, a ∈ Q := by
  have hpos : 0 < Q.card := by
    apply Nat.pos_of_ne_zero
    intro hcard
    have : 2 * 0 > n := by simpa [hcard] using h.2
    omega
  rcases Finset.card_pos.mp hpos with ⟨a, ha⟩
  exact ⟨a, ha⟩

/-! ## The semantic vocabulary (Voting.tla) -/

/-- Acceptor `a` voted for value `v` in ballot `b`. -/
@[simp] def VotedFor (s : St) (a : Acceptor) (b : Ballot) (v : Value) : Prop :=
  s.votes a b = some v

/-- Acceptor `a` has not voted in ballot `b` and never will (its promise
exceeds `b`). -/
@[simp] def WontVoteAt (s : St) (a : Acceptor) (b : Ballot) : Prop :=
  s.maxBal a > b ∧ s.votes a b = none

/-- No value other than `v` has been or ever will be chosen at ballot `b`. -/
def NoneOtherChoosableAt (s : St) (n : Nat) (b : Ballot) (v : Value) : Prop :=
  ∃ Q : Finset Acceptor, Quorum n Q ∧
    ∀ a : Acceptor, a ∈ Q → VotedFor s a b v ∨ WontVoteAt s a b

/-- Value `v` is safe at ballot `b`: no other value was chosen in any
lower ballot. -/
def SafeAt (s : St) (n : Nat) (b : Ballot) (v : Value) : Prop :=
  ∀ c : Ballot, c < b → NoneOtherChoosableAt s n c v

/-- Quorum `Q` shows `v` safe at ballot `b` — the leader's local criterion:
every member has promised for `b` or higher, and the phase-1b reports from
`Q` (a vote for `v` at the highest reported ballot `c`, with no votes at
ballots between `c` and `b`) let the leader deduce `v` is safe. -/
def ShowsSafeAt (s : St) (Q : Finset Acceptor) (b : Ballot) (v : Value) : Prop :=
  (∀ a : Acceptor, a ∈ Q → s.maxBal a ≥ b) ∧
  ((∀ a : Acceptor, a ∈ Q → ∀ c : Ballot, c < b → s.votes a c = none) ∨
   ∃ c : Ballot, c < b ∧ (∃ a : Acceptor, a ∈ Q ∧ s.votes a c = some v) ∧
     (∀ a : Acceptor, a ∈ Q → ∀ d : Ballot, c < d → d < b → s.votes a d = none))

/-- Value `v` is chosen at ballot `b`: a quorum all voted for it there. -/
@[simp] def ChosenAt (s : St) (n : Nat) (b : Ballot) (v : Value) : Prop :=
  ∃ Q : Finset Acceptor, Quorum n Q ∧ ∀ a : Acceptor, a ∈ Q → s.votes a b = some v

/-! ## The protocol (in the DSL) -/

@[simp] def Init : Tla.StatePred St :=
  [p| (∀ a : Acceptor, ∀ b : Ballot, votes[a][b] = none) ∧
      (∀ a : Acceptor, maxBal[a] = 0)]

/-- The state after acceptor `a` promises ballot `b`. -/
def promise (s : St) (a : Acceptor) (b : Ballot) : St :=
  { s with maxBal := Function.update s.maxBal a b }

/-- The state after acceptor `a` votes for `v` in ballot `b`. -/
def vote (s : St) (a : Acceptor) (b : Ballot) (v : Value) : St :=
  { s with
    votes := Function.update s.votes a (Function.update (s.votes a) b (some v))
    maxBal := Function.update s.maxBal a b }

/-- Acceptor `a` raises its promise to ballot `b`. -/
@[simp] def IncreaseMaxBal (a : Acceptor) (b : Ballot) : Tla.Action St :=
  [a| b > maxBal[a] ∧ maxBal' = Function.update maxBal a b ∧ votes' = votes]

/-- Acceptor `a` votes for `v` in ballot `b`. The enabling conditions are
exactly `Voting.tla`'s `VoteFor`: the promise allows the ballot, `a` has not
already voted there, no one else voted for a different value in `b`, and a
quorum shows `v` safe at `b`. -/
@[simp] def VoteFor (n : Nat) (a : Acceptor) (b : Ballot) (v : Value) : Tla.Action St :=
  [a| maxBal[a] ≤ b ∧ votes[a][b] = none ∧
      (∀ c : Acceptor, ∀ w : Value, votes[c][b] = some w → w = v) ∧
      (∃ Q : Finset Acceptor, Quorum n Q ∧ ShowsSafeAt Q b v) ∧
      votes' = Function.update votes a (Function.update (votes a) b (some v)) ∧
      maxBal' = Function.update maxBal a b]

@[simp] def Next (n : Nat) : Tla.Action St :=
  [a| ∃ a : Acceptor, ∃ b : Ballot,
      IncreaseMaxBal a b ∨ ∃ v : Value, VoteFor n a b v]

/-! ## The inductive invariant (Voting.tla's `Inv`) -/

/-- Every ballot has at most one value: if two acceptors voted in ballot
`b`, they voted for the same value. -/
@[simp] def OneValuePerBallot : Tla.StatePred St :=
  [p| ∀ a1 : Acceptor, ∀ a2 : Acceptor, ∀ b : Ballot, ∀ v1 : Value, ∀ v2 : Value,
      votes[a1][b] = some v1 → votes[a2][b] = some v2 → v1 = v2]

/-- Every recorded vote is for a value safe at its ballot. -/
@[simp] def VotesSafe (n : Nat) : Tla.StatePred St :=
  [p| ∀ a : Acceptor, ∀ b : Ballot, ∀ v : Value, votes[a][b] = some v → SafeAt n b v]

@[simp] def Inv (n : Nat) : Tla.StatePred St :=
  fun s => OneValuePerBallot s ∧ VotesSafe n s

/-! ## Agreement -/

/-- No two different values are chosen. -/
@[simp] def Agree (n : Nat) : Tla.StatePred St :=
  [p| ∀ v : Value, ∀ w : Value,
      (∃ b : Ballot, ChosenAt n b v) → (∃ b' : Ballot, ChosenAt n b' w) → v = w]

def Spec (n : Nat) : Tla.Pred St := [t| Init ∧ □[Next n]_vars]

/-! ## The heart of the algorithm: `ShowsSafety` -/

/-- `NoneOtherChoosableAt` survives a vote in a higher ballot: no member of
the witnessing quorum can be the new voter. -/
lemma noneOther_vote {n : Nat} {s : St} {a : Acceptor} {b : Ballot} {v : Value}
    (hNoVote : s.votes a b = none) (hMax : s.maxBal a ≤ b)
    {c : Ballot} {w : Value} (h : NoneOtherChoosableAt s n c w) :
    NoneOtherChoosableAt (vote s a b v) n c w := by
  rcases h with ⟨Q, hQ, hQc⟩
  refine ⟨Q, hQ, ?_⟩
  intro a' ha'
  rcases hQc a' ha' with hv | hw
  · left
    by_cases hcb : c = b
    · subst c
      by_cases haa : a' = a
      · subst a'
        simp [hNoVote] at hv
      · simpa [vote, haa] using hv
    · by_cases haa : a' = a
      · subst a'
        simpa [vote, hcb] using hv
      · simpa [vote, haa] using hv
  · right
    rcases hw with ⟨hm, hnv⟩
    constructor
    · by_cases haa : a' = a
      · subst a'
        simp [vote]
        exact Nat.lt_of_lt_of_le hm hMax
      · simpa [vote, haa] using hm
    · by_cases hcb : c = b
      · subst c
        by_cases haa : a' = a
        · subst a'
          exfalso
          exact (not_lt_of_ge hMax) hm
        · simpa [vote, haa] using hnv
      · by_cases haa : a' = a
        · subst a'
          simpa [vote, hcb] using hnv
        · simpa [vote, haa] using hnv

/-- `NoneOtherChoosableAt` survives a promise: a higher promise only makes
`WontVoteAt` easier to satisfy. -/
lemma noneOther_promise {n : Nat} {s : St} {a : Acceptor} {b : Ballot}
    (hb : b > s.maxBal a) {c : Ballot} {w : Value} (h : NoneOtherChoosableAt s n c w) :
    NoneOtherChoosableAt (promise s a b) n c w := by
  rcases h with ⟨Q, hQ, hQc⟩
  refine ⟨Q, hQ, ?_⟩
  intro a' ha'
  rcases hQc a' ha' with hv | hw
  · left
    simpa [promise] using hv
  · right
    rcases hw with ⟨hm, hnv⟩
    constructor
    · by_cases haa : a' = a
      · subst a'
        simp [promise]
        exact Nat.lt_trans hm hb
      · simpa [promise, haa] using hm
    · simpa [promise] using hnv

/-- **The heart of the algorithm** (`Voting.tla`'s `ShowsSafety`): if a
quorum's reports show `v` safe at ballot `b`, then `v` really is safe at
`b` — provided the invariant holds. -/
theorem shows_safety {n : Nat} {s : St} {Q : Finset Acceptor} {b : Ballot} {v : Value}
    (hQ : Quorum n Q) (hInv : Inv n s) (hS : ShowsSafeAt s Q b v) : SafeAt s n b v := by
  rcases hS with ⟨hmax, hS2⟩
  intro c hc
  rcases hS2 with hNo | ⟨c0, hc0, hc0v, hc0n⟩
  · -- Nobody in Q has voted below b: Q itself witnesses safety at c.
    refine ⟨Q, hQ, ?_⟩
    intro a ha
    right
    constructor
    · exact lt_of_lt_of_le hc (hmax a ha)
    · exact hNo a ha c hc
  · by_cases hle : c ≤ c0
    · rcases lt_or_eq_of_le hle with hclt | hceq
      · -- c < c0: the vote for v at c0 is safe, so c is already covered.
        rcases hc0v with ⟨a0, ha0, hv0⟩
        exact hInv.2 a0 c0 v hv0 c hclt
      · -- c = c0: Q witnesses safety; one-value-per-ballot makes any other
        -- vote in c0 equal to v.
        subst c
        refine ⟨Q, hQ, ?_⟩
        intro a ha
        rcases hc0v with ⟨a0, ha0, hv0⟩
        cases hvc : s.votes a c0 with
        | none =>
            right
            constructor
            · exact lt_of_lt_of_le hc0 (hmax a ha)
            · exact hvc
        | some w =>
            left
            have heq : v = w := hInv.1 a0 a c0 v w hv0 hvc
            simpa [heq] using hvc
    · -- c > c0: nobody in Q voted in (c0, b), so everyone in Q cannot vote at c.
      refine ⟨Q, hQ, ?_⟩
      intro a ha
      right
      constructor
      · exact lt_of_lt_of_le hc (hmax a ha)
      · exact hc0n a ha c (Nat.lt_of_not_ge hle) hc

/-! ## The invariant is inductive -/

/-- A vote preserves one-value-per-ballot. -/
theorem oneValue_vote {n : Nat} {s : St} {a : Acceptor} {b : Ballot} {v : Value}
    (hOne : ∀ c : Acceptor, ∀ w : Value, s.votes c b = some w → w = v)
    (hInv : Inv n s) :
    OneValuePerBallot (vote s a b v) := by
  intro a1 a2 b1 v1 v2 hv1 hv2
  by_cases hb1 : b1 = b
  · subst b1
    have hv1' : v1 = v := by
      by_cases ha1 : a1 = a
      · subst a1
        exact (Option.some.inj (by simpa [vote] using hv1)).symm
      · have h : s.votes a1 b = some v1 := by simpa [vote, ha1] using hv1
        exact hOne a1 v1 h
    have hv2' : v2 = v := by
      by_cases ha2 : a2 = a
      · subst a2
        exact (Option.some.inj (by simpa [vote] using hv2)).symm
      · have h : s.votes a2 b = some v2 := by simpa [vote, ha2] using hv2
        exact hOne a2 v2 h
    simp [hv1', hv2']
  · have h1 : s.votes a1 b1 = some v1 := by
      by_cases ha1 : a1 = a
      · subst a1
        simpa [vote, hb1] using hv1
      · simpa [vote, ha1, hb1] using hv1
    have h2 : s.votes a2 b1 = some v2 := by
      by_cases ha2 : a2 = a
      · subst a2
        simpa [vote, hb1] using hv2
      · simpa [vote, ha2, hb1] using hv2
    exact hInv.1 a1 a2 b1 v1 v2 h1 h2

/-- A vote preserves vote-safety: the new vote is safe by `ShowsSafety`,
and every old vote stays safe because `NoneOtherChoosableAt` survives the
vote. -/
theorem votesSafe_vote {n : Nat} {s : St} {a : Acceptor} {b : Ballot} {v : Value}
    (hNoVote : s.votes a b = none) (hMax : s.maxBal a ≤ b)
    (hSafe : SafeAt s n b v) (hInv : Inv n s) :
    VotesSafe n (vote s a b v) := by
  intro a' b' v' hv'
  by_cases hnew : a' = a ∧ b' = b
  · rcases hnew with ⟨rfl, rfl⟩
    have hv'' : v' = v := (Option.some.inj (by simpa [vote] using hv')).symm
    subst v'
    intro c hc
    exact noneOther_vote hNoVote hMax (hSafe c hc)
  · have hsafe0 : SafeAt s n b' v' :=
      hInv.2 a' b' v' (by
        by_cases haa : a' = a
        · subst a'
          by_cases hbb : b' = b
          · exfalso
            exact hnew ⟨rfl, hbb⟩
          · simpa [vote, hbb] using hv'
        · simpa [vote, haa] using hv')
    intro c hc
    exact noneOther_vote hNoVote hMax (hsafe0 c hc)

theorem vote_inv {n : Nat} {s s' : St} {a : Acceptor} {b : Ballot} {v : Value}
    (hstep : VoteFor n a b v s s') (hInv : Inv n s) : Inv n s' := by
  tla_unfold
  rcases hstep with ⟨hMax, hNoVote, hOne, hShow, hVotes', hMaxBal'⟩
  have hs' : s' = vote s a b v := by
    ext <;> simp [vote, hVotes', hMaxBal']
  subst s'
  constructor
  · exact oneValue_vote hOne hInv
  · have hSafe : SafeAt s n b v := by
      rcases hShow with ⟨Q, hQ, hS⟩
      exact shows_safety hQ hInv hS
    exact votesSafe_vote hNoVote hMax hSafe hInv

theorem increase_inv {n : Nat} {s s' : St} {a : Acceptor} {b : Ballot}
    (hstep : IncreaseMaxBal a b s s') (hInv : Inv n s) : Inv n s' := by
  tla_unfold
  rcases hstep with ⟨hb, hMaxBal', hVotes'⟩
  have hs' : s' = promise s a b := by
    ext <;> simp [promise, hMaxBal', hVotes']
  subst s'
  constructor
  · simpa [promise] using hInv.1
  · intro a' b' v' hv'
    have hsafe0 : SafeAt s n b' v' :=
      hInv.2 a' b' v' (by simpa [promise] using hv')
    intro c hc
    exact noneOther_promise hb (hsafe0 c hc)

theorem init_inv {n : Nat} {s : St} (h : Init s) : Inv n s := by
  tla_unfold
  rcases h with ⟨hNoVotes, hMax0⟩
  constructor
  · intro a1 a2 b1 v1 v2 hv1 hv2
    simp [hNoVotes a1 b1] at hv1
  · intro a' b' v' hv'
    simp [hNoVotes a' b'] at hv'

theorem next_inv (n : Nat) : ∀ s s' : St, Next n s s' → Inv n s → Inv n s' := by
  intro s s' hstep hInv
  unfold Next at hstep
  rcases hstep with ⟨a, b, hstep⟩
  rcases hstep with hinc | ⟨v, hvot⟩
  · exact increase_inv hinc hInv
  · exact vote_inv hvot hInv

theorem stutter_inv (n : Nat) : ∀ s s' : St, vars s' = vars s → Inv n s → Inv n s' := by
  intro s s' hstut hInv
  tla_unfold
  cases hstut
  exact hInv

/-! ## Agreement -/

/-- The overlap argument: a value chosen at a lower ballot agrees with any
value chosen at a higher one. -/
lemma agree_lower {n : Nat} {s : St} {v w : Value} {b b' : Ballot}
    (hInv : Inv n s)
    (hv : ∃ Q : Finset Acceptor, Quorum n Q ∧ ∀ a : Acceptor, a ∈ Q → s.votes a b = some v)
    (hw : ∃ Q : Finset Acceptor, Quorum n Q ∧ ∀ a : Acceptor, a ∈ Q → s.votes a b' = some w)
    (hlt : b < b') : v = w := by
  rcases hv with ⟨Q, hQ, hQv⟩
  rcases hw with ⟨Q', hQ', hQ'w⟩
  rcases quorum_nonempty hQ' with ⟨a0, ha0⟩
  have hSafe : SafeAt s n b' w := hInv.2 a0 b' w (hQ'w a0 ha0)
  have hNOC : NoneOtherChoosableAt s n b w := hSafe b hlt
  rcases hNOC with ⟨Q'', hQ'', hQ''b⟩
  rcases quorum_overlap hQ hQ'' with ⟨a1, ha1, ha1''⟩
  have hvote1 : s.votes a1 b = some v := hQv a1 ha1
  rcases hQ''b a1 ha1'' with hv' | hw'
  · have hw'1 : s.votes a1 b = some w := by simpa using hv'
    exact (Option.some.inj (hw'1.symm.trans hvote1)).symm
  · rcases hw' with ⟨_, hnv⟩
    simp [hnv] at hvote1

/-- The invariant implies agreement. -/
theorem agree_of_inv (n : Nat) : ∀ s : St, Inv n s → Agree n s := by
  intro s hInv
  change ∀ v : Value, ∀ w : Value,
      (∃ b : Ballot, ChosenAt s n b v) → (∃ b' : Ballot, ChosenAt s n b' w) → v = w
  intro v w hv hw
  rcases hv with ⟨b, Q, hQ, hQv⟩
  rcases hw with ⟨b', Q', hQ', hQ'w⟩
  rcases lt_or_ge b b' with hlt | hge
  · exact agree_lower hInv ⟨Q, hQ, hQv⟩ ⟨Q', hQ', hQ'w⟩ hlt
  · rcases lt_or_eq_of_le hge with hlt' | heq
    · exact (agree_lower hInv ⟨Q', hQ', hQ'w⟩ ⟨Q, hQ, hQv⟩ hlt').symm
    · subst b'
      rcases quorum_overlap hQ hQ' with ⟨a0, ha0, ha0'⟩
      have h1 : s.votes a0 b = some v := hQv a0 ha0
      have h2 : s.votes a0 b = some w := hQ'w a0 ha0'
      exact Option.some.inj (h1.symm.trans h2)

/-! ## The safety theorems -/

theorem spec_entails_inv (n : Nat) :
    (Tla.tlaAnd (Tla.statePred Init) (Tla.stutAlways (Next n) vars)) ⊢ □ ⌜ Inv n ⌝ := by
  apply Tla.init_invariant_stut
  · intro s hs
    exact init_inv hs
  · intro s s' hstep hInv
    rcases hstep with hnext | hstut
    · exact next_inv n s s' hnext hInv
    · exact stutter_inv n s s' hstut hInv

/-- The canonical Paxos safety theorem: no two different values are ever
chosen. -/
theorem spec_entails_agree (n : Nat) :
    (Tla.tlaAnd (Tla.statePred Init) (Tla.stutAlways (Next n) vars)) ⊢ □ ⌜ Agree n ⌝ := by
  intro e he
  have hInv : Tla.always (Tla.statePred (Inv n)) e := spec_entails_inv n e he
  intro k
  have hk : Inv n ((e.drop k) 0) := hInv k
  exact agree_of_inv n ((e.drop k) 0) hk

end TlaDsl.Examples.Paxos
