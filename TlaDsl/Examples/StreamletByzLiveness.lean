import TlaDsl.Examples.StreamletByz
import TlaDsl.Examples.StreamletLiveness

open scoped Tla

open TlaDsl.Examples.Streamlet (Block)
open TlaDsl.Examples.Streamlet.Liveness (propose vote vote_votes_self vote_votes_of_ne
  propose_proposed_self propose_proposed_of_ne lt_of_le_pred vote_preserves_pred_bound
  ProposeAssumption ClockAssumption LeaderProposeAssumption le_self_add vars cur proposed votes)
open TlaDsl.Examples.StreamletByz (ByzOk QuorumByz quorum_overlap quorum_overlap_honest
  quorum_honest_member)

/-! # Streamlet liveness under Byzantine faults

The liveness half of the Byzantine case study (north-star M6 item b). The
honest model (`StreamletLiveness.lean`) proves that five consecutive
honest-leader epochs with on-time proposals and votes deliver a final
block; this file shows the same conclusion survives `f < n/3` Byzantine
nodes. The changes relative to the honest model:

* the **same state** as the honest liveness model (`Streamlet.Liveness.St`):
  `cur`, per-epoch `proposed`, and per-node `votes` — epoch numbers are the
  timestamps, so the whole timing-abstract proof structure is reused;
* **Byzantine quorums** of size `> 2n/3` with the honest-overlap facts from
  `StreamletByz.lean` — two quorums share an honest node, and every quorum
  *contains* an honest node (`quorum_honest_member`);
* the propose/vote actions carry **honest guards** — `L e ∉ Byz` for the
  leader of epoch `e`, `i ∉ Byz` for the voter — and the initial state
  leaves Byzantine nodes' votes arbitrary (unconstrained by the spec,
  exactly as in the safety model). The protocol invariants are therefore
  the **honest-restricted** ones: every *honest* vote carries its epoch, is
  for the epoch's unique proposal, is bounded by the current epoch, and
  extends a longest chain the voter had seen at the start of the epoch;
* every notarization argument picks an **honest voter** from the quorum,
  so the Byzantine-vote noise never enters the proof — Fact 3, the
  longest-chain bound, Lemma 5 and Theorem 6 go through verbatim with the
  honest voter doing the work the arbitrary voter did in the honest model;
* the temporal wrapper (`HByz`) is the honest-timing wrapper with the
  explicit leader schedule: `L e ∉ Byz` for every epoch, honest nodes vote
  before their epoch passes, and the clock advances.

**Theorem** (`liveness_spec_byz`): for `ByzOk n Byz` and `0 < e0`,
`HByz n Byz L ⊢ cur = e0 ↝ FinalSomeByz` — the Byzantine analogue of the
paper's Theorem 13 under an explicit honest leader schedule.
-/

namespace TlaDsl.Examples.StreamletByzLiveness

abbrev Node := TlaDsl.Examples.Streamlet.Liveness.Node
abbrev Epoch := TlaDsl.Examples.Streamlet.Liveness.Epoch
abbrev St := TlaDsl.Examples.Streamlet.Liveness.St

/-! ## Notarization with Byzantine quorums -/

/-- Block `b` is notarized by epoch `e`: a **Byzantine quorum** voted for
it in epochs `≤ e`. The state is the first argument so the bracket
elaborator lifts it. -/
def NotarizedBy (s : St) (n : Nat) (b : Block) (e : Epoch) : Prop :=
  ∃ Q : Finset Node, QuorumByz n Q ∧
    ∀ i : Node, i ∈ Q → ∃ e' : Epoch, e' ≤ e ∧ s.votes i e' = some b

/-- Block `b` is notarized at some time. -/
def Notarized (s : St) (n : Nat) (b : Block) : Prop :=
  ∃ e : Epoch, NotarizedBy s n b e

/-- The chain ending at `b` is notarized by epoch `e`. -/
def ChainNotarizedBy (s : St) (n : Nat) (b : Block) (e : Epoch) : Prop :=
  ∀ C : Block, C ∈ b.ancestors → C ≠ Block.genesis → NotarizedBy s n C e

/-- The chain ending at `b` is notarized at some time. -/
def ChainNotarized (s : St) (n : Nat) (b : Block) : Prop :=
  ∀ C : Block, C ∈ b.ancestors → C ≠ Block.genesis → Notarized s n C

theorem notarizedBy_mono {s : St} {n : Nat} {b : Block} {e e' : Epoch}
    (h : e ≤ e') : NotarizedBy s n b e → NotarizedBy s n b e' := by
  rintro ⟨Q, hQ, hv⟩
  refine ⟨Q, hQ, ?_⟩
  intro i hi
  rcases hv i hi with ⟨e0, he0, hv0⟩
  exact ⟨e0, le_trans he0 h, hv0⟩

theorem chainNotarizedBy_mono {s : St} {n : Nat} {b : Block} {e e' : Epoch}
    (h : e ≤ e') : ChainNotarizedBy s n b e → ChainNotarizedBy s n b e' := by
  intro hc C hmem hne
  exact notarizedBy_mono h (hc C hmem hne)

/-- Notarization facts bounded by `e` are unaffected by any change that
keeps the votes of epochs `≤ e` intact. -/
theorem notarizedBy_votes_eq {s s' : St} {n : Nat} {b : Block} {e : Epoch}
    (h : ∀ i : Node, ∀ e' : Epoch, e' ≤ e → s'.votes i e' = s.votes i e') :
    NotarizedBy s n b e ↔ NotarizedBy s' n b e := by
  constructor
  · rintro ⟨Q, hQ, hv⟩
    refine ⟨Q, hQ, ?_⟩
    intro i hi
    rcases hv i hi with ⟨e0, he0, hv0⟩
    refine ⟨e0, he0, ?_⟩
    rw [h i e0 he0]
    exact hv0
  · rintro ⟨Q, hQ, hv⟩
    refine ⟨Q, hQ, ?_⟩
    intro i hi
    rcases hv i hi with ⟨e0, he0, hv0⟩
    refine ⟨e0, he0, ?_⟩
    rw [← h i e0 he0]
    exact hv0

theorem chainNotarizedBy_votes_eq {s s' : St} {n : Nat} {b : Block} {e : Epoch}
    (h : ∀ i : Node, ∀ e' : Epoch, e' ≤ e → s'.votes i e' = s.votes i e') :
    ChainNotarizedBy s n b e ↔ ChainNotarizedBy s' n b e := by
  constructor
  · intro hc C hmem hne
    exact (notarizedBy_votes_eq h).1 (hc C hmem hne)
  · intro hc C hmem hne
    exact (notarizedBy_votes_eq h).2 (hc C hmem hne)

lemma notarizedBy_votes_same {s s' : St} {n : Nat} {b : Block} {e : Epoch}
    (h : s'.votes = s.votes) : NotarizedBy s n b e ↔ NotarizedBy s' n b e :=
  notarizedBy_votes_eq (fun i e' he' => by rw [h])

lemma chainNotarizedBy_votes_same {s s' : St} {n : Nat} {b : Block} {e : Epoch}
    (h : s'.votes = s.votes) : ChainNotarizedBy s n b e ↔ ChainNotarizedBy s' n b e :=
  chainNotarizedBy_votes_eq (fun i e' he' => by rw [h])

/-! ## The protocol (in the DSL) -/

/-- Initially: epoch 0, no proposals, and no honest votes — Byzantine nodes
may carry arbitrary pre-existing votes (they are unconstrained). -/
@[simp] def InitByz (Byz : Finset Node) : Tla.StatePred St :=
  [p| cur = 0 ∧ (∀ e : Epoch, proposed[e] = none) ∧
      (∀ i : Node, i ∉ Byz → ∀ e : Epoch, votes[i][e] = none)]

/-- The clock advances to the next epoch. -/
@[simp] def Advance : Tla.Action St :=
  [a| cur' = cur + 1 ∧ proposed' = proposed ∧ votes' = votes]

/-- The honest leader `L e` of epoch `e` proposes `b` at the start of the
epoch: `b` extends one of the longest chains notarized by the end of
`e-1`. -/
@[simp] def Propose (Byz : Finset Node) (L : Epoch → Node) (n : Nat)
    (e : Epoch) (b : Block) : Tla.Action St :=
  [a| L e ∉ Byz ∧ cur = e ∧ proposed[e] = none ∧ 0 < e ∧ b.epoch = e ∧
      ChainNotarizedBy n b.pred (e - 1) ∧
      (∀ C : Block, NotarizedBy n C (e - 1) → C.length ≤ b.pred.length) ∧
      proposed' = Function.update proposed e (some b) ∧ cur' = cur ∧ votes' = votes]

/-- An honest node `i` votes for the epoch-`e` proposal `b` during epoch
`e`, only if `b` extends a longest chain notarized by the end of `e-1`. -/
@[simp] def Vote (Byz : Finset Node) (n : Nat) (i : Node) (b : Block) : Tla.Action St :=
  [a| i ∉ Byz ∧ cur = b.epoch ∧ 0 < b.epoch ∧ proposed[b.epoch] = some b ∧
      votes[i][b.epoch] = none ∧
      ChainNotarizedBy n b.pred (b.epoch - 1) ∧
      (∀ C : Block, NotarizedBy n C (b.epoch - 1) → C.length ≤ b.pred.length) ∧
      votes' = Function.update votes i (Function.update (votes i) b.epoch (some b)) ∧
      proposed' = proposed ∧ cur' = cur]

@[simp] def Next (Byz : Finset Node) (L : Epoch → Node) (n : Nat) : Tla.Action St :=
  [a| Advance ∨
      ∃ e : Epoch, ∃ b : Block, Propose Byz L n e b ∨ ∃ i : Node, Vote Byz n i b]

def SpecByz (Byz : Finset Node) (L : Epoch → Node) (n : Nat) : Tla.Pred St :=
  [t| InitByz Byz ∧ □[Next Byz L n]_vars]

/-! ## The honest-restricted invariants -/

/-- Honest votes are for blocks whose epoch matches the voting epoch. -/
@[simp] def VotedEpochByz (Byz : Finset Node) (s : St) : Prop :=
  ∀ i : Node, i ∉ Byz → ∀ e : Epoch, ∀ b : Block,
    s.votes i e = some b → b.epoch = e

/-- Honest votes only happen in positive epochs. -/
@[simp] def VotedPosEpochByz (Byz : Finset Node) (s : St) : Prop :=
  ∀ i : Node, i ∉ Byz → ∀ e : Epoch, ∀ b : Block,
    s.votes i e = some b → 0 < e

/-- Honest votes are only for the unique proposal of the epoch. -/
@[simp] def VotedProposedByz (Byz : Finset Node) (s : St) : Prop :=
  ∀ i : Node, i ∉ Byz → ∀ e : Epoch, ∀ b : Block,
    s.votes i e = some b → s.proposed e = some b

/-- Honest votes happen no later than the current epoch. -/
@[simp] def VotedCurByz (Byz : Finset Node) (s : St) : Prop :=
  ∀ i : Node, i ∉ Byz → ∀ e : Epoch, ∀ b : Block,
    s.votes i e = some b → e ≤ s.cur

/-- An honest voter had seen the proposal's parent chain notarized by the
start of the epoch. -/
@[simp] def VotedSeenParentByz (n : Nat) (Byz : Finset Node) (s : St) : Prop :=
  ∀ i : Node, i ∉ Byz → ∀ e : Epoch, ∀ b : Block,
    s.votes i e = some b → ChainNotarizedBy s n b.pred (e - 1)

/-- An honest voter had seen nothing longer than the proposal's parent
chain by the start of the epoch. -/
@[simp] def VotedLongestByz (n : Nat) (Byz : Finset Node) (s : St) : Prop :=
  ∀ i : Node, i ∉ Byz → ∀ e : Epoch, ∀ b : Block,
    s.votes i e = some b →
    ∀ C : Block, NotarizedBy s n C (e - 1) → C.length ≤ b.pred.length

/-- **The honest longest-chain discipline**: an honest node's votes are
for blocks of non-decreasing length. -/
@[simp] def VoteLenMonoByz (Byz : Finset Node) (s : St) : Prop :=
  ∀ i : Node, i ∉ Byz → ∀ e1 e2 : Epoch, ∀ b1 b2 : Block,
    s.votes i e1 = some b1 → s.votes i e2 = some b2 → e1 < e2 → b1.length ≤ b2.length

/-- Proposals carry their own epoch. -/
@[simp] def ProposedEpoch (s : St) : Prop :=
  ∀ e : Epoch, ∀ b : Block, s.proposed e = some b → b.epoch = e

/-- Proposals happen in positive epochs. -/
@[simp] def ProposedPosEpoch (s : St) : Prop :=
  ∀ e : Epoch, ∀ b : Block, s.proposed e = some b → 0 < e

/-- Proposals happen no later than the current epoch. -/
@[simp] def ProposedCur (s : St) : Prop :=
  ∀ e : Epoch, ∀ b : Block, s.proposed e = some b → e ≤ s.cur

/-- A proposer had seen the parent chain notarized by the end of the
previous epoch. -/
@[simp] def ProposedSeenParent (n : Nat) (s : St) : Prop :=
  ∀ e : Epoch, ∀ b : Block,
    s.proposed e = some b → ChainNotarizedBy s n b.pred (e - 1)

/-- A proposer had seen nothing longer by the end of the previous epoch. -/
@[simp] def ProposedLongest (n : Nat) (s : St) : Prop :=
  ∀ e : Epoch, ∀ b : Block,
    s.proposed e = some b →
    ∀ C : Block, NotarizedBy s n C (e - 1) → C.length ≤ b.pred.length

/-- The conjunction of all protocol invariants, as a named structure so
proofs use `hInv.votedEpochByz`, `hInv.proposedLongest`, ... instead of
deep nested projections. The proposal invariants are unrestricted
(only honest leaders propose — the action guard); the vote invariants are
honest-restricted (Byzantine pre-votes may violate them). -/
structure InvByz (Byz : Finset Node) (n : Nat) (s : St) : Prop where
  votedEpochByz : VotedEpochByz Byz s
  votedPosEpochByz : VotedPosEpochByz Byz s
  votedProposedByz : VotedProposedByz Byz s
  votedCurByz : VotedCurByz Byz s
  votedSeenParentByz : VotedSeenParentByz n Byz s
  votedLongestByz : VotedLongestByz n Byz s
  voteLenMonoByz : VoteLenMonoByz Byz s
  proposedEpoch : ProposedEpoch s
  proposedPosEpoch : ProposedPosEpoch s
  proposedCur : ProposedCur s
  proposedSeenParent : ProposedSeenParent n s
  proposedLongest : ProposedLongest n s

/-! ## The invariants are inductive -/

theorem votedEpochByz_vote {n : Nat} {Byz : Finset Node} {s : St} {i : Node} {b : Block}
    (hInv : InvByz Byz n s) : VotedEpochByz Byz (vote s i b) := by
  intro j hj e' b' hv'
  by_cases hje : j = i ∧ e' = b.epoch
  · tla_rcases_subst hje
    have hb' : b' = b := (Option.some.inj (by simpa [vote, Function.update] using hv')).symm
    subst b'
    rfl
  · have hv'' : s.votes j e' = some b' := vote_votes_of_ne (not_and_or.mp hje) ▸ hv'
    exact hInv.votedEpochByz j hj e' b' hv''

theorem votedPosEpochByz_vote {n : Nat} {Byz : Finset Node} {s : St} {i : Node} {b : Block}
    (hpos : 0 < b.epoch) (hInv : InvByz Byz n s) :
    VotedPosEpochByz Byz (vote s i b) := by
  intro j hj e' b' hv'
  by_cases hje : j = i ∧ e' = b.epoch
  · tla_rcases_subst hje
    have hb' : b' = b := (Option.some.inj (by simpa [vote, Function.update] using hv')).symm
    subst b'
    exact hpos
  · have hv'' : s.votes j e' = some b' := vote_votes_of_ne (not_and_or.mp hje) ▸ hv'
    exact hInv.votedPosEpochByz j hj e' b' hv''

theorem votedProposedByz_vote {n : Nat} {Byz : Finset Node} {s : St} {i : Node} {b : Block}
    (hProp : s.proposed b.epoch = some b) (hInv : InvByz Byz n s) :
    VotedProposedByz Byz (vote s i b) := by
  intro j hj e' b' hv'
  by_cases hje : j = i ∧ e' = b.epoch
  · tla_rcases_subst hje
    have hb' : b' = b := (Option.some.inj (by simpa [vote, Function.update] using hv')).symm
    subst b'
    exact hProp
  · have hv'' : s.votes j e' = some b' := vote_votes_of_ne (not_and_or.mp hje) ▸ hv'
    exact hInv.votedProposedByz j hj e' b' hv''

theorem votedCurByz_vote {n : Nat} {Byz : Finset Node} {s : St} {i : Node} {b : Block}
    (hcur : s.cur = b.epoch) (hInv : InvByz Byz n s) :
    VotedCurByz Byz (vote s i b) := by
  intro j hj e' b' hv'
  by_cases hje : j = i ∧ e' = b.epoch
  · tla_rcases_subst hje
    have hb' : b' = b := (Option.some.inj (by simpa [vote, Function.update] using hv')).symm
    subst b'
    simpa [vote] using (le_of_eq hcur.symm)
  · have hv'' : s.votes j e' = some b' := vote_votes_of_ne (not_and_or.mp hje) ▸ hv'
    exact hInv.votedCurByz j hj e' b' hv''

theorem votedSeenParentByz_vote {n : Nat} {Byz : Finset Node} {s : St} {i : Node} {b : Block}
    (hSeen : ChainNotarizedBy s n b.pred (b.epoch - 1))
    (hpos : 0 < b.epoch) (hcur : s.cur = b.epoch) (hInv : InvByz Byz n s) :
    VotedSeenParentByz n Byz (vote s i b) := by
  intro j hj e' b' hv'
  by_cases hje : j = i ∧ e' = b.epoch
  · tla_rcases_subst hje
    have hb' : b' = b := (Option.some.inj (by simpa [vote, Function.update] using hv')).symm
    subst b'
    have hpres : ∀ k : Node, ∀ e0 : Epoch, e0 ≤ b.epoch - 1 →
        (vote s i b).votes k e0 = s.votes k e0 := by
      intro k e0 he0
      exact vote_votes_of_ne (Or.inr (ne_of_lt (lt_of_le_pred hpos he0)))
    exact (chainNotarizedBy_votes_eq hpres).1 hSeen
  · have hv'' : s.votes j e' = some b' := vote_votes_of_ne (not_and_or.mp hje) ▸ hv'
    have hc : ChainNotarizedBy s n b'.pred (e' - 1) := hInv.votedSeenParentByz j hj e' b' hv''
    have hle : e' ≤ b.epoch := by
      simpa [hcur] using (hInv.votedCurByz j hj e' b' hv'')
    have hpres : ∀ k : Node, ∀ e0 : Epoch, e0 ≤ e' - 1 →
        (vote s i b).votes k e0 = s.votes k e0 := by
      intro k e0 he0
      have hle0 : e0 ≤ b.epoch - 1 := le_trans he0 (Nat.sub_le_sub_right hle 1)
      exact vote_votes_of_ne (Or.inr (ne_of_lt (lt_of_le_pred hpos hle0)))
    exact (chainNotarizedBy_votes_eq hpres).1 hc

theorem votedLongestByz_vote {n : Nat} {Byz : Finset Node} {s : St} {i : Node} {b : Block}
    (hLongest : ∀ C : Block, NotarizedBy s n C (b.epoch - 1) → C.length ≤ b.pred.length)
    (hpos : 0 < b.epoch) (hcur : s.cur = b.epoch) (hInv : InvByz Byz n s) :
    VotedLongestByz n Byz (vote s i b) := by
  intro j hj e' b' hv' C hC
  by_cases hje : j = i ∧ e' = b.epoch
  · tla_rcases_subst hje
    have hb' : b' = b := (Option.some.inj (by simpa [vote, Function.update] using hv')).symm
    subst b'
    have hpres : ∀ k : Node, ∀ e0 : Epoch, e0 ≤ b.epoch - 1 →
        (vote s i b).votes k e0 = s.votes k e0 := by
      intro k e0 he0
      exact vote_votes_of_ne (Or.inr (ne_of_lt (lt_of_le_pred hpos he0)))
    exact hLongest C ((notarizedBy_votes_eq hpres).2 hC)
  · have hv'' : s.votes j e' = some b' := vote_votes_of_ne (not_and_or.mp hje) ▸ hv'
    have hle : e' ≤ b.epoch := by
      simpa [hcur] using (hInv.votedCurByz j hj e' b' hv'')
    have hpres : ∀ k : Node, ∀ e0 : Epoch, e0 ≤ e' - 1 →
        (vote s i b).votes k e0 = s.votes k e0 := by
      intro k e0 he0
      have hle0 : e0 ≤ b.epoch - 1 := le_trans he0 (Nat.sub_le_sub_right hle 1)
      exact vote_votes_of_ne (Or.inr (ne_of_lt (lt_of_le_pred hpos hle0)))
    have hC' : NotarizedBy s n C (e' - 1) :=
      (notarizedBy_votes_eq hpres).2 hC
    exact hInv.votedLongestByz j hj e' b' hv'' C hC'

theorem voteLenMonoByz_vote {n : Nat} {Byz : Finset Node} {s : St} {i : Node} {b : Block}
    (hi : i ∉ Byz) (hbne : b ≠ Block.genesis)
    (hLongest : ∀ C : Block, NotarizedBy s n C (b.epoch - 1) → C.length ≤ b.pred.length)
    (hcur : s.cur = b.epoch) (hInv : InvByz Byz n s) : VoteLenMonoByz Byz (vote s i b) := by
  intro j hj e1 e2 b1 b2 hv1 hv2 hlt
  by_cases he2 : e2 = b.epoch
  · subst e2
    by_cases hji : j = i
    · subst j
      have hb2 : b2 = b := (Option.some.inj (by simpa [vote, Function.update] using hv2)).symm
      subst b2
      have hne1 : e1 ≠ b.epoch := ne_of_lt hlt
      have hv1' : s.votes i e1 = some b1 := vote_votes_of_ne (Or.inr hne1) ▸ hv1
      have hb1ne : b1 ≠ Block.genesis :=
        Block.epoch_pos_ne_genesis (by
          have h0 : 0 < e1 := hInv.votedPosEpochByz i hi e1 b1 hv1'
          have he : b1.epoch = e1 := hInv.votedEpochByz i hi e1 b1 hv1'
          simpa [he] using h0)
      have hlen : b1.length ≤ b.length := by
        by_cases hg : b1.pred = Block.genesis
        · have hb1len : b1.length = b1.pred.length + 1 := Block.pred_length hb1ne
          have hblen : b.length = b.pred.length + 1 := Block.pred_length hbne
          simp [hg] at hb1len
          omega
        · have hc : ChainNotarizedBy s n b1.pred (e1 - 1) := hInv.votedSeenParentByz i hi e1 b1 hv1'
          have hN : NotarizedBy s n b1.pred (e1 - 1) :=
            hc b1.pred (Block.mem_ancestors_self b1.pred) hg
          have hN' : NotarizedBy s n b1.pred (b.epoch - 1) :=
            notarizedBy_mono (Nat.sub_le_sub_right (le_of_lt hlt) 1) hN
          have hle : b1.pred.length ≤ b.pred.length := hLongest b1.pred hN'
          have hb1len : b1.length = b1.pred.length + 1 := Block.pred_length hb1ne
          have hblen : b.length = b.pred.length + 1 := Block.pred_length hbne
          omega
      exact hlen
    · have hv1' : s.votes j e1 = some b1 := vote_votes_of_ne (Or.inl hji) ▸ hv1
      have hv2' : s.votes j b.epoch = some b2 := vote_votes_of_ne (Or.inl hji) ▸ hv2
      exact hInv.voteLenMonoByz j hj e1 b.epoch b1 b2 hv1' hv2' hlt
  · by_cases he1 : e1 = b.epoch
    · subst e1
      by_cases hji : j = i
      · subst j
        have hb1 : b1 = b := (Option.some.inj (by simpa [vote, Function.update] using hv1)).symm
        subst b1
        have hv2' : s.votes i e2 = some b2 := vote_votes_of_ne (Or.inr (by omega)) ▸ hv2
        have hle2 : e2 ≤ b.epoch := by
          simpa [hcur] using (hInv.votedCurByz i hi e2 b2 hv2')
        exact (not_le_of_gt hlt hle2).elim
      · have hv1' : s.votes j b.epoch = some b1 := vote_votes_of_ne (Or.inl hji) ▸ hv1
        have hv2' : s.votes j e2 = some b2 := vote_votes_of_ne (Or.inl hji) ▸ hv2
        exact hInv.voteLenMonoByz j hj b.epoch e2 b1 b2 hv1' hv2' hlt
    · have hv1' : s.votes j e1 = some b1 := vote_votes_of_ne (Or.inr he1) ▸ hv1
      have hv2' : s.votes j e2 = some b2 := vote_votes_of_ne (Or.inr he2) ▸ hv2
      exact hInv.voteLenMonoByz j hj e1 e2 b1 b2 hv1' hv2' hlt

theorem vote_inv_byz {n : Nat} {Byz : Finset Node} {s s' : St} {i : Node} {b : Block}
    (hstep : Vote Byz n i b s s') (hInv : InvByz Byz n s) : InvByz Byz n s' := by
  tla_unfold
  rcases hstep with ⟨hi, hcur, hpos, hProp, hNoVote, hSeen, hLongest, hVotes', hProp', hCur'⟩
  have hs' : s' = vote s i b := by
    ext <;> simp [vote, hVotes', hProp', hCur']
  subst s'
  tla_inv_step
  · -- VoteLenMonoByz: votes changed; the dedicated lemma needs the
    -- non-genesis fact derived from `hpos`
    exact voteLenMonoByz_vote hi (Block.epoch_pos_ne_genesis hpos) hLongest hcur hInv
  · -- ProposedSeenParent: votes changed, so the chain lookup needs the
    -- votes-preservation rewrite
    intro e0 b0 hv0
    have hv0' : s.proposed e0 = some b0 := by simpa [vote] using hv0
    have hc : ChainNotarizedBy s n b0.pred (e0 - 1) := hInv.proposedSeenParent e0 b0 hv0'
    have hle : e0 ≤ b.epoch := by simpa [hcur] using (hInv.proposedCur e0 b0 hv0')
    exact (chainNotarizedBy_votes_eq
      (vote_preserves_pred_bound hpos hle)).1 hc
  · -- ProposedLongest
    intro e0 b0 hv0 C hC
    have hv0' : s.proposed e0 = some b0 := by simpa [vote] using hv0
    have hle : e0 ≤ b.epoch := by simpa [hcur] using (hInv.proposedCur e0 b0 hv0')
    have hC' : NotarizedBy s n C (e0 - 1) :=
      (notarizedBy_votes_eq (vote_preserves_pred_bound hpos hle)).2 hC
    exact hInv.proposedLongest e0 b0 hv0' C hC'

theorem propose_inv_byz {n : Nat} {Byz : Finset Node} {L : Epoch → Node} {s s' : St}
    {e : Epoch} {b : Block}
    (hstep : Propose Byz L n e b s s') (hInv : InvByz Byz n s) : InvByz Byz n s' := by
  tla_unfold
  rcases hstep with ⟨hLeader, hcur, hNone, hpos, hbE, hSeen, hLongest, hProp', hCur', hVotes'⟩
  have hs' : s' = propose s e b := by
    ext <;> simp [propose, hProp', hCur', hVotes']
  subst s'
  tla_inv_step
  · -- VotedProposedByz: a vote for the new epoch-e proposal
    intro i hi e0 b0 hv0
    have hv0' : s.votes i e0 = some b0 := by simpa [propose] using hv0
    have hp0 : s.proposed e0 = some b0 := hInv.votedProposedByz i hi e0 b0 hv0'
    have hne : e0 ≠ e := by
      intro he
      subst e0
      rw [hp0] at hNone
      cases hNone
    exact (propose_proposed_of_ne (s := s) (e := e) (e0 := e0) (b := b) hne) ▸ hp0
  · -- ProposedEpoch
    intro e0 b0 hv0
    by_cases he0 : e0 = e
    · subst e0
      have hb0 : b0 = b := (Option.some.inj (by simpa [propose, Function.update] using hv0)).symm
      subst b0
      exact hbE
    · have hv0' : s.proposed e0 = some b0 := by
        simpa [propose, Function.update, he0] using hv0
      exact hInv.proposedEpoch e0 b0 hv0'
  · -- ProposedPosEpoch
    intro e0 b0 hv0
    by_cases he0 : e0 = e
    · subst e0
      have hb0 : b0 = b := (Option.some.inj (by simpa [propose, Function.update] using hv0)).symm
      subst b0
      exact hpos
    · have hv0' : s.proposed e0 = some b0 := by
        simpa [propose, Function.update, he0] using hv0
      exact hInv.proposedPosEpoch e0 b0 hv0'
  · -- ProposedCur
    intro e0 b0 hv0
    by_cases he0 : e0 = e
    · subst e0
      have hb0 : b0 = b := (Option.some.inj (by simpa [propose, Function.update] using hv0)).symm
      subst b0
      simpa [propose] using (le_of_eq hcur.symm)
    · have hv0' : s.proposed e0 = some b0 := by
        simpa [propose, Function.update, he0] using hv0
      exact hInv.proposedCur e0 b0 hv0'
  · -- ProposedSeenParent
    intro e0 b0 hv0
    by_cases he0 : e0 = e
    · subst e0
      have hb0 : b0 = b := (Option.some.inj (by simpa [propose, Function.update] using hv0)).symm
      subst b0
      exact hSeen
    · have hv0' : s.proposed e0 = some b0 := by
        simpa [propose, Function.update, he0] using hv0
      exact (chainNotarizedBy_votes_same (by rfl : (propose s e b).votes = s.votes)).1
        (hInv.proposedSeenParent e0 b0 hv0')
  · -- ProposedLongest
    intro e0 b0 hv0 C hC
    by_cases he0 : e0 = e
    · subst e0
      have hb0 : b0 = b := (Option.some.inj (by simpa [propose, Function.update] using hv0)).symm
      subst b0
      exact hLongest C hC
    · have hv0' : s.proposed e0 = some b0 := by
        simpa [propose, Function.update, he0] using hv0
      have hC' : NotarizedBy s n C (e0 - 1) :=
        (notarizedBy_votes_same (by rfl : (propose s e b).votes = s.votes)).2 hC
      exact hInv.proposedLongest e0 b0 hv0' C hC'

theorem advance_inv_byz {n : Nat} {Byz : Finset Node} {s s' : St}
    (hstep : Advance s s') (hInv : InvByz Byz n s) : InvByz Byz n s' := by
  tla_unfold
  rcases hstep with ⟨hCur', hProp', hVotes'⟩
  have hs' : s' = { s with cur := s.cur + 1 } := by
    ext <;> simp [hCur', hProp', hVotes']
  subst s'
  tla_inv_step
  · -- VotedCurByz: the clock advanced, so `e0 ≤ cur` needs the step
    intro i hi e0 b0 hv0
    have h1 : e0 ≤ s.cur := hInv.votedCurByz i hi e0 b0 (by simpa [hVotes'] using hv0)
    simpa using (le_trans h1 (Nat.le_succ s.cur))
  · -- ProposedCur
    intro e0 b0 hv0
    have h1 : e0 ≤ s.cur := hInv.proposedCur e0 b0 (by simpa [hProp'] using hv0)
    simpa using (le_trans h1 (Nat.le_succ s.cur))

theorem init_inv_byz {n : Nat} {Byz : Finset Node} {s : St} (h : InitByz Byz s) :
    InvByz Byz n s := by
  tla_unfold
  rcases h with ⟨hCur0, hNoProp, hNoVotes⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi e0 b0 hv0
    rw [hNoVotes i hi e0] at hv0
    cases hv0
  · intro i hi e0 b0 hv0
    rw [hNoVotes i hi e0] at hv0
    cases hv0
  · intro i hi e0 b0 hv0
    rw [hNoVotes i hi e0] at hv0
    cases hv0
  · intro i hi e0 b0 hv0
    rw [hNoVotes i hi e0] at hv0
    cases hv0
  · intro i hi e0 b0 hv0
    rw [hNoVotes i hi e0] at hv0
    cases hv0
  · intro i hi e0 b0 hv0
    rw [hNoVotes i hi e0] at hv0
    cases hv0
  · intro i hi e1 e2 b1 b2 hv1 hv2 hlt
    rw [hNoVotes i hi e1] at hv1
    cases hv1
  · intro e0 b0 hv0
    rw [hNoProp e0] at hv0
    cases hv0
  · intro e0 b0 hv0
    rw [hNoProp e0] at hv0
    cases hv0
  · intro e0 b0 hv0
    rw [hNoProp e0] at hv0
    cases hv0
  · intro e0 b0 hv0
    rw [hNoProp e0] at hv0
    cases hv0
  · intro e0 b0 hv0
    rw [hNoProp e0] at hv0
    cases hv0

theorem next_inv_byz (Byz : Finset Node) (L : Epoch → Node) (n : Nat) :
    ∀ s s' : St, Next Byz L n s s' → InvByz Byz n s → InvByz Byz n s' := by
  intro s s' hstep hInv
  unfold Next at hstep
  rcases hstep with hadv | ⟨e, b, hstep⟩
  · exact advance_inv_byz hadv hInv
  · rcases hstep with hp | ⟨i, hv⟩
    · exact propose_inv_byz hp hInv
    · exact vote_inv_byz hv hInv

theorem stutter_inv_byz (Byz : Finset Node) (_L : Epoch → Node) (n : Nat) :
    ∀ s s' : St, vars s' = vars s → InvByz Byz n s → InvByz Byz n s' := by
  intro s s' hstut hInv
  tla_unfold
  have hs' : s' = s := by simpa using hstut
  subst s'
  exact hInv

/-- Every reachable state satisfies the invariants. -/
theorem spec_entails_inv_byz (Byz : Finset Node) (L : Epoch → Node) (n : Nat) :
    (Tla.tlaAnd (Tla.statePred (InitByz Byz)) (Tla.stutAlways (Next Byz L n) vars)) ⊢
      □ ⌜ InvByz Byz n ⌝ := by
  apply Tla.init_invariant_stut
  · intro s hs
    exact init_inv_byz hs
  · intro s s' hstep hInv
    rcases hstep with hnext | hstut
    · exact next_inv_byz Byz L n s s' hnext hInv
    · exact stutter_inv_byz Byz L n s s' hstut hInv

/-! ## Safety for the extended model -/

/-- A notarized block has an **honest** voter, and that voter's vote is
recorded in the block's own epoch (honest votes carry their epoch). This
is the Byzantine replacement for "pick any voter from the quorum": the
quorum's Byzantine members may have voted arbitrarily, so only the honest
one can be interrogated. -/
lemma notarized_honest_vote {n : Nat} {Byz : Finset Node} (hByz : ByzOk n Byz)
    {s : St} (hInv : InvByz Byz n s) {b : Block} (hN : Notarized s n b) :
    ∃ i : Node, i ∉ Byz ∧ s.votes i b.epoch = some b := by
  rcases hN with ⟨e, ⟨Q, hQ, hv⟩⟩
  rcases quorum_honest_member hByz hQ with ⟨i, hi, hiQ⟩
  rcases hv i hiQ with ⟨e0, he0, hv0⟩
  have hbE : b.epoch = e0 := hInv.votedEpochByz i hi e0 b hv0
  rw [← hbE] at hv0
  exact ⟨i, hi, hv0⟩

/-- **Lemma 10 (Byzantine)**: at most one notarized block per epoch — two
notarized blocks of the same epoch share an **honest** voter, and an honest
node votes at most once per epoch. -/
theorem unique_notarization_byz {n : Nat} {Byz : Finset Node} (hByz : ByzOk n Byz)
    {s : St} (hInv : InvByz Byz n s) {b b' : Block}
    (hN : Notarized s n b) (hN' : Notarized s n b') (hE : b.epoch = b'.epoch) : b = b' := by
  rcases hN with ⟨e, ⟨Q, hQ, hv⟩⟩
  rcases hN' with ⟨e', ⟨Q', hQ', hv'⟩⟩
  rcases quorum_overlap_honest hByz hQ hQ' with ⟨i, hi, hiQ, hiQ'⟩
  rcases hv i hiQ with ⟨e0, he0, hv0⟩
  rcases hv' i hiQ' with ⟨e0', he0', hv0'⟩
  have hbE : b.epoch = e0 := hInv.votedEpochByz i hi e0 b hv0
  have hbE' : b'.epoch = e0' := hInv.votedEpochByz i hi e0' b' hv0'
  have h1 : s.votes i b.epoch = some b := by
    rw [← hbE] at hv0
    exact hv0
  have h2 : s.votes i b'.epoch = some b' := by
    rw [← hbE'] at hv0'
    exact hv0'
  rw [← hE] at h2
  exact Option.some.inj (h1.symm.trans h2)

/-! ## Liveness structure: Fact 3, Lemma 5, Theorem 6 -/

/-- A proposal carries its epoch, hence is non-genesis. -/
lemma proposal_ne_genesis_of {n : Nat} {Byz : Finset Node} {s : St} (hInv : InvByz Byz n s)
    {e : Epoch} {b : Block} (hp : s.proposed e = some b) (hpos : 0 < e) :
    b ≠ Block.genesis :=
  Block.epoch_pos_ne_genesis (by
    have he : b.epoch = e := hInv.proposedEpoch e b hp
    simpa [he] using hpos)

/-- The proposal of `e+1` is non-genesis. -/
lemma proposal_succ_ne_genesis {n : Nat} {Byz : Finset Node} {s : St} (hInv : InvByz Byz n s)
    {e : Epoch} {b : Block} (hp : s.proposed (e + 1) = some b) : b ≠ Block.genesis :=
  proposal_ne_genesis_of hInv hp (Nat.succ_pos e)

/-- **Fact 3 (Byzantine)**: if a chain of length `≥ ℓ` was notarized by the
time the next epoch's leader proposed, the next proposal is strictly longer
than `ℓ`. -/
theorem proposal_growth {n : Nat} {Byz : Finset Node} {s : St} (hInv : InvByz Byz n s)
    {e : Epoch} {b0 b1 : Block}
    (_hp0 : s.proposed e = some b0) (hp1 : s.proposed (e + 1) = some b1)
    (hseen : ∃ C : Block, NotarizedBy s n C e ∧ b0.length ≤ C.length) :
    b0.length < b1.length := by
  rcases hseen with ⟨C, hC, hlen⟩
  have hle : C.length ≤ b1.pred.length := hInv.proposedLongest (e + 1) b1 hp1 C hC
  have hb1ne : b1 ≠ Block.genesis := proposal_succ_ne_genesis hInv hp1
  have hb1len : b1.length = b1.pred.length + 1 := Block.pred_length hb1ne
  omega

/-- No block longer than the third proposal is notarized by `e+2`: any such
block would be the proposal of its own epoch (an **honest** voter in its
quorum votes only for proposals), so it is one of `b0, b1, b2` (too short)
or was voted for before epoch `e` (contradicting the growth against `b1`).
The Byzantine members of the quorum may have voted for anything; the
honest voter makes the argument go through unchanged. -/
theorem longest_chain_by {n : Nat} {Byz : Finset Node} (hByz : ByzOk n Byz)
    {s : St} (hInv : InvByz Byz n s)
    {e : Epoch} {b0 b1 b2 : Block}
    (hp0 : s.proposed e = some b0) (hp1 : s.proposed (e + 1) = some b1)
    (hp2 : s.proposed (e + 2) = some b2)
    (hG01 : b0.length < b1.length) (hG12 : b1.length < b2.length)
    (_hC2 : ChainNotarizedBy s n b2 (e + 2)) :
    ∀ C : Block, NotarizedBy s n C (e + 2) → C.length ≤ b2.length := by
  intro C hC
  rcases hC with ⟨Q, hQ, hv⟩
  rcases quorum_honest_member hByz hQ with ⟨i0, hi0, hi0Q⟩
  rcases hv i0 hi0Q with ⟨e0, he0, hv0⟩
  have hCE : C.epoch = e0 := hInv.votedEpochByz i0 hi0 e0 C hv0
  have hCP : s.proposed e0 = some C := hInv.votedProposedByz i0 hi0 e0 C hv0
  have hb1ne : b1 ≠ Block.genesis := proposal_succ_ne_genesis hInv hp1
  have hb2ne : b2 ≠ Block.genesis :=
    proposal_ne_genesis_of hInv hp2 (Nat.succ_pos (e + 1))
  by_cases h1 : C.epoch = e
  · have he0' : e0 = e := by rw [← hCE, h1]
    have hCb : s.proposed e = some C := by rw [he0'] at hCP; exact hCP
    have hC0 : C = b0 := Option.some.inj (hCb.symm.trans hp0)
    subst C
    omega
  · by_cases h2 : C.epoch = e + 1
    · have he0' : e0 = e + 1 := by rw [← hCE, h2]
      have hCb : s.proposed (e + 1) = some C := by rw [he0'] at hCP; exact hCP
      have hC1 : C = b1 := Option.some.inj (hCb.symm.trans hp1)
      subst C
      omega
    · by_cases h3 : C.epoch = e + 2
      · have he0' : e0 = e + 2 := by rw [← hCE, h3]
        have hCb : s.proposed (e + 2) = some C := by rw [he0'] at hCP; exact hCP
        have hC2' : C = b2 := Option.some.inj (hCb.symm.trans hp2)
        subst C
        rfl
      · have hleC : C.epoch ≤ e + 2 := by rw [hCE]; exact he0
        have hlt : C.epoch < e := by
          by_cases hle : C.epoch ≤ e
          · exact lt_of_le_of_ne hle h1
          · have hge : e + 1 ≤ C.epoch := Nat.succ_le_of_lt (lt_of_not_ge hle)
            have hcase : C.epoch = e + 1 ∨ C.epoch = e + 2 := by omega
            rcases hcase with hc1 | hc2
            · exact (h2 hc1).elim
            · exact (h3 hc2).elim
        by_cases hg : C = Block.genesis
        · subst C
          simp
        · have hCp : ChainNotarizedBy s n C.pred (C.epoch - 1) :=
            by simpa [hCE] using (hInv.votedSeenParentByz i0 hi0 e0 C hv0)
          have hlenP : C.pred.length ≤ b1.pred.length := by
            by_cases hgp : C.pred = Block.genesis
            · simp [hgp]
            · have hN : NotarizedBy s n C.pred (C.epoch - 1) :=
                hCp C.pred (Block.mem_ancestors_self C.pred) hgp
              have hN' : NotarizedBy s n C.pred e :=
                notarizedBy_mono (Nat.le_trans (Nat.sub_le C.epoch 1) (le_of_lt hlt)) hN
              exact hInv.proposedLongest (e + 1) b1 hp1 C.pred hN'
          have hClen' : C.length = C.pred.length + 1 := Block.pred_length hg
          have hb1len : b1.length = b1.pred.length + 1 := Block.pred_length hb1ne
          have hb2len : b2.length = b2.pred.length + 1 := Block.pred_length hb2ne
          have hCleq : C.length ≤ b1.length := by omega
          omega

/-- **Lemma 5(b) (Byzantine)**: three consecutive proposals with strictly
growing lengths and the third's chain notarized on time — no conflicting
block at the third's length is ever notarized. -/
theorem main_liveness_lemma {n : Nat} {Byz : Finset Node} (hByz : ByzOk n Byz)
    {s : St} (hInv : InvByz Byz n s)
    {e : Epoch} {b0 b1 b2 : Block}
    (hp0 : s.proposed e = some b0) (hp1 : s.proposed (e + 1) = some b1)
    (hp2 : s.proposed (e + 2) = some b2)
    (hG01 : b0.length < b1.length) (hG12 : b1.length < b2.length)
    (hC2 : ChainNotarizedBy s n b2 (e + 2)) :
    ∀ C : Block, C ≠ b2 → C.length = b2.length → ¬ Notarized s n C := by
  intro C hCne hClen hNC
  rcases hNC with ⟨eC, ⟨Q, hQ, hv⟩⟩
  rcases quorum_honest_member hByz hQ with ⟨i0, hi0, hi0Q⟩
  rcases hv i0 hi0Q with ⟨e0, he0, hv0⟩
  have hCE : C.epoch = e0 := hInv.votedEpochByz i0 hi0 e0 C hv0
  have hCP : s.proposed e0 = some C := hInv.votedProposedByz i0 hi0 e0 C hv0
  have hb1ne : b1 ≠ Block.genesis := proposal_succ_ne_genesis hInv hp1
  have hb2ne : b2 ≠ Block.genesis :=
    proposal_ne_genesis_of hInv hp2 (Nat.succ_pos (e + 1))
  by_cases h1 : C.epoch = e
  · have he0' : e0 = e := by rw [← hCE, h1]
    have hCb : s.proposed e = some C := by rw [he0'] at hCP; exact hCP
    have hC0 : C = b0 := Option.some.inj (hCb.symm.trans hp0)
    subst C
    omega
  · by_cases h2 : C.epoch = e + 1
    · have he0' : e0 = e + 1 := by rw [← hCE, h2]
      have hCb : s.proposed (e + 1) = some C := by rw [he0'] at hCP; exact hCP
      have hC1 : C = b1 := Option.some.inj (hCb.symm.trans hp1)
      subst C
      omega
    · by_cases h3 : C.epoch = e + 2
      · have he0' : e0 = e + 2 := by rw [← hCE, h3]
        have hCb : s.proposed (e + 2) = some C := by rw [he0'] at hCP; exact hCP
        have hC2' : C = b2 := Option.some.inj (hCb.symm.trans hp2)
        exact hCne hC2'
      · by_cases hlt : C.epoch < e
        · by_cases hg : C = Block.genesis
          · subst C
            simp at hClen
            have hb2pos : 0 < b2.length := Block.length_pos hb2ne
            omega
          · have hCp : ChainNotarizedBy s n C.pred (C.epoch - 1) :=
              by simpa [hCE] using (hInv.votedSeenParentByz i0 hi0 e0 C hv0)
            have hlenP : C.pred.length ≤ b1.pred.length := by
              by_cases hgp : C.pred = Block.genesis
              · simp [hgp]
              · have hN : NotarizedBy s n C.pred (C.epoch - 1) :=
                  hCp C.pred (Block.mem_ancestors_self C.pred) hgp
                have hN' : NotarizedBy s n C.pred e :=
                  notarizedBy_mono (Nat.le_trans (Nat.sub_le C.epoch 1) (le_of_lt hlt)) hN
                exact hInv.proposedLongest (e + 1) b1 hp1 C.pred hN'
            have hClen' : C.length = C.pred.length + 1 := Block.pred_length hg
            have hb1len : b1.length = b1.pred.length + 1 := Block.pred_length hb1ne
            have hb2len : b2.length = b2.pred.length + 1 := Block.pred_length hb2ne
            have hCleq : C.length ≤ b1.length := by omega
            omega
        · have hge : e ≤ C.epoch := le_of_not_gt hlt
          have h1l : e + 1 ≤ C.epoch :=
            Nat.succ_le_of_lt (lt_of_le_of_ne hge (Ne.symm h1))
          have h2l : e + 2 ≤ C.epoch :=
            Nat.succ_le_of_lt (lt_of_le_of_ne h1l (Ne.symm h2))
          have hgt : e + 2 < C.epoch := lt_of_le_of_ne h2l (Ne.symm h3)
          by_cases hg : C = Block.genesis
          · subst C
            simp at hClen
            have hb2pos : 0 < b2.length := Block.length_pos hb2ne
            omega
          · have hlong : ∀ C' : Block, NotarizedBy s n C' (C.epoch - 1) →
              C'.length ≤ C.pred.length := by
              simpa [hCE] using (hInv.votedLongestByz i0 hi0 e0 C hv0)
            have hb2N : NotarizedBy s n b2 (e + 2) :=
              hC2 b2 (Block.mem_ancestors_self b2) hb2ne
            have hle' : e + 2 ≤ C.epoch - 1 := Nat.le_sub_one_of_lt hgt
            have hb2N' : NotarizedBy s n b2 (C.epoch - 1) := notarizedBy_mono hle' hb2N
            have hb2le : b2.length ≤ C.pred.length := hlong b2 hb2N'
            have hClen' : C.length = C.pred.length + 1 := Block.pred_length hg
            have hb2len : b2.length = b2.pred.length + 1 := Block.pred_length hb2ne
            omega

/-- A block is final when it is the middle of three adjacent notarized
blocks with consecutive positive epochs on a fully notarized chain. -/
@[simp] def FinalizedByz (n : Nat) (s : St) (e : Epoch) (b0 b b2 : Block) : Prop :=
  0 < e ∧ b0.epoch = e ∧ b.epoch = e + 1 ∧ b2.epoch = e + 2 ∧
  b = Block.block b0 (e + 1) ∧ b2 = Block.block b (e + 2) ∧ ChainNotarized s n b2

/-- **Theorem 6 (Byzantine liveness core)**: five consecutive proposals
with strictly growing lengths, each with its chain notarized on time —
`B₃` (the proposal of epoch `e+3`) is final, exactly the paper's finality
rule applied to `B₂, B₃, B₄`, with Byzantine quorums throughout. -/
theorem liveness_finality {n : Nat} {Byz : Finset Node} (hByz : ByzOk n Byz)
    {s : St} (hInv : InvByz Byz n s)
    {e : Epoch} {b0 b1 b2 b3 b4 : Block}
    (hp0 : s.proposed e = some b0) (hp1 : s.proposed (e + 1) = some b1)
    (hp2 : s.proposed (e + 2) = some b2) (hp3 : s.proposed (e + 3) = some b3)
    (hp4 : s.proposed (e + 4) = some b4)
    (hG01 : b0.length < b1.length) (hG12 : b1.length < b2.length)
    (hG23 : b2.length < b3.length) (_hG34 : b3.length < b4.length)
    (hC2 : ChainNotarizedBy s n b2 (e + 2)) (hC3 : ChainNotarizedBy s n b3 (e + 3))
    (hC4 : ChainNotarizedBy s n b4 (e + 4)) :
    FinalizedByz n s (e + 2) b2 b3 b4 := by
  have hb2ne : b2 ≠ Block.genesis :=
    proposal_ne_genesis_of hInv hp2 (Nat.succ_pos (e + 1))
  have hb3ne : b3 ≠ Block.genesis :=
    proposal_ne_genesis_of hInv hp3 (Nat.succ_pos (e + 2))
  have hb4ne : b4 ≠ Block.genesis :=
    proposal_ne_genesis_of hInv hp4 (Nat.succ_pos (e + 3))
  -- `B₃` extends `B₂`: its parent is the unique longest chain at `e+2`
  have hAdj23 : b3 = Block.block b2 (e + 3) := by
    have hb3pred : b3.pred = b2 := by
      have hlen : b3.pred.length = b2.length := by
        apply le_antisymm
        · by_cases hg : b3.pred = Block.genesis
          · simp [hg]
          · have hN3 : NotarizedBy s n b3.pred (e + 2) :=
              hInv.proposedSeenParent (e + 3) b3 hp3 b3.pred
                (Block.mem_ancestors_self b3.pred) hg
            exact longest_chain_by hByz hInv hp0 hp1 hp2 hG01 hG12 hC2 b3.pred hN3
        · have hN : NotarizedBy s n b2 (e + 2) :=
            hC2 b2 (Block.mem_ancestors_self b2) hb2ne
          exact hInv.proposedLongest (e + 3) b3 hp3 b2 hN
      by_contra hne
      by_cases hg : b3.pred = Block.genesis
      · have : b3.length = 1 := by
          have hb3len : b3.length = b3.pred.length + 1 := Block.pred_length hb3ne
          simp [hg] at hb3len
          exact hb3len
        have hpos : 0 < b3.length := Block.length_pos hb3ne
        have hgt : b2.length < b3.length := hG23
        omega
      · have hN3 : NotarizedBy s n b3.pred (e + 2) :=
          hInv.proposedSeenParent (e + 3) b3 hp3 b3.pred
            (Block.mem_ancestors_self b3.pred) hg
        have hN3' : Notarized s n b3.pred := ⟨e + 2, hN3⟩
        exact (main_liveness_lemma hByz hInv hp0 hp1 hp2 hG01 hG12 hC2 b3.pred hne hlen hN3')
    have hb3eq : b3 = Block.block b3.pred b3.epoch := Block.eq_block_pred_epoch hb3ne
    have hb3E : b3.epoch = e + 3 := hInv.proposedEpoch (e + 3) b3 hp3
    rw [hb3pred, hb3E] at hb3eq
    exact hb3eq
  -- `B₄` extends `B₃`: same argument with the triple `(B₁, B₂, B₃)`
  have hAdj34 : b4 = Block.block b3 (e + 4) := by
    have hb4pred : b4.pred = b3 := by
      have hlen : b4.pred.length = b3.length := by
        apply le_antisymm
        · by_cases hg : b4.pred = Block.genesis
          · simp [hg]
          · have hN4 : NotarizedBy s n b4.pred (e + 3) :=
              hInv.proposedSeenParent (e + 4) b4 hp4 b4.pred
                (Block.mem_ancestors_self b4.pred) hg
            exact longest_chain_by hByz hInv hp1 hp2 hp3 hG12 hG23 hC3 b4.pred hN4
        · have hN : NotarizedBy s n b3 (e + 3) :=
            hC3 b3 (Block.mem_ancestors_self b3) hb3ne
          exact hInv.proposedLongest (e + 4) b4 hp4 b3 hN
      by_contra hne
      by_cases hg : b4.pred = Block.genesis
      · have : b3.length = 0 := by simpa [hg] using hlen.symm
        have hpos : 0 < b3.length := Block.length_pos hb3ne
        omega
      · have hN4 : NotarizedBy s n b4.pred (e + 3) :=
          hInv.proposedSeenParent (e + 4) b4 hp4 b4.pred
            (Block.mem_ancestors_self b4.pred) hg
        have hN4' : Notarized s n b4.pred := ⟨e + 3, hN4⟩
        exact (main_liveness_lemma hByz hInv hp1 hp2 hp3 hG12 hG23 hC3 b4.pred hne hlen hN4')
    have hb4eq : b4 = Block.block b4.pred b4.epoch := Block.eq_block_pred_epoch hb4ne
    have hb4E : b4.epoch = e + 4 := hInv.proposedEpoch (e + 4) b4 hp4
    rw [hb4pred, hb4E] at hb4eq
    exact hb4eq
  refine ⟨Nat.succ_pos (e + 1), hInv.proposedEpoch (e + 2) b2 hp2,
    hInv.proposedEpoch (e + 3) b3 hp3, hInv.proposedEpoch (e + 4) b4 hp4,
    hAdj23, hAdj34, ?_⟩
  intro C hmem hne
  exact ⟨e + 4, hC4 C hmem hne⟩

/-! ## Temporal liveness: the Byzantine-timing wrapper -/

/-- Some block is final. -/
def FinalSomeByz (n : Nat) (s : St) : Prop :=
  ∃ e : Epoch, ∃ b0 b b2 : Block, FinalizedByz n s e b0 b b2

/-- The window `[e0, e0+5)` progress predicate: every completed window
epoch's proposal is chain-notarized by its own epoch. -/
def WindowDoneByz (n : Nat) (e0 : Epoch) (s : St) : Prop :=
  ∀ e' : Epoch, e0 ≤ e' → e' < s.cur →
    ∃ b : Block, s.proposed e' = some b ∧ ChainNotarizedBy s n b e'

/-- Every honest node votes for the epoch's proposal once it is ready, so
it becomes (Byzantine-quorum) chain-notarized before the epoch passes. -/
def VoteAssumptionByz (n : Nat) (e : Epoch) : Tla.Pred St :=
  Tla.leadsTo
    (Tla.statePred (fun s => s.cur = e ∧
      ∃ b : Block, s.proposed e = some b ∧
        ChainNotarizedBy s n b.pred (e - 1) ∧
        ∀ C : Block, NotarizedBy s n C (e - 1) → C.length ≤ b.pred.length))
    (Tla.statePred (fun s => s.cur = e ∧
      ∃ b : Block, s.proposed e = some b ∧ ChainNotarizedBy s n b e))

/-- The Byzantine-timing spec: the protocol plus the clock, the honest
leaders (`L e ∉ Byz`) proposing each epoch, and the honest nodes voting. -/
def HByz (n : Nat) (Byz : Finset Node) (L : Epoch → Node) : Tla.Pred St :=
  Tla.tlaAnd (Tla.statePred (InitByz Byz))
    (Tla.tlaAnd (Tla.stutAlways (Next Byz L n) vars)
      (Tla.tlaAnd (fun e => ∀ e' : Epoch, ClockAssumption e' e)
        (Tla.tlaAnd (fun e => ∀ e' : Epoch, LeaderProposeAssumption Byz L e' e)
          (fun e => ∀ e' : Epoch, VoteAssumptionByz n e' e))))

/-! ### Persistence along behaviors -/

/-- A frame step (votes unchanged) preserves every recorded vote. -/
lemma votes_persist_of_frame {s s' : St} {i : Node} {e : Epoch} {b : Block}
    (hframe : votes s' = votes s) (hv : s.votes i e = some b) :
    s'.votes i e = some b := by
  have hv' : votes s i e = some b := by simpa using hv
  have hv'' : votes s' i e = some b := by rw [hframe]; exact hv'
  simpa using hv''

/-- A frame step (proposals unchanged) preserves every recorded proposal. -/
lemma proposals_persist_of_frame {s s' : St} {e : Epoch} {b : Block}
    (hframe : proposed s' = proposed s) (hp : s.proposed e = some b) :
    s'.proposed e = some b := by
  have hp' : proposed s e = some b := by simpa using hp
  have hp'' : proposed s' e = some b := by rw [hframe]; exact hp'
  simpa using hp''

/-- A `Next` step never removes a vote. -/
lemma next_votes_persist {n : Nat} {Byz : Finset Node} {L : Epoch → Node} {s s' : St}
    (hstep : Next Byz L n s s') {i : Node} {e : Epoch} {b : Block}
    (hv : s.votes i e = some b) : s'.votes i e = some b := by
  unfold Next at hstep
  rcases hstep with hadv | ⟨e0, b0, hstep⟩
  · rcases hadv with ⟨hCur', hProp', hVotes'⟩
    exact votes_persist_of_frame hVotes' hv
  · rcases hstep with hp | ⟨i0, hvot⟩
    · rcases hp with ⟨hLeader, hcur, hNone, hpos, hbE, hSeen, hLongest, hProp', hCur', hVotes'⟩
      exact votes_persist_of_frame hVotes' hv
    · rcases hvot with ⟨hi0, hcur, hpos, hProp, hNoVote, hSeen, hLongest, hVotes', hProp', hCur'⟩
      by_cases hke : i = i0 ∧ e = b0.epoch
      · rcases hke with ⟨hii, hee⟩
        subst i
        subst e
        have hv' : votes s i0 b0.epoch = some b := by simpa using hv
        have hvn : votes s i0 b0.epoch ≠ none := by
          rw [hv']
          simp
        exact (hvn hNoVote).elim
      · have hv' : (vote s i0 b0).votes i e = s.votes i e :=
          vote_votes_of_ne (not_and_or.mp hke)
        have hs' : s' = vote s i0 b0 := by
          apply TlaDsl.Examples.Streamlet.Liveness.St.ext
          · simpa [vote] using hCur'
          · simpa [vote] using hProp'
          · simpa [vote] using hVotes'
        rw [hs']
        exact hv'.trans hv

/-- A `Next` step never removes a proposal. -/
lemma next_proposals_persist {n : Nat} {Byz : Finset Node} {L : Epoch → Node} {s s' : St}
    (hstep : Next Byz L n s s') {e : Epoch} {b : Block}
    (hp : s.proposed e = some b) : s'.proposed e = some b := by
  unfold Next at hstep
  rcases hstep with hadv | ⟨e0, b0, hstep⟩
  · rcases hadv with ⟨hCur', hProp', hVotes'⟩
    exact proposals_persist_of_frame hProp' hp
  · rcases hstep with hp' | ⟨i0, hvot⟩
    · rcases hp' with ⟨hLeader, hcur, hNone, hpos, hbE, hSeen, hLongest, hProp', hCur', hVotes'⟩
      by_cases he : e = e0
      · subst e
        have hp' : proposed s e0 = some b := by simpa using hp
        have hpn : proposed s e0 ≠ none := by
          rw [hp']
          simp
        exact (hpn hNone).elim
      · have hp'' : (propose s e0 b0).proposed e = s.proposed e := by
          simp [propose, Function.update, he]
        have hs' : s' = propose s e0 b0 := by
          apply TlaDsl.Examples.Streamlet.Liveness.St.ext
          · simpa [propose] using hCur'
          · simpa [propose] using hProp'
          · simpa [propose] using hVotes'
        rw [hs']
        exact hp''.trans hp
    · rcases hvot with ⟨hi0, hcur, hpos, hProp, hNoVote, hSeen, hLongest, hVotes', hProp', hCur'⟩
      exact proposals_persist_of_frame hProp' hp

/-- Stuttering steps never remove votes or proposals. -/
lemma stut_votes_persist {n : Nat} {Byz : Finset Node} {L : Epoch → Node} {s s' : St}
    (hstep : Tla.StutAction (Next Byz L n) vars s s')
    {i : Node} {e : Epoch} {b : Block} (hv : s.votes i e = some b) :
    s'.votes i e = some b := by
  rcases hstep with hnext | hstut
  · exact next_votes_persist hnext hv
  · have hs' : s' = s := by simpa using hstut
    subst s'
    exact hv

lemma stut_proposals_persist {n : Nat} {Byz : Finset Node} {L : Epoch → Node} {s s' : St}
    (hstep : Tla.StutAction (Next Byz L n) vars s s')
    {e : Epoch} {b : Block} (hp : s.proposed e = some b) :
    s'.proposed e = some b := by
  rcases hstep with hnext | hstut
  · exact next_proposals_persist hnext hp
  · have hs' : s' = s := by simpa using hstut
    subst s'
    exact hp

lemma votes_persist_along {n : Nat} {Byz : Finset Node} {L : Epoch → Node}
    {e : Tla.Behavior St}
    (hStut : ∀ m, Tla.StutAction (Next Byz L n) vars (e m) (e (m + 1)))
    {i : Node} {e' : Epoch} {b : Block} {k j : Nat}
    (hv : (e k).votes i e' = some b) : (e (k + j)).votes i e' = some b := by
  induction j with
  | zero => simpa using hv
  | succ j ih =>
      have h' : (e (k + j)).votes i e' = some b := ih
      have h'' := stut_votes_persist (hStut (k + j)) h'
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h''

lemma proposals_persist_along {n : Nat} {Byz : Finset Node} {L : Epoch → Node}
    {e : Tla.Behavior St}
    (hStut : ∀ m, Tla.StutAction (Next Byz L n) vars (e m) (e (m + 1)))
    {e' : Epoch} {b : Block} {k j : Nat}
    (hp : (e k).proposed e' = some b) : (e (k + j)).proposed e' = some b := by
  induction j with
  | zero => simpa using hp
  | succ j ih =>
      have h' : (e (k + j)).proposed e' = some b := ih
      have h'' := stut_proposals_persist (hStut (k + j)) h'
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h''

/-- Notarization facts survive additions of votes. -/
lemma notarizedBy_votes_add {n : Nat} {s s' : St} {b : Block} {e : Epoch}
    (hv : ∀ i : Node, ∀ e' : Epoch, s.votes i e' = some b → s'.votes i e' = some b) :
    NotarizedBy s n b e → NotarizedBy s' n b e := by
  rintro ⟨Q, hQ, h⟩
  refine ⟨Q, hQ, ?_⟩
  intro i hi
  rcases h i hi with ⟨e0, he0, hv0⟩
  exact ⟨e0, he0, hv i e0 hv0⟩

lemma chainNotarizedBy_votes_add {n : Nat} {s s' : St} {b : Block} {e : Epoch}
    (hv : ∀ b : Block, ∀ i : Node, ∀ e' : Epoch,
      s.votes i e' = some b → s'.votes i e' = some b) :
    ChainNotarizedBy s n b e → ChainNotarizedBy s' n b e := by
  intro hc C hmem hne
  exact notarizedBy_votes_add (hv C) (hc C hmem hne)

lemma chainNotarizedBy_persist_along {n : Nat} {Byz : Finset Node} {L : Epoch → Node}
    {e : Tla.Behavior St}
    (hStut : ∀ m, Tla.StutAction (Next Byz L n) vars (e m) (e (m + 1)))
    {b : Block} {e' : Epoch} {k j : Nat}
    (hc : ChainNotarizedBy (e k) n b e') : ChainNotarizedBy (e (k + j)) n b e' := by
  intro C hmem hne
  rcases hc C hmem hne with ⟨Q, hQ, hv⟩
  refine ⟨Q, hQ, ?_⟩
  intro i hi
  rcases hv i hi with ⟨e0, he0, hv0⟩
  exact ⟨e0, he0, votes_persist_along hStut hv0⟩

/-- The completed-window facts survive to a later state. -/
lemma window_done_persist {n : Nat} {s s' : St}
    (hv : ∀ b : Block, ∀ i : Node, ∀ e : Epoch,
      s.votes i e = some b → s'.votes i e = some b)
    (hp : ∀ b : Block, ∀ e : Epoch, s.proposed e = some b → s'.proposed e = some b)
    {e0 : Epoch} (hW : WindowDoneByz n e0 s) :
    ∀ e' : Epoch, e0 ≤ e' → e' < s.cur →
      ∃ b : Block, s'.proposed e' = some b ∧ ChainNotarizedBy s' n b e' := by
  intro e' he0' he'
  rcases hW e' he0' he' with ⟨b0, hpb0, hcb0⟩
  refine ⟨b0, hp b0 e' hpb0, chainNotarizedBy_votes_add hv hcb0⟩

/-! ### The final step: the window delivers a final block -/

/-- A chain-notarized block is itself notarized. -/
lemma chain_notarized_block {n : Nat} {s : St} {b : Block} {e : Epoch}
    (hc : ChainNotarizedBy s n b e) (hne : b ≠ Block.genesis) : NotarizedBy s n b e :=
  hc b (Block.mem_ancestors_self b) hne

/-- **The window delivers** (Byzantine): if all five window epochs
completed with chain-notarized proposals, the third proposal is final. -/
lemma window_finality_byz {n : Nat} {Byz : Finset Node} (hByz : ByzOk n Byz)
    {s : St} (hInv : InvByz Byz n s) {e0 : Epoch} (he0 : 0 < e0)
    (hW : WindowDoneByz n e0 s) (hcur : s.cur = e0 + 5) : FinalSomeByz n s := by
  have hlt0 : e0 < s.cur := by
    rw [hcur]
    exact Nat.lt_add_of_pos_right (by decide : 0 < 5)
  have hlt1 : e0 + 1 < s.cur := by
    rw [hcur]
    exact Nat.add_lt_add_left (by decide : 1 < 5) e0
  have hlt2 : e0 + 2 < s.cur := by
    rw [hcur]
    exact Nat.add_lt_add_left (by decide : 2 < 5) e0
  have hlt3 : e0 + 3 < s.cur := by
    rw [hcur]
    exact Nat.add_lt_add_left (by decide : 3 < 5) e0
  have hlt4 : e0 + 4 < s.cur := by
    rw [hcur]
    exact Nat.add_lt_add_left (by decide : 4 < 5) e0
  rcases hW e0 le_rfl hlt0 with ⟨b0, hp0, hc0⟩
  rcases hW (e0 + 1) (le_self_add e0 1) hlt1 with ⟨b1, hp1, hc1⟩
  rcases hW (e0 + 2) (le_self_add e0 2) hlt2 with ⟨b2, hp2, hc2⟩
  rcases hW (e0 + 3) (le_self_add e0 3) hlt3 with ⟨b3, hp3, hc3⟩
  rcases hW (e0 + 4) (le_self_add e0 4) hlt4 with ⟨b4, hp4, hc4⟩
  have hb0ne : b0 ≠ Block.genesis := proposal_ne_genesis_of hInv hp0 (by omega)
  have hb1ne : b1 ≠ Block.genesis := proposal_succ_ne_genesis hInv hp1
  have hb2ne : b2 ≠ Block.genesis :=
    proposal_ne_genesis_of hInv hp2 (Nat.succ_pos (e0 + 1))
  have hb3ne : b3 ≠ Block.genesis :=
    proposal_ne_genesis_of hInv hp3 (Nat.succ_pos (e0 + 2))
  have hb4ne : b4 ≠ Block.genesis :=
    proposal_ne_genesis_of hInv hp4 (Nat.succ_pos (e0 + 3))
  have hG01 : b0.length < b1.length :=
    proposal_growth hInv hp0 hp1 ⟨b0, chain_notarized_block hc0 hb0ne, le_rfl⟩
  have hG12 : b1.length < b2.length :=
    proposal_growth hInv hp1 hp2 ⟨b1, chain_notarized_block hc1 hb1ne, le_rfl⟩
  have hG23 : b2.length < b3.length :=
    proposal_growth hInv hp2 hp3 ⟨b2, chain_notarized_block hc2 hb2ne, le_rfl⟩
  have hG34 : b3.length < b4.length :=
    proposal_growth hInv hp3 hp4 ⟨b3, chain_notarized_block hc3 hb3ne, le_rfl⟩
  exact ⟨e0 + 2, b2, b3, b4,
    liveness_finality hByz hInv hp0 hp1 hp2 hp3 hp4 hG01 hG12 hG23 hG34 hc2 hc3 hc4⟩

/-! ### The per-epoch step -/

/-- **One epoch completes** (Byzantine): from `cur = e'` (with the
invariants), the propose/vote/clock assumptions deliver `cur = e'+1` with
the epoch's proposal chain-notarized. -/
lemma epoch_step_byz {n : Nat} {Byz : Finset Node} {L : Epoch → Node} {e' : Epoch}
    {e : Tla.Behavior St} (hH : HByz n Byz L e) :
    Tla.leadsTo
      (Tla.statePred (fun s => InvByz Byz n s ∧ s.cur = e'))
      (Tla.statePred (fun s => InvByz Byz n s ∧ s.cur = e' + 1 ∧
        ∃ b : Block, s.proposed e' = some b ∧ ChainNotarizedBy s n b e')) e := by
  have hStut : ∀ m, Tla.StutAction (Next Byz L n) vars (e m) (e (m + 1)) := by
    intro m
    have hm := hH.2.1 m
    tla_drop_simpa using hm
  have hInvAll : ∀ m, InvByz Byz n (e m) := by
    exact Tla.inv_all_of_spec (spec_entails_inv_byz Byz L n) ⟨hH.1, hH.2.1⟩
  intro k hp
  rcases hp with ⟨hInv0, hcur⟩
  -- step 1: the proposal of epoch `e'` exists (maybe after the propose
  -- assumption fires — the honest-leader conjunct is dropped)
  have hstep1 : ∃ j1 : Nat,
      (e (k + j1)).proposed e' ≠ none ∧ (e (k + j1)).cur = e' := by
    by_cases hnone : (e k).proposed e' = none
    · have hnone0 : ((e.drop k) 0).proposed e' = none := by
        tla_drop_simpa using hnone
      rcases Tla.leadsTo_at_suffix (hH.2.2.2.1 e').2 ⟨hcur, hnone0⟩ with ⟨j1, hj1⟩
      exact ⟨j1, hj1⟩
    · refine ⟨0, ?_⟩
      have hk : e (k + 0) = e k := by rw [Nat.add_zero]
      have hcur' : (e k).cur = e' := by
        tla_drop_simpa using hcur
      constructor
      · rw [hk]
        exact hnone
      · rw [hk]
        exact hcur'
  rcases hstep1 with ⟨j1, hj1⟩
  -- step 2: the vote assumption chain-notarizes the proposal
  have hp1s : (fun s => s.cur = e' ∧
      ∃ b : Block, s.proposed e' = some b ∧
        ChainNotarizedBy s n b.pred (e' - 1) ∧
        ∀ C : Block, NotarizedBy s n C (e' - 1) → C.length ≤ b.pred.length)
      (e (k + j1)) := by
    have hne : (e (k + j1)).proposed e' ≠ none := hj1.1
    rcases Option.ne_none_iff_exists.mp hne with ⟨b, hpb⟩
    have hpb' : (e (k + j1)).proposed e' = some b := hpb.symm
    have hInv1 : InvByz Byz n (e (k + j1)) := hInvAll (k + j1)
    refine ⟨hj1.2, ⟨b, hpb', ?_, ?_⟩⟩
    · exact hInv1.proposedSeenParent e' b hpb'
    · intro C hC
      exact hInv1.proposedLongest e' b hpb' C hC
  rcases Tla.leadsTo_at (hH.2.2.2.2 e') hp1s with ⟨j2, hj2⟩
  -- step 3: the clock advances
  rcases Tla.leadsTo_at (hH.2.2.1 e') hj2.1 with ⟨j3, hj3⟩
  -- assemble
  rcases hj2 with ⟨hcur2, b, hpb, hcb⟩
  refine ⟨j1 + j2 + j3, ?_⟩
  constructor
  · tla_drop_simpa using (hInvAll (k + (j1 + j2 + j3)))
  · constructor
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj3
    · refine ⟨b, ?_, ?_⟩
      · tla_drop_simpa using (proposals_persist_along hStut (k := k + j1 + j2) (j := j3) hpb)
      · tla_drop_simpa using (chainNotarizedBy_persist_along hStut (k := k + j1 + j2) (j := j3) hcb)

/-! ### The window countdown -/

/-- From `k` epochs remaining in the window, the window completes:
`WindowDoneByz ∧ cur = e0+5-k` leads to `WindowDoneByz ∧ cur = e0+5`. -/
theorem window_progress_byz (n : Nat) (Byz : Finset Node) (L : Epoch → Node)
    (e0 : Epoch) (k : Nat) (hk : k ≤ 5) {e : Tla.Behavior St} (hH : HByz n Byz L e) :
    Tla.leadsTo
      (Tla.statePred (fun s => WindowDoneByz n e0 s ∧ s.cur = e0 + 5 - k))
      (Tla.statePred (fun s => WindowDoneByz n e0 s ∧ s.cur = e0 + 5)) e := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro n' hp
      rcases hp with ⟨hW, hcur⟩
      by_cases hk0 : k = 0
      · subst k
        have hW' : WindowDoneByz n e0 (e n') := by
          tla_drop_simpa using hW
        have hcur' : (e n').cur = e0 + 5 := by
          tla_drop_simpa using hcur
        refine ⟨0, ?_⟩
        tla_drop_simpa using ⟨hW', hcur'⟩
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        let e' := e0 + 5 - k
        have hcur0 : (e n').cur = e0 + 5 - k := by
          tla_drop_simpa using hcur
        have hcur' : (e n').cur = e' := by simpa [e'] using hcur0
        have hInv' : InvByz Byz n (e n') :=
          Tla.inv_all_of_spec (spec_entails_inv_byz Byz L n) ⟨hH.1, hH.2.1⟩ n'
        have hstep := epoch_step_byz (n := n) (Byz := Byz) (L := L) (e' := e') hH
        rcases Tla.leadsTo_at hstep ⟨hInv', hcur'⟩ with ⟨j, hj⟩
        have hStut : ∀ m, Tla.StutAction (Next Byz L n) vars (e m) (e (m + 1)) := by
          intro m
          have hm := hH.2.1 m
          tla_drop_simpa using hm
        have hW0 : WindowDoneByz n e0 (e n') := by
          tla_drop_simpa using hW
        -- build WindowDoneByz at the new state
        have hW' : WindowDoneByz n e0 (e (n' + j)) := by
          rcases hj with ⟨hInvj, hcurj, hfact⟩
          intro e'' he0'' hlt''
          have hltj : e'' < e' + 1 := by
            simpa [hcurj] using hlt''
          by_cases hlt : e'' < e'
          · have hlt0 : e'' < (e n').cur := by
              simpa [hcur'] using hlt
            rcases hW0 e'' he0'' hlt0 with ⟨b, hpb, hcb⟩
            refine ⟨b, proposals_persist_along hStut (k := n') (j := j) hpb,
              chainNotarizedBy_persist_along hStut (k := n') (j := j) hcb⟩
          · have heq : e'' = e' := by
              have hge : e' ≤ e'' := le_of_not_gt hlt
              exact le_antisymm (Nat.le_of_lt_succ hltj) hge
            subst e''
            rcases hfact with ⟨b, hpb, hcb⟩
            exact ⟨b, hpb, hcb⟩
        -- the rank decreased by one
        have hrank : (e (n' + j)).cur = e0 + 5 - (k - 1) := by
          have hcurj : (e (n' + j)).cur = e' + 1 := hj.2.1
          have hsub : e' + 1 = e0 + 5 - (k - 1) := by
            dsimp [e']
            have hk1 : 1 ≤ k := hkpos
            have hka : k ≤ e0 + 5 := by omega
            have hkk : k = (k - 1) + 1 := (Nat.sub_add_cancel hk1).symm
            rw [hkk]
            rw [← Nat.sub_sub]
            have hk' : k - 1 ≤ e0 + 4 := Nat.sub_le_sub_right hka 1
            have hsub2 : e0 + 5 - (e0 + 4) ≤ e0 + 5 - (k - 1) :=
              Nat.sub_le_sub_left hk' (e0 + 5)
            have h1 : 1 ≤ e0 + 5 - (e0 + 4) := by
              have hh : e0 + 5 = e0 + 4 + 1 := by
                rw [Nat.add_succ]
              rw [hh]
              simp
            have hle : 1 ≤ e0 + 5 - (k - 1) := le_trans h1 hsub2
            rw [Nat.sub_add_cancel hle]
            rfl
          rw [hsub] at hcurj
          exact hcurj
        have hkm : k - 1 < k := by omega
        have hkm5 : k - 1 ≤ 5 := by omega
        have hih : Tla.leadsTo
            (Tla.statePred (fun s => WindowDoneByz n e0 s ∧ s.cur = e0 + 5 - (k - 1)))
            (Tla.statePred (fun s => WindowDoneByz n e0 s ∧ s.cur = e0 + 5)) e :=
          ih (k - 1) hkm hkm5
        rcases Tla.leadsTo_at hih ⟨hW', hrank⟩ with ⟨j', hj'⟩
        refine ⟨j + j', ?_⟩
        tla_drop_simpa using hj'

/-! ### The Byzantine liveness theorem -/

/-- **Streamlet liveness under Byzantine faults (Theorem 13, Byzantine)**:
with `f < n/3` Byzantine nodes, under the clock, the honest leaders
proposing, and the honest nodes voting, from the start of a 5-epoch window
some block is eventually final — for any leader schedule `L` whose leaders
are honest. -/
theorem liveness_spec_byz (n : Nat) (Byz : Finset Node) (L : Epoch → Node)
    (hByz : ByzOk n Byz) (e0 : Epoch) (he0 : 0 < e0) :
    Tla.Entails (HByz n Byz L)
      (Tla.leadsTo (Tla.statePred (fun s => s.cur = e0))
        (Tla.statePred (fun s => FinalSomeByz n s))) := by
  intro e hH n' hp
  have hcur0 : (e n').cur = e0 := by
    tla_drop_simpa using hp
  have hStut : ∀ m, Tla.StutAction (Next Byz L n) vars (e m) (e (m + 1)) := by
    intro m
    have hm := hH.2.1 m
    tla_drop_simpa using hm
  have hInvAll : ∀ m, InvByz Byz n (e m) := by
    exact Tla.inv_all_of_spec (spec_entails_inv_byz Byz L n) ⟨hH.1, hH.2.1⟩
  have hW : WindowDoneByz n e0 (e n') := by
    intro e'' he0'' hlt''
    have hlt0 : e'' < e0 := by
      rw [hcur0] at hlt''
      exact hlt''
    exact (not_lt_of_ge he0'' hlt0).elim
  have hrank : (e n').cur = e0 + 5 - 5 := by
    rw [hcur0]
    exact Nat.add_sub_cancel e0 5
  have h5 := window_progress_byz n Byz L e0 5 (by omega) hH
  rcases Tla.leadsTo_at h5 ⟨hW, hrank⟩ with ⟨j, hj⟩
  rcases hj with ⟨hW', hcur'⟩
  refine ⟨j, ?_⟩
  have hfin : FinalSomeByz n (e (n' + j)) := window_finality_byz hByz (hInvAll (n' + j)) he0 hW' hcur'
  tla_drop_simpa using hfin

end TlaDsl.Examples.StreamletByzLiveness
