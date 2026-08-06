import TlaDsl.Examples.Streamlet

open scoped Tla

/-! # Streamlet: liveness structure

The liveness side of **Streamlet** (Chan & Shi, IACR ePrint 2020/088,
Appendix A, all-honest crash-fault model): the epoch/proposal machinery
behind Fact 3, Lemma 5 and Theorem 6 of Section 3.6.

The safety file (`Streamlet.lean`) modeled votes and *seen* chain lengths
without a time dimension, which is exactly what consistency needs (the
paper stresses that consistency is timing-independent). Liveness is
different: it is about *progress* — proposals, votes, notarizations and
the 5-epoch honest-leader window. This file adds the missing structure in
the lightest faithful way:

* the state carries `cur : Epoch` (the current epoch) and
  `proposed : Epoch → Option Block` (each epoch's unique proposal), plus
  the votes from the safety model;
* **epoch numbers are the timestamps**: "block `b` is notarized by epoch
  `e`" (`NotarizedBy n s b e`) means a quorum voted for `b` in epochs
  `≤ e` (every vote happens in its own epoch — an invariant), and "every
  honest node has observed a notarized chain ending at `b` by the
  beginning of epoch `e+1`" is exactly `ChainNotarizedBy n s b e`. The
  paper's Fact 1/2 (message delivery within `∆` after GST, epochs of
  length `2∆`) is abstracted to this immediate-delivery predicate — a
  documented, timing-abstract model of the partially-synchronous regime;
* the proposal rule (the leader proposes extending a longest notarized
  chain known by the start of its epoch) and the vote rule (vote for the
  epoch's proposal iff its parent chain is a longest chain known by the
  start of the epoch) are action preconditions with **epoch-bounded**
  `NotarizedBy` predicates, so the "at that time" conditions are preserved
  as plain invariants (new votes in epoch `e` never affect predicates
  bounded by `e-1`).

What is proved here:

1. **Safety core for the extended model** — `unique_notarization` and the
   main consistency lemma `finality_no_conflict`, re-proved for the
   epoch/proposal model (the vote-length discipline `VoteLenMono` is the
   whole content, as in the safety file).
2. **Fact 3** (`proposal_growth`) — if a chain of length `≥ ℓ` is
   notarized by the time the next epoch's leader proposes, the next
   proposal is strictly longer than `ℓ`.
3. **Lemma 5** (`main_liveness_lemma`) — three consecutive proposals with
   strictly growing lengths, the third with its chain notarized on time:
   no conflicting block at the third's length is ever notarized.
4. **Theorem 6** (`liveness_finality`) — five consecutive proposals with
   growing lengths and on-time notarized chains: the third's chain is
   final, exactly the paper's finality rule applied to `B₂, B₃, B₄`.

The temporal wrapper — "under the spec plus honest-behavior timing
assumptions, a block becomes final" — is the remaining slice; the
state-level lemmas here are the proof's mathematical core.
-/

/-! ## Blocks: parent and length facts -/

namespace TlaDsl.Examples.Streamlet.Block

/-- The parent of a non-genesis block (genesis maps to itself). Defined
inside the `Block` namespace with fully-qualified names: the namespace and
the inductive share the identifier `Block`, so the bare name resolves to
the namespace here. -/
def pred : TlaDsl.Examples.Streamlet.Block → TlaDsl.Examples.Streamlet.Block
  | TlaDsl.Examples.Streamlet.Block.genesis => TlaDsl.Examples.Streamlet.Block.genesis
  | TlaDsl.Examples.Streamlet.Block.block p _ => p

/-- A non-genesis block's length is its parent's plus one. -/
theorem pred_length {b : TlaDsl.Examples.Streamlet.Block}
    (h : b ≠ TlaDsl.Examples.Streamlet.Block.genesis) :
    b.length = b.pred.length + 1 := by
  cases b with
  | genesis => exact (h rfl).elim
  | block p _ => simp [TlaDsl.Examples.Streamlet.Block.pred,
    TlaDsl.Examples.Streamlet.Block.length]

/-- A non-genesis block is exactly its parent with its own epoch. -/
theorem eq_block_pred_epoch {b : TlaDsl.Examples.Streamlet.Block}
    (h : b ≠ TlaDsl.Examples.Streamlet.Block.genesis) :
    b = TlaDsl.Examples.Streamlet.Block.block b.pred b.epoch := by
  cases b with
  | genesis => exact (h rfl).elim
  | block p e => simp [TlaDsl.Examples.Streamlet.Block.pred,
    TlaDsl.Examples.Streamlet.Block.epoch]

/-- The parent of a non-genesis block is on its chain. -/
theorem pred_mem_ancestors {b : TlaDsl.Examples.Streamlet.Block}
    (h : b ≠ TlaDsl.Examples.Streamlet.Block.genesis) :
    b.pred ∈ b.ancestors := by
  cases b with
  | genesis => exact (h rfl).elim
  | block p e =>
      change p ∈ p.ancestors ++ [TlaDsl.Examples.Streamlet.Block.block p e]
      exact List.mem_append_left _ (Block.mem_ancestors_self p)

/-- A non-genesis block has positive length. -/
theorem length_pos {b : TlaDsl.Examples.Streamlet.Block}
    (h : b ≠ TlaDsl.Examples.Streamlet.Block.genesis) : 0 < b.length := by
  have h' := pred_length h
  omega

end TlaDsl.Examples.Streamlet.Block

namespace TlaDsl.Examples.Streamlet.Liveness

open TlaDsl.Examples.Streamlet

/-! ## The epoch/proposal model -/

/-- Node identities (the parties are `0, ..., n-1`). -/
abbrev Node := Nat

/-- Epoch numbers. -/
abbrev Epoch := Nat

/-- The liveness state: the current epoch, each epoch's proposal, and the
votes. "Notarized by epoch `e`" is *derived* from the votes (a quorum that
voted in epochs `≤ e`), so no delivery/seen state is needed — epoch numbers
are the timestamps. -/
@[ext]
structure St where
  cur : Epoch
  proposed : Epoch → Option Block
  votes : Node → Epoch → Option Block

tla_var St cur proposed votes

/-- Quorums: a strict majority of the first `n` nodes. -/
abbrev Quorum (n : Nat) (Q : Finset Node) : Prop := Streamlet.Quorum n Q

/-- Any two quorums intersect. -/
theorem quorum_overlap {n : Nat} {Q1 Q2 : Finset Node}
    (h1 : Quorum n Q1) (h2 : Quorum n Q2) : ∃ a : Node, a ∈ Q1 ∧ a ∈ Q2 :=
  Streamlet.quorum_overlap h1 h2

/-- A quorum is nonempty. -/
theorem quorum_nonempty {n : Nat} {Q : Finset Node} (h : Quorum n Q) :
    ∃ a : Node, a ∈ Q := by
  have hpos : 0 < Q.card := by
    apply Nat.pos_of_ne_zero
    intro hcard
    have : 2 * 0 > n := by simpa [hcard] using h.2
    omega
  rcases Finset.card_pos.mp hpos with ⟨a, ha⟩
  exact ⟨a, ha⟩

/-- Block `b` is notarized by epoch `e`: a quorum voted for it in epochs
`≤ e`. The state is the first argument so the bracket elaborator lifts it. -/
def NotarizedBy (s : St) (n : Nat) (b : Block) (e : Epoch) : Prop :=
  ∃ Q : Finset Node, Quorum n Q ∧
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
keeps the votes of epochs `≤ e` intact (the equation is symmetric, so the
equivalence goes both ways). -/
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

/-- Notarization facts are unchanged when the votes are unchanged. -/
lemma notarizedBy_votes_same {s s' : St} {n : Nat} {b : Block} {e : Epoch}
    (h : s'.votes = s.votes) : NotarizedBy s n b e ↔ NotarizedBy s' n b e :=
  notarizedBy_votes_eq (fun i e' he' => by rw [h])

lemma chainNotarizedBy_votes_same {s s' : St} {n : Nat} {b : Block} {e : Epoch}
    (h : s'.votes = s.votes) : ChainNotarizedBy s n b e ↔ ChainNotarizedBy s' n b e :=
  chainNotarizedBy_votes_eq (fun i e' he' => by rw [h])

/-! ## The protocol (in the DSL) -/

/-- Initially: epoch 0, no proposals, no votes. -/
@[simp] def Init : Tla.StatePred St :=
  [p| cur = 0 ∧ (∀ e : Epoch, proposed[e] = none) ∧
      (∀ i : Node, ∀ e : Epoch, votes[i][e] = none)]

/-- The state after the leader of epoch `e` proposes `b`. -/
def propose (s : St) (e : Epoch) (b : Block) : St :=
  { s with proposed := Function.update s.proposed e (some b) }

/-- The state after node `i` votes for `b` in epoch `b.epoch`. -/
def vote (s : St) (i : Node) (b : Block) : St :=
  { s with
    votes := Function.update s.votes i (Function.update (s.votes i) b.epoch (some b)) }

/-- The clock advances to the next epoch. -/
@[simp] def Advance : Tla.Action St :=
  [a| cur' = cur + 1 ∧ proposed' = proposed ∧ votes' = votes]

/-- The epoch-`e` leader proposes `b` at the start of epoch `e`: `b`
extends one of the longest chains notarized by the end of epoch `e-1`. -/
@[simp] def Propose (n : Nat) (e : Epoch) (b : Block) : Tla.Action St :=
  [a| cur = e ∧ proposed[e] = none ∧ 0 < e ∧ b.epoch = e ∧
      ChainNotarizedBy n (b.pred) (e - 1) ∧
      (∀ C : Block, NotarizedBy n C (e - 1) → C.length ≤ b.pred.length) ∧
      proposed' = Function.update proposed e (some b) ∧ cur' = cur ∧ votes' = votes]

/-- Node `i` votes for the epoch-`e` proposal `b` during epoch `e`, only if
`b` extends a longest chain notarized by the end of `e-1`, and only for the
unique proposal of the epoch. -/
@[simp] def Vote (n : Nat) (i : Node) (b : Block) : Tla.Action St :=
  [a| cur = b.epoch ∧ 0 < b.epoch ∧ proposed[b.epoch] = some b ∧
      votes[i][b.epoch] = none ∧
      ChainNotarizedBy n (b.pred) (b.epoch - 1) ∧
      (∀ C : Block, NotarizedBy n C (b.epoch - 1) → C.length ≤ b.pred.length) ∧
      votes' = Function.update votes i (Function.update (votes i) b.epoch (some b)) ∧
      proposed' = proposed ∧ cur' = cur]

@[simp] def Next (n : Nat) : Tla.Action St :=
  [a| Advance ∨
      ∃ e : Epoch, ∃ b : Block, Propose n e b ∨ ∃ i : Node, Vote n i b]

def Spec (n : Nat) : Tla.Pred St := [t| Init ∧ □[Next n]_vars]

/-! ## Invariants -/

/-- Votes are for blocks whose epoch matches the voting epoch. -/
@[simp] def VotedEpoch (s : St) : Prop :=
  ∀ i : Node, ∀ e : Epoch, ∀ b : Block, s.votes i e = some b → b.epoch = e

/-- Votes only happen in positive epochs (never for genesis). -/
@[simp] def VotedPosEpoch (s : St) : Prop :=
  ∀ i : Node, ∀ e : Epoch, ∀ b : Block, s.votes i e = some b → 0 < e

/-- Votes are only for the unique proposal of the epoch. -/
@[simp] def VotedProposed (s : St) : Prop :=
  ∀ i : Node, ∀ e : Epoch, ∀ b : Block, s.votes i e = some b → s.proposed e = some b

/-- Votes happen no later than the current epoch. -/
@[simp] def VotedCur (s : St) : Prop :=
  ∀ i : Node, ∀ e : Epoch, ∀ b : Block, s.votes i e = some b → e ≤ s.cur

/-- A voter had seen the proposal's parent chain notarized by the start of
the epoch. -/
@[simp] def VotedSeenParent (n : Nat) (s : St) : Prop :=
  ∀ i : Node, ∀ e : Epoch, ∀ b : Block,
    s.votes i e = some b → ChainNotarizedBy s n b.pred (e - 1)

/-- A voter had seen nothing longer than the proposal's parent chain by
the start of the epoch (the longest-chain condition, epoch-bounded). -/
@[simp] def VotedLongest (n : Nat) (s : St) : Prop :=
  ∀ i : Node, ∀ e : Epoch, ∀ b : Block,
    s.votes i e = some b →
    ∀ C : Block, NotarizedBy s n C (e - 1) → C.length ≤ b.pred.length

/-- **The honest longest-chain discipline**: a node's votes are for blocks
of non-decreasing length. -/
@[simp] def VoteLenMono (s : St) : Prop :=
  ∀ i : Node, ∀ e1 e2 : Epoch, ∀ b1 b2 : Block,
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
proofs use `hInv.votedEpoch`, `hInv.proposedLongest`, ... instead of deep
nested projections. -/
structure Inv (n : Nat) (s : St) : Prop where
  votedEpoch : VotedEpoch s
  votedPosEpoch : VotedPosEpoch s
  votedProposed : VotedProposed s
  votedCur : VotedCur s
  votedSeenParent : VotedSeenParent n s
  votedLongest : VotedLongest n s
  voteLenMono : VoteLenMono s
  proposedEpoch : ProposedEpoch s
  proposedPosEpoch : ProposedPosEpoch s
  proposedCur : ProposedCur s
  proposedSeenParent : ProposedSeenParent n s
  proposedLongest : ProposedLongest n s

/-! ## The invariants are inductive -/

lemma vote_votes_self {s : St} {i : Node} {b : Block} :
    (vote s i b).votes i b.epoch = some b := by
  simp [vote, Function.update]

lemma vote_votes_of_ne {s : St} {i : Node} {b : Block} {j : Node} {e : Epoch}
    (h : j ≠ i ∨ e ≠ b.epoch) : (vote s i b).votes j e = s.votes j e := by
  rcases h with hji | he
  · simp [vote, Function.update, hji]
  · by_cases hji' : j = i
    · subst j
      simp [vote, Function.update, he]
    · simp [vote, Function.update, hji']

lemma propose_proposed_self {s : St} {e : Epoch} {b : Block} :
    (propose s e b).proposed e = some b := by
  simp [propose, Function.update]

lemma propose_proposed_of_ne {s : St} {e e0 : Epoch} {b : Block}
    (h : e0 ≠ e) : (propose s e b).proposed e0 = s.proposed e0 := by
  simp [propose, Function.update, h]

theorem votedEpoch_vote {n : Nat} {s : St} {i : Node} {b : Block} (hInv : Inv n s) :
    VotedEpoch (vote s i b) := by
  intro j e' b' hv'
  by_cases hje : j = i ∧ e' = b.epoch
  · rcases hje with ⟨hji, he'⟩
    subst j
    subst e'
    have hb' : b' = b := (Option.some.inj (by simpa [vote, Function.update] using hv')).symm
    subst b'
    rfl
  · have hv'' : s.votes j e' = some b' := vote_votes_of_ne (not_and_or.mp hje) ▸ hv'
    exact hInv.votedEpoch j e' b' hv''

theorem votedPosEpoch_vote {n : Nat} {s : St} {i : Node} {b : Block}
    (hpos : 0 < b.epoch) (hInv : Inv n s) :
    VotedPosEpoch (vote s i b) := by
  intro j e' b' hv'
  by_cases hje : j = i ∧ e' = b.epoch
  · rcases hje with ⟨rfl, rfl⟩
    have hb' : b' = b := (Option.some.inj (by simpa [vote, Function.update] using hv')).symm
    subst b'
    exact hpos
  · have hv'' : s.votes j e' = some b' := vote_votes_of_ne (not_and_or.mp hje) ▸ hv'
    exact hInv.votedPosEpoch j e' b' hv''

theorem votedProposed_vote {n : Nat} {s : St} {i : Node} {b : Block}
    (hProp : s.proposed b.epoch = some b) (hInv : Inv n s) :
    VotedProposed (vote s i b) := by
  intro j e' b' hv'
  by_cases hje : j = i ∧ e' = b.epoch
  · rcases hje with ⟨rfl, rfl⟩
    have hb' : b' = b := (Option.some.inj (by simpa [vote, Function.update] using hv')).symm
    subst b'
    exact hProp
  · have hv'' : s.votes j e' = some b' := vote_votes_of_ne (not_and_or.mp hje) ▸ hv'
    exact hInv.votedProposed j e' b' hv''

/-- `a ≤ b - 1` with `0 < b` gives `a < b`. -/
lemma lt_of_le_pred {a b : Nat} (ha : 0 < b) (h : a ≤ b - 1) : a < b := by
  have hb : 1 ≤ b := Nat.succ_le_of_lt ha
  have h1 : a + 1 ≤ b - 1 + 1 := Nat.add_le_add_right h 1
  have h2 : a + 1 ≤ b := by
    rw [Nat.sub_add_cancel hb] at h1
    exact h1
  exact Nat.lt_of_succ_le h2

/-- Voting for `b` in epoch `b.epoch` does not touch votes recorded in
epochs strictly before it (`≤ e - 1` for any `e ≤ b.epoch`). -/
lemma vote_preserves_pred_bound {s : St} {i : Node} {b : Block} {e : Epoch}
    (hpos : 0 < b.epoch) (hle : e ≤ b.epoch) :
    ∀ k : Node, ∀ e0 : Epoch, e0 ≤ e - 1 →
      (vote s i b).votes k e0 = s.votes k e0 := by
  intro k e0 he0
  have hle0 : e0 ≤ b.epoch - 1 := le_trans he0 (Nat.sub_le_sub_right hle 1)
  exact vote_votes_of_ne (Or.inr (ne_of_lt (lt_of_le_pred hpos hle0)))

theorem votedCur_vote {n : Nat} {s : St} {i : Node} {b : Block}
    (hcur : s.cur = b.epoch) (hInv : Inv n s) :
    VotedCur (vote s i b) := by
  intro j e' b' hv'
  by_cases hje : j = i ∧ e' = b.epoch
  · rcases hje with ⟨rfl, rfl⟩
    have hb' : b' = b := (Option.some.inj (by simpa [vote, Function.update] using hv')).symm
    subst b'
    simpa [vote] using (le_of_eq hcur.symm)
  · have hv'' : s.votes j e' = some b' := vote_votes_of_ne (not_and_or.mp hje) ▸ hv'
    exact hInv.votedCur j e' b' hv''

theorem votedSeenParent_vote {n : Nat} {s : St} {i : Node} {b : Block}
    (hSeen : ChainNotarizedBy s n b.pred (b.epoch - 1))
    (hpos : 0 < b.epoch) (hcur : s.cur = b.epoch) (hInv : Inv n s) :
    VotedSeenParent n (vote s i b) := by
  intro j e' b' hv'
  by_cases hje : j = i ∧ e' = b.epoch
  · rcases hje with ⟨hji, he'⟩
    subst j
    subst e'
    have hb' : b' = b := (Option.some.inj (by simpa [vote, Function.update] using hv')).symm
    subst b'
    have hpres : ∀ k : Node, ∀ e0 : Epoch, e0 ≤ b.epoch - 1 →
        (vote s i b).votes k e0 = s.votes k e0 := by
      intro k e0 he0
      exact vote_votes_of_ne (Or.inr (ne_of_lt (lt_of_le_pred hpos he0)))
    exact (chainNotarizedBy_votes_eq hpres).1 hSeen
  · have hv'' : s.votes j e' = some b' := vote_votes_of_ne (not_and_or.mp hje) ▸ hv'
    have hc : ChainNotarizedBy s n b'.pred (e' - 1) := hInv.votedSeenParent j e' b' hv''
    have hle : e' ≤ b.epoch := by
      simpa [hcur] using (hInv.votedCur j e' b' hv'')
    have hpres : ∀ k : Node, ∀ e0 : Epoch, e0 ≤ e' - 1 →
        (vote s i b).votes k e0 = s.votes k e0 := by
      intro k e0 he0
      have hle0 : e0 ≤ b.epoch - 1 := le_trans he0 (Nat.sub_le_sub_right hle 1)
      exact vote_votes_of_ne (Or.inr (ne_of_lt (lt_of_le_pred hpos hle0)))
    exact (chainNotarizedBy_votes_eq hpres).1 hc

theorem votedLongest_vote {n : Nat} {s : St} {i : Node} {b : Block}
    (hLongest : ∀ C : Block, NotarizedBy s n C (b.epoch - 1) → C.length ≤ b.pred.length)
    (hpos : 0 < b.epoch) (hcur : s.cur = b.epoch) (hInv : Inv n s) :
    VotedLongest n (vote s i b) := by
  intro j e' b' hv' C hC
  by_cases hje : j = i ∧ e' = b.epoch
  · rcases hje with ⟨hji, he'⟩
    subst j
    subst e'
    have hb' : b' = b := (Option.some.inj (by simpa [vote, Function.update] using hv')).symm
    subst b'
    have hpres : ∀ k : Node, ∀ e0 : Epoch, e0 ≤ b.epoch - 1 →
        (vote s i b).votes k e0 = s.votes k e0 := by
      intro k e0 he0
      exact vote_votes_of_ne (Or.inr (ne_of_lt (lt_of_le_pred hpos he0)))
    exact hLongest C ((notarizedBy_votes_eq hpres).2 hC)
  · have hv'' : s.votes j e' = some b' := vote_votes_of_ne (not_and_or.mp hje) ▸ hv'
    have hle : e' ≤ b.epoch := by
      simpa [hcur] using (hInv.votedCur j e' b' hv'')
    have hpres : ∀ k : Node, ∀ e0 : Epoch, e0 ≤ e' - 1 →
        (vote s i b).votes k e0 = s.votes k e0 := by
      intro k e0 he0
      have hle0 : e0 ≤ b.epoch - 1 := le_trans he0 (Nat.sub_le_sub_right hle 1)
      exact vote_votes_of_ne (Or.inr (ne_of_lt (lt_of_le_pred hpos hle0)))
    have hC' : NotarizedBy s n C (e' - 1) :=
      (notarizedBy_votes_eq hpres).2 hC
    exact hInv.votedLongest j e' b' hv'' C hC'

theorem voteLenMono_vote {n : Nat} {s : St} {i : Node} {b : Block}
    (hbne : b ≠ Block.genesis)
    (hLongest : ∀ C : Block, NotarizedBy s n C (b.epoch - 1) → C.length ≤ b.pred.length)
    (hcur : s.cur = b.epoch) (hInv : Inv n s) : VoteLenMono (vote s i b) := by
  intro j e1 e2 b1 b2 hv1 hv2 hlt
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
          have h0 : 0 < e1 := hInv.votedPosEpoch i e1 b1 hv1'
          have he : b1.epoch = e1 := hInv.votedEpoch i e1 b1 hv1'
          simpa [he] using h0)
      have hlen : b1.length ≤ b.length := by
        by_cases hg : b1.pred = Block.genesis
        · have hb1len : b1.length = b1.pred.length + 1 := Block.pred_length hb1ne
          have hblen : b.length = b.pred.length + 1 := Block.pred_length hbne
          simp [hg] at hb1len
          omega
        · have hc : ChainNotarizedBy s n b1.pred (e1 - 1) := hInv.votedSeenParent i e1 b1 hv1'
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
      exact hInv.voteLenMono j e1 b.epoch b1 b2 hv1' hv2' hlt
  · by_cases he1 : e1 = b.epoch
    · subst e1
      by_cases hji : j = i
      · subst j
        have hb1 : b1 = b := (Option.some.inj (by simpa [vote, Function.update] using hv1)).symm
        subst b1
        have hv2' : s.votes i e2 = some b2 := vote_votes_of_ne (Or.inr (by omega)) ▸ hv2
        have hle2 : e2 ≤ b.epoch := by
          simpa [hcur] using (hInv.votedCur i e2 b2 hv2')
        exact (not_le_of_gt hlt hle2).elim
      · have hv1' : s.votes j b.epoch = some b1 := vote_votes_of_ne (Or.inl hji) ▸ hv1
        have hv2' : s.votes j e2 = some b2 := vote_votes_of_ne (Or.inl hji) ▸ hv2
        exact hInv.voteLenMono j b.epoch e2 b1 b2 hv1' hv2' hlt
    · have hv1' : s.votes j e1 = some b1 := vote_votes_of_ne (Or.inr he1) ▸ hv1
      have hv2' : s.votes j e2 = some b2 := vote_votes_of_ne (Or.inr he2) ▸ hv2
      exact hInv.voteLenMono j e1 e2 b1 b2 hv1' hv2' hlt

theorem vote_inv {n : Nat} {s s' : St} {i : Node} {b : Block}
    (hstep : Vote n i b s s') (hInv : Inv n s) : Inv n s' := by
  tla_unfold
  rcases hstep with ⟨hcur, hpos, hProp, hNoVote, hSeen, hLongest, hVotes', hProp', hCur'⟩
  have hs' : s' = vote s i b := by
    ext <;> simp [vote, hVotes', hProp', hCur']
  subst s'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact votedEpoch_vote hInv
  · exact votedPosEpoch_vote hpos hInv
  · exact votedProposed_vote hProp hInv
  · exact votedCur_vote hcur hInv
  · exact votedSeenParent_vote hSeen hpos hcur hInv
  · exact votedLongest_vote hLongest hpos hcur hInv
  · exact voteLenMono_vote
      (Block.epoch_pos_ne_genesis hpos)
      hLongest hcur hInv
  · -- ProposedEpoch: unchanged
    intro e0 b0 hv0
    exact hInv.proposedEpoch e0 b0 (by simpa [vote] using hv0)
  · -- ProposedPosEpoch
    intro e0 b0 hv0
    exact hInv.proposedPosEpoch e0 b0 (by simpa [vote] using hv0)
  · -- ProposedCur
    intro e0 b0 hv0
    exact hInv.proposedCur e0 b0 (by simpa [vote] using hv0)
  · -- ProposedSeenParent
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

theorem propose_inv {n : Nat} {s s' : St} {e : Epoch} {b : Block}
    (hstep : Propose n e b s s') (hInv : Inv n s) : Inv n s' := by
  tla_unfold
  rcases hstep with ⟨hcur, hNone, hpos, hbE, hSeen, hLongest, hProp', hCur', hVotes'⟩
  have hs' : s' = propose s e b := by
    ext <;> simp [propose, hProp', hCur', hVotes']
  subst s'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i e0 b0 hv0
    exact hInv.votedEpoch i e0 b0 (by simpa [propose] using hv0)
  · intro i e0 b0 hv0
    exact hInv.votedPosEpoch i e0 b0 (by simpa [propose] using hv0)
  · intro i e0 b0 hv0
    have hv0' : s.votes i e0 = some b0 := by simpa [propose] using hv0
    have hp0 : s.proposed e0 = some b0 := hInv.votedProposed i e0 b0 hv0'
    have hne : e0 ≠ e := by
      intro he
      subst e0
      rw [hp0] at hNone
      cases hNone
    exact (propose_proposed_of_ne (s := s) (e := e) (e0 := e0) (b := b) hne) ▸ hp0
  · intro i e0 b0 hv0
    exact hInv.votedCur i e0 b0 (by simpa [propose] using hv0)
  · intro i e0 b0 hv0
    exact hInv.votedSeenParent i e0 b0 (by simpa [propose] using hv0)
  · intro i e0 b0 hv0 C hC
    have hv0' : s.votes i e0 = some b0 := by simpa [propose] using hv0
    have hC' : NotarizedBy s n C (e0 - 1) :=
      (notarizedBy_votes_same (by rfl : (propose s e b).votes = s.votes)).2 hC
    exact hInv.votedLongest i e0 b0 hv0' C hC'
  · intro i e1 e2 b1 b2 hv1 hv2 hlt
    exact hInv.voteLenMono i e1 e2 b1 b2
      (by simpa [propose] using hv1) (by simpa [propose] using hv2) hlt
  · -- ProposedEpoch: the new proposal has b.epoch = e; old ones unchanged
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

theorem advance_inv {n : Nat} {s s' : St}
    (hstep : Advance s s') (hInv : Inv n s) : Inv n s' := by
  tla_unfold
  rcases hstep with ⟨hCur', hProp', hVotes'⟩
  have hs' : s' = { s with cur := s.cur + 1 } := by
    ext <;> simp [hCur', hProp', hVotes']
  subst s'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i e0 b0 hv0
    exact hInv.votedEpoch i e0 b0 (by simpa [hVotes'] using hv0)
  · intro i e0 b0 hv0
    exact hInv.votedPosEpoch i e0 b0 (by simpa [hVotes'] using hv0)
  · intro i e0 b0 hv0
    exact hInv.votedProposed i e0 b0 (by simpa [hVotes'] using hv0)
  · intro i e0 b0 hv0
    have h1 : e0 ≤ s.cur := hInv.votedCur i e0 b0 (by simpa [hVotes'] using hv0)
    simpa using (le_trans h1 (Nat.le_succ s.cur))
  · intro i e0 b0 hv0
    have hv0' : s.votes i e0 = some b0 := by simpa [hVotes'] using hv0
    exact (chainNotarizedBy_votes_same (by rfl : { s with cur := s.cur + 1 }.votes = s.votes)).1
      (hInv.votedSeenParent i e0 b0 hv0')
  · intro i e0 b0 hv0 C hC
    have hv0' : s.votes i e0 = some b0 := by simpa [hVotes'] using hv0
    have hC' : NotarizedBy s n C (e0 - 1) :=
      (notarizedBy_votes_same (by rfl : { s with cur := s.cur + 1 }.votes = s.votes)).2 hC
    exact hInv.votedLongest i e0 b0 hv0' C hC'
  · intro i e1 e2 b1 b2 hv1 hv2 hlt
    exact hInv.voteLenMono i e1 e2 b1 b2
      (by simpa [hVotes'] using hv1) (by simpa [hVotes'] using hv2) hlt
  · intro e0 b0 hv0
    exact hInv.proposedEpoch e0 b0 (by simpa [hProp'] using hv0)
  · intro e0 b0 hv0
    exact hInv.proposedPosEpoch e0 b0 (by simpa [hProp'] using hv0)
  · intro e0 b0 hv0
    have h1 : e0 ≤ s.cur := hInv.proposedCur e0 b0 (by simpa [hProp'] using hv0)
    simpa using (le_trans h1 (Nat.le_succ s.cur))
  · intro e0 b0 hv0
    have hv0' : s.proposed e0 = some b0 := by simpa [hProp'] using hv0
    exact (chainNotarizedBy_votes_same (by rfl : { s with cur := s.cur + 1 }.votes = s.votes)).1
      (hInv.proposedSeenParent e0 b0 hv0')
  · intro e0 b0 hv0 C hC
    have hv0' : s.proposed e0 = some b0 := by simpa [hProp'] using hv0
    have hC' : NotarizedBy s n C (e0 - 1) :=
      (notarizedBy_votes_same (by rfl : { s with cur := s.cur + 1 }.votes = s.votes)).2 hC
    exact hInv.proposedLongest e0 b0 hv0' C hC'

theorem init_inv {n : Nat} {s : St} (h : Init s) : Inv n s := by
  tla_unfold
  rcases h with ⟨hCur0, hNoProp, hNoVotes⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i e0 b0 hv0
    rw [hNoVotes i e0] at hv0
    cases hv0
  · intro i e0 b0 hv0
    rw [hNoVotes i e0] at hv0
    cases hv0
  · intro i e0 b0 hv0
    rw [hNoVotes i e0] at hv0
    cases hv0
  · intro i e0 b0 hv0
    rw [hNoVotes i e0] at hv0
    cases hv0
  · intro i e0 b0 hv0
    rw [hNoVotes i e0] at hv0
    cases hv0
  · intro i e0 b0 hv0
    rw [hNoVotes i e0] at hv0
    cases hv0
  · intro i e1 e2 b1 b2 hv1 hv2 hlt
    rw [hNoVotes i e1] at hv1
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

theorem next_inv (n : Nat) : ∀ s s' : St, Next n s s' → Inv n s → Inv n s' := by
  intro s s' hstep hInv
  unfold Next at hstep
  rcases hstep with hadv | ⟨e, b, hstep⟩
  · exact advance_inv hadv hInv
  · rcases hstep with hp | ⟨i, hv⟩
    · exact propose_inv hp hInv
    · exact vote_inv hv hInv

theorem stutter_inv (n : Nat) : ∀ s s' : St, vars s' = vars s → Inv n s → Inv n s' := by
  intro s s' hstut hInv
  tla_unfold
  have hs' : s' = s := by simpa using hstut
  subst s'
  exact hInv

/-- Every reachable state satisfies the invariants. -/
theorem spec_entails_inv (n : Nat) :
    (Tla.tlaAnd (Tla.statePred Init) (Tla.stutAlways (Next n) vars)) ⊢ □ ⌜ Inv n ⌝ := by
  apply Tla.init_invariant_stut
  · intro s hs
    exact init_inv hs
  · intro s s' hstep hInv
    rcases hstep with hnext | hstut
    · exact next_inv n s s' hnext hInv
    · exact stutter_inv n s s' hstut hInv

/-! ## Safety for the extended model -/

/-- A notarization of `b` gives a quorum that voted for `b` in `b`'s own
epoch (votes carry their epoch). -/
lemma notarized_quorum_at_epoch {n : Nat} {s : St} (hInv : Inv n s) {b : Block}
    (hN : Notarized s n b) :
    ∃ Q : Finset Node, Quorum n Q ∧
      ∀ i : Node, i ∈ Q → s.votes i b.epoch = some b := by
  rcases hN with ⟨e, ⟨Q, hQ, hv⟩⟩
  refine ⟨Q, hQ, ?_⟩
  intro i hi
  rcases hv i hi with ⟨e0, he0, hv0⟩
  have hbE : b.epoch = e0 := hInv.votedEpoch i e0 b hv0
  rw [← hbE] at hv0
  exact hv0

/-- **Lemma 10**: at most one notarized block per epoch — two notarized
blocks of the same epoch share a voter (quorum overlap), and a node votes
at most once per epoch. -/
theorem unique_notarization {n : Nat} {s : St} (hInv : Inv n s) {b b' : Block}
    (hN : Notarized s n b) (hN' : Notarized s n b') (hE : b.epoch = b'.epoch) : b = b' := by
  rcases notarized_quorum_at_epoch hInv hN with ⟨Q, hQ, hQv⟩
  rcases notarized_quorum_at_epoch hInv hN' with ⟨Q', hQ', hQ'v⟩
  rcases quorum_overlap hQ hQ' with ⟨i, hiQ, hiQ'⟩
  have h1 : s.votes i b.epoch = some b := hQv i hiQ
  have h2 : s.votes i b'.epoch = some b' := hQ'v i hiQ'
  rw [← hE] at h2
  exact Option.some.inj (h1.symm.trans h2)

/-- **Lemma 11/14**: a finality witness `(b0, b, b2)` — three adjacent
notarized blocks with consecutive epochs — blocks any conflicting
notarized block at `b`'s length. -/
theorem finality_no_conflict {n : Nat} {s : St} (hInv : Inv n s)
    {e : Epoch} {b0 b b2 : Block}
    (hEpos : 0 < e) (hB0 : b0.epoch = e) (hB : b.epoch = e + 1) (hB2 : b2.epoch = e + 2)
    (hAdj1 : b = Block.block b0 (e + 1)) (hAdj2 : b2 = Block.block b (e + 2))
    (hChain : ChainNotarized s n b2)
    {c : Block} (hc : c ≠ b) (hclen : c.length = b.length)
    (hNc : Notarized s n c) : False := by
  have hb0ne : b0 ≠ Block.genesis := Block.epoch_pos_ne_genesis (by rw [hB0]; exact hEpos)
  have hbne : b ≠ Block.genesis := Block.epoch_pos_ne_genesis (by rw [hB]; omega)
  have hb2ne : b2 ≠ Block.genesis := Block.epoch_pos_ne_genesis (by rw [hB2]; omega)
  have hb0mem : b0 ∈ b2.ancestors := by
    rw [hAdj2, hAdj1]
    exact Block.mem_ancestors_of_mem_parent (Block.parent_mem_ancestors (p := b0) (e := e + 1))
  have hbmem : b ∈ b2.ancestors := by
    rw [hAdj2]
    exact Block.mem_ancestors_of_mem_parent (Block.mem_ancestors_self b)
  have hb2mem : b2 ∈ b2.ancestors := Block.mem_ancestors_self b2
  have hN0 : Notarized s n b0 := hChain b0 hb0mem hb0ne
  have hN1 : Notarized s n b := hChain b hbmem hbne
  have hN2 : Notarized s n b2 := hChain b2 hb2mem hb2ne
  have hlen1 : b.length = b0.length + 1 := by simp [Block.length, hAdj1]
  have hlen2 : b2.length = b.length + 1 := by simp [Block.length, hAdj2]
  by_cases h1 : c.epoch = e
  · have hc0 : c = b0 := unique_notarization hInv hNc hN0 (by rw [h1, hB0])
    subst c
    omega
  · by_cases h2 : c.epoch = e + 1
    · have hcb : c = b := unique_notarization hInv hNc hN1 (by rw [h2, hB])
      exact hc hcb
    · by_cases h3 : c.epoch = e + 2
      · have hcb2 : c = b2 := unique_notarization hInv hNc hN2 (by rw [h3, hB2])
        subst c
        omega
      · by_cases hlt : c.epoch < e
        · rcases notarized_quorum_at_epoch hInv hNc with ⟨Q, hQ, hQv⟩
          rcases notarized_quorum_at_epoch hInv hN0 with ⟨Q0, hQ0, hQ0v⟩
          rcases quorum_overlap hQ hQ0 with ⟨i, hiQ, hiQ0⟩
          have hv1 : s.votes i c.epoch = some c := hQv i hiQ
          have hv2 : s.votes i e = some b0 := by
            rw [← hB0]
            exact hQ0v i hiQ0
          have hmono : c.length ≤ b0.length := hInv.voteLenMono i c.epoch e c b0 hv1 hv2 hlt
          have hmono' : b0.length + 1 ≤ b0.length := by
            rw [← hlen1, ← hclen]
            exact hmono
          omega
        · have hge : e ≤ c.epoch := le_of_not_gt hlt
          have h1l : e + 1 ≤ c.epoch :=
            Nat.succ_le_of_lt (lt_of_le_of_ne hge (Ne.symm h1))
          have h2l : e + 2 ≤ c.epoch :=
            Nat.succ_le_of_lt (lt_of_le_of_ne h1l (Ne.symm h2))
          have hgt : e + 2 < c.epoch := lt_of_le_of_ne h2l (Ne.symm h3)
          rcases notarized_quorum_at_epoch hInv hNc with ⟨Q, hQ, hQv⟩
          rcases notarized_quorum_at_epoch hInv hN2 with ⟨Q2, hQ2, hQ2v⟩
          rcases quorum_overlap hQ hQ2 with ⟨i, hiQ, hiQ2⟩
          have hv1 : s.votes i (e + 2) = some b2 := by
            rw [← hB2]
            exact hQ2v i hiQ2
          have hv2 : s.votes i c.epoch = some c := hQv i hiQ
          have hmono : b2.length ≤ c.length :=
            hInv.voteLenMono i (e + 2) c.epoch b2 c hv1 hv2 hgt
          have hmono' : b.length + 1 ≤ b.length := by
            rw [← hlen2, ← hclen]
            exact hmono
          omega

/-! ## Liveness structure: Fact 3, Lemma 5, Theorem 6 -/

/-- A proposal carries its epoch, hence is non-genesis. -/
lemma proposal_ne_genesis_of {n : Nat} {s : St} (hInv : Inv n s) {e : Epoch} {b : Block}
    (hp : s.proposed e = some b) (hpos : 0 < e) : b ≠ Block.genesis :=
  Block.epoch_pos_ne_genesis (by
    have he : b.epoch = e := hInv.proposedEpoch e b hp
    simpa [he] using hpos)

/-- The proposal of `e+1` is non-genesis. -/
lemma proposal_succ_ne_genesis {n : Nat} {s : St} (hInv : Inv n s) {e : Epoch} {b : Block}
    (hp : s.proposed (e + 1) = some b) : b ≠ Block.genesis :=
  proposal_ne_genesis_of hInv hp (Nat.succ_pos e)

/-- **Fact 3** (abstract): if a chain of length `≥ ℓ` was notarized by the
time the next epoch's leader proposed, the next proposal is strictly longer
than `ℓ`. -/
theorem proposal_growth {n : Nat} {s : St} (hInv : Inv n s) {e : Epoch} {b0 b1 : Block}
    (_hp0 : s.proposed e = some b0) (hp1 : s.proposed (e + 1) = some b1)
    (hseen : ∃ C : Block, NotarizedBy s n C e ∧ b0.length ≤ C.length) :
    b0.length < b1.length := by
  rcases hseen with ⟨C, hC, hlen⟩
  have hle : C.length ≤ b1.pred.length := hInv.proposedLongest (e + 1) b1 hp1 C hC
  have hb1ne : b1 ≠ Block.genesis := proposal_succ_ne_genesis hInv hp1
  have hb1len : b1.length = b1.pred.length + 1 := Block.pred_length hb1ne
  omega

/-- No block longer than the third proposal is notarized by `e+2`: any such
block would be the proposal of its own epoch (votes only for proposals), so
it is one of `b0, b1, b2` (too short) or was voted for before epoch `e`
(contradicting the growth against `b1`). -/
theorem longest_chain_by {n : Nat} {s : St} (hInv : Inv n s)
    {e : Epoch} {b0 b1 b2 : Block}
    (hp0 : s.proposed e = some b0) (hp1 : s.proposed (e + 1) = some b1)
    (hp2 : s.proposed (e + 2) = some b2)
    (hG01 : b0.length < b1.length) (hG12 : b1.length < b2.length)
    (_hC2 : ChainNotarizedBy s n b2 (e + 2)) :
    ∀ C : Block, NotarizedBy s n C (e + 2) → C.length ≤ b2.length := by
  intro C hC
  rcases hC with ⟨Q, hQ, hv⟩
  rcases quorum_nonempty hQ with ⟨i0, hi0⟩
  rcases hv i0 hi0 with ⟨e0, he0, hv0⟩
  have hCE : C.epoch = e0 := hInv.votedEpoch i0 e0 C hv0
  have hCP : s.proposed e0 = some C := hInv.votedProposed i0 e0 C hv0
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
            by simpa [hCE] using (hInv.votedSeenParent i0 e0 C hv0)
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

/-- **Lemma 5(b)**: three consecutive proposals with strictly growing
lengths and the third's chain notarized on time — no conflicting block at
the third's length is ever notarized. -/
theorem main_liveness_lemma {n : Nat} {s : St} (hInv : Inv n s)
    {e : Epoch} {b0 b1 b2 : Block}
    (hp0 : s.proposed e = some b0) (hp1 : s.proposed (e + 1) = some b1)
    (hp2 : s.proposed (e + 2) = some b2)
    (hG01 : b0.length < b1.length) (hG12 : b1.length < b2.length)
    (hC2 : ChainNotarizedBy s n b2 (e + 2)) :
    ∀ C : Block, C ≠ b2 → C.length = b2.length → ¬ Notarized s n C := by
  intro C hCne hClen hNC
  rcases hNC with ⟨eC, ⟨Q, hQ, hv⟩⟩
  rcases quorum_nonempty hQ with ⟨i0, hi0⟩
  rcases hv i0 hi0 with ⟨e0, he0, hv0⟩
  have hCE : C.epoch = e0 := hInv.votedEpoch i0 e0 C hv0
  have hCP : s.proposed e0 = some C := hInv.votedProposed i0 e0 C hv0
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
              by simpa [hCE] using (hInv.votedSeenParent i0 e0 C hv0)
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
              simpa [hCE] using (hInv.votedLongest i0 e0 C hv0)
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
@[simp] def Finalized (n : Nat) (s : St) (e : Epoch) (b0 b b2 : Block) : Prop :=
  0 < e ∧ b0.epoch = e ∧ b.epoch = e + 1 ∧ b2.epoch = e + 2 ∧
  b = Block.block b0 (e + 1) ∧ b2 = Block.block b (e + 2) ∧ ChainNotarized s n b2

/-- **Theorem 6 (liveness core)**: five consecutive proposals with strictly
growing lengths, each with its chain notarized on time — `B₃` (the proposal
of epoch `e+3`) is final, exactly the paper's finality rule applied to
`B₂, B₃, B₄`. -/
theorem liveness_finality {n : Nat} {s : St} (hInv : Inv n s)
    {e : Epoch} {b0 b1 b2 b3 b4 : Block}
    (hp0 : s.proposed e = some b0) (hp1 : s.proposed (e + 1) = some b1)
    (hp2 : s.proposed (e + 2) = some b2) (hp3 : s.proposed (e + 3) = some b3)
    (hp4 : s.proposed (e + 4) = some b4)
    (hG01 : b0.length < b1.length) (hG12 : b1.length < b2.length)
    (hG23 : b2.length < b3.length) (_hG34 : b3.length < b4.length)
    (hC2 : ChainNotarizedBy s n b2 (e + 2)) (hC3 : ChainNotarizedBy s n b3 (e + 3))
    (hC4 : ChainNotarizedBy s n b4 (e + 4)) :
    Finalized n s (e + 2) b2 b3 b4 := by
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
            exact longest_chain_by hInv hp0 hp1 hp2 hG01 hG12 hC2 b3.pred hN3
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
        exact (main_liveness_lemma hInv hp0 hp1 hp2 hG01 hG12 hC2 b3.pred hne hlen hN3')
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
            exact longest_chain_by hInv hp1 hp2 hp3 hG12 hG23 hC3 b4.pred hN4
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
        exact (main_liveness_lemma hInv hp1 hp2 hp3 hG12 hG23 hC3 b4.pred hne hlen hN4')
    have hb4eq : b4 = Block.block b4.pred b4.epoch := Block.eq_block_pred_epoch hb4ne
    have hb4E : b4.epoch = e + 4 := hInv.proposedEpoch (e + 4) b4 hp4
    rw [hb4pred, hb4E] at hb4eq
    exact hb4eq
  refine ⟨Nat.succ_pos (e + 1), hInv.proposedEpoch (e + 2) b2 hp2,
    hInv.proposedEpoch (e + 3) b3 hp3, hInv.proposedEpoch (e + 4) b4 hp4,
    hAdj23, hAdj34, ?_⟩
  intro C hmem hne
  exact ⟨e + 4, hC4 C hmem hne⟩

end TlaDsl.Examples.Streamlet.Liveness
