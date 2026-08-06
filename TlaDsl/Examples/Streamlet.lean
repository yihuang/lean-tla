import TlaDsl.Basic
import TlaDsl.Notation
import TlaDsl.Coercion
import TlaDsl.Prime
import TlaDsl.Rules
import TlaDsl.Tactic
import TlaDsl.TlaVar

open scoped Tla

/-! # Streamlet: consistency

The safety (consistency) argument of **Streamlet** (Chan & Shi,
"Streamlet: Textbook Streamlined Blockchains", IACR ePrint 2020/088), in
the typed DSL. We formalize the crash-fault version of the paper
(Appendix A, tolerating `f < n/2`), specialized to the all-honest case
(`f = 0`): the consistency proof needs only the honest-node protocol rules,
which every node follows here.

The model is the paper's abstract block-tree view, at the same level as
`Paxos.lean`'s `Voting.tla`:

* `Block` is a rooted tree (`genesis` or `block parent e`), with
  `Block.epoch` and `Block.length` (distance from genesis);
* `votes : Node → Epoch → Option Block` records each node's vote per epoch
  (at most one, enforced by the action);
* `seen : Node → Nat → Prop` records the *lengths* of notarized chains a
  node has observed. The vote action enforces Streamlet's rule — a node
  votes for a proposal only if its parent chain is a *longest* notarized
  chain it has seen — through `seen[i][b.length - 1]` (the parent length)
  and `∀ k, seen[i][k] → k ≤ b.length - 1` (nothing longer seen);
* notarization is a strict majority of the `n` parties
  (`2 * Q.card > n`, quorums over `range n`), matching Appendix A's
  `> n/2` threshold;
* a block is *final* when it is the middle of three adjacent notarized
  blocks with consecutive epoch numbers, on a fully notarized chain.

The consistency proof is the paper's (Lemma 10 / 11 / Theorem 12 of
Appendix A), and it is *timing-independent*, exactly as the paper stresses:

1. **Unique notarization per epoch** — two notarized blocks of the same
   epoch share a voter (quorum overlap), and a node votes at most once per
   epoch, so the blocks are equal.
2. **Honest votes are length-monotone** — voting for a block means its
   parent is a *longest* seen chain; since seen chains only grow, a node
   never later votes for a block shorter than one it already voted for.
   This invariant (`VoteLenMono`) is the whole content of the honest
   longest-chain discipline.
3. **Main consistency lemma** — a finality witness `(b0, b, b2)` with
   consecutive epochs blocks a conflicting notarized block at `b`'s length:
   its epoch is either below `b0.epoch` (then a common voter of it and
   `b0` violates length-monotonicity) or above `b2.epoch` (same argument
   against `b2`).
4. **Consistency** — two final chains agree on the shorter one's prefix:
   otherwise their middle blocks would differ at the same length, both
   notarized, contradicting 3.

Liveness (the paper's Theorem 13: 5 consecutive honest-leader epochs after
GST) is deliberately out of scope here; it needs the leader schedule and
the partially-synchronous delivery model, and is orthogonal to the safety
structure above.
-/

namespace TlaDsl.Examples.Streamlet

/-! ## Blocks, chains, lengths -/

/-- A block: genesis, or a block with a parent and an epoch number.
The tree structure abstracts away the hash-chain details (Remark 1 of the
paper: given a block, its prefix is uniquely determined). -/
inductive Block : Type where
  | genesis : Block
  | block (parent : Block) (e : Nat) : Block

namespace Block

/-- The epoch number of a block (genesis has epoch 0). -/
def epoch : Block → Nat
  | genesis => 0
  | block _ e => e

/-- The length of a block: distance from genesis. -/
def length : Block → Nat
  | genesis => 0
  | block p _ => p.length + 1

/-- The unique chain from genesis to `b` (the "prefix" of `b`). -/
def ancestors : Block → List Block
  | genesis => [genesis]
  | block p e => p.ancestors ++ [block p e]

/-- The ancestor of `b` at length `k`, if `k ≤ b.length`. -/
def atLen : Block → Nat → Option Block
  | genesis, 0 => some genesis
  | genesis, _ + 1 => none
  | block p e, k =>
      if _h : k = p.length + 1 then some (block p e) else p.atLen k

@[simp] theorem epoch_genesis : Block.genesis.epoch = 0 := rfl
@[simp] theorem length_genesis : Block.genesis.length = 0 := rfl

/-- A block with a positive epoch is not genesis. -/
theorem epoch_pos_ne_genesis {b : Block} (h : 0 < b.epoch) : b ≠ Block.genesis := by
  intro hg
  subst hg
  simp at h

/-- A non-genesis block has positive length. -/
theorem length_pos_of_ne_genesis {b : Block} (h : b ≠ Block.genesis) : 0 < b.length := by
  cases b with
  | genesis => exact (h rfl).elim
  | block p _ => simp [Block.length]

/-- Every block is on its own chain. -/
theorem mem_ancestors_self (b : Block) : b ∈ b.ancestors := by
  cases b with
  | genesis => simp [Block.ancestors]
  | block p _ => simp [Block.ancestors]

/-- The parent of a block is on the block's chain. -/
theorem parent_mem_ancestors {p : Block} {e : Nat} : p ∈ (Block.block p e).ancestors := by
  change p ∈ p.ancestors ++ [Block.block p e]
  exact List.mem_append_left [Block.block p e] (mem_ancestors_self p)

/-- Chains extend under parents: anything on `p`'s chain is on any block
built on top of `p`. -/
theorem mem_ancestors_of_mem_parent {p : Block} {e : Nat} {a : Block}
    (h : a ∈ p.ancestors) : a ∈ (Block.block p e).ancestors := by
  simp [Block.ancestors, h]

/-- `b.atLen b.length = some b`: the ancestor of `b` at its own length is
itself. -/
theorem atLen_len (b : Block) : b.atLen b.length = some b := by
  cases b with
  | genesis => simp [Block.atLen, Block.length]
  | block p _ => simp [Block.atLen, Block.length]

/-- `atLen` is defined wherever the index does not exceed the length. -/
theorem atLen_ne_none : ∀ (b : Block) (k : Nat), k ≤ b.length → b.atLen k ≠ none
  | genesis, 0, _ => by simp [Block.atLen]
  | genesis, k + 1, h => by simp [Block.length] at h
  | block p _, 0, _ => by
      by_cases h0 : 0 = p.length + 1
      · unfold Block.atLen
        rw [dif_pos h0]
        simp
      · unfold Block.atLen
        rw [dif_neg h0]
        exact atLen_ne_none p 0 (by omega)
  | block p _, k + 1, h => by
      by_cases hk : k + 1 = p.length + 1
      · unfold Block.atLen
        rw [dif_pos hk]
        simp
      · unfold Block.atLen
        rw [dif_neg hk]
        have hle : k + 1 ≤ p.length := by
          have h' : k + 1 ≤ p.length + 1 := by simpa [Block.length] using h
          omega
        exact atLen_ne_none p (k + 1) hle

/-- `atLen` returns an ancestor. -/
theorem atLen_mem : ∀ (b : Block) (k : Nat) (c : Block),
    b.atLen k = some c → c ∈ b.ancestors
  | genesis, 0, c, h => by
      have hc : c = Block.genesis :=
        (Option.some.inj (by simpa [Block.atLen] using h)).symm
      subst c
      simp [Block.ancestors]
  | genesis, k + 1, c, h => by cases h
  | block p e, 0, c, h => by
      by_cases h0 : 0 = p.length + 1
      · unfold Block.atLen at h
        rw [dif_pos h0] at h
        have hc : c = Block.block p e := (Option.some.inj h).symm
        subst c
        exact mem_ancestors_self (Block.block p e)
      · unfold Block.atLen at h
        rw [dif_neg h0] at h
        exact mem_ancestors_of_mem_parent (atLen_mem p 0 c h)
  | block p e, k + 1, c, h => by
      by_cases hk : k + 1 = p.length + 1
      · unfold Block.atLen at h
        rw [dif_pos hk] at h
        have hc : c = Block.block p e := (Option.some.inj h).symm
        subst c
        exact mem_ancestors_self (Block.block p e)
      · unfold Block.atLen at h
        rw [dif_neg hk] at h
        exact mem_ancestors_of_mem_parent (atLen_mem p (k + 1) c h)

/-- The ancestor at length `k` has length `k`. -/
theorem atLen_len_of_eq : ∀ (b : Block) (k : Nat) (c : Block),
    b.atLen k = some c → c.length = k
  | genesis, 0, c, h => by
      have hc : c = Block.genesis :=
        (Option.some.inj (by simpa [Block.atLen] using h)).symm
      subst c
      rfl
  | genesis, k + 1, c, h => by cases h
  | block p e, 0, c, h => by
      by_cases h0 : 0 = p.length + 1
      · unfold Block.atLen at h
        rw [dif_pos h0] at h
        have hc : c = Block.block p e := (Option.some.inj h).symm
        subst c
        unfold Block.length
        exact h0.symm
      · unfold Block.atLen at h
        rw [dif_neg h0] at h
        exact atLen_len_of_eq p 0 c h
  | block p e, k + 1, c, h => by
      by_cases hk : k + 1 = p.length + 1
      · unfold Block.atLen at h
        rw [dif_pos hk] at h
        have hc : c = Block.block p e := (Option.some.inj h).symm
        subst c
        unfold Block.length
        exact hk.symm
      · unfold Block.atLen at h
        rw [dif_neg hk] at h
        exact atLen_len_of_eq p (k + 1) c h

end Block

/-! ## State and the protocol (in the DSL) -/

/-- Node identities (the parties are `0, ..., n-1`, as in the quorum
predicate below). -/
abbrev Node := Nat

/-- Epoch numbers. -/
abbrev Epoch := Nat

/-- The Streamlet state: the votes (one per node per epoch, enforced by the
action) and, per node, the lengths of notarized chains it has seen. -/
@[ext]
structure St where
  votes : Node → Epoch → Option Block
  seen : Node → Nat → Prop

tla_var St votes seen

/-- Quorums: a strict majority of the first `n` nodes. -/
def Quorum (n : Nat) (Q : Finset Node) : Prop :=
  Q ⊆ Finset.range n ∧ 2 * Q.card > n

/-- Any two quorums intersect. -/
theorem quorum_overlap {n : Nat} {Q1 Q2 : Finset Node}
    (h1 : Quorum n Q1) (h2 : Quorum n Q2) : ∃ a : Node, a ∈ Q1 ∧ a ∈ Q2 := by
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

/-- Block `b` is notarized: a quorum of nodes voted for it in its epoch. -/
def Notarized (n : Nat) (s : St) (b : Block) : Prop :=
  ∃ Q : Finset Node, Quorum n Q ∧ ∀ i : Node, i ∈ Q → s.votes i b.epoch = some b

/-- The chain ending at `b` is notarized: every non-genesis block on it is
notarized. -/
def ChainNotarized (n : Nat) (s : St) (b : Block) : Prop :=
  ∀ c : Block, c ∈ b.ancestors → c ≠ Block.genesis → Notarized n s c

/-- Initially: no votes, and every node has seen the (genesis) chain of
length 0. -/
@[simp] def Init : Tla.StatePred St :=
  [p| (∀ i : Node, ∀ e : Epoch, votes[i][e] = none) ∧
      (∀ i : Node, seen[i][0])]

/-- The state after node `i` votes for `b` in epoch `b.epoch`. -/
def vote (s : St) (i : Node) (b : Block) : St :=
  { s with
    votes := Function.update s.votes i (Function.update (s.votes i) b.epoch (some b)) }

/-- The state after a notarization of `b` becomes visible: every node has
now seen a notarized chain of length `b.length`. -/
def notarize (s : St) (b : Block) : St :=
  { s with seen := fun j k => s.seen j k ∨ k = b.length }

/-- Streamlet's vote rule (Appendix A, §A.2): during epoch `e = b.epoch`,
node `i` votes for the leader's proposal `b` iff it extends one of the
longest notarized chains `i` has seen (`seen[i][b.length - 1]` and nothing
longer), provided `i` has not voted in this or any later epoch yet. -/
@[simp] def Vote (i : Node) (b : Block) : Tla.Action St :=
  [a| 0 < b.epoch ∧
      votes[i][b.epoch] = none ∧
      (∀ e' : Epoch, b.epoch < e' → votes[i][e'] = none) ∧
      seen[i][b.length - 1] ∧
      (∀ k : Nat, seen[i][k] → k ≤ b.length - 1) ∧
      votes' = Function.update votes i (Function.update (votes i) b.epoch (some b)) ∧
      seen' = seen]

/-- Notarization becomes visible once a quorum has voted for `b`. -/
@[simp] def Notarize (n : Nat) (b : Block) : Tla.Action St :=
  [a| (∃ Q : Finset Node, Quorum n Q ∧ (∀ i : Node, i ∈ Q → votes[i][b.epoch] = some b)) ∧
      (seen' = fun j k => seen[j][k] ∨ k = b.length) ∧
      votes' = votes]

@[simp] def Next (n : Nat) : Tla.Action St :=
  [a| ∃ i : Node, ∃ b : Block, Vote i b ∨ Notarize n b]

def Spec (n : Nat) : Tla.Pred St := [t| Init ∧ □[Next n]_vars]

/-! ## The invariants -/

/-- Every recorded vote is for a block whose epoch matches the voting
epoch. -/
@[simp] def VotedEpoch (s : St) : Prop :=
  ∀ i : Node, ∀ e : Epoch, ∀ b : Block, s.votes i e = some b → b.epoch = e

/-- Votes only happen in positive epochs (never for genesis). -/
@[simp] def VotedPosEpoch (s : St) : Prop :=
  ∀ i : Node, ∀ e : Epoch, ∀ b : Block, s.votes i e = some b → 0 < e

/-- Whoever voted for a block had seen its parent chain (of length
`b.length - 1`) notarized at voting time; since `seen` only grows, this
remains true forever. -/
@[simp] def VotedSeenParent (s : St) : Prop :=
  ∀ i : Node, ∀ e : Epoch, ∀ b : Block, s.votes i e = some b → s.seen i (b.length - 1)

/-- **The honest longest-chain discipline**: a node's votes are for blocks
of non-decreasing length. -/
@[simp] def VoteLenMono (s : St) : Prop :=
  ∀ i : Node, ∀ e1 e2 : Epoch, ∀ b1 b2 : Block,
    s.votes i e1 = some b1 → s.votes i e2 = some b2 → e1 < e2 → b1.length ≤ b2.length

@[simp] def Inv (s : St) : Prop :=
  VotedEpoch s ∧ VotedPosEpoch s ∧ VotedSeenParent s ∧ VoteLenMono s

/-! ## The invariants are inductive -/

/-- Voting writes only the new entry. -/
lemma vote_votes_self {s : St} {i : Node} {b : Block} :
    (vote s i b).votes i b.epoch = some b := by
  simp [vote, Function.update]

/-- Voting leaves every other entry alone. -/
lemma vote_votes_of_ne {s : St} {i : Node} {b : Block} {j : Node} {e : Epoch}
    (h : j ≠ i ∨ e ≠ b.epoch) : (vote s i b).votes j e = s.votes j e := by
  rcases h with hji | he
  · simp [vote, Function.update, hji]
  · by_cases hji' : j = i
    · subst j
      simp [vote, Function.update, he]
    · simp [vote, Function.update, hji']

theorem votedEpoch_vote {s : St} {i : Node} {b : Block} (hInv : Inv s) :
    VotedEpoch (vote s i b) := by
  intro j e' b' hv'
  by_cases hje : j = i ∧ e' = b.epoch
  · rcases hje with ⟨rfl, rfl⟩
    have hb' : b' = b := (Option.some.inj (by simpa [vote, Function.update] using hv')).symm
    subst b'
    rfl
  · have hv'' : s.votes j e' = some b' :=
      vote_votes_of_ne (not_and_or.mp hje) ▸ hv'
    exact hInv.1 j e' b' hv''

theorem votedPosEpoch_vote {s : St} {i : Node} {b : Block}
    (hpos : 0 < b.epoch) (hInv : Inv s) :
    VotedPosEpoch (vote s i b) := by
  intro j e' b' hv'
  by_cases hje : j = i ∧ e' = b.epoch
  · rcases hje with ⟨rfl, rfl⟩
    have hb' : b' = b := (Option.some.inj (by simpa [vote, Function.update] using hv')).symm
    subst b'
    exact hpos
  · have hv'' : s.votes j e' = some b' :=
      vote_votes_of_ne (not_and_or.mp hje) ▸ hv'
    exact hInv.2.1 j e' b' hv''

theorem votedSeenParent_vote {s : St} {i : Node} {b : Block}
    (hSeen : s.seen i (b.length - 1)) (hInv : Inv s) :
    VotedSeenParent (vote s i b) := by
  intro j e' b' hv'
  by_cases hje : j = i ∧ e' = b.epoch
  · rcases hje with ⟨rfl, rfl⟩
    have hb' : b' = b := (Option.some.inj (by simpa [vote, Function.update] using hv')).symm
    subst b'
    exact hSeen
  · have hv'' : s.votes j e' = some b' :=
      vote_votes_of_ne (not_and_or.mp hje) ▸ hv'
    exact hInv.2.2.1 j e' b' hv''

/-- `a - 1 ≤ b - 1` with both positive gives `a ≤ b`. -/
lemma pred_le_pred_of_le {a b : Nat} (ha : 0 < a) (hb : 0 < b)
    (h : a - 1 ≤ b - 1) : a ≤ b := by
  have ha' : 1 ≤ a := Nat.succ_le_of_lt ha
  have hb' : 1 ≤ b := Nat.succ_le_of_lt hb
  have h1 : a - 1 + 1 ≤ b - 1 + 1 := Nat.add_le_add_right h 1
  have h2 : a ≤ b - 1 + 1 := by
    rw [Nat.sub_add_cancel ha'] at h1
    exact h1
  have h3 : b - 1 + 1 ≤ b := by rw [Nat.sub_add_cancel hb']
  exact le_trans h2 h3

theorem voteLenMono_vote {s : St} {i : Node} {b : Block}
    (hbpos : 0 < b.length)
    (hNoLater : ∀ e' : Epoch, b.epoch < e' → s.votes i e' = none)
    (hLongest : ∀ k : Nat, s.seen i k → k ≤ b.length - 1)
    (hInv : Inv s) : VoteLenMono (vote s i b) := by
  intro j e1 e2 b1 b2 hv1 hv2 hlt
  by_cases he2 : e2 = b.epoch
  · subst e2
    by_cases hji : j = i
    · subst j
      have hb2 : b2 = b := (Option.some.inj (by simpa [vote, Function.update] using hv2)).symm
      subst b2
      have hne1 : e1 ≠ b.epoch := ne_of_lt hlt
      have hv1' : s.votes i e1 = some b1 := vote_votes_of_ne (Or.inr hne1) ▸ hv1
      have hse : s.seen i (b1.length - 1) := hInv.2.2.1 i e1 b1 hv1'
      have hle : b1.length - 1 ≤ b.length - 1 := hLongest (b1.length - 1) hse
      have hb1ne : b1 ≠ Block.genesis :=
        Block.epoch_pos_ne_genesis (by
          have h0 : 0 < e1 := hInv.2.1 i e1 b1 hv1'
          have he : b1.epoch = e1 := hInv.1 i e1 b1 hv1'
          simpa [he] using h0)
      exact pred_le_pred_of_le (Block.length_pos_of_ne_genesis hb1ne) hbpos hle
    · have hv1' : s.votes j e1 = some b1 := vote_votes_of_ne (Or.inl hji) ▸ hv1
      have hv2' : s.votes j b.epoch = some b2 := vote_votes_of_ne (Or.inl hji) ▸ hv2
      exact hInv.2.2.2 j e1 b.epoch b1 b2 hv1' hv2' hlt
  · by_cases he1 : e1 = b.epoch
    · subst e1
      by_cases hji : j = i
      · subst j
        have hb1 : b1 = b := (Option.some.inj (by simpa [vote, Function.update] using hv1)).symm
        subst b1
        have hgt : b.epoch < e2 := by omega
        have hnone : s.votes i e2 = none := hNoLater e2 hgt
        have hne2 : e2 ≠ b.epoch := (ne_of_lt hgt).symm
        have hv2' : s.votes i e2 = some b2 := vote_votes_of_ne (Or.inr hne2) ▸ hv2
        rw [hnone] at hv2'
        cases hv2'
      · have hv1' : s.votes j b.epoch = some b1 := vote_votes_of_ne (Or.inl hji) ▸ hv1
        have hv2' : s.votes j e2 = some b2 := vote_votes_of_ne (Or.inl hji) ▸ hv2
        exact hInv.2.2.2 j b.epoch e2 b1 b2 hv1' hv2' hlt
    · have hv1' : s.votes j e1 = some b1 := vote_votes_of_ne (Or.inr he1) ▸ hv1
      have hv2' : s.votes j e2 = some b2 := vote_votes_of_ne (Or.inr he2) ▸ hv2
      exact hInv.2.2.2 j e1 e2 b1 b2 hv1' hv2' hlt

theorem votedEpoch_notarize {s : St} {b : Block} (hInv : Inv s) :
    VotedEpoch (notarize s b) := by
  intro j e' b' hv'
  exact hInv.1 j e' b' (by simpa [notarize] using hv')

theorem votedPosEpoch_notarize {s : St} {b : Block} (hInv : Inv s) :
    VotedPosEpoch (notarize s b) := by
  intro j e' b' hv'
  exact hInv.2.1 j e' b' (by simpa [notarize] using hv')

theorem votedSeenParent_notarize {s : St} {b : Block} (hInv : Inv s) :
    VotedSeenParent (notarize s b) := by
  intro j e' b' hv'
  simp [notarize]
  left
  exact hInv.2.2.1 j e' b' (by simpa [notarize] using hv')

theorem voteLenMono_notarize {s : St} {b : Block} (hInv : Inv s) :
    VoteLenMono (notarize s b) := by
  intro j e1 e2 b1 b2 hv1 hv2 hlt
  exact hInv.2.2.2 j e1 e2 b1 b2
    (by simpa [notarize] using hv1) (by simpa [notarize] using hv2) hlt

theorem vote_inv {s s' : St} {i : Node} {b : Block}
    (hstep : Vote i b s s') (hInv : Inv s) : Inv s' := by
  tla_unfold
  rcases hstep with ⟨hpos, _, hNoLater, hSeen, hLongest, hVotes', hSeen'⟩
  have hs' : s' = vote s i b := by
    ext <;> simp [vote, hVotes', hSeen']
  subst s'
  constructor
  · exact votedEpoch_vote hInv
  · constructor
    · exact votedPosEpoch_vote hpos hInv
    · constructor
      · exact votedSeenParent_vote hSeen hInv
      · exact voteLenMono_vote
          (Block.length_pos_of_ne_genesis (Block.epoch_pos_ne_genesis hpos))
          hNoLater hLongest hInv

theorem notarize_inv {n : Nat} {s s' : St} {b : Block}
    (hstep : Notarize n b s s') (hInv : Inv s) : Inv s' := by
  tla_unfold
  rcases hstep with ⟨hQ, hSeen', hVotes'⟩
  have hs' : s' = notarize s b := by
    ext <;> simp [notarize, hSeen', hVotes']
  subst s'
  constructor
  · exact votedEpoch_notarize hInv
  · constructor
    · exact votedPosEpoch_notarize hInv
    · constructor
      · exact votedSeenParent_notarize hInv
      · exact voteLenMono_notarize hInv

theorem init_inv {s : St} (h : Init s) : Inv s := by
  tla_unfold
  rcases h with ⟨hNoVotes, _⟩
  constructor
  · intro i e' b' hv'
    simp [hNoVotes i e'] at hv'
  · constructor
    · intro i e' b' hv'
      simp [hNoVotes i e'] at hv'
    · constructor
      · intro i e' b' hv'
        simp [hNoVotes i e'] at hv'
      · intro i e1 e2 b1 b2 hv1 hv2 hlt
        simp [hNoVotes i e1] at hv1

theorem next_inv (n : Nat) : ∀ s s' : St, Next n s s' → Inv s → Inv s' := by
  intro s s' hstep hInv
  unfold Next at hstep
  rcases hstep with ⟨i, b, hstep⟩
  rcases hstep with hv | hn
  · exact vote_inv hv hInv
  · exact notarize_inv hn hInv

theorem stutter_inv : ∀ s s' : St, vars s' = vars s → Inv s → Inv s' := by
  intro s s' hstut hInv
  tla_unfold
  have hs' : s' = s := by simpa using hstut
  subst s'
  exact hInv

/-- Every reachable state satisfies the invariants. -/
theorem spec_entails_inv (n : Nat) :
    (Tla.tlaAnd (Tla.statePred Init) (Tla.stutAlways (Next n) vars)) ⊢ □ ⌜ Inv ⌝ := by
  apply Tla.init_invariant_stut
  · intro s hs
    exact init_inv hs
  · intro s s' hstep hInv
    rcases hstep with hnext | hstut
    · exact next_inv n s s' hnext hInv
    · exact stutter_inv s s' hstut hInv

/-! ## Safety: the consistency proof -/

/-- **Lemma 10**: at most one notarized block per epoch — two notarized
blocks of the same epoch share a voter (quorum overlap), and a node votes
at most once per epoch. -/
theorem unique_notarization {n : Nat} {s : St} {b b' : Block}
    (hN : Notarized n s b) (hN' : Notarized n s b') (hE : b.epoch = b'.epoch) : b = b' := by
  rcases hN with ⟨Q, hQ, hQv⟩
  rcases hN' with ⟨Q', hQ', hQ'v⟩
  rcases quorum_overlap hQ hQ' with ⟨i, hiQ, hiQ'⟩
  have h1 : s.votes i b.epoch = some b := hQv i hiQ
  have h2 : s.votes i b'.epoch = some b' := hQ'v i hiQ'
  rw [← hE] at h2
  exact Option.some.inj (h1.symm.trans h2)

/-- **Lemma 11/14**: a finality witness `(b0, b, b2)` — three adjacent
notarized blocks with consecutive epochs — blocks any conflicting
notarized block at `b`'s length. -/
theorem finality_no_conflict {n : Nat} {s : St} (hInv : Inv s)
    {e : Nat} {b0 b b2 : Block}
    (hEpos : 0 < e) (hB0 : b0.epoch = e) (hB : b.epoch = e + 1) (hB2 : b2.epoch = e + 2)
    (hAdj1 : b = Block.block b0 (e + 1)) (hAdj2 : b2 = Block.block b (e + 2))
    (hChain : ChainNotarized n s b2)
    {c : Block} (hc : c ≠ b) (hclen : c.length = b.length)
    (hNc : Notarized n s c) : False := by
  have hb0e : 0 < b0.epoch := by rw [hB0]; exact hEpos
  have hb0ne : b0 ≠ Block.genesis := Block.epoch_pos_ne_genesis hb0e
  have hbe : 0 < b.epoch := by rw [hB]; omega
  have hbne : b ≠ Block.genesis := Block.epoch_pos_ne_genesis hbe
  have hb2e : 0 < b2.epoch := by rw [hB2]; omega
  have hb2ne : b2 ≠ Block.genesis := Block.epoch_pos_ne_genesis hb2e
  have hb0mem : b0 ∈ b2.ancestors := by
    rw [hAdj2, hAdj1]
    exact Block.mem_ancestors_of_mem_parent (Block.parent_mem_ancestors (p := b0) (e := e + 1))
  have hbmem : b ∈ b2.ancestors := by
    rw [hAdj2]
    exact Block.mem_ancestors_of_mem_parent (Block.mem_ancestors_self b)
  have hb2mem : b2 ∈ b2.ancestors := Block.mem_ancestors_self b2
  have hN0 : Notarized n s b0 := hChain b0 hb0mem hb0ne
  have hN1 : Notarized n s b := hChain b hbmem hbne
  have hN2 : Notarized n s b2 := hChain b2 hb2mem hb2ne
  have hlen1 : b.length = b0.length + 1 := by simp [Block.length, hAdj1]
  have hlen2 : b2.length = b.length + 1 := by simp [Block.length, hAdj2]
  by_cases h1 : c.epoch = e
  · have hc0 : c = b0 := unique_notarization hNc hN0 (by rw [h1, hB0])
    subst c
    omega
  · by_cases h2 : c.epoch = e + 1
    · have hcb : c = b := unique_notarization hNc hN1 (by rw [h2, hB])
      exact hc hcb
    · by_cases h3 : c.epoch = e + 2
      · have hcb2 : c = b2 := unique_notarization hNc hN2 (by rw [h3, hB2])
        subst c
        omega
      · by_cases hlt : c.epoch < e
        · -- c notarized before the finality chain could even start growing
          rcases hNc with ⟨Q, hQ, hQv⟩
          rcases hN0 with ⟨Q0, hQ0, hQ0v⟩
          rcases quorum_overlap hQ hQ0 with ⟨i, hiQ, hiQ0⟩
          have hv1 : s.votes i c.epoch = some c := hQv i hiQ
          have hv2 : s.votes i e = some b0 := by
            rw [← hB0]
            exact hQ0v i hiQ0
          have hmono : c.length ≤ b0.length := hInv.2.2.2 i c.epoch e c b0 hv1 hv2 hlt
          have hmono' : b0.length + 1 ≤ b0.length := by
            rw [← hlen1, ← hclen]
            exact hmono
          omega
        · -- c notarized after the finality chain: contradict length
          -- monotonicity against the common voter of c and b2
          have hgt : e + 2 < c.epoch := by omega
          rcases hNc with ⟨Q, hQ, hQv⟩
          rcases hN2 with ⟨Q2, hQ2, hQ2v⟩
          rcases quorum_overlap hQ hQ2 with ⟨i, hiQ, hiQ2⟩
          have hv1 : s.votes i (e + 2) = some b2 := by
            rw [← hB2]
            exact hQ2v i hiQ2
          have hv2 : s.votes i c.epoch = some c := hQv i hiQ
          have hmono : b2.length ≤ c.length :=
            hInv.2.2.2 i (e + 2) c.epoch b2 c hv1 hv2 hgt
          have hmono' : b.length + 1 ≤ b.length := by
            rw [← hlen2, ← hclen]
            exact hmono
          omega

/-- A block is final when it is the middle of three adjacent notarized
blocks with consecutive positive epochs on a fully notarized chain. -/
@[simp] def Finalized (n : Nat) (s : St) (e : Nat) (b0 b b2 : Block) : Prop :=
  0 < e ∧ b0.epoch = e ∧ b.epoch = e + 1 ∧ b2.epoch = e + 2 ∧
  b = Block.block b0 (e + 1) ∧ b2 = Block.block b (e + 2) ∧ ChainNotarized n s b2

/-- **Theorem 12**: two final chains are prefix-comparable — the shorter
one's middle block is the block of the longer one at the same length. -/
theorem consistency {n : Nat} {s : St} (hInv : Inv s)
    {e : Nat} {b0 b b2 : Block} (hFin : Finalized n s e b0 b b2)
    {e' : Nat} {b0' b' b2' : Block} (hFin' : Finalized n s e' b0' b' b2')
    (hle : b.length ≤ b'.length) :
    b'.atLen b.length = some b := by
  rcases hFin with ⟨hEpos, hB0, hB, hB2, hAdj1, hAdj2, hChain⟩
  rcases hFin' with ⟨_, _, _, _, _, hAdj2', hChain'⟩
  by_contra hne
  have hc' : b'.atLen b.length ≠ none := Block.atLen_ne_none b' b.length hle
  rcases Option.ne_none_iff_exists.mp hc' with ⟨c, hc⟩
  have hc0 : b'.atLen b.length = some c := hc.symm
  have hcne : c ≠ b := by
    intro hcb
    subst c
    exact hne hc0
  have hcMem : c ∈ b'.ancestors := Block.atLen_mem b' b.length c hc0
  have hclen : c.length = b.length := Block.atLen_len_of_eq b' b.length c hc0
  have hcMem2' : c ∈ b2'.ancestors := by
    rw [hAdj2']
    exact Block.mem_ancestors_of_mem_parent hcMem
  have hcneG : c ≠ Block.genesis := by
    intro hg
    subst c
    have h0 : b.length = 0 := by simpa [Block.length] using hclen.symm
    have hbpos : 0 < b.length := by
      rw [hAdj1]
      simp [Block.length]
    omega
  have hNc : Notarized n s c := hChain' c hcMem2' hcneG
  exact finality_no_conflict hInv hEpos hB0 hB hB2 hAdj1 hAdj2 hChain hcne hclen hNc

/-- The canonical safety theorem: any two final blocks in a reachable state
agree on the shorter chain's prefix. -/
@[simp] def Consistency (n : Nat) (s : St) : Prop :=
  ∀ e : Nat, ∀ b0 b b2 : Block, Finalized n s e b0 b b2 →
  ∀ e' : Nat, ∀ b0' b' b2' : Block, Finalized n s e' b0' b' b2' →
    b.length ≤ b'.length → b'.atLen b.length = some b

theorem consistency_of_inv {n : Nat} {s : St} (hInv : Inv s) : Consistency n s := by
  intro e b0 b b2 hFin e' b0' b' b2' hFin' hle
  exact consistency hInv hFin hFin' hle

/-- `Init ∧ □[Next]_vars` entails consistency at every step. -/
theorem spec_entails_consistency (n : Nat) :
    (Tla.tlaAnd (Tla.statePred Init) (Tla.stutAlways (Next n) vars)) ⊢ □ ⌜ Consistency n ⌝ := by
  intro e he
  have hInv : Tla.always (Tla.statePred Inv) e := spec_entails_inv n e he
  intro k
  exact consistency_of_inv (hInv k)

end TlaDsl.Examples.Streamlet
