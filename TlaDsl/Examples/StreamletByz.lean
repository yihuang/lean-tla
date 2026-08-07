import TlaDsl.Examples.Streamlet
import TlaDsl.Tactic
import TlaDsl.TlaVar

open scoped Tla

/-! # Streamlet under Byzantine faults

The roadmap's Byzantine item: the same block-tree model as
`Streamlet.lean`, but with `f < n/3` Byzantine nodes. The differences:

* **quorums of size `> 2n/3`** (`QuorumByz`) instead of strict majority, so
  two notarizing quorums share a node — and, with fewer than `n/3`
  Byzantine nodes, that common node is **honest** (`quorum_overlap_honest`);
* the protocol actions are guarded by `i ∉ Byz` (the `[c| ...]` pattern),
  so Byzantine nodes are unconstrained by the spec — their pre-existing
  votes can be anything;
* the invariant is the honest-restricted one (`VoteLenMonoByz`: honest
  votes are for non-decreasing lengths), and the consistency theorem
  follows by the same finality-chain argument as the honest model, using
  the honest common voter at every overlap.

This is the safety core of BFT Streamlet: two final chains are
prefix-comparable even though Byzantine nodes may vote arbitrarily.
-/

namespace TlaDsl.Examples.StreamletByz

abbrev St := Streamlet.St
abbrev Node := Streamlet.Node
abbrev Epoch := Streamlet.Epoch

open TlaDsl.Examples.Streamlet (votes seen Block)

/-! ## Byzantine quorums and the honest-overlap -/

/-- A Byzantine quorum: more than `2n/3` of the `n` nodes. -/
def QuorumByz (n : Nat) (Q : Finset Node) : Prop :=
  Q ⊆ Finset.range n ∧ 3 * Q.card > 2 * n

/-- The Byzantine bound: fewer than `n/3` Byzantine nodes. -/
def ByzOk (n : Nat) (Byz : Finset Node) : Prop :=
  Byz ⊆ Finset.range n ∧ 3 * Byz.card < n

/-- Two Byzantine quorums intersect. -/
theorem quorum_overlap {n : Nat} {Q1 Q2 : Finset Node}
    (h1 : QuorumByz n Q1) (h2 : QuorumByz n Q2) : ∃ a : Node, a ∈ Q1 ∧ a ∈ Q2 := by
  rcases h1 with ⟨h1sub, h1maj⟩
  rcases h2 with ⟨h2sub, h2maj⟩
  by_contra h
  have hinter0 : (Q1 ∩ Q2).card = 0 := by
    rw [Finset.card_eq_zero]
    ext a
    constructor
    · intro ha
      rcases Finset.mem_inter.mp ha with ⟨ha1, ha2⟩
      exact False.elim (h ⟨a, ha1, ha2⟩)
    · intro ha
      simp at ha
  have hle : Q1.card + Q2.card ≤ n := by
    have hsub : Q1 ∪ Q2 ⊆ Finset.range n := by
      intro a ha
      rcases Finset.mem_union.mp ha with ha1 | ha2
      · exact h1sub ha1
      · exact h2sub ha2
    have hcard : (Q1 ∪ Q2).card ≤ n := by
      simpa using Finset.card_le_card hsub
    have hcu : (Q1 ∪ Q2).card = Q1.card + Q2.card - (Q1 ∩ Q2).card :=
      Finset.card_union (s := Q1) (t := Q2)
    have hc : (Q1 ∪ Q2).card = Q1.card + Q2.card := by
      simpa [hinter0] using hcu
    exact le_trans (le_of_eq hc.symm) hcard
  have hmul : 4 * n < 3 * (Q1.card + Q2.card) := by omega
  have hc : 3 * (Q1.card + Q2.card) ≤ 3 * n := by
    exact Nat.mul_le_mul_left 3 hle
  omega

/-- Two Byzantine quorums share an **honest** node: the intersection is
larger than the Byzantine set. -/
theorem quorum_overlap_honest {n : Nat} {Byz Q1 Q2 : Finset Node}
    (hByz : ByzOk n Byz) (h1 : QuorumByz n Q1) (h2 : QuorumByz n Q2) :
    ∃ i : Node, i ∉ Byz ∧ i ∈ Q1 ∧ i ∈ Q2 := by
  rcases quorum_overlap h1 h2 with ⟨a, ha1, ha2⟩
  by_contra h
  -- every common node is Byzantine
  have hsub : Q1 ∩ Q2 ⊆ Byz := by
    intro a ha
    rcases Finset.mem_inter.mp ha with ⟨ha1, ha2⟩
    by_contra hnb
    exact h ⟨a, hnb, ha1, ha2⟩
  have hcard : (Q1 ∩ Q2).card ≤ Byz.card := Finset.card_le_card hsub
  rcases h1 with ⟨h1sub, h1maj⟩
  rcases h2 with ⟨h2sub, h2maj⟩
  rcases hByz with ⟨_, hb⟩
  -- `3 * |Q1 ∩ Q2| > n` (from the quorum sizes) but `≤ 3 * |Byz| < n`
  have hbig : n < 3 * (Q1 ∩ Q2).card := by
    have hcu : (Q1 ∪ Q2).card = Q1.card + Q2.card - (Q1 ∩ Q2).card :=
      Finset.card_union (s := Q1) (t := Q2)
    have hunion_le : (Q1 ∪ Q2).card ≤ n := by
      have hsub : Q1 ∪ Q2 ⊆ Finset.range n := by
        intro a ha
        rcases Finset.mem_union.mp ha with ha1 | ha2
        · exact h1sub ha1
        · exact h2sub ha2
      simpa using Finset.card_le_card hsub
    have hmul1 : 3 * (Q1.card + Q2.card) > 4 * n := by omega
    omega
  have hsmall : 3 * (Q1 ∩ Q2).card ≤ 3 * Byz.card := by
    exact Nat.mul_le_mul_left 3 hcard
  omega

/-! ## The Byzantine model -/

/-- `b` is notarized by epoch `e`: a Byzantine quorum voted for it. -/
def NotarizedBy (n : Nat) (s : St) (b : Block) (e : Epoch) : Prop :=
  ∃ Q : Finset Node, QuorumByz n Q ∧
    ∀ i : Node, i ∈ Q → s.votes i e = some b

def Notarized (n : Nat) (s : St) (b : Block) : Prop :=
  ∃ Q : Finset Node, QuorumByz n Q ∧
    ∀ i : Node, i ∈ Q → s.votes i b.epoch = some b

/-- The chain ending at `b` is notarized by epoch `e`. -/
def ChainNotarizedBy (n : Nat) (s : St) (b : Block) (e : Epoch) : Prop :=
  ∀ C : Block, C ∈ b.ancestors → C ≠ Streamlet.Block.genesis → NotarizedBy n s C e

def ChainNotarized (n : Nat) (s : St) (b : Block) : Prop :=
  ∀ C : Block, C ∈ b.ancestors → C ≠ Streamlet.Block.genesis → Notarized n s C

/-- Streamlet's vote rule, guarded by honesty (`i ∉ Byz`), with Byzantine
notarizations for the notarization action. -/
@[simp] def Vote (Byz : Finset Node) (i : Node) (b : Block) : Tla.Action St :=
  [a| i ∉ Byz ∧ 0 < b.epoch ∧
      votes[i][b.epoch] = none ∧
      (∀ e' : Epoch, b.epoch < e' → votes[i][e'] = none) ∧
      seen[i][b.length - 1] ∧
      (∀ k : Nat, seen[i][k] → k ≤ b.length - 1) ∧
      votes' = Function.update votes i (Function.update (votes i) b.epoch (some b)) ∧
      seen' = seen]

/-- Notarization becomes visible once a Byzantine quorum has voted. -/
@[simp] def Notarize (n : Nat) (b : Block) : Tla.Action St :=
  [a| (∃ Q : Finset Node, QuorumByz n Q ∧ (∀ i : Node, i ∈ Q → votes[i][b.epoch] = some b)) ∧
      (seen' = fun j k => seen[j][k] ∨ k = b.length) ∧
      votes' = votes]

@[simp] def Next (Byz : Finset Node) (n : Nat) : Tla.Action St :=
  [a| ∃ i : Node, i ∉ Byz ∧ ∃ b : Block, Vote Byz i b ∨ Notarize n b]

/-- The state after node `i` votes for `b`. -/
def vote (s : St) (i : Node) (b : Block) : St :=
  Streamlet.vote s i b

lemma vote_votes_self (s : St) (i : Node) (b : Block) :
    (vote s i b).votes i b.epoch = some b :=
  Streamlet.vote_votes_self

lemma vote_votes_of_ne (s : St) (i : Node) (b : Block) {j : Node} {e : Epoch}
    (h : j ≠ i ∨ e ≠ b.epoch) : (vote s i b).votes j e = s.votes j e :=
  Streamlet.vote_votes_of_ne h

/-- The state after a notarization: `b`'s length becomes seen. -/
def notarize (s : St) (b : Block) : St :=
  { s with seen := fun j k => s.seen j k ∨ k = b.length }

/-! ## The honest-restricted invariants -/

def VotedEpochByz (Byz : Finset Node) (s : St) : Prop :=
  ∀ i : Node, i ∉ Byz → ∀ e : Epoch, ∀ b : Block, s.votes i e = some b → b.epoch = e

def VotedPosEpochByz (Byz : Finset Node) (s : St) : Prop :=
  ∀ i : Node, i ∉ Byz → ∀ e : Epoch, ∀ b : Block, s.votes i e = some b → 0 < e

def VotedSeenParentByz (Byz : Finset Node) (s : St) : Prop :=
  ∀ i : Node, i ∉ Byz → ∀ e : Epoch, ∀ b : Block,
    s.votes i e = some b → s.seen i (b.length - 1)

def VoteLenMonoByz (Byz : Finset Node) (s : St) : Prop :=
  ∀ i : Node, i ∉ Byz → ∀ e1 e2 : Epoch, ∀ b1 b2 : Block,
    s.votes i e1 = some b1 → s.votes i e2 = some b2 → e1 < e2 → b1.length ≤ b2.length

/-- The honest-restricted invariant: Byzantine votes are unconstrained. -/
def InvByz (Byz : Finset Node) (s : St) : Prop :=
  VotedEpochByz Byz s ∧ VotedPosEpochByz Byz s ∧ VotedSeenParentByz Byz s ∧ VoteLenMonoByz Byz s

/-! ## The invariants are inductive -/

theorem votedEpochByz_vote {s : St} {i : Node} {b : Block} {Byz : Finset Node}
    (hi : i ∉ Byz) (hInv : InvByz Byz s) :
    VotedEpochByz Byz (vote s i b) := by
  intro j hj e' b' hv'
  by_cases hje : j = i ∧ e' = b.epoch
  · rcases hje with ⟨rfl, rfl⟩
    have hb' : b' = b := (Option.some.inj (by simpa [vote_votes_self] using hv')).symm
    subst b'
    rfl
  · have hv'' : s.votes j e' = some b' :=
      vote_votes_of_ne s i b (not_and_or.mp hje) ▸ hv'
    exact hInv.1 j hj e' b' hv''

theorem votedPosEpochByz_vote {s : St} {i : Node} {b : Block} {Byz : Finset Node}
    (hi : i ∉ Byz) (hpos : 0 < b.epoch) (hInv : InvByz Byz s) :
    VotedPosEpochByz Byz (vote s i b) := by
  intro j hj e' b' hv'
  by_cases hje : j = i ∧ e' = b.epoch
  · rcases hje with ⟨rfl, rfl⟩
    have hb' : b' = b := (Option.some.inj (by simpa [vote_votes_self] using hv')).symm
    subst b'
    exact hpos
  · have hv'' : s.votes j e' = some b' :=
      vote_votes_of_ne s i b (not_and_or.mp hje) ▸ hv'
    exact hInv.2.1 j hj e' b' hv''

theorem votedSeenParentByz_vote {s : St} {i : Node} {b : Block} {Byz : Finset Node}
    (hi : i ∉ Byz) (hSeen : s.seen i (b.length - 1)) (hInv : InvByz Byz s) :
    VotedSeenParentByz Byz (vote s i b) := by
  intro j hj e' b' hv'
  by_cases hje : j = i ∧ e' = b.epoch
  · rcases hje with ⟨rfl, rfl⟩
    have hb' : b' = b := (Option.some.inj (by simpa [vote_votes_self] using hv')).symm
    subst b'
    exact hSeen
  · have hv'' : s.votes j e' = some b' :=
      vote_votes_of_ne s i b (not_and_or.mp hje) ▸ hv'
    exact hInv.2.2.1 j hj e' b' hv''

theorem voteLenMonoByz_vote {s : St} {i : Node} {b : Block} {Byz : Finset Node}
    (hi : i ∉ Byz)
    (hbpos : 0 < b.length)
    (hNoLater : ∀ e' : Epoch, b.epoch < e' → s.votes i e' = none)
    (hLongest : ∀ k : Nat, s.seen i k → k ≤ b.length - 1)
    (hInv : InvByz Byz s) : VoteLenMonoByz Byz (vote s i b) := by
  intro j hj e1 e2 b1 b2 hv1 hv2 hlt
  by_cases he2 : e2 = b.epoch
  · subst e2
    by_cases hji : j = i
    · subst j
      have hb2 : b2 = b := (Option.some.inj (by simpa [vote_votes_self] using hv2)).symm
      subst b2
      have hne1 : e1 ≠ b.epoch := ne_of_lt hlt
      have hv1' : s.votes i e1 = some b1 := vote_votes_of_ne s i b (Or.inr hne1) ▸ hv1
      have hse : s.seen i (b1.length - 1) := hInv.2.2.1 i hi e1 b1 hv1'
      have hle : b1.length - 1 ≤ b.length - 1 := hLongest (b1.length - 1) hse
      have hb1ne : b1 ≠ Block.genesis :=
        Block.epoch_pos_ne_genesis (by
          have h0 : 0 < e1 := hInv.2.1 i hi e1 b1 hv1'
          have he : b1.epoch = e1 := hInv.1 i hi e1 b1 hv1'
          simpa [he] using h0)
      exact Streamlet.pred_le_pred_of_le (Block.length_pos_of_ne_genesis hb1ne) hbpos hle
    · have hv1' : s.votes j e1 = some b1 := vote_votes_of_ne s i b (Or.inl hji) ▸ hv1
      have hv2' : s.votes j b.epoch = some b2 := vote_votes_of_ne s i b (Or.inl hji) ▸ hv2
      exact hInv.2.2.2 j hj e1 b.epoch b1 b2 hv1' hv2' hlt
  · by_cases he1 : e1 = b.epoch
    · subst e1
      by_cases hji : j = i
      · subst j
        have hb1 : b1 = b := (Option.some.inj (by simpa [vote_votes_self] using hv1)).symm
        subst b1
        have hgt : b.epoch < e2 := by omega
        have hnone : s.votes i e2 = none := hNoLater e2 hgt
        have hne2 : e2 ≠ b.epoch := (ne_of_lt hgt).symm
        have hv2' : s.votes i e2 = some b2 := vote_votes_of_ne s i b (Or.inr hne2) ▸ hv2
        rw [hnone] at hv2'
        cases hv2'
      · have hv1' : s.votes j b.epoch = some b1 := vote_votes_of_ne s i b (Or.inl hji) ▸ hv1
        have hv2' : s.votes j e2 = some b2 := vote_votes_of_ne s i b (Or.inl hji) ▸ hv2
        exact hInv.2.2.2 j hj b.epoch e2 b1 b2 hv1' hv2' hlt
    · have hv1' : s.votes j e1 = some b1 := vote_votes_of_ne s i b (Or.inr he1) ▸ hv1
      have hv2' : s.votes j e2 = some b2 := vote_votes_of_ne s i b (Or.inr he2) ▸ hv2
      exact hInv.2.2.2 j hj e1 e2 b1 b2 hv1' hv2' hlt

theorem votedEpochByz_notarize {s : St} {b : Block} {Byz : Finset Node}
    (hInv : InvByz Byz s) : VotedEpochByz Byz (notarize s b) := by
  intro j hj e' b' hv'
  exact hInv.1 j hj e' b' (by simpa [notarize] using hv')

theorem votedPosEpochByz_notarize {s : St} {b : Block} {Byz : Finset Node}
    (hInv : InvByz Byz s) : VotedPosEpochByz Byz (notarize s b) := by
  intro j hj e' b' hv'
  exact hInv.2.1 j hj e' b' (by simpa [notarize] using hv')

theorem votedSeenParentByz_notarize {s : St} {b : Block} {Byz : Finset Node}
    (hInv : InvByz Byz s) : VotedSeenParentByz Byz (notarize s b) := by
  intro j hj e' b' hv'
  have hv'' : s.votes j e' = some b' := by simpa [notarize] using hv'
  have hs : s.seen j (b'.length - 1) := hInv.2.2.1 j hj e' b' hv''
  simpa [notarize] using Or.inl hs

theorem voteLenMonoByz_notarize {s : St} {b : Block} {Byz : Finset Node}
    (hInv : InvByz Byz s) : VoteLenMonoByz Byz (notarize s b) := by
  intro j hj e1 e2 b1 b2 hv1 hv2 hlt
  exact hInv.2.2.2 j hj e1 e2 b1 b2
    (by simpa [notarize] using hv1) (by simpa [notarize] using hv2) hlt

theorem vote_inv_byz {s s' : St} {i : Node} {b : Block} {Byz : Finset Node}
    (hstep : Vote Byz i b s s') (hInv : InvByz Byz s) : InvByz Byz s' := by
  tla_unfold
  rcases hstep with ⟨hi, hpos, _, hNoLater, hSeen, hLongest, hVotes', hSeen'⟩
  have hs' : s' = vote s i b := by
    cases s' with
    | mk v' se' =>
        cases s with
        | mk v0 se0 =>
            have hv' : v' = Function.update v0 i (Function.update (v0 i) b.epoch (some b)) := hVotes'
            have hse' : se' = se0 := hSeen'
            rw [hv', hse']
            rfl
  subst s'
  constructor
  · exact votedEpochByz_vote hi hInv
  · constructor
    · exact votedPosEpochByz_vote hi hpos hInv
    · constructor
      · exact votedSeenParentByz_vote hi hSeen hInv
      · exact voteLenMonoByz_vote hi
          (Block.length_pos_of_ne_genesis (Block.epoch_pos_ne_genesis hpos))
          hNoLater hLongest hInv

theorem notarize_inv_byz {n : Nat} {s s' : St} {b : Block} {Byz : Finset Node}
    (hstep : Notarize n b s s') (hInv : InvByz Byz s) : InvByz Byz s' := by
  tla_unfold
  rcases hstep with ⟨_, hSeen', hVotes'⟩
  have hs' : s' = notarize s b := by
    cases s' with
    | mk v' se' =>
        cases s with
        | mk v0 se0 =>
            have hse' : se' = fun j k => se0 j k ∨ k = b.length := hSeen'
            have hv' : v' = v0 := hVotes'
            rw [hse', hv']
            rfl
  subst s'
  constructor
  · exact votedEpochByz_notarize hInv
  · constructor
    · exact votedPosEpochByz_notarize hInv
    · constructor
      · exact votedSeenParentByz_notarize hInv
      · exact voteLenMonoByz_notarize hInv

/-! ## Byzantine consistency -/

/-- **Lemma 10 (Byzantine)**: at most one notarized block per epoch — two
notarized blocks of the same epoch share an **honest** voter, and a node
votes at most once per epoch. -/
theorem unique_notarization_byz {n : Nat} {Byz : Finset Node} (hByz : ByzOk n Byz)
    {s : St} {b b' : Block}
    (hN : Notarized n s b) (hN' : Notarized n s b') (hE : b.epoch = b'.epoch) : b = b' := by
  rcases hN with ⟨Q, hQ, hQv⟩
  rcases hN' with ⟨Q', hQ', hQ'v⟩
  rcases quorum_overlap_honest hByz hQ hQ' with ⟨i, hi, hiQ, hiQ'⟩
  have h1 : s.votes i b.epoch = some b := hQv i hiQ
  have h2 : s.votes i b'.epoch = some b' := hQ'v i hiQ'
  rw [← hE] at h2
  exact Option.some.inj (h1.symm.trans h2)

/-- A block is final when it is the middle of three adjacent notarized
blocks with consecutive positive epochs on a fully notarized chain. -/
@[simp] def FinalizedByz (n : Nat) (s : St) (e : Nat)
    (b0 b b2 : Block) : Prop :=
  0 < e ∧ b0.epoch = e ∧ b.epoch = e + 1 ∧ b2.epoch = e + 2 ∧
  b = Block.block b0 (e + 1) ∧ b2 = Block.block b (e + 2) ∧ ChainNotarized n s b2

/-- **Lemma 11/14 (Byzantine)**: a finality witness `(b0, b, b2)` blocks
any conflicting notarized block at `b`'s length — the honest-restricted
length monotonicity applies because the two quorums share an honest
voter. -/
theorem finality_no_conflict_byz {n : Nat} {Byz : Finset Node} (hByz : ByzOk n Byz)
    {s : St} (hInv : InvByz Byz s)
    {e : Nat} {b0 b b2 : Block}
    (hEpos : 0 < e) (hB0 : b0.epoch = e) (hB : b.epoch = e + 1) (hB2 : b2.epoch = e + 2)
    (hAdj1 : b = Block.block b0 (e + 1)) (hAdj2 : b2 = Block.block b (e + 2))
    (hChain : ChainNotarized n s b2)
    {c : Block} (hc : c ≠ b) (hclen : c.length = b.length)
    (hNc : Notarized n s c) : False := by
  have hb0e : 0 < b0.epoch := by rw [hB0]; exact hEpos
  have hb0ne : b0 ≠ Streamlet.Block.genesis := Block.epoch_pos_ne_genesis hb0e
  have hbe : 0 < b.epoch := by rw [hB]; omega
  have hbne : b ≠ Streamlet.Block.genesis := Block.epoch_pos_ne_genesis hbe
  have hb2e : 0 < b2.epoch := by rw [hB2]; omega
  have hb2ne : b2 ≠ Streamlet.Block.genesis := Block.epoch_pos_ne_genesis hb2e
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
  · have hc0 : c = b0 := unique_notarization_byz hByz hNc hN0 (by rw [h1, hB0])
    subst c
    omega
  · by_cases h2 : c.epoch = e + 1
    · have hcb : c = b := unique_notarization_byz hByz hNc hN1 (by rw [h2, hB])
      exact hc hcb
    · by_cases h3 : c.epoch = e + 2
      · have hcb2 : c = b2 := unique_notarization_byz hByz hNc hN2 (by rw [h3, hB2])
        subst c
        omega
      · by_cases hlt : c.epoch < e
        · -- c notarized before the finality chain could even start growing
          rcases hNc with ⟨Q, hQ, hQv⟩
          rcases hN0 with ⟨Q0, hQ0, hQ0v⟩
          rcases quorum_overlap_honest hByz hQ hQ0 with ⟨i, hi, hiQ, hiQ0⟩
          have hv1 : s.votes i c.epoch = some c := hQv i hiQ
          have hv2 : s.votes i e = some b0 := by
            rw [← hB0]
            exact hQ0v i hiQ0
          have hmono : c.length ≤ b0.length := hInv.2.2.2 i hi c.epoch e c b0 hv1 hv2 hlt
          have hmono' : b0.length + 1 ≤ b0.length := by
            rw [← hlen1, ← hclen]
            exact hmono
          omega
        · -- c notarized after the finality chain: contradict length
          -- monotonicity against the common honest voter of c and b2
          have hgt : e + 2 < c.epoch := by omega
          rcases hNc with ⟨Q, hQ, hQv⟩
          rcases hN2 with ⟨Q2, hQ2, hQ2v⟩
          rcases quorum_overlap_honest hByz hQ hQ2 with ⟨i, hi, hiQ, hiQ2⟩
          have hv1 : s.votes i (e + 2) = some b2 := by
            rw [← hB2]
            exact hQ2v i hiQ2
          have hv2 : s.votes i c.epoch = some c := hQv i hiQ
          have hmono : b2.length ≤ c.length :=
            hInv.2.2.2 i hi (e + 2) c.epoch b2 c hv1 hv2 hgt
          have hmono' : b.length + 1 ≤ b.length := by
            rw [← hlen2, ← hclen]
            exact hmono
          omega

/-- **Theorem 12 (Byzantine)**: two final chains are prefix-comparable —
the shorter one's middle block is the block of the longer one at the same
length, even with Byzantine nodes voting arbitrarily. -/
theorem consistency_byz {n : Nat} {Byz : Finset Node} (hByz : ByzOk n Byz)
    {s : St} (hInv : InvByz Byz s)
    {e : Nat} {b0 b b2 : Block} (hFin : FinalizedByz n s e b0 b b2)
    {e' : Nat} {b0' b' b2' : Block} (hFin' : FinalizedByz n s e' b0' b' b2')
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
  have hcneG : c ≠ Streamlet.Block.genesis := by
    intro hg
    subst c
    have h0 : b.length = 0 := by simpa [Block.length] using hclen.symm
    have hbpos : 0 < b.length := by
      rw [hAdj1]
      simp [Block.length]
    omega
  have hNc : Notarized n s c := hChain' c hcMem2' hcneG
  exact finality_no_conflict_byz hByz hInv hEpos hB0 hB hB2 hAdj1 hAdj2 hChain hcne hclen hNc

/-- The canonical safety theorem: any two final blocks in a reachable
state agree on the shorter chain's prefix. -/
@[simp] def ConsistencyByz (n : Nat) (s : St) : Prop :=
  ∀ e : Nat, ∀ b0 b b2 : Block, FinalizedByz n s e b0 b b2 →
  ∀ e' : Nat, ∀ b0' b' b2' : Block, FinalizedByz n s e' b0' b' b2' →
    b.length ≤ b'.length → b'.atLen b.length = some b

theorem consistency_byz_of_inv {n : Nat} {Byz : Finset Node} (hByz : ByzOk n Byz)
    {s : St} (hInv : InvByz Byz s) : ConsistencyByz n s := by
  intro e b0 b b2 hFin e' b0' b' b2' hFin' hle
  exact consistency_byz hByz hInv hFin hFin' hle

end TlaDsl.Examples.StreamletByz
