/-
Copyright (c) 2026 lean-tla contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Case study: Streamlet protocol over the partial-sync transport

This file layers the **Streamlet protocol** on top of the transport model in
`Bft.Examples.StreamletNet`: proposals, votes, notarization, the leader
schedule, and the paper's **Fact 2** and **Fact 3** (§3.6.2).

Design, in service of the paper:

* **Byzantine nodes equivocate.** Honest behavior is the guarded actions
  `Propose` (the epoch's leader proposes once, on a longest notarized chain)
  and `VoteH` (first vote of the epoch, on the leader's proposal). A faulty
  node runs `SendB`: it broadcasts *any* well-formed message at *any* time —
  including several votes in one epoch and several proposals, the paper's
  equivocation. Authentication is by construction: a message's `src` is its
  unforgeable sender, so the proposal of epoch `e` is the one cast by `L e`
  (`castProps` records `(src, e, b)` triples and `propCast` reads the
  `L e`-row; a Byzantine node's stray `.prop` body never speaks for the
  leader). Every invariant field about a node's cast is guarded by that node
  being honest, so Byzantine sends cannot disturb them.
* **Cast histories, one-directional bridge.** `voteCast`/`propCast` are
  *defined* as membership in the monotone history variables `castVotes` /
  `castProps` (what was sent — in flight or delivered). The only
  message-level invariant is the one direction the facts need
  (`Inv.sentMem`): every in-flight or delivered message's vote/proposal is
  recorded in the histories (delivery and flight never outrun the cast).
* **Notarization** is `2f+1` distinct voters. The delivery-side notion
  (`votersSeen`/`NotarizedSeen`, used by Fact 2) counts all delivered
  votes; the cast-side notion (`votersCast`/`NotarizedCast`, used by the
  liveness machinery) counts **honest** votes only — Byzantine nodes can
  withhold but never inflate a quorum, so a late Byzantine vote for an
  old-epoch block cannot make it "notarized by" that epoch after the fact.
  `NotarizedBy s b e` — the paper's epoch-bounded notion — is "a (honest)
  quorum cast votes for `b`, and `bep b ≤ e`". This is the device that
  makes the liveness facts provable: a vote cast in epoch `bep b` cannot
  change `NotarizedBy C e` for any `e < bep b` (its own epoch is too late),
  and a Byzantine cast cannot change it at all.
* **Fact 2** (notarization implies the parent chain was notarized): among
  the `2f+1` voters of a notarized block, one is honest (`honest_in_quorum`),
  and an honest voter only votes after seeing the parent chain notarized
  (`Inv.voteSeenParent`).
* **Fact 3** (two honest consecutive leaders propose at growing lengths):
  the honest `L(e+1)` extends a longest chain notarized by epoch `e`
  (`Inv.propLongest`), and by then some chain of length ≥ `b₀.length` is
  notarized (`hseen`); hence `b₁.length > b₀.length`.
* **Shared guard.** `Propose e b` and `VoteH i b` both require `b.tail` to
  be a *longest notarized view* by the previous epoch — the three conjuncts
  (notarized in `seen`, notarized by epoch `e-1`, longest such) are bundled
  once in `LongestNotarized`.

The invariant bundle `Inv` collects the honest-vote and honest-proposal
conditions these facts rest on. Its inductiveness over the protocol actions
is proved in the same file (below).
-/
import Bft.Examples.StreamletNet

namespace Bft.Examples.StreamletProto

open Bft
open Bft.Examples.StreamletNet (Body Msg St Send Deliver Tick Next Hspec NoOverdue vars castVotesAdd castPropsAdd)
open Bft.Examples.Streamlet (Blk ValidChain bep quorum)

variable (n : ℕ) (Byz : Finset (Fin n)) (Δ GST f : ℕ) (L : ℕ → Fin n)

/-! ## Protocol predicates over the transport state -/

/-- Node `i` has cast a vote for `b`: the vote is in the monotone cast
history — by `Inv.sentMem`, equivalently the vote message has been sent
(in flight or delivered). -/
abbrev voteCast (s : St n) (i : Fin n) (b : Blk) : Prop := (i, b) ∈ s.castVotes

/-- The leader of epoch `e` has cast a proposal for `b`: the sender-stamped
history records `L e` proposing `b` in epoch `e`. A Byzantine node's stray
`.prop` body of the same epoch does not count — sources are authenticated. -/
abbrev propCast (s : St n) (e : ℕ) (b : Blk) : Prop := (L e, e, b) ∈ s.castProps

/-- Node `i`'s vote for `b` has been delivered (is in `seen`). -/
def voteMsg (s : St n) (i : Fin n) (b : Blk) : Prop :=
  ∃ m, m ∈ s.seen ∧ m.src = i ∧ m.body = Body.vote b

/-- The distinct *honest* nodes that cast a vote for `b`. The cast-side
notarization machinery counts honest votes only — Byzantine nodes can
withhold votes but never inflate a quorum (a late Byzantine vote for an
old-epoch block must not make it "notarized by" that epoch). The
delivery-side notion (`votersSeen`) counts all delivered votes; quorum
intersection (`honest_in_quorum`) is what connects the two. -/
def votersCast (s : St n) (b : Blk) : Finset (Fin n) :=
  (s.castVotes.filter fun p => p.2 = b ∧ p.1 ∉ Byz).image (fun p => p.1)

/-- The distinct nodes whose vote for `b` has been delivered. -/
def votersSeen (s : St n) (b : Blk) : Finset (Fin n) :=
  (s.seen.filter fun m => m.body = Body.vote b).image (fun m => m.src)

/-- A quorum of honest cast votes for `b`. -/
def NotarizedCast (s : St n) (b : Blk) : Prop := quorum f ≤ (votersCast n Byz s b).card

/-- A quorum of delivered votes for `b`. -/
def NotarizedSeen (s : St n) (b : Blk) : Prop := quorum f ≤ (votersSeen n s b).card

/-- Block `b` is notarized (cast) by epoch `e`: a quorum cast votes for it,
and its own epoch is at most `e`. -/
def NotarizedBy (s : St n) (b : Blk) (e : ℕ) : Prop := NotarizedCast n Byz f s b ∧ bep b ≤ e

/-- Every nonempty suffix of `c` is notarized (in `seen`). -/
def ChainNotarizedSeen (s : St n) (c : Blk) : Prop :=
  ∀ d : Blk, d ≠ [] → d <:+ c → NotarizedSeen n f s d

/-- Every nonempty suffix of `c` is notarized (cast) by epoch `e`. -/
def ChainNotarizedBy (s : St n) (c : Blk) (e : ℕ) : Prop :=
  ∀ d : Blk, d ≠ [] → d <:+ c → NotarizedBy n Byz f s d e

/-- The epoch of a round: epochs have length `2Δ`. -/
def curEpoch (Δ : ℕ) (now : ℕ) : ℕ := now / (2 * Δ)

/-- The one-directional message-to-history bridge: every in-flight or
delivered message's vote (proposal) is recorded in the cast history. This
is exactly "the histories are what was sent"; the converse direction is not
needed by any fact. Stated with body equations (no `match`) so the
transport lemmas below never case-split on a message body. -/
def SentMem (s : St n) : Prop :=
  (∀ m : Msg n, (m ∈ s.inflight ∨ m ∈ s.seen) → ∀ b : Blk,
      m.body = Body.vote b → (m.src, b) ∈ s.castVotes) ∧
  (∀ m : Msg n, (m ∈ s.inflight ∨ m ∈ s.seen) → ∀ e : ℕ, ∀ b : Blk,
      m.body = Body.prop e b → (m.src, e, b) ∈ s.castProps)

/-- `c` is a *longest notarized view* by epoch `e`: every nonempty suffix of
`c` is notarized in `seen` and by epoch `e - 1` (cast), and no chain
notarized by `e - 1` is longer. This is the shared guard of `Propose e`
(proposing `b = e :: c`) and `VoteH` (voting for `b` with `bep b = e`,
`c = b.tail`). -/
def LongestNotarized (s : St n) (e : ℕ) (c : Blk) : Prop :=
  ChainNotarizedSeen n f s c ∧ ChainNotarizedBy n Byz f s c (e - 1) ∧
    ∀ C : Blk, NotarizedBy n Byz f s C (e - 1) → C.length ≤ c.length

/-- A message body carries a well-formed chain — the ideal-hash assumption:
the data structure only *contains* hash chains, forged or not. -/
def ValidBody : Body → Prop
  | Body.prop _ b => ValidChain b
  | Body.vote b => ValidChain b

/-! ## The invariant bundle -/

/-- The honest-vote and honest-proposal conditions that Fact 2 and Fact 3
rest on, plus the epoch bookkeeping (`propCur`) that makes `propLongest`
inductive. Every field quantifying over a node's cast is guarded by that
node being honest — which is what makes the bundle survive arbitrary
Byzantine sends (`SendB`). -/
structure Inv (s : St n) : Prop where
  voteSeenParent : ∀ i b, i ∉ Byz → (i, b) ∈ s.castVotes → ChainNotarizedSeen n f s b.tail
  propValid : ∀ e b, (L e, e, b) ∈ s.castProps → L e ∉ Byz → ValidChain b
  propLongest : ∀ e b, (L e, e, b) ∈ s.castProps → L e ∉ Byz → ∀ C : Blk,
    NotarizedBy n Byz f s C (e - 1) → C.length ≤ b.tail.length
  propCur : ∀ e b, (L e, e, b) ∈ s.castProps → L e ∉ Byz → e ≤ curEpoch Δ s.now
  voteCur : ∀ i b, i ∉ Byz → (i, b) ∈ s.castVotes → bep b ≤ curEpoch Δ s.now
  votedProposed : ∀ i b, i ∉ Byz → (i, b) ∈ s.castVotes → (L (bep b), bep b, b) ∈ s.castProps
  votedSeenParent : ∀ i b, i ∉ Byz → (i, b) ∈ s.castVotes → ChainNotarizedBy n Byz f s b.tail (bep b - 1)
  votedLongest : ∀ i b, i ∉ Byz → (i, b) ∈ s.castVotes → ∀ C : Blk,
    NotarizedBy n Byz f s C (bep b - 1) → C.length ≤ b.tail.length
  proposedSeenParent : ∀ e b, (L e, e, b) ∈ s.castProps → L e ∉ Byz →
    ChainNotarizedBy n Byz f s b.tail (e - 1)
  proposedEpoch : ∀ e b, (L e, e, b) ∈ s.castProps → L e ∉ Byz → bep b = e
  propUniq : ∀ e b₁ b₂, (L e, e, b₁) ∈ s.castProps → (L e, e, b₂) ∈ s.castProps →
    L e ∉ Byz → b₁ = b₂
  voteValid : ∀ i b, i ∉ Byz → (i, b) ∈ s.castVotes → ValidChain b
  sentMem : SentMem n s

/-- `Inv` as a state predicate (for the TLA induction). -/
def InvState : StatePred (St n) := { s | Inv n Byz Δ f L s }

/-! ## Quorum intersection: a quorum contains an honest node -/

/-- A set of `2f+1` nodes contains an honest one: at most `f` are Byzantine. -/
theorem honest_in_quorum (hB : Byz.card ≤ f) {Q : Finset (Fin n)}
    (hq : quorum f ≤ Q.card) : ∃ i, i ∈ Q ∧ i ∉ Byz := by
  have hpos : 0 < ((Q.filter fun i => i ∉ Byz)).card := by
    have hle : ((Q.filter fun i => i ∈ Byz)).card ≤ Byz.card := by
      apply Finset.card_le_card
      intro x hx
      rw [Finset.mem_filter] at hx
      exact hx.2
    have hsd := Finset.card_filter_add_card_filter_not (s := Q) (p := fun i => i ∈ Byz)
    unfold quorum at hq
    omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hi
  exact ⟨i, hi.1, hi.2⟩

/-! ## Membership lemmas -/

/-- Membership in a block's seen-voter set is having delivered that vote. -/
@[tla_msgs] theorem mem_votersSeen {s : St n} {i : Fin n} {b : Blk} :
    i ∈ votersSeen n s b ↔ voteMsg n s i b := by
  simp only [votersSeen, voteMsg, Finset.mem_image, Finset.mem_filter]
  grind

/-- Membership in a block's cast-voter set is having cast that vote
(and being honest — the set is honest by construction). -/
@[tla_msgs] theorem mem_votersCast {s : St n} {i : Fin n} {b : Blk} :
    i ∈ votersCast n Byz s b ↔ (i, b) ∈ s.castVotes ∧ i ∉ Byz := by
  simp [votersCast]

/-- A delivered vote is recorded in the cast history (the one-directional
bridge at work). -/
theorem voteMsg_castMem {s : St n} (h : SentMem n s) {i : Fin n} {b : Blk}
    (hv : voteMsg n s i b) : (i, b) ∈ s.castVotes := by
  obtain ⟨m, hm, hsrc, hb⟩ := hv
  have hmem := h.1 m (Or.inr hm) b hb
  rw [hsrc] at hmem
  exact hmem

/-! ## Fact 2: notarization implies the parent chain was notarized -/

/-- **Fact 2** (broadcast form): if `B` is notarized (a quorum's votes for it
are delivered), then every block of `B`'s parent chain was notarized in
`seen`. The honest voter in the quorum saw the parent chain notarized before
voting (`Inv.voteSeenParent`), and `seen` only grows. -/
theorem fact2 (hB : Byz.card ≤ f) {s : St n} (hinv : Inv n Byz Δ f L s)
    {B : Blk} (hN : NotarizedSeen n f s B) :
    ∀ d : Blk, d ≠ [] → d <:+ B.tail → NotarizedSeen n f s d := by
  obtain ⟨i, hiQ, hih⟩ := honest_in_quorum n Byz f hB hN
  have hiv : voteMsg n s i B := (mem_votersSeen n).mp hiQ
  exact hinv.voteSeenParent i B hih (voteMsg_castMem n hinv.sentMem hiv)

/-! ## Fact 3: two honest leaders propose at strictly growing lengths -/

/-- **Fact 3** (mathematical core): an honest `L(e+1)` that proposed `b₁`
extends a longest chain notarized by epoch `e` (`Inv.propLongest`); if some
chain of length ≥ `b₀.length` was notarized by epoch `e`, then
`b₀.length < b₁.length`. The `b₀`-side hypotheses are intentionally absent:
only the length of some notarized chain matters. -/
theorem proposal_growth {s : St n} (hinv : Inv n Byz Δ f L s)
    {e : ℕ} {b₀ b₁ : Blk}
    (hp1 : propCast n L s (e + 1) b₁) (hL1 : L (e + 1) ∉ Byz)
    (hseen : ∃ C : Blk, NotarizedBy n Byz f s C e ∧ b₀.length ≤ C.length) :
    b₀.length < b₁.length := by
  rcases hseen with ⟨C, hC, hlen⟩
  have hle : C.length ≤ b₁.tail.length :=
    hinv.propLongest (e + 1) b₁ hp1 hL1 C hC
  have hb1valid : ValidChain b₁ := hinv.propValid (e + 1) b₁ hp1 hL1
  have hb1pos : 0 < b₁.length := by
    exact List.length_pos_of_mem hb1valid.1
  have hb1len : b₁.length = b₁.tail.length + 1 := by
    have h : b₁.tail.length = b₁.length - 1 := List.length_tail
    omega
  omega

/-- Fact 3 in the form the liveness theorems use: an honest `L(e+1)`
proposal `b₁` outgrows any nonempty block `b₀` chain-notarized by epoch
`e`. -/
theorem proposal_growth_chain {s : St n} (hinv : Inv n Byz Δ f L s)
    {e : ℕ} {b₀ b₁ : Blk}
    (hp1 : propCast n L s (e + 1) b₁) (hL1 : L (e + 1) ∉ Byz)
    (hb0ne : b₀ ≠ []) (hc0 : ChainNotarizedBy n Byz f s b₀ e) :
    b₀.length < b₁.length :=
  proposal_growth n Byz Δ f L hinv hp1 hL1
    ⟨b₀, hc0 b₀ hb0ne (List.suffix_refl b₀), le_rfl⟩

/-! ## The protocol actions -/

/-- The honest leader of epoch `e` proposes `b` at the start of the epoch:
`b` is valid, of epoch `e`, extends a longest chain notarized by `e - 1` in
the leader's view, and the leader has not yet proposed this epoch. -/
def Propose (e : ℕ) (b : Blk) : Action (St n) := fun s s' =>
  (∀ b' : Blk, ¬ propCast n L s e b') ∧
  L e ∉ Byz ∧ ValidChain b ∧ bep b = e ∧ curEpoch Δ s.now = e ∧
  LongestNotarized n Byz f s e b.tail ∧
  Send n (⟨L e, s.now, Body.prop e b⟩ : Msg n) s s'

/-- An honest node votes for `b` in its own epoch: valid, first vote of the
epoch, on the epoch leader's proposal, extending a longest notarized view. -/
def VoteH (i : Fin n) (b : Blk) : Action (St n) := fun s s' =>
  i ∉ Byz ∧ ValidChain b ∧ 0 < bep b ∧ bep b = curEpoch Δ s.now ∧
  (∀ b' : Blk, voteCast n s i b' → bep b' ≠ bep b) ∧
  propCast n L s (bep b) b ∧
  LongestNotarized n Byz f s (bep b) b.tail ∧
  Send n (⟨i, s.now, Body.vote b⟩ : Msg n) s s'

/-- A Byzantine node broadcasts an arbitrary well-formed message at any
time — equivocation included: nothing constrains two sends from the same
faulty node to agree (several votes in one epoch, several proposals of one
epoch by a faulty leader). Well-formedness of the carried chain is the
ideal-hash assumption, not an honesty restriction. -/
def SendB (m : Msg n) : Action (St n) := fun s s' =>
  m.src ∈ Byz ∧ ValidBody m.body ∧ Send n m s s'

/-- The protocol step relation: clock ticks, honest proposals, honest votes,
Byzantine broadcasts, and delivery. -/
def PNext : Action (St n) := fun s s' =>
  Tick n Byz Δ GST s s' ∨ (∃ e b, Propose n Byz Δ f L e b s s') ∨
    (∃ i b, VoteH n Byz Δ f L i b s s') ∨ (∃ m, SendB n Byz m s s') ∨
    (∃ m, Deliver n Byz Δ GST m s s')

/-- Initially: round 0, nothing in flight, nothing seen. -/
def PInit : StatePred (St n) := { s | s.now = 0 ∧ s.inflight = ∅ ∧ s.seen = ∅ ∧ s.castVotes = ∅ ∧ s.castProps = ∅ }

/-- The protocol specification, bundled (for `Spec.init_invariant`). -/
def ProtoSpec (n : ℕ) (Byz : Finset (Fin n)) (Δ GST f : ℕ) (L : ℕ → Fin n) : Spec (St n) (St n) :=
  ⟨PInit n, PNext n Byz Δ GST f L, vars n⟩

/-- The protocol specification. -/
def PSpec : Pred (St n) := (ProtoSpec n Byz Δ GST f L).pred

/-! ## Monotonicity and stability lemmas -/

/-- The epoch clock is monotone in the round. -/
theorem curEpoch_mono {a b : ℕ} (h : a ≤ b) : curEpoch Δ a ≤ curEpoch Δ b := by
  unfold curEpoch
  exact Nat.div_le_div_right h

/-- `votersSeen` is monotone in `seen`. -/
theorem votersSeen_mono {s s' : St n} (h : ∀ m, m ∈ s.seen → m ∈ s'.seen) (b : Blk) :
    votersSeen n s b ⊆ votersSeen n s' b := by
  intro i hi
  rw [mem_votersSeen n] at hi ⊢
  rcases hi with ⟨m, hm, hsrc, hb⟩
  exact ⟨m, h m hm, hsrc, hb⟩

/-- `NotarizedSeen` is monotone in `seen`. -/
theorem notarizedSeen_mono {s s' : St n} (h : ∀ m, m ∈ s.seen → m ∈ s'.seen) {b : Blk} :
    NotarizedSeen n f s b → NotarizedSeen n f s' b := by
  intro hN
  exact le_trans hN (Finset.card_le_card (votersSeen_mono n h b))

/-- `ChainNotarizedSeen` is monotone in `seen`. -/
theorem chainNotarizedSeen_mono {s s' : St n} (h : ∀ m, m ∈ s.seen → m ∈ s'.seen) {c : Blk} :
    ChainNotarizedSeen n f s c → ChainNotarizedSeen n f s' c := by
  intro hc d hd hs
  exact notarizedSeen_mono n f h (hc d hd hs)

/-- NotarizedCast is monotone in the cast-vote history. -/
theorem notarizedCast_mono {s s' : St n} (h : s.castVotes ⊆ s'.castVotes) {b : Blk} :
    NotarizedCast n Byz f s b → NotarizedCast n Byz f s' b := by
  intro hN
  unfold NotarizedCast at hN ⊢
  exact le_trans hN (Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset_filter (p := fun p => p.2 = b ∧ p.1 ∉ Byz) h)))

/-- NotarizedBy is monotone in the cast-vote history. -/
theorem notarizedBy_mono_cast {s s' : St n} (h : s.castVotes ⊆ s'.castVotes) {b : Blk} {e : ℕ} :
    NotarizedBy n Byz f s b e → NotarizedBy n Byz f s' b e := by
  rintro ⟨hN, hbep⟩
  exact ⟨notarizedCast_mono n Byz f h hN, hbep⟩

/-- ChainNotarizedBy is monotone in the cast-vote history. -/
theorem chainNotarizedBy_mono_cast {s s' : St n} (h : s.castVotes ⊆ s'.castVotes) {c : Blk} {e : ℕ} :
    ChainNotarizedBy n Byz f s c e → ChainNotarizedBy n Byz f s' c e := by
  intro hc d hd hs
  exact notarizedBy_mono_cast n Byz f h (hc d hd hs)

attribute [grind =>] notarizedCast_mono notarizedBy_mono_cast chainNotarizedBy_mono_cast
  notarizedSeen_mono chainNotarizedSeen_mono

/-- Delivery moves a message from `inflight` to `seen`, leaving the sent set
(`inflight ∨ seen`) unchanged. -/
theorem sent_eq_deliver {s s' : St n} {m0 : Msg n}
    (hm0 : m0 ∈ s.inflight)
    (hinf : s'.inflight = s.inflight.erase m0) (hseen : s'.seen = insert m0 s.seen) :
    ∀ m, (m ∈ s'.inflight ∨ m ∈ s'.seen) ↔ (m ∈ s.inflight ∨ m ∈ s.seen) := by
  intro m
  constructor
  · intro hm
    rcases hm with h | h
    · rw [hinf] at h; left; exact Finset.mem_of_mem_erase h
    · rw [hseen] at h
      rcases Finset.mem_insert.mp h with h | h
      · subst h; left; exact hm0
      · right; exact h
  · intro hm
    rcases hm with h | h
    · by_cases heq : m = m0
      · right; rw [hseen]; exact Finset.mem_insert.mpr (Or.inl heq)
      · left; rw [hinf]; exact Finset.mem_erase_of_ne_of_mem heq h
    · right; rw [hseen]; exact Finset.mem_insert_of_mem h

/-- The one case analysis on a sent message's body, done once in a clean
context: after `Send`'s history update, the old histories are covered and
the new message is recorded, whatever the body. -/
theorem send_hist (n : ℕ) (bd : Body) (src : Fin n)
    (CV : Finset (Fin n × Blk)) (CP : Finset (Fin n × ℕ × Blk)) :
    CV ⊆ castVotesAdd n bd src CV ∧
    CP ⊆ castPropsAdd n bd src CP ∧
    (∀ p : Fin n × Blk, p ∈ castVotesAdd n bd src CV → p ∈ CV ∨ p.1 = src) ∧
    (∀ p : Fin n × ℕ × Blk, p ∈ castPropsAdd n bd src CP → p ∈ CP ∨ p.1 = src) :=
  by cases bd <;> unfold castVotesAdd castPropsAdd <;> grind

/-- A `Send` only grows the vote history. -/
theorem send_castVotes_mono {s s' : St n} {m : Msg n} (hs : Send n m s s') :
    s.castVotes ⊆ s'.castVotes := by
  intro p hp
  have hcv : s'.castVotes = castVotesAdd n m.body m.src s.castVotes := by grind
  rw [hcv]
  exact (send_hist n m.body m.src s.castVotes s.castProps).1 hp

/-- A `Send` only grows the proposal history. -/
theorem send_castProps_mono {s s' : St n} {m : Msg n} (hs : Send n m s s') :
    s.castProps ⊆ s'.castProps := by
  intro p hp
  have hcp : s'.castProps = castPropsAdd n m.body m.src s.castProps := by grind
  rw [hcp]
  exact (send_hist n m.body m.src s.castVotes s.castProps).2.1 hp

/-- A `Send` preserves the message-to-history bridge: the new message is
recorded (whatever its body), and old messages' records survive since the
histories only grow. -/
theorem sentMem_send {s s' : St n} {m : Msg n} (hs : Send n m s s')
    (h : SentMem n s) : SentMem n s' := by
  have hinf : s'.inflight = insert m s.inflight := by grind
  have hseen : s'.seen = s.seen := by grind
  have hcv : s'.castVotes = castVotesAdd n m.body m.src s.castVotes := by grind
  have hcp : s'.castProps = castPropsAdd n m.body m.src s.castProps := by grind
  have hmono := send_hist n m.body m.src s.castVotes s.castProps
  obtain ⟨hv, hp⟩ := h
  refine ⟨?_, ?_⟩
  · intro m' hsent b hbody
    rcases hsent with hin | hsin
    · rw [hinf] at hin
      rcases Finset.mem_insert.mp hin with heq | hold
      · subst heq
        rw [hbody] at hcv
        rw [hcv]
        exact Finset.mem_insert_self _ _
      · rw [hcv]; exact hmono.1 (hv m' (Or.inl hold) b hbody)
    · rw [hseen] at hsin
      rw [hcv]
      exact hmono.1 (hv m' (Or.inr hsin) b hbody)
  · intro m' hsent e b hbody
    rcases hsent with hin | hsin
    · rw [hinf] at hin
      rcases Finset.mem_insert.mp hin with heq | hold
      · subst heq
        rw [hbody] at hcp
        rw [hcp]
        exact Finset.mem_insert_self _ _
      · rw [hcp]; exact hmono.2.1 (hp m' (Or.inl hold) e b hbody)
    · rw [hseen] at hsin
      rw [hcp]
      exact hmono.2.1 (hp m' (Or.inr hsin) e b hbody)

/-- A `Deliver` preserves the message-to-history bridge: delivery does not
change the sent set or the cast histories. -/
theorem sentMem_deliver {s s' : St n} {m : Msg n}
    (hd : Deliver n Byz Δ GST m s s') (h : SentMem n s) : SentMem n s' := by
  obtain ⟨hmem, _hguard, _hnow, hinf, hseen, hcv, hcp⟩ := hd
  refine ⟨?_, ?_⟩
  · intro m' hsent b hbody
    rw [hcv]
    exact h.1 m' ((sent_eq_deliver n hmem hinf hseen m').mp hsent) b hbody
  · intro m' hsent e b hbody
    rw [hcp]
    exact h.2 m' ((sent_eq_deliver n hmem hinf hseen m').mp hsent) e b hbody

/-- A `Tick` preserves the message-to-history bridge: nothing moves. -/
theorem sentMem_tick {s s' : St n} (hinf : s'.inflight = s.inflight)
    (hseen : s'.seen = s.seen) (hcv : s'.castVotes = s.castVotes)
    (hcp : s'.castProps = s.castProps) (h : SentMem n s) : SentMem n s' := by
  refine ⟨?_, ?_⟩
  · intro m hsent b hbody
    rw [hinf, hseen] at hsent
    rw [hcv]
    exact h.1 m hsent b hbody
  · intro m hsent e b hbody
    rw [hinf, hseen] at hsent
    rw [hcp]
    exact h.2 m hsent e b hbody

/-- Adding a vote for block `b` to the cast history leaves `NotarizedBy C e`
unchanged whenever `e < bep b` (the new vote is for a block of too late an
epoch to count toward `C`'s quorum at epoch `e`). -/
theorem notarizedBy_stable_cast_vote {s s' : St n} {i : Fin n} {b : Blk}
    (hcv : s'.castVotes = insert (i, b) s.castVotes) {C : Blk} {e : ℕ}
    (hgt : e < bep b) :
    NotarizedBy n Byz f s C e ↔ NotarizedBy n Byz f s' C e := by
  constructor
  · exact notarizedBy_mono_cast n Byz f
      (by intro p hp; rw [hcv]; exact Finset.mem_insert_of_mem hp)
  · rintro ⟨hq, hbep⟩
    refine ⟨?_, hbep⟩
    unfold NotarizedCast at hq ⊢
    have hv : votersCast n Byz s' C = votersCast n Byz s C := by
      unfold votersCast
      rw [hcv]
      have hbC : b ≠ C := by intro h; subst C; omega
      simp [Finset.filter_insert, hbC]
    simpa [hv] using hq

/-- The cast histories of `s'` contain those of `s`. -/
def castGrows (s s' : St n) : Prop :=
  s.castVotes ⊆ s'.castVotes ∧ s.castProps ⊆ s'.castProps

/-- Every protocol step preserves (grows) the cast histories. -/
theorem pnext_castGrows {s s' : St n} (hstep : PNext n Byz Δ GST f L s s') : castGrows n s s' := by
  rcases hstep with htick | ⟨e, b, hpr⟩ | ⟨i, b, hv⟩ | ⟨m, hbyzm, hval, hs⟩ | ⟨m, hd⟩
  · constructor <;> grind
  · obtain ⟨_hprior, _hL, _hval, _hbep, _hcur, _hlong, hsend⟩ := hpr
    exact ⟨send_castVotes_mono n hsend, send_castProps_mono n hsend⟩
  · obtain ⟨_hi, _hval, _hbpos, _hbcur, _hfirst, _hprop, _hlong, hsend⟩ := hv
    exact ⟨send_castVotes_mono n hsend, send_castProps_mono n hsend⟩
  · exact ⟨send_castVotes_mono n hs, send_castProps_mono n hs⟩
  · constructor <;> grind

/-- `propCast` is monotone in the cast history. -/
theorem propCast_mono {s s' : St n} (h : castGrows n s s') {e : ℕ} {b : Blk} :
    propCast n L s e b → propCast n L s' e b := fun hp => h.2 hp

theorem init_inv : ∀ s, s ∈ PInit n → s ∈ InvState n Byz Δ f L := by
  intro s hs
  obtain ⟨_hnow, hinf, hseen, hcv, hcp⟩ := hs
  constructor <;> simp [hinf, hseen, hcv, hcp, SentMem]

/-- The invariant is preserved by every protocol step — including Byzantine
sends. The 12 honest-node fields — stated over the monotone cast histories
and guarded by the caster's honesty — are closed by `grind` with the
`[grind =>]`-tagged monotonicity lemmas: a `SendB` adds only Byzantine
casts, which every honest premise `i ∉ Byz` / `L e ∉ Byz` filters out.
Only the vote-stability transports (`propLongest` / `votedLongest` under
`VoteH`) and the message-to-history bridge (`sentMem`) need the
hand-written `∃`/`↔` reasoning. -/
theorem step_inv : ∀ s s', StutAction (PNext n Byz Δ GST f L) (vars n) s s' →
    s ∈ InvState n Byz Δ f L → s' ∈ InvState n Byz Δ f L := by
  intro s s' hstep hinv
  rcases hstep with hnext | hstut
  swap
  · have hss' : s' = s := hstut
    rwa [hss']
  rcases hinv with ⟨hvsp, hpv, hpl, hpc, hvc, hvpr, hvsp2, hvl, hpsp, hpe, hpu, hvv, hsm⟩
  rcases hnext with htick | ⟨e, b, hp⟩ | ⟨i, b, hv⟩ | ⟨m, hbyz⟩ | ⟨m, hd⟩
  · -- Tick: clock advances, cast/seen unchanged
    obtain ⟨hnow, hinf, hseen, hcv, hcp, _⟩ := htick
    have hseenmono : ∀ m, m ∈ s.seen → m ∈ s'.seen := by intro m hm; rw [hseen]; exact hm
    have hcvmono : s.castVotes ⊆ s'.castVotes := by intro p hp; rw [hcv]; exact hp
    have hcpmono : s.castProps ⊆ s'.castProps := by intro p hp; rw [hcp]; exact hp
    have hclockmono : curEpoch Δ s.now ≤ curEpoch Δ s'.now := by rw [hnow]; exact curEpoch_mono Δ (Nat.le_succ s.now)
    constructor <;> first
    | grind
    | exact sentMem_tick n hinf hseen hcv hcp hsm
  · -- Propose: the honest leader adds its own proposal to castProps
    obtain ⟨hprior, _, hval, hbep, hcur, hlong, hsend⟩ := hp
    obtain ⟨hlnSeen, hlnBy, hlnLong⟩ : ChainNotarizedSeen n f s b.tail ∧
        ChainNotarizedBy n Byz f s b.tail (e - 1) ∧
          ∀ C : Blk, NotarizedBy n Byz f s C (e - 1) → C.length ≤ b.tail.length := hlong
    have hsm' : SentMem n s' := sentMem_send n hsend hsm
    obtain ⟨_, _, _, hnow, hinf, hseen, hcv, hcp⟩ := hsend
    have hseenmono : ∀ m, m ∈ s.seen → m ∈ s'.seen := by intro m hm; rw [hseen]; exact hm
    have hcvmono : s.castVotes ⊆ s'.castVotes := by intro p hp; rw [hcv]; exact hp
    have hcpmono : s.castProps ⊆ s'.castProps := by intro p hp; rw [hcp]; exact Finset.mem_insert_of_mem hp
    have hclockmono : curEpoch Δ s.now ≤ curEpoch Δ s'.now := by rw [hnow]
    constructor <;> grind
  · -- VoteH: the honest node adds its own vote to castVotes
    obtain ⟨_, hval, hbpos, hbcur, _, hprop, hlong, hsend⟩ := hv
    obtain ⟨hlnSeen, hlnBy, hlnLong⟩ : ChainNotarizedSeen n f s b.tail ∧
        ChainNotarizedBy n Byz f s b.tail (bep b - 1) ∧
          ∀ C : Blk, NotarizedBy n Byz f s C (bep b - 1) → C.length ≤ b.tail.length := hlong
    have hsm' : SentMem n s' := sentMem_send n hsend hsm
    obtain ⟨_, _, _, hnow, hinf, hseen, hcv, hcp⟩ := hsend
    -- The vote body leaves `castProps` alone and extends `castVotes` by
    -- `(i, b)`; expose that so the `rw [hcv, Finset.mem_insert]` and
    -- `simpa [hcp]` below match.
    simp [castVotesAdd, castPropsAdd] at hcv hcp
    have hseenmono : ∀ m, m ∈ s.seen → m ∈ s'.seen := by intro m hm; rw [hseen]; exact hm
    have hcvmono : s.castVotes ⊆ s'.castVotes := by intro p hp; rw [hcv]; exact Finset.mem_insert_of_mem hp
    have hcpmono : s.castProps ⊆ s'.castProps := by intro p hp; rw [hcp]; exact hp
    have hclockmono : curEpoch Δ s.now ≤ curEpoch Δ s'.now := by rw [hnow]
    constructor <;> first
    | grind
    | intro e' b' hpb hL C hC
      have hgt : e' - 1 < bep b := by
        have hle : e' ≤ curEpoch Δ s.now := hpc e' b' (by simpa [hcp] using hpb) hL
        omega
      exact hpl e' b' (by simpa [hcp] using hpb) hL C
        ((notarizedBy_stable_cast_vote n Byz f hcv hgt).2 hC)
    | intro j b' hj hvb C hC
      rw [hcv, Finset.mem_insert] at hvb
      rcases hvb with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact hlnLong C ((notarizedBy_stable_cast_vote n Byz f hcv (by omega)).2 hC)
      · have hgt : bep b' - 1 < bep b := by
          have hle : bep b' ≤ curEpoch Δ s.now := hvc j b' hj h
          omega
        exact hvl j b' hj h C ((notarizedBy_stable_cast_vote n Byz f hcv hgt).2 hC)
  · -- SendB: a Byzantine node adds only Byzantine casts; every honest
    -- premise (`i ∉ Byz` / `L e ∉ Byz`) filters them out
    obtain ⟨hbyzm, hval, hsend⟩ := hbyz
    have hsm' : SentMem n s' := sentMem_send n hsend hsm
    have hnow : s'.now = s.now := by grind
    have hseen : s'.seen = s.seen := by grind
    have hcv : s'.castVotes = castVotesAdd n m.body m.src s.castVotes := by grind
    have hcp : s'.castProps = castPropsAdd n m.body m.src s.castProps := by grind
    have hseenmono : ∀ m, m ∈ s.seen → m ∈ s'.seen := by intro m hm; rw [hseen]; exact hm
    have hhist := send_hist n m.body m.src s.castVotes s.castProps
    have hcvmono : s.castVotes ⊆ s'.castVotes := by
      intro p hp; rw [hcv]; exact hhist.1 hp
    have hcpmono : s.castProps ⊆ s'.castProps := by
      intro p hp; rw [hcp]; exact hhist.2.1 hp
    have hcvnew : ∀ p : Fin n × Blk, p ∈ s'.castVotes → p ∈ s.castVotes ∨ p.1 = m.src := by
      intro p hp; rw [hcv] at hp; exact hhist.2.2.1 p hp
    have hcpnew : ∀ p : Fin n × ℕ × Blk, p ∈ s'.castProps → p ∈ s.castProps ∨ p.1 = m.src := by
      intro p hp; rw [hcp] at hp; exact hhist.2.2.2 p hp
    have hcvback : ∀ C : Blk, ∀ e : ℕ, NotarizedBy n Byz f s' C e → NotarizedBy n Byz f s C e := by
      intro C e ⟨hq, hbep⟩
      refine ⟨?_, hbep⟩
      unfold NotarizedCast at hq ⊢
      have hv : votersCast n Byz s' C ⊆ votersCast n Byz s C := by
        intro i hi
        rw [mem_votersCast n Byz] at hi ⊢
        rcases hcvnew (i, C) hi.1 with h | h
        · exact ⟨h, hi.2⟩
        · exfalso
          have hiEq : i = m.src := by simpa using h
          exact hi.2 (by rw [hiEq]; exact hbyzm)
      exact le_trans hq (Finset.card_le_card hv)
    have hclockmono : curEpoch Δ s.now ≤ curEpoch Δ s'.now := by rw [hnow]
    constructor <;> grind
  · -- Deliver: seen grows, cast/clock unchanged
    have hd' := hd
    obtain ⟨hmem, _, hnow, hinf, hseen, hcv, hcp⟩ := hd
    have hseenmono : ∀ m, m ∈ s.seen → m ∈ s'.seen := by intro m hm; rw [hseen]; exact Finset.mem_insert_of_mem hm
    have hcvmono : s.castVotes ⊆ s'.castVotes := by intro p hp; rw [hcv]; exact hp
    have hcpmono : s.castProps ⊆ s'.castProps := by intro p hp; rw [hcp]; exact hp
    have hclockmono : curEpoch Δ s.now ≤ curEpoch Δ s'.now := by rw [hnow]
    constructor <;> first
    | grind
    | exact sentMem_deliver n Byz Δ GST hd' hsm

theorem spec_entails_inv :
    Entails (PSpec n Byz Δ GST f L) (always (statePred (InvState n Byz Δ f L))) :=
  (ProtoSpec n Byz Δ GST f L).init_invariant (InvState n Byz Δ f L)
    (init_inv n Byz Δ f L) (step_inv n Byz Δ GST f L)

end Bft.Examples.StreamletProto
