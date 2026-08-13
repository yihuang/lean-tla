/-
Copyright (c) 2026 lean-tla contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Case study: Streamlet protocol facts over the partial-sync transport

This file layers the **Streamlet protocol** on top of the transport model in
`Bft.Examples.StreamletNet`: proposals, votes, notarization, the leader
schedule, and the paper's **Fact 2** and **Fact 3** (§3.6.2).

Design, in service of the paper:

* **Votes and proposals are messages.** A vote for block `b` by node `i` is
  a `Msg` with `src = i` and `body = .vote b`; the proposal of epoch `e` is
  a `Msg` with `src = L e` (the epoch's leader) and `body = .prop e b`.
  "Cast" means the message has been sent (`inflight ∨ seen`); "seen" means
  delivered (`seen`). This is where the transport layer's real in-flight +
  GST + Δ enters: cast ⇒ seen within Δ after GST (Fact 1), so the protocol
  facts only need to talk about the cast/seen distinction, not delivery
  itself.
* **Notarization** is `2f+1` distinct voters (`votersCast` / `votersSeen`).
  `NotarizedBy s b e` — the paper's epoch-bounded notion — is "a quorum cast
  votes for `b`, and `bep b ≤ e`". This is the device that makes the
  liveness facts provable: a vote cast in epoch `bep b` cannot change
  `NotarizedBy C e` for any `e < bep b` (its own epoch is too late).
* **Fact 2** (notarization implies the parent chain was notarized): among
  the `2f+1` voters of a notarized block, one is honest (`honest_in_quorum`),
  and an honest voter only votes after seeing the parent chain notarized
  (`Inv.voteSeenParent`).
* **Fact 3** (two honest consecutive leaders propose at growing lengths):
  the honest `L(e+1)` extends a longest chain notarized by epoch `e`
  (`Inv.propLongest`), and by then some chain of length ≥ `b₀.length` is
  notarized (`hseen`); hence `b₁.length > b₀.length`.

The invariant bundle `Inv` collects the honest-vote and honest-proposal
conditions these facts need. Its inductiveness over the protocol actions is
proved in the same file (below).
-/
import Bft.Examples.StreamletNet

namespace Bft.Examples.StreamletProto

open Bft
open Bft.Examples.StreamletNet (Body Msg St deadline Send Deliver Tick Next Hspec NoOverdue vars)
open Bft.Examples.Streamlet (Blk ValidChain bep quorum)

variable (n : ℕ) (Byz : Finset (Fin n)) (Δ GST f : ℕ) (L : ℕ → Fin n)

/-! ## Protocol predicates over the transport state -/

/-- Node `i` has cast a vote for `b` (sent, possibly not yet delivered). -/
def voteCast (s : St n) (i : Fin n) (b : Blk) : Prop :=
  ∃ m, (m ∈ s.inflight ∨ m ∈ s.seen) ∧ m.src = i ∧ m.body = Body.vote b

/-- The leader of epoch `e` has cast a proposal for `b`. -/
def propCast (s : St n) (e : ℕ) (b : Blk) : Prop :=
  ∃ m, (m ∈ s.inflight ∨ m ∈ s.seen) ∧ m.src = L e ∧ m.body = Body.prop e b

/-- Node `i`'s vote for `b` has been delivered (is in `seen`). -/
def voteMsg (s : St n) (i : Fin n) (b : Blk) : Prop :=
  ∃ m, m ∈ s.seen ∧ m.src = i ∧ m.body = Body.vote b

/-- The leader of epoch `e`'s proposal for `b` has been delivered. -/
def propMsg (s : St n) (e : ℕ) (b : Blk) : Prop :=
  ∃ m, m ∈ s.seen ∧ m.src = L e ∧ m.body = Body.prop e b

/-- The distinct nodes that cast a vote for `b`. -/
def votersCast (s : St n) (b : Blk) : Finset (Fin n) :=
  (s.castVotes.filter fun p => p.2 = b).image (fun p => p.1)

/-- The distinct nodes whose vote for `b` has been delivered. -/
def votersSeen (s : St n) (b : Blk) : Finset (Fin n) :=
  (s.seen.filter fun m => m.body = Body.vote b).image (fun m => m.src)

/-- A quorum of cast votes for `b`. -/
def NotarizedCast (s : St n) (b : Blk) : Prop := quorum f ≤ (votersCast n s b).card

/-- A quorum of delivered votes for `b`. -/
def NotarizedSeen (s : St n) (b : Blk) : Prop := quorum f ≤ (votersSeen n s b).card

/-- Block `b` is notarized (cast) by epoch `e`: a quorum cast votes for it,
and its own epoch is at most `e`. -/
def NotarizedBy (s : St n) (b : Blk) (e : ℕ) : Prop := NotarizedCast n f s b ∧ bep b ≤ e

/-- Every nonempty suffix of `c` is notarized (in `seen`). -/
def ChainNotarizedSeen (s : St n) (c : Blk) : Prop :=
  ∀ d : Blk, d ≠ [] → d <:+ c → NotarizedSeen n f s d

/-- Every nonempty suffix of `c` is notarized (cast) by epoch `e`. -/
def ChainNotarizedBy (s : St n) (c : Blk) (e : ℕ) : Prop :=
  ∀ d : Blk, d ≠ [] → d <:+ c → NotarizedBy n f s d e

/-- The epoch of a round: epochs have length `2Δ`. -/
def curEpoch (Δ : ℕ) (now : ℕ) : ℕ := now / (2 * Δ)

/-! ## The invariant bundle -/

/-- The honest-vote and honest-proposal conditions that Fact 2 and Fact 3
rest on, plus the epoch bookkeeping (`propCur`) that makes `propLongest`
inductive. -/
structure Inv (s : St n) : Prop where
  voteSeenParent : ∀ i b, i ∉ Byz → (i, b) ∈ s.castVotes → ChainNotarizedSeen n f s b.tail
  propValid : ∀ e b, (e, b) ∈ s.castProps → L e ∉ Byz → ValidChain b
  propLongest : ∀ e b, (e, b) ∈ s.castProps → L e ∉ Byz → ∀ C : Blk,
    NotarizedBy n f s C (e - 1) → C.length ≤ b.tail.length
  propCur : ∀ e b, (e, b) ∈ s.castProps → L e ∉ Byz → e ≤ curEpoch Δ s.now
  voteCur : ∀ i b, i ∉ Byz → (i, b) ∈ s.castVotes → bep b ≤ curEpoch Δ s.now
  votedProposed : ∀ i b, i ∉ Byz → (i, b) ∈ s.castVotes → (bep b, b) ∈ s.castProps
  votedSeenParent : ∀ i b, i ∉ Byz → (i, b) ∈ s.castVotes → ChainNotarizedBy n f s b.tail (bep b - 1)
  votedLongest : ∀ i b, i ∉ Byz → (i, b) ∈ s.castVotes → ∀ C : Blk,
    NotarizedBy n f s C (bep b - 1) → C.length ≤ b.tail.length
  proposedSeenParent : ∀ e b, (e, b) ∈ s.castProps → L e ∉ Byz →
    ChainNotarizedBy n f s b.tail (e - 1)
  proposedEpoch : ∀ e b, (e, b) ∈ s.castProps → L e ∉ Byz → bep b = e
  propUniq : ∀ e b₁ b₂, (e, b₁) ∈ s.castProps → (e, b₂) ∈ s.castProps → L e ∉ Byz → b₁ = b₂
  voteValid : ∀ i b, i ∉ Byz → (i, b) ∈ s.castVotes → ValidChain b
  castVotes_iff : ∀ i b, (i, b) ∈ s.castVotes ↔ voteCast n s i b
  castProps_iff : ∀ e b, (e, b) ∈ s.castProps ↔ propCast n L s e b

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

/-- A delivered vote is a cast vote. -/
theorem voteMsg_cast {s : St n} {i : Fin n} {b : Blk} :
    voteMsg n s i b → voteCast n s i b := by
  rintro ⟨m, hm, hsrc, hb⟩
  exact ⟨m, Or.inr hm, hsrc, hb⟩

/-- Membership in a block's seen-voter set is having delivered that vote. -/
@[tla_msgs] theorem mem_votersSeen {s : St n} {i : Fin n} {b : Blk} :
    i ∈ votersSeen n s b ↔ voteMsg n s i b := by
  simp only [votersSeen, voteMsg, Finset.mem_image, Finset.mem_filter]
  grind

/-- Membership in a block's cast-voter set is having cast that vote. -/
@[tla_msgs] theorem mem_votersCast {s : St n} {i : Fin n} {b : Blk} :
    i ∈ votersCast n s b ↔ (i, b) ∈ s.castVotes := by
  simp [votersCast]

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
  exact hinv.voteSeenParent i B hih ((hinv.castVotes_iff i B).2 (voteMsg_cast n hiv))

/-! ## Fact 3: two honest leaders propose at strictly growing lengths -/

/-- **Fact 3** (mathematical core): an honest `L(e+1)` that proposed `b₁`
extends a longest chain notarized by epoch `e` (`Inv.propLongest`); if some
chain of length ≥ `b₀.length` was notarized by epoch `e`, then
`b₀.length < b₁.length`. -/
theorem proposal_growth {s : St n} (hinv : Inv n Byz Δ f L s)
    {e : ℕ} {b₀ b₁ : Blk}
    (_hp0 : propCast n L s e b₀) (hp1 : propCast n L s (e + 1) b₁)
    (_hL0 : L e ∉ Byz) (hL1 : L (e + 1) ∉ Byz)
    (hseen : ∃ C : Blk, NotarizedBy n f s C e ∧ b₀.length ≤ C.length) :
    b₀.length < b₁.length := by
  rcases hseen with ⟨C, hC, hlen⟩
  have hle : C.length ≤ b₁.tail.length :=
    hinv.propLongest (e + 1) b₁ ((hinv.castProps_iff (e + 1) b₁).2 hp1) hL1 C hC
  have hb1valid : ValidChain b₁ :=
    hinv.propValid (e + 1) b₁ ((hinv.castProps_iff (e + 1) b₁).2 hp1) hL1
  have hb1pos : 0 < b₁.length := by
    exact List.length_pos_of_mem hb1valid.1
  have hb1len : b₁.length = b₁.tail.length + 1 := by
    have h : b₁.tail.length = b₁.length - 1 := List.length_tail
    omega
  omega

/-! ## The protocol actions (honest nodes only; Byzantine nodes are silent) -/

/-- The honest leader of epoch `e` proposes `b` at the start of the epoch:
`b` is valid, of epoch `e`, extends a longest chain notarized by `e - 1` in
the leader's view. -/
def Propose (e : ℕ) (b : Blk) : Action (St n) := fun s s' =>
  (∀ b' : Blk, ¬ propCast n L s e b') ∧
  L e ∉ Byz ∧ ValidChain b ∧ bep b = e ∧ curEpoch Δ s.now = e ∧
  ChainNotarizedSeen n f s b.tail ∧
  ChainNotarizedBy n f s b.tail (e - 1) ∧
  (∀ C : Blk, NotarizedBy n f s C (e - 1) → C.length ≤ b.tail.length) ∧
  Send n (⟨L e, s.now, Body.prop e b⟩ : Msg n) s s'

/-- An honest node votes for `b` in its own epoch: valid, first vote of the
epoch, extends a longest notarized chain seen. -/
def VoteH (i : Fin n) (b : Blk) : Action (St n) := fun s s' =>
  i ∉ Byz ∧ ValidChain b ∧ 0 < bep b ∧ bep b = curEpoch Δ s.now ∧
  (∀ b' : Blk, voteCast n s i b' → bep b' ≠ bep b) ∧
  propCast n L s (bep b) b ∧
  ChainNotarizedSeen n f s b.tail ∧
  ChainNotarizedBy n f s b.tail (bep b - 1) ∧
  (∀ C : Blk, NotarizedBy n f s C (bep b - 1) → C.length ≤ b.tail.length) ∧
  Send n (⟨i, s.now, Body.vote b⟩ : Msg n) s s'

/-- The protocol step relation: ticks, honest proposals, honest votes, and
delivery. (Faulty nodes are modeled as silent — the crash-fault setting;
Byzantine equivocation is a follow-up.) -/
def PNext : Action (St n) := fun s s' =>
  Tick n Byz Δ GST s s' ∨ (∃ e b, Propose n Byz Δ f L e b s s') ∨
    (∃ i b, VoteH n Byz Δ f L i b s s') ∨ (∃ m, Deliver n Byz Δ GST m s s')

/-- Initially: round 0, nothing in flight, nothing seen. -/
def PInit : StatePred (St n) := { s | s.now = 0 ∧ s.inflight = ∅ ∧ s.seen = ∅ ∧ s.castVotes = ∅ ∧ s.castProps = ∅ }

/-- The protocol specification. -/
def PSpec : Pred (St n) := tlaAnd (statePred (PInit n)) (stutAlways (PNext n Byz Δ GST f L) (vars n))

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
    NotarizedCast n f s b → NotarizedCast n f s' b := by
  intro hN
  unfold NotarizedCast at hN ⊢
  exact le_trans hN (Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset_filter (p := fun p => p.2 = b) h)))

/-- NotarizedBy is monotone in the cast-vote history. -/
theorem notarizedBy_mono_cast {s s' : St n} (h : s.castVotes ⊆ s'.castVotes) {b : Blk} {e : ℕ} :
    NotarizedBy n f s b e → NotarizedBy n f s' b e := by
  rintro ⟨hN, hbep⟩
  exact ⟨notarizedCast_mono n f h hN, hbep⟩

/-- ChainNotarizedBy is monotone in the cast-vote history. -/
theorem chainNotarizedBy_mono_cast {s s' : St n} (h : s.castVotes ⊆ s'.castVotes) {c : Blk} {e : ℕ} :
    ChainNotarizedBy n f s c e → ChainNotarizedBy n f s' c e := by
  intro hc d hd hs
  exact notarizedBy_mono_cast n f h (hc d hd hs)

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

/-- A single send of `m` (which enters `inflight`) extends `voteCast` by
exactly `m` when `m` is a vote. -/
theorem voteCast_send {s s' : St n} {m : Msg n}
    (hinf : s'.inflight = insert m s.inflight) (hseen : s'.seen = s.seen)
    (i : Fin n) (b : Blk) :
    voteCast n s' i b ↔ voteCast n s i b ∨ (m.src = i ∧ m.body = Body.vote b) := by
  unfold voteCast
  constructor
  · rintro ⟨x, hx, hsrc, hbody⟩
    rw [hinf, hseen, Finset.mem_insert] at hx
    rcases hx with hx | hx
    · rcases hx with hx | hx
      · subst x
        exact Or.inr ⟨hsrc, hbody⟩
      · exact Or.inl ⟨x, Or.inl hx, hsrc, hbody⟩
    · exact Or.inl ⟨x, Or.inr hx, hsrc, hbody⟩
  · rintro (h | h)
    · rcases h with ⟨x, hx, hsrc, hbody⟩
      refine ⟨x, ?_, hsrc, hbody⟩
      rw [hinf, hseen]
      rcases hx with hx | hx
      · exact Or.inl (Finset.mem_insert_of_mem hx)
      · exact Or.inr hx
    · rcases h with ⟨hsrc, hbody⟩
      refine ⟨m, ?_, hsrc, hbody⟩
      rw [hinf, hseen]
      exact Or.inl (Finset.mem_insert_self m s.inflight)

/-- A single send of `m` extends `propCast` by exactly `m` when `m` is a
proposal. -/
theorem propCast_send {s s' : St n} {m : Msg n}
    (hinf : s'.inflight = insert m s.inflight) (hseen : s'.seen = s.seen)
    (e : ℕ) (b : Blk) :
    propCast n L s' e b ↔ propCast n L s e b ∨ (m.src = L e ∧ m.body = Body.prop e b) := by
  unfold propCast
  constructor
  · rintro ⟨x, hx, hsrc, hbody⟩
    rw [hinf, hseen, Finset.mem_insert] at hx
    rcases hx with hx | hx
    · rcases hx with hx | hx
      · subst x
        exact Or.inr ⟨hsrc, hbody⟩
      · exact Or.inl ⟨x, Or.inl hx, hsrc, hbody⟩
    · exact Or.inl ⟨x, Or.inr hx, hsrc, hbody⟩
  · rintro (h | h)
    · rcases h with ⟨x, hx, hsrc, hbody⟩
      refine ⟨x, ?_, hsrc, hbody⟩
      rw [hinf, hseen]
      rcases hx with hx | hx
      · exact Or.inl (Finset.mem_insert_of_mem hx)
      · exact Or.inr hx
    · rcases h with ⟨hsrc, hbody⟩
      refine ⟨m, ?_, hsrc, hbody⟩
      rw [hinf, hseen]
      exact Or.inl (Finset.mem_insert_self m s.inflight)

/-- Adding a vote for block `b` to the cast history leaves `NotarizedBy C e`
unchanged whenever `e < bep b` (the new vote is for a block of too late an
epoch to count toward `C`'s quorum at epoch `e`). -/
theorem notarizedBy_stable_cast_vote {s s' : St n} {i : Fin n} {b : Blk}
    (hcv : s'.castVotes = insert (i, b) s.castVotes) {C : Blk} {e : ℕ}
    (hgt : e < bep b) :
    NotarizedBy n f s C e ↔ NotarizedBy n f s' C e := by
  constructor
  · exact notarizedBy_mono_cast n f
      (by intro p hp; rw [hcv]; exact Finset.mem_insert_of_mem hp)
  · rintro ⟨hq, hbep⟩
    refine ⟨?_, hbep⟩
    unfold NotarizedCast at hq ⊢
    have hv : votersCast n s' C = votersCast n s C := by
      unfold votersCast
      rw [hcv]
      have hbC : b ≠ C := by intro h; subst C; omega
      simp [Finset.filter_insert, hbC]
    simpa [hv] using hq

theorem init_inv : ∀ s, s ∈ PInit n → s ∈ InvState n Byz Δ f L := by
  intro s hs
  obtain ⟨_hnow, hinf, hseen, hcv, hcp⟩ := hs
  constructor <;> simp [hinf, hseen, hcv, hcp, voteCast, propCast]

/-- The invariant is preserved by every protocol step. Each safety field is
transported by the cast history (direct membership), the bridge fields by
unfolding `voteCast`/`propCast` over the unchanged frame. -/
/- The invariant is preserved by every protocol step. Each safety field is
transported by the cast history (direct membership), the bridge fields by
unfolding `voteCast`/`propCast` over the unchanged frame. -/
theorem step_inv : ∀ s s', StutAction (PNext n Byz Δ GST f L) (vars n) s s' →
    s ∈ InvState n Byz Δ f L → s' ∈ InvState n Byz Δ f L := by
  intro s s' hstep hinv
  rcases hstep with hnext | hstut
  swap
  · have hss' : s' = s := hstut
    rwa [hss']
  rcases hinv with ⟨hvsp, hpv, hpl, hpc, hvc, hvpr, hvsp2, hvl, hpsp, hpe, hpu, hvv, hcviff, hcpiff⟩
  rcases hnext with htick | ⟨e, bp, hp⟩ | ⟨i, b, hv⟩ | ⟨m, hd⟩
  · -- Tick: clock advances, cast/seen unchanged
    obtain ⟨hnow, hinf, hseen, hcv, hcp, _⟩ := htick
    have hseenmono : ∀ m, m ∈ s.seen → m ∈ s'.seen := by intro m hm; rw [hseen]; exact hm
    have hcvmono : s.castVotes ⊆ s'.castVotes := by intro p hp; rw [hcv]; exact hp
    have hcvmono' : s'.castVotes ⊆ s.castVotes := by intro p hp; rw [hcv] at hp; exact hp
    have hcpmono : s.castProps ⊆ s'.castProps := by intro p hp; rw [hcp]; exact hp
    have hclockmono : curEpoch Δ s.now ≤ curEpoch Δ s'.now := by rw [hnow]; exact curEpoch_mono Δ (Nat.le_succ s.now)
    constructor <;> first
    | intro i b hi hvb
      exact chainNotarizedSeen_mono n f hseenmono (hvsp i b hi (by simpa [hcv] using hvb))
    | intro e b hpb hL
      exact hpv e b (by simpa [hcp] using hpb) hL
    | intro e b hpb hL C hC
      exact hpl e b (by simpa [hcp] using hpb) hL C (notarizedBy_mono_cast n f hcvmono' hC)
    | intro e b hpb hL
      exact le_trans (hpc e b (by simpa [hcp] using hpb) hL) hclockmono
    | intro i b hi hvb
      exact le_trans (hvc i b hi (by simpa [hcv] using hvb)) hclockmono
    | intro i b hi hvb
      exact hcpmono (hvpr i b hi (by simpa [hcv] using hvb))
    | intro i b hi hvb
      exact chainNotarizedBy_mono_cast n f hcvmono (hvsp2 i b hi (by simpa [hcv] using hvb))
    | intro i b hi hvb C hC
      exact hvl i b hi (by simpa [hcv] using hvb) C (notarizedBy_mono_cast n f hcvmono' hC)
    | intro e b hpb hL
      exact chainNotarizedBy_mono_cast n f hcvmono (hpsp e b (by simpa [hcp] using hpb) hL)
    | intro e b hpb hL
      exact hpe e b (by simpa [hcp] using hpb) hL
    | intro e b₁ b₂ hpb₁ hpb₂ hL
      exact hpu e b₁ b₂ (by simpa [hcp] using hpb₁) (by simpa [hcp] using hpb₂) hL
    | intro i b hi hvb
      exact hvv i b hi (by simpa [hcv] using hvb)
    | simp [hcv, hinf, hseen, voteCast, hcviff]
    | simp [hcp, hinf, hseen, propCast, hcpiff]
  · -- Propose: adds its own proposal to castProps
    obtain ⟨hprior, _, hval, hbep, hcur, _, hparcast, hlong, hsend⟩ := hp
    obtain ⟨_, _, _, hnow, hinf, hseen, hcv, hcp⟩ := hsend
    have hseenmono : ∀ m, m ∈ s.seen → m ∈ s'.seen := by intro m hm; rw [hseen]; exact hm
    have hcvmono : s.castVotes ⊆ s'.castVotes := by intro p hp; rw [hcv]; exact hp
    have hcvmono' : s'.castVotes ⊆ s.castVotes := by intro p hp; rw [hcv] at hp; exact hp
    have hcpmono : s.castProps ⊆ s'.castProps := by intro p hp; rw [hcp]; exact Finset.mem_insert_of_mem hp
    have hclockmono : curEpoch Δ s.now ≤ curEpoch Δ s'.now := by rw [hnow]
    constructor <;> first
    | intro j b' hj hvb
      exact chainNotarizedSeen_mono n f hseenmono (hvsp j b' hj (by simpa [hcv] using hvb))
    | intro e' b' hpb hL
      rw [hcp, Finset.mem_insert] at hpb; rcases hpb with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact hval
      · exact hpv e' b' h hL
    | intro e' b' hpb hL C hC
      rw [hcp, Finset.mem_insert] at hpb; rcases hpb with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact hlong C (notarizedBy_mono_cast n f hcvmono' hC)
      · exact hpl e' b' h hL C (notarizedBy_mono_cast n f hcvmono' hC)
    | intro e' b' hpb hL
      rw [hcp, Finset.mem_insert] at hpb; rcases hpb with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact le_trans (le_of_eq hcur.symm) hclockmono
      · exact le_trans (hpc e' b' h hL) hclockmono
    | intro j b' hj hvb
      exact le_trans (hvc j b' hj (by simpa [hcv] using hvb)) hclockmono
    | intro j b' hj hvb
      exact hcpmono (hvpr j b' hj (by simpa [hcv] using hvb))
    | intro j b' hj hvb
      exact chainNotarizedBy_mono_cast n f hcvmono (hvsp2 j b' hj (by simpa [hcv] using hvb))
    | intro j b' hj hvb C hC
      exact hvl j b' hj (by simpa [hcv] using hvb) C (notarizedBy_mono_cast n f hcvmono' hC)
    | intro e' b' hpb hL
      rw [hcp, Finset.mem_insert] at hpb; rcases hpb with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact chainNotarizedBy_mono_cast n f hcvmono hparcast
      · exact chainNotarizedBy_mono_cast n f hcvmono (hpsp e' b' h hL)
    | intro e' b' hpb hL
      rw [hcp, Finset.mem_insert] at hpb; rcases hpb with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact hbep
      · exact hpe e' b' h hL
    | intro e1 b₁ b₂ hpb₁ hpb₂ hL
      rw [hcp, Finset.mem_insert] at hpb₁ hpb₂
      rcases hpb₁ with h₁ | h₁ <;> rcases hpb₂ with h₂ | h₂
      · obtain ⟨_, rfl⟩ := Prod.mk.inj h₁; obtain ⟨_, rfl⟩ := Prod.mk.inj h₂; rfl
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₁; exfalso; exact hprior b₂ ((hcpiff e1 b₂).1 h₂)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₂; exfalso; exact hprior b₁ ((hcpiff e1 b₁).1 h₁)
      · exact hpu e1 b₁ b₂ h₁ h₂ hL
    | intro j b' hj hvb
      exact hvv j b' hj (by simpa [hcv] using hvb)
    | intro i b
      rw [hcv, hcviff i b]
      rw [voteCast_send n hinf hseen i b]
      constructor
      · intro h; exact Or.inl h
      · rintro (h | h)
        · exact h
        · rcases h with ⟨_, hb⟩; cases hb
    | intro e' b'
      rw [hcp, Finset.mem_insert, hcpiff e' b']
      rw [propCast_send n L hinf hseen e' b']
      constructor
      · rintro (h | h)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact Or.inr ⟨rfl, rfl⟩
        · exact Or.inl h
      · rintro (h | h)
        · exact Or.inr h
        · rcases h with ⟨_, hb⟩; left; cases hb; rfl
  · -- VoteH: adds its own vote to castVotes
    obtain ⟨_, hval, hbpos, hbcur, _, hprop, hparseen, hparcast, hlong, hsend⟩ := hv
    obtain ⟨_, _, _, hnow, hinf, hseen, hcv, hcp⟩ := hsend
    have hseenmono : ∀ m, m ∈ s.seen → m ∈ s'.seen := by intro m hm; rw [hseen]; exact hm
    have hcvmono : s.castVotes ⊆ s'.castVotes := by intro p hp; rw [hcv]; exact Finset.mem_insert_of_mem hp
    have hcpmono : s.castProps ⊆ s'.castProps := by intro p hp; rw [hcp]; exact hp
    have hclockmono : curEpoch Δ s.now ≤ curEpoch Δ s'.now := by rw [hnow]
    constructor <;> first
    | intro j b' hj hvb
      rw [hcv, Finset.mem_insert] at hvb; rcases hvb with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact chainNotarizedSeen_mono n f hseenmono hparseen
      · exact chainNotarizedSeen_mono n f hseenmono (hvsp j b' hj h)
    | intro e' b' hpb hL
      exact hpv e' b' (by simpa [hcp] using hpb) hL
    | intro e' b' hpb hL C hC
      have hgt : e' - 1 < bep b := by
        have hle : e' ≤ curEpoch Δ s.now := hpc e' b' (by simpa [hcp] using hpb) hL
        omega
      exact hpl e' b' (by simpa [hcp] using hpb) hL C ((notarizedBy_stable_cast_vote n f hcv hgt).2 hC)
    | intro e' b' hpb hL
      exact le_trans (hpc e' b' (by simpa [hcp] using hpb) hL) hclockmono
    | intro j b' hj hvb
      rw [hcv, Finset.mem_insert] at hvb; rcases hvb with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact le_trans (le_of_eq hbcur) hclockmono
      · exact le_trans (hvc j b' hj h) hclockmono
    | intro j b' hj hvb
      rw [hcv, Finset.mem_insert] at hvb; rcases hvb with h | h
      · obtain ⟨hji, hbb⟩ := Prod.mk.inj h; subst j; subst b'
        exact hcpmono ((hcpiff (bep b) b).2 hprop)
      · exact hcpmono (hvpr j b' hj h)
    | intro j b' hj hvb
      rw [hcv, Finset.mem_insert] at hvb; rcases hvb with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact chainNotarizedBy_mono_cast n f hcvmono hparcast
      · exact chainNotarizedBy_mono_cast n f hcvmono (hvsp2 j b' hj h)
    | intro j b' hj hvb C hC
      rw [hcv, Finset.mem_insert] at hvb; rcases hvb with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact hlong C ((notarizedBy_stable_cast_vote n f hcv (by omega)).2 hC)
      · have hgt : bep b' - 1 < bep b := by
          have hle : bep b' ≤ curEpoch Δ s.now := hvc j b' hj h
          omega
        exact hvl j b' hj h C ((notarizedBy_stable_cast_vote n f hcv hgt).2 hC)
    | intro e' b' hpb hL
      exact chainNotarizedBy_mono_cast n f hcvmono (hpsp e' b' (by simpa [hcp] using hpb) hL)
    | intro e' b' hpb hL
      exact hpe e' b' (by simpa [hcp] using hpb) hL
    | intro e₁ b₁ b₂ hpb₁ hpb₂ hL
      exact hpu e₁ b₁ b₂ (by simpa [hcp] using hpb₁) (by simpa [hcp] using hpb₂) hL
    | intro j b' hj hvb
      rw [hcv, Finset.mem_insert] at hvb; rcases hvb with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact hval
      · exact hvv j b' hj h
    | intro j b'
      rw [hcv, Finset.mem_insert, hcviff j b']
      rw [voteCast_send n hinf hseen j b']
      constructor
      · rintro (h | h)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact Or.inr ⟨rfl, rfl⟩
        · exact Or.inl h
      · rintro (h | h)
        · exact Or.inr h
        · rcases h with ⟨hij, hb⟩; left; rw [hij]; cases hb; rfl
    | intro e' b'
      rw [hcp, hcpiff e' b']
      rw [propCast_send n L hinf hseen e' b']
      constructor
      · intro h; exact Or.inl h
      · rintro (h | h)
        · exact h
        · rcases h with ⟨_, hb⟩; cases hb
  · -- Deliver: seen grows, cast/clock unchanged
    obtain ⟨hmem, _, hnow, hinf, hseen, hcv, hcp⟩ := hd
    have hseenmono : ∀ m, m ∈ s.seen → m ∈ s'.seen := by intro m hm; rw [hseen]; exact Finset.mem_insert_of_mem hm
    have hcvmono : s.castVotes ⊆ s'.castVotes := by intro p hp; rw [hcv]; exact hp
    have hcvmono' : s'.castVotes ⊆ s.castVotes := by intro p hp; rw [hcv] at hp; exact hp
    have hcpmono : s.castProps ⊆ s'.castProps := by intro p hp; rw [hcp]; exact hp
    have hclockmono : curEpoch Δ s.now ≤ curEpoch Δ s'.now := by rw [hnow]
    constructor <;> first
    | intro i b hi hvb
      exact chainNotarizedSeen_mono n f hseenmono (hvsp i b hi (by simpa [hcv] using hvb))
    | intro e b hpb hL
      exact hpv e b (by simpa [hcp] using hpb) hL
    | intro e b hpb hL C hC
      exact hpl e b (by simpa [hcp] using hpb) hL C (notarizedBy_mono_cast n f hcvmono' hC)
    | intro e b hpb hL
      exact le_trans (hpc e b (by simpa [hcp] using hpb) hL) hclockmono
    | intro i b hi hvb
      exact le_trans (hvc i b hi (by simpa [hcv] using hvb)) hclockmono
    | intro i b hi hvb
      exact hcpmono (hvpr i b hi (by simpa [hcv] using hvb))
    | intro i b hi hvb
      exact chainNotarizedBy_mono_cast n f hcvmono (hvsp2 i b hi (by simpa [hcv] using hvb))
    | intro i b hi hvb C hC
      exact hvl i b hi (by simpa [hcv] using hvb) C (notarizedBy_mono_cast n f hcvmono' hC)
    | intro e b hpb hL
      exact chainNotarizedBy_mono_cast n f hcvmono (hpsp e b (by simpa [hcp] using hpb) hL)
    | intro e b hpb hL
      exact hpe e b (by simpa [hcp] using hpb) hL
    | intro e b₁ b₂ hpb₁ hpb₂ hL
      exact hpu e b₁ b₂ (by simpa [hcp] using hpb₁) (by simpa [hcp] using hpb₂) hL
    | intro i b hi hvb
      exact hvv i b hi (by simpa [hcv] using hvb)
    | intro i b
      rw [hcv, hcviff i b]
      unfold voteCast
      constructor
      · rintro ⟨x, hx, hsrc, hb⟩
        exact ⟨x, (sent_eq_deliver n hmem hinf hseen x).2 hx, hsrc, hb⟩
      · rintro ⟨x, hx, hsrc, hb⟩
        exact ⟨x, (sent_eq_deliver n hmem hinf hseen x).1 hx, hsrc, hb⟩
    | intro e' b'
      rw [hcp, hcpiff e' b']
      unfold propCast
      constructor
      · rintro ⟨x, hx, hsrc, hb⟩
        exact ⟨x, (sent_eq_deliver n hmem hinf hseen x).2 hx, hsrc, hb⟩
      · rintro ⟨x, hx, hsrc, hb⟩
        exact ⟨x, (sent_eq_deliver n hmem hinf hseen x).1 hx, hsrc, hb⟩

theorem spec_entails_inv :
    Entails (PSpec n Byz Δ GST f L) (always (statePred (InvState n Byz Δ f L))) :=
  init_invariant_stut (PInit n) (PNext n Byz Δ GST f L) (vars n) (InvState n Byz Δ f L)
    (init_inv n Byz Δ f L) (step_inv n Byz Δ GST f L)

end Bft.Examples.StreamletProto
