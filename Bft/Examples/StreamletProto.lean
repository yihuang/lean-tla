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
  ((s.inflight ++ s.seen).toFinset.filter fun m => m.body = Body.vote b).image (fun m => m.src)

/-- The distinct nodes whose vote for `b` has been delivered. -/
def votersSeen (s : St n) (b : Blk) : Finset (Fin n) :=
  (s.seen.toFinset.filter fun m => m.body = Body.vote b).image (fun m => m.src)

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
  voteSeenParent : ∀ i b, i ∉ Byz → voteCast n s i b → ChainNotarizedSeen n f s b.tail
  propValid : ∀ e b, propCast n L s e b → L e ∉ Byz → ValidChain b
  propLongest : ∀ e b, propCast n L s e b → L e ∉ Byz → ∀ C : Blk,
    NotarizedBy n f s C (e - 1) → C.length ≤ b.tail.length
  propCur : ∀ e b, propCast n L s e b → L e ∉ Byz → e ≤ curEpoch Δ s.now
  voteCur : ∀ i b, i ∉ Byz → voteCast n s i b → bep b ≤ curEpoch Δ s.now
  votedProposed : ∀ i b, i ∉ Byz → voteCast n s i b → propCast n L s (bep b) b
  votedSeenParent : ∀ i b, i ∉ Byz → voteCast n s i b → ChainNotarizedBy n f s b.tail (bep b - 1)
  votedLongest : ∀ i b, i ∉ Byz → voteCast n s i b → ∀ C : Blk,
    NotarizedBy n f s C (bep b - 1) → C.length ≤ b.tail.length
  proposedSeenParent : ∀ e b, propCast n L s e b → L e ∉ Byz →
    ChainNotarizedBy n f s b.tail (e - 1)
  proposedEpoch : ∀ e b, propCast n L s e b → L e ∉ Byz → bep b = e
  propUniq : ∀ e b₁ b₂, propCast n L s e b₁ → propCast n L s e b₂ → L e ∉ Byz → b₁ = b₂
  voteValid : ∀ i b, i ∉ Byz → voteCast n s i b → ValidChain b

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
  simp only [votersSeen, voteMsg, Finset.mem_image, Finset.mem_filter, List.mem_toFinset]
  grind

/-- Membership in a block's cast-voter set is having cast that vote. -/
@[tla_msgs] theorem mem_votersCast {s : St n} {i : Fin n} {b : Blk} :
    i ∈ votersCast n s b ↔ voteCast n s i b := by
  simp only [votersCast, voteCast, Finset.mem_image, Finset.mem_filter,
    List.mem_toFinset, List.mem_append]
  grind

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
  exact hinv.voteSeenParent i B hih (voteMsg_cast n hiv)

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
  have hle : C.length ≤ b₁.tail.length := hinv.propLongest (e + 1) b₁ hp1 hL1 C hC
  have hb1valid : ValidChain b₁ := hinv.propValid (e + 1) b₁ hp1 hL1
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
def PInit : StatePred (St n) := { s | s.now = 0 ∧ s.inflight = [] ∧ s.seen = [] }

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

/-- Delivery moves a message from `inflight` to `seen`, leaving the sent set
(`inflight ∨ seen`) unchanged. -/
theorem sent_eq_deliver {s s' : St n} {m0 : Msg n}
    (hm0 : m0 ∈ s.inflight)
    (hinf : s'.inflight = s.inflight.erase m0) (hseen : s'.seen = m0 :: s.seen) :
    ∀ m, (m ∈ s'.inflight ∨ m ∈ s'.seen) ↔ (m ∈ s.inflight ∨ m ∈ s.seen) := by
  intro m
  constructor
  · intro hm
    rcases hm with h | h
    · rw [hinf] at h; left; exact List.mem_of_mem_erase h
    · rw [hseen] at h
      rcases List.mem_cons.mp h with h | h
      · subst h; left; exact hm0
      · right; exact h
  · intro hm
    rcases hm with h | h
    · by_cases heq : m = m0
      · right; rw [hseen]; exact List.mem_cons.mpr (Or.inl heq)
      · left; rw [hinf]; exact (List.mem_erase_of_ne heq).mpr h
    · right; rw [hseen]; exact List.mem_cons_of_mem m0 h

/-- `voteCast` is unchanged when the sent set is unchanged. -/
theorem voteCast_sent_eq {s s' : St n}
    (h : ∀ m, (m ∈ s'.inflight ∨ m ∈ s'.seen) ↔ (m ∈ s.inflight ∨ m ∈ s.seen))
    (i : Fin n) (b : Blk) :
    voteCast n s' i b ↔ voteCast n s i b := by
  constructor
  · rintro ⟨m, hm, hsrc, hb⟩; exact ⟨m, (h m).1 hm, hsrc, hb⟩
  · rintro ⟨m, hm, hsrc, hb⟩; exact ⟨m, (h m).2 hm, hsrc, hb⟩

/-- `propCast` is unchanged when the sent set is unchanged. -/
theorem propCast_sent_eq {s s' : St n}
    (h : ∀ m, (m ∈ s'.inflight ∨ m ∈ s'.seen) ↔ (m ∈ s.inflight ∨ m ∈ s.seen))
    (e : ℕ) (b : Blk) :
    propCast n L s' e b ↔ propCast n L s e b := by
  constructor
  · rintro ⟨m, hm, hsrc, hb⟩; exact ⟨m, (h m).1 hm, hsrc, hb⟩
  · rintro ⟨m, hm, hsrc, hb⟩; exact ⟨m, (h m).2 hm, hsrc, hb⟩

/-- A sent proposal is not a vote: `voteCast` is unchanged by a proposal. -/
theorem voteCast_send_prop {s s' : St n} {e0 : ℕ} {b0 : Blk} {t : ℕ}
    (hinf : s'.inflight = ⟨L e0, t, Body.prop e0 b0⟩ :: s.inflight)
    (hseen : s'.seen = s.seen) (j : Fin n) (b : Blk) :
    voteCast n s' j b ↔ voteCast n s j b := by
  constructor
  · rintro ⟨m, hm, hsrc, hb⟩
    rw [hinf, hseen] at hm
    rcases hm with hm | hm
    · rcases List.mem_cons.mp hm with hm | hm
      · subst hm
        cases hb
      · exact ⟨m, Or.inl hm, hsrc, hb⟩
    · exact ⟨m, Or.inr hm, hsrc, hb⟩
  · rintro ⟨m, hm, hsrc, hb⟩
    rcases hm with hm | hm
    · exact ⟨m, by rw [hinf, hseen]; left; exact List.mem_cons_of_mem _ hm, hsrc, hb⟩
    · exact ⟨m, by rw [hinf, hseen]; right; exact hm, hsrc, hb⟩

/-- Sending a proposal adds exactly one proposal (the new one). -/
theorem propCast_send_prop_iff {s s' : St n} {e0 : ℕ} {b0 : Blk} {t : ℕ}
    (hinf : s'.inflight = ⟨L e0, t, Body.prop e0 b0⟩ :: s.inflight)
    (hseen : s'.seen = s.seen) (e : ℕ) (b : Blk) :
    propCast n L s' e b ↔ (propCast n L s e b ∨ (e = e0 ∧ b = b0)) := by
  constructor
  · rintro ⟨m, hm, hsrc, hb⟩
    rw [hinf, hseen] at hm
    rcases hm with hm | hm
    · rcases List.mem_cons.mp hm with hm | hm
      · right
        have hb' : Body.prop e b = Body.prop e0 b0 := by simpa [hm] using hb.symm
        cases hb'
        exact ⟨rfl, rfl⟩
      · left; exact ⟨m, Or.inl hm, hsrc, hb⟩
    · left; exact ⟨m, Or.inr hm, hsrc, hb⟩
  · rintro (h | h)
    · rcases h with ⟨m, hm, hsrc, hb⟩
      refine ⟨m, ?_, hsrc, hb⟩
      rcases hm with hm | hm
      · left; rw [hinf]; exact List.mem_cons_of_mem _ hm
      · right; rw [hseen]; exact hm
    · rcases h with ⟨he, hb⟩
      subst e
      subst b
      exact ⟨⟨L e0, t, Body.prop e0 b0⟩, Or.inl (by rw [hinf]; exact List.mem_cons_self), rfl, rfl⟩

/-- A sent proposal does not affect `votersCast` (it is not a vote). -/
theorem votersCast_send_prop {s s' : St n} {e0 : ℕ} {b0 : Blk} {t : ℕ}
    (hinf : s'.inflight = ⟨L e0, t, Body.prop e0 b0⟩ :: s.inflight)
    (hseen : s'.seen = s.seen) {C : Blk} :
    votersCast n s' C = votersCast n s C := by
  ext j
  rw [mem_votersCast n, mem_votersCast n]
  exact voteCast_send_prop n L hinf hseen j C

/-- A sent vote for a different block does not affect `votersCast C`. -/
theorem votersCast_send_vote_ne {s s' : St n} {i : Fin n} {b : Blk} {t : ℕ}
    (hinf : s'.inflight = ⟨i, t, Body.vote b⟩ :: s.inflight)
    (hseen : s'.seen = s.seen) {C : Blk} (hCb : C ≠ b) :
    votersCast n s' C = votersCast n s C := by
  ext j
  rw [mem_votersCast n, mem_votersCast n]
  constructor
  · rintro ⟨m, hm, hsrc, hb⟩
    rw [hinf, hseen] at hm
    rcases hm with hm | hm
    · rcases List.mem_cons.mp hm with hm | hm
      · have hCb' : C = b := by
          have hb' : Body.vote C = Body.vote b := by simpa [hm] using hb.symm
          cases hb'
          rfl
        exact (hCb hCb').elim
      · exact ⟨m, Or.inl hm, hsrc, hb⟩
    · exact ⟨m, Or.inr hm, hsrc, hb⟩
  · rintro ⟨m, hm, hsrc, hb⟩
    refine ⟨m, ?_, hsrc, hb⟩
    rcases hm with hm | hm
    · left; rw [hinf]; exact List.mem_cons_of_mem ⟨i, t, Body.vote b⟩ hm
    · right; rw [hseen]; exact hm

/-- A proposal does not change `NotarizedBy`. -/
theorem notarizedBy_stable_prop {s s' : St n} {e0 : ℕ} {b0 : Blk} {t : ℕ}
    (hinf : s'.inflight = ⟨L e0, t, Body.prop e0 b0⟩ :: s.inflight)
    (hseen : s'.seen = s.seen) {C : Blk} {e : ℕ} :
    NotarizedBy n f s C e ↔ NotarizedBy n f s' C e := by
  constructor <;> intro h
  · rcases h with ⟨hN, hbep⟩
    refine ⟨?_, hbep⟩
    unfold NotarizedCast at hN ⊢
    rw [votersCast_send_prop n L hinf hseen]
    exact hN
  · rcases h with ⟨hN, hbep⟩
    refine ⟨?_, hbep⟩
    unfold NotarizedCast at hN ⊢
    rw [← votersCast_send_prop n L hinf hseen]
    exact hN

/-- A vote for `b` does not change `NotarizedBy C e` when `e < bep b` (its
own epoch is too late to matter for a notarization bounded by `e`). -/
theorem notarizedBy_stable_vote {s s' : St n} {i : Fin n} {b : Blk} {t : ℕ}
    (hinf : s'.inflight = ⟨i, t, Body.vote b⟩ :: s.inflight)
    (hseen : s'.seen = s.seen) {C : Blk} {e : ℕ} (hgt : e < bep b) :
    NotarizedBy n f s C e ↔ NotarizedBy n f s' C e := by
  constructor <;> intro h
  · rcases h with ⟨hN, hbep⟩
    have hCb : C ≠ b := by intro hCb; subst C; exact (not_le_of_gt hgt) hbep
    refine ⟨?_, hbep⟩
    unfold NotarizedCast at hN ⊢
    rw [votersCast_send_vote_ne n hinf hseen hCb]
    exact hN
  · rcases h with ⟨hN, hbep⟩
    have hCb : C ≠ b := by intro hCb; subst C; exact (not_le_of_gt hgt) hbep
    refine ⟨?_, hbep⟩
    unfold NotarizedCast at hN ⊢
    rw [← votersCast_send_vote_ne n hinf hseen hCb]
    exact hN

/-- A sent vote for a different `(node, block)` pair is not the tracked vote. -/
theorem voteCast_back_vote {s s' : St n} {i : Fin n} {b0 : Blk} {t : ℕ}
    (hinf : s'.inflight = ⟨i, t, Body.vote b0⟩ :: s.inflight)
    (hseen : s'.seen = s.seen) {j : Fin n} {b : Blk}
    (hne : j ≠ i ∨ b ≠ b0) :
    voteCast n s' j b → voteCast n s j b := by
  rintro ⟨m, hm, hsrc, hb⟩
  rw [hinf, hseen] at hm
  rcases hm with hm | hm
  · rcases List.mem_cons.mp hm with hm | hm
    · have hji : j = i := by simpa [hm] using hsrc.symm
      have hbb0 : b = b0 := by
        have hb' : Body.vote b = Body.vote b0 := by simpa [hm] using hb.symm
        cases hb'
        rfl
      cases hne with
      | inl h => exact (h hji).elim
      | inr h => exact (h hbb0).elim
    · exact ⟨m, Or.inl hm, hsrc, hb⟩
  · exact ⟨m, Or.inr hm, hsrc, hb⟩

/-- Sending a vote does not create a proposal. -/
theorem propCast_send_vote {s s' : St n} {i : Fin n} {b0 : Blk} {t : ℕ}
    (hinf : s'.inflight = ⟨i, t, Body.vote b0⟩ :: s.inflight)
    (hseen : s'.seen = s.seen) (e : ℕ) (b : Blk) :
    propCast n L s' e b ↔ propCast n L s e b := by
  constructor
  · rintro ⟨m, hm, hsrc, hb⟩
    rw [hinf, hseen] at hm
    rcases hm with hm | hm
    · rcases List.mem_cons.mp hm with hm | hm
      · subst hm
        cases hb
      · exact ⟨m, Or.inl hm, hsrc, hb⟩
    · exact ⟨m, Or.inr hm, hsrc, hb⟩
  · rintro ⟨m, hm, hsrc, hb⟩
    refine ⟨m, ?_, hsrc, hb⟩
    rcases hm with hm | hm
    · left; rw [hinf]; exact List.mem_cons_of_mem _ hm
    · right; rw [hseen]; exact hm

/-- `votersCast` is unchanged when the sent set is unchanged. -/
theorem votersCast_sent_eq {s s' : St n}
    (h : ∀ m, (m ∈ s'.inflight ∨ m ∈ s'.seen) ↔ (m ∈ s.inflight ∨ m ∈ s.seen))
    (b : Blk) : votersCast n s' b = votersCast n s b := by
  ext j
  rw [mem_votersCast n, mem_votersCast n]
  exact voteCast_sent_eq n h j b

/-- `NotarizedBy` is unchanged when the sent set is unchanged. -/
theorem notarizedBy_sent_eq {s s' : St n}
    (h : ∀ m, (m ∈ s'.inflight ∨ m ∈ s'.seen) ↔ (m ∈ s.inflight ∨ m ∈ s.seen))
    (C : Blk) (e : ℕ) : NotarizedBy n f s C e ↔ NotarizedBy n f s' C e := by
  constructor <;> intro hC
  · rcases hC with ⟨hN, hbep⟩
    refine ⟨?_, hbep⟩
    unfold NotarizedCast at hN ⊢
    rw [votersCast_sent_eq n h C]
    exact hN
  · rcases hC with ⟨hN, hbep⟩
    refine ⟨?_, hbep⟩
    unfold NotarizedCast at hN ⊢
    rw [← votersCast_sent_eq n h C]
    exact hN

/-- `ChainNotarizedBy` is unchanged when the sent set is unchanged. -/
theorem chainNotarizedBy_sent_eq {s s' : St n}
    (h : ∀ m, (m ∈ s'.inflight ∨ m ∈ s'.seen) ↔ (m ∈ s.inflight ∨ m ∈ s.seen))
    (c : Blk) (e : ℕ) : ChainNotarizedBy n f s c e ↔ ChainNotarizedBy n f s' c e := by
  constructor <;> intro hc d hd hs
  · exact (notarizedBy_sent_eq n f h d e).1 (hc d hd hs)
  · exact (notarizedBy_sent_eq n f h d e).2 (hc d hd hs)

/-- A proposal does not change `ChainNotarizedBy`. -/
theorem chainNotarizedBy_stable_prop {s s' : St n} {e0 : ℕ} {b0 : Blk} {t : ℕ}
    (hinf : s'.inflight = ⟨L e0, t, Body.prop e0 b0⟩ :: s.inflight)
    (hseen : s'.seen = s.seen) (c : Blk) (e : ℕ) :
    ChainNotarizedBy n f s c e ↔ ChainNotarizedBy n f s' c e := by
  constructor <;> intro hc d hd hs
  · exact (notarizedBy_stable_prop n f L hinf hseen).1 (hc d hd hs)
  · exact (notarizedBy_stable_prop n f L hinf hseen).2 (hc d hd hs)

/-- A later-epoch vote does not change `ChainNotarizedBy` bounded by `e`. -/
theorem chainNotarizedBy_stable_vote {s s' : St n} {i : Fin n} {b : Blk} {t : ℕ}
    (hinf : s'.inflight = ⟨i, t, Body.vote b⟩ :: s.inflight)
    (hseen : s'.seen = s.seen) {c : Blk} {e : ℕ} (hgt : e < bep b) :
    ChainNotarizedBy n f s c e ↔ ChainNotarizedBy n f s' c e := by
  constructor <;> intro hc d hd hs
  · exact (notarizedBy_stable_vote n f hinf hseen hgt).1 (hc d hd hs)
  · exact (notarizedBy_stable_vote n f hinf hseen hgt).2 (hc d hd hs)

/-- The invariant holds initially: no messages have been sent, so every
honest-vote/honest-proposal precondition is vacuous. -/
theorem init_inv : ∀ s, s ∈ PInit n → s ∈ InvState n Byz Δ f L := by
  intro s hs
  obtain ⟨_hnow, hinf, hseen⟩ := hs
  constructor <;> simp [hinf, hseen, voteCast, propCast]

/-- Any step that leaves the sent set unchanged (Tick, Deliver) preserves the
invariant: `seen` only grows, the clock only advances, and every field
transports back to `s` through the stability lemmas. -/
theorem inv_sent_step {s s' : St n}
    (hsent : ∀ x, (x ∈ s'.inflight ∨ x ∈ s'.seen) ↔ (x ∈ s.inflight ∨ x ∈ s.seen))
    (hseenmono : ∀ x, x ∈ s.seen → x ∈ s'.seen)
    (hclockmono : curEpoch Δ s.now ≤ curEpoch Δ s'.now)
    (hinv : Inv n Byz Δ f L s) : Inv n Byz Δ f L s' := by
  constructor <;> first
  | intro j b' hj hvc
    exact chainNotarizedSeen_mono n f hseenmono
      (hinv.voteSeenParent j b' hj ((voteCast_sent_eq n hsent j b').1 hvc))
  | intro e' b' hpc hL'
    exact hinv.propValid e' b' ((propCast_sent_eq n L hsent e' b').1 hpc) hL'
  | intro e' b' hpc hL' C hC
    exact hinv.propLongest e' b' ((propCast_sent_eq n L hsent e' b').1 hpc) hL' C
      ((notarizedBy_sent_eq n f hsent C (e' - 1)).2 hC)
  | intro e' b' hpc hL'
    exact le_trans (hinv.propCur e' b' ((propCast_sent_eq n L hsent e' b').1 hpc) hL') hclockmono
  | intro j b' hj hvc
    exact le_trans (hinv.voteCur j b' hj ((voteCast_sent_eq n hsent j b').1 hvc)) hclockmono
  | intro j b' hj hvc
    exact (propCast_sent_eq n L hsent (bep b') b').2
      (hinv.votedProposed j b' hj ((voteCast_sent_eq n hsent j b').1 hvc))
  | intro j b' hj hvc
    exact (chainNotarizedBy_sent_eq n f hsent b'.tail (bep b' - 1)).1
      (hinv.votedSeenParent j b' hj ((voteCast_sent_eq n hsent j b').1 hvc))
  | intro j b' hj hvc C hC
    exact hinv.votedLongest j b' hj ((voteCast_sent_eq n hsent j b').1 hvc) C
      ((notarizedBy_sent_eq n f hsent C (bep b' - 1)).2 hC)
  | intro e' b' hpc hL'
    exact (chainNotarizedBy_sent_eq n f hsent b'.tail (e' - 1)).1
      (hinv.proposedSeenParent e' b' ((propCast_sent_eq n L hsent e' b').1 hpc) hL')
  | intro e' b' hpc hL'
    exact hinv.proposedEpoch e' b' ((propCast_sent_eq n L hsent e' b').1 hpc) hL'
  | intro e₁ b₁ b₂ hpc₁ hpc₂ hL₁
    exact hinv.propUniq e₁ b₁ b₂ ((propCast_sent_eq n L hsent e₁ b₁).1 hpc₁)
      ((propCast_sent_eq n L hsent e₁ b₂).1 hpc₂) hL₁
  | intro j b' hj hvc
    exact hinv.voteValid j b' hj ((voteCast_sent_eq n hsent j b').1 hvc)

/-- The invariant is preserved by every protocol step. -/
theorem step_inv : ∀ s s', StutAction (PNext n Byz Δ GST f L) (vars n) s s' →
    s ∈ InvState n Byz Δ f L → s' ∈ InvState n Byz Δ f L := by
  intro s s' hstep hinv
  rcases hstep with hnext | hstut
  swap
  · have hss' : s' = s := hstut
    rwa [hss']
  rcases hnext with htick | ⟨e, bp, hp⟩ | ⟨i, b, hv⟩ | ⟨m, hd⟩
  · -- Tick: sent set unchanged, clock advances
    obtain ⟨hnow, hinf, hseen, _⟩ := htick
    exact inv_sent_step n Byz Δ f L
      (by intro x; rw [hinf, hseen])
      (by intro x hx; rw [hseen]; exact hx)
      (by rw [hnow]; exact curEpoch_mono Δ (Nat.le_succ s.now))
      hinv
  · -- Propose e b
    obtain ⟨hprior, hL, hval, hbep, hcur, hparseen, hparcast, hlong, hsend⟩ := hp
    obtain ⟨_hr, _hninf, _hnseen, hnow, hinf, hseen⟩ := hsend
    have hseenmono : ∀ x, x ∈ s.seen → x ∈ s'.seen := by
      intro x hx; rw [hseen]; exact hx
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j b' hj hvc
      have hvc' : voteCast n s j b' := (voteCast_send_prop n L hinf hseen j b').1 hvc
      exact chainNotarizedSeen_mono n f hseenmono (hinv.voteSeenParent j b' hj hvc')
    · intro e' b' hpc hL'
      have hpc' := (propCast_send_prop_iff n L hinf hseen e' b').1 hpc
      rcases hpc' with hpc' | ⟨he, hb⟩
      · exact hinv.propValid e' b' hpc' hL'
      · subst e'; subst b'; exact hval
    · intro e' b' hpc hL' C hC
      have hpc' := (propCast_send_prop_iff n L hinf hseen e' b').1 hpc
      rcases hpc' with hpc' | ⟨he, hb⟩
      · have hC' : NotarizedBy n f s C (e' - 1) := (notarizedBy_stable_prop n f L hinf hseen).2 hC
        exact hinv.propLongest e' b' hpc' hL' C hC'
      · subst e'; subst b'
        exact hlong C ((notarizedBy_stable_prop n f L hinf hseen).2 hC)
    · intro e' b' hpc hL'
      have hpc' := (propCast_send_prop_iff n L hinf hseen e' b').1 hpc
      rcases hpc' with hpc' | ⟨he, hb⟩
      · simpa [hnow] using (hinv.propCur e' b' hpc' hL')
      · subst e'; subst b'; simpa [hnow] using (le_of_eq hcur.symm)
    · intro j b' hj hvc
      have hvc' : voteCast n s j b' := (voteCast_send_prop n L hinf hseen j b').1 hvc
      simpa [hnow] using (hinv.voteCur j b' hj hvc')
    · intro j b' hj hvc
      have hvc' : voteCast n s j b' := (voteCast_send_prop n L hinf hseen j b').1 hvc
      exact (propCast_send_prop_iff n L hinf hseen (bep b') b').2 (Or.inl (hinv.votedProposed j b' hj hvc'))
    · intro j b' hj hvc
      have hvc' : voteCast n s j b' := (voteCast_send_prop n L hinf hseen j b').1 hvc
      exact (chainNotarizedBy_stable_prop n f L hinf hseen b'.tail (bep b' - 1)).1 (hinv.votedSeenParent j b' hj hvc')
    · intro j b' hj hvc C hC
      have hvc' : voteCast n s j b' := (voteCast_send_prop n L hinf hseen j b').1 hvc
      have hC' : NotarizedBy n f s C (bep b' - 1) := (notarizedBy_stable_prop n f L hinf hseen).2 hC
      exact hinv.votedLongest j b' hj hvc' C hC'
    · intro e' b' hpc hL'
      have hpc' := (propCast_send_prop_iff n L hinf hseen e' b').1 hpc
      rcases hpc' with hpc' | ⟨he, hb⟩
      · exact (chainNotarizedBy_stable_prop n f L hinf hseen b'.tail (e' - 1)).1 (hinv.proposedSeenParent e' b' hpc' hL')
      · subst e'; subst b'
        exact (chainNotarizedBy_stable_prop n f L hinf hseen bp.tail (e - 1)).1 hparcast
    · intro e' b' hpc hL'
      have hpc' := (propCast_send_prop_iff n L hinf hseen e' b').1 hpc
      rcases hpc' with hpc' | ⟨he, hb⟩
      · exact hinv.proposedEpoch e' b' hpc' hL'
      · subst e'; subst b'; exact hbep
    · intro e₁ b₁ b₂ hpc₁ hpc₂ hL₁
      have hpc₁' := (propCast_send_prop_iff n L hinf hseen e₁ b₁).1 hpc₁
      have hpc₂' := (propCast_send_prop_iff n L hinf hseen e₁ b₂).1 hpc₂
      rcases hpc₁' with hpc₁' | ⟨he1, hb1⟩
      · rcases hpc₂' with hpc₂' | ⟨he2, hb2⟩
        · exact hinv.propUniq e₁ b₁ b₂ hpc₁' hpc₂' hL₁
        · subst e₁; subst b₂; exfalso; exact hprior b₁ hpc₁'
      · subst e₁; subst b₁
        rcases hpc₂' with hpc₂' | ⟨he2, hb2⟩
        · exfalso; exact hprior b₂ hpc₂'
        · subst b₂; rfl
    · intro j b' hj hvc
      have hvc' : voteCast n s j b' := (voteCast_send_prop n L hinf hseen j b').1 hvc
      exact hinv.voteValid j b' hj hvc'
  · -- VoteH i b
    obtain ⟨hi, hval, hbpos, hbcur, hfirst, hprop, hparseen, hparcast, hlong, hsend⟩ := hv
    obtain ⟨_hr, _hninf, _hnseen, hnow, hinf, hseen⟩ := hsend
    have hseenmono : ∀ x, x ∈ s.seen → x ∈ s'.seen := by
      intro x hx; rw [hseen]; exact hx
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j b' hj hvc
      by_cases hjb : j = i ∧ b' = b
      · rcases hjb with ⟨rfl, rfl⟩
        exact chainNotarizedSeen_mono n f hseenmono hparseen
      · have hne : j ≠ i ∨ b' ≠ b := by
          by_cases hji : j = i
          · right; intro hbb; exact hjb ⟨hji, hbb⟩
          · left; exact hji
        have hvc' : voteCast n s j b' := voteCast_back_vote n hinf hseen hne hvc
        exact chainNotarizedSeen_mono n f hseenmono (hinv.voteSeenParent j b' hj hvc')
    · intro e' b' hpc hL'
      have hpc' : propCast n L s e' b' := (propCast_send_vote n L hinf hseen e' b').1 hpc
      exact hinv.propValid e' b' hpc' hL'
    · intro e' b' hpc hL' C hC
      have hpc' : propCast n L s e' b' := (propCast_send_vote n L hinf hseen e' b').1 hpc
      have hle' : e' ≤ curEpoch Δ s.now := hinv.propCur e' b' hpc' hL'
      have hgt : e' - 1 < bep b := by omega
      have hC' : NotarizedBy n f s C (e' - 1) := (notarizedBy_stable_vote n f hinf hseen hgt).2 hC
      exact hinv.propLongest e' b' hpc' hL' C hC'
    · intro e' b' hpc hL'
      have hpc' : propCast n L s e' b' := (propCast_send_vote n L hinf hseen e' b').1 hpc
      simpa [hnow] using (hinv.propCur e' b' hpc' hL')
    · intro j b' hj hvc
      by_cases hjb : j = i ∧ b' = b
      · rcases hjb with ⟨rfl, rfl⟩
        simpa [hnow] using (le_of_eq hbcur)
      · have hne : j ≠ i ∨ b' ≠ b := by
          by_cases hji : j = i
          · right; intro hbb; exact hjb ⟨hji, hbb⟩
          · left; exact hji
        have hvc' : voteCast n s j b' := voteCast_back_vote n hinf hseen hne hvc
        simpa [hnow] using (hinv.voteCur j b' hj hvc')
    · intro j b' hj hvc
      by_cases hjb : j = i ∧ b' = b
      · rcases hjb with ⟨hji, hbb⟩
        subst j
        subst b'
        exact (propCast_send_vote n L hinf hseen (bep b) b).2 hprop
      · have hne : j ≠ i ∨ b' ≠ b := by
          by_cases hji : j = i
          · right; intro hbb; exact hjb ⟨hji, hbb⟩
          · left; exact hji
        have hvc' : voteCast n s j b' := voteCast_back_vote n hinf hseen hne hvc
        exact (propCast_send_vote n L hinf hseen (bep b') b').2 (hinv.votedProposed j b' hj hvc')
    · intro j b' hj hvc
      by_cases hjb : j = i ∧ b' = b
      · rcases hjb with ⟨rfl, rfl⟩
        exact (chainNotarizedBy_stable_vote n f hinf hseen (by omega)).1 hparcast
      · have hne : j ≠ i ∨ b' ≠ b := by
          by_cases hji : j = i
          · right; intro hbb; exact hjb ⟨hji, hbb⟩
          · left; exact hji
        have hvc' : voteCast n s j b' := voteCast_back_vote n hinf hseen hne hvc
        have hle' : bep b' ≤ curEpoch Δ s.now := hinv.voteCur j b' hj hvc'
        have hgt : bep b' - 1 < bep b := by omega
        exact (chainNotarizedBy_stable_vote n f hinf hseen hgt).1 (hinv.votedSeenParent j b' hj hvc')
    · intro j b' hj hvc C hC
      by_cases hjb : j = i ∧ b' = b
      · rcases hjb with ⟨rfl, rfl⟩
        exact hlong C ((notarizedBy_stable_vote n f hinf hseen (by omega)).2 hC)
      · have hne : j ≠ i ∨ b' ≠ b := by
          by_cases hji : j = i
          · right; intro hbb; exact hjb ⟨hji, hbb⟩
          · left; exact hji
        have hvc' : voteCast n s j b' := voteCast_back_vote n hinf hseen hne hvc
        have hle' : bep b' ≤ curEpoch Δ s.now := hinv.voteCur j b' hj hvc'
        have hgt : bep b' - 1 < bep b := by omega
        have hC' : NotarizedBy n f s C (bep b' - 1) := (notarizedBy_stable_vote n f hinf hseen hgt).2 hC
        exact hinv.votedLongest j b' hj hvc' C hC'
    · intro e' b' hpc hL'
      have hpc' : propCast n L s e' b' := (propCast_send_vote n L hinf hseen e' b').1 hpc
      have hle' : e' ≤ curEpoch Δ s.now := hinv.propCur e' b' hpc' hL'
      have hgt : e' - 1 < bep b := by omega
      exact (chainNotarizedBy_stable_vote n f hinf hseen hgt).1 (hinv.proposedSeenParent e' b' hpc' hL')
    · intro e' b' hpc hL'
      have hpc' : propCast n L s e' b' := (propCast_send_vote n L hinf hseen e' b').1 hpc
      exact hinv.proposedEpoch e' b' hpc' hL'
    · intro e₁ b₁ b₂ hpc₁ hpc₂ hL₁
      have hpc₁' : propCast n L s e₁ b₁ := (propCast_send_vote n L hinf hseen e₁ b₁).1 hpc₁
      have hpc₂' : propCast n L s e₁ b₂ := (propCast_send_vote n L hinf hseen e₁ b₂).1 hpc₂
      exact hinv.propUniq e₁ b₁ b₂ hpc₁' hpc₂' hL₁
    · intro j b' hj hvc
      by_cases hjb : j = i ∧ b' = b
      · rcases hjb with ⟨rfl, rfl⟩
        exact hval
      · have hne : j ≠ i ∨ b' ≠ b := by
          by_cases hji : j = i
          · right; intro hbb; exact hjb ⟨hji, hbb⟩
          · left; exact hji
        have hvc' : voteCast n s j b' := voteCast_back_vote n hinf hseen hne hvc
        exact hinv.voteValid j b' hj hvc'
  · -- Deliver m: sent set unchanged, seen grows
    obtain ⟨hmem, _, hnow, hinf, hseen⟩ := hd
    exact inv_sent_step n Byz Δ f L
      (sent_eq_deliver n hmem hinf hseen)
      (by intro x hx; rw [hseen]; exact List.mem_cons_of_mem m hx)
      (by rw [hnow])
      hinv

/-- Every reachable state satisfies the invariant bundle. -/
theorem spec_entails_inv :
    Entails (PSpec n Byz Δ GST f L) (always (statePred (InvState n Byz Δ f L))) :=
  init_invariant_stut (PInit n) (PNext n Byz Δ GST f L) (vars n) (InvState n Byz Δ f L)
    (init_inv n Byz Δ f L) (step_inv n Byz Δ GST f L)

end Bft.Examples.StreamletProto
