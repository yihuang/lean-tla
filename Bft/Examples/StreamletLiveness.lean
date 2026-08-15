/-
Copyright (c) 2026 lean-tla contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Case study: Streamlet liveness — Lemma 5 and Theorem 6

The state-level liveness core of **Streamlet** (Chan & Shi, §3.6.2), on top of
the partial-sync transport (`StreamletNet`) and the protocol invariants
(`StreamletProto`). This file ports the paper's **Lemma 5**
(`main_liveness_lemma`) and **Theorem 6** (`liveness_finality`) from
`TlaDsl/Examples/StreamletLiveness.lean` to the message-based model.

The facts are pure state-level theorems from the invariant bundle `Inv`; the
temporal wrapper (per-epoch leads-to progress, composed to Theorem 4) is
`StreamletTemporal.lean`. The two key ingredients beyond the safety facts:

* **`propUniq`** — each epoch has at most one proposal (enforced by the
  `Propose` "no prior proposal" guard), so the epoch case-analysis in
  Lemma 5 can conclude `C = bᵢ`.
* **`voteValid`** — honest votes are for valid chains, so a conflicting
  notarized block is a well-formed chain and the length arithmetic applies.
-/
import Bft.Examples.StreamletProto

namespace Bft.Examples.StreamletLiveness

open Bft
open Bft.Examples.StreamletNet (Body Msg St)
open Bft.Examples.Streamlet (Blk ValidChain bep quorum mem_tail_of_bep_pos Consecutive)
open Bft.Examples.StreamletProto

variable (n : ℕ) (Byz : Finset (Fin n)) (Δ GST f : ℕ) (L : ℕ → Fin n)

/-! ## Block and notarization helper lemmas -/

/-- A valid chain is nonempty. -/
theorem ne_nil_of_valid {b : Blk} (hv : ValidChain b) : b ≠ [] := by
  intro h; subst b; exact (List.not_mem_nil (a := 0)) hv.1

/-- A valid chain with positive epoch has a nonempty tail. -/
theorem ne_nil_tail_of_bep_pos {b : Blk} (hv : ValidChain b) (hpos : 0 < bep b) :
    b.tail ≠ [] := by
  have h0t : 0 ∈ b.tail := mem_tail_of_bep_pos hv.1 hpos
  intro h; rw [h] at h0t; exact (List.not_mem_nil (a := 0)) h0t

/-- List length of a nonempty block is its tail length plus one. -/
theorem length_tail_succ {b : Blk} (h : b ≠ []) : b.length = b.tail.length + 1 := by
  have h' : b.tail.length = b.length - 1 := List.length_tail
  have hpos : 0 < b.length := List.length_pos_of_ne_nil h
  omega

/-- A valid chain with positive epoch has length at least two. -/
theorem length_ge_two_of_bep_pos {b : Blk} (hv : ValidChain b) (hpos : 0 < bep b) : 2 ≤ b.length := by
  have h0t : 0 ∈ b.tail := mem_tail_of_bep_pos hv.1 hpos
  have hpos' : 0 < b.tail.length := List.length_pos_of_mem h0t
  have h : b.length = b.tail.length + 1 := length_tail_succ (ne_nil_of_valid hv)
  omega

/-- `NotarizedBy` is monotone in the epoch bound. -/
theorem notarizedBy_mono {s : St n} {b : Blk} {e e' : ℕ} (h : e ≤ e') :
    NotarizedBy n Byz f s b e → NotarizedBy n Byz f s b e' := by
  rintro ⟨hN, hbep⟩
  exact ⟨hN, le_trans hbep h⟩

/-- A chain-notarized nonempty block is itself notarized. -/
theorem chain_notarized_block {s : St n} {b : Blk} {e : ℕ}
    (hc : ChainNotarizedBy n Byz f s b e) (hne : b ≠ []) : NotarizedBy n Byz f s b e :=
  hc b hne (List.suffix_refl b)

/-! ## The honest-proposal bundle -/

/-- The honest leader of epoch `e` has proposed `b`: the proposal is recorded
in the cast history, and the leader is honest. Every invariant field about
honest proposals (`propValid`, `propLongest`, `proposedEpoch`, `propUniq`,
`proposedSeenParent`) takes exactly these two facts, so the liveness theorems
below carry them as one bundled hypothesis per epoch instead of a
`propCast`-plus-honestness pair. -/
structure HonestProposal (s : St n) (e : ℕ) (b : Blk) : Prop where
  mem : (L e, e, b) ∈ s.castProps
  honest : L e ∉ Byz

/-! ## Lemma 5: the longest-chain bound and the main liveness lemma -/

/-- An honest vote for a block of epoch `e₀` equals the honest proposal of
that epoch (`votedProposed` + `propUniq`). -/
theorem voted_eq_proposal_of_epoch {s : St n} (hinv : Inv n Byz Δ f L s)
    {e₀ : ℕ} {b : Blk} {i : Fin n} {C : Blk}
    (hp : HonestProposal n Byz L s e₀ b)
    (hih : i ∉ Byz) (hv : (i, C) ∈ s.castVotes) (hbe : bep C = e₀) :
    C = b := by
  have hCP : (L (bep C), bep C, C) ∈ s.castProps := hinv.votedProposed i C hih hv
  have hCb : (L e₀, e₀, C) ∈ s.castProps := by simpa [hbe] using hCP
  exact hinv.propUniq e₀ C b hCb hp.mem hp.honest

/-- A non-genesis honest vote for `C` with `bep C < e` is no longer than the
honest `e+1` proposal: `C`'s tail is notarized by `bep C - 1 ≤ e`, so
`propLongest` bounds it by `b₁.tail`. -/
theorem voted_le_proposal_of_earlier_epoch {s : St n} (hinv : Inv n Byz Δ f L s)
    {e : ℕ} {b1 C : Blk} {i : Fin n}
    (hp1 : HonestProposal n Byz L s (e + 1) b1)
    (hih : i ∉ Byz) (hv : (i, C) ∈ s.castVotes)
    (hCval : ValidChain C) (hCn0 : C ≠ [0]) (hlt : bep C < e) :
    C.length ≤ b1.length := by
  have hCn : C ≠ [] := ne_nil_of_valid hCval
  have hCpos : 0 < bep C := by
    by_contra hnot
    have h0 : bep C = 0 := Nat.eq_zero_of_not_pos hnot
    exact hCn0 (ValidChain.eq_genesis hCval h0)
  have hCn' : C.tail ≠ [] := ne_nil_tail_of_bep_pos hCval hCpos
  have hCp : ChainNotarizedBy n Byz f s C.tail (bep C - 1) :=
    hinv.votedSeenParent i C hih hv
  have hN : NotarizedBy n Byz f s C.tail (bep C - 1) :=
    chain_notarized_block n Byz f hCp hCn'
  have hN' : NotarizedBy n Byz f s C.tail e :=
    notarizedBy_mono n Byz f (Nat.le_trans (Nat.sub_le (bep C) 1) (le_of_lt hlt)) hN
  have hlenP : C.tail.length ≤ b1.tail.length :=
    hinv.propLongest (e + 1) b1 hp1.mem hp1.honest C.tail hN'
  have hClen' : C.length = C.tail.length + 1 := length_tail_succ hCn
  have hb1len : b1.length = b1.tail.length + 1 :=
    length_tail_succ (ne_nil_of_valid (hinv.propValid (e + 1) b1 hp1.mem hp1.honest))
  rw [hClen', hb1len]
  exact Nat.succ_le_succ hlenP

/-- A block `C` honestly voted in an epoch `> e+2` has tail at least as long
as `b₂` (`votedLongest`). -/
theorem proposal_le_voted_of_later_epoch {s : St n} (hinv : Inv n Byz Δ f L s)
    {e : ℕ} {b2 C : Blk} {i : Fin n}
    (hp2 : HonestProposal n Byz L s (e + 2) b2)
    (hC2 : ChainNotarizedBy n Byz f s b2 (e + 2))
    (hih : i ∉ Byz) (hv : (i, C) ∈ s.castVotes)
    (hgt : e + 2 < bep C) :
    b2.length ≤ C.tail.length := by
  have hlong : ∀ C' : Blk, NotarizedBy n Byz f s C' (bep C - 1) → C'.length ≤ C.tail.length :=
    hinv.votedLongest i C hih hv
  have hb2n : b2 ≠ [] := ne_nil_of_valid (hinv.propValid (e + 2) b2 hp2.mem hp2.honest)
  have hb2N : NotarizedBy n Byz f s b2 (e + 2) := chain_notarized_block n Byz f hC2 hb2n
  have hle' : e + 2 ≤ bep C - 1 := by omega
  have hb2N' : NotarizedBy n Byz f s b2 (bep C - 1) := notarizedBy_mono n Byz f hle' hb2N
  exact hlong b2 hb2N'

/-- A block `C` honestly voted at some point satisfies the five-way epoch
case split against the three honest proposals: it equals one of them, or is
strictly earlier (`bep C < e`), or strictly later (`e + 2 < bep C`). This is
the shared skeleton of `longest_chain_by` and `main_liveness_lemma`. -/
theorem vote_case_of_proposals {s : St n} (hinv : Inv n Byz Δ f L s)
    {e : ℕ} {b0 b1 b2 C : Blk} {i : Fin n}
    (hp0 : HonestProposal n Byz L s e b0)
    (hp1 : HonestProposal n Byz L s (e + 1) b1)
    (hp2 : HonestProposal n Byz L s (e + 2) b2)
    (hih : i ∉ Byz) (hv : (i, C) ∈ s.castVotes) :
    C = b0 ∨ C = b1 ∨ C = b2 ∨ bep C < e ∨ e + 2 < bep C := by
  by_cases h1 : bep C = e
  · exact Or.inl (voted_eq_proposal_of_epoch n Byz Δ f L hinv hp0 hih hv h1)
  · by_cases h2 : bep C = e + 1
    · exact Or.inr (Or.inl (voted_eq_proposal_of_epoch n Byz Δ f L hinv hp1 hih hv h2))
    · by_cases h3 : bep C = e + 2
      · exact Or.inr (Or.inr (Or.inl (voted_eq_proposal_of_epoch n Byz Δ f L hinv hp2 hih hv h3)))
      · exact Or.inr (Or.inr (Or.inr (by omega)))

/-- **The longest-chain bound**: a block notarized by `e+2` is no longer
than the honest `b₂`. -/
theorem longest_chain_by (hB : Byz.card ≤ f) {s : St n} (hinv : Inv n Byz Δ f L s)
    {e : ℕ} {b0 b1 b2 : Blk}
    (hp0 : HonestProposal n Byz L s e b0)
    (hp1 : HonestProposal n Byz L s (e + 1) b1)
    (hp2 : HonestProposal n Byz L s (e + 2) b2)
    (hG01 : b0.length < b1.length) (hG12 : b1.length < b2.length) :
    ∀ C : Blk, NotarizedBy n Byz f s C (e + 2) → C.length ≤ b2.length := by
  intro C hC
  rcases hC with ⟨hN, hbepC⟩
  rcases honest_in_quorum n Byz f hB hN with ⟨i0, hi0, hih⟩
  have hv0 : (i0, C) ∈ s.castVotes := ((mem_votersCast n Byz).mp hi0).1
  have hCval : ValidChain C := hinv.voteValid i0 C hih hv0
  rcases vote_case_of_proposals n Byz Δ f L hinv hp0 hp1 hp2 hih hv0 with hC0 | hC1 | hC2 | hlt | hgt
  · subst C; omega
  · subst C; omega
  · subst C; omega
  · -- `bep C < e`: an older vote; bound `C` by `b₁` via `propLongest`
    by_cases hg : C = [0]
    · subst C
      have hb2n : b2 ≠ [] := ne_nil_of_valid (hinv.propValid (e + 2) b2 hp2.mem hp2.honest)
      have hb2pos : 0 < b2.length := List.length_pos_of_ne_nil hb2n
      simpa using (Nat.succ_le_of_lt hb2pos)
    · have hCleq : C.length ≤ b1.length :=
        voted_le_proposal_of_earlier_epoch n Byz Δ f L hinv hp1 hih hv0 hCval hg hlt
      exact le_trans hCleq (le_of_lt hG12)
  · omega  -- `e + 2 < bep C` contradicts `hbepC : bep C ≤ e + 2`

/-- **Lemma 5** (main liveness lemma): three consecutive honest-leader
proposals with growing lengths and the third chain-notarized on time — no
conflicting block at `b₂`'s length is ever notarized. -/
theorem main_liveness_lemma (hB : Byz.card ≤ f) {s : St n} (hinv : Inv n Byz Δ f L s)
    {e : ℕ} {b0 b1 b2 : Blk}
    (hp0 : HonestProposal n Byz L s e b0)
    (hp1 : HonestProposal n Byz L s (e + 1) b1)
    (hp2 : HonestProposal n Byz L s (e + 2) b2)
    (hG01 : b0.length < b1.length) (hG12 : b1.length < b2.length)
    (hC2 : ChainNotarizedBy n Byz f s b2 (e + 2)) :
    ∀ C : Blk, C ≠ b2 → C.length = b2.length → ¬ NotarizedCast n Byz f s C := by
  intro C hCne hClen hNC
  rcases honest_in_quorum n Byz f hB hNC with ⟨i0, hi0, hih⟩
  have hv0 : (i0, C) ∈ s.castVotes := ((mem_votersCast n Byz).mp hi0).1
  have hCval : ValidChain C := hinv.voteValid i0 C hih hv0
  rcases vote_case_of_proposals n Byz Δ f L hinv hp0 hp1 hp2 hih hv0 with hC0 | hC1 | hC2 | hlt | hgt
  · subst C; omega
  · subst C; omega
  · exact (hCne hC2).elim
  · -- earlier: `C ≤ b₁ < b₂ = C`, contradiction
    have hb2ge2 : 2 ≤ b2.length := by
      have hb2pos : 0 < bep b2 := by
        have h : bep b2 = e + 2 := hinv.proposedEpoch (e + 2) b2 hp2.mem hp2.honest
        omega
      exact length_ge_two_of_bep_pos (hinv.propValid (e + 2) b2 hp2.mem hp2.honest) hb2pos
    have hCge2 : 2 ≤ C.length := by rw [hClen]; exact hb2ge2
    have hCn0 : C ≠ [0] := by
      intro hCg; subst C; simp at hCge2
    have hCleq : C.length ≤ b1.length :=
      voted_le_proposal_of_earlier_epoch n Byz Δ f L hinv hp1 hih hv0 hCval hCn0 hlt
    have hlt' : C.length < b2.length := lt_of_le_of_lt hCleq hG12
    rw [hClen] at hlt'
    exact (lt_irrefl b2.length) hlt'
  · -- later: `e+2 < bep C`, so `b₂ ≤ C.tail < C`
    have hb2le : b2.length ≤ C.tail.length :=
      proposal_le_voted_of_later_epoch n Byz Δ f L hinv hp2 hC2 hih hv0 hgt
    have hCn : C ≠ [] := ne_nil_of_valid hCval
    have hClen' : C.length = C.tail.length + 1 := length_tail_succ hCn
    omega

/-! ## Theorem 6: five honest leaders finalize -/

/-- A block is final when it is the middle of three adjacent notarized
blocks with consecutive epochs on a fully notarized chain. -/
def ChainNotarizedCast (s : St n) (c : Blk) : Prop :=
  ∀ d : Blk, d ≠ [] → d <:+ c → NotarizedCast n Byz f s d

/-- A block is final: the middle `b` of a `Consecutive` triple of
notarized blocks with positive starting epoch on a notarized chain. -/
def Finalized (s : St n) (e : ℕ) (b0 b b2 : Blk) : Prop :=
  0 < e ∧ bep b0 = e ∧ Consecutive b0 b b2 ∧ ChainNotarizedCast n Byz f s b2

/-- Some block is final. -/
def FinalSome (s : St n) : Prop :=
  ∃ e b0 b b2, Finalized n Byz f s e b0 b b2

/-- `b₃`'s parent is notarized by `e+2`: the `e+3` proposal extends a
longest chain notarized by `e+2` (`proposedSeenParent`), and the parent is
nonempty (the proposal has positive epoch). -/
theorem proposal_parent_notarized {s : St n} (hinv : Inv n Byz Δ f L s)
    {e : ℕ} {b3 : Blk} (hp3 : HonestProposal n Byz L s (e + 3) b3)
    (hb3pos : 0 < bep b3) : NotarizedBy n Byz f s b3.tail (e + 2) := by
  have hc : ChainNotarizedBy n Byz f s b3.tail (e + 2) :=
    hinv.proposedSeenParent (e + 3) b3 hp3.mem hp3.honest
  exact chain_notarized_block n Byz f hc
    (ne_nil_tail_of_bep_pos (hinv.propValid (e + 3) b3 hp3.mem hp3.honest) hb3pos)

/-- **Adjacency**: four honest proposals at `e…e+3` with strictly growing
lengths and the last two chain-notarized — the `e+3` proposal extends the
`e+2` proposal: `b₃ = (e+3) :: b₂`. Its tail has the same length as `b₂` by
`longest_chain_by`/`propLongest`, and `main_liveness_lemma` rules out any
*different* same-length notarized block. -/
theorem next_proposal_extends (hB : Byz.card ≤ f) {s : St n} (hinv : Inv n Byz Δ f L s)
    {e : ℕ} {b0 b1 b2 b3 : Blk}
    (hp0 : HonestProposal n Byz L s e b0)
    (hp1 : HonestProposal n Byz L s (e + 1) b1)
    (hp2 : HonestProposal n Byz L s (e + 2) b2)
    (hp3 : HonestProposal n Byz L s (e + 3) b3)
    (hG01 : b0.length < b1.length) (hG12 : b1.length < b2.length)
    (hG23 : b2.length < b3.length)
    (hC2 : ChainNotarizedBy n Byz f s b2 (e + 2)) (hC3 : ChainNotarizedBy n Byz f s b3 (e + 3)) :
    b3 = (e + 3) :: b2 := by
  have hb2n : b2 ≠ [] := ne_nil_of_valid (hinv.propValid (e + 2) b2 hp2.mem hp2.honest)
  have hb3n : b3 ≠ [] := ne_nil_of_valid (hinv.propValid (e + 3) b3 hp3.mem hp3.honest)
  have hb2pos : 0 < bep b2 := by
    have h : bep b2 = e + 2 := hinv.proposedEpoch (e + 2) b2 hp2.mem hp2.honest
    omega
  have hb3pos : 0 < bep b3 := by
    have h : bep b3 = e + 3 := hinv.proposedEpoch (e + 3) b3 hp3.mem hp3.honest
    omega
  have hb2ge2 : 2 ≤ b2.length :=
    length_ge_two_of_bep_pos (hinv.propValid (e + 2) b2 hp2.mem hp2.honest) hb2pos
  -- `b₃`'s parent has the same length as `b₂`, hence is `b₂` itself
  have hb3pred : b3.tail = b2 := by
    have hlen : b3.tail.length = b2.length := by
      apply le_antisymm
      · by_cases hg : b3.tail = [0]
        · rw [hg]
          change 1 ≤ b2.length
          exact le_trans (by omega : 1 ≤ 2) hb2ge2
        · exact longest_chain_by n Byz Δ f L hB hinv hp0 hp1 hp2 hG01 hG12 b3.tail
            (proposal_parent_notarized n Byz Δ f L hinv hp3 hb3pos)
      · have hN : NotarizedBy n Byz f s b2 (e + 2) := chain_notarized_block n Byz f hC2 hb2n
        exact hinv.propLongest (e + 3) b3 hp3.mem hp3.honest b2 hN
    by_contra hne
    by_cases hg : b3.tail = [0]
    · have hb3taillen : b3.tail.length = 1 := by rw [hg]; rfl
      omega
    · have hN3' : NotarizedCast n Byz f s b3.tail :=
        (proposal_parent_notarized n Byz Δ f L hinv hp3 hb3pos).1
      exact (main_liveness_lemma n Byz Δ f L hB hinv hp0 hp1 hp2 hG01 hG12 hC2
        b3.tail hne hlen hN3')
  have hb3eq : b3 = bep b3 :: b3.tail := by
    cases b3 with
    | nil => exact (hb3n rfl).elim
    | cons a t => rfl
  have hb3E : bep b3 = e + 3 := hinv.proposedEpoch (e + 3) b3 hp3.mem hp3.honest
  rw [hb3pred, hb3E] at hb3eq
  exact hb3eq

/-- **Theorem 6 (liveness core)**: five consecutive honest-leader proposals
with strictly growing lengths, each chain-notarized on time — `b₃` (the
proposal of epoch `e+3`) is final. -/
theorem liveness_finality (hB : Byz.card ≤ f) {s : St n} (hinv : Inv n Byz Δ f L s)
    {e : ℕ} {b0 b1 b2 b3 b4 : Blk}
    (hp0 : HonestProposal n Byz L s e b0)
    (hp1 : HonestProposal n Byz L s (e + 1) b1)
    (hp2 : HonestProposal n Byz L s (e + 2) b2)
    (hp3 : HonestProposal n Byz L s (e + 3) b3)
    (hp4 : HonestProposal n Byz L s (e + 4) b4)
    (hG01 : b0.length < b1.length) (hG12 : b1.length < b2.length)
    (hG23 : b2.length < b3.length) (hG34 : b3.length < b4.length)
    (hC2 : ChainNotarizedBy n Byz f s b2 (e + 2)) (hC3 : ChainNotarizedBy n Byz f s b3 (e + 3))
    (hC4 : ChainNotarizedBy n Byz f s b4 (e + 4)) :
    Finalized n Byz f s (e + 2) b2 b3 b4 := by
  have hAdj23 : b3 = (e + 3) :: b2 :=
    next_proposal_extends n Byz Δ f L hB hinv hp0 hp1 hp2 hp3 hG01 hG12 hG23 hC2 hC3
  have hAdj34 : b4 = (e + 4) :: b3 :=
    next_proposal_extends n Byz Δ f L hB hinv hp1 hp2 hp3 hp4 hG12 hG23 hG34 hC3 hC4
  refine ⟨Nat.succ_pos (e + 1),
    hinv.proposedEpoch (e + 2) b2 hp2.mem hp2.honest,
    ?_, ?_⟩
  · -- `Consecutive b2 b3 b4`: tail equalities from the two adjacency
    -- lemmas, epoch equalities from `proposedEpoch`
    constructor
    · rw [hAdj34]; rfl
    · constructor
      · rw [hAdj23]; rfl
      · constructor
        · have hbep2 : bep b2 = e + 2 := hinv.proposedEpoch (e + 2) b2 hp2.mem hp2.honest
          have hbep3 : bep b3 = e + 3 := hinv.proposedEpoch (e + 3) b3 hp3.mem hp3.honest
          omega
        · have hbep3 : bep b3 = e + 3 := hinv.proposedEpoch (e + 3) b3 hp3.mem hp3.honest
          have hbep4 : bep b4 = e + 4 := hinv.proposedEpoch (e + 4) b4 hp4.mem hp4.honest
          omega
  · intro d hd hdsuf
    exact (hC4 d hd hdsuf).1

end Bft.Examples.StreamletLiveness
