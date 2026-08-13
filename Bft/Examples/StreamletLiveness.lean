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
temporal wrapper (per-epoch leads-to progress, composed to Theorem 4) is a
follow-up. The two key ingredients beyond the safety facts:

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
open Bft.Examples.Streamlet (Blk ValidChain bep quorum mem_tail_of_bep_pos)
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

/-- A block of length at least two has a nonempty tail. -/
theorem tail_ne_nil_of_length_ge_two {b : Blk} (h : 2 ≤ b.length) : b.tail ≠ [] := by
  intro ht
  have hbne : b ≠ [] := by
    intro hb
    rw [hb] at h
    rw [List.length_nil] at h
    omega
  have hlen : b.length = b.tail.length + 1 := length_tail_succ hbne
  rw [ht] at hlen
  rw [List.length_nil] at hlen
  omega

/-- A quorum is nonempty. -/
theorem quorum_nonempty {Q : Finset (Fin n)} (h : quorum f ≤ Q.card) : ∃ i, i ∈ Q := by
  have hpos : 0 < Q.card := by unfold quorum at h; omega
  exact Finset.card_pos.mp hpos

/-- `NotarizedBy` is monotone in the epoch bound. -/
theorem notarizedBy_mono {s : St n} {b : Blk} {e e' : ℕ} (h : e ≤ e') :
    NotarizedBy n f s b e → NotarizedBy n f s b e' := by
  rintro ⟨hN, hbep⟩
  exact ⟨hN, le_trans hbep h⟩

/-- A chain-notarized nonempty block is itself notarized. -/
theorem chain_notarized_block {s : St n} {b : Blk} {e : ℕ}
    (hc : ChainNotarizedBy n f s b e) (hne : b ≠ []) : NotarizedBy n f s b e :=
  hc b hne (List.suffix_refl b)

/-- A proposal of a positive epoch is not the genesis block. -/
theorem proposal_ne_genesis_of {s : St n} (hinv : Inv n Byz Δ f L s) {e : ℕ} {b : Blk}
    (hp : propCast n L s e b) (hL : L e ∉ Byz) (hpos : 0 < e) : b ≠ [0] := by
  intro hb; subst b
  have he : bep [0] = e := hinv.proposedEpoch e [0] ((hinv.castProps_iff e [0]).2 hp) hL
  simp [bep] at he
  omega

/-- A proposal of epoch `e+1` is not the genesis block. -/
theorem proposal_succ_ne_genesis {s : St n} (hinv : Inv n Byz Δ f L s) {e : ℕ} {b : Blk}
    (hp : propCast n L s (e + 1) b) (hL : L (e + 1) ∉ Byz) : b ≠ [0] :=
  proposal_ne_genesis_of n Byz Δ f L hinv hp hL (Nat.succ_pos e)

/-! ## Lemma 5: the longest-chain bound and the main liveness lemma -/

/-- **The longest-chain bound**: a block notarized by `e+2` is no longer
than the honest `b₂`. -/
theorem longest_chain_by (hB : Byz.card ≤ f) {s : St n} (hinv : Inv n Byz Δ f L s)
    {e : ℕ} {b0 b1 b2 : Blk}
    (hp0 : propCast n L s e b0) (hp1 : propCast n L s (e + 1) b1)
    (hp2 : propCast n L s (e + 2) b2)
    (hL0 : L e ∉ Byz) (hL1 : L (e + 1) ∉ Byz) (hL2 : L (e + 2) ∉ Byz)
    (hG01 : b0.length < b1.length) (hG12 : b1.length < b2.length)
    (_hC2 : ChainNotarizedBy n f s b2 (e + 2)) :
    ∀ C : Blk, NotarizedBy n f s C (e + 2) → C.length ≤ b2.length := by
  intro C hC
  rcases hC with ⟨hN, hbepC⟩
  rcases honest_in_quorum n Byz f hB hN with ⟨i0, hi0, hih⟩
  have hv0 : (i0, C) ∈ s.castVotes := (mem_votersCast n).mp hi0
  have hCP : (bep C, C) ∈ s.castProps := hinv.votedProposed i0 C hih hv0
  have hCval : ValidChain C := hinv.voteValid i0 C hih hv0
  have hb1ne : b1 ≠ [0] := proposal_succ_ne_genesis n Byz Δ f L hinv hp1 hL1
  have hb2ne : b2 ≠ [0] := proposal_ne_genesis_of n Byz Δ f L hinv hp2 hL2 (Nat.succ_pos (e + 1))
  by_cases h1 : bep C = e
  · have hCb : (e, C) ∈ s.castProps := by simpa [h1] using hCP
    have hC0 : C = b0 := hinv.propUniq e C b0 hCb ((hinv.castProps_iff e b0).2 hp0) hL0
    subst C
    omega
  · by_cases h2 : bep C = e + 1
    · have hCb : (e + 1, C) ∈ s.castProps := by simpa [h2] using hCP
      have hC1 : C = b1 := hinv.propUniq (e + 1) C b1 hCb ((hinv.castProps_iff (e + 1) b1).2 hp1) hL1
      subst C
      omega
    · by_cases h3 : bep C = e + 2
      · have hCb : (e + 2, C) ∈ s.castProps := by simpa [h3] using hCP
        have hC2' : C = b2 := hinv.propUniq (e + 2) C b2 hCb ((hinv.castProps_iff (e + 2) b2).2 hp2) hL2
        subst C
        omega
      · have hlt : bep C < e := by
          by_cases hle : bep C ≤ e
          · exact lt_of_le_of_ne hle h1
          · have hge : e + 1 ≤ bep C := Nat.succ_le_of_lt (lt_of_not_ge hle)
            have hcase : bep C = e + 1 ∨ bep C = e + 2 := by omega
            rcases hcase with hc1 | hc2
            · exact (h2 hc1).elim
            · exact (h3 hc2).elim
        by_cases hg : C = [0]
        · subst C
          have hb2n : b2 ≠ [] := ne_nil_of_valid (hinv.propValid (e + 2) b2 ((hinv.castProps_iff (e + 2) b2).2 hp2) hL2)
          have hb2pos : 0 < b2.length := List.length_pos_of_ne_nil hb2n
          simpa using (Nat.succ_le_of_lt hb2pos)
        · have hCpos : 0 < bep C := by
            by_contra hnot
            have h0 : bep C = 0 := Nat.eq_zero_of_not_pos hnot
            exact hg (ValidChain.eq_genesis hCval h0)
          have hCn : C ≠ [] := ne_nil_of_valid hCval
          have hCn' : C.tail ≠ [] := ne_nil_tail_of_bep_pos hCval hCpos
          have hCp : ChainNotarizedBy n f s C.tail (bep C - 1) :=
            hinv.votedSeenParent i0 C hih hv0
          have hN : NotarizedBy n f s C.tail (bep C - 1) :=
            chain_notarized_block n f hCp hCn'
          have hN' : NotarizedBy n f s C.tail e :=
            notarizedBy_mono n f (Nat.le_trans (Nat.sub_le (bep C) 1) (le_of_lt hlt)) hN
          have hlenP : C.tail.length ≤ b1.tail.length :=
            hinv.propLongest (e + 1) b1 ((hinv.castProps_iff (e + 1) b1).2 hp1) hL1 C.tail hN'
          have hClen' : C.length = C.tail.length + 1 := length_tail_succ hCn
          have hb1len : b1.length = b1.tail.length + 1 :=
            length_tail_succ (ne_nil_of_valid (hinv.propValid (e + 1) b1 ((hinv.castProps_iff (e + 1) b1).2 hp1) hL1))
          have hCleq : C.length ≤ b1.length := by
            rw [hClen', hb1len]
            exact Nat.succ_le_succ hlenP
          exact le_trans hCleq (le_of_lt hG12)

/-- **Lemma 5** (main liveness lemma): three consecutive honest-leader
proposals with growing lengths and the third chain-notarized on time — no
conflicting block at `b₂`'s length is ever notarized. -/
theorem main_liveness_lemma (hB : Byz.card ≤ f) {s : St n} (hinv : Inv n Byz Δ f L s)
    {e : ℕ} {b0 b1 b2 : Blk}
    (hp0 : propCast n L s e b0) (hp1 : propCast n L s (e + 1) b1)
    (hp2 : propCast n L s (e + 2) b2)
    (hL0 : L e ∉ Byz) (hL1 : L (e + 1) ∉ Byz) (hL2 : L (e + 2) ∉ Byz)
    (hG01 : b0.length < b1.length) (hG12 : b1.length < b2.length)
    (hC2 : ChainNotarizedBy n f s b2 (e + 2)) :
    ∀ C : Blk, C ≠ b2 → C.length = b2.length → ¬ NotarizedCast n f s C := by
  intro C hCne hClen hNC
  rcases honest_in_quorum n Byz f hB hNC with ⟨i0, hi0, hih⟩
  have hv0 : (i0, C) ∈ s.castVotes := (mem_votersCast n).mp hi0
  have hCP : (bep C, C) ∈ s.castProps := hinv.votedProposed i0 C hih hv0
  have hCval : ValidChain C := hinv.voteValid i0 C hih hv0
  have hb1ne : b1 ≠ [0] := proposal_succ_ne_genesis n Byz Δ f L hinv hp1 hL1
  have hb2ne : b2 ≠ [0] := proposal_ne_genesis_of n Byz Δ f L hinv hp2 hL2 (Nat.succ_pos (e + 1))
  by_cases h1 : bep C = e
  · have hCb : (e, C) ∈ s.castProps := by simpa [h1] using hCP
    have hC0 : C = b0 := hinv.propUniq e C b0 hCb ((hinv.castProps_iff e b0).2 hp0) hL0
    subst C
    omega
  · by_cases h2 : bep C = e + 1
    · have hCb : (e + 1, C) ∈ s.castProps := by simpa [h2] using hCP
      have hC1 : C = b1 := hinv.propUniq (e + 1) C b1 hCb ((hinv.castProps_iff (e + 1) b1).2 hp1) hL1
      subst C
      omega
    · by_cases h3 : bep C = e + 2
      · have hCb : (e + 2, C) ∈ s.castProps := by simpa [h3] using hCP
        have hC2' : C = b2 := hinv.propUniq (e + 2) C b2 hCb ((hinv.castProps_iff (e + 2) b2).2 hp2) hL2
        exact (hCne hC2').elim
      · by_cases hlt : bep C < e
        · have hb2pos : 0 < bep b2 := by
            have h : bep b2 = e + 2 := hinv.proposedEpoch (e + 2) b2 ((hinv.castProps_iff (e + 2) b2).2 hp2) hL2
            omega
          have hb2ge2 : 2 ≤ b2.length :=
            length_ge_two_of_bep_pos (hinv.propValid (e + 2) b2 ((hinv.castProps_iff (e + 2) b2).2 hp2) hL2) hb2pos
          have hCge2 : 2 ≤ C.length := by rw [hClen]; exact hb2ge2
          have hCpos : 0 < bep C := by
            by_contra hnot
            have h0 : bep C = 0 := Nat.eq_zero_of_not_pos hnot
            have hCg : C = [0] := ValidChain.eq_genesis hCval h0
            rw [hCg] at hCge2
            exact (Nat.not_lt_of_ge hCge2) (by decide : 1 < 2)
          have hCn : C ≠ [] := ne_nil_of_valid hCval
          have hCn' : C.tail ≠ [] := tail_ne_nil_of_length_ge_two hCge2
          have hCp : ChainNotarizedBy n f s C.tail (bep C - 1) :=
            hinv.votedSeenParent i0 C hih hv0
          have hN : NotarizedBy n f s C.tail (bep C - 1) :=
            chain_notarized_block n f hCp hCn'
          have hN' : NotarizedBy n f s C.tail e :=
            notarizedBy_mono n f (Nat.le_trans (Nat.sub_le (bep C) 1) (le_of_lt hlt)) hN
          have hlenP : C.tail.length ≤ b1.tail.length :=
            hinv.propLongest (e + 1) b1 ((hinv.castProps_iff (e + 1) b1).2 hp1) hL1 C.tail hN'
          have hClen' : C.length = C.tail.length + 1 := length_tail_succ hCn
          have hb1len : b1.length = b1.tail.length + 1 :=
            length_tail_succ (ne_nil_of_valid (hinv.propValid (e + 1) b1 ((hinv.castProps_iff (e + 1) b1).2 hp1) hL1))
          have hCleq : C.length ≤ b1.length := by
            rw [hClen', hb1len]
            exact Nat.succ_le_succ hlenP
          have hlt' : C.length < b2.length := lt_of_le_of_lt hCleq hG12
          rw [hClen] at hlt'
          exact (lt_irrefl b2.length) hlt'
        · have hgt : e + 2 < bep C := by omega
          have hlong : ∀ C' : Blk, NotarizedBy n f s C' (bep C - 1) → C'.length ≤ C.tail.length :=
            hinv.votedLongest i0 C hih hv0
          have hb2n : b2 ≠ [] := ne_nil_of_valid (hinv.propValid (e + 2) b2 ((hinv.castProps_iff (e + 2) b2).2 hp2) hL2)
          have hb2N : NotarizedBy n f s b2 (e + 2) := chain_notarized_block n f hC2 hb2n
          have hle' : e + 2 ≤ bep C - 1 := by omega
          have hb2N' : NotarizedBy n f s b2 (bep C - 1) := notarizedBy_mono n f hle' hb2N
          have hb2le : b2.length ≤ C.tail.length := hlong b2 hb2N'
          have hCn : C ≠ [] := ne_nil_of_valid hCval
          have hClen' : C.length = C.tail.length + 1 := length_tail_succ hCn
          omega

/-! ## Theorem 6: five honest leaders finalize -/

/-- A block is final when it is the middle of three adjacent notarized
blocks with consecutive epochs on a fully notarized chain. -/
def ChainNotarizedCast (s : St n) (c : Blk) : Prop :=
  ∀ d : Blk, d ≠ [] → d <:+ c → NotarizedCast n f s d

/-- A block is final: three adjacent notarized blocks with consecutive
positive epochs on a notarized chain. -/
def Finalized (s : St n) (e : ℕ) (b0 b b2 : Blk) : Prop :=
  0 < e ∧ bep b0 = e ∧ bep b = e + 1 ∧ bep b2 = e + 2 ∧
  b = (e + 1) :: b0 ∧ b2 = (e + 2) :: b ∧
  ChainNotarizedCast n f s b2

/-- Some block is final. -/
def FinalSome (s : St n) : Prop :=
  ∃ e b0 b b2, Finalized n f s e b0 b b2

/-- **Theorem 6 (liveness core)**: five consecutive honest-leader proposals
with strictly growing lengths, each chain-notarized on time — `b₃` (the
proposal of epoch `e+3`) is final. -/
theorem liveness_finality (hB : Byz.card ≤ f) {s : St n} (hinv : Inv n Byz Δ f L s)
    {e : ℕ} {b0 b1 b2 b3 b4 : Blk}
    (hp0 : propCast n L s e b0) (hp1 : propCast n L s (e + 1) b1)
    (hp2 : propCast n L s (e + 2) b2) (hp3 : propCast n L s (e + 3) b3)
    (hp4 : propCast n L s (e + 4) b4)
    (hL0 : L e ∉ Byz) (hL1 : L (e + 1) ∉ Byz) (hL2 : L (e + 2) ∉ Byz)
    (hL3 : L (e + 3) ∉ Byz) (hL4 : L (e + 4) ∉ Byz)
    (hG01 : b0.length < b1.length) (hG12 : b1.length < b2.length)
    (hG23 : b2.length < b3.length) (_hG34 : b3.length < b4.length)
    (hC2 : ChainNotarizedBy n f s b2 (e + 2)) (hC3 : ChainNotarizedBy n f s b3 (e + 3))
    (hC4 : ChainNotarizedBy n f s b4 (e + 4)) :
    Finalized n f s (e + 2) b2 b3 b4 := by
  have hb2ne : b2 ≠ [0] := proposal_ne_genesis_of n Byz Δ f L hinv hp2 hL2 (Nat.succ_pos (e + 1))
  have hb3ne : b3 ≠ [0] := proposal_ne_genesis_of n Byz Δ f L hinv hp3 hL3 (Nat.succ_pos (e + 2))
  have hb4ne : b4 ≠ [0] := proposal_ne_genesis_of n Byz Δ f L hinv hp4 hL4 (Nat.succ_pos (e + 3))
  have hb2n : b2 ≠ [] := ne_nil_of_valid (hinv.propValid (e + 2) b2 ((hinv.castProps_iff (e + 2) b2).2 hp2) hL2)
  have hb3n : b3 ≠ [] := ne_nil_of_valid (hinv.propValid (e + 3) b3 ((hinv.castProps_iff (e + 3) b3).2 hp3) hL3)
  have hb4n : b4 ≠ [] := ne_nil_of_valid (hinv.propValid (e + 4) b4 ((hinv.castProps_iff (e + 4) b4).2 hp4) hL4)
  have hb3pos : 0 < bep b3 := by
    have h : bep b3 = e + 3 := hinv.proposedEpoch (e + 3) b3 ((hinv.castProps_iff (e + 3) b3).2 hp3) hL3
    omega
  have hb4pos : 0 < bep b4 := by
    have h : bep b4 = e + 4 := hinv.proposedEpoch (e + 4) b4 ((hinv.castProps_iff (e + 4) b4).2 hp4) hL4
    omega
  -- `b₃` extends `b₂`
  have hAdj23 : b3 = (e + 3) :: b2 := by
    have hb3pred : b3.tail = b2 := by
      have hlen : b3.tail.length = b2.length := by
        apply le_antisymm
        · by_cases hg : b3.tail = [0]
          · have hb2ge2 : 2 ≤ b2.length :=
              length_ge_two_of_bep_pos (hinv.propValid (e + 2) b2 ((hinv.castProps_iff (e + 2) b2).2 hp2) hL2) (by
                have h : bep b2 = e + 2 := hinv.proposedEpoch (e + 2) b2 ((hinv.castProps_iff (e + 2) b2).2 hp2) hL2
                omega)
            rw [hg]
            change 1 ≤ b2.length
            exact le_trans (by omega : 1 ≤ 2) hb2ge2
          · have hN3 : NotarizedBy n f s b3.tail (e + 2) := by
              have hc : ChainNotarizedBy n f s b3.tail (e + 2) :=
                hinv.proposedSeenParent (e + 3) b3 ((hinv.castProps_iff (e + 3) b3).2 hp3) hL3
              exact chain_notarized_block n f hc (ne_nil_tail_of_bep_pos (hinv.propValid (e + 3) b3 ((hinv.castProps_iff (e + 3) b3).2 hp3) hL3) hb3pos)
            exact longest_chain_by n Byz Δ f L hB hinv hp0 hp1 hp2 hL0 hL1 hL2 hG01 hG12 hC2 b3.tail hN3
        · have hN : NotarizedBy n f s b2 (e + 2) := chain_notarized_block n f hC2 hb2n
          exact hinv.propLongest (e + 3) b3 ((hinv.castProps_iff (e + 3) b3).2 hp3) hL3 b2 hN
      by_contra hne
      by_cases hg : b3.tail = [0]
      · have hb3taillen : b3.tail.length = 1 := by rw [hg]; rfl
        have hb2ge2 : 2 ≤ b2.length :=
          length_ge_two_of_bep_pos (hinv.propValid (e + 2) b2 ((hinv.castProps_iff (e + 2) b2).2 hp2) hL2) (by
            have h : bep b2 = e + 2 := hinv.proposedEpoch (e + 2) b2 ((hinv.castProps_iff (e + 2) b2).2 hp2) hL2
            omega)
        omega
      · have hN3 : NotarizedBy n f s b3.tail (e + 2) := by
          have hc : ChainNotarizedBy n f s b3.tail (e + 2) :=
            hinv.proposedSeenParent (e + 3) b3 ((hinv.castProps_iff (e + 3) b3).2 hp3) hL3
          exact chain_notarized_block n f hc (ne_nil_tail_of_bep_pos (hinv.propValid (e + 3) b3 ((hinv.castProps_iff (e + 3) b3).2 hp3) hL3) hb3pos)
        have hN3' : NotarizedCast n f s b3.tail := hN3.1
        exact (main_liveness_lemma n Byz Δ f L hB hinv hp0 hp1 hp2 hL0 hL1 hL2 hG01 hG12 hC2
          b3.tail hne hlen hN3')
    have hb3eq : b3 = bep b3 :: b3.tail := by
      cases b3 with
      | nil => exact (hb3n rfl).elim
      | cons a t => rfl
    have hb3E : bep b3 = e + 3 := hinv.proposedEpoch (e + 3) b3 ((hinv.castProps_iff (e + 3) b3).2 hp3) hL3
    rw [hb3pred, hb3E] at hb3eq
    exact hb3eq
  -- `b₄` extends `b₃`
  have hAdj34 : b4 = (e + 4) :: b3 := by
    have hb4pred : b4.tail = b3 := by
      have hlen : b4.tail.length = b3.length := by
        apply le_antisymm
        · by_cases hg : b4.tail = [0]
          · have hb3ge2 : 2 ≤ b3.length :=
              length_ge_two_of_bep_pos (hinv.propValid (e + 3) b3 ((hinv.castProps_iff (e + 3) b3).2 hp3) hL3) hb3pos
            rw [hg]
            change 1 ≤ b3.length
            exact le_trans (by omega : 1 ≤ 2) hb3ge2
          · have hN4 : NotarizedBy n f s b4.tail (e + 3) := by
              have hc : ChainNotarizedBy n f s b4.tail (e + 3) :=
                hinv.proposedSeenParent (e + 4) b4 ((hinv.castProps_iff (e + 4) b4).2 hp4) hL4
              exact chain_notarized_block n f hc (ne_nil_tail_of_bep_pos (hinv.propValid (e + 4) b4 ((hinv.castProps_iff (e + 4) b4).2 hp4) hL4) hb4pos)
            exact longest_chain_by n Byz Δ f L hB hinv hp1 hp2 hp3 hL1 hL2 hL3 hG12 hG23 hC3 b4.tail hN4
        · have hN : NotarizedBy n f s b3 (e + 3) := chain_notarized_block n f hC3 hb3n
          exact hinv.propLongest (e + 4) b4 ((hinv.castProps_iff (e + 4) b4).2 hp4) hL4 b3 hN
      by_contra hne
      by_cases hg : b4.tail = [0]
      · have hb4taillen : b4.tail.length = 1 := by rw [hg]; rfl
        have hb3ge2 : 2 ≤ b3.length :=
          length_ge_two_of_bep_pos (hinv.propValid (e + 3) b3 ((hinv.castProps_iff (e + 3) b3).2 hp3) hL3) hb3pos
        omega
      · have hN4 : NotarizedBy n f s b4.tail (e + 3) := by
          have hc : ChainNotarizedBy n f s b4.tail (e + 3) :=
            hinv.proposedSeenParent (e + 4) b4 ((hinv.castProps_iff (e + 4) b4).2 hp4) hL4
          exact chain_notarized_block n f hc (ne_nil_tail_of_bep_pos (hinv.propValid (e + 4) b4 ((hinv.castProps_iff (e + 4) b4).2 hp4) hL4) hb4pos)
        have hN4' : NotarizedCast n f s b4.tail := hN4.1
        exact (main_liveness_lemma n Byz Δ f L hB hinv hp1 hp2 hp3 hL1 hL2 hL3 hG12 hG23 hC3
          b4.tail hne hlen hN4')
    have hb4eq : b4 = bep b4 :: b4.tail := by
      cases b4 with
      | nil => exact (hb4n rfl).elim
      | cons a t => rfl
    have hb4E : bep b4 = e + 4 := hinv.proposedEpoch (e + 4) b4 ((hinv.castProps_iff (e + 4) b4).2 hp4) hL4
    rw [hb4pred, hb4E] at hb4eq
    exact hb4eq
  refine ⟨Nat.succ_pos (e + 1), hinv.proposedEpoch (e + 2) b2 ((hinv.castProps_iff (e + 2) b2).2 hp2) hL2,
    hinv.proposedEpoch (e + 3) b3 ((hinv.castProps_iff (e + 3) b3).2 hp3) hL3,
    hinv.proposedEpoch (e + 4) b4 ((hinv.castProps_iff (e + 4) b4).2 hp4) hL4,
    hAdj23, hAdj34, ?_⟩
  intro d hd hdsuf
  exact (hC4 d hd hdsuf).1

end Bft.Examples.StreamletLiveness
