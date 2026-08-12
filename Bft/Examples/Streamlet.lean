/-
Copyright (c) 2026 lean-tla contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Case study: Streamlet consistency (Chan & Shi, 2020)

The safety core of Streamlet ("Textbook Streamlined Blockchains"):
`f < n/3` Byzantine, notarization at `2f+1` votes out of `3f+1`, and the
"magic" finalization rule — three adjacent blocks with consecutive epoch
numbers in a notarized chain finalize the middle one's prefix.

Modeling choices, all in service of the paper's own remarks:

* **A block *is* its chain** (`Blk := List ℕ`, tip at the head, genesis
  `0` at the end). The paper's Remark 1 — "the hash-chained data
  structure guarantees that given a block, its prefix is uniquely
  determined" — made literal: ideal hashes mean a block can be
  identified with its prefix chain. Ancestry is `List.IsSuffix`,
  extension is `List.tail`, "same length" is `List.length`.
* **Message soup**: the state is a global epoch clock plus the list of
  votes cast, as in Minimmit. Honest votes are guarded (own epoch, first
  vote per epoch, parent notarized, parent longest seen); Byzantine
  votes are arbitrary (well-formed chains only — the ideal-hash
  assumption). There is no proposal action: leaders matter for
  liveness, not for consistency.
* **Safety proof**: the paper's Lemma 1 (unique notarization per epoch)
  plus one uniform length-monotonicity invariant (I5 below) replace the
  paper's two-case argument — the same inequality
  `parent(x).length ≤ parent(y).length` for any two honest votes
  `x` (earlier epoch) and `y` kills both Case 1 and Case 2.

Scope limit (documented, not hidden): consistency only. Liveness needs
a partial-synchrony model (epochs of `2Δ` and message delivery bounds),
which this global-clock model does not attempt.
-/
import Bft.Examples.Minimmit
import Bft.Tactic

namespace Bft.Examples.Streamlet

open Bft

/-- A block, identified with its prefix chain: tip epoch at the head,
genesis epoch `0` at the end. E.g. `[7, 6, 5, 2, 0]` is the block at
epoch 7 whose parent chain is `[6, 5, 2, 0]`. -/
abbrev Blk := List ℕ

/-- A well-formed chain: strictly decreasing epochs anchored at genesis. -/
def ValidChain (c : Blk) : Prop := 0 ∈ c ∧ c.Chain' (· > ·)

/-- The block's own epoch (0 for the empty chain, which never votes). -/
def bep (b : Blk) : ℕ := b.head?.getD 0

variable (n f : ℕ) (Byz : Finset (Fin n))

/-- Global state: epoch clock and the votes cast so far. -/
structure St (n : ℕ) where
  ep : ℕ
  msgs : List (Fin n × Blk)

/-- The distinct voters of a block. -/
def voters (s : St n) (b : Blk) : Finset (Fin n) :=
  (s.msgs.toFinset.filter fun p => p.2 = b).image Prod.fst

/-- Notarization threshold: `2f+1` out of (at most) `3f+1`. -/
def quorum (f : ℕ) : ℕ := 2 * f + 1

/-- A block is notarized with `2f+1` distinct votes; genesis is
notarized by fiat. -/
def Notarized (f : ℕ) (s : St n) (b : Blk) : Prop :=
  b = [0] ∨ quorum f ≤ (voters n s b).card

/-- A chain is notarized if every block in it (every nonempty suffix)
is notarized. -/
def NotarizedChain (f : ℕ) (s : St n) (c : Blk) : Prop :=
  ∀ d : Blk, d ≠ [] → d <:+ c → Notarized n f s d

/-! ## Actions -/

/-- Time passes. -/
def Tick : Action (St n) := fun s s' =>
  s'.ep = s.ep + 1 ∧ s'.msgs = s.msgs

/-- An honest vote: in the block's own epoch, the node's first vote this
epoch, on a block whose parent chain is notarized and is (one of) the
longest notarized chain(s) seen. -/
def VoteH (i : Fin n) (b : Blk) : Action (St n) := fun s s' =>
  i ∉ Byz ∧
  ValidChain b ∧ bep b = s.ep ∧
  (∀ b', (i, b') ∈ s.msgs → bep b' ≠ s.ep) ∧
  NotarizedChain n f s b.tail ∧
  (∀ c : Blk, NotarizedChain n f s c → c.length ≤ b.tail.length) ∧
  s'.msgs = (i, b) :: s.msgs ∧ s'.ep = s.ep

/-- A Byzantine vote: any well-formed chain, any time. -/
def VoteB (i : Fin n) (b : Blk) : Action (St n) := fun s s' =>
  i ∈ Byz ∧ ValidChain b ∧ s'.msgs = (i, b) :: s.msgs ∧ s'.ep = s.ep

/-- The step relation. -/
def Next : Action (St n) := fun s s' =>
  Tick n s s' ∨ (∃ i b, VoteH n f Byz i b s s') ∨ (∃ i b, VoteB n Byz i b s s')

/-- Frame: the whole state. -/
def vars (n : ℕ) : St n → St n := id

/-- Initially: epoch 0, no votes. -/
def Init (n : ℕ) : StatePred (St n) := { s | s.ep = 0 ∧ s.msgs = [] }

/-- The specification. -/
def Hspec : Pred (St n) := tlaAnd (statePred (Init n)) (stutAlways (Next n f Byz) (vars n))

/-! ## Monotonicity of notarization -/

theorem voters_mono {s t : St n} (h : ∀ p, p ∈ s.msgs → p ∈ t.msgs) (b : Blk) :
    voters n s b ⊆ voters n t b := by
  intro i hi
  rw [voters, Finset.mem_image] at hi ⊢
  obtain ⟨p, hp, hpi⟩ := hi
  rw [Finset.mem_filter, List.mem_toFinset] at hp
  exact ⟨p, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (h p hp.1), hp.2⟩, hpi⟩

theorem Notarized.mono {s t : St n} (h : ∀ p, p ∈ s.msgs → p ∈ t.msgs) (b : Blk) :
    Notarized n f s b → Notarized n f t b := by
  rintro (hb | hq)
  · exact Or.inl hb
  · exact Or.inr (le_trans hq (Finset.card_le_card (voters_mono n h b)))

theorem NotarizedChain.mono {s t : St n} (h : ∀ p, p ∈ s.msgs → p ∈ t.msgs)
    (c : Blk) : NotarizedChain n f s c → NotarizedChain n f t c :=
  fun hnc d hd hs => (hnc d hd hs).mono n f h d

/-! ## The invariant bundle

* IV: every vote cast is on a well-formed chain (ideal hashes);
* I0: honest votes happen in their own epoch, hence at most the clock;
* I1 (HonestUniq): an honest node votes at most once per epoch;
* I2: an honest vote's parent chain was notarized at vote time — and
  stays notarized (monotonicity);
* I5: an honest node's later votes extend longer parents: for any two
  honest votes `x`, `y` of the same node, `bep x < bep y` implies
  `x.tail.length ≤ y.tail.length`. This single inequality is the whole
  content of the paper's Case 1 / Case 2 argument. -/

/-- The inductive invariant. -/
def Inv := { s |
  (∀ i b, (i, b) ∈ s.msgs → ValidChain b) ∧
  (∀ i b, i ∉ Byz → (i, b) ∈ s.msgs → bep b ≤ s.ep) ∧
  (∀ i b₁ b₂, i ∉ Byz → (i, b₁) ∈ s.msgs → (i, b₂) ∈ s.msgs →
    bep b₁ = bep b₂ → b₁ = b₂) ∧
  (∀ i b, i ∉ Byz → (i, b) ∈ s.msgs → NotarizedChain n f s b.tail) ∧
  (∀ i b₁ b₂, i ∉ Byz → (i, b₁) ∈ s.msgs → (i, b₂) ∈ s.msgs →
    bep b₁ < bep b₂ → b₁.tail.length ≤ b₂.tail.length) }

theorem init_inv : ∀ s, s ∈ Init n → s ∈ Inv n f Byz := by
  intro s hs
  obtain ⟨h0, h1⟩ := hs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [h1]

theorem step_inv : ∀ s s', StutAction (Next n f Byz) (vars n) s s' → s ∈ Inv n f Byz → s' ∈ Inv n f Byz := by
  intro s s' hstep hinv
  rcases hstep with hnext | hstut
  swap
  · change s' = s at hstut
    rwa [hstut]
  obtain ⟨hv, h0, h1, h2, h5⟩ := hinv
  rcases hnext with ⟨hep, hmsgs⟩ | ⟨i, b, hvote⟩ | ⟨i, b, hvote⟩
  · -- Tick: clock advances, votes unchanged
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [hmsgs]
    · exact hv
    · intro i b hi hb; rw [hep]; exact le_trans (h0 i b hi hb) (by omega)
    · exact h1
    · intro i b hi hb
      exact (h2 i b hi (hmsgs ▸ hb)).mono n f (fun p hp => hmsgs ▸ hp) b.tail
    · exact h5
  · -- Honest vote
    obtain ⟨hi, hval, hep, hfirst, hpar, hlong, hmsgs, hep2⟩ := hvote
    have hmono : ∀ p, p ∈ s.msgs → p ∈ s'.msgs := by
      intro p hp; rw [hmsgs]; exact List.mem_cons_of_mem _ hp
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro j b' hj
      rw [hmsgs] at hj
      rcases List.mem_cons.mp hj with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact hval
      · exact hv j b' h
    · intro j b' hj hb'
      rw [hmsgs] at hb'
      rcases List.mem_cons.mp hb' with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        rw [hep2]; exact le_of_eq hep
      · exact le_trans (h0 j b' hj h) (by omega)
    · intro j b₁ b₂ hj hb₁ hb₂ heq
      rw [hmsgs] at hb₁ hb₂
      rcases List.mem_cons.mp hb₁ with h₁ | h₁ <;>
        rcases List.mem_cons.mp hb₂ with h₂ | h₂
      · obtain ⟨_, rfl⟩ := Prod.mk.inj h₁
        obtain ⟨_, rfl⟩ := Prod.mk.inj h₂; rfl
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₁
        exact absurd (heq.symm.trans hep) (hfirst b₂ h₂)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₂
        exact absurd (heq.trans hep) (hfirst b₁ h₁)
      · exact h1 j b₁ b₂ hj h₁ h₂ heq
    · intro j b' hj hb'
      rw [hmsgs] at hb'
      rcases List.mem_cons.mp hb' with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact hpar.mono n f hmono b'.tail
      · exact (h2 j b' hj h).mono n f hmono b'.tail
    · intro j b₁ b₂ hj hb₁ hb₂ hlt
      rw [hmsgs] at hb₁ hb₂
      rcases List.mem_cons.mp hb₂ with h₂ | h₂
      · -- b₂ is the new vote: b₁'s parent was notarized-longest at s
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₂
        rcases List.mem_cons.mp hb₁ with h₁ | h₁
        · obtain ⟨-, rfl⟩ := Prod.mk.inj h₁
          exact absurd hlt (lt_irrefl _)
        · exact hlong b₁.tail (h2 j b₁ hj h₁)
      · rcases List.mem_cons.mp hb₁ with h₁ | h₁
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₁
          have hle : bep b₂ ≤ s.ep := h0 j b₂ hj h₂
          exact absurd hlt (by omega)
        · exact h5 j b₁ b₂ hj h₁ h₂ hlt
  · -- Byzantine vote: honest-node facts untouched, notarization monotone
    obtain ⟨hi, hval, hmsgs, hep⟩ := hvote
    have hmono : ∀ p, p ∈ s.msgs → p ∈ s'.msgs := by
      intro p hp; rw [hmsgs]; exact List.mem_cons_of_mem _ hp
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro j b' hj
      rw [hmsgs] at hj
      rcases List.mem_cons.mp hj with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact hval
      · exact hv j b' h
    · intro j b' hj hb'
      rw [hmsgs] at hb'
      rcases List.mem_cons.mp hb' with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact (hj hi).elim
      · rw [hep]; exact h0 j b' hj h
    · intro j b₁ b₂ hj hb₁ hb₂ heq
      rw [hmsgs] at hb₁ hb₂
      rcases List.mem_cons.mp hb₁ with h₁ | h₁ <;>
        rcases List.mem_cons.mp hb₂ with h₂ | h₂
      · obtain ⟨_, rfl⟩ := Prod.mk.inj h₁
        obtain ⟨_, rfl⟩ := Prod.mk.inj h₂; rfl
      · obtain ⟨hji, -⟩ := Prod.mk.inj h₁
        exact absurd hi (hji ▸ hj)
      · obtain ⟨hji, -⟩ := Prod.mk.inj h₂
        exact absurd hi (hji ▸ hj)
      · exact h1 j b₁ b₂ hj h₁ h₂ heq
    · intro j b' hj hb'
      rw [hmsgs] at hb'
      rcases List.mem_cons.mp hb' with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact (hj hi).elim
      · exact (h2 j b' hj h).mono n f hmono b'.tail
    · intro j b₁ b₂ hj hb₁ hb₂ hlt
      rw [hmsgs] at hb₁ hb₂
      rcases List.mem_cons.mp hb₁ with h₁ | h₁ <;>
        rcases List.mem_cons.mp hb₂ with h₂ | h₂
      · obtain ⟨hji, -⟩ := Prod.mk.inj h₁
        exact absurd hi (hji ▸ hj)
      · obtain ⟨hji, -⟩ := Prod.mk.inj h₁
        exact absurd hi (hji ▸ hj)
      · obtain ⟨hji, -⟩ := Prod.mk.inj h₂
        exact absurd hi (hji ▸ hj)
      · exact h5 j b₁ b₂ hj h₁ h₂ hlt

theorem safety : Entails (Hspec n f Byz) (always (statePred (Inv n f Byz))) :=
  init_invariant_stut (Init n) (Next n f Byz) (vars n) (Inv n f Byz) (init_inv n f Byz) (step_inv n f Byz)


/-! ## Lemma 1: at most one notarized block per epoch -/

/-- Membership in a block's voter set is just having cast that vote. -/
theorem mem_voters {s : St n} {i : Fin n} {b : Blk} :
    i ∈ voters n s b ↔ (i, b) ∈ s.msgs := by
  simp only [voters, Finset.mem_image, Finset.mem_filter, List.mem_toFinset]
  constructor
  · rintro ⟨x, ⟨hm, hxb⟩, hxi⟩
    cases hxi; cases hxb; exact hm
  · intro hm
    exact ⟨(i, b), ⟨hm, rfl⟩, rfl⟩

/-- A valid chain whose epoch is 0 can only be genesis. -/
theorem ValidChain.eq_genesis {c : Blk} (hv : ValidChain c) (he : bep c = 0) : c = [0] := by
  obtain ⟨h0, hchain⟩ := hv
  cases c with
  | nil => simp at h0
  | cons a t =>
    have ha : a = 0 := by simpa [bep] using he
    cases t with
    | nil => rw [ha]
    | cons b u =>
      cases hchain with
      | cons_cons hab _ =>
        rw [ha] at hab
        exact absurd hab (Nat.not_lt_zero b)

/-- A block with positive epoch is nonempty. -/
theorem ne_of_bep_pos {c : Blk} (h : 0 < bep c) : c ≠ [] := by
  intro hc; rw [hc] at h; simp [bep] at h

/-- Genesis sits in the tail of any chain with positive epoch that
contains it. -/
theorem mem_tail_of_bep_pos {c : Blk} (h0 : 0 ∈ c) (hb : 0 < bep c) : 0 ∈ c.tail := by
  cases c with
  | nil => simp [bep] at hb
  | cons a t =>
    rw [List.mem_cons] at h0
    rcases h0 with rfl | h0
    · simp [bep] at hb
    · exact h0

/-- The paper's Lemma 1: per epoch, at most one block is notarized.
Quorum intersection yields an honest node in both voter sets; I1
(honest nodes vote at most once per epoch) finishes. -/
theorem unique_notarized (hn : n = 3 * f + 1) (hB : Byz.card ≤ f)
    {s : St n} (hs : s ∈ Inv n f Byz) {b₁ b₂ : Blk}
    (hn1 : Notarized n f s b₁) (hn2 : Notarized n f s b₂) (he : bep b₁ = bep b₂) :
    b₁ = b₂ := by
  obtain ⟨hv, -, h1, -, -⟩ := hs
  have hqnum : quorum f = 2 * f + 1 := rfl
  have valid_of_quorum : ∀ {b : Blk}, quorum f ≤ (voters n s b).card → ValidChain b := by
    intro b hq
    rw [hqnum] at hq
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < (voters n s b).card)
    rw [mem_voters] at hi
    exact hv i b hi
  rcases hn1 with hg1 | hq1
  · subst hg1
    rcases hn2 with hg2 | hq2
    · exact hg2.symm
    · exact (ValidChain.eq_genesis (valid_of_quorum hq2) he.symm).symm
  · rcases hn2 with hg2 | hq2
    · subst hg2
      exact ValidChain.eq_genesis (valid_of_quorum hq1) he
    · obtain ⟨i, hi1, hi2, hih⟩ := Minimmit.exists_honest_inter n f Byz hB (quorum f) (quorum f)
        hq1 hq2 (by rw [hqnum]; omega)
      rw [mem_voters] at hi1 hi2
      exact h1 i b₁ b₂ hih hi1 hi2 he

/-! ## Consistency -/

/-- The paper's consistency theorem at an invariant state: if a notarized
chain ends in three blocks with consecutive epochs, no other block of the
middle one's length can be notarized.

The paper's two-case epoch analysis collapses to one move per case:
quorum intersection puts an honest node in the two voter sets, and I5
(its later votes have longer parents) yields the impossible length
inequality; the three middle epochs fall to `unique_notarized`. -/
theorem consistency_of_inv (hn : n = 3 * f + 1) (hB : Byz.card ≤ f)
    {s : St n} (hs : s ∈ Inv n f Byz)
    {B7 B6 B5 X : Blk} (hB7 : NotarizedChain n f s B7)
    (h76 : B7.tail = B6) (h65 : B6.tail = B5)
    (he65 : bep B6 = bep B5 + 1) (he76 : bep B7 = bep B6 + 1)
    (hXne : X ≠ B6) (hXlen : X.length = B6.length) :
    ¬ Notarized n f s X := by
  have hinv := hs
  obtain ⟨hv, -, -, -, h5⟩ := hinv
  have hqnum : quorum f = 2 * f + 1 := rfl
  intro hnotX
  -- The three blocks are nonempty, notarized (suffixes of B7), and B7 is
  -- genuinely voted, hence valid; so genesis lies in all of them.
  have bepB6pos : 0 < bep B6 := by omega
  have bepB7pos : 0 < bep B7 := by omega
  have neB6 : B6 ≠ [] := ne_of_bep_pos bepB6pos
  have neB7 : B7 ≠ [] := ne_of_bep_pos bepB7pos
  have nB7 : Notarized n f s B7 := hB7 B7 neB7 (List.suffix_refl B7)
  have nB6 : Notarized n f s B6 := hB7 B6 neB6 (h76 ▸ List.tail_suffix B7)
  have B7ne0 : B7 ≠ [0] := by
    intro hc; rw [hc] at he76; simp [bep] at he76
  have qB7 : quorum f ≤ (voters n s B7).card := nB7.resolve_left B7ne0
  have h0B7 : 0 ∈ B7 := by
    have hq := qB7
    rw [hqnum] at hq
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < (voters n s B7).card)
    rw [mem_voters] at hi
    exact (hv i B7 hi).1
  have h0B6 : 0 ∈ B6 := h76 ▸ mem_tail_of_bep_pos h0B7 bepB7pos
  have h0B5 : 0 ∈ B5 := h65 ▸ mem_tail_of_bep_pos h0B6 bepB6pos
  have neB5 : B5 ≠ [] := by intro hc; rw [hc] at h0B5; simp at h0B5
  have hB5suf : B5 <:+ B7 :=
    (h65 ▸ List.tail_suffix B6).trans (h76 ▸ List.tail_suffix B7)
  have nB5 : Notarized n f s B5 := hB7 B5 neB5 hB5suf
  -- Length arithmetic.
  have lenB7 : 0 < B7.length := List.length_pos_of_mem h0B7
  have lenB6 : 0 < B6.length := List.length_pos_of_mem h0B6
  have len76 : B7.length = B6.length + 1 := by
    have h := congrArg List.length h76
    rw [List.length_tail] at h; omega
  have len65 : B6.length = B5.length + 1 := by
    have h := congrArg List.length h65
    rw [List.length_tail] at h; omega
  have lenB5 : 0 < B5.length := List.length_pos_of_mem h0B5
  -- X is long, hence not genesis, hence genuinely voted.
  have Xne0 : X ≠ [0] := by
    intro hc; rw [hc] at hXlen; simp at hXlen; omega
  have qX : quorum f ≤ (voters n s X).card := hnotX.resolve_left Xne0
  -- Shared honest voter of two genuinely voted blocks.
  have inter : ∀ {u v : Blk}, quorum f ≤ (voters n s u).card →
      quorum f ≤ (voters n s v).card →
      ∃ i, i ∉ Byz ∧ (i, u) ∈ s.msgs ∧ (i, v) ∈ s.msgs := by
    intro u v hu hv'
    obtain ⟨i, hi1, hi2, hih⟩ := Minimmit.exists_honest_inter n f Byz hB (quorum f) (quorum f)
      hu hv' (by rw [hqnum]; omega)
    rw [mem_voters] at hi1 hi2
    exact ⟨i, hih, hi1, hi2⟩
  -- Five-way epoch analysis.
  rcases lt_trichotomy (bep X) (bep B6) with hlt | heq | hgt
  · rcases lt_trichotomy (bep X) (bep B5) with hlt2 | heq2 | hgt2
    · -- epoch X < epoch B5: honest i voted X (earlier) and B5
      have B5ne0 : B5 ≠ [0] := by
        intro hc; rw [hc] at hlt2; simp [bep] at hlt2
      obtain ⟨i, hih, hiX, hiB5⟩ := inter qX (nB5.resolve_left B5ne0)
      have hle := h5 i X B5 hih hiX hiB5 hlt2
      rw [List.length_tail, List.length_tail] at hle
      omega
    · -- epoch X = epoch B5: Lemma 1 forces X = B5, too short
      have hXB5 : X = B5 := unique_notarized n f Byz hn hB hs hnotX nB5 heq2
      rw [hXB5] at hXlen
      omega
    · omega
  · -- epoch X = epoch B6: Lemma 1 forces X = B6
    exact hXne (unique_notarized n f Byz hn hB hs hnotX nB6 heq)
  · rcases lt_trichotomy (bep X) (bep B7) with hlt2 | heq2 | hgt2
    · omega
    · -- epoch X = epoch B7: Lemma 1 forces X = B7, too long
      have hXB7 : X = B7 := unique_notarized n f Byz hn hB hs hnotX nB7 heq2
      rw [hXB7, len76] at hXlen
      omega
    · -- epoch X > epoch B7: honest i voted B7 (earlier) and X
      obtain ⟨i, hih, hiX, hiB7⟩ := inter qX qB7
      have hle := h5 i B7 X hih hiB7 hiX hgt2
      rw [List.length_tail, List.length_tail] at hle
      omega

/-- Consistency packaged over executions: at every reachable state, no
block conflicting with the finalized middle block can be notarized. -/
theorem consistency (hn : n = 3 * f + 1) (hB : Byz.card ≤ f)
    (e : Behavior (St n)) (hE : Hspec n f Byz e) (k : ℕ)
    {B7 B6 B5 X : Blk} (hB7 : NotarizedChain n f (e k) B7)
    (h76 : B7.tail = B6) (h65 : B6.tail = B5)
    (he65 : bep B6 = bep B5 + 1) (he76 : bep B7 = bep B6 + 1)
    (hXne : X ≠ B6) (hXlen : X.length = B6.length) :
    ¬ Notarized n f (e k) X :=
  consistency_of_inv n f Byz hn hB (always_statePred_at (k := k) (safety n f Byz e hE))
    hB7 h76 h65 he65 he76 hXne hXlen

end Bft.Examples.Streamlet
