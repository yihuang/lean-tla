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
def ValidChain (c : Blk) : Prop := 0 ∈ c ∧ c.IsChain (· > ·)

/-- The block's own epoch (0 for the empty chain, which never votes). -/
def bep (b : Blk) : ℕ := b.head?.getD 0

variable (n f : ℕ) (Byz : Finset (Fin n))

/-- Global state: epoch clock and the votes cast so far. -/
structure St (n : ℕ) where
  ep : ℕ
  msgs : Finset (Fin n × Blk)

/-- The distinct voters of a block. -/
def voters (s : St n) (b : Blk) : Finset (Fin n) :=
  (s.msgs.filter fun p => p.2 = b).image Prod.fst

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
  s'.msgs = insert (i, b) s.msgs ∧ s'.ep = s.ep

/-- A Byzantine vote: any well-formed chain, any time. -/
def VoteB (i : Fin n) (b : Blk) : Action (St n) := fun s s' =>
  i ∈ Byz ∧ ValidChain b ∧ s'.msgs = insert (i, b) s.msgs ∧ s'.ep = s.ep

/-- The step relation. -/
def Next : Action (St n) := fun s s' =>
  Tick n s s' ∨ (∃ i b, VoteH n f Byz i b s s') ∨ (∃ i b, VoteB n Byz i b s s')

attribute [grind unfold] Tick VoteH VoteB

/-- Frame: the whole state. -/
def vars (n : ℕ) : St n → St n := id

/-- Initially: epoch 0, no votes. -/
def Init (n : ℕ) : StatePred (St n) := { s | s.ep = 0 ∧ s.msgs = ∅ }

/-- The specification, bundled (for `Spec.init_invariant`). -/
def StreamletSpec (n f : ℕ) (Byz : Finset (Fin n)) : Spec (St n) (St n) :=
  ⟨Init n, Next n f Byz, vars n⟩

/-- The specification. -/
def Hspec : Pred (St n) := (StreamletSpec n f Byz).pred

/-! ## Monotonicity of notarization -/

theorem voters_mono {s t : St n} (h : s.msgs ⊆ t.msgs) (b : Blk) :
    voters n s b ⊆ voters n t b := by
  intro i hi
  change ∀ m, m ∈ s.msgs → m ∈ t.msgs at h
  rw [voters, Finset.mem_image] at hi ⊢
  obtain ⟨p, hp, hpi⟩ := hi
  rw [Finset.mem_filter] at hp
  exact ⟨p, Finset.mem_filter.mpr ⟨h p hp.1, hp.2⟩, hpi⟩

theorem Notarized.mono {s t : St n} (h : s.msgs ⊆ t.msgs) (b : Blk) :
    Notarized n f s b → Notarized n f t b := by
  rintro (hb | hq)
  · exact Or.inl hb
  · exact Or.inr (le_trans hq (Finset.card_le_card (voters_mono n h b)))

theorem NotarizedChain.mono {s t : St n} (h : ∀ p, p ∈ s.msgs → p ∈ t.msgs)
    (c : Blk) : NotarizedChain n f s c → NotarizedChain n f t c :=
  fun hnc d hd hs => (hnc d hd hs).mono n f h d

attribute [grind =>] Notarized.mono NotarizedChain.mono

/-! ## The invariant bundle

Each paper invariant (IV, I0, I1, I2, I5) is a named field of the
structure `Inv` (as in `StreamletProto.Inv`), not an anonymous conjunct. -/

/-- The inductive invariant: one field per paper invariant.

* IV (`valid`): every vote cast is on a well-formed chain (ideal hashes);
* I0 (`bepLeEp`): honest votes happen in their own epoch, hence at most
  the clock;
* I1 (`honestUniq`): an honest node votes at most once per epoch;
* I2 (`parentNotarized`): an honest vote's parent chain was notarized at
  vote time — and stays notarized (monotonicity);
* I5 (`lengthMono`): an honest node's later votes extend longer parents:
  for any two honest votes `x`, `y` of the same node, `bep x < bep y`
  implies `x.tail.length ≤ y.tail.length`. This single inequality is the
  whole content of the paper's Case 1 / Case 2 argument. -/
structure Inv (s : St n) : Prop where
  /-- IV: every vote cast is on a well-formed chain (ideal hashes). -/
  valid : ∀ i b, (i, b) ∈ s.msgs → ValidChain b
  /-- I0: honest votes happen in their own epoch, hence at most the clock. -/
  bepLeEp : ∀ i b, i ∉ Byz → (i, b) ∈ s.msgs → bep b ≤ s.ep
  /-- I1 (HonestUniq): an honest node votes at most once per epoch. -/
  honestUniq : ∀ i b₁ b₂, i ∉ Byz → (i, b₁) ∈ s.msgs → (i, b₂) ∈ s.msgs →
    bep b₁ = bep b₂ → b₁ = b₂
  /-- I2: an honest vote's parent chain was notarized at vote time — and
  stays notarized (monotonicity). -/
  parentNotarized : ∀ i b, i ∉ Byz → (i, b) ∈ s.msgs → NotarizedChain n f s b.tail
  /-- I5: an honest node's later votes extend longer parents: for any two
  honest votes `x`, `y` of the same node, `bep x < bep y` implies
  `x.tail.length ≤ y.tail.length`. This single inequality is the whole
  content of the paper's Case 1 / Case 2 argument. -/
  lengthMono : ∀ i b₁ b₂, i ∉ Byz → (i, b₁) ∈ s.msgs → (i, b₂) ∈ s.msgs →
    bep b₁ < bep b₂ → b₁.tail.length ≤ b₂.tail.length

/-- `Inv` as a state predicate, for the TLA induction. -/
def InvState : StatePred (St n) := { s | Inv n f Byz s }

theorem init_inv : ∀ s, s ∈ Init n → s ∈ InvState n f Byz := by
  intro s hs
  obtain ⟨h0, h1⟩ := hs
  constructor <;> simp [h1]

theorem step_inv : ∀ s s', StutAction (Next n f Byz) (vars n) s s' → s ∈ InvState n f Byz → s' ∈ InvState n f Byz := by
  intro s s' hstep hinv
  rcases hstep with hnext | hstut
  swap
  · change s' = s at hstut
    rwa [hstut]
  rcases hinv with ⟨hvalid, hbep, huniq, hparent, hlen⟩
  rcases hnext with htick | ⟨i, b, hvote⟩ | ⟨i, b, hvote⟩ <;> constructor <;> grind

theorem safety : Entails (Hspec n f Byz) (always (statePred (InvState n f Byz))) :=
  (StreamletSpec n f Byz).init_invariant (InvState n f Byz) (init_inv n f Byz) (step_inv n f Byz)


/-! ## Lemma 1: at most one notarized block per epoch -/

/-- Membership in a block's voter set is just having cast that vote. -/
@[tla_msgs] theorem mem_voters {s : St n} {i : Fin n} {b : Blk} :
    i ∈ voters n s b ↔ (i, b) ∈ s.msgs := by
  simp [voters]

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
    {s : St n} (hs : Inv n f Byz s) {b₁ b₂ : Blk}
    (hn1 : Notarized n f s b₁) (hn2 : Notarized n f s b₂) (he : bep b₁ = bep b₂) :
    b₁ = b₂ := by
  have hv := hs.valid
  have h1 := hs.honestUniq
  have valid_of_quorum : ∀ {b : Blk}, quorum f ≤ (voters n s b).card → ValidChain b := by
    intro b hq
    rw [quorum] at hq
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
        hq1 hq2 (by rw [quorum]; omega)
      rw [mem_voters] at hi1 hi2
      exact h1 i b₁ b₂ hih hi1 hi2 he

/-! ## Consistency -/

/-- Three adjacent blocks with consecutive epochs: `bNext`'s parent is
`bMid`, `bMid`'s parent is `bPrev`, and the epochs increase by one at
each step (`bep bMid = bep bPrev + 1`, `bep bNext = bep bMid + 1`). The
finalization rule: three such blocks at the head of a notarized chain
finalize the middle one's prefix. -/
def Consecutive (bPrev bMid bNext : Blk) : Prop :=
  bNext.tail = bMid ∧ bMid.tail = bPrev ∧
  bep bMid = bep bPrev + 1 ∧ bep bNext = bep bMid + 1

/-- `X` conflicts with `b`: a different block of the same length. -/
def Conflicts (X b : Blk) : Prop := X ≠ b ∧ X.length = b.length

/-- The paper's consistency theorem at an invariant state: if a notarized
chain ends in three blocks with consecutive epochs, no other block of the
middle one's length can be notarized.

The paper's two-case epoch analysis collapses to one move per case:
quorum intersection puts an honest node in the two voter sets, and I5
(its later votes have longer parents) yields the impossible length
inequality; the three middle epochs fall to `unique_notarized`. -/
theorem consistency_of_inv (hn : n = 3 * f + 1) (hB : Byz.card ≤ f)
    {s : St n} (hs : Inv n f Byz s)
    {bPrev bMid bNext X : Blk} (hChain : NotarizedChain n f s bNext)
    (hConsec : Consecutive bPrev bMid bNext) (hConf : Conflicts X bMid) :
    ¬ Notarized n f s X := by
  rcases hConsec with ⟨hNextMid, hMidPrev, heMid, heNext⟩
  rcases hConf with ⟨hXne, hXlen⟩
  have hv := hs.valid
  have h5 := hs.lengthMono
  intro hnotX
  -- The three blocks are nonempty, notarized (suffixes of bNext), and
  -- bNext is genuinely voted, hence valid; so genesis lies in all of them.
  have bepMidPos : 0 < bep bMid := by omega
  have bepNextPos : 0 < bep bNext := by omega
  have neMid : bMid ≠ [] := ne_of_bep_pos bepMidPos
  have neNext : bNext ≠ [] := ne_of_bep_pos bepNextPos
  have nNext : Notarized n f s bNext := hChain bNext neNext (List.suffix_refl bNext)
  have nMid : Notarized n f s bMid := hChain bMid neMid (hNextMid ▸ List.tail_suffix bNext)
  have NextNe0 : bNext ≠ [0] := by
    intro hc; rw [hc] at heNext; simp [bep] at heNext
  have qNext : quorum f ≤ (voters n s bNext).card := nNext.resolve_left NextNe0
  have h0Next : 0 ∈ bNext := by
    have hq := qNext
    rw [quorum] at hq
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < (voters n s bNext).card)
    rw [mem_voters] at hi
    exact (hv i bNext hi).1
  have h0Mid : 0 ∈ bMid := hNextMid ▸ mem_tail_of_bep_pos h0Next bepNextPos
  have h0Prev : 0 ∈ bPrev := hMidPrev ▸ mem_tail_of_bep_pos h0Mid bepMidPos
  have nePrev : bPrev ≠ [] := by intro hc; rw [hc] at h0Prev; simp at h0Prev
  have hPrevSuf : bPrev <:+ bNext :=
    (hMidPrev ▸ List.tail_suffix bMid).trans (hNextMid ▸ List.tail_suffix bNext)
  have nPrev : Notarized n f s bPrev := hChain bPrev nePrev hPrevSuf
  -- Length arithmetic.
  have lenNext : 0 < bNext.length := List.length_pos_of_mem h0Next
  have lenMid : 0 < bMid.length := List.length_pos_of_mem h0Mid
  have lenNextEq : bNext.length = bMid.length + 1 := by
    have h := congrArg List.length hNextMid
    rw [List.length_tail] at h; omega
  have lenMidEq : bMid.length = bPrev.length + 1 := by
    have h := congrArg List.length hMidPrev
    rw [List.length_tail] at h; omega
  have lenPrev : 0 < bPrev.length := List.length_pos_of_mem h0Prev
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
      hu hv' (by rw [quorum]; omega)
    rw [mem_voters] at hi1 hi2
    exact ⟨i, hih, hi1, hi2⟩
  -- Five-way epoch analysis.
  rcases lt_trichotomy (bep X) (bep bMid) with hlt | heq | hgt
  · rcases lt_trichotomy (bep X) (bep bPrev) with hlt2 | heq2 | hgt2
    · -- epoch X < epoch bPrev: honest i voted X (earlier) and bPrev
      have PrevNe0 : bPrev ≠ [0] := by
        intro hc; rw [hc] at hlt2; simp [bep] at hlt2
      obtain ⟨i, hih, hiX, hiPrev⟩ := inter qX (nPrev.resolve_left PrevNe0)
      have hle := h5 i X bPrev hih hiX hiPrev hlt2
      rw [List.length_tail, List.length_tail] at hle
      omega
    · -- epoch X = epoch bPrev: Lemma 1 forces X = bPrev, too short
      have hXPrev : X = bPrev := unique_notarized n f Byz hn hB hs hnotX nPrev heq2
      rw [hXPrev] at hXlen
      omega
    · omega
  · -- epoch X = epoch bMid: Lemma 1 forces X = bMid
    exact hXne (unique_notarized n f Byz hn hB hs hnotX nMid heq)
  · rcases lt_trichotomy (bep X) (bep bNext) with hlt2 | heq2 | hgt2
    · omega
    · -- epoch X = epoch bNext: Lemma 1 forces X = bNext, too long
      have hXNext : X = bNext := unique_notarized n f Byz hn hB hs hnotX nNext heq2
      rw [hXNext, lenNextEq] at hXlen
      omega
    · -- epoch X > epoch bNext: honest i voted bNext (earlier) and X
      obtain ⟨i, hih, hiX, hiNext⟩ := inter qX qNext
      have hle := h5 i bNext X hih hiNext hiX hgt2
      rw [List.length_tail, List.length_tail] at hle
      omega

/-- Consistency packaged over executions: at every reachable state, no
block conflicting with the finalized middle block can be notarized. -/
theorem consistency (hn : n = 3 * f + 1) (hB : Byz.card ≤ f)
    (e : Behavior (St n)) (hE : Hspec n f Byz e) (k : ℕ)
    {bPrev bMid bNext X : Blk} (hChain : NotarizedChain n f (e k) bNext)
    (hConsec : Consecutive bPrev bMid bNext) (hConf : Conflicts X bMid) :
    ¬ Notarized n f (e k) X :=
  consistency_of_inv n f Byz hn hB
    (by simpa [InvState] using (always_statePred_at (k := k) (safety n f Byz e hE)))
    hChain hConsec hConf

end Bft.Examples.Streamlet
