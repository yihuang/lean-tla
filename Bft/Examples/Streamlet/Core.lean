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
def Blk.epoch (b : Blk) : ℕ := b.head?.getD 0

variable (n f : ℕ) (Byz : Finset (Fin n))

/-- Global state: epoch clock and the votes cast so far. -/
structure VoteLog (n : ℕ) where
  epoch : ℕ
  msgs : Finset (Fin n × Blk)

/-- The distinct voters of a block. -/
def voters (s : VoteLog n) (b : Blk) : Finset (Fin n) :=
  (s.msgs.filter fun p => p.2 = b).image Prod.fst

/-- Notarization threshold: `2f+1` out of (at most) `3f+1`. -/
def quorum (f : ℕ) : ℕ := 2 * f + 1

/-- A block is notarized with `2f+1` distinct votes; genesis is
notarized by fiat. -/
def Notarized (f : ℕ) (s : VoteLog n) (b : Blk) : Prop :=
  b = [0] ∨ quorum f ≤ (voters n s b).card

/-- A chain is notarized if every block in it (every nonempty suffix)
is notarized. -/
def NotarizedChain (f : ℕ) (s : VoteLog n) (c : Blk) : Prop :=
  ∀ d : Blk, d ≠ [] → d <:+ c → Notarized n f s d

/-! ## Actions -/

/-- Time passes. -/
def EpochTick : Action (VoteLog n) := fun s s' =>
  s'.epoch = s.epoch + 1 ∧ s'.msgs = s.msgs

/-- An honest vote: in the block's own epoch, the node's first vote this
epoch, on a block whose parent chain is notarized and is (one of) the
longest notarized chain(s) seen. -/
def VoteH (i : Fin n) (b : Blk) : Action (VoteLog n) := fun s s' =>
  i ∉ Byz ∧
  ValidChain b ∧ b.epoch = s.epoch ∧
  (∀ b', (i, b') ∈ s.msgs → b'.epoch ≠ s.epoch) ∧
  NotarizedChain n f s b.tail ∧
  (∀ c : Blk, NotarizedChain n f s c → c.length ≤ b.tail.length) ∧
  s'.msgs = insert (i, b) s.msgs ∧ s'.epoch = s.epoch

/-- A Byzantine vote: any well-formed chain, any time. -/
def VoteB (i : Fin n) (b : Blk) : Action (VoteLog n) := fun s s' =>
  i ∈ Byz ∧ ValidChain b ∧ s'.msgs = insert (i, b) s.msgs ∧ s'.epoch = s.epoch

/-- The step relation. Private: the generic `Init`/`Next`/`vars` names are
module-local here, exported only through the `Spec` bundle `StreamletSpec`
(access its fields `(StreamletSpec n f Byz).Init/.Next/.vars`). -/
private def Next : Action (VoteLog n) := fun s s' =>
  EpochTick n s s' ∨ (∃ i b, VoteH n f Byz i b s s') ∨ (∃ i b, VoteB n Byz i b s s')

attribute [grind unfold] EpochTick VoteH VoteB

/-- Frame: the whole state. Private (see `Next`). -/
private def vars (n : ℕ) : VoteLog n → VoteLog n := id

/-- Initially: epoch 0, no votes. Private (see `Next`). -/
private def Init (n : ℕ) : StatePred (VoteLog n) := { s | s.epoch = 0 ∧ s.msgs = ∅ }

/-- The specification, bundled (for `Spec.init_invariant`). -/
def StreamletSpec (n f : ℕ) (Byz : Finset (Fin n)) : Spec (VoteLog n) (VoteLog n) :=
  ⟨Init n, Next n f Byz, vars n⟩

/-- The specification. -/
def Hspec : Pred (VoteLog n) := (StreamletSpec n f Byz).pred

/-! ## Monotonicity of notarization -/

theorem voters.mono {s t : VoteLog n} (h : s.msgs ⊆ t.msgs) (b : Blk) :
    voters n s b ⊆ voters n t b := by
  intro i hi
  change ∀ m, m ∈ s.msgs → m ∈ t.msgs at h
  rw [voters, Finset.mem_image] at hi ⊢
  obtain ⟨p, hp, hpi⟩ := hi
  rw [Finset.mem_filter] at hp
  exact ⟨p, Finset.mem_filter.mpr ⟨h p hp.1, hp.2⟩, hpi⟩

theorem Notarized.mono {s t : VoteLog n} (h : s.msgs ⊆ t.msgs) (b : Blk) :
    Notarized n f s b → Notarized n f t b := by
  rintro (hb | hq)
  · exact Or.inl hb
  · exact Or.inr (le_trans hq (Finset.card_le_card (voters.mono n h b)))

theorem NotarizedChain.mono {s t : VoteLog n} (h : ∀ p, p ∈ s.msgs → p ∈ t.msgs)
    (c : Blk) : NotarizedChain n f s c → NotarizedChain n f t c :=
  fun hnc d hd hs => (hnc d hd hs).mono n f h d

attribute [grind =>] Notarized.mono NotarizedChain.mono

/-! ## The invariant bundle

Each paper invariant (IV, I0, I1, I2, I5) is a named field of the
structure `SafetyInv` (as in `Streamlet.Proto.Inv`), not an anonymous conjunct. -/

/-- The inductive invariant: one field per paper invariant.

* IV (`valid`): every vote cast is on a well-formed chain (ideal hashes);
* I0 (`honestVoteEpochLeClock`): honest votes happen in their own epoch, hence at most
  the clock;
* I1 (`honestUniq`): an honest node votes at most once per epoch;
* I2 (`parentNotarized`): an honest vote's parent chain was notarized at
  vote time — and stays notarized (monotonicity);
* I5 (`lengthMono`): an honest node's later votes extend longer parents:
  for any two honest votes `x`, `y` of the same node, `x.epoch < y.epoch`
  implies `x.tail.length ≤ y.tail.length`. This single inequality is the
  whole content of the paper's Case 1 / Case 2 argument. -/
structure SafetyInv (s : VoteLog n) : Prop where
  /-- IV: every vote cast is on a well-formed chain (ideal hashes). -/
  valid : ∀ i b, (i, b) ∈ s.msgs → ValidChain b
  /-- I0: honest votes happen in their own epoch, hence at most the clock. -/
  honestVoteEpochLeClock : ∀ i b, i ∉ Byz → (i, b) ∈ s.msgs → b.epoch ≤ s.epoch
  /-- I1 (HonestUniq): an honest node votes at most once per epoch. -/
  honestUniq : ∀ i b₁ b₂, i ∉ Byz → (i, b₁) ∈ s.msgs → (i, b₂) ∈ s.msgs →
    b₁.epoch = b₂.epoch → b₁ = b₂
  /-- I2: an honest vote's parent chain was notarized at vote time — and
  stays notarized (monotonicity). -/
  parentNotarized : ∀ i b, i ∉ Byz → (i, b) ∈ s.msgs → NotarizedChain n f s b.tail
  /-- I5: an honest node's later votes extend longer parents: for any two
  honest votes `x`, `y` of the same node, `x.epoch < y.epoch` implies
  `x.tail.length ≤ y.tail.length`. This single inequality is the whole
  content of the paper's Case 1 / Case 2 argument. -/
  lengthMono : ∀ i b₁ b₂, i ∉ Byz → (i, b₁) ∈ s.msgs → (i, b₂) ∈ s.msgs →
    b₁.epoch < b₂.epoch → b₁.tail.length ≤ b₂.tail.length

/-- `SafetyInv` as a state predicate, for the TLA induction. -/
def SafetyInvState : StatePred (VoteLog n) := { s | SafetyInv n f Byz s }

theorem init_inv : ∀ s, s ∈ Init n → s ∈ SafetyInvState n f Byz := by
  intro s hs
  obtain ⟨h0, h1⟩ := hs
  constructor <;> simp [h1]

theorem step_inv : ∀ s s', StutAction (Next n f Byz) (vars n) s s' →
    s ∈ SafetyInvState n f Byz → s' ∈ SafetyInvState n f Byz := by
  intro s s' hstep hinv
  rcases hstep with hnext | hstut
  swap
  · change s' = s at hstut
    rwa [hstut]
  rcases hinv with ⟨hvalid, hbep, huniq, hparent, hlen⟩
  rcases hnext with htick | ⟨i, b, hvote⟩ | ⟨i, b, hvote⟩ <;> constructor <;> grind

theorem safety : Entails (Hspec n f Byz) (always (statePred (SafetyInvState n f Byz))) :=
  (StreamletSpec n f Byz).init_invariant (SafetyInvState n f Byz) (init_inv n f Byz) (step_inv n f Byz)


/-! ## Lemma 1: at most one notarized block per epoch -/

/-- Membership in a block's voter set is just having cast that vote. -/
@[tla_msgs] theorem mem_voters {s : VoteLog n} {i : Fin n} {b : Blk} :
    i ∈ voters n s b ↔ (i, b) ∈ s.msgs := by
  simp [voters]

/-- A quorum of votes on a block makes it valid: some voter exists, and
every vote cast at an invariant state is on a well-formed chain. -/
theorem valid_of_quorum {s : VoteLog n} (hs : SafetyInv n f Byz s) {b : Blk}
    (hq : quorum f ≤ (voters n s b).card) : ValidChain b := by
  have hpos : 0 < (voters n s b).card := by
    rw [quorum] at hq
    omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  rw [mem_voters] at hi
  exact hs.valid i b hi

/-- A quorum of votes on a block proves it contains genesis (as its last
element). -/
theorem genesis_mem_of_quorum {s : VoteLog n} (hs : SafetyInv n f Byz s) {b : Blk}
    (hq : quorum f ≤ (voters n s b).card) : 0 ∈ b :=
  (valid_of_quorum n f Byz hs hq).1

/-- A valid chain whose epoch is 0 can only be genesis. -/
theorem ValidChain.eq_genesis {c : Blk} (hv : ValidChain c) (he : c.epoch = 0) : c = [0] := by
  obtain ⟨h0, hchain⟩ := hv
  cases c with
  | nil => simp at h0
  | cons a t =>
    have ha : a = 0 := by simpa [Blk.epoch] using he
    cases t with
    | nil => rw [ha]
    | cons b u =>
      cases hchain with
      | cons_cons hab _ =>
        rw [ha] at hab
        exact absurd hab (Nat.not_lt_zero b)

/-- A block with positive epoch is nonempty. -/
theorem Blk.epoch.ne_of_pos {c : Blk} (h : 0 < c.epoch) : c ≠ [] := by
  intro hc; rw [hc] at h; simp [Blk.epoch] at h

/-- Genesis sits in the tail of any chain with positive epoch that
contains it. -/
theorem Blk.epoch.mem_tail_of_pos {c : Blk} (h0 : 0 ∈ c) (hb : 0 < c.epoch) : 0 ∈ c.tail := by
  cases c with
  | nil => simp [Blk.epoch] at hb
  | cons a t =>
    rw [List.mem_cons] at h0
    rcases h0 with rfl | h0
    · simp [Blk.epoch] at hb
    · exact h0

/-- Two genuinely voted blocks share an honest voter: quorum intersection
(`Minimmit.exists_honest_inter`) plus `mem_voters`. -/
theorem exists_honest_voter_of_two_quorums (hn : n = 3 * f + 1) (hB : Byz.card ≤ f)
    {s : VoteLog n} {u v : Blk} (hu : quorum f ≤ (voters n s u).card)
    (hv : quorum f ≤ (voters n s v).card) :
    ∃ i, i ∉ Byz ∧ (i, u) ∈ s.msgs ∧ (i, v) ∈ s.msgs := by
  obtain ⟨i, hi1, hi2, hih⟩ := Minimmit.exists_honest_inter n f Byz hB (quorum f) (quorum f)
    hu hv (by rw [quorum]; omega)
  rw [mem_voters] at hi1 hi2
  exact ⟨i, hih, hi1, hi2⟩

/-- The paper's Lemma 1: per epoch, at most one block is notarized.
Quorum intersection yields an honest node in both voter sets; I1
(honest nodes vote at most once per epoch) finishes. -/
theorem unique_notarized (hn : n = 3 * f + 1) (hB : Byz.card ≤ f)
    {s : VoteLog n} (hs : SafetyInv n f Byz s) {b₁ b₂ : Blk}
    (hn1 : Notarized n f s b₁) (hn2 : Notarized n f s b₂) (he : b₁.epoch = b₂.epoch) :
    b₁ = b₂ := by
  have h1 := hs.honestUniq
  rcases hn1 with hg1 | hq1
  · subst hg1
    rcases hn2 with hg2 | hq2
    · exact hg2.symm
    · exact (ValidChain.eq_genesis (valid_of_quorum n f Byz hs hq2) he.symm).symm
  · rcases hn2 with hg2 | hq2
    · subst hg2
      exact ValidChain.eq_genesis (valid_of_quorum n f Byz hs hq1) he
    · obtain ⟨i, hih, hi1, hi2⟩ := exists_honest_voter_of_two_quorums n f Byz hn hB hq1 hq2
      exact h1 i b₁ b₂ hih hi1 hi2 he

/-! ## Consistency -/

/-- Three adjacent blocks with consecutive epochs: `bNext`'s parent is
`bMid`, `bMid`'s parent is `bPrev`, and the epochs increase by one at
each step (`bMid.epoch = bPrev.epoch + 1`, `bNext.epoch = bMid.epoch + 1`). The
finalization rule: three such blocks at the head of a notarized chain
finalize the middle one's prefix. -/
def Consecutive (bPrev bMid bNext : Blk) : Prop :=
  bNext.tail = bMid ∧ bMid.tail = bPrev ∧
  bMid.epoch = bPrev.epoch + 1 ∧ bNext.epoch = bMid.epoch + 1

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
    {s : VoteLog n} (hs : SafetyInv n f Byz s)
    {bPrev bMid bNext X : Blk} (hChain : NotarizedChain n f s bNext)
    (hConsec : Consecutive bPrev bMid bNext) (hConf : Conflicts X bMid) :
    ¬ Notarized n f s X := by
  rcases hConsec with ⟨hNextMid, hMidPrev, heMid, heNext⟩
  rcases hConf with ⟨hXne, hXlen⟩
  have hlenMono := hs.lengthMono
  intro hnotX
  -- The three blocks are nonempty, notarized (suffixes of bNext), and
  -- bNext is genuinely voted, hence valid; so genesis lies in all of them.
  have bepMidPos : 0 < bMid.epoch := by omega
  have bepNextPos : 0 < bNext.epoch := by omega
  have hMid_ne_nil : bMid ≠ [] := Blk.epoch.ne_of_pos bepMidPos
  have hNext_ne_nil : bNext ≠ [] := Blk.epoch.ne_of_pos bepNextPos
  have hNext_notarized : Notarized n f s bNext := hChain bNext hNext_ne_nil (List.suffix_refl bNext)
  have hMid_notarized : Notarized n f s bMid := hChain bMid hMid_ne_nil (hNextMid ▸ List.tail_suffix bNext)
  have hNext_ne_genesis : bNext ≠ [0] := by
    intro hc; rw [hc] at heNext; simp [Blk.epoch] at heNext
  have hNext_quorum : quorum f ≤ (voters n s bNext).card := hNext_notarized.resolve_left hNext_ne_genesis
  have hNext_has_genesis : 0 ∈ bNext := genesis_mem_of_quorum n f Byz hs hNext_quorum
  have hMid_has_genesis : 0 ∈ bMid := hNextMid ▸ Blk.epoch.mem_tail_of_pos hNext_has_genesis bepNextPos
  have hPrev_has_genesis : 0 ∈ bPrev := hMidPrev ▸ Blk.epoch.mem_tail_of_pos hMid_has_genesis bepMidPos
  have hPrev_ne_nil : bPrev ≠ [] := by intro hc; rw [hc] at hPrev_has_genesis; simp at hPrev_has_genesis
  have hPrev_suffix : bPrev <:+ bNext :=
    (hMidPrev ▸ List.tail_suffix bMid).trans (hNextMid ▸ List.tail_suffix bNext)
  have hPrev_notarized : Notarized n f s bPrev := hChain bPrev hPrev_ne_nil hPrev_suffix
  -- Length arithmetic.
  have hNext_len_pos : 0 < bNext.length := List.length_pos_of_mem hNext_has_genesis
  have hMid_len_pos : 0 < bMid.length := List.length_pos_of_mem hMid_has_genesis
  have hNext_len_eq : bNext.length = bMid.length + 1 := by
    have h := congrArg List.length hNextMid
    rw [List.length_tail] at h; omega
  have hMid_len_eq : bMid.length = bPrev.length + 1 := by
    have h := congrArg List.length hMidPrev
    rw [List.length_tail] at h; omega
  have hPrev_len_pos : 0 < bPrev.length := List.length_pos_of_mem hPrev_has_genesis
  -- X is long, hence not genesis, hence genuinely voted.
  have hX_ne_genesis : X ≠ [0] := by
    intro hc; rw [hc] at hXlen; simp at hXlen; omega
  have hX_quorum : quorum f ≤ (voters n s X).card := hnotX.resolve_left hX_ne_genesis
  -- Shared honest voter of two genuinely voted blocks
  -- (`exists_honest_voter_of_two_quorums`).
  rcases lt_trichotomy (X.epoch) (bMid.epoch) with hlt | heq | hgt
  · rcases lt_trichotomy (X.epoch) (bPrev.epoch) with hlt2 | heq2 | hgt2
    · -- epoch X < epoch bPrev: honest i voted X (earlier) and bPrev
      have hPrev_ne_genesis : bPrev ≠ [0] := by
        intro hc; rw [hc] at hlt2; simp [Blk.epoch] at hlt2
      obtain ⟨i, hih, hiX, hiPrev⟩ :=
        exists_honest_voter_of_two_quorums n f Byz hn hB hX_quorum (hPrev_notarized.resolve_left hPrev_ne_genesis)
      have hle := hlenMono i X bPrev hih hiX hiPrev hlt2
      rw [List.length_tail, List.length_tail] at hle
      omega
    · -- epoch X = epoch bPrev: Lemma 1 forces X = bPrev, too short
      have hXPrev : X = bPrev := unique_notarized n f Byz hn hB hs hnotX hPrev_notarized heq2
      rw [hXPrev] at hXlen
      omega
    · omega
  · -- epoch X = epoch bMid: Lemma 1 forces X = bMid
    exact hXne (unique_notarized n f Byz hn hB hs hnotX hMid_notarized heq)
  · rcases lt_trichotomy (X.epoch) (bNext.epoch) with hlt2 | heq2 | hgt2
    · omega
    · -- epoch X = epoch bNext: Lemma 1 forces X = bNext, too long
      have hXNext : X = bNext := unique_notarized n f Byz hn hB hs hnotX hNext_notarized heq2
      rw [hXNext, hNext_len_eq] at hXlen
      omega
    · -- epoch X > epoch bNext: honest i voted bNext (earlier) and X
      obtain ⟨i, hih, hiX, hiNext⟩ := exists_honest_voter_of_two_quorums n f Byz hn hB hX_quorum hNext_quorum
      have hle := hlenMono i bNext X hih hiNext hiX hgt2
      rw [List.length_tail, List.length_tail] at hle
      omega

/-- Consistency packaged over executions: at every reachable state, no
block conflicting with the finalized middle block can be notarized. -/
theorem consistency (hn : n = 3 * f + 1) (hB : Byz.card ≤ f)
    (e : Behavior (VoteLog n)) (hE : Hspec n f Byz e) (k : ℕ)
    {bPrev bMid bNext X : Blk} (hChain : NotarizedChain n f (e k) bNext)
    (hConsec : Consecutive bPrev bMid bNext) (hConf : Conflicts X bMid) :
    ¬ Notarized n f (e k) X :=
  consistency_of_inv n f Byz hn hB
    (by simpa [SafetyInvState] using (always_statePred_at (k := k) (safety n f Byz e hE)))
    hChain hConsec hConf

end Bft.Examples.Streamlet
