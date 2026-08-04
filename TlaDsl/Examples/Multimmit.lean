import TlaDsl.Basic

/-! # Multimmit extraction core: rank rules and safe extension

The Multimmit consensus layer (Lewis-Pye & O'Grady, *Multimmit: Extending
Blocks for Faster Finality*, arXiv:2607.21021) finalises per-chain tips from
sets of votes. The **extraction rules** are the paper's Section 4.2 functions
`Tips` (for a V-QC, the "safe to extend" tips) and `Tips*` (for an L-QC, the
finalised tips), both built on a **rank rule**: order the reported positions
on a chain from greatest to least (with multiplicity), discard the first `f`
values for a V-QC and the first `3f` for an L-QC, and take the next value as
the tip's position. Extensions (blocks above the proposed tip) then apply a
deeper-block carry at a `2f+1` (V-QC) or unanimity (L-QC) threshold.

The safety of the extraction is **Lemma 7 (safe extension)**: if the L-QC
pool `Pv` (at least `n - f` votes for the block) has rank `kStar` after
discarding `3f`, then every same-view V-notarisation's vote tally `Wv` (at
least `2f + 1` votes for the same block) has rank `k ≥ kStar`, so the V-QC's
tip extends the L-QC's tip. This file proves the **position part** of that
lemma, which is where the Byzantine quorum arithmetic lives:

* `RankAt V π k j`: `k` is the `(j+1)`-th largest position in `V`;
* `rank_transfer`: of the `3f+1` pool votes reporting `≥ k`, at least `f+1`
  come from correct processors whose messages also appear in the
  V-notarisation's message set (the `(n-f)`/`(n-f)`-message overlap, plus
  `|Byz| ≤ f`);
* `rank_ge`: the V-QC rank is at least the L-QC rank;
* `safe_extension_positions`: the V-QC tip block extends the L-QC tip block.

The `hAppear` hypothesis is exactly the paper's Lemmas 2–4 (one vote per
view, vote–novote exclusivity, designation): a correct voter for the block
that appears in the V-notarisation's `n-f` message set must appear there as
its vote for the same block. The extension-carry (deepest block with
`2f+1`/unanimity support) and the settledness equality (Lemma 7(b)) are the
documented next steps; the write-up
`docs/research/multimmit-exploration.md` tracks the remaining slices.
-/

namespace TlaDsl.Examples.Multimmit

abbrev Proc := Nat
abbrev Block := Nat

/-! ## Positions and the rank rule -/

/-- The number of votes in `V` reporting a position at least `k`. -/
def AtLeast (V : Finset Proc) (π : Proc → Nat) (k : Nat) : Nat :=
  (V.filter (fun v => k ≤ π v)).card

/-- `k` is the `(j+1)`-th largest position reported by `V` (with
multiplicity, `j` 0-based): more than `j` votes report `≥ k`, and at most
`j` report `> k`. -/
def RankAt (V : Finset Proc) (π : Proc → Nat) (k j : Nat) : Prop :=
  j < AtLeast V π k ∧ AtLeast V π (k + 1) ≤ j

/-- `AtLeast` is antitone in the threshold. -/
theorem atLeast_mono {V : Finset Proc} {π : Proc → Nat} {k k' : Nat} (h : k ≤ k') :
    AtLeast V π k' ≤ AtLeast V π k := by
  unfold AtLeast
  exact Finset.card_le_card (by
    intro v hv
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).1, le_trans h (Finset.mem_filter.mp hv).2⟩)

/-- A concrete check of the rank rule: positions `{3, 5, 5}` have
second-largest value `5`. -/
example : RankAt ({0, 1, 2} : Finset Proc)
    (fun v => if v = 0 then 3 else if v = 1 then 5 else 5) 5 1 := by
  unfold RankAt AtLeast
  decide

/-! ## The Byzantine overlap (Lemma 7, positions) -/

/-- From `3f+1` pool votes reporting at least `k`, at least `f+1` of them are
correct processors whose messages also appear in the V-notarisation's
`n-f`-message set:

* `3f+1` pool votes, minus at most `f` Byzantine, leave `2f+1` correct;
* the `n-f`-message V-notarisation set is missing at most `f` processors
  overall, so at least `2f+1 - f = f+1` of them appear there;
* each such correct voter appears in `Wv` by `hAppear` (Lemmas 2–4). -/
theorem rank_transfer {n f : Nat} {Byz Pv Wset Wv : Finset Proc} {π : Proc → Nat} {k : Nat}
    (hByz : Byz.card ≤ f)
    (hPv : Pv ⊆ Finset.range n)
    (hWset : Wset ⊆ Finset.range n) (hWsetCard : n - f ≤ Wset.card)
    (hAppear : ∀ v : Proc, v ∈ Pv → v ∉ Byz → v ∈ Wset → v ∈ Wv)
    (hA : 3 * f + 1 ≤ AtLeast Pv π k) :
    f + 1 ≤ AtLeast Wv π k := by
  let A := Pv.filter (fun v => k ≤ π v)
  let C := A.filter (fun v => v ∉ Byz)
  have hA_ge : 3 * f + 1 ≤ A.card := by
    simpa [A, AtLeast] using hA
  have hC_ge : 2 * f + 1 ≤ C.card := by
    have hsum : C.card + (A.filter (fun v => v ∈ Byz)).card = A.card := by
      simpa [C] using
        (Finset.card_filter_add_card_filter_not (s := A) (p := fun v => v ∉ Byz))
    have hbyz : (A.filter (fun v => v ∈ Byz)).card ≤ Byz.card := by
      exact Finset.card_le_card (by
        intro v hv
        exact (Finset.mem_filter.mp hv).2)
    omega
  have hC_sub : C ⊆ Finset.range n := by
    intro v hv
    exact hPv (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).1
  have hC_out : (C \ Wset).card ≤ f := by
    have hsub : C \ Wset ⊆ Finset.range n \ Wset := by
      intro v hv
      exact Finset.mem_sdiff.mpr ⟨hC_sub (Finset.mem_sdiff.mp hv).1, (Finset.mem_sdiff.mp hv).2⟩
    have hcard : (Finset.range n \ Wset).card = n - Wset.card := by
      simpa [Finset.card_range] using Finset.card_sdiff_of_subset hWset
    calc
      (C \ Wset).card ≤ (Finset.range n \ Wset).card := Finset.card_le_card hsub
      _ = n - Wset.card := hcard
      _ ≤ f := by omega
  have hC_in : f + 1 ≤ (C ∩ Wset).card := by
    have hsum : (C ∩ Wset).card + (C \ Wset).card = C.card :=
      Finset.card_inter_add_card_sdiff C Wset
    omega
  have hsub : C ∩ Wset ⊆ Wv.filter (fun v => k ≤ π v) := by
    intro v hv
    have hvC : v ∈ C := (Finset.mem_inter.mp hv).1
    have hvW : v ∈ Wset := (Finset.mem_inter.mp hv).2
    have hvA : v ∈ A := (Finset.mem_filter.mp hvC).1
    have hvNot : v ∉ Byz := (Finset.mem_filter.mp hvC).2
    have hvPv : v ∈ Pv := (Finset.mem_filter.mp hvA).1
    have hvk : k ≤ π v := (Finset.mem_filter.mp hvA).2
    exact Finset.mem_filter.mpr ⟨hAppear v hvPv hvNot hvW, hvk⟩
  have hle : (C ∩ Wset).card ≤ AtLeast Wv π k := by
    simpa [AtLeast] using Finset.card_le_card hsub
  omega

/-- The V-notarisation rank is at least the L-QC rank (Lemma 7, positions).
From `f+1 ≤ AtLeast Wv π kStar`, the `(f+1)`-th largest value of `Wv` is at
least `kStar`; if `k < kStar` then `Wv` would have at most `f` votes above
`k`, contradicting `AtLeast Wv π (k+1) ≤ f`. -/
theorem rank_ge {n f : Nat} {Byz Pv Wset Wv : Finset Proc} {π : Proc → Nat} {kStar k : Nat}
    (hByz : Byz.card ≤ f)
    (hPv : Pv ⊆ Finset.range n)
    (hWset : Wset ⊆ Finset.range n) (hWsetCard : n - f ≤ Wset.card)
    (hAppear : ∀ v : Proc, v ∈ Pv → v ∉ Byz → v ∈ Wset → v ∈ Wv)
    (hRankL : RankAt Pv π kStar (3 * f))
    (hRankV : RankAt Wv π k f) :
    kStar ≤ k := by
  have htrans : f + 1 ≤ AtLeast Wv π kStar :=
    rank_transfer hByz hPv hWset hWsetCard hAppear (Nat.succ_le_of_lt hRankL.1)
  by_contra hnot
  have hlt : k < kStar := Nat.lt_of_not_ge hnot
  have hmono : AtLeast Wv π kStar ≤ AtLeast Wv π (k + 1) := by
    apply atLeast_mono
    omega
  have hchain : f + 1 ≤ AtLeast Wv π (k + 1) := le_trans htrans hmono
  have hbad : f + 1 ≤ f := le_trans hchain hRankV.2
  omega

/-! ## Blocks: proposal positions form a chain -/

/-- A transaction chain: blocks have heights, and the proposal pins position
`k` to the block `prop k`, at strictly increasing heights. Extensions
(blocks above the proposed tip) are modelled by heights beyond the proposal;
the carry rules are the documented next step. -/
structure Chain where
  height : Block → Nat
  prop : Nat → Block
  prop_succ : ∀ k : Nat, height (prop (k + 1)) = height (prop k) + 1

/-- `b` extends `b'`: `b` is no shallower than `b'`. -/
def Extends (c : Chain) (b b' : Block) : Prop :=
  c.height b' ≤ c.height b

/-- Position monotonicity: later proposal positions extend earlier ones. -/
private lemma extend_prop_aux {c : Chain} : ∀ d k' : Nat,
    Extends c (c.prop (k' + d)) (c.prop k') := by
  intro d
  induction d with
  | zero => intro k'; simp [Extends]
  | succ d ih =>
      intro k'
      have hs : c.height (c.prop (k' + (d + 1))) = c.height (c.prop (k' + d)) + 1 := by
        simpa [Nat.add_assoc] using c.prop_succ (k' + d)
      exact le_trans (ih k') (by omega)

theorem extend_prop {c : Chain} {k k' : Nat} (h : k' ≤ k) :
    Extends c (c.prop k) (c.prop k') := by
  rcases Nat.exists_eq_add_of_le h with ⟨d, hEq⟩
  simpa [hEq] using extend_prop_aux d k'

/-! ## Lemma 7 (safe extension), position part -/

/-- **Safe extension, positions.** If the L-QC pool `Pv` (`n - f` or more
votes for the block) has rank `kStar` after discarding `3f`, and a
V-notarisation's vote tally `Wv` (at least `2f + 1` votes) has rank `k`
after discarding `f`, then the V-QC tip `prop k` extends the L-QC tip
`prop kStar`. This is the position part of the paper's Lemma 7(a); the
extension-carry that deepens the V-QC tip only strengthens the conclusion. -/
theorem safe_extension_positions {n f : Nat} {Byz Pv Wset Wv : Finset Proc} {π : Proc → Nat}
    {c : Chain} {kStar k : Nat}
    (hByz : Byz.card ≤ f)
    (hPv : Pv ⊆ Finset.range n)
    (hWset : Wset ⊆ Finset.range n) (hWsetCard : n - f ≤ Wset.card)
    (hAppear : ∀ v : Proc, v ∈ Pv → v ∉ Byz → v ∈ Wset → v ∈ Wv)
    (hRankL : RankAt Pv π kStar (3 * f))
    (hRankV : RankAt Wv π k f) :
    Extends c (c.prop k) (c.prop kStar) := by
  exact extend_prop (rank_ge hByz hPv hWset hWsetCard hAppear hRankL hRankV)

end TlaDsl.Examples.Multimmit
