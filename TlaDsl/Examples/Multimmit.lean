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

/-! ## Extension carry and settledness (Lemma 7, heights)

The rank rules fix each chain's tip *position*; the extension rules then
deepen the tip if enough votes count for blocks above the proposal. In
height terms (all on one chain, blocks comparable by height):

* a vote with endorsed height `endorse p` counts for every height `≤ endorse p`
  (`CountsForHeight`/`Supported`, downward-closed);
* the **extension carry** of a V-QC is the deepest height at least the
  position height that `2f+1` votes in the V-tally support (`IsDeepest` at
  threshold `2f+1`);
* the **finalised tip** `F` of an L-QC is the deepest height at least the
  position height that *every* vote in the pool `P` supports (threshold
  `P.card`, i.e. unanimity), applied only in the `k* = m` case.

Lemma 7's two remaining parts, at the height level:

* `carry_reaches_final` (7a, extension half): if `F` is unanimity-deepened
  from `h0`, the V-QC carry from the same `h0` reaches `F` — of the
  `n−f−|Byz|` correct voters counting for `F`, at most `f` are missing from
  the V-notarisation's `n−f`-message set, leaving `≥ n−3f ≥ 2f+1` votes in
  the V-tally counting for `F`.
* `carry_bounded_settled` (7b): if the chain is *settled* (`β + (n−|P|) ≤ f`,
  where `β` is the number of pool votes endorsing strictly above `F`), no
  height above `F` can be `2f+1`-supported in the V-tally: correct votes
  above `F` number at most `β + (n−|P|) ≤ f` and faulty at most `f`.

Together they give `safe_extension_settled`: under settledness the V-QC tip
height equals the L-QC tip height, i.e. `Tips(W) = F` (Lemma 7b). The
abstraction elides two chain-layer facts that the paper uses at this point —
certified blocks on a chain are compatible (so "extends" is height
comparison), and correct processors DA-vote at most once per height — which
are the subject of the DA-certificate slice.
-/

/-- The number of votes in `V` endorsing height at least `h`. -/
def CountsForHeight (endorse : Proc → Nat) (V : Finset Proc) (h : Nat) : Nat :=
  (V.filter (fun p => h ≤ endorse p)).card

/-- `h` is supported by at least `thr` votes in `V`. -/
def Supported (endorse : Proc → Nat) (V : Finset Proc) (thr : Nat) (h : Nat) : Prop :=
  thr ≤ CountsForHeight endorse V h

/-- `hF` is the deepest height at least `h0` supported by `V` at threshold
`thr` (the extension carry at `2f+1`, or the unanimity deepening at
`V.card`). -/
def IsDeepest (endorse : Proc → Nat) (V : Finset Proc) (thr : Nat) (h0 hF : Nat) : Prop :=
  h0 ≤ hF ∧ Supported endorse V thr hF ∧
    ∀ h : Nat, h0 ≤ h → Supported endorse V thr h → h ≤ hF

/-- `CountsForHeight` is antitone in the height. -/
theorem counts_mono {endorse : Proc → Nat} {V : Finset Proc} {h h' : Nat} (hle : h ≤ h') :
    CountsForHeight endorse V h' ≤ CountsForHeight endorse V h := by
  unfold CountsForHeight
  exact Finset.card_le_card (by
    intro p hp
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1, le_trans hle (Finset.mem_filter.mp hp).2⟩)

/-- Maximality of the deepest supported height. -/
theorem deepest_le_of_supported {endorse : Proc → Nat} {V : Finset Proc} {thr h0 h hF : Nat}
    (hD : IsDeepest endorse V thr h0 hF) (hh0 : h0 ≤ h) (hh : Supported endorse V thr h) :
    h ≤ hF := hD.2.2 h hh0 hh

/-- Unanimity support: if `V.card` votes support `h`, every vote in `V`
endorses at least `h`. -/
theorem counts_all {endorse : Proc → Nat} {V : Finset Proc} {h : Nat}
    (hS : Supported endorse V V.card h) : ∀ p : Proc, p ∈ V → h ≤ endorse p := by
  intro p hp
  by_contra hnot
  have hlt : endorse p < h := Nat.lt_of_not_ge hnot
  have hle : (V.filter (fun p => h ≤ endorse p)).card ≤ V.card - 1 := by
    have hsub : V.filter (fun p => h ≤ endorse p) ⊆ V.erase p := by
      intro q hq
      have hqV : q ∈ V := (Finset.mem_filter.mp hq).1
      have hqh : h ≤ endorse q := (Finset.mem_filter.mp hq).2
      exact Finset.mem_erase.mpr ⟨(by intro hqp; subst q; exact (not_lt_of_ge hqh) hlt), hqV⟩
    have hcard : (V.erase p).card = V.card - 1 := Finset.card_erase_of_mem hp
    simpa [hcard] using Finset.card_le_card hsub
  have hS' : V.card ≤ (V.filter (fun p => h ≤ endorse p)).card := hS
  have hVpos : 0 < V.card := Finset.card_pos.mpr ⟨p, hp⟩
  omega

/-- **Lemma 7a (extension half).** If the L-QC tip `F` is the deepest height
`≥ h0` supported by the whole pool `P` (unanimity), then the V-QC extension
carry from the same `h0` reaches `F`. -/
theorem carry_reaches_final {n f : Nat} {Byz P Wset Wv : Finset Proc} {endorse : Proc → Nat}
    {h0 hF hW : Nat}
    (hByz : Byz.card ≤ f)
    (hP : P ⊆ Finset.range n) (hPcard : n - f ≤ P.card)
    (hWset : Wset ⊆ Finset.range n) (hWsetCard : n - f ≤ Wset.card)
    (hAppear : ∀ p : Proc, p ∈ P → p ∉ Byz → p ∈ Wset → p ∈ Wv)
    (hFdeep : IsDeepest endorse P P.card h0 hF)
    (hWdeep : IsDeepest endorse Wv (2 * f + 1) h0 hW)
    (hn : 5 * f + 1 ≤ n) :
    hF ≤ hW := by
  have hPall : ∀ p : Proc, p ∈ P → hF ≤ endorse p := counts_all hFdeep.2.1
  let C := P.filter (fun p => p ∉ Byz)
  have hC_ge : n - f - Byz.card ≤ C.card := by
    have hsum : C.card + (P.filter (fun p => p ∈ Byz)).card = P.card := by
      simpa [C] using (Finset.card_filter_add_card_filter_not (s := P) (p := fun p => p ∉ Byz))
    have hbyz : (P.filter (fun p => p ∈ Byz)).card ≤ Byz.card := by
      exact Finset.card_le_card (by intro p hp; exact (Finset.mem_filter.mp hp).2)
    omega
  have hC_sub : C ⊆ Finset.range n := by
    intro p hp
    exact hP (Finset.mem_filter.mp hp).1
  have hC_out : (C \ Wset).card ≤ f := by
    have hsub : C \ Wset ⊆ Finset.range n \ Wset := by
      intro p hp
      exact Finset.mem_sdiff.mpr ⟨hC_sub (Finset.mem_sdiff.mp hp).1, (Finset.mem_sdiff.mp hp).2⟩
    have hcard : (Finset.range n \ Wset).card = n - Wset.card := by
      simpa [Finset.card_range] using Finset.card_sdiff_of_subset hWset
    calc
      (C \ Wset).card ≤ (Finset.range n \ Wset).card := Finset.card_le_card hsub
      _ = n - Wset.card := hcard
      _ ≤ f := by omega
  have hC_in : 2 * f + 1 ≤ (C ∩ Wset).card := by
    have hsum : (C ∩ Wset).card + (C \ Wset).card = C.card :=
      Finset.card_inter_add_card_sdiff C Wset
    omega
  have hSupp : Supported endorse Wv (2 * f + 1) hF := by
    unfold Supported CountsForHeight
    have hsub : C ∩ Wset ⊆ Wv.filter (fun p => hF ≤ endorse p) := by
      intro p hp
      have hpC : p ∈ C := (Finset.mem_inter.mp hp).1
      have hpW : p ∈ Wset := (Finset.mem_inter.mp hp).2
      have hpP : p ∈ P := (Finset.mem_filter.mp hpC).1
      have hpNot : p ∉ Byz := (Finset.mem_filter.mp hpC).2
      exact Finset.mem_filter.mpr ⟨hAppear p hpP hpNot hpW, hPall p hpP⟩
    have hle : (C ∩ Wset).card ≤ (Wv.filter (fun p => hF ≤ endorse p)).card :=
      Finset.card_le_card hsub
    omega
  exact deepest_le_of_supported hWdeep hFdeep.1 hSupp

/-- **Lemma 7b (settledness).** If the chain is settled (`β + (n−|P|) ≤ f`),
no height above the finalised tip `F` is `2f+1`-supported in the V-tally, so
the V-QC carry does not exceed `F`. -/
theorem carry_bounded_settled {n f : Nat} {Byz P Wv : Finset Proc} {endorse : Proc → Nat}
    {h0 hF hW : Nat}
    (hByz : Byz.card ≤ f)
    (hP : P ⊆ Finset.range n)
    (hWv : Wv ⊆ Finset.range n)
    (hWdeep : IsDeepest endorse Wv (2 * f + 1) h0 hW)
    (hSettled : (P.filter (fun p => hF < endorse p)).card + (n - P.card) ≤ f) :
    hW ≤ hF := by
  by_contra hgt
  have hFlt : hF < hW := Nat.lt_of_not_ge hgt
  let E := Wv.filter (fun p => hW ≤ endorse p)
  have hCorr : (E.filter (fun p => p ∉ Byz)).card ≤ f := by
    have hsum : ((E.filter (fun p => p ∉ Byz)).filter (fun p => p ∈ P)).card +
                ((E.filter (fun p => p ∉ Byz)).filter (fun p => p ∉ P)).card =
                (E.filter (fun p => p ∉ Byz)).card := by
      simpa using (Finset.card_filter_add_card_filter_not
        (s := E.filter (fun p => p ∉ Byz)) (p := fun p => p ∈ P))
    have h1 : ((E.filter (fun p => p ∉ Byz)).filter (fun p => p ∈ P)).card ≤
        (P.filter (fun p => hF < endorse p)).card := by
      exact Finset.card_le_card (by
        intro p hp
        have hpP : p ∈ P := (Finset.mem_filter.mp hp).2
        have hpH : hW ≤ endorse p := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).2
        exact Finset.mem_filter.mpr ⟨hpP, by omega⟩)
    have h2 : ((E.filter (fun p => p ∉ Byz)).filter (fun p => p ∉ P)).card ≤ n - P.card := by
      have hsub : (E.filter (fun p => p ∉ Byz)).filter (fun p => p ∉ P) ⊆ Finset.range n \ P := by
        intro p hp
        have hpWv : p ∈ Wv := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
        have hpNotP : p ∉ P := (Finset.mem_filter.mp hp).2
        exact Finset.mem_sdiff.mpr ⟨hWv hpWv, hpNotP⟩
      have hcard : (Finset.range n \ P).card = n - P.card := by
        simpa [Finset.card_range] using Finset.card_sdiff_of_subset hP
      calc
        ((E.filter (fun p => p ∉ Byz)).filter (fun p => p ∉ P)).card ≤
          (Finset.range n \ P).card := Finset.card_le_card hsub
        _ = n - P.card := hcard
    omega
  have hFaulty : (E.filter (fun p => p ∈ Byz)).card ≤ f := by
    have hsub : E.filter (fun p => p ∈ Byz) ⊆ Byz := by
      intro p hp
      exact (Finset.mem_filter.mp hp).2
    exact le_trans (Finset.card_le_card hsub) hByz
  have hTotal : E.card ≤ 2 * f := by
    have hsum : (E.filter (fun p => p ∉ Byz)).card + (E.filter (fun p => p ∈ Byz)).card = E.card := by
      simpa using (Finset.card_filter_add_card_filter_not (s := E) (p := fun p => p ∉ Byz))
    omega
  have hSuppW : Supported endorse Wv (2 * f + 1) hW := hWdeep.2.1
  have hSuppE : 2 * f + 1 ≤ E.card := by
    simpa [E, Supported, CountsForHeight] using hSuppW
  omega

/-- **Lemma 7b.** Under settledness the V-QC tip height equals the L-QC tip
height: `Tips(W) = F`. -/
theorem safe_extension_settled {n f : Nat} {Byz P Wset Wv : Finset Proc} {endorse : Proc → Nat}
    {h0 hF hW : Nat}
    (hByz : Byz.card ≤ f)
    (hP : P ⊆ Finset.range n) (hPcard : n - f ≤ P.card)
    (hWset : Wset ⊆ Finset.range n) (hWsetCard : n - f ≤ Wset.card)
    (hWv : Wv ⊆ Finset.range n)
    (hAppear : ∀ p : Proc, p ∈ P → p ∉ Byz → p ∈ Wset → p ∈ Wv)
    (hFdeep : IsDeepest endorse P P.card h0 hF)
    (hWdeep : IsDeepest endorse Wv (2 * f + 1) h0 hW)
    (hn : 5 * f + 1 ≤ n)
    (hSettled : (P.filter (fun p => hF < endorse p)).card + (n - P.card) ≤ f) :
    hW = hF := by
  have h1 : hF ≤ hW := carry_reaches_final hByz hP hPcard hWset hWsetCard hAppear hFdeep hWdeep hn
  have h2 : hW ≤ hF := carry_bounded_settled hByz hP hWv hWdeep hSettled
  omega

end TlaDsl.Examples.Multimmit
