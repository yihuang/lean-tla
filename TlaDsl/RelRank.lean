import TlaDsl.Rules
import Mathlib.Data.Set.Card
import Mathlib.Order.WellFounded

/-! # Relational rankings (McMillan, CAV 2024)

Formalization of the liveness engine from Kenneth L. McMillan, *Toward
Liveness Proofs at Scale*, CAV 2024, LNCS 14681, pp. 255–276 — the repo's
north-star paper (see `docs/north-star.md`).

A *relational ranking* is a relation `δ : σ → α → Prop` whose extension is
finite at every finite time, ordered by implication: a step *conserves* `δ`
when it adds no elements and *reduces* `δ` when it removes at least one.
Soundness needs no well-founded domain for the ranking's elements (real
timestamps are fine); it only needs the ranking to stay finite, which is
established by `finite_rank` (the paper's Rule 5) or directly.

Contents:

* `Conserves`/`Reduces` — the two per-step shorthands;
* `finite_rank` — Rule 5: a relation is finite at every finite time when it
  starts empty and each step adds finitely many elements;
* `relational_ranking_rule` — Rule 6: `H ∧ □◇⟨r⟩ ⊢ p ↝ q` from an
  invariant `φ`, a relational ranking `δ`, a finite envelope `R`, and the
  step premises C1–C3 (proved under the spec `H`); soundness by finite
  descent on `|δ|`, mirroring `leads_to_via_nat`;
* `LexLess`/`lex_less_wellFounded` — Theorem 1: the lexicographic order
  induced by a lexicographic relational ranking (components as finite
  sets) is well-founded.
-/

namespace Tla

/-! ## Conservation and reduction -/

/-- A step conserves the relational ranking `δ` if it adds no elements
(`δ' ⊆ δ`). -/
def Conserves {σ : Type u} {α : Type v} (δ : σ → α → Prop) (s s' : σ) : Prop :=
  ∀ x, δ s' x → δ s x

/-- A step reduces the relational ranking `δ` if it removes at least one
element. -/
def Reduces {σ : Type u} {α : Type v} (δ : σ → α → Prop) (s s' : σ) : Prop :=
  ∃ x, δ s x ∧ ¬ δ s' x

/-! ## Rule 5: proving a ranking is finite at every time -/

/-- If `R` is empty initially and each step adds at most finitely many
elements, then `R` is finite at every finite time. This is the Lean-native
form of the paper's Rule 5: in the paper finiteness cannot be expressed in
the (EPR) logic and is established outside it; here it is a theorem by
induction on time. -/
theorem finite_rank {σ : Type u} {α : Type v} (R : σ → α → Prop) (e : Behavior σ)
    (h0 : ∀ x, ¬ R (e 0) x)
    (hstep : ∀ n : Nat, Set.Finite {x : α | R (e (n + 1)) x ∧ ¬ R (e n) x}) :
    ∀ n : Nat, Set.Finite {x : α | R (e n) x} := by
  intro n
  induction n with
  | zero =>
      -- initially empty: the extension is contained in `∅`
      refine Set.Finite.subset (s := (∅ : Set α)) Set.finite_empty ?_
      intro x hx
      exact (h0 x) hx
  | succ n ih =>
      -- `R_{n+1} ⊆ R_n ∪ (elements added at step n)`, both finite
      have hsub : {x | R (e (n + 1)) x} ⊆
          {x | R (e n) x} ∪ {x | R (e (n + 1)) x ∧ ¬ R (e n) x} := by
        intro x hx
        by_cases h : R (e n) x
        · exact Or.inl h
        · exact Or.inr ⟨hx, h⟩
      exact (Set.Finite.union ih (hstep n)).subset hsub

/-! ## Rule 6: the relational reactivity rule -/

/-- McMillan's relational reactivity rule (Rule 6 of the paper), with the
spec `H` supplying the invariants the premises are proved under:

* C1: `p` implies `q` or the invariant `φ` with `δ ⊆ R`;
* C2: while `φ` holds, every step either reaches `q` or keeps `φ` and
  conserves `δ`;
* C3: while `φ` holds, every step that fires the justice action `r` either
  reaches `q` or reduces `δ`;
* `R` is finite at every time,

then `p` leads to `q` under `H ∧ □◇⟨r⟩`. Soundness is finite descent:
`|δ|` is a natural rank that never increases and strictly decreases at
every `r`-step, so strong induction on `|δ|` terminates. -/
theorem relational_ranking_rule {σ : Type u} {α : Type v} (p q : StatePred σ)
    (r : Action σ) (φ : StatePred σ) (δ R : σ → α → Prop) (H : Pred σ)
    (hR : ∀ e : Behavior σ, ∀ n : Nat, Set.Finite {x : α | R (e n) x})
    (hC1 : ∀ e : Behavior σ, H e → ∀ k : Nat, p (e k) →
      q (e k) ∨ (φ (e k) ∧ ∀ x, δ (e k) x → R (e k) x))
    (hC2 : ∀ e : Behavior σ, H e → ∀ k : Nat, φ (e k) →
      q (e (k + 1)) ∨ (φ (e (k + 1)) ∧ Conserves δ (e k) (e (k + 1))))
    (hC3 : ∀ e : Behavior σ, H e → ∀ k : Nat, φ (e k) → r (e k) (e (k + 1)) →
      q (e (k + 1)) ∨ Reduces δ (e k) (e (k + 1))) :
    Entails (tlaAnd H (always (eventually (actionPred r))))
      (leadsTo (statePred p) (statePred q)) := by
  intro e h
  rcases h with ⟨hH, hJ⟩
  -- finite descent on |δ|: from φ at a finite rank, q is eventually reached
  have hmain : ∀ n : Nat, ∀ k : Nat,
      Set.Finite {x | δ (e k) x} → ({x | δ (e k) x}).ncard ≤ n → φ (e k) →
      eventually (statePred q) (e.drop k) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih k hfin hn hφk
    -- the justice condition: some step `m ≥ k` fires `r`
    have hJk : eventually (actionPred r) (e.drop k) := hJ k
    rcases hJk with ⟨m, hm⟩
    have hr : r (e (k + m)) (e (k + m + 1)) := by
      simpa [actionPred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm
    -- walk from `k` to `k + m`: unless `q` occurs, `φ` persists, `δ` is
    -- conserved at every step, and `δ` stays inside the (finite) start set
    have hwalk : ∀ d : Nat, d ≤ m →
        eventually (statePred q) (e.drop k) ∨
          (φ (e (k + d)) ∧
           (∀ m' : Nat, m' < d → Conserves δ (e (k + m')) (e (k + m' + 1))) ∧
           {x | δ (e (k + d)) x} ⊆ {x | δ (e k) x}) := by
      intro d
      induction d with
      | zero =>
          intro _hle
          right
          refine ⟨by simpa using hφk, ?_, ?_⟩
          · intro m' hm'
            omega
          · intro x hx
            exact hx
      | succ d ihd =>
          intro hle
          rcases ihd (Nat.le_trans (Nat.le_succ d) hle) with hev | hrest
          · exact Or.inl hev
          · rcases hrest with ⟨hφd, hcons, hsubd⟩
            have hc2 := hC2 e hH (k + d) hφd
            rcases hc2 with hq' | hrest'
            · left
              refine ⟨d + 1, ?_⟩
              simpa [statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using hq'
            · rcases hrest' with ⟨hφd1, hconsd⟩
              right
              refine ⟨by simpa [Nat.add_assoc] using hφd1, ?_, ?_⟩
              · intro m' hm'
                by_cases h : m' = d
                · simpa [h] using hconsd
                · exact hcons m' (by omega)
              · intro x hx
                exact hsubd (hconsd x hx)
    rcases hwalk m le_rfl with hev | hrest
    · exact hev
    · rcases hrest with ⟨hφm, _hcons, hsubm⟩
      -- C3 at the justice step: `q` now, or the rank strictly decreases
      have hc3 := hC3 e hH (k + m) hφm hr
      rcases hc3 with hq' | hred
      · refine ⟨m + 1, ?_⟩
        simpa [statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hq'
      · rcases hred with ⟨x0, hx0in, hx0out⟩
        -- `φ` persists one more step (C2 at `k + m`) and `δ` is conserved
        have hc2m := hC2 e hH (k + m) hφm
        rcases hc2m with hq'' | hrest'
        · refine ⟨m + 1, ?_⟩
          simpa [statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hq''
        · rcases hrest' with ⟨hφm1, hconsm⟩
          -- `δ_{k+m+1} ⊊ δ_{k+m} ⊆ δ_k`, so the cardinal strictly decreases
          have hsubm1 : {x | δ (e (k + m + 1)) x} ⊆ {x | δ (e k) x} := by
            intro x hx
            exact hsubm (hconsm x hx)
          have hfinm : Set.Finite {x | δ (e (k + m)) x} := hfin.subset hsubm
          have hfinm1 : Set.Finite {x | δ (e (k + m + 1)) x} := hfin.subset hsubm1
          have hssub : {x | δ (e (k + m + 1)) x} ⊂ {x | δ (e (k + m)) x} := by
            constructor
            · exact hconsm
            · intro hsup
              exact hx0out (hsup hx0in)
          have hnlt : ({x | δ (e (k + m + 1)) x}).ncard <
              ({x | δ (e (k + m)) x}).ncard :=
            Set.ncard_lt_ncard hssub hfinm
          have hnle : ({x | δ (e (k + m)) x}).ncard ≤ n :=
            le_trans (Set.ncard_le_ncard hsubm hfin) hn
          have hn' : ({x | δ (e (k + m + 1)) x}).ncard < n :=
            lt_of_lt_of_le hnlt hnle
          -- induction hypothesis at the strictly smaller rank
          have hev' : eventually (statePred q) ((e.drop k).drop (m + 1)) := by
            simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              ih ({x | δ (e (k + m + 1)) x}).ncard hn' (k + m + 1) hfinm1 le_rfl hφm1
          -- lift from the suffix at offset `m + 1` back to the suffix at `k`
          rcases hev' with ⟨t, ht⟩
          refine ⟨m + 1 + t, ?_⟩
          simpa [statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using ht
  intro k hp
  have hp' : p (e k) := by
    simpa [statePred, Cslib.ωSequence.drop, Nat.add_comm] using hp
  have hc1 := hC1 e hH k hp'
  rcases hc1 with hq | hrest
  · refine ⟨0, ?_⟩
    simpa [statePred, Cslib.ωSequence.drop, Nat.add_comm] using hq
  · rcases hrest with ⟨hφk, hδR⟩
    have hfin : Set.Finite {x | δ (e k) x} := (hR e k).subset hδR
    exact hmain ({x | δ (e k) x}).ncard k hfin le_rfl hφk

/-! ## Theorem 1: lexicographic relational rankings are well-founded -/

/-- A lexicographic relational ranking is a finite family of finite-set
components; `LexLess` is the paper's induced pre-order: `s₁` is
lexicographically below `s₂` when, at the first index where the components
differ, `s₁`'s set is a proper subset of `s₂`'s (so time advancing removes
elements from the low-order component only after all higher components have
stabilized). Components are `Finset α` here (the finite-representation
version of the ranking; the paper allows arbitrary relations with proved
finiteness). -/
def LexLess {σ : Type u} {α : Type v} {n : Nat} (δs : Fin n → σ → Finset α)
    (s₁ s₂ : σ) : Prop :=
  -- `(<)` on `Finset` is proper subset (`Finset.lt_iff_ssubset`), so the
  -- strict-set spelling below is the paper's `δᵢ[s₁] ⊂ δᵢ[s₂]`
  ∃ i : Fin n, (∀ j : Fin n, j.val < i.val → δs j s₁ = δs j s₂) ∧ δs i s₁ < δs i s₂

/-- Theorem 1 (McMillan, CAV 2024): the lexicographic order induced by any
lexicographic relational ranking is well-founded. Proof by induction on the
number of components: the first component ranges over `Finset α` with
strict subset (well-founded), the tail is well-founded by the induction
hypothesis, and the lexicographic product of well-founded orders is
well-founded. -/
theorem lex_less_wellFounded {σ : Type u} {α : Type v} :
    ∀ (n : Nat) (δs : Fin n → σ → Finset α),
      WellFounded (fun s₁ s₂ : σ => LexLess δs s₁ s₂)
  | 0, _δs => by
      -- no components: the order is empty
      refine ⟨fun s => Acc.intro s ?_⟩
      intro t ht
      rcases ht with ⟨i, _⟩
      exact Fin.elim0 i
  | n + 1, δs => by
      let first : σ → Finset α := fun s => δs 0 s
      let tail : Fin n → σ → Finset α := fun i s => δs i.succ s
      have htail : WellFounded (fun s₁ s₂ : σ => LexLess tail s₁ s₂) :=
        lex_less_wellFounded n tail
      have hprod : WellFounded (Prod.Lex (LT.lt : Finset α → Finset α → Prop)
          (fun s₁ s₂ : σ => LexLess tail s₁ s₂)) :=
        WellFounded.prod_lex Finset.wellFoundedLT.wf htail
      -- map states to (first component, state): `LexLess` embeds into the
      -- product order, so it inherits well-foundedness
      refine WellFounded.mono (InvImage.wf (fun s : σ => (first s, s)) hprod) ?_
      intro s₁ s₂ hlex
      rcases hlex with ⟨i, hsame, hdiff⟩
      have i_cases : i = 0 ∨ ∃ k : Fin n, i = k.succ :=
        Fin.cases (motive := fun j : Fin (n + 1) => j = 0 ∨ ∃ k : Fin n, j = k.succ)
          (Or.inl rfl) (fun k => Or.inr ⟨k, rfl⟩) i
      rcases i_cases with rfl | ⟨k, rfl⟩
      · -- the differing component is the first one
        change Prod.Lex LT.lt (fun x y : σ => LexLess tail x y) (δs 0 s₁, s₁) (δs 0 s₂, s₂)
        exact Prod.Lex.left s₁ s₂ hdiff
      · -- the differing component is in the tail
        -- the first component agrees, so only the tail matters
        have hfirst : first s₁ = first s₂ := by
          have h0 := hsame 0 (by simp)
          simpa [first] using h0
        have htaillex : LexLess tail s₁ s₂ := by
          refine ⟨k, ?_, ?_⟩
          · intro j' hj'
            have h := hsame j'.succ (by
              simpa using (Nat.succ_lt_succ hj'))
            simpa [tail] using h
          · simpa [tail] using hdiff
        change Prod.Lex LT.lt (fun x y : σ => LexLess tail x y) (first s₁, s₁) (first s₂, s₂)
        rw [← hfirst]
        exact Prod.Lex.right (first s₁) htaillex

end Tla
