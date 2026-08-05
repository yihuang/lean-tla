import TlaDsl.Rules
import Mathlib.Data.Set.Card
import Mathlib.Order.WellFounded
import Mathlib.Order.PiLex

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
* `eventually_unfold`/`eventually_imp` — the `◇` tableau axioms used when
  chaining response properties;
* `relational_ranking_rule_leadsTo` — Rule 7: the chaining variant whose
  premises carry `◇q` instead of `q` and whose justice condition `r` is a
  parameter supplied by a `D4` premise (while `φ` holds, `r` eventually
  fires) instead of a global `□◇⟨r⟩`; this is how response properties are
  proved from other response properties;
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

/-- Finset-valued conservation: a step adds no element (`δ s' ⊆ δ s`). -/
def ConservesFinset {σ : Type u} {α : Type v} (δ : σ → Finset α) (s s' : σ) : Prop :=
  δ s' ⊆ δ s

/-- Finset-valued reduction: a step removes at least one element. -/
def ReducesFinset {σ : Type u} {α : Type v} (δ : σ → Finset α) (s s' : σ) : Prop :=
  ∃ x, x ∈ δ s ∧ x ∉ δ s'

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

/-! ## The `◇` tableau axioms -/

/-- The `◇` tableau axiom: `◇F` at a suffix is `F` now, or `◇F` at the next
suffix. This is the fact that lets rule premises mentioning `◇q` be chained
propositionally (the paper's §3.2). -/
theorem eventually_unfold {σ : Type u} (F : Pred σ) (e : Behavior σ) (k : Nat) :
    eventually F (e.drop k) ↔ F (e.drop k) ∨ eventually F (e.drop (k + 1)) := by
  constructor
  · rintro ⟨m, hm⟩
    cases m with
    | zero =>
        left
        simpa [Cslib.ωSequence.drop] using hm
    | succ m =>
        right
        refine ⟨m, ?_⟩
        simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm
  · rintro (h | ⟨m, hm⟩)
    · exact ⟨0, h⟩
    · refine ⟨m + 1, ?_⟩
      simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm

/-- `F` now implies `◇F` (the trivial tableau axiom). -/
theorem eventually_imp {σ : Type u} (F : Pred σ) (e : Behavior σ) (k : Nat) :
    F (e.drop k) → eventually F (e.drop k) := fun h => ⟨0, by simpa using h⟩

/-! ## Rule 7: the chaining (relational reactivity) rule -/

/-- The chaining variant of the relational reactivity rule (Rule 7 in the
paper). The premises carry the eventual `◇q` instead of `q`, and the
justice condition `r` is a rule parameter supplied by `D4` (while `φ`
holds, `r` eventually fires — unless `q` is reached) instead of a global
`□◇⟨r⟩` assumption. This is what allows response properties to be proved
from other response properties (the cascaded-queue example): `D3` is
discharged by a lemma `φ ∧ r ⇒ ◇q`, and the `◇q`s are manipulated with the
tableau axioms. Soundness is the same finite descent as Rule 6, with
`◇q`-branches lifted along suffixes. -/
theorem relational_ranking_rule_leadsTo {σ : Type u} {α : Type v} (p q : StatePred σ)
    (r : Action σ) (φ : StatePred σ) (δ R : σ → α → Prop) (H : Pred σ)
    (hR : ∀ e : Behavior σ, ∀ n : Nat, Set.Finite {x : α | R (e n) x})
    (hD1 : ∀ e : Behavior σ, H e → ∀ k : Nat, p (e k) →
      eventually (statePred q) (e.drop k) ∨ (φ (e k) ∧ ∀ x, δ (e k) x → R (e k) x))
    (hD2 : ∀ e : Behavior σ, H e → ∀ k : Nat, φ (e k) →
      eventually (statePred q) (e.drop k) ∨
        (φ (e (k + 1)) ∧ Conserves δ (e k) (e (k + 1))))
    (hD3 : ∀ e : Behavior σ, H e → ∀ k : Nat, φ (e k) → r (e k) (e (k + 1)) →
      eventually (statePred q) (e.drop k) ∨ Reduces δ (e k) (e (k + 1)))
    (hD4 : ∀ e : Behavior σ, H e → ∀ k : Nat, φ (e k) →
      eventually (statePred q) (e.drop k) ∨ eventually (actionPred r) (e.drop k)) :
    Entails H (leadsTo (statePred p) (statePred q)) := by
  intro e hH k hp
  have hp' : p (e k) := by
    simpa [statePred, Cslib.ωSequence.drop, Nat.add_comm] using hp
  have hmain : ∀ n : Nat, ∀ k : Nat,
      Set.Finite {x | δ (e k) x} → ({x | δ (e k) x}).ncard ≤ n → φ (e k) →
      eventually (statePred q) (e.drop k) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih k hfin hn hφk
    rcases hD4 e hH k hφk with hevq | hevr
    · exact hevq
    · rcases hevr with ⟨m, hm⟩
      have hr : r (e (k + m)) (e (k + m + 1)) := by
        simpa [actionPred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm
      have hwalk : ∀ d : Nat, d ≤ m → eventually (statePred q) (e.drop k) ∨
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
              have hd2 := hD2 e hH (k + d) hφd
              rcases hd2 with hevq' | hrest'
              · left
                rcases hevq' with ⟨t0, ht0⟩
                refine ⟨d + t0, ?_⟩
                simpa [statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
                  Nat.add_left_comm] using ht0
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
        have hd3 := hD3 e hH (k + m) hφm hr
        rcases hd3 with hevq' | hred
        · rcases hevq' with ⟨t0, ht0⟩
          refine ⟨m + t0, ?_⟩
          simpa [statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using ht0
        · rcases hred with ⟨x0, hx0in, hx0out⟩
          have hd2m := hD2 e hH (k + m) hφm
          rcases hd2m with hevq'' | hrest'
          · rcases hevq'' with ⟨t0, ht0⟩
            refine ⟨m + t0, ?_⟩
            simpa [statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using ht0
          · rcases hrest' with ⟨hφm1, hconsm⟩
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
            have hev' : eventually (statePred q) ((e.drop k).drop (m + 1)) := by
              simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                ih ({x | δ (e (k + m + 1)) x}).ncard hn' (k + m + 1) hfinm1 le_rfl hφm1
            rcases hev' with ⟨t0, ht0⟩
            refine ⟨m + 1 + t0, ?_⟩
            simpa [statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using ht0
  rcases hD1 e hH k hp' with hevq | hrest
  · exact hevq
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

/-! ## Rule 10: lexicographic relational rankings with stable schedulers -/

/-- `pre_i(ψ)`: ranking component `i` is *preempted* when some
higher-priority scheduler is on. -/
def Pre {σ : Type u} {n : Nat} (ψs : Fin n → σ → Prop) (i : Fin n) (s : σ) : Prop :=
  ∃ j : Fin n, j.val < i.val ∧ ψs j s

/-- `req_i(ψ)`: ranking component `i` is *required* when it is scheduled
and not preempted. -/
def Req {σ : Type u} {n : Nat} (ψs : Fin n → σ → Prop) (i : Fin n) (s : σ) : Prop :=
  ψs i s ∧ ¬ Pre ψs i s

/-- The monotone lexicographic order on `Fin n → ℕ` vectors (component
cardinalities): `x` is below `y` when at some index `i` we have `x i < y i`
and all higher-priority components are non-increasing (`x j ≤ y j` for
`j < i`). This is the order the Rule-10 descent produces: a preempted
lower-priority component may grow, and only the first component that
changes is required to strictly shrink. -/
def VecLexLess {n : Nat} (x y : Fin n → Nat) : Prop :=
  ∃ i : Fin n, (∀ j : Fin n, j.val < i.val → x j ≤ y j) ∧ x i < y i

/-- The strict lexicographic order on `Fin n → ℕ` (first differing
component strictly smaller, earlier components equal) is well-founded:
induction on `n`, splitting the head component off with
`WellFounded.prod_lex`. -/
theorem piLexNat_wellFounded : ∀ (n : Nat),
    WellFounded (Pi.Lex (· < ·) (· < ·) : (Fin n → Nat) → (Fin n → Nat) → Prop)
  | 0 => by
      refine ⟨fun x => Acc.intro x ?_⟩
      intro y hy
      rcases hy with ⟨i, _⟩
      exact Fin.elim0 i
  | n + 1 => by
      let first : (Fin (n + 1) → Nat) → Nat := fun x => x 0
      let tail : (Fin (n + 1) → Nat) → Fin n → Nat := fun x i => x i.succ
      have htail : WellFounded (Pi.Lex (· < ·) (· < ·) :
          (Fin n → Nat) → (Fin n → Nat) → Prop) :=
        piLexNat_wellFounded n
      have hprod : WellFounded (Prod.Lex (fun a b : Nat => a < b)
          (fun x y : Fin n → Nat => Pi.Lex (· < ·) (· < ·) x y)) :=
        WellFounded.prod_lex Nat.lt_wfRel.wf htail
      refine WellFounded.mono (InvImage.wf (fun x : Fin (n + 1) → Nat => (first x, tail x)) hprod) ?_
      intro x y hlex
      rcases hlex with ⟨i, hsame, hlt⟩
      have i_cases : i = 0 ∨ ∃ k : Fin n, i = k.succ :=
        Fin.cases (motive := fun j : Fin (n + 1) => j = 0 ∨ ∃ k : Fin n, j = k.succ)
          (Or.inl rfl) (fun k => Or.inr ⟨k, rfl⟩) i
      rcases i_cases with rfl | ⟨k, rfl⟩
      · -- the head component strictly decreases
        change Prod.Lex (fun a b : Nat => a < b)
          (fun x y : Fin n → Nat => Pi.Lex (· < ·) (· < ·) x y) (first x, tail x) (first y, tail y)
        exact Prod.Lex.left (tail x) (tail y) hlt
      · -- the head agrees and the tail lex-decreases
        have hfirst : first x = first y := by
          have h0 := hsame 0 (by simp)
          simpa [first] using h0
        have htaillex : Pi.Lex (· < ·) (· < ·) (tail x) (tail y) := by
          refine ⟨k, ?_, ?_⟩
          · intro j' hj'
            have h := hsame j'.succ (by
              simpa using (Nat.succ_lt_succ hj'))
            simpa [tail] using h
          · simpa [tail] using hlt
        change Prod.Lex (fun a b : Nat => a < b)
          (fun x y : Fin n → Nat => Pi.Lex (· < ·) (· < ·) x y) (first x, tail x) (first y, tail y)
        rw [← hfirst]
        exact Prod.Lex.right (first x) htaillex

/-- `VecLexLess` embeds into the strict lexicographic order: take the least
index `j₀` where the vectors differ; at `j₀` the value strictly decreases
(it is non-increasing by the monotone condition) and all earlier components
are equal. -/
theorem vecLexLess_imp_piLex {n : Nat} {x y : Fin n → Nat} (h : VecLexLess x y) :
    Pi.Lex (· < ·) (· < ·) x y := by
  rcases h with ⟨i, hle, hlt⟩
  let D : Finset (Fin n) := Finset.univ.filter (fun j => x j < y j)
  have hD : D.Nonempty := ⟨i, by simp [D, hlt]⟩
  let j0 : Fin n := D.min' hD
  refine ⟨j0, ?_, ?_⟩
  · intro j hj
    have hjD : j ∉ D := by
      intro hjD
      have hlej : j0 ≤ j := (Finset.isLeast_min' D hD).2 hjD
      exact (not_lt_of_ge hlej) hj
    have hxjy : ¬ x j < y j := by simpa [D] using hjD
    have hle' : x j ≤ y j := hle j (by
      have hleji : j0 ≤ i := (Finset.isLeast_min' D hD).2 (by simp [D, hlt])
      exact lt_of_lt_of_le hj hleji)
    exact le_antisymm hle' (not_lt.mp hxjy)
  · simpa [D] using D.min'_mem hD

/-- The monotone lexicographic order on component-cardinality vectors is
well-founded (the paper's Theorem 1 in the form the Rule-10 descent
produces). -/
theorem vecLexLess_wellFounded : ∀ (n : Nat), WellFounded (@VecLexLess n) := by
  intro n
  exact WellFounded.mono (piLexNat_wellFounded n) (fun x y h => vecLexLess_imp_piLex h)

/-- Rule 10 (paper): lexicographic relational rankings with stable
schedulers. With `n` ranking components `δs i` (finite sets), scheduler
predicates `ψs i` and justice actions `rs i`:

* S1: `p` implies `◇q` or the invariant `φ`;
* L2: while `φ` holds, every step either reaches `◇q` or keeps `φ`, and
  (a) un-preempted components are conserved, (b) a required component is
  reduced when its justice action fires, (c) required schedulers are stable
  until their justice fires;
* S3: a scheduled justice action eventually fires (unless `q` is reached);
* S4: at least one scheduler is always on (unless `q` is reached);

then `p` leads to `q` under `H`. Soundness: from any `φ`-state, the least
index ever scheduled is required forever, so every higher-priority
component is conserved and that component strictly shrinks when its justice
fires; the cardinality vector therefore strictly descends in `VecLexLess`,
and well-founded induction on that order terminates. -/
theorem rel_rank_lex {σ : Type u} {α : Type v} {n : Nat} (p q : StatePred σ)
    (φ : StatePred σ) (δs : Fin n → σ → Finset α)
    (ψs : Fin n → σ → Prop) (rs : Fin n → Action σ) (H : Pred σ)
    (hS1 : ∀ e : Behavior σ, H e → ∀ k : Nat, p (e k) →
      eventually (statePred q) (e.drop k) ∨ φ (e k))
    (hL2 : ∀ e : Behavior σ, H e → ∀ k : Nat, φ (e k) →
      eventually (statePred q) (e.drop k) ∨
        (φ (e (k + 1)) ∧
         (∀ i : Fin n, ¬ Pre ψs i (e k) → ConservesFinset (δs i) (e k) (e (k + 1))) ∧
         (∀ i : Fin n, Req ψs i (e k) → rs i (e k) (e (k + 1)) →
           ReducesFinset (δs i) (e k) (e (k + 1))) ∧
         (∀ i : Fin n, Req ψs i (e k) → ¬ rs i (e k) (e (k + 1)) → ψs i (e (k + 1)))))
    (hS3 : ∀ e : Behavior σ, H e → ∀ k : Nat, φ (e k) → ∀ i : Fin n, ψs i (e k) →
      eventually (statePred q) (e.drop k) ∨ eventually (actionPred (rs i)) (e.drop k))
    (hS4 : ∀ e : Behavior σ, H e → ∀ k : Nat, φ (e k) →
      eventually (statePred q) (e.drop k) ∨ ∃ i : Fin n, ψs i (e k)) :
    Entails H (leadsTo (statePred p) (statePred q)) := by
  intro e hH k hp
  have hp' : p (e k) := by
    simpa [statePred, Cslib.ωSequence.drop, Nat.add_comm] using hp
  rcases hS1 e hH k hp' with hevq | hφk
  · exact hevq
  · have hwf : WellFounded (@VecLexLess n) := vecLexLess_wellFounded n
    have hmain : ∀ (v : Fin n → Nat) (k : Nat), φ (e k) →
        (∀ i, (δs i (e k)).card ≤ v i) → eventually (statePred q) (e.drop k) := by
      intro v
      refine WellFounded.induction (C := fun v => ∀ k : Nat, φ (e k) →
          (∀ i, (δs i (e k)).card ≤ v i) → eventually (statePred q) (e.drop k)) hwf v ?_
      intro v ih k hφk hv
      by_cases hevq : eventually (statePred q) (e.drop k)
      · exact hevq
      · -- `q` never occurs from `k`: build the descent stretch
        have hnot : ¬ eventually (statePred q) (e.drop k) := hevq
        have hlift : ∀ (t : Nat), eventually (statePred q) (e.drop (k + t)) → False := by
          intro t h
          exact hnot (by
            rcases h with ⟨j, hj⟩
            refine ⟨t + j, ?_⟩
            simpa [statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using hj)
        rcases hS4 e hH k hφk with hevq' | ⟨i0, hi0⟩
        · exact hevq'
        · -- the least index ever scheduled
          let _inst : DecidablePred (fun i : Fin n => ∃ m : Nat, ψs i (e (k + m))) :=
            Classical.decPred _
          let Sched : Finset (Fin n) := Finset.univ.filter (fun i => ∃ m : Nat, ψs i (e (k + m)))
          have hS : Sched.Nonempty := ⟨i0, by
            simp [Sched]
            exact ⟨0, hi0⟩⟩
          let l : Fin n := Sched.min' hS
          have hlmem : ∃ m : Nat, ψs l (e (k + m)) := by
            simpa [Sched] using Sched.min'_mem hS
          rcases hlmem with ⟨m0, hψlm0⟩
          -- no smaller index is ever scheduled
          have hminimal : ∀ (j : Fin n), j.val < l.val → ∀ t : Nat, ¬ ψs j (e (k + t)) := by
            intro j hj t hψ
            have hjS : j ∈ Sched := by
              simp [Sched]
              exact ⟨t, hψ⟩
            have hle : l ≤ j := (Finset.isLeast_min' Sched hS).2 hjS
            exact (not_lt_of_ge hle) hj
          -- preemption is never active at or below `l`
          have hnotpre : ∀ (i : Fin n), i.val ≤ l.val → ∀ t : Nat, ¬ Pre ψs i (e (k + t)) := by
            intro i hi t hpre
            rcases hpre with ⟨j, hj, hψj⟩
            exact hminimal j (lt_of_lt_of_le hj hi) t hψj
          -- walk A: `φ` persists from `k` to `k + m0`
          have hwalkA : ∀ t, t ≤ m0 → φ (e (k + t)) := by
            intro t
            induction t with
            | zero =>
                intro ht
                simpa using hφk
            | succ t ih =>
                intro ht
                have hφt : φ (e (k + t)) := ih (by omega)
                rcases hL2 e hH (k + t) hφt with hevq' | hrest
                · exact False.elim (hlift t hevq')
                · simpa [Nat.add_assoc] using hrest.1
          have hφm0 : φ (e (k + m0)) := hwalkA m0 le_rfl
          -- S3: the least-ever-scheduled justice eventually fires
          rcases hS3 e hH (k + m0) hφm0 l hψlm0 with hevq' | hrl
          · exact False.elim (hlift m0 hevq')
          · -- the first firing after `m0`
            let pj : Nat → Prop := fun j => rs l (e (k + m0 + j)) (e (k + m0 + j + 1))
            have hrl' : ∃ j, pj j := by
              rcases hrl with ⟨j, hj⟩
              refine ⟨j, ?_⟩
              simpa [pj, actionPred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using hj
            let _instpj : DecidablePred pj := Classical.decPred _
            let j0 : Nat := Nat.find hrl'
            have hfires : pj j0 := Nat.find_spec (p := pj) (H := hrl')
            have hfire : rs l (e (k + m0 + j0)) (e (k + m0 + j0 + 1)) := hfires
            have hfirst : ∀ j, j < j0 → ¬ pj j := fun j hj => Nat.find_min (p := pj) (H := hrl') hj
            -- walk B: `φ` persists and every component `≤ l` keeps its
            -- cardinality bounded by the start value, from `k` to
            -- `k + m0 + j0 + 1`
            have hwalkB : ∀ t, t ≤ m0 + j0 + 1 →
                φ (e (k + t)) ∧ ∀ i : Fin n, i.val ≤ l.val →
                  (δs i (e (k + t))).card ≤ (δs i (e k)).card := by
              intro t
              induction t with
              | zero =>
                  intro ht
                  constructor
                  · simpa using hφk
                  · intro i hi
                    exact le_rfl
              | succ t ih =>
                  intro ht
                  have hφt : φ (e (k + t)) := (ih (by omega)).1
                  rcases hL2 e hH (k + t) hφt with hevq' | hrest
                  · exact False.elim (hlift t hevq')
                  · constructor
                    · simpa [Nat.add_assoc] using hrest.1
                    · intro i hi
                      have hcons : ConservesFinset (δs i) (e (k + t)) (e (k + t + 1)) :=
                        hrest.2.1 i (hnotpre i hi t)
                      have hle1 : (δs i (e (k + t + 1))).card ≤ (δs i (e (k + t))).card :=
                        Finset.card_le_card hcons
                      simpa [Nat.add_assoc] using le_trans hle1 ((ih (by omega)).2 i hi)
            -- walk C: `φ` and `ψ_l` persist from `k + m0` to `k + m0 + j0`
            -- (stability of the required scheduler)
            have hwalkC : ∀ t, t ≤ j0 → φ (e (k + m0 + t)) ∧ ψs l (e (k + m0 + t)) := by
              intro t
              induction t with
              | zero =>
                  intro ht
                  constructor
                  · exact (hwalkB m0 (by omega)).1
                  · exact hψlm0
              | succ t ih =>
                  intro ht
                  have hφt : φ (e (k + m0 + t)) := (ih (by omega)).1
                  have hψt : ψs l (e (k + m0 + t)) := (ih (by omega)).2
                  have hreqt : Req ψs l (e (k + m0 + t)) :=
                    ⟨hψt, by simpa [Nat.add_assoc] using hnotpre l le_rfl (m0 + t)⟩
                  have hnr : ¬ rs l (e (k + m0 + t)) (e (k + m0 + t + 1)) :=
                    hfirst t (by omega)
                  rcases hL2 e hH (k + m0 + t) hφt with hevq' | hrest
                  · exact False.elim (hlift (m0 + t) (by simpa [Nat.add_assoc] using hevq'))
                  · constructor
                    · simpa [Nat.add_assoc] using hrest.1
                    · simpa [Nat.add_assoc] using hrest.2.2.2 l hreqt hnr
            -- at the firing step: the required component strictly shrinks
            have hφk'' : φ (e (k + m0 + j0)) := (hwalkC j0 le_rfl).1
            have hψk'' : ψs l (e (k + m0 + j0)) := (hwalkC j0 le_rfl).2
            have hreqk'' : Req ψs l (e (k + m0 + j0)) :=
              ⟨hψk'', by simpa [Nat.add_assoc] using hnotpre l le_rfl (m0 + j0)⟩
            rcases hL2 e hH (k + m0 + j0) hφk'' with hevq' | hrest
            · exact False.elim (hlift (m0 + j0) (by simpa [Nat.add_assoc] using hevq'))
            · have hφnext : φ (e (k + m0 + j0 + 1)) := hrest.1
              have hred : ReducesFinset (δs l) (e (k + m0 + j0)) (e (k + m0 + j0 + 1)) :=
                hrest.2.2.1 l hreqk'' hfire
              -- the cardinality vector at the end is lex-below the one at `k`
              have hlex : VecLexLess (fun i => (δs i (e (k + m0 + j0 + 1))).card)
                  v := by
                refine ⟨l, ?_, ?_⟩
                · intro j hj
                  have h1 : (δs j (e (k + m0 + j0 + 1))).card ≤ (δs j (e k)).card := by
                    simpa [Nat.add_assoc] using (hwalkB (m0 + j0 + 1) le_rfl).2 j (le_of_lt hj)
                  exact le_trans h1 (hv j)
                · rcases hred with ⟨x0, hx0in, hx0out⟩
                  have hcons : ConservesFinset (δs l) (e (k + m0 + j0)) (e (k + m0 + j0 + 1)) :=
                    hrest.2.1 l (by simpa [Nat.add_assoc] using hnotpre l le_rfl (m0 + j0))
                  have hssub : δs l (e (k + m0 + j0 + 1)) ⊂ δs l (e (k + m0 + j0)) := by
                    constructor
                    · exact hcons
                    · intro hsup
                      exact hx0out (hsup hx0in)
                  have hnlt : (δs l (e (k + m0 + j0 + 1))).card <
                      (δs l (e (k + m0 + j0))).card :=
                    Finset.card_lt_card hssub
                  have hchainl : (δs l (e (k + m0 + j0))).card ≤ (δs l (e k)).card := by
                    simpa [Nat.add_assoc] using (hwalkB (m0 + j0) (by omega)).2 l le_rfl
                  exact lt_of_lt_of_le hnlt (le_trans hchainl (hv l))
              -- well-founded induction at the strictly smaller vector
              have hev' : eventually (statePred q) ((e.drop k).drop (m0 + j0 + 1)) := by
                simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                  ih (fun i => (δs i (e (k + m0 + j0 + 1))).card) hlex (k + m0 + j0 + 1) hφnext
                    (fun i => le_rfl)
              rcases hev' with ⟨t0, ht0⟩
              refine ⟨m0 + j0 + 1 + t0, ?_⟩
              simpa [statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using ht0
    exact hmain (fun i => (δs i (e k)).card) k hφk (fun i => le_rfl)

end Tla
