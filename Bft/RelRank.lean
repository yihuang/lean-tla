import Bft.Core
import Bft.Rules
import Mathlib.Data.Set.Card
import Mathlib.Order.WellFounded
import Mathlib.Order.PiLex

/-!
# Bft.RelRank — the relational-ranking liveness engine (McMillan CAV 2024)

Engine design (docs/bft-design.md §3):

1. **Rules as certificates**: `RelRankCert` packages all the witnesses of
   one Rule 6 application (φ, δ, R, r, and the obligation proofs) into an
   object that can be stored, composed, and printed;
2. **Combinators**: `RelRankCert.trans` (Rule 7 chaining) composes two
   certificates into one; the lexicographic/parameterized combinators
   (Rule 10/11) are given the same way (`LexRankCert`);
3. **Obligation shapes**: C1–C3 are all single-step safety-like properties,
   discharged automatically by the tactic layer (the obligation normalizer
   in `Bft/Obligation.lean` + grind).

The pointwise normal form of `drop` is a definitional equation in `Core`,
so the descent proofs contain no suffix-rewrite chains.
-/

namespace Bft

/-! ## Conserve / Reduce -/

/-- One step conserves `δ`: no new elements. -/
def Conserves {σ : Type u} {α : Type v} (δ : σ → α → Prop) (s s' : σ) : Prop :=
  ∀ x, δ s' x → δ s x

/-- One step reduces `δ`: at least one element removed. -/
def Reduces {σ : Type u} {α : Type v} (δ : σ → α → Prop) (s s' : σ) : Prop :=
  ∃ x, δ s x ∧ ¬ δ s' x

/-! ## Rule 5: finiteness by induction -/

/-- If `R` starts empty and gains only finitely many elements per step,
then `R` is finite at every finite time. -/
theorem finite_rank {σ : Type u} {α : Type v} (R : σ → α → Prop) (e : Behavior σ)
    (h0 : ∀ x, ¬ R (e 0) x)
    (hstep : ∀ n : ℕ, Set.Finite {x : α | R (e (n + 1)) x ∧ ¬ R (e n) x}) :
    ∀ n : ℕ, Set.Finite {x : α | R (e n) x} := by
  intro n
  induction n with
  | zero =>
      refine Set.Finite.subset (s := (∅ : Set α)) Set.finite_empty ?_
      intro x hx; exact (h0 x) hx
  | succ n ih =>
      have hsub : {x | R (e (n + 1)) x} ⊆
          {x | R (e n) x} ∪ {x | R (e (n + 1)) x ∧ ¬ R (e n) x} := by
        intro x hx
        by_cases h : R (e n) x
        · exact Or.inl h
        · exact Or.inr ⟨hx, h⟩
      exact (Set.Finite.union ih (hstep n)).subset hsub

/-! ## The three descent helpers -/

/-- conserve + reduce + finite ⇒ cardinality strictly decreases. -/
theorem ncard_decrease {σ : Type u} {α : Type v} (δ : σ → α → Prop) {s s' : σ}
    (hcons : Conserves δ s s') (hred : Reduces δ s s')
    (hfin : Set.Finite {x | δ s x}) :
    ({x | δ s' x}).ncard < ({x | δ s x}).ncard := by
  have hssub : {x | δ s' x} ⊂ {x | δ s x} := by
    constructor
    · exact hcons
    · intro hsup
      rcases hred with ⟨x, hx, hx'⟩
      exact hx' (hsup hx)
  exact Set.ncard_lt_ncard hssub hfin

/-- The walk: while `φ` holds, either `q` is reached first, or `φ` persists,
`δ` is conserved step by step, and stays within the starting envelope. -/
theorem rank_persist {σ : Type u} {α : Type v} (q : StatePred σ) (φ : StatePred σ)
    (δ : σ → α → Prop) (e : Behavior σ)
    (hD2 : ∀ k : ℕ, φ (e k) →
      (∃ m, q (e (k + m))) ∨ (φ (e (k + 1)) ∧ Conserves δ (e k) (e (k + 1))))
    (k m : ℕ) (hφk : φ (e k)) :
    (∃ t, q (e (k + t))) ∨
      (φ (e (k + m)) ∧
       (∀ d : ℕ, d < m → Conserves δ (e (k + d)) (e (k + d + 1))) ∧
       {x | δ (e (k + m)) x} ⊆ {x | δ (e k) x}) := by
  induction m with
  | zero =>
      exact Or.inr ⟨hφk, fun d hd => absurd hd (Nat.not_lt_zero d),
        fun _ hx => hx⟩
  | succ m ih =>
      rcases ih with hev | ⟨hφm, hcons, hsubm⟩
      · exact Or.inl hev
      · rcases hD2 (k + m) hφm with hev' | ⟨hφm1, hconsm⟩
        · rcases hev' with ⟨t, ht⟩
          exact Or.inl ⟨m + t, by simpa [Nat.add_assoc] using ht⟩
        · refine Or.inr ⟨by simpa [Nat.add_assoc] using hφm1, fun d hd => ?_, fun x hx => ?_⟩
          · by_cases h : d = m
            · subst h; exact hconsm
            · exact hcons d (by omega)
          · exact hsubm (hconsm x (by rwa [← Nat.add_assoc] at hx))

/-- The soundness core: finite descent of `|δ|`. -/
theorem rank_descent {σ : Type u} {α : Type v} (q : StatePred σ) (r : Action σ)
    (φ : StatePred σ) (δ R : σ → α → Prop) (e : Behavior σ) (k : ℕ)
    (hR : ∀ n : ℕ, Set.Finite {x : α | R (e n) x})
    (hD1 : (∃ m, q (e (k + m))) ∨ (φ (e k) ∧ ∀ x, δ (e k) x → R (e k) x))
    (hD2 : ∀ j : ℕ, φ (e j) →
      (∃ m, q (e (j + m))) ∨ (φ (e (j + 1)) ∧ Conserves δ (e j) (e (j + 1))))
    (hD3 : ∀ j : ℕ, φ (e j) → r (e j) (e (j + 1)) →
      (∃ m, q (e (j + m))) ∨ Reduces δ (e j) (e (j + 1)))
    (hD4 : ∀ j : ℕ, φ (e j) →
      (∃ m, q (e (j + m))) ∨ (∃ m, r (e (j + m)) (e (j + m + 1)))) :
    ∃ m, q (e (k + m)) := by
  rcases hD1 with hevq | ⟨hφk, hδR⟩
  · exact hevq
  · have hfin : Set.Finite {x | δ (e k) x} := (hR k).subset hδR
    suffices hmain : ∀ n : ℕ, ∀ k : ℕ, Set.Finite {x | δ (e k) x} →
        ({x | δ (e k) x}).ncard ≤ n → φ (e k) → ∃ m, q (e (k + m)) by
      exact hmain ({x | δ (e k) x}).ncard k hfin le_rfl hφk
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih k hfin hn hφk
    rcases hD4 k hφk with hevq | ⟨m, hm⟩
    · exact hevq
    · rcases rank_persist q φ δ e hD2 k m hφk with hevq | ⟨hφm, _hcons, hsubm⟩
      · exact hevq
      · rcases hD3 (k + m) hφm (by rwa [Nat.add_assoc] at hm ⊢)
          with hevq | hred
        · rcases hevq with ⟨t, ht⟩
          exact ⟨m + t, by simpa [Nat.add_assoc] using ht⟩
        · rcases hD2 (k + m) hφm with hevq | ⟨hφm1, hconsm⟩
          · rcases hevq with ⟨t, ht⟩
            exact ⟨m + t, by simpa [Nat.add_assoc] using ht⟩
          · have hn' : ({x | δ (e (k + m + 1)) x}).ncard < n :=
              lt_of_lt_of_le
                (ncard_decrease δ hconsm hred (hfin.subset hsubm))
                (le_trans (Set.ncard_le_ncard hsubm hfin) hn)
            have hfin' : Set.Finite {x | δ (e (k + m + 1)) x} :=
              hfin.subset (fun x hx => hsubm (hconsm x hx))
            have hφm1' : φ (e (k + m + 1)) := by rwa [Nat.add_assoc] at hφm1 ⊢
            rcases ih ({x | δ (e (k + m + 1)) x}).ncard hn' (k + m + 1)
                hfin' le_rfl hφm1' with ⟨t, ht⟩
            exact ⟨m + 1 + t, by simpa [Nat.add_assoc] using ht⟩

/-! ## Rule 6: the relational reactivity rule -/

/-- Rule 6: `p ↝ q` under `H ∧ □◇⟨r⟩`. -/
theorem relational_ranking_rule {σ : Type u} {α : Type v} (p q : StatePred σ)
    (r : Action σ) (φ : StatePred σ) (δ R : σ → α → Prop) (H : Pred σ)
    (hR : ∀ e : Behavior σ, ∀ n : ℕ, Set.Finite {x : α | R (e n) x})
    (hC1 : ∀ e : Behavior σ, H e → ∀ k : ℕ, p (e k) →
      q (e k) ∨ (φ (e k) ∧ ∀ x, δ (e k) x → R (e k) x))
    (hC2 : ∀ e : Behavior σ, H e → ∀ k : ℕ, φ (e k) →
      q (e (k + 1)) ∨ (φ (e (k + 1)) ∧ Conserves δ (e k) (e (k + 1))))
    (hC3 : ∀ e : Behavior σ, H e → ∀ k : ℕ, φ (e k) → r (e k) (e (k + 1)) →
      q (e (k + 1)) ∨ Reduces δ (e k) (e (k + 1))) :
    Entails (tlaAnd H (globalJustice r)) (leadsTo (statePred p) (statePred q)) := by
  intro e h k hpk
  have hpk' : p (e k) := by simpa using hpk
  refine (eventually_statePred_drop q e k).mpr ?_
  apply rank_descent q r φ δ R e k (fun n => hR e n)
  · rcases hC1 e h.1 k hpk' with hq | hφδ
    · exact Or.inl ⟨0, hq⟩
    · exact Or.inr hφδ
  · intro j hφ
    rcases hC2 e h.1 j hφ with hq | h
    · exact Or.inl ⟨1, hq⟩
    · exact Or.inr h
  · intro j hφ hr
    rcases hC3 e h.1 j hφ hr with hq | hred
    · exact Or.inl ⟨1, hq⟩
    · exact Or.inr hred
  · intro j _hφ
    exact Or.inr ((eventually_actionPred_drop r e j).mp (h.2 j))

/-! ## Certificates -/

/-- A Rule 6 certificate: all the witnesses of one liveness proof, in a
storable/composable/printable object. -/
structure RelRankCert (σ : Type u) (p q : StatePred σ) where
  α : Type v
  r : Action σ
  φ : StatePred σ
  δ : σ → α → Prop
  R : σ → α → Prop
  H : Pred σ
  finiteness : ∀ e : Behavior σ, ∀ n : ℕ, Set.Finite {x | R (e n) x}
  c1 : ∀ e : Behavior σ, H e → ∀ k : ℕ, p (e k) →
    q (e k) ∨ (φ (e k) ∧ ∀ x, δ (e k) x → R (e k) x)
  c2 : ∀ e : Behavior σ, H e → ∀ k : ℕ, φ (e k) →
    q (e (k + 1)) ∨ (φ (e (k + 1)) ∧ Conserves δ (e k) (e (k + 1)))
  c3 : ∀ e : Behavior σ, H e → ∀ k : ℕ, φ (e k) → r (e k) (e (k + 1)) →
    q (e (k + 1)) ∨ Reduces δ (e k) (e (k + 1))

/-- A certificate yields its leads-to conclusion. -/
theorem RelRankCert.toLeadsTo {σ : Type u} {p q : StatePred σ}
    (cert : RelRankCert σ p q) :
    Entails (tlaAnd cert.H (globalJustice cert.r))
      (leadsTo (statePred p) (statePred q)) :=
  relational_ranking_rule p q cert.r cert.φ cert.δ cert.R cert.H
    cert.finiteness cert.c1 cert.c2 cert.c3

/-- Rule 7 (chaining): two certificates compose into one leads-to.
Note the obligation premises are relaxed to an eventually form: the second
certificate's conclusion appears in the first certificate's C2/C3 branches
as `∃ m, q (e (· + m))` — exactly the left-disjunct shape of `rank_descent`'s
hD2/hD3, so composition happens at the descent layer with no second
induction. -/
theorem RelRankCert.trans {σ : Type u} {p q q' : StatePred σ}
    (cert₁ : RelRankCert σ p q)
    (cert₂ : RelRankCert σ q q')
    (hH : ∀ e, tlaAnd cert₁.H (globalJustice cert₁.r) e →
      tlaAnd cert₂.H (globalJustice cert₂.r) e) :
    Entails (tlaAnd cert₁.H (globalJustice cert₁.r))
      (leadsTo (statePred p) (statePred q')) := by
  intro e hE k hpk
  -- certificate one: p leads-to q
  have h1 : (leadsTo (statePred p) (statePred q)) e := cert₁.toLeadsTo e hE
  -- certificate two, in the reached environment
  have h2 : (leadsTo (statePred q) (statePred q')) e :=
    cert₂.toLeadsTo e (hH e hE)
  exact (leadsTo_trans (statePred p) (statePred q) (statePred q')) e ⟨h1, h2⟩ k hpk

/-- Rule 11 (disjunction over a family, predicate level): if every member of a
family of state predicates leads to `q` on a behavior, so does their
existential disjunction. -/
theorem leadsTo_exists {σ : Type u} {ι : Type v} {p : ι → StatePred σ}
    {q : StatePred σ} (e : Behavior σ)
    (h : ∀ i, leadsTo (statePred (p i)) (statePred q) e) :
    leadsTo (statePred (fun s => ∃ i, p i s)) (statePred q) e := by
  intro k hpk
  rcases hpk with ⟨i, hi⟩
  exact h i k hi

/-- Rule 11 for certificates: a finite family of certificates that share the
same ambient truth `H` and justice action `r` jointly proves
`(∃ i, p i) ↝ q` under `H ∧ □◇⟨r⟩`. -/
theorem RelRankCert.forall_fin {σ : Type u} {n : ℕ} {p : Fin n → StatePred σ}
    {q : StatePred σ} (H : Pred σ) (r : Action σ)
    (certs : ∀ i : Fin n, RelRankCert σ (p i) q)
    (hsame : ∀ i, (certs i).H = H ∧ (certs i).r = r) :
    Entails (tlaAnd H (globalJustice r))
      (leadsTo (statePred (fun s => ∃ i, p i s)) (statePred q)) := by
  intro e hE
  apply leadsTo_exists
  intro i
  have hcert := (certs i).toLeadsTo e
  rw [(hsame i).1, (hsame i).2] at hcert
  exact hcert hE

/-! ## Rule 10/11: lexicographic and parameterized combinators

The well-foundedness facts (`VecLexLess`, `piLexNat_wellFounded`) are ported
from the machine-checked versions in lean-tla `RelRank.lean`. -/

/-- Monotone lexicographic order: some component strictly decreases while no
higher-priority component increases. -/
def VecLexLess {n : ℕ} (x y : Fin n → ℕ) : Prop :=
  ∃ i : Fin n, (∀ j : Fin n, j.val < i.val → x j ≤ y j) ∧ x i < y i

/-- The strict lexicographic order (first differing component strictly
smaller, earlier components equal) is well-founded: induction on `n`,
peeling off the head component with `WellFounded.prod_lex`.
(Ported from the machine-checked version in TlaDsl/RelRank.lean.) -/
theorem piLexNat_wellFounded : ∀ (n : ℕ),
    WellFounded (Pi.Lex (· < ·) (· < ·) : (Fin n → ℕ) → (Fin n → ℕ) → Prop)
  | 0 => by
      refine ⟨fun x => Acc.intro x ?_⟩
      intro y hy
      rcases hy with ⟨i, _⟩
      exact Fin.elim0 i
  | n + 1 => by
      let first : (Fin (n + 1) → ℕ) → ℕ := fun x => x 0
      let tail : (Fin (n + 1) → ℕ) → Fin n → ℕ := fun x i => x i.succ
      have htail : WellFounded (Pi.Lex (· < ·) (· < ·) :
          (Fin n → ℕ) → (Fin n → ℕ) → Prop) :=
        piLexNat_wellFounded n
      have hprod : WellFounded (Prod.Lex (fun a b : ℕ => a < b)
          (fun x y : Fin n → ℕ => Pi.Lex (· < ·) (· < ·) x y)) :=
        WellFounded.prod_lex Nat.lt_wfRel.wf htail
      refine WellFounded.mono (InvImage.wf (fun x : Fin (n + 1) → ℕ => (first x, tail x)) hprod) ?_
      intro x y hlex
      rcases hlex with ⟨i, hsame, hlt⟩
      have i_cases : i = 0 ∨ ∃ k : Fin n, i = k.succ :=
        Fin.cases (motive := fun j : Fin (n + 1) => j = 0 ∨ ∃ k : Fin n, j = k.succ)
          (Or.inl rfl) (fun k => Or.inr ⟨k, rfl⟩) i
      rcases i_cases with rfl | ⟨k, rfl⟩
      · change Prod.Lex (fun a b : ℕ => a < b)
          (fun x y : Fin n → ℕ => Pi.Lex (· < ·) (· < ·) x y) (first x, tail x) (first y, tail y)
        exact Prod.Lex.left (tail x) (tail y) hlt
      · have hfirst : first x = first y := by
          have h0 := hsame 0 (by simp)
          simpa [first] using h0
        have htaillex : Pi.Lex (· < ·) (· < ·) (tail x) (tail y) := by
          refine ⟨k, ?_, ?_⟩
          · intro j' hj'
            have h := hsame j'.succ (by
              simpa using (Nat.succ_lt_succ hj'))
            simpa [tail] using h
          · simpa [tail] using hlt
        change Prod.Lex (fun a b : ℕ => a < b)
          (fun x y : Fin n → ℕ => Pi.Lex (· < ·) (· < ·) x y) (first x, tail x) (first y, tail y)
        rw [← hfirst]
        exact Prod.Lex.right (first x) htaillex

/-- `VecLexLess` embeds into the strict lexicographic order: take the least
index `j₀` where the vectors differ; it strictly decreases there (the
monotonicity premise gives non-increase), and earlier components are equal. -/
theorem vecLexLess_imp_piLex {n : ℕ} {x y : Fin n → ℕ} (h : VecLexLess x y) :
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

/-- `VecLexLess` is well-founded (Theorem 1). -/
theorem vecLexLess_wellFounded : ∀ (n : ℕ), WellFounded (@VecLexLess n) := by
  intro n
  exact WellFounded.mono (piLexNat_wellFounded n) (fun x y h => vecLexLess_imp_piLex h)

/-- Component `i` is preempted: a higher-priority scheduler is on. -/
def Pre {σ : Type u} {n : ℕ} (ψs : Fin n → σ → Prop) (i : Fin n) (s : σ) : Prop :=
  ∃ j : Fin n, j.val < i.val ∧ ψs j s

/-- Component `i` is required: on and not preempted. -/
def Req {σ : Type u} {n : ℕ} (ψs : Fin n → σ → Prop) (i : Fin n) (s : σ) : Prop :=
  ψs i s ∧ ¬ Pre ψs i s

/-! ### Helpers for `Finset`-valued rankings -/

def ConservesFinset {σ : Type u} {α : Type v} (δ : σ → Finset α) (s s' : σ) : Prop :=
  δ s' ⊆ δ s

def ReducesFinset {σ : Type u} {α : Type v} (δ : σ → Finset α) (s s' : σ) : Prop :=
  ∃ x, x ∈ δ s ∧ x ∉ δ s'

theorem card_le_card_of_conserve {σ : Type u} {α : Type v} (δ : σ → Finset α)
    {s s' : σ} :
    ConservesFinset δ s s' → (δ s').card ≤ (δ s).card :=
  Finset.card_le_card

theorem card_lt_card_of_reduce {σ : Type u} {α : Type v} (δ : σ → Finset α)
    {s s' : σ} :
    ConservesFinset δ s s' → ReducesFinset δ s s' → (δ s').card < (δ s).card := by
  intro hcons hred
  rcases hred with ⟨x0, hx0in, hx0out⟩
  have hssub : δ s' ⊂ δ s := by
    constructor
    · exact hcons
    · intro hsup
      exact hx0out (hsup hx0in)
  exact Finset.card_lt_card hssub

/-- A `◇q` at a later position lifts back to an earlier suffix. -/
theorem eventually_statePred_lift {σ : Type u} (q : StatePred σ) (e : Behavior σ)
    (k t : ℕ) (h : eventually (statePred q) (e.drop (k + t))) :
    eventually (statePred q) (e.drop k) := by
  rw [eventually_statePred_drop] at h ⊢
  rcases h with ⟨m, hm⟩
  exact ⟨t + m, by simpa [Nat.add_assoc] using hm⟩

/-- The L2 step shape (Rule 10 of the paper). -/
def L2Step {σ : Type u} {α : Type v} {n : ℕ} (q : StatePred σ) (φ : StatePred σ)
    (δs : Fin n → σ → Finset α) (ψs : Fin n → σ → Prop) (rs : Fin n → Action σ)
    (e : Behavior σ) (k : ℕ) : Prop :=
  eventually (statePred q) (e.drop k) ∨
    (φ (e (k + 1)) ∧
     (∀ i : Fin n, ¬ Pre ψs i (e k) → ConservesFinset (δs i) (e k) (e (k + 1))) ∧
     (∀ i : Fin n, Req ψs i (e k) → rs i (e k) (e (k + 1)) →
       ReducesFinset (δs i) (e k) (e (k + 1))) ∧
     (∀ i : Fin n, Req ψs i (e k) → ¬ rs i (e k) (e (k + 1)) → ψs i (e (k + 1))))

/-- Walk A+B: under `¬◇q`, L2 preserves `φ` and conserves all non-preempted
components. -/
theorem walk_below {σ : Type u} {α : Type v} {n : ℕ} (q : StatePred σ)
    (φ : StatePred σ)
    (δs : Fin n → σ → Finset α) (ψs : Fin n → σ → Prop) (rs : Fin n → Action σ)
    (e : Behavior σ) (k : ℕ) (l : Fin n)
    (hL2 : ∀ k : ℕ, φ (e k) → L2Step q φ δs ψs rs e k)
    (hnot : ¬ eventually (statePred q) (e.drop k)) (hφk : φ (e k))
    (hnotpre : ∀ i : Fin n, i.val ≤ l.val → ∀ t : ℕ, ¬ Pre ψs i (e (k + t))) :
    ∀ t : ℕ, φ (e (k + t)) ∧
      ∀ i : Fin n, i.val ≤ l.val → (δs i (e (k + t))).card ≤ (δs i (e k)).card := by
  intro t
  induction t with
  | zero =>
      constructor
      · simpa using hφk
      · intro i hi
        exact le_rfl
  | succ t ih =>
      rcases ih with ⟨hφt, hle⟩
      rcases hL2 (k + t) hφt with hevq' | hrest
      · exact False.elim (hnot (eventually_statePred_lift q e k t hevq'))
      · constructor
        · simpa [Nat.add_assoc] using hrest.1
        · intro i hi
          have hcons : ConservesFinset (δs i) (e (k + t)) (e (k + t + 1)) :=
            hrest.2.1 i (hnotpre i hi t)
          have hle1 : (δs i (e (k + t + 1))).card ≤ (δs i (e (k + t))).card :=
            Finset.card_le_card hcons
          simpa [Nat.add_assoc] using le_trans hle1 (hle i hi)

/-- Walk C: while justice has not fired, a required scheduler `ψ_l` persists
until the first firing. -/
theorem sched_persist {σ : Type u} {α : Type v} {n : ℕ} (q : StatePred σ)
    (φ : StatePred σ)
    (δs : Fin n → σ → Finset α) (ψs : Fin n → σ → Prop) (rs : Fin n → Action σ)
    (e : Behavior σ) (k m0 j0 : ℕ) (l : Fin n)
    (hL2 : ∀ k : ℕ, φ (e k) → L2Step q φ δs ψs rs e k)
    (hnot : ¬ eventually (statePred q) (e.drop k))
    (hφm0 : φ (e (k + m0))) (hψm0 : ψs l (e (k + m0)))
    (hnotpre : ∀ t : ℕ, ¬ Pre ψs l (e (k + m0 + t)))
    (hfirst : ∀ j : ℕ, j < j0 → ¬ rs l (e (k + m0 + j)) (e (k + m0 + j + 1))) :
    ∀ t : ℕ, t ≤ j0 → φ (e (k + m0 + t)) ∧ ψs l (e (k + m0 + t)) := by
  intro t
  induction t with
  | zero =>
      intro ht
      constructor
      · simpa [Nat.add_assoc] using hφm0
      · exact hψm0
  | succ t ih =>
      intro ht
      rcases ih (by omega) with ⟨hφt, hψt⟩
      have hreqt : Req ψs l (e (k + m0 + t)) := ⟨hψt, hnotpre t⟩
      have hnr : ¬ rs l (e (k + m0 + t)) (e (k + m0 + t + 1)) := hfirst t (by omega)
      rcases hL2 (k + m0 + t) hφt with hevq' | hrest
      · exact False.elim (hnot (eventually_statePred_lift q e k (m0 + t)
          (by simpa [Nat.add_assoc] using hevq')))
      · constructor
        · simpa [Nat.add_assoc] using hrest.1
        · simpa [Nat.add_assoc] using hrest.2.2.2 l hreqt hnr

/-- The least index ever scheduled from `k`: the minimum over `Fin n`;
smaller indices are never scheduled, so it and everything below it are
never preempted. -/
theorem min_ever_scheduled {σ : Type u} {n : ℕ} (ψs : Fin n → σ → Prop)
    (e : Behavior σ) (k : ℕ) (hS4 : ∃ i0 : Fin n, ψs i0 (e k)) :
    ∃ l : Fin n, (∃ m : ℕ, ψs l (e (k + m))) ∧
      ∀ j : Fin n, j.val < l.val → ∀ t : ℕ, ¬ ψs j (e (k + t)) := by
  classical
  let Sched : Finset (Fin n) := Finset.univ.filter (fun i => ∃ m : ℕ, ψs i (e (k + m)))
  have hS : Sched.Nonempty := by
    rcases hS4 with ⟨i0, hi0⟩
    refine ⟨i0, ?_⟩
    simp [Sched]
    exact ⟨0, hi0⟩
  let l : Fin n := Sched.min' hS
  refine ⟨l, ?_, ?_⟩
  · simpa [Sched, l] using Sched.min'_mem hS
  · intro j hj t hψ
    have hjS : j ∈ Sched := by
      simp [Sched]
      exact ⟨t, hψ⟩
    have hle : l ≤ j := (Finset.isLeast_min' Sched hS).2 hjS
    exact (not_lt_of_ge hle) hj

/-- Rule 10 (of the paper): lexicographic relational ranking + stable
schedulers. Soundness: take the least ever-scheduled index `l`
(`min_ever_scheduled`) — it is never preempted, and higher-priority
components stay conserved and bounded (`walk_below`); its justice
eventually fires (S3), and by stability the first firing strictly shrinks
its component (`sched_persist` + `card_lt_card_of_reduce`); the cardinality
vector strictly decreases in `VecLexLess`, which terminates by
`vecLexLess_wellFounded`.
(Ported from the machine-checked version in TlaDsl/RelRank.lean.) -/
theorem rel_rank_lex {σ : Type u} {α : Type v} {n : ℕ} (p q : StatePred σ)
    (φ : StatePred σ) (δs : Fin n → σ → Finset α)
    (ψs : Fin n → σ → Prop) (rs : Fin n → Action σ) (H : Pred σ)
    (hS1 : ∀ e : Behavior σ, H e → ∀ k : ℕ, p (e k) →
      eventually (statePred q) (e.drop k) ∨ φ (e k))
    (hL2 : ∀ e : Behavior σ, H e → ∀ k : ℕ, φ (e k) → L2Step q φ δs ψs rs e k)
    (hS3 : ∀ e : Behavior σ, H e → ∀ k : ℕ, φ (e k) → ∀ i : Fin n, ψs i (e k) →
      eventually (statePred q) (e.drop k) ∨
        eventually (actionPred (rs i)) (e.drop k))
    (hS4 : ∀ e : Behavior σ, H e → ∀ k : ℕ, φ (e k) →
      eventually (statePred q) (e.drop k) ∨ ∃ i : Fin n, ψs i (e k)) :
    Entails H (leadsTo (statePred p) (statePred q)) := by
  intro e hH k hp
  have hp' : p (e k) := by simpa using hp
  rcases hS1 e hH k hp' with hevq | hφk
  · exact hevq
  · have hwf : WellFounded (@VecLexLess n) := vecLexLess_wellFounded n
    have hmain : ∀ (v : Fin n → ℕ) (k : ℕ), φ (e k) →
        (∀ i, (δs i (e k)).card ≤ v i) → eventually (statePred q) (e.drop k) := by
      intro v
      refine WellFounded.induction (C := fun v => ∀ k : ℕ, φ (e k) →
          (∀ i, (δs i (e k)).card ≤ v i) → eventually (statePred q) (e.drop k)) hwf v ?_
      intro v ih k hφk hv
      classical
      by_cases hevq : eventually (statePred q) (e.drop k)
      · exact hevq
      · have hnot : ¬ eventually (statePred q) (e.drop k) := hevq
        rcases hS4 e hH k hφk with hevq' | ⟨i0, hi0⟩
        · exact False.elim (hnot hevq')
        · rcases min_ever_scheduled ψs e k ⟨i0, hi0⟩ with ⟨l, hlmem, hminimal⟩
          have hnotpre : ∀ (i : Fin n), i.val ≤ l.val → ∀ t : ℕ,
              ¬ Pre ψs i (e (k + t)) := by
            intro i hi t hpre
            rcases hpre with ⟨j, hj, hψj⟩
            exact hminimal j (lt_of_lt_of_le hj hi) t hψj
          have hwalk : ∀ t : ℕ, φ (e (k + t)) ∧
              ∀ i : Fin n, i.val ≤ l.val →
                (δs i (e (k + t))).card ≤ (δs i (e k)).card :=
            walk_below q φ δs ψs rs e k l (hL2 e hH) hnot hφk hnotpre
          rcases hlmem with ⟨m0, hψlm0⟩
          have hφm0 : φ (e (k + m0)) := (hwalk m0).1
          rcases hS3 e hH (k + m0) hφm0 l hψlm0 with hevq' | hrl
          · exact False.elim (hnot (eventually_statePred_lift q e k m0 hevq'))
          · have hrl' : ∃ j : ℕ, rs l (e (k + m0 + j)) (e (k + m0 + j + 1)) := by
              rcases hrl with ⟨j, hj⟩
              refine ⟨j, ?_⟩
              simpa [Nat.add_assoc] using hj
            let j0 : ℕ := Nat.find hrl'
            have hfire : rs l (e (k + m0 + j0)) (e (k + m0 + j0 + 1)) := by
              simpa [j0] using
                (Nat.find_spec (p := fun j => rs l (e (k + m0 + j))
                  (e (k + m0 + j + 1))) hrl')
            have hfirst : ∀ j : ℕ, j < j0 →
                ¬ rs l (e (k + m0 + j)) (e (k + m0 + j + 1)) := by
              intro j hj
              exact Nat.find_min (p := fun j => rs l (e (k + m0 + j))
                (e (k + m0 + j + 1))) hrl' (by simpa [j0] using hj)
            have hpersist : ∀ t : ℕ, t ≤ j0 →
                φ (e (k + m0 + t)) ∧ ψs l (e (k + m0 + t)) :=
              sched_persist q φ δs ψs rs e k m0 j0 l (hL2 e hH) hnot hφm0 hψlm0
                (fun t => by simpa [Nat.add_assoc] using hnotpre l le_rfl (m0 + t))
                hfirst
            have hφk'' : φ (e (k + m0 + j0)) := (hpersist j0 le_rfl).1
            have hψk'' : ψs l (e (k + m0 + j0)) := (hpersist j0 le_rfl).2
            have hreqk'' : Req ψs l (e (k + m0 + j0)) :=
              ⟨hψk'', by simpa [Nat.add_assoc] using hnotpre l le_rfl (m0 + j0)⟩
            rcases hL2 e hH (k + m0 + j0) hφk'' with hevq' | hrest
            · exact False.elim (hnot (eventually_statePred_lift q e k (m0 + j0)
                (by simpa [Nat.add_assoc] using hevq')))
            · have hφnext : φ (e (k + m0 + j0 + 1)) := hrest.1
              have hcons : ConservesFinset (δs l) (e (k + m0 + j0))
                  (e (k + m0 + j0 + 1)) :=
                hrest.2.1 l (by simpa [Nat.add_assoc] using hnotpre l le_rfl (m0 + j0))
              have hred : ReducesFinset (δs l) (e (k + m0 + j0))
                  (e (k + m0 + j0 + 1)) :=
                hrest.2.2.1 l hreqk'' hfire
              have hlex : VecLexLess (fun i => (δs i (e (k + m0 + j0 + 1))).card) v := by
                refine ⟨l, ?_, ?_⟩
                · intro j hj
                  have h1 : (δs j (e (k + m0 + j0 + 1))).card ≤ (δs j (e k)).card := by
                    simpa [Nat.add_assoc] using (hwalk (m0 + j0 + 1)).2 j (le_of_lt hj)
                  exact le_trans h1 (hv j)
                · have hnlt : (δs l (e (k + m0 + j0 + 1))).card <
                      (δs l (e (k + m0 + j0))).card :=
                    card_lt_card_of_reduce (δs l) hcons hred
                  have hchainl : (δs l (e (k + m0 + j0))).card ≤ (δs l (e k)).card := by
                    simpa [Nat.add_assoc] using (hwalk (m0 + j0)).2 l le_rfl
                  exact lt_of_lt_of_le hnlt (le_trans hchainl (hv l))
              have hev' : eventually (statePred q) (e.drop (k + m0 + j0 + 1)) :=
                ih (fun i => (δs i (e (k + m0 + j0 + 1))).card) hlex (k + m0 + j0 + 1)
                  hφnext (fun i => le_rfl)
              exact eventually_statePred_lift q e k (m0 + j0 + 1) (by
                simpa [Nat.add_assoc] using hev')
    exact hmain (fun i => (δs i (e k)).card) k hφk (fun i => le_rfl)

/-- A Rule 10 certificate (lexicographic + stable schedulers): the fields
correspond one-to-one to the paper's L2/P3/P4 premises. -/
structure LexRankCert (σ : Type u) (p q : StatePred σ) where
  n : ℕ
  α : Type v
  rs : Fin n → Action σ
  ψs : Fin n → σ → Prop
  φ : StatePred σ
  δs : Fin n → σ → Finset α
  H : Pred σ
  c1 : ∀ e : Behavior σ, H e → ∀ k : ℕ, p (e k) → q (e k) ∨ φ (e k)
  l2 : ∀ e : Behavior σ, H e → ∀ k : ℕ, φ (e k) →
    (∃ m, q (e (k + m))) ∨
      (φ (e (k + 1)) ∧
       (∀ i : Fin n, ¬ Pre ψs i (e k) →
         ∀ x, x ∈ δs i (e (k + 1)) → x ∈ δs i (e k)) ∧
       (∀ i : Fin n, Req ψs i (e k) → rs i (e k) (e (k + 1)) →
         ∃ x, x ∈ δs i (e k) ∧ x ∉ δs i (e (k + 1))) ∧
       (∀ i : Fin n, Req ψs i (e k) → ¬ rs i (e k) (e (k + 1)) →
         ψs i (e (k + 1))))

/-- The Rule 10 conclusion: applies `rel_rank_lex` directly, converting the
certificate fields into its premise shapes.

**Two statement corrections (relative to the first draft, both found while
writing the proof)**:

1. The draft's `hjustice` had `Req ψs i` as antecedent — weaker than the
   paper's S3 (every scheduler that is **on** eventually fires, including
   preempted components). Although the soundness proof only invokes S3 at
   non-preempted points, `rel_rank_lex`'s premise quantifies over all `i`,
   so the certificate must supply full-strength S3. This version uses the
   `cert.ψs i` antecedent.
2. The draft was missing S4 (at every time, at least one scheduler is on).
   Without S4 the statement is **false**: on a constant behavior with φ
   always true, all δs empty, and no scheduler, every premise holds
   vacuously while q never happens. This version adds `hsched`. -/
theorem LexRankCert.toLeadsTo {σ : Type u} {p q : StatePred σ}
    (cert : LexRankCert σ p q)
    (hjustice : ∀ e, cert.H e → ∀ k : ℕ, cert.φ (e k) → ∀ i : Fin cert.n,
      cert.ψs i (e k) →
      (∃ m, q (e (k + m))) ∨ (∃ m, cert.rs i (e (k + m)) (e (k + m + 1))))
    (hsched : ∀ e, cert.H e → ∀ k : ℕ, cert.φ (e k) →
      (∃ m, q (e (k + m))) ∨ ∃ i : Fin cert.n, cert.ψs i (e k)) :
    Entails cert.H (leadsTo (statePred p) (statePred q)) := by
  have hS1 : ∀ e : Behavior σ, cert.H e → ∀ k : ℕ, p (e k) →
      eventually (statePred q) (e.drop k) ∨ cert.φ (e k) := by
    intro e' hH' k' hp'
    rcases cert.c1 e' hH' k' hp' with hq | hφ
    · exact Or.inl (eventually_statePred_drop q e' k' |>.mpr ⟨0, hq⟩)
    · exact Or.inr hφ
  have hL2 : ∀ e : Behavior σ, cert.H e → ∀ k : ℕ, cert.φ (e k) →
      L2Step q cert.φ cert.δs cert.ψs cert.rs e k := by
    intro e' hH' k' hφ'
    rcases cert.l2 e' hH' k' hφ' with hevq | hrest
    · exact Or.inl (eventually_statePred_drop q e' k' |>.mpr hevq)
    · exact Or.inr hrest
  have hS3 : ∀ e : Behavior σ, cert.H e → ∀ k : ℕ, cert.φ (e k) →
      ∀ i : Fin cert.n, cert.ψs i (e k) →
      eventually (statePred q) (e.drop k) ∨
        eventually (actionPred (cert.rs i)) (e.drop k) := by
    intro e' hH' k' hφ' i hψ
    rcases hjustice e' hH' k' hφ' i hψ with hq | hr
    · exact Or.inl (eventually_statePred_drop q e' k' |>.mpr hq)
    · exact Or.inr (eventually_actionPred_drop (cert.rs i) e' k' |>.mpr hr)
  have hS4 : ∀ e : Behavior σ, cert.H e → ∀ k : ℕ, cert.φ (e k) →
      eventually (statePred q) (e.drop k) ∨ ∃ i : Fin cert.n, cert.ψs i (e k) := by
    intro e' hH' k' hφ'
    rcases hsched e' hH' k' hφ' with hq | hψ
    · exact Or.inl (eventually_statePred_drop q e' k' |>.mpr hq)
    · exact Or.inr hψ
  exact rel_rank_lex p q cert.φ cert.δs cert.ψs cert.rs cert.H hS1 hL2 hS3 hS4

end Bft
