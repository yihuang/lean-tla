import Mathlib.Order.Filter.AtTopBot.Basic
import TlaDsl.Basic
import TlaDsl.Prime
import Cslib.Foundations.Data.OmegaSequence.Temporal
import Cslib.Foundations.Data.OmegaSequence.InfOcc

namespace Tla

/-! # A few derived rules

Everything is proved from the semantics; these are the rules the tactic layer
and users build on.
-/

/-- Standard invariant induction for `Init ∧ □⟨Next⟩ ⊢ □Inv`. -/
theorem init_invariant {σ : Type u} (init : StatePred σ) (next : Action σ) (inv : StatePred σ)
    (hinit : ∀ s, init s → inv s)
    (hstep : ∀ s s', next s s' → inv s → inv s') :
    Entails (tlaAnd (statePred init) (always (actionPred next))) (always (statePred inv)) := by
  intro e he
  have hinit0 : init (e 0) := by simpa [tlaAnd, statePred] using he.1
  have hnext : ∀ k, actionPred next (e.drop k) := by simpa [always] using he.2
  intro n
  induction n with
  | zero => exact hinit (e 0) hinit0
  | succ n ih =>
      have hstepn : next (e n) (e (n + 1)) := by
        simpa [actionPred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext n
      exact (by simpa [statePred] using hstep (e n) (e (n + 1)) hstepn (by simpa [statePred] using ih))

/-- Invariant induction for stuttering specs `Init ∧ □[Next]_v ⊢ □Inv`.
The step case must account for the stutter disjunct. -/
theorem init_invariant_stut {σ : Type u} {α : Type v} (init : StatePred σ) (next : Action σ)
    (v : σ → α) (inv : StatePred σ)
    (hinit : ∀ s, init s → inv s)
    (hstep : ∀ s s', (next s s' ∨ v s' = v s) → inv s → inv s') :
    Entails (tlaAnd (statePred init) (stutAlways next v)) (always (statePred inv)) := by
  intro e he
  have hinit0 : init (e 0) := by simpa [tlaAnd, statePred] using he.1
  have hnext : ∀ k, actionPred (StutAction next v) (e.drop k) := by
    simpa [stutAlways, always] using he.2
  intro n
  induction n with
  | zero => exact hinit (e 0) hinit0
  | succ n ih =>
      have hstepn : next (e n) (e (n + 1)) ∨ v (e (n + 1)) = v (e n) := by
        simpa [actionPred, StutAction, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext n
      exact (by simpa [statePred] using hstep (e n) (e (n + 1)) hstepn (by simpa [statePred] using ih))

/-- Leads-to is transitive. -/
theorem leadsTo_trans_entails {σ : Type u} (P Q R : Pred σ) :
    Entails (tlaAnd (leadsTo P Q) (leadsTo Q R)) (leadsTo P R) := by
  intro e h n hP
  have h1 : ∀ k, (tlaImp P (eventually Q)) (e.drop k) := by simpa [leadsTo, always] using h.1
  have h2 : ∀ k, (tlaImp Q (eventually R)) (e.drop k) := by simpa [leadsTo, always] using h.2
  rcases h1 n hP with ⟨k, hQ⟩
  have hQ' : Q (e.drop (n + k)) := by simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hQ
  rcases h2 (n + k) hQ' with ⟨m, hR⟩
  refine ⟨k + m, ?_⟩
  simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hR

/-! ## Liveness rules: WF1 and SF1 -/

/-- Leads-to distributes over disjunction on the left. -/
theorem leadsTo_or {σ : Type u} (p1 p2 q : Pred σ) :
    Entails (tlaAnd (leadsTo p1 q) (leadsTo p2 q)) (leadsTo (tlaOr p1 p2) q) := by
  intro e h n hpq
  rcases hpq with hp1 | hp2
  · have h1 : ∀ n, p1 (e.drop n) → eventually q (e.drop n) := by
      simpa [leadsTo, always, tlaImp] using h.1
    exact h1 n hp1
  · have h2 : ∀ n, p2 (e.drop n) → eventually q (e.drop n) := by
      simpa [leadsTo, always, tlaImp] using h.2
    exact h2 n hp2

/-- Case split under an invariant: if `p` implies (under `inv`) one of
`p1 ∨ p2 ∨ p3`, and each `pᵢ` leads to `q`, then `p` leads to `q`. -/
theorem leads_to_cases {σ : Type u} (e : Behavior σ) (inv : σ → Prop) (p q p1 p2 p3 : Pred σ)
    (hcase : ∀ n, inv (e n) → p (e.drop n) → (tlaOr (tlaOr p1 p2) p3) (e.drop n))
    (h1 : ∀ n, p1 (e.drop n) → eventually q (e.drop n))
    (h2 : ∀ n, p2 (e.drop n) → eventually q (e.drop n))
    (h3 : ∀ n, p3 (e.drop n) → eventually q (e.drop n)) :
    ∀ n, inv (e n) → p (e.drop n) → eventually q (e.drop n) := by
  intro n hinv hp
  rcases hcase n hinv hp with hAB | h3'
  · rcases hAB with h1' | h2'
    · exact h1 n h1'
    · exact h2 n h2'
  · exact h3 n h3'

/-- WF1 (Lamport): under `□[N]_v ∧ WF_v(A)`, if from a `p` state each
`[N]_v`-step reaches `p ∨ q`, each `⟨A⟩_v`-step reaches `q`, and `p` implies
`Enabled ⟨A⟩_v ∨ q`, then `p` leads to `q`. Proved from the semantics. -/
theorem wf1 {σ : Type u} {α : Type v} (p q : StatePred σ) (N A : Action σ) (v : σ → α)
    (hstep : ∀ s s', p s → StutAction N v s s' → p s' ∨ q s')
    (haq : ∀ s s', p s → AngleAction A v s s' → q s')
    (henable : ∀ s, p s → Enabled (AngleAction A v) s ∨ q s) :
    Entails (tlaAnd (stutAlways N v) (WF_v A v)) (leadsTo (statePred p) (statePred q)) := by
  intro e h k hpk
  simp [eventually, statePred, Cslib.ωSequence.drop, Nat.add_comm] at hpk ⊢
  apply Classical.byContradiction
  intro hq
  have hqall : ∀ m, ¬ q (e (k + m)) := by
    intro m hm
    exact hq ⟨m, hm⟩
  have hN : ∀ n, StutAction N v (e n) (e (n + 1)) := by
    simpa [stutAlways, always, actionPred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.1
  have hp : ∀ j, p (e (k + j)) := by
    intro j
    induction j with
    | zero => simpa using hpk
    | succ j ih =>
        rcases hstep (e (k + j)) (e (k + j + 1)) ih (hN (k + j)) with hp' | hq'
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp'
        · exact False.elim (hqall (j + 1) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hq'))
  have hen : ∀ j, Enabled (AngleAction A v) (e (k + j)) := by
    intro j
    rcases henable (e (k + j)) (hp j) with hEn | hqj
    · exact hEn
    · exact False.elim (hqall j hqj)
  have hWF : ∀ n, (always (statePred (Enabled (AngleAction A v))) (e.drop n)) →
      eventually (actionPred (AngleAction A v)) (e.drop n) := by
    simpa [WF_v, always, tlaImp] using h.2
  have hEnAlways : always (statePred (Enabled (AngleAction A v))) (e.drop k) := by
    simpa [always, statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hen
  rcases hWF k hEnAlways with ⟨j, hB⟩
  have hB' : AngleAction A v (e (k + j)) (e (k + j + 1)) := by
    simpa [actionPred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hB
  exact False.elim (hqall (j + 1) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using haq (e (k + j)) (e (k + j + 1)) (hp j) hB'))

/-- SF1 (strong fairness): like WF1, but `p` only requires `A` to be
*eventually* enabled — semantically: from any `p` state of any behavior,
`Enabled ⟨A⟩_v` holds at some later position. -/
theorem sf1 {σ : Type u} {α : Type v} (p q : StatePred σ) (N A : Action σ) (v : σ → α)
    (hstep : ∀ s s', p s → StutAction N v s s' → p s' ∨ q s')
    (haq : ∀ s s', p s → AngleAction A v s s' → q s')
    (henable : ∀ e : Behavior σ, ∀ k : Nat, p (e k) →
      ∃ j : Nat, Enabled (AngleAction A v) (e (k + j))) :
    Entails (tlaAnd (stutAlways N v) (SF_v A v)) (leadsTo (statePred p) (statePred q)) := by
  intro e h k hpk
  simp [eventually, statePred, Cslib.ωSequence.drop, Nat.add_comm] at hpk ⊢
  apply Classical.byContradiction
  intro hq
  have hqall : ∀ m, ¬ q (e (k + m)) := by
    intro m hm
    exact hq ⟨m, hm⟩
  have hN : ∀ n, StutAction N v (e n) (e (n + 1)) := by
    simpa [stutAlways, always, actionPred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.1
  have hp : ∀ j, p (e (k + j)) := by
    intro j
    induction j with
    | zero => simpa using hpk
    | succ j ih =>
        rcases hstep (e (k + j)) (e (k + j + 1)) ih (hN (k + j)) with hp' | hq'
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp'
        · exact False.elim (hqall (j + 1) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hq'))
  have hInf : ∀ i, ∃ j, Enabled (AngleAction A v) (e (k + i + j)) := by
    intro i
    exact henable e (k + i) (hp i)
  have hSF : ∀ n, (always (eventually (statePred (Enabled (AngleAction A v)))) (e.drop n)) →
      eventually (actionPred (AngleAction A v)) (e.drop n) := by
    simpa [SF_v, always, tlaImp] using h.2
  have hInfAlways : always (eventually (statePred (Enabled (AngleAction A v)))) (e.drop k) := by
    simpa [always, eventually, statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hInf
  rcases hSF k hInfAlways with ⟨j, hB⟩
  have hB' : AngleAction A v (e (k + j)) (e (k + j + 1)) := by
    simpa [actionPred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hB
  exact False.elim (hqall (j + 1) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using haq (e (k + j)) (e (k + j + 1)) (hp j) hB'))

/-- Standard-form SF1: under `□[N]_v ∧ SF_v(A)`, if from a `p` state each
`[N]_v`-step either reaches `q` or is eventually followed by
`Enabled ⟨A⟩_v`, then `p` leads to `q`. The enablement is *spec-relative*
(it recurs along the spec's own steps) — this is the distinguishing SF1
premise: weak fairness needs enablement to hold eventually-always, strong
fairness only needs it to recur. -/
theorem sf1_standard {σ : Type u} {α : Type v} (p q : StatePred σ) (N A : Action σ)
    (v : σ → α)
    (hstep : ∀ s s', p s → StutAction N v s s' → p s' ∨ q s')
    (haq : ∀ s s', p s → AngleAction A v s s' → q s') :
    Entails (tlaAnd (tlaAnd (stutAlways N v) (SF_v A v))
      (always (tlaImp (tlaAnd (statePred p) (actionPred (StutAction N v)))
        (tlaOr (eventually (statePred (Enabled (AngleAction A v)))) (statePred q)))))
      (leadsTo (statePred p) (statePred q)) := by
  intro e h k hpk
  simp [eventually, statePred, Cslib.ωSequence.drop, Nat.add_comm] at hpk ⊢
  apply Classical.byContradiction
  intro hq
  have hqall : ∀ m, ¬ q (e (k + m)) := by
    intro m hm
    exact hq ⟨m, hm⟩
  have hN : ∀ n, StutAction N v (e n) (e (n + 1)) := by
    simpa [stutAlways, always, actionPred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.1.1
  have hp : ∀ j, p (e (k + j)) := by
    intro j
    induction j with
    | zero => simpa using hpk
    | succ j ih =>
        rcases hstep (e (k + j)) (e (k + j + 1)) ih (hN (k + j)) with hp' | hq'
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp'
        · exact False.elim (hqall (j + 1) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hq'))
  have hEn : ∀ i, (tlaOr (eventually (statePred (Enabled (AngleAction A v)))) (statePred q))
      (e.drop (k + i)) := by
    intro i
    have hc := h.2 (k + i)
    exact hc ⟨by simpa [statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp i,
      by simpa [actionPred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hN (k + i)⟩
  have hInf : ∀ i, ∃ j, Enabled (AngleAction A v) (e (k + i + j)) := by
    intro i
    rcases hEn i with hE | hq'
    · simpa [eventually, statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hE
    · exact False.elim (hqall i (by simpa [statePred, Cslib.ωSequence.drop] using hq'))
  have hSF : ∀ n, (always (eventually (statePred (Enabled (AngleAction A v)))) (e.drop n)) →
      eventually (actionPred (AngleAction A v)) (e.drop n) := by
    simpa [SF_v, always, tlaImp] using h.1.2
  have hInfAlways : always (eventually (statePred (Enabled (AngleAction A v)))) (e.drop k) := by
    simpa [always, eventually, statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hInf
  rcases hSF k hInfAlways with ⟨j, hB⟩
  have hB' : AngleAction A v (e (k + j)) (e (k + j + 1)) := by
    simpa [actionPred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hB
  exact False.elim (hqall (j + 1) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using haq (e (k + j)) (e (k + j + 1)) (hp j) hB'))

/-! ## The rank-function leads-to rule -/

/-- The rank-function leads-to rule: if, at every rank `n`, the spec makes
`p ∧ f = n` lead to `q ∨ (p ∧ f < n)`, then `p` leads to `q`. This packages
the well-founded (strong) induction on the `Nat` rank, so each WF1/SF1 step
only has to show the rank strictly decreases — the engine for protocols
whose progress is a chain of *different* actions (ticket locks, BFT view
advance, ...). -/
theorem leads_to_via_nat {σ : Type u} (p q : StatePred σ) (f : σ → Nat) (H : Pred σ)
    (hstep : ∀ n : Nat, Entails H (leadsTo
      (statePred (fun s => p s ∧ f s = n))
      (statePred (fun s => q s ∨ (p s ∧ f s < n))))) :
    Entails H (leadsTo (statePred p) (statePred q)) := by
  intro e hH
  have hmain : ∀ n k : Nat, f (e k) = n → p (e k) →
      eventually (statePred q) (e.drop k) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih k hfn hp
    have hl : leadsTo (statePred (fun s => p s ∧ f s = n))
        (statePred (fun s => q s ∨ (p s ∧ f s < n))) e := hstep n e hH
    have hp' : (statePred (fun s => p s ∧ f s = n)) (e.drop k) := by
      simpa [statePred, Cslib.ωSequence.drop, Nat.add_comm] using ⟨hp, hfn⟩
    rcases hl k hp' with ⟨j, hj⟩
    rcases hj with hq | hp_lt
    · -- reached `q` now
      refine ⟨j, ?_⟩
      simpa [statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hq
    · -- the rank strictly decreased: apply the hypothesis at the new rank
      have hlt : f (e (k + j)) < n := by
        simpa [statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp_lt.2
      have hpj : p (e (k + j)) := by
        simpa [statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp_lt.1
      have hih : eventually (statePred q) (e.drop (k + j)) :=
        ih (f (e (k + j))) hlt (k + j) rfl hpj
      rcases hih with ⟨m, hm⟩
      refine ⟨j + m, ?_⟩
      simpa [statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm
  intro k hp
  have hp' : p (e k) := by simpa [statePred, Cslib.ωSequence.drop, Nat.add_comm] using hp
  exact hmain (f (e k)) k rfl hp'

/-! ## Action algebra -/

/-- `Enabled` distributes over action disjunction. -/
theorem enabled_or {σ : Type u} (A B : Action σ) (s : σ) :
    Enabled (actOr A B) s ↔ Enabled A s ∨ Enabled B s := by
  constructor
  · rintro ⟨s', hA | hB⟩
    · exact Or.inl ⟨s', hA⟩
    · exact Or.inr ⟨s', hB⟩
  · rintro (hA | hB)
    · rcases hA with ⟨s', hA'⟩
      exact ⟨s', Or.inl hA'⟩
    · rcases hB with ⟨s', hB'⟩
      exact ⟨s', Or.inr hB'⟩

/-- `Enabled` over action conjunction implies both conjuncts are enabled
(the converse would need a common witness). -/
theorem enabled_and {σ : Type u} (A B : Action σ) (s : σ) :
    Enabled (actAnd A B) s → Enabled A s ∧ Enabled B s := by
  rintro ⟨s', hA, hB⟩
  exact ⟨⟨s', hA⟩, ⟨s', hB⟩⟩

/-- `Enabled ⟨A ∨ B⟩` is the disjunction of the angle-enablements. -/
theorem enabled_angle_or {σ : Type u} {α : Type v} (A B : Action σ) (v : σ → α) (s : σ) :
    Enabled (AngleAction (actOr A B) v) s ↔
      Enabled (AngleAction A v) s ∨ Enabled (AngleAction B v) s := by
  constructor
  · rintro ⟨s', hAB, hchg⟩
    rcases hAB with hA' | hB'
    · exact Or.inl ⟨s', hA', hchg⟩
    · exact Or.inr ⟨s', hB', hchg⟩
  · rintro (hA | hB)
    · rcases hA with ⟨s', hA', hchg⟩
      exact ⟨s', Or.inl hA', hchg⟩
    · rcases hB with ⟨s', hB', hchg⟩
      exact ⟨s', Or.inr hB', hchg⟩

/-- Fairness of a disjunction from one component: if `A` is weakly fair and
`A ∨ B`'s enablement always implies `A`'s, then `A ∨ B` is weakly fair.
(The plain `WF(A) ∧ WF(B) ⊢ WF(A ∨ B)` is *not* valid: the components can
alternate enablement while the union stays enabled, so neither is ever
eventually-always enabled and no fairness applies.) -/
theorem wf_or_of_wf {σ : Type u} {α : Type v} (A B : Action σ) (v : σ → α) :
    Entails
      (tlaAnd (WF_v A v)
        (always (tlaImp
          (statePred (Enabled (AngleAction (actOr A B) v)))
          (statePred (Enabled (AngleAction A v))))))
      (WF_v (actOr A B) v) := by
  intro e h k hEn
  -- hEn : always (statePred (Enabled ⟨A ∨ B⟩)) (e.drop k)
  have hEnA : always (statePred (Enabled (AngleAction A v))) (e.drop k) := by
    intro n
    -- dominance: Enabled ⟨A ∨ B⟩ at position k + n implies Enabled ⟨A⟩
    have hdom : ∀ m, Enabled (AngleAction (actOr A B) v) (e (k + m)) →
        Enabled (AngleAction A v) (e (k + m)) := by
      intro m hm
      have hd := h.2 (k + m)
      have hm' : statePred (Enabled (AngleAction (actOr A B) v)) (e.drop (k + m)) := by
        simpa [statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm
      have hA : statePred (Enabled (AngleAction A v)) (e.drop (k + m)) := by
        simpa [tlaImp] using hd hm'
      simpa [statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hA
    have hEn' : statePred (Enabled (AngleAction (actOr A B) v)) (e.drop (k + n)) := by
      have he := hEn n
      simpa [always, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he
    have hEn'' : Enabled (AngleAction (actOr A B) v) (e (k + n)) := by
      simpa [statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hEn'
    exact (by
      simpa [statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hdom n hEn'')
  -- WF(A) fires an A-step, which is also an (A ∨ B)-step
  have hWF : always (tlaImp (always (statePred (Enabled (AngleAction A v))))
      (eventually (actionPred (AngleAction A v)))) (e.drop k) := by
    intro n
    have h1 := h.1 (n + k)
    simpa [always, tlaImp, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h1
  have hAstep : eventually (actionPred (AngleAction A v)) (e.drop k) := hWF 0 hEnA
  rcases hAstep with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  -- an A-angle-step is an (A ∨ B)-angle-step
  have hj' : actionPred (AngleAction (actOr A B) v) (e.drop (k + j)) := by
    have hh : AngleAction (actOr A B) v (e (k + j)) (e (k + j + 1)) := by
      have hAA : AngleAction A v (e (k + j)) (e (k + j + 1)) := by
        simpa [actionPred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj
      rcases hAA with ⟨hA', hchg⟩
      exact ⟨Or.inl hA', hchg⟩
    simpa [actionPred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
  simpa [actionPred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj'

/-! ## Bridge to CSLib's `LeadsTo` -/

/-- The bridge: TlaDsl's leads-to over state predicates is exactly CSLib's
`LeadsTo` on the same behavior, so CSLib's grind-native `LeadsTo` lemmas
(`leadsTo_trans`, `leadsTo_cases_or`, ...) apply to the fragment that
`wf1`/`sf1` conclude in. -/
theorem leads_to_state_iff {σ : Type u} (p q : StatePred σ) (e : Behavior σ) :
    leadsTo (statePred p) (statePred q) e ↔
      e.LeadsTo {s | p s} {s | q s} := by
  constructor
  · intro h k hp
    have hev : eventually (statePred q) (e.drop k) :=
      h k (by simpa [statePred, Cslib.ωSequence.drop, Nat.add_comm] using hp)
    rcases hev with ⟨m, hm⟩
    refine ⟨k + m, Nat.le_add_right k m, ?_⟩
    simpa [statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm
  · intro h k hp
    have hp' : e k ∈ {s | p s} := by
      simpa [statePred, Cslib.ωSequence.drop, Nat.add_comm] using hp
    rcases h k hp' with ⟨k', hk', hq⟩
    rcases Nat.exists_eq_add_of_le hk' with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    simpa [statePred, Cslib.ωSequence.drop, hm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hq

/-- Leads-to transitivity for state predicates, re-proved through CSLib's
grind-native `LeadsTo` (no manual proof). -/
theorem leads_to_trans_state {σ : Type u} (p q r : StatePred σ) (e : Behavior σ) :
    leadsTo (statePred p) (statePred q) e →
    leadsTo (statePred q) (statePred r) e →
    leadsTo (statePred p) (statePred r) e := by
  intro h1 h2
  exact (leads_to_state_iff p r e).2 (Cslib.ωSequence.leadsTo_trans
    ((leads_to_state_iff p q e).1 h1) ((leads_to_state_iff q r e).1 h2))

/-- Leads-to distributes over disjunction on the left, in the
state-predicate fragment, re-proved through CSLib's grind-native
`leadsTo_cases_or` (no manual behavior-level case analysis). -/
theorem leads_to_or_state {σ : Type u} (p1 p2 q : StatePred σ) (e : Behavior σ)
    (h1 : leadsTo (statePred p1) (statePred q) e)
    (h2 : leadsTo (statePred p2) (statePred q) e) :
    leadsTo (statePred (fun s => p1 s ∨ p2 s)) (statePred q) e := by
  rw [leads_to_state_iff]
  have h1' : e.LeadsTo {s | p1 s} {s | q s} := (leads_to_state_iff p1 q e).1 h1
  have h2' : e.LeadsTo {s | p2 s} {s | q s} := (leads_to_state_iff p2 q e).1 h2
  simpa using
    (Cslib.ωSequence.leadsTo_cases_or
      (p := {s | p1 s ∨ p2 s}) (q := {s | p1 s})
      (r := {s | q s}) (s := {s | q s})
      (by
        intro k hk
        have hk' : e k ∈ {s | p1 s ∨ p2 s} ∧ e k ∈ {s | p1 s} := by
          simpa using hk
        exact h1' k hk'.2)
      (by
        intro k hk
        have hk' : e k ∈ {s | p1 s ∨ p2 s} ∧ e k ∈ {s | p1 s}ᶜ := by
          simpa using hk
        have hk1 : p1 (e k) ∨ p2 (e k) := by
          simpa using hk'.1
        have hk2 : ¬ p1 (e k) := by
          simpa using hk'.2
        exact h2' k (by simpa using hk1.resolve_left hk2)))

/-- Invariant-guided 3-way case split in the state-predicate fragment,
routed through the CSLib bridge (`leads_to_or_state` + transitivity). -/
theorem leads_to_cases_state {σ : Type u} (e : Behavior σ) (inv : σ → Prop)
    (p q p1 p2 p3 : StatePred σ)
    (hcase : ∀ n, inv (e n) → p (e n) → p1 (e n) ∨ p2 (e n) ∨ p3 (e n))
    (h1 : leadsTo (statePred p1) (statePred q) e)
    (h2 : leadsTo (statePred p2) (statePred q) e)
    (h3 : leadsTo (statePred p3) (statePred q) e) :
    ∀ n, inv (e n) → p (e n) → eventually (statePred q) (e.drop n) := by
  have hOr12 : leadsTo (statePred (fun s => p1 s ∨ p2 s)) (statePred q) e :=
    leads_to_or_state p1 p2 q e h1 h2
  have hOr : leadsTo (statePred (fun s => (p1 s ∨ p2 s) ∨ p3 s)) (statePred q) e :=
    leads_to_or_state (fun s => p1 s ∨ p2 s) p3 q e hOr12 h3
  intro n hinv hp
  have hsplit : (p1 (e n) ∨ p2 (e n)) ∨ p3 (e n) := by
    rcases hcase n hinv hp with hp1 | hp2 | hp3
    · exact Or.inl (Or.inl hp1)
    · exact Or.inl (Or.inr hp2)
    · exact Or.inr hp3
  exact hOr n (by
    simpa [statePred, Cslib.ωSequence.drop, Nat.add_comm] using hsplit)

/-! ## CSLib bridges: enabled-infinitely-often in filter vocabulary -/

open Filter

/-- The `SF_v` premise "`Enabled a` infinitely often along the behavior",
written with mathlib's `∃ᶠ` filter (the vocabulary of CSLib's
`ωSequence.Temporal` and `ωSequence.InfOcc`), is equivalent to the pointwise
form `∀ i, ∃ j, Enabled a (e (i + j))` used in `sf1`. -/
theorem sf_enabled_frequently_iff {σ : Type u} (e : Behavior σ) (a : Action σ) :
    (∀ n : Nat, ∃ j : Nat, Enabled a (e (n + j))) ↔
      ∃ᶠ k in atTop, Enabled a (e k) := by
  rw [frequently_atTop]
  constructor
  · intro h m
    rcases h m with ⟨j, hj⟩
    exact ⟨m + j, Nat.le_add_right m j, hj⟩
  · intro h n
    rcases h n with ⟨k, hnk, hk⟩
    exact ⟨k - n, by simpa [Nat.add_sub_of_le hnk] using hk⟩

/-- SF1 stated with the frequently-flavoured enablement premise (infinitely
often enabled, matching `ωSequence.Temporal`/`InfOcc` conventions). The
frequently premise is stronger than `sf1`'s pointwise one, so the theorem
reduces to `sf1`. -/
theorem sf1_frequently {σ : Type u} {α : Type v} (p q : StatePred σ) (N A : Action σ)
    (v : σ → α)
    (hstep : ∀ s s', p s → StutAction N v s s' → p s' ∨ q s')
    (haq : ∀ s s', p s → AngleAction A v s s' → q s')
    (henable : ∀ e : Behavior σ, ∀ k : Nat, p (e k) →
      ∃ᶠ j in atTop, Enabled (AngleAction A v) (e (k + j))) :
    Entails (tlaAnd (stutAlways N v) (SF_v A v)) (leadsTo (statePred p) (statePred q)) := by
  refine sf1 p q N A v hstep haq ?_
  intro e k hpk
  have hfreq : ∃ᶠ j in atTop, Enabled (AngleAction A v) (e (k + j)) := henable e k hpk
  have hf : ∃ j : Nat, Enabled (AngleAction A v) (e (k + j)) := by
    rw [frequently_atTop] at hfreq
    rcases hfreq 0 with ⟨j, _hj0, hj⟩
    exact ⟨j, hj⟩
  exact hf

/-- Finite-state pigeonhole (CSLib `frequently_in_finite_type`): in a
finite state space, "`a` is enabled infinitely often along `e`" is witnessed
by a single enabled state that recurs infinitely often (the `infOcc`
vocabulary). -/
theorem frequently_enabled_finite {σ : Type u} [Finite σ] (e : Behavior σ) (a : Action σ) :
    (∃ᶠ k in atTop, Enabled a (e k)) ↔
      ∃ s : σ, Enabled a s ∧ ∃ᶠ k in atTop, e k = s := by
  simpa using (Cslib.ωSequence.frequently_in_finite_type
    (α := σ) (xs := e) (s := {s : σ | Enabled a s}))

/-- The pointwise "enabled infinitely often" premise of `sf1` is equivalent,
for finite state spaces, to the existence of a single enabled state that
occurs infinitely often — the pigeonhole ingredient for finite-state
strong-fairness arguments. -/
theorem sf_enabled_infOcc_iff {σ : Type u} [Finite σ] (e : Behavior σ) (a : Action σ) :
    (∀ n : Nat, ∃ j : Nat, Enabled a (e (n + j))) ↔
      ∃ s : σ, Enabled a s ∧ ∃ᶠ k in atTop, e k = s := by
  rw [sf_enabled_frequently_iff]
  exact frequently_enabled_finite e a

end Tla
