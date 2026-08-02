import Mathlib.Order.Filter.AtTopBot.Basic
import TlaDsl.Basic

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

end Tla
