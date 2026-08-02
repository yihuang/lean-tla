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
        simpa [actionPred, Behavior.drop] using hnext n
      exact hstep (e n) (e (n + 1)) hstepn ih

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
        simpa [actionPred, StutAction, Behavior.drop] using hnext n
      exact hstep (e n) (e (n + 1)) hstepn ih

/-- Leads-to is transitive. -/
theorem leadsTo_trans_entails {σ : Type u} (P Q R : Pred σ) :
    Entails (tlaAnd (leadsTo P Q) (leadsTo Q R)) (leadsTo P R) := by
  intro e h n hP
  have h1 : ∀ k, (tlaImp P (eventually Q)) (e.drop k) := by simpa [leadsTo, always] using h.1
  have h2 : ∀ k, (tlaImp Q (eventually R)) (e.drop k) := by simpa [leadsTo, always] using h.2
  rcases h1 n hP with ⟨k, hQ⟩
  have hQ' : Q (e.drop (n + k)) := by simpa [Behavior.drop] using hQ
  rcases h2 (n + k) hQ' with ⟨m, hR⟩
  refine ⟨k + m, ?_⟩
  simpa [Behavior.drop, Nat.add_assoc] using hR

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

/-- WF1 (Lamport): under `□[N]_v ∧ WF_v(A)`, if from a `p` state each
`[N]_v`-step reaches `p ∨ q`, each `⟨A⟩_v`-step reaches `q`, and `p` implies
`Enabled ⟨A⟩_v ∨ q`, then `p` leads to `q`. Proved from the semantics. -/
theorem wf1 {σ : Type u} {α : Type v} (p q : StatePred σ) (N A : Action σ) (v : σ → α)
    (hstep : ∀ s s', p s → StutAction N v s s' → p s' ∨ q s')
    (haq : ∀ s s', p s → AngleAction A v s s' → q s')
    (henable : ∀ s, p s → Enabled (AngleAction A v) s ∨ q s) :
    Entails (tlaAnd (stutAlways N v) (WF_v A v)) (leadsTo (statePred p) (statePred q)) := by
  intro e h k hpk
  simp [eventually, statePred, Behavior.drop] at hpk ⊢
  apply Classical.byContradiction
  intro hq
  have hqall : ∀ m, ¬ q (e (k + m)) := by
    intro m hm
    exact hq ⟨m, hm⟩
  have hN : ∀ n, StutAction N v (e n) (e (n + 1)) := by
    simpa [stutAlways, always, actionPred, Behavior.drop] using h.1
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
    simpa [always, statePred, Behavior.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hen
  rcases hWF k hEnAlways with ⟨j, hB⟩
  have hB' : AngleAction A v (e (k + j)) (e (k + j + 1)) := by
    simpa [actionPred, Behavior.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hB
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
  simp [eventually, statePred, Behavior.drop] at hpk ⊢
  apply Classical.byContradiction
  intro hq
  have hqall : ∀ m, ¬ q (e (k + m)) := by
    intro m hm
    exact hq ⟨m, hm⟩
  have hN : ∀ n, StutAction N v (e n) (e (n + 1)) := by
    simpa [stutAlways, always, actionPred, Behavior.drop] using h.1
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
    simpa [always, eventually, statePred, Behavior.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hInf
  rcases hSF k hInfAlways with ⟨j, hB⟩
  have hB' : AngleAction A v (e (k + j)) (e (k + j + 1)) := by
    simpa [actionPred, Behavior.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hB
  exact False.elim (hqall (j + 1) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using haq (e (k + j)) (e (k + j + 1)) (hp j) hB'))

end Tla
