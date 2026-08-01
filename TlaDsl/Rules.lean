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

end Tla
