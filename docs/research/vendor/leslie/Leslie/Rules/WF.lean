import Leslie.Rules.Basic
import Leslie.Tactics.Structural
import Leslie.Gadgets.TheoremDeriving

/-! Theorems about weak-fairness. -/

open Classical

namespace TLA

section wf

variable {σ : Type u}

section wf_def

variable {a : action σ}

theorem wf_as_leads_to : (𝒲ℱ a) =tla= (□ Enabled a ↝ ⟨a⟩) := rfl

theorem wf_alt1 : (𝒲ℱ a) =tla= □ ◇ ((¬ Enabled a) ∨ □ ◇ ⟨a⟩) := by
  funext e ; unfold weak_fairness ; rw [implies_to_or] ; simp [tlasimp]
  rw [← eventually_or] ; (repeat rw [always_eventually_or_distrib]) ; simp [tlasimp]

theorem wf_alt1' : (𝒲ℱ a) =tla= □ ◇ ((¬ Enabled a) ∨ ⟨a⟩) := by
  rw [wf_alt1] ; (repeat rw [always_eventually_or_distrib]) ; simp [tlasimp]

end wf_def

/--
A useful rule for proving `↝`. Compared with its original presentation in
the paper "The Temporal Logic of Actions", the following version contains
some changes to make it hopefully more practical.
-/
@[tla_derive]
theorem wf1 (p q : pred σ) (next a : action σ) :
  ((p ∧ ⟨next⟩ ⇒ ◯ p ∨ ◯ q) ∧
   (p ∧ ⟨next⟩ ∧ ⟨a⟩ ⇒ ◯ q) ∧
   (p ⇒ Enabled a ∨ q) ∧
   (□ ⟨next⟩ ∧ 𝒲ℱ a)) |-tla- (p ↝ q) := by
  rw [wf_alt1']
  intro e ⟨hpuntilq, haq, henable, hnext, hwf_alt⟩ k hp
  specialize hwf_alt k ; rcases hwf_alt with ⟨k1, hwf_alt⟩
  -- know that: either `q` holds between `k` and `k + k1`, or `p` holds at `k1`
  -- use `henable` to know that if it is the latter case, then `q` must hold in the next step
  have htmp : (∃ k' ≤ k1, q <| e.drop (k + k')) ∨ (p <| e.drop (k + k1)) := by
    clear hwf_alt
    induction k1 with
    | zero => right ; assumption
    | succ n ih => {
      rw [← Nat.add_assoc]
      rcases ih with ⟨k', hle, ih⟩ | ih
      · left ; exists k' ; constructor ; omega ; apply ih
      · specialize hpuntilq _ ⟨ih, (hnext _)⟩
        rcases hpuntilq with hq | hq <;> tla_unfold_simp'
        · right ; apply hq
        · left ; exists (n + 1) ; aesop
    }
  rcases htmp with ⟨k', _, hq⟩ | hq <;> tla_unfold_simp'
  · aesop
  · rcases hwf_alt with hq2 | hq2
    · specialize henable _ hq ; aesop
    · exists (k1 + 1)
      specialize haq (k + k1) hq ; rw [← Nat.add_assoc] ; apply haq <;> aesop

/-- Structured premises for the `wf1` rule. Using a structure avoids
    positional tuple destructuring and makes each obligation named. -/
structure WF1Premises (p q : pred σ) (next a : action σ) (e : exec σ) : Prop where
  /-- Safety: if `p` holds and `next` fires, then `p` or `q` holds in the next state. -/
  safety : ∀ k, p (e.drop k) → next (e k) (e (k + 1)) → p (e.drop (k + 1)) ∨ q (e.drop (k + 1))
  /-- Progress: if `p` holds and the fair action `a` fires, `q` holds in the next state. -/
  progress : ∀ k, p (e.drop k) → next (e k) (e (k + 1)) → a (e k) (e (k + 1)) → q (e.drop (k + 1))
  /-- Enablement: if `p` holds, then either `a` is enabled or `q` already holds. -/
  enablement : ∀ k, p (e.drop k) → (∃ s', a (e k) s') ∨ q (e.drop k)
  /-- The system always takes next steps. -/
  always_next : always (action_pred next) e
  /-- The fair action satisfies weak fairness. -/
  fair : weak_fairness a e

/-- Apply `wf1` using structured premises. This is the recommended way to use WF1
    in liveness proofs: instantiate `WF1Premises` with named fields, then call this. -/
theorem wf1_apply {p q : pred σ} {next a : action σ} {e : exec σ}
    (h : WF1Premises p q next a e) : leads_to p q e := by
  apply wf1 p q next a e
  refine ⟨?_, ?_, ?_, h.always_next, h.fair⟩
  · intro k ⟨hp, hnext⟩
    simp only [action_pred, exec.drop] at hnext
    have hsafe := h.safety k hp hnext
    -- Goal: later p (e.drop k) ∨ later q (e.drop k)
    -- = p ((e.drop k).drop 1) ∨ q ((e.drop k).drop 1)
    -- = p (e.drop (k + 1)) ∨ q (e.drop (k + 1))  [by exec.drop_drop]
    rcases hsafe with hp' | hq'
    · left ; show p ((e.drop k).drop 1) ; rw [exec.drop_drop] ; exact hp'
    · right ; show q ((e.drop k).drop 1) ; rw [exec.drop_drop] ; exact hq'
  · intro k ⟨hp, hnext, ha⟩
    simp only [action_pred, exec.drop] at hnext ha
    have hprog := h.progress k hp hnext ha
    show q ((e.drop k).drop 1) ; rw [exec.drop_drop] ; exact hprog
  · intro k hp
    simp only [tla_enabled, state_pred, exec.drop, tla_or]
    exact h.enablement k hp

/-- A (relatively) original presentation of the `wf1` rule. -/
theorem wf1_original (p q : pred σ) (next a : action σ) :
  ((p ∧ ⟨next⟩ ⇒ ◯ (p ∨ q)) ∧
   ((p ∧ ⟨next⟩ ∧ ⟨a⟩ ⇒ ◯ q)) ∧
   ((p ⇒ Enabled a))) |-tla- (□ ⟨next⟩ ∧ 𝒲ℱ a → p ↝ q) := by
  tla_intros
  apply pred_implies_trans
  on_goal 2=> apply wf1 (next := next) (a := a)
  all_goals (tla_unfold_simp ; try aesop)

end wf

end TLA
