import Bft.Skin
import Bft.Rules
import Bft.Tactic

/-! # Bft.Examples.SkinCounter — the syntax skin end to end

The full authoring arc of the skin layer on a bounded two-counter:

```
state + tla_var  →  spec in brackets  →  invariant  →  WF1 liveness
```

Everything is proved with kernel rules (`init_invariant_stut`, `wf1`); the
brackets only change how the spec is written and how goals display.
-/

open scoped Bft

namespace Bft.Examples.SkinCounter

/-- The state: two counters and a shared bound. -/
structure St where
  x : ℕ
  y : ℕ
deriving Repr, DecidableEq

tla_var St x y

/-- Initial predicate, written as pseudocode. -/
def Init : StatePred St := [p| x = 0 ∧ y = 0]

/-- Both counters increment together while below the bound. -/
def Tick : Action St := [a| x < 2 ∧ x' = x + 1 ∧ y' = y + 1]

/-- The next-state relation: tick or finish. -/
def Next : Action St := [a| Tick ∨ (x = 2 ∧ x' = x ∧ y' = y)]

/-- The spec, read like TLA: `Init ∧ □[Next]_vars ∧ WF_(vars)(Tick)`. -/
def Spec : Pred St := [t| Init ∧ □[Next]_vars]
def SpecWF : Pred St := [t| Init ∧ □[Next]_vars ∧ WF_(vars)(Tick)]

/-- Invariant: the counters stay in lockstep and within the bound. -/
structure Inv (s : St) : Prop where
  sync : s.x = s.y
  bound : s.x ≤ 2

theorem init_inv : ∀ s, Init s → Inv s := by
  intro s h
  have e1 : s.x = 0 := h.1
  have e2 : s.y = 0 := h.2
  exact ⟨by omega, by omega⟩

theorem step_inv : ∀ s s', StutAction Next vars s s' → Inv s → Inv s' := by
  intro s s' hstep hinv
  rcases hstep with hnext | hstut
  · rcases hnext with htick | ⟨hx, hx', hy'⟩
    · obtain ⟨hlt, hx', hy'⟩ := htick
      have e0 : s.x < 2 := hlt
      have e1 : s'.x = s.x + 1 := hx'
      have e2 : s'.y = s.y + 1 := hy'
      exact ⟨by rw [e1, e2, hinv.sync], by rw [e1]; omega⟩
    · have e1 : s'.x = s.x := hx'
      have e2 : s'.y = s.y := hy'
      exact ⟨by rw [e1, e2, hinv.sync], by rw [e1]; exact hinv.bound⟩
  · have : s' = s := hstut
    rw [this]
    exact hinv

/-- Safety: on every reachable state the counters are equal and bounded. -/
theorem safety : Entails Spec (always (statePred Inv)) :=
  init_invariant_stut Init Next vars Inv init_inv step_inv

/-- One tick brings `x = n` to `x = n + 1` (below the bound), by WF1. -/
theorem tick_progress (n : ℕ) (hn : n < 2) :
    Entails (tlaAnd (stutAlways Next vars) (WF_v Tick vars))
      (leadsTo (statePred { s | s.x = n }) (statePred { s | s.x = n + 1 })) := by
  apply wf1
  · -- p preserved by [Next]_vars unless q holds
    intro s s' hp hstep
    simp at hp
    rcases hstep with hnext | hstut
    · rcases hnext with htick | ⟨hx2, hx', _⟩
      · obtain ⟨hlt, hx', _⟩ := htick
        have e1 : s'.x = s.x + 1 := hx'
        right; show s'.x = n + 1; omega
      · have e1 : s'.x = s.x := hx'
        left; show s'.x = n; omega
    · left; have : s' = s := hstut; rwa [this]
  · -- ⟨Tick⟩_vars achieves q
    intro s s' hp hang
    simp at hp
    obtain ⟨⟨hlt, hx', _⟩, hne⟩ := hang
    have e1 : s'.x = s.x + 1 := hx'
    show s'.x = n + 1; omega
  · -- ⟨Tick⟩_vars is enabled whenever x < 2
    intro s hp
    simp at hp
    left
    refine ⟨⟨s.x + 1, s.y + 1⟩, ⟨?_, ?_, ?_⟩, ?_⟩
    · show x s < 2; simp only [x_apply]; omega
    · rfl
    · rfl
    · -- the frame changes: the new state differs in x
      show vars _ ≠ vars s
      simp only [vars_apply]
      intro h; have h2 : s.x + 1 = s.x := congrArg St.x h; omega

end Bft.Examples.SkinCounter
