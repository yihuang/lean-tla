import Bft.Core

/-!
# Bft.Rules — 从语义证明的规则

全部从 `Core` 的语义定义证明，不引入 axiom。时序/位置边界的归约依赖
`Core` 注册的 pointwise simp 引理（`statePred_drop`/`actionPred_drop` 等，
底层是 CSLib 的 `@[simp] get_drop`）——证明里不出现加法重写链。
-/

namespace Bft

/-- 不变式归纳（非 stutter 版）。 -/
theorem init_invariant {σ : Type u} (init : StatePred σ) (next : Action σ)
    (inv : StatePred σ)
    (hinit : ∀ s, init s → inv s)
    (hstep : ∀ s s', next s s' → inv s → inv s') :
    Entails (tlaAnd (statePred init) (always (actionPred next)))
      (always (statePred inv)) := by
  intro e he n
  induction n with
  | zero => exact hinit (e 0) he.1
  | succ n ih =>
      have hstepn : next (e n) (e (n + 1)) := by
        have := he.2 n
        simpa [always] using this
      simpa [statePred] using
        hstep (e n) (e (n + 1)) hstepn (by simpa [statePred] using ih)

/-- Stutter 版不变式归纳。 -/
theorem init_invariant_stut {σ : Type u} {α : Type v} (init : StatePred σ)
    (next : Action σ) (v : σ → α) (inv : StatePred σ)
    (hinit : ∀ s, init s → inv s)
    (hstep : ∀ s s', StutAction next v s s' → inv s → inv s') :
    Entails (tlaAnd (statePred init) (stutAlways next v))
      (always (statePred inv)) := by
  intro e he n
  induction n with
  | zero => exact hinit (e 0) he.1
  | succ n ih =>
      have hstepn : StutAction next v (e n) (e (n + 1)) := by
        have := he.2 n
        simpa [stutAlways, always] using this
      simpa [statePred] using
        hstep (e n) (e (n + 1)) hstepn (by simpa [statePred] using ih)

/-- leads-to 传递性。 -/
theorem leadsTo_trans {σ : Type u} (P Q R : Pred σ) :
    Entails (tlaAnd (leadsTo P Q) (leadsTo Q R)) (leadsTo P R) := by
  intro e h n hP
  rcases h.1 n hP with ⟨k, hQ⟩
  rw [Cslib.ωSequence.drop_drop] at hQ
  rcases h.2 (n + k) hQ with ⟨m, hR⟩
  rw [Cslib.ωSequence.drop_drop] at hR
  exact ⟨k + m, by
    simpa [Cslib.ωSequence.drop_drop, Nat.add_assoc] using hR⟩

/-- leads-to 左析取分配。 -/
theorem leadsTo_or {σ : Type u} (p1 p2 q : Pred σ) :
    Entails (tlaAnd (leadsTo p1 q) (leadsTo p2 q)) (leadsTo (tlaOr p1 p2) q) := by
  intro e h n hpq
  rcases hpq with hp1 | hp2
  · exact h.1 n hp1
  · exact h.2 n hp2

/-- WF1（Lamport）：在 `□[N]_v ∧ WF_v(A)` 下 `p ↝ q`。从语义证明。 -/
theorem wf1 {σ : Type u} {α : Type v} (p q : StatePred σ) (N A : Action σ)
    (v : σ → α)
    (hstep : ∀ s s', p s → StutAction N v s s' → p s' ∨ q s')
    (haq : ∀ s s', p s → AngleAction A v s s' → q s')
    (henable : ∀ s, p s → Enabled (AngleAction A v) s ∨ q s) :
    Entails (tlaAnd (stutAlways N v) (WF_v A v))
      (leadsTo (statePred p) (statePred q)) := by
  intro e h k hpk
  apply Classical.byContradiction
  intro hq
  have hqall : ∀ m, ¬ q (e (k + m)) := by
    intro m hm
    exact hq ⟨m, by simpa using hm⟩
  have hp : ∀ j, p (e (k + j)) := by
    intro j
    induction j with
    | zero => simpa [statePred] using hpk
    | succ j ih =>
        have hN : StutAction N v (e (k + j)) (e (k + j + 1)) := by
          have := h.1 (k + j)
          simpa [stutAlways, always] using this
        rcases hstep _ _ ih hN with hp' | hq'
        · exact hp'
        · exact absurd hq' (hqall (j + 1))
  have hen : ∀ j, Enabled (AngleAction A v) (e (k + j)) := by
    intro j
    rcases henable _ (hp j) with hEn | hqj
    · exact hEn
    · exact absurd hqj (hqall j)
  have hWF : eventually (actionPred (AngleAction A v)) (e.drop k) := by
    have h2 := h.2 k
    apply h2
    intro j
    -- goal: statePred (Enabled …) ((e.drop k).drop j)，归约为 e (k+j)
    simpa using hen j
  rcases hWF with ⟨j, hA⟩
  have hA' : AngleAction A v (e (k + j)) (e (k + j + 1)) := by
    simpa using hA
  exact hqall (j + 1) (haq _ _ (hp j) hA')

/-- SF1：SF 版（反证下永久 enabled 蕴含无限次 enabled，SF 保证触发）。 -/
theorem sf1 {σ : Type u} {α : Type v} (p q : StatePred σ) (N A : Action σ)
    (v : σ → α)
    (hstep : ∀ s s', p s → StutAction N v s s' → p s' ∨ q s')
    (haq : ∀ s s', p s → AngleAction A v s s' → q s')
    (henable : ∀ s, p s → Enabled (AngleAction A v) s ∨ q s) :
    Entails (tlaAnd (stutAlways N v) (SF_v A v))
      (leadsTo (statePred p) (statePred q)) := by
  intro e h k hpk
  apply Classical.byContradiction
  intro hq
  have hqall : ∀ m, ¬ q (e (k + m)) := by
    intro m hm
    exact hq ⟨m, by simpa using hm⟩
  have hp : ∀ j, p (e (k + j)) := by
    intro j
    induction j with
    | zero => simpa [statePred] using hpk
    | succ j ih =>
        have hN : StutAction N v (e (k + j)) (e (k + j + 1)) := by
          have := h.1 (k + j)
          simpa [stutAlways, always] using this
        rcases hstep _ _ ih hN with hp' | hq'
        · exact hp'
        · exact absurd hq' (hqall (j + 1))
  have hen : ∀ j, Enabled (AngleAction A v) (e (k + j)) := by
    intro j
    rcases henable _ (hp j) with hEn | hqj
    · exact hEn
    · exact absurd hqj (hqall j)
  have hInfEn :
      always (eventually (statePred (Enabled (AngleAction A v)))) (e.drop k) := by
    intro j
    exact ⟨0, by simpa using hen j⟩
  have hSF : eventually (actionPred (AngleAction A v)) (e.drop k) :=
    h.2 k hInfEn
  rcases hSF with ⟨j, hA⟩
  have hA' : AngleAction A v (e (k + j)) (e (k + j + 1)) := by
    simpa using hA
  exact hqall (j + 1) (haq _ _ (hp j) hA')

end Bft
