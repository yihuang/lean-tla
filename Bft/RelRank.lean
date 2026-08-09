import Bft.Core
import Bft.Rules
import Mathlib.Data.Set.Card

/-!
# Bft.RelRank — relational ranking 活性引擎（McMillan CAV 2024）

引擎化设计（docs/design.md §3）：

1. **规则即证书**：`RelRankCert` 把一次 Rule 6 应用的全部见证（φ, δ, R, r
   与义务证明）打包成可存储、可组合、可打印的对象；
2. **组合子**：`RelRankCert.trans`（Rule 7 链接）把两个证书合成一个；
   字典序/参数化组合子（Rule 10/11）以同样方式给出（draft 陈述）；
3. **义务形状**：C1–C3 全部是单步安全式性质，供 tactic 层
   （`Bft/Tactic.lean` 的义务规范化器 + grind）自动 discharge。

`drop` 的 pointwise normal form 在 `Core` 里是定义等式，所以 descent
证明里没有 suffix 重写链。
-/

namespace Bft

/-! ## Conserve / Reduce -/

/-- 一步 conserve `δ`：不增加元素。 -/
def Conserves {σ : Type u} {α : Type v} (δ : σ → α → Prop) (s s' : σ) : Prop :=
  ∀ x, δ s' x → δ s x

/-- 一步 reduce `δ`：至少移除一个元素。 -/
def Reduces {σ : Type u} {α : Type v} (δ : σ → α → Prop) (s s' : σ) : Prop :=
  ∃ x, δ s x ∧ ¬ δ s' x

/-! ## Rule 5：有限性由归纳得到 -/

/-- 若 `R` 初始为空、每步至多增加有限多元素，则 `R` 在每个有限时刻有限。 -/
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

/-! ## descent 三助手 -/

/-- conserve + reduce + finite ⇒ 基数严格下降。 -/
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

/-- walk：`φ` 成立期间，要么先到达 `q`，要么 `φ` 持续、`δ` 逐步 conserve
且保持在起点外延之内。 -/
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

/-- soundness 核心：`|δ|` 的有限下降。 -/
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

/-! ## Rule 6：relational reactivity rule -/

/-- Rule 6：在 `H ∧ □◇⟨r⟩` 下 `p ↝ q`。 -/
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

/-! ## 证书 -/

/-- Rule 6 证书：一次活性证明的全部见证，可存储/组合/打印。
`α` 由 δ 决定，作为结构体的 outParam 出现。 -/
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

/-- 证书给出 leads-to 结论。 -/
theorem RelRankCert.toLeadsTo {σ : Type u} {p q : StatePred σ}
    (cert : RelRankCert σ p q) :
    Entails (tlaAnd cert.H (globalJustice cert.r))
      (leadsTo (statePred p) (statePred q)) :=
  relational_ranking_rule p q cert.r cert.φ cert.δ cert.R cert.H
    cert.finiteness cert.c1 cert.c2 cert.c3

/-- Rule 7（链接）：两个证书合成 `p ↝ r'`。
注意义务前提放宽为 `◇` 形式：第二个证书的结论在第一个证书的
C2/C3 分支里以 `∃ m, q (e (· + m))` 出现，正是 `rank_descent`
hD2/hD3 的左析取支形状——组合在 descent 层完成，不需要二次归纳。 -/
theorem RelRankCert.trans {σ : Type u} {p q q' : StatePred σ}
    (cert₁ : RelRankCert σ p q)
    (cert₂ : RelRankCert σ q q')
    (hH : ∀ e, tlaAnd cert₁.H (globalJustice cert₁.r) e →
      tlaAnd cert₂.H (globalJustice cert₂.r) e) :
    Entails (tlaAnd cert₁.H (globalJustice cert₁.r))
      (leadsTo (statePred p) (statePred q')) := by
  intro e hE k hpk
  -- 证书一：`p ↝ q`
  have h1 : (leadsTo (statePred p) (statePred q)) e := cert₁.toLeadsTo e hE
  -- 证书二在所达环境下：`q ↝ q'`
  have h2 : (leadsTo (statePred q) (statePred q')) e :=
    cert₂.toLeadsTo e (hH e hE)
  exact (leadsTo_trans (statePred p) (statePred q) (statePred q')) e ⟨h1, h2⟩ k hpk

/-! ## Rule 10/11：字典序与参数化组合子（draft 陈述）

`VecLexLess`/`piLexNat_wellFounded` 等 well-foundedness 事实在 lean-tla
`RelRank.lean` 已机器检查，可直接移植；此处给出引擎接口的陈述，证明
标记 draft。 -/

/-- 单调字典序：某个分量严格下降、更高优先级分量不增。 -/
def VecLexLess {n : ℕ} (x y : Fin n → ℕ) : Prop :=
  ∃ i : Fin n, (∀ j : Fin n, j.val < i.val → x j ≤ y j) ∧ x i < y i

/-- `VecLexLess` well-founded（Theorem 1）。draft。 -/
theorem vecLexLess_wellFounded : ∀ n : ℕ, WellFounded (@VecLexLess n) := sorry

/-- 分量 `i` 被抢占：存在更高优先级的 scheduler 处于开启。 -/
def Pre {σ : Type u} {n : ℕ} (ψs : Fin n → σ → Prop) (i : Fin n) (s : σ) : Prop :=
  ∃ j : Fin n, j.val < i.val ∧ ψs j s

/-- 分量 `i` 被需要：开启且未被抢占。 -/
def Req {σ : Type u} {n : ℕ} (ψs : Fin n → σ → Prop) (i : Fin n) (s : σ) : Prop :=
  ψs i s ∧ ¬ Pre ψs i s

/-- Rule 10 证书（字典序 + stable scheduler）。draft：字段即论文
L2/P3/P4 前提的逐条对应。 -/
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

/-- Rule 10 结论。draft：descent 在 cardinality 向量的 `VecLexLess` 上进行，
结构同 `rank_descent`，归纳原理换为 `vecLexLess_wellFounded`。 -/
theorem LexRankCert.toLeadsTo {σ : Type u} {p q : StatePred σ}
    (cert : LexRankCert σ p q)
    (hjustice : ∀ e, cert.H e → ∀ k : ℕ, cert.φ (e k) → ∀ i : Fin cert.n,
      Req cert.ψs i (e k) →
      (∃ m, q (e (k + m))) ∨ (∃ m, cert.rs i (e (k + m)) (e (k + m + 1)))) :
    Entails cert.H (leadsTo (statePred p) (statePred q)) := sorry

end Bft
