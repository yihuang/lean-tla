import Bft.Core
import Bft.Rules
import Mathlib.Data.Set.Card
import Mathlib.Order.WellFounded
import Mathlib.Order.PiLex

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

/-- 严格字典序（首个不同分量严格更小、之前分量相等）well-founded：
对 `n` 归纳，用 `WellFounded.prod_lex` 拆掉头分量。
（移植自 TlaDsl/RelRank.lean 已机器检查版本。） -/
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

/-- `VecLexLess` 嵌入严格字典序：取向量不同的最小下标 `j₀`；`j₀` 处严格
下降（单调条件给出不增），更早分量相等。 -/
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

/-- `VecLexLess` well-founded（Theorem 1）。 -/
theorem vecLexLess_wellFounded : ∀ (n : ℕ), WellFounded (@VecLexLess n) := by
  intro n
  exact WellFounded.mono (piLexNat_wellFounded n) (fun x y h => vecLexLess_imp_piLex h)

/-- 分量 `i` 被抢占：存在更高优先级的 scheduler 处于开启。 -/
def Pre {σ : Type u} {n : ℕ} (ψs : Fin n → σ → Prop) (i : Fin n) (s : σ) : Prop :=
  ∃ j : Fin n, j.val < i.val ∧ ψs j s

/-- 分量 `i` 被需要：开启且未被抢占。 -/
def Req {σ : Type u} {n : ℕ} (ψs : Fin n → σ → Prop) (i : Fin n) (s : σ) : Prop :=
  ψs i s ∧ ¬ Pre ψs i s

/-! ### Finset 值 ranking 的辅助定义 -/

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

/-- 后续位置的 `◇q` 提升回前面的后缀。 -/
theorem eventually_statePred_lift {σ : Type u} (q : StatePred σ) (e : Behavior σ)
    (k t : ℕ) (h : eventually (statePred q) (e.drop (k + t))) :
    eventually (statePred q) (e.drop k) := by
  rw [eventually_statePred_drop] at h ⊢
  rcases h with ⟨m, hm⟩
  exact ⟨t + m, by simpa [Nat.add_assoc] using hm⟩

/-- L2 步形状（论文 Rule 10）。 -/
def L2Step {σ : Type u} {α : Type v} {n : ℕ} (q : StatePred σ) (φ : StatePred σ)
    (δs : Fin n → σ → Finset α) (ψs : Fin n → σ → Prop) (rs : Fin n → Action σ)
    (e : Behavior σ) (k : ℕ) : Prop :=
  eventually (statePred q) (e.drop k) ∨
    (φ (e (k + 1)) ∧
     (∀ i : Fin n, ¬ Pre ψs i (e k) → ConservesFinset (δs i) (e k) (e (k + 1))) ∧
     (∀ i : Fin n, Req ψs i (e k) → rs i (e k) (e (k + 1)) →
       ReducesFinset (δs i) (e k) (e (k + 1))) ∧
     (∀ i : Fin n, Req ψs i (e k) → ¬ rs i (e k) (e (k + 1)) → ψs i (e (k + 1))))

/-- Walk A+B：`¬◇q` 下 L2 保持 `φ` 且 conserve 所有未被抢占的分量。 -/
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

/-- Walk C：justice 未触发期间，被需要的 scheduler `ψ_l` 保持到首次触发。 -/
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

/-- 从 `k` 起曾经被调度的最小下标：`Fin n` 上取最小元；比它小的下标
永不调度，因此它及其以下永不抢占。 -/
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

/-- Rule 10（论文）：字典序 relational ranking + stable scheduler。
soundness：取最小被调度下标 `l`（`min_ever_scheduled`），它永不抢占，
高优先级分量 conserve 有界（`walk_below`）；其 justice 最终触发（S3），
由稳定性在首次触发时严格缩小（`sched_persist` +
`card_lt_card_of_reduce`）；cardinality 向量在 `VecLexLess` 中严格下降，
由 `vecLexLess_wellFounded` 终止。
（移植自 TlaDsl/RelRank.lean 已机器检查版本。） -/
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

/-- Rule 10 结论：直接应用 `rel_rank_lex`，把证书字段转换为其前提形状。

**两处陈述修正（相对初版草案，均在写证明时发现）**：

1. 初版的 `hjustice` 以 `Req ψs i` 为前件，弱于论文的 S3（任意**开启**
   的 justice 最终触发，包括被抢占的分量）。虽然 soundness 证明只在
   无抢占点调用 S3，但 `rel_rank_lex` 的前提对全部 `i` 量化，故证书
   必须提供全强度 S3。本版改为 `cert.ψs i` 前件。
2. 初版遗漏 S4（任一时刻至少一个 scheduler 开启）。没有 S4 该陈述是
   **假的**：常值行为上 φ 恒真、所有 δs 为空、无 scheduler 时全部前提
   vacuous 成立而 q 永不发生。本版补上 `hsched`。 -/
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
