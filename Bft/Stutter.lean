import Bft.Core

/-!
# Bft.Stutter — stuttering invariance 的 typeclass 方案

`SI F`（stutter-invariant）表示公式 `F` 在单步 stutter 的插入/删除下不变。
这两类变换生成**有限** stuttering 等价；无限 stutter 闭包（即 TLA 全语义，
对应 lean-tla 的 `SimFull` / run compression）不在本层处理——见
docs/design.md §2.3 的诚实说明。

设计要点：`SI` 是 `Prop` 值 class，全部组合子配 instance。DSL 生成的公式
经 TC 推断自动获得合法性证明；用户手写裸 `Pred` 时推断失败、在 `refine`
处显式报缺——合法性从"事后纪律"变成"推断时检查"。

本文件的 sorry 均附证明方案；难点只有一个（`stutAlways` 的 SI），它是
TLA 元理论里标准的非平凡定理。
-/

namespace Bft

/-- 删除位置 `n`（仅当 `e n = e (n+1)` 时是合法 stutter 删除）。
经 `Coe (ℕ → σ) (ωSequence σ)` 构造；应用形式的归约引理是
`Cslib.ωSequence.get_fun`（`@[simp]` 候选）。 -/
def removeAt {σ : Type u} (e : Behavior σ) (n : ℕ) : Behavior σ :=
  fun m => if m < n then e m else e (m + 1)

/-- 在位置 `n` 后插入一份 `e n` 的拷贝：位置 `n` 与 `n+1` 都是 `e n`。 -/
def insertAt {σ : Type u} (e : Behavior σ) (n : ℕ) : Behavior σ :=
  fun m => if m ≤ n then e m else e (m - 1)

@[simp] theorem removeAt_apply {σ : Type u} (e : Behavior σ) (n m : ℕ) :
    removeAt e n m = if m < n then e m else e (m + 1) := rfl

@[simp] theorem insertAt_apply {σ : Type u} (e : Behavior σ) (n m : ℕ) :
    insertAt e n m = if m ≤ n then e m else e (m - 1) := rfl

/-- 有限 stuttering 不变性。 -/
def StutterInvariant {σ : Type u} (F : Pred σ) : Prop :=
  (∀ e n, e n = e (n + 1) → (F (removeAt e n) ↔ F e)) ∧
    (∀ e n, F (insertAt e n) ↔ F e)

/-- typeclass 包装：让合法性子目标走实例推断。 -/
class SI {σ : Type u} (F : Pred σ) : Prop where
  inv : StutterInvariant F

/-! ## 基础 instance -/

/-- 状态谓词只读首状态；stutter 不改变首状态（删除时用到 `e n = e (n+1)`）。 -/
instance {σ : Type u} (p : StatePred σ) : SI (statePred p) where
  inv := by
    constructor
    · intro e n hst
      show p (removeAt e n 0) ↔ p (e 0)
      rw [removeAt_apply]
      by_cases hn : 0 < n
      · simp [hn]
      · have hn0 : n = 0 := by omega
        subst hn0; simp [hst]
    · intro e n
      show p (insertAt e n 0) ↔ p (e 0)
      simp

/-- 纯命题与行为无关。 -/
instance {σ : Type u} (p : Prop) : SI (purePred (σ := σ) p) where
  inv := ⟨fun _ _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

/-! ## 组合子保持 SI

通用模式：`F` 的插入等价式对每个后缀逐点使用。以 `always` 为例给出完整
证明结构；`eventually`/`leadsTo` 同理。 -/

/-- 辅助：对 `insertAt e n` 的位置 `m` 取后缀，等于对 `e` 的某个位置取后缀
再做一次插入/恒等。具体地：
  - `m ≤ n` 时 `drop m (insertAt e n) = insertAt (drop m e) (n - m)`；
  - `m > n` 时 `drop m (insertAt e n) = drop (m - 1) e`。
两者都是 `funext` + `omega` 级别的算术，此处陈述，证明略（draft）。 -/
theorem drop_insertAt {σ : Type u} (e : Behavior σ) (n m : ℕ) :
    drop m (insertAt e n) =
      if m ≤ n then insertAt (drop m e) (n - m) else drop (m - 1) e := by
  ext k
  by_cases hm : m ≤ n
  · simp [hm]
    by_cases hk : k ≤ n - m
    · have hmk : m + k ≤ n := by omega
      simp [hk, hmk]
    · have hmk : ¬ m + k ≤ n := by omega
      have hsub : m + k - 1 = m + (k - 1) := by omega
      simp [hk, hmk, hsub]
  · have hmk : ¬ m + k ≤ n := by omega
    have hsub : m + k - 1 = (m - 1) + k := by omega
    simp [hm, hmk, hsub]

/-- `□` 保持 SI：后缀逐个用 `F` 的 SI 归纳。 -/
instance {σ : Type u} (F : Pred σ) [SI F] : SI (always F) where
  inv := by
    obtain ⟨hrem, hins⟩ := SI.inv (F := F)
    constructor
    · intro e n hst
      -- 证明方案：`removeAt e n` 的每个后缀要么是 `e` 的后缀，要么是
      -- `e` 某后缀删除首步 stutter 的结果；两方向分别用 `hrem`。需要一个
      -- `drop_removeAt` 引理（与 `drop_insertAt` 对偶，同样 funext+omega）。
      sorry
    · intro e n
      constructor
      · intro h m
        by_cases hm : m ≤ n
        · have hd : drop m (insertAt e n) = insertAt (drop m e) (n - m) := by
            rw [drop_insertAt]
            simp [hm]
          exact (hins (drop m e) (n - m)).1 (by simpa [hd] using h m)
        · have hd : drop (m + 1) (insertAt e n) = drop m e := by
            have hm1 : ¬ m + 1 ≤ n := by omega
            rw [drop_insertAt]
            simp [hm1]
          exact (by simpa [hd] using h (m + 1))
      · intro h m
        by_cases hm : m ≤ n
        · simp [drop_insertAt, hm]
          exact (hins (drop m e) (n - m)).2 (h m)
        · simp [drop_insertAt, hm]
          exact h (m - 1)

/-- `◇` 保持 SI。证明方案同 `always`（对偶），draft 标记。 -/
instance {σ : Type u} (F : Pred σ) [SI F] : SI (eventually F) where
  inv := sorry

instance {σ : Type u} (F G : Pred σ) [SI F] [SI G] : SI (tlaAnd F G) where
  inv := by
    obtain ⟨hremF, hinsF⟩ := SI.inv (F := F)
    obtain ⟨hremG, hinsG⟩ := SI.inv (F := G)
    refine ⟨fun e n hst => ?_, fun e n => ?_⟩
    · simp [tlaAnd, hremF e n hst, hremG e n hst]
    · simp [tlaAnd, hinsF e n, hinsG e n]

instance {σ : Type u} (F G : Pred σ) [SI F] [SI G] : SI (tlaOr F G) where
  inv := by
    obtain ⟨hremF, hinsF⟩ := SI.inv (F := F)
    obtain ⟨hremG, hinsG⟩ := SI.inv (F := G)
    refine ⟨fun e n hst => ?_, fun e n => ?_⟩
    · simp [tlaOr, hremF e n hst, hremG e n hst]
    · simp [tlaOr, hinsF e n, hinsG e n]

/-- 注意：`tlaImp` **不**一般保持 SI（`⇒` 的反单调性在反例分支上失败是
TLA 里的经典现象：蕴含不是 stuttering-safe 的组合子，合法的 TLA 语法只允许
它在受限位置出现）。`leadsTo` 是安全的，因为它的形状是 `□(P ⇒ ◇Q)`。 -/
instance {σ : Type u} (P Q : Pred σ) [SI P] [SI Q] : SI (leadsTo P Q) where
  inv := sorry -- 证明方案：展开为 `□(P ⇒ ◇Q)` 后直接对后缀推理；关键步是
  -- `eventually Q` 在插入点两侧的等价（已有 `eventually` 的 SI）。
  -- draft 标记。

/-- `□[A]_v` 是 SI：TLA 元理论的标准定理，也是整个框架的合法性地基。
证明方案（lean-tla `Meta.lean`/`SimFull.lean` 已完成同构版本）：
对插入的 stutter 步，它自身满足 `Unchanged v` 析取支；删除 stutter 步时，
相邻两步 `[A]_v` 的析取支合并：若任一支是 `A`，需把两段 `A` 合成一段——
注意这里 **不成立**于任意 `A`，标准论证是对 `v` 的值域归纳 stutter 段长度，
把 `[A]_v` 段重新切分。这是本文件唯一的实质证明缺口，建议直接从
SimFull 方向的 run-compression 定理移植。 -/
instance {σ : Type u} {α : Type v} (A : Action σ) (v : σ → α) :
    SI (stutAlways A v) where
  inv := sorry

/-- `WF_v` / `SF_v` 的 SI 由 `stutAlways` 与 `eventually` 的 SI 组合得到。 -/
instance {σ : Type u} {α : Type v} (A : Action σ) (v : σ → α) : SI (WF_v A v) where
  inv := sorry -- 由上述 instance 组合，draft 标记

instance {σ : Type u} {α : Type v} (A : Action σ) (v : σ → α) : SI (SF_v A v) where
  inv := sorry -- 同上

end Bft
