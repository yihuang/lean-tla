import Bft.Core

/-!
# Bft.Stutter — stuttering invariance 的 typeclass 方案

`SI F`（stutter-invariant）表示公式 `F` 在单步 stutter 的插入/删除下不变。
这两类变换生成**有限** stuttering 等价；无限 stutter 闭包（即 TLA 全语义，
对应 lean-tla 的 `SimFull` / run compression）不在本层处理——见
docs/bft-design.md §2.3 的诚实说明。

设计要点：`SI` 是 `Prop` 值 class，全部组合子配 instance。DSL 生成的公式
经 TC 推断自动获得合法性证明；用户手写裸 `Pred` 时推断失败、在 `refine`
处显式报缺——合法性从"事后纪律"变成"推断时检查"。

证明组织：

* `drop_insertAt`/`drop_removeAt`：后缀与插入/删除的交换律（全部
  `ext` + `omega`），一律用 `ωSequence.drop` 点记法陈述，保证与
  `always`/`eventually` 展开后的目标头常量一致；
* `si_forall_suffix_imp`：**核心模式引理**——形如
  `fun e => ∀ k, X (e.drop k) → Y (e.drop k)` 的公式在 `SI X`、`SI Y`
  下是 SI。`leadsTo`（`X = P, Y = ◇Q`）、`WF_v`、`SF_v` 全部是它的实例；
* `stutAlways` 的 SI 是**直接的逐点论证**（不是元理论深水区）：
  插入的重复步满足 `Unchanged v` 析取支；删除 stutter 步后每个剩余步
  仍是原行为的步或 stutter。

## 边界注记（改错记录）

* 删除点跨越引理取 `(removeAt e n).drop (k-1) = e.drop k`（`n < k`），
  删除从位置 `n` 起整体左移；
* 插入引理只有 `(insertAt e n).drop k = e.drop (k-1)`（`n < k`）方向
  成立——`(insertAt e n).drop (k-1) = e.drop k` 在 `k-1 = n` 处为假
  （首位置是 `e n` 而非 `e (n+1)`），证明中必须绕开这个假形式。
-/

namespace Bft

/-- 删除位置 `n`（仅当 `e n = e (n+1)` 时是合法 stutter 删除）。 -/
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

/-! ## 后缀交换律 -/

theorem drop_insertAt {σ : Type u} (e : Behavior σ) (n m : ℕ) :
    (insertAt e n).drop m =
      if m ≤ n then insertAt (e.drop m) (n - m) else e.drop (m - 1) := by
  ext k
  by_cases hm : m ≤ n
  · rw [if_pos hm]
    simp only [Cslib.ωSequence.get_drop, insertAt_apply]
    by_cases hk : k ≤ n - m
    · have hmk : m + k ≤ n := by omega
      simp [hk, hmk]
    · have hmk : ¬ m + k ≤ n := by omega
      have hsub : m + k - 1 = m + (k - 1) := by omega
      simp [hk, hmk, hsub]
  · rw [if_neg hm]
    simp only [Cslib.ωSequence.get_drop, insertAt_apply]
    have hmk : ¬ m + k ≤ n := by omega
    simp only [hmk, if_false]
    congr 1
    omega

theorem drop_removeAt {σ : Type u} (e : Behavior σ) (n m : ℕ) :
    (removeAt e n).drop m =
      if m ≤ n then removeAt (e.drop m) (n - m) else e.drop (m + 1) := by
  ext k
  by_cases hm : m ≤ n
  · rw [if_pos hm]
    simp only [Cslib.ωSequence.get_drop, removeAt_apply]
    by_cases hk : m + k < n
    · have hk' : k < n - m := by omega
      simp [hk, hk']
    · have hk' : ¬ k < n - m := by omega
      have hsub : m + k + 1 = m + (k + 1) := by omega
      simp [hk, hk', hsub]
  · rw [if_neg hm]
    simp only [Cslib.ωSequence.get_drop, removeAt_apply]
    have hmk : ¬ m + k < n := by omega
    simp only [hmk, if_false]
    congr 1
    omega

/-- 删除合法性条件在后缀层面的形式：`e n = e (n+1)` 且 `k ≤ n` 时，
`e.drop k` 在位置 `n - k` 处 stutter。 -/
theorem drop_removeAt_cond {σ : Type u} (e : Behavior σ) {n k : ℕ}
    (hst : e n = e (n + 1)) (hk : k ≤ n) :
    (e.drop k) (n - k) = (e.drop k) (n - k + 1) := by
  have h1 : k + (n - k) = n := by omega
  have h2 : k + (n - k + 1) = n + 1 := by omega
  rw [Cslib.ωSequence.get_drop, Cslib.ωSequence.get_drop, h1, h2]
  exact hst

/-- 跨越删除点的后缀：`n < k` 时 `(removeAt e n).drop (k-1) = e.drop k`。 -/
theorem drop_removeAt_pred {σ : Type u} (e : Behavior σ) {n k : ℕ} (hk : n < k) :
    (removeAt e n).drop (k - 1) = e.drop k := by
  ext m
  simp only [Cslib.ωSequence.get_drop, removeAt_apply]
  have h1 : ¬ k - 1 + m < n := by omega
  simp only [h1, if_false]
  congr 1
  omega

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

/-! ## 组合子保持 SI -/

/-- `□` 保持 SI。 -/
instance {σ : Type u} (F : Pred σ) [SI F] : SI (always F) where
  inv := by
    obtain ⟨hrem, hins⟩ := SI.inv (F := F)
    constructor
    · intro e n hst
      constructor
      · intro h m
        by_cases hm : m ≤ n
        · have h1 := h m
          rw [drop_removeAt, if_pos hm] at h1
          exact (hrem (e.drop m) (n - m) (drop_removeAt_cond e hst hm)).1 h1
        · have h1 := h (m - 1)
          rwa [drop_removeAt_pred e (by omega : n < m)] at h1
      · intro h m
        by_cases hm : m ≤ n
        · have h1 := h m
          rw [drop_removeAt, if_pos hm]
          exact (hrem (e.drop m) (n - m) (drop_removeAt_cond e hst hm)).2 h1
        · have h1 := h (m + 1)
          rwa [drop_removeAt, if_neg hm]
    · intro e n
      constructor
      · intro h m
        by_cases hm : m ≤ n
        · have h1 := h m
          rw [drop_insertAt, if_pos hm] at h1
          exact (hins (e.drop m) (n - m)).1 h1
        · have h1 := h (m + 1)
          rw [drop_insertAt, if_neg (by omega : ¬ m + 1 ≤ n)] at h1
          rwa [show m + 1 - 1 = m from by omega] at h1
      · intro h m
        by_cases hm : m ≤ n
        · have h1 := h m
          rw [drop_insertAt, if_pos hm]
          exact (hins (e.drop m) (n - m)).2 h1
        · have h1 := h (m - 1)
          rwa [drop_insertAt, if_neg hm]

/-- `◇` 保持 SI（`□` 的对偶）。 -/
instance {σ : Type u} (F : Pred σ) [SI F] : SI (eventually F) where
  inv := by
    obtain ⟨hrem, hins⟩ := SI.inv (F := F)
    constructor
    · intro e n hst
      constructor
      · rintro ⟨m, hm⟩
        by_cases hmk : m ≤ n
        · rw [drop_removeAt, if_pos hmk] at hm
          exact ⟨m, (hrem (e.drop m) (n - m) (drop_removeAt_cond e hst hmk)).1 hm⟩
        · rw [drop_removeAt, if_neg hmk] at hm
          exact ⟨m + 1, hm⟩
      · rintro ⟨m, hm⟩
        by_cases hmk : m ≤ n
        · refine ⟨m, ?_⟩
          rw [drop_removeAt, if_pos hmk]
          exact (hrem (e.drop m) (n - m) (drop_removeAt_cond e hst hmk)).2 hm
        · refine ⟨m - 1, ?_⟩
          rw [drop_removeAt_pred e (by omega : n < m)]
          exact hm
    · intro e n
      constructor
      · rintro ⟨m, hm⟩
        by_cases hmk : m ≤ n
        · rw [drop_insertAt, if_pos hmk] at hm
          exact ⟨m, (hins (e.drop m) (n - m)).1 hm⟩
        · rw [drop_insertAt, if_neg hmk] at hm
          exact ⟨m - 1, hm⟩
      · rintro ⟨m, hm⟩
        by_cases hmk : m ≤ n
        · refine ⟨m, ?_⟩
          rw [drop_insertAt, if_pos hmk]
          exact (hins (e.drop m) (n - m)).2 hm
        · refine ⟨m + 1, ?_⟩
          rw [drop_insertAt, if_neg (by omega : ¬ m + 1 ≤ n),
            show m + 1 - 1 = m from by omega]
          exact hm

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

/-! ## 核心模式引理：后缀蕴含保持 SI

`leadsTo`/`WF_v`/`SF_v` 都是 `∀ k, X (e.drop k) → Y (e.drop k)` 的形状。
注意 `tlaImp` 自身**不**保持 SI（蕴含的反单调性），但后缀量化把它锁在
安全位置。 -/

theorem si_forall_suffix_imp {σ : Type u} (X Y : Pred σ) [SI X] [SI Y] :
    StutterInvariant (fun e => ∀ k, X (e.drop k) → Y (e.drop k)) := by
  obtain ⟨hremX, hinsX⟩ := SI.inv (F := X)
  obtain ⟨hremY, hinsY⟩ := SI.inv (F := Y)
  constructor
  · intro e n hst
    constructor
    · intro h k hXk
      by_cases hk : k ≤ n
      · have hst' := drop_removeAt_cond e hst hk
        have hX' : X ((removeAt e n).drop k) := by
          rw [drop_removeAt, if_pos hk]
          exact (hremX (e.drop k) (n - k) hst').2 hXk
        have hY' := h k hX'
        rw [drop_removeAt, if_pos hk] at hY'
        exact (hremY (e.drop k) (n - k) hst').1 hY'
      · have hkey := drop_removeAt_pred e (show n < k by omega)
        have hX' : X ((removeAt e n).drop (k - 1)) := by rwa [hkey]
        have hY' := h (k - 1) hX'
        rwa [hkey] at hY'
    · intro h k hXk
      by_cases hk : k ≤ n
      · have hst' := drop_removeAt_cond e hst hk
        rw [drop_removeAt, if_pos hk] at hXk
        have hX' := (hremX (e.drop k) (n - k) hst').1 hXk
        have hY' := h k hX'
        rw [drop_removeAt, if_pos hk]
        exact (hremY (e.drop k) (n - k) hst').2 hY'
      · rw [drop_removeAt, if_neg hk] at hXk ⊢
        exact h (k + 1) hXk
  · intro e n
    constructor
    · intro h k hXk
      by_cases hk : k ≤ n
      · have hX' : X ((insertAt e n).drop k) := by
          rw [drop_insertAt, if_pos hk]
          exact (hinsX (e.drop k) (n - k)).2 hXk
        have hY' := h k hX'
        rw [drop_insertAt, if_pos hk] at hY'
        exact (hinsY (e.drop k) (n - k)).1 hY'
      · -- 注意：这里必须用 `k + 1` 而非 `k - 1`——插入点之后整体右移，
        -- `(insertAt e n).drop (k+1) = e.drop k`。
        have hX' : X ((insertAt e n).drop (k + 1)) := by
          rw [drop_insertAt, if_neg (by omega : ¬ k + 1 ≤ n),
            show k + 1 - 1 = k from by omega]
          exact hXk
        have hY' := h (k + 1) hX'
        rwa [drop_insertAt, if_neg (by omega : ¬ k + 1 ≤ n),
          show k + 1 - 1 = k from by omega] at hY'
    · intro h k hXk
      by_cases hk : k ≤ n
      · rw [drop_insertAt, if_pos hk] at hXk ⊢
        exact (hinsY (e.drop k) (n - k)).2 (h k ((hinsX (e.drop k) (n - k)).1 hXk))
      · rw [drop_insertAt, if_neg hk] at hXk ⊢
        exact h (k - 1) hXk

/-- `leadsTo P Q = ∀ k, P (e.drop k) → ◇Q (e.drop k)`。 -/
instance {σ : Type u} (P Q : Pred σ) [SI P] [SI Q] : SI (leadsTo P Q) where
  inv := si_forall_suffix_imp P (eventually Q)

/-! ## `□[A]_v` 的 SI：直接逐点论证 -/

/-- `□[A]_v` 是 SI：插入的重复步满足 `Unchanged v` 析取支；删除 stutter
步后每个剩余步仍是原行为的步（跨越点处由 `e n = e (n+1)` 保证）。 -/
instance {σ : Type u} {α : Type v} (A : Action σ) (v : σ → α) :
    SI (stutAlways A v) where
  inv := by
    constructor
    · intro e n hst
      simp only [stutAlways, always, actionPred_drop]
      constructor
      · intro h m
        by_cases hm : m < n
        · have h1 := h m
          by_cases hm1 : m + 1 < n
          · rwa [removeAt_apply, removeAt_apply, if_pos hm, if_pos hm1] at h1
          · have hmn : m + 1 = n := by omega
            rw [removeAt_apply, removeAt_apply, if_pos hm, if_neg hm1] at h1
            -- h1 : StutAction A v (e m) (e (m+1+1))；e (n+1) = e n（hst 对称）
            have e1 : m + 1 + 1 = n + 1 := by omega
            rw [e1, ← hst, ← hmn] at h1
            exact h1
        · by_cases hmn : m = n
          · subst hmn
            -- (e n, e (n+1)) 是 stutter 步：Unchanged 析取支
            exact Or.inr (by rw [hst])
          · have h1 := h (m - 1)
            have h2 : ¬ m - 1 < n := by omega
            have h3 : ¬ m - 1 + 1 < n := by omega
            rw [removeAt_apply, removeAt_apply, if_neg h2, if_neg h3] at h1
            rw [show m - 1 + 1 = m from by omega] at h1
            exact h1
      · intro h m
        by_cases hm1 : m + 1 < n
        · rw [removeAt_apply, removeAt_apply, if_pos (by omega : m < n), if_pos hm1]
          exact h m
        · by_cases hm : m < n
          · -- m + 1 = n：跨越删除点，第二分量为 e (n+1) = e n（hst 对称）
            have e2 : m + 1 = n := by omega
            rw [removeAt_apply, removeAt_apply, if_pos hm, if_neg hm1]
            have e1 : m + 1 + 1 = n + 1 := by omega
            rw [e1, ← hst, ← e2]
            exact h m
          · rw [removeAt_apply, removeAt_apply, if_neg hm, if_neg hm1]
            exact h (m + 1)
    · intro e n
      simp only [stutAlways, always, actionPred_drop]
      constructor
      · intro h m
        by_cases hm : m < n
        · have h1 := h m
          rwa [insertAt_apply, insertAt_apply, if_pos (by omega : m ≤ n),
            if_pos (by omega : m + 1 ≤ n)] at h1
        · by_cases hmn : m = n
          · subst hmn
            have h1 := h (m + 1)
            rwa [insertAt_apply, insertAt_apply, if_neg (by omega : ¬ m + 1 ≤ m),
              if_neg (by omega : ¬ m + 1 + 1 ≤ m)] at h1
          · have h1 := h (m + 1)
            rwa [insertAt_apply, insertAt_apply, if_neg (by omega : ¬ m + 1 ≤ n),
              if_neg (by omega : ¬ m + 1 + 1 ≤ n)] at h1
      · intro h m
        by_cases hm : m < n
        · rw [insertAt_apply, insertAt_apply, if_pos (by omega : m ≤ n),
            if_pos (by omega : m + 1 ≤ n)]
          exact h m
        · by_cases hmn : m = n
          · subst hmn
            -- 插入的重复步 (e m, e m)：Unchanged 析取支
            rw [insertAt_apply, insertAt_apply, if_pos (le_refl m),
              if_neg (by omega : ¬ m + 1 ≤ m)]
            exact Or.inr rfl
          · rw [insertAt_apply, insertAt_apply, if_neg (by omega : ¬ m ≤ n),
              if_neg (by omega : ¬ m + 1 ≤ n)]
            have h1 := h (m - 1)
            rwa [show m - 1 + 1 = m from by omega] at h1

/-! ## `WF_v` / `SF_v` 的 SI

`eventually (actionPred ⟨A⟩_v)` 是 SI（尽管 `actionPred` 本身不是）：
`⟨A⟩_v` 要求 `v` 改变，stutter 步永远不触发，所以插入/删除只在
两侧平移触发位置。 -/

theorem si_eventually_angle {σ : Type u} {α : Type v} (A : Action σ) (v : σ → α) :
    StutterInvariant (eventually (actionPred (AngleAction A v))) := by
  constructor
  · intro e n hst
    simp only [eventually, actionPred_drop]
    constructor
    · rintro ⟨m, hm⟩
      by_cases hm1 : m + 1 < n
      · refine ⟨m, ?_⟩
        rwa [removeAt_apply, removeAt_apply, if_pos (by omega : m < n), if_pos hm1]
          at hm
      · by_cases hmn : m < n
        · -- m + 1 = n：removeAt 的第 m 步是 (e m, e (n+1))，由 hst 即 (e m, e n)
          have e2 : m + 1 = n := by omega
          refine ⟨m, ?_⟩
          rw [removeAt_apply, removeAt_apply, if_pos hmn, if_neg hm1] at hm
          have e1 : m + 1 + 1 = n + 1 := by omega
          rwa [e1, ← hst, ← e2] at hm
        · refine ⟨m + 1, ?_⟩
          rwa [removeAt_apply, removeAt_apply, if_neg hmn,
            if_neg (by omega : ¬ m + 1 < n)] at hm
    · rintro ⟨m, hm⟩
      by_cases hm1 : m + 1 < n
      · refine ⟨m, ?_⟩
        rwa [removeAt_apply, removeAt_apply, if_pos (by omega : m < n), if_pos hm1]
      · by_cases hmn : m < n
        · -- m + 1 = n：目标第二分量为 e (n+1)，由 hst 等于 e n
          have e2 : m + 1 = n := by omega
          refine ⟨m, ?_⟩
          rw [removeAt_apply, removeAt_apply, if_pos hmn, if_neg hm1]
          have e1 : m + 1 + 1 = n + 1 := by omega
          rwa [e1, ← hst, ← e2]
        · by_cases hmn2 : m = n
          · -- e 的第 n 步是 stutter：`⟨A⟩_v` 不可能触发，矛盾
            subst hmn2
            exact absurd (by rw [← hst]) hm.2
          · refine ⟨m - 1, ?_⟩
            rw [removeAt_apply, removeAt_apply, if_neg (by omega : ¬ m - 1 < n),
              if_neg (by omega : ¬ m - 1 + 1 < n),
              show m - 1 + 1 = m from by omega]
            exact hm
  · intro e n
    simp only [eventually, actionPred_drop]
    constructor
    · rintro ⟨m, hm⟩
      by_cases hmn : m < n
      · refine ⟨m, ?_⟩
        rwa [insertAt_apply, insertAt_apply, if_pos (by omega : m ≤ n),
          if_pos (by omega : m + 1 ≤ n)] at hm
      · by_cases hmn2 : m = n
        · -- 插入的 stutter 步不触发 `⟨A⟩_v`：矛盾
          subst hmn2
          rw [insertAt_apply, insertAt_apply, if_pos (le_refl m),
            if_neg (by omega : ¬ m + 1 ≤ m)] at hm
          exact absurd rfl hm.2
        · refine ⟨m - 1, ?_⟩
          rw [show m - 1 + 1 = m from by omega]
          rwa [insertAt_apply, insertAt_apply, if_neg (by omega : ¬ m ≤ n),
            if_neg (by omega : ¬ m + 1 ≤ n)] at hm
    · rintro ⟨m, hm⟩
      by_cases hmn : m < n
      · refine ⟨m, ?_⟩
        rwa [insertAt_apply, insertAt_apply, if_pos (by omega : m ≤ n),
          if_pos (by omega : m + 1 ≤ n)]
      · refine ⟨m + 1, ?_⟩
        rwa [insertAt_apply, insertAt_apply, if_neg (by omega : ¬ m + 1 ≤ n),
          if_neg (by omega : ¬ m + 1 + 1 ≤ n)]

instance {σ : Type u} {α : Type v} (A : Action σ) (v : σ → α) :
    SI (eventually (actionPred (AngleAction A v))) where
  inv := si_eventually_angle A v

/-- `WF_v A v = ∀ k, (□⌜Enabled ⟨A⟩_v⌝) (e.drop k) → (◇⟨⟨A⟩_v⟩) (e.drop k)`。 -/
instance {σ : Type u} {α : Type v} (A : Action σ) (v : σ → α) : SI (WF_v A v) where
  inv := si_forall_suffix_imp (always (statePred (Enabled (AngleAction A v))))
    (eventually (actionPred (AngleAction A v)))

/-- `SF_v A v = ∀ k, (□◇⌜Enabled ⟨A⟩_v⌝) (e.drop k) → (◇⟨⟨A⟩_v⟩) (e.drop k)`。 -/
instance {σ : Type u} {α : Type v} (A : Action σ) (v : σ → α) : SI (SF_v A v) where
  inv := si_forall_suffix_imp
    (always (eventually (statePred (Enabled (AngleAction A v)))))
    (eventually (actionPred (AngleAction A v)))

end Bft
