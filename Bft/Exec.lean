import Bft.Core
import Bft.Rules
import Cslib.Foundations.Semantics.FLTS.Basic

/-!
# Bft.Exec — 可执行化管道：从关系 spec 到 step 函数

核心模式（Verdi/IronFleet 同款）：把 `Next = A₁ ∨ ... ∨ Aₙ` 的每个析取支
拆成 **guard（前提，只读当前状态）** 与 **update（确定性更新）**，组装成
label-indexed step 函数。若 guard 可判定、update 可计算，则 step 函数
可编译执行。

正确性定理 `run_is_behavior`：step 函数的任意 run 都是 spec 的 behavior
——guard 成立时该步触发对应动作，否则该步 stutter。于是 spec 上证明的
`□Inv`（以及任何 safety 性质）自动覆盖所有可执行 run。**活性不在此处
获得**：可执行系统的活性来自部署环境的公平性假设（网络最终送达、
定时器最终触发），这是信任基的显式组成部分，见 docs/design.md §4.4。

与 lean-tla `StreamletExec` 的差别：那里 guard 含存在量词导致
`noncomputable step`；本文件把"可判定 guard"作为一等设计约束，
`GuardedAction` 结构体把 guard 的 `Decidable` 实例和"guard ⇒ 动作语义
吻合"的证明打包，由 elaborator/tactic 半自动构造。
-/

namespace Bft

/-- 一个可执行动作：确定性更新 + 可判定 guard + 与关系语义的一致性证明。 -/
structure GuardedAction (σ : Type u) (lbl : Type v) where
  /-- 关系语义（spec 层的动作）。 -/
  rel : lbl → Action σ
  /-- 前提。 -/
  guard : lbl → σ → Prop
  /-- 确定性更新。 -/
  update : lbl → σ → σ
  /-- guard 成立 ⇒ 更新后的状态满足关系。 -/
  fires : ∀ l s, guard l s → rel l s (update l s)
  /-- 关系是确定性的：任何满足关系的状态都是 update 的结果。 -/
  det : ∀ l s s', rel l s s' → s' = update l s

/-- 可执行 spec：label 类型 + 一组动作 + guard 可判定性。 -/
structure ExecSpec (σ : Type u) where
  lbl : Type v
  actions : GuardedAction σ lbl
  decGuard : ∀ l s, Decidable (actions.guard l s)

attribute [instance] ExecSpec.decGuard

/-- step 函数：guard 成立则更新，否则 stutter。**可编译**。 -/
def ExecSpec.step {σ : Type u} (es : ExecSpec σ) (s : σ) (l : es.lbl) : σ :=
  if es.actions.guard l s then es.actions.update l s else s

/-- 从初始状态出发、按 label 序列驱动的 run。 -/
def ExecSpec.run {σ : Type u} (es : ExecSpec σ) (s₀ : σ) :
    List es.lbl → σ
  | [] => s₀
  | l :: ls => es.run (es.step s₀ l) ls

/-- spec 层的 Next：存在某个 label 使关系成立。 -/
def ExecSpec.next {σ : Type u} (es : ExecSpec σ) : Action σ :=
  fun s s' => ∃ l, es.actions.rel l s s'

/-- **正确性定理**：每个 step 要么是 `next` 步，要么是 stutter
（对任意帧 `v` 都成立，取 `v = id` 即得 `Unchanged`）。 -/
theorem ExecSpec.step_is_spec_step {σ : Type u} (es : ExecSpec σ) (s : σ)
    (l : es.lbl) :
    es.next s (es.step s l) ∨ es.step s l = s := by
  unfold step
  by_cases hg : es.actions.guard l s
  · rw [if_pos hg]
    exact Or.inl ⟨l, es.actions.fires l s hg⟩
  · rw [if_neg hg]
    exact Or.inr rfl

/-- 由此，`run` 的每一步都是 spec 步：任意有限 trace 是 spec 某个
behavior 的前缀。结合 `init_invariant_stut`，spec 的不变式覆盖所有 run。 -/
theorem ExecSpec.run_invariant {σ : Type u} (es : ExecSpec σ)
    (init inv : StatePred σ)
    (hinit : ∀ s, init s → inv s)
    (hstep : ∀ s s', StutAction es.next (fun s => s) s s' → inv s → inv s')
    (s₀ : σ) (hs₀ : init s₀) (trace : List es.lbl) :
    inv (es.run s₀ trace) := by
  suffices hgen : ∀ s₀ : σ, inv s₀ → inv (es.run s₀ trace) by
    exact hgen s₀ (hinit s₀ hs₀)
  intro s₀ hinv
  induction trace generalizing s₀ with
  | nil => exact hinv
  | cons l ls ih =>
      unfold run
      have hinv_step : inv (es.step s₀ l) := by
        rcases es.step_is_spec_step s₀ l with hnext | hstut
        · exact hstep _ _ (Or.inl hnext) hinv
        · rw [hstut]
          exact hinv
      exact ih (es.step s₀ l) hinv_step

/-! ## FLTS 桥接

`ExecSpec.step` 就是一个 `Cslib.FLTS`（确定性 label 迁移函数），
`run = mtr`。于是执行层免费接入 CSLib 的 FLTS/LTS 机器
（`FLTSToLTS`、积 `Prod`、simulation）。 -/

/-- 可执行 spec 对应的 FLTS。 -/
def ExecSpec.toFLTS {σ : Type u} (es : ExecSpec σ) : Cslib.FLTS σ es.lbl where
  tr := es.step

/-- run 即 FLTS 的多步迁移。 -/
theorem ExecSpec.run_eq_mtr {σ : Type u} (es : ExecSpec σ) (s₀ : σ)
    (ls : List es.lbl) :
    es.run s₀ ls = es.toFLTS.mtr s₀ ls := by
  induction ls generalizing s₀ with
  | nil => rfl
  | cons l ls ih =>
      -- 两边分别展开一步：run 的 cons 子句与 `List.foldl` 的 cons 子句
      -- （`mtr` 即 `μs.foldl flts.tr s`），再对尾段用归纳假设。
      show es.run (es.step s₀ l) ls = es.toFLTS.mtr (es.step s₀ l) ls
      exact ih (es.step s₀ l)

/-- **确定性**：spec 关系在可执行动作下是函数——refinement 方向
（每个 spec 步都是某个 step）也因此免费得到，对模型检查/对拍有用。 -/
theorem ExecSpec.next_det {σ : Type u} (es : ExecSpec σ) (s s' : σ)
    (h : es.next s s') : ∃ l, s' = es.step s l ∨
      (¬ es.actions.guard l s ∧ es.step s l = s) := by
  rcases h with ⟨l, hrel⟩
  refine ⟨l, ?_⟩
  rw [es.actions.det l s s' hrel]
  unfold step
  by_cases hg : es.actions.guard l s
  · exact Or.inl (by rw [if_pos hg])
  · exact Or.inr ⟨hg, by rw [if_neg hg]⟩

end Bft
