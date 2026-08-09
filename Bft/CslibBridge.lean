import Bft.Core
import Cslib.Foundations.Data.OmegaSequence.InfOcc
import Cslib.Foundations.Semantics.LTS.OmegaExecution

/-!
# Bft.CslibBridge — 与 CSLib 现有层的桥接

调研结论（docs/design.md §2.2）：CSLib 已有三个与本书直接对接的层，
桥接而非重建：

1. **`ωSequence.Temporal`**（`Step`/`LeadsTo`，pointwise + grind 注解）：
   本库 DSL 的**状态层片段**与之逐字等价。证书引擎（`RelRankCert`）的
   结论可无损翻译成 `LeadsTo`，这是 upstream 的接口形状。
2. **`ωSequence.infOcc` / `∃ᶠ k in atTop`**：`SF` 的"无限次 enabled"。
3. **`LTS.OmegaExecution` / `FLTS`**：执行层（`Bft.Exec`）的 step 函数
   即一个 `FLTS`，`run = mtr`；spec 的行为即隐式 LTS 的
   `OmegaExecution`（label 取 `Unit`）。
-/

namespace Bft

open Cslib Set Filter

/-! ## 1. 状态层 leads-to 与 CSLib `LeadsTo` 等价 -/

/-- `leadsTo ⌜p⌝ ⌜q⌝` 在行为 `e` 上成立，当且仅当 CSLib 的
`e.LeadsTo {s | p s} {s | q s}`。这把证书结论接入 CSLib 的
grind 注解 API（`step_leadsTo`、`leadsTo_trans`、
`until_frequently_leadsTo_and` 等可直接复用）。 -/
theorem leadsTo_statePred_iff {σ : Type u} (p q : StatePred σ) (e : Behavior σ) :
    leadsTo (statePred p) (statePred q) e ↔
      e.LeadsTo {s | p s} {s | q s} := by
  simp [leadsTo, always, tlaImp, eventually, statePred, Cslib.ωSequence.LeadsTo]
  constructor
  · intro h k hpk
    rcases h k hpk with ⟨m, hm⟩
    exact ⟨k + m, Nat.le_add_right k m, hm⟩
  · intro h k hpk
    rcases h k hpk with ⟨k', hk', hq⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk'
    exact ⟨m, hq⟩

/-- `Step` 是"单步蕴含"的 CSLib 形式：与不变式归纳的 step 义务同形。 -/
theorem step_iff {σ : Type u} (p q : StatePred σ) (e : Behavior σ) :
    e.Step {s | p s} {s | q s} ↔ ∀ k, p (e k) → q (e (k + 1)) :=
  Iff.rfl

/-! ## 2. SF 与 `∃ᶠ` -/

/-- "无限次 enabled"的 filter 形式与 `□◇ Enabled` 的等价。 -/
theorem always_eventually_enabled_iff_frequently {σ : Type u} {α : Type v}
    (A : Action σ) (v : σ → α) (e : Behavior σ) :
    (always (eventually (statePred (Enabled (AngleAction A v))))) e ↔
      ∃ᶠ k in atTop, Enabled (AngleAction A v) (e k) := by
  simp [always, eventually, statePred, frequently_atTop]
  constructor
  · intro h m
    rcases h m with ⟨k, hk⟩
    exact ⟨m + k, Nat.le_add_right m k, hk⟩
  · intro h m
    rcases h m with ⟨k, hmk, hk⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmk
    exact ⟨d, hk⟩

/-! 由此 `SF_v` 可以陈述为：`∃ᶠ enabled → □◇ fires`。这是对接
`infOcc` 机器（pigeonhole、strictMono 提取）的接口。 -/

/-! ## 3. 行为即 LTS 的无限执行 -/

/-- 动作 `next` 生成一个 label 为 `Unit` 的 LTS。 -/
def Action.toLTS {σ : Type u} (next : Action σ) : Cslib.LTS σ Unit where
  Tr s _ s' := next s s'

/-- `□⟨next⟩ e` 当且仅当 `e` 是 `next.toLTS` 的无限执行。这把 spec 的
迁移结构接入 CSLib 的 LTS 机器（simulation、bisimulation、trace 等价）。 -/
theorem always_actionPred_iff_omegaExecution {σ : Type u} (next : Action σ)
    (e : Behavior σ) :
    (always (actionPred next)) e ↔
      (Action.toLTS next).OmegaExecution e (Cslib.ωSequence.const ()) := by
  simp [always, actionPred, Cslib.LTS.OmegaExecution, Action.toLTS]

end Bft
