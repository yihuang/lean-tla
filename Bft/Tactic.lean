import Bft.Core
import Bft.Rules
import Bft.RelRank

/-!
# Bft.Tactic — tactic 层：义务规范化器

原则（docs/design.md §3.2）：

1. 分层 simp 集，不做 all-or-nothing 巨型 simp：
   - `tla_temporal`：时序层展开（`always/eventually/leadsTo/...`）；
   - `tla_action`：动作层展开（`StutAction/AngleAction/Enabled/...`）；
   - `tla_state`：状态层（用户注册的变量 `_apply` 引理）。
2. `Conserves`/`Reduces` 展开后立即重写回用户数据结构语言，用 grind
   patterns 控制——不展开 `Set.ncard`，那是证明义务不是用户义务。
3. 每个规则一个专用 tactic：`tla_inv` / `tla_wf1` / `tla_rel_rank`，
   义务按固定形状交给 grind；失败时 tactic 报告**哪个义务**失败
   （引擎诊断的第一层）。

本文件是可工作的宏骨架；义务规范化器的完整版（grind pattern 注册、
失败分类）是工程任务，见 design.md §3.2 的接口契约。
-/

namespace Bft

open Lean Elab Tactic

/-- 时序层展开。 -/
macro "tla_temporal" : tactic =>
  `(tactic| simp only [Bft.always, Bft.eventually, Bft.later, Bft.leadsTo,
    Bft.tlaAnd, Bft.tlaOr, Bft.tlaImp, Bft.tlaNot, Bft.statePred,
    Bft.actionPred, Bft.purePred, Bft.globalJustice, Bft.Entails])

/-- 动作层展开。 -/
macro "tla_action" : tactic =>
  `(tactic| simp only [Bft.StutAction, Bft.AngleAction, Bft.Enabled,
    Bft.Unchanged, Bft.WF_v, Bft.SF_v, Bft.stutAlways])

/-- 全展开（调试逃生口，不推荐用于脚本）。 -/
macro "tla_unfold" : tactic => `(tactic| (tla_temporal; tla_action))

/-- 不变式归纳：套 stutter 版定理，留 init/step 两个义务。 -/
macro "tla_inv" : tactic => `(tactic| apply Bft.init_invariant_stut)

/-- 展开后 grind 收尾：action 层义务的主力。 -/
macro "tla_grind" : tactic => `(tactic| (tla_unfold; grind))

/-- WF1：套规则后自动尝试简单义务。 -/
macro "tla_wf1" : tactic => `(tactic| (apply Bft.wf1 <;> try tla_grind))

/-- SF1。 -/
macro "tla_sf1" : tactic => `(tactic| (apply Bft.sf1 <;> try tla_grind))

/-- RelRank：把 goal 归到 Rule 6 后构造证书。
用法：`tla_rel_rank φ δ R r`，留 C1/C2/C3/finiteness 四个义务，
每个义务先用义务规范化器 + grind 尝试。 -/
macro "tla_rel_rank" φ:term δ:term r:term rr:term : tactic =>
  `(tactic| (apply Bft.relational_ranking_rule (φ := $φ) (δ := $δ) (r := $rr) (R := $r)
      <;> try tla_grind))

/-- 证书组合：`cert₁.then cert₂ hH`。 -/
theorem RelRankCert.then {σ : Type u} {p q q' : StatePred σ}
    (cert₁ : RelRankCert σ p q) (cert₂ : RelRankCert σ q q')
    (hH : ∀ e, tlaAnd cert₁.H (globalJustice cert₁.r) e →
      tlaAnd cert₂.H (globalJustice cert₂.r) e) :
    Entails (tlaAnd cert₁.H (globalJustice cert₁.r))
      (leadsTo (statePred p) (statePred q')) := by
  exact RelRankCert.trans cert₁ cert₂ hH

end Bft
