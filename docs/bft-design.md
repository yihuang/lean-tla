# 设计文档：从模型到可执行 BFT 的 Lean4 验证管道

> 项目代号 **Bft**。本文档记录设计决策与理由，特别是与 lean-tla（本项目的
> 思想来源与对照组）的分歧点。
>
> **修订记录**：v2 经 CSLib 源码调研（toolchain `v4.33.0-rc2`）后，
> 内核从 `ℕ → σ` 迁移到 `Cslib.ωSequence`，新增 `Bft/CslibBridge.lean`
> 与 FLTS 桥接；见 §2.2。v3（M1 完成）：**全部 sorry 消除，`lake build Bft`
> 绿**（Stutter.lean 6 处全部证明——`stutAlways` 的 SI 实际是直接的逐点
> 论证而非元理论深水区；RelRank.lean 2 处——`vecLexLess_wellFounded`
> 移植 + `LexRankCert.toLeadsTo` 经完整 Rule 10 移植）。证明过程中修正了
> `LexRankCert` 陈述的两处缺陷（见 §3.1 修正记录）：补上缺失的 S4 前提
> （至少一个 scheduler 常开，否则命题本身为假），`hjustice` 前件从
> `Req` 加强为 `ψs i` 本身（否则无法供给 S3）。

## 1. 愿景与定位

**愿景**：现代 BFT 共识协议的"模型 → 机器检查证明 → 可执行参考实现"管道。

**定位约束**（从 TLAPS 失败学到的）：

- 不做通用 TLA 工具。目标人群是**正在设计新 BFT 协议的协议研究者**。
- 活性证明必须成为安全性证明的低成本副产品，不是独立项目。
- 可执行参考实现是获客入口，证明是留存。
- 内核设计以最终并入 CSLib 为准绳（不发明私有基础概念）。

## 2. 语义内核（`Bft/Core.lean`, `Bft/Stutter.lean`）

### 2.1 浅嵌入，但 stuttering invariance 走 typeclass

- `Pred σ := Behavior σ → Prop`，纯浅嵌入。放弃"语法树深嵌入 + eval"
  方案：它能把 SI 做成归纳定理，但代价是所有组合子维护两套、
  elaborator 错误信息恶化、且 mathlib 生态的引理（都是裸 `Prop`）无法
  直接接入。
- 替代方案：`SI F` 是 `Prop` 值 typeclass。所有 DSL 组合子配 instance，
  推断按构造收集合法性；用户手写裸 `Pred` 时推断失败、显式报错。
  **合法性从纪律变成推断时检查**，这是相对 lean-tla（SI 纯靠元理论
  事后刻画）的主要改进。
- 已知边界：`tlaImp` 一般**不**保持 SI（蕴含的反单调性），因此刻意
  不提供 `SI (tlaImp F G)` instance；`leadsTo` 提供。TLA+ 的语法限制
  用"instance 存在与否"表达——这是把 TLA 的语法约束翻译成 Lean 的
  类型类约束。

### 2.2 `drop` 与 CSLib（经源码调研后修正）

**初版草案用 `ℕ → σ` 并自定义 `drop n e m = e (n + m)`，是错的**——
调研 CSLib 最新源码（toolchain `v4.33.0-rc2`）后修正为
`Behavior = Cslib.ωSequence`。调研发现：

1. **pointwise normal form CSLib 已经解决了，且方向正确**：
   `@[simp] get_drop : (drop m s) n = s (m + n)`（drop 计数在前、
   索引在后），`drop_drop`/`drop_zero` 同为 simp。lean-tla 的加法
   重写链来自其 simp 集显式展开 `drop` 定义、绕过了这些引理，
   不是 CSLib 的缺陷。本库只需在 `Core.lean` 注册薄薄一层
   `statePred_drop`/`actionPred_drop`/`eventually_*_drop`。
2. **`ωSequence.Temporal`（新增，`Step`/`LeadsTo`，grind 注解）与
   本库 DSL 的状态层片段逐字等价**：
   `leadsTo ⌜p⌝ ⌜q⌝ e ↔ e.LeadsTo {s|p s} {s|q s}`
   （`Bft/CslibBridge.lean`）。证书结论可无损翻译成 CSLib 词汇，
   且 CSLib 的 `step_leadsTo`/`leadsTo_trans`/
   `until_frequently_leadsTo_and` 等 grind 注解定理可直接复用。
3. **`InfOcc`（`∃ᶠ k in atTop` 机器：pigeonhole、strictMono 提取）
   对接 `SF` 的"无限次 enabled"**（桥接定理已写）。
4. **`LTS.OmegaExecution`/`FLTS` 比预期成熟**：执行层的
   `ExecSpec.step` 就是一个 `FLTS`（`run = mtr`，桥接已写）；
   spec 的 `□⟨next⟩` 行为即隐式 LTS 的 `OmegaExecution`。
   CSLib 的 `Logics/` 目前只有 modal/HML/linear——**时序逻辑层
   （TLA 式算子 + fairness + SI）确实是空白**，是本内核 upstream
   的候选位置。

### 2.3 有限 stutter 与全 stutter 的诚实切割

`StutterInvariant` 定义为单步 stutter 插入/删除下不变，生成**有限**
stutter 等价。TLA 全语义还要求无限 stutter 闭包（run compression，
lean-tla `SimFull.lean` 800 行）。本草案不含 run compression，因为：
(1) 有限 stutter 不变性已覆盖工程上所有相关公式（`□[A]_v`、`WF_v`、
`SF_v`、`↝` 全部是）；(2) run compression 定理在 lean-tla 已机器检查，
移植是机械工作。**明确声明而非假装完成**。

### 2.4 状态与变量

本草案示例直接写 `fun s => s.pc = 1`（无 `tla_var` elaborator、无
`[p|...]` 语法）。理由：语法皮是 UX 实验层，不属于内核；先把证明义务
的形状打对，语法皮最后加，且应该可替换。生产版应提供 lean-tla 式
`tla_var`（其设计——`addAndCompile` + `abbrev` hints + 自动 `_apply`
simp 引理——是对的，可直接借鉴）。

## 3. 活性引擎（`Bft/RelRank.lean`, `Bft/Tactic.lean`）

### 3.1 规则即证书

`RelRankCert` 结构体打包一次 Rule 6 应用的全部见证与义务证明。
`toLeadsTo` 给出结论；`trans`（Rule 7）组合证书。设计意图：

- 活性证明从 tactic 树变成**对象**：可存储、可打印、可跨文件复用、
  可被组合子消费；
- 组合子是引擎的真正价值所在（McMillan 论文标题里的 "at Scale" 指
  的就是组合，不是单条规则）；
- `LexRankCert`（Rule 10，字典序 + stable scheduler）以同样方式给出，
  已完整证明（`toLeadsTo` 经移植的 `rel_rank_lex` 全封闭）。

**修正记录（M1 证明过程中发现）**：`LexRankCert.toLeadsTo` 的初版陈述
**为假**——缺 S4 前提（任一时刻至少一个 scheduler 开启；反例：φ 恒真、
无 scheduler 的常值行为满足全部旧前提但 q 永不成立），已补 `hsched`；
同时 `hjustice` 前件从 `Req`（开启且未被抢占）加强为 `ψs i` 本身，
否则被抢占分量无法供给 S3。这正暴露了"陈述先行、证明后补"工作流的
风险，也说明 Rule 10 的前提结构必须机器检查才算数。

### 3.2 义务规范化器（tactic 层的核心工程）

C1–C3 展开后永远是同一模式：`∀ s s', Next s s' → φ s → q s' ∨ (φ s' ∧
Conserves δ s s')`。契约：

1. 分层 simp 集（`tla_temporal` / `tla_action` / `tla_state`），不做
   all-or-nothing 巨型 simp（lean-tla `tla_unfold` 40+ 项的教训）；
2. `Conserves`/`Reduces` 展开后立即重写回用户数据结构语言，
   grind patterns 受控，**绝不展开 `Set.ncard`**（那是规则内部的事）；
3. 失败时报告哪个义务失败（C1/C2/C3/finiteness）；后续接 ModelCheck
   生成两状态反例（本草案未含，接口预留）。

### 3.3 公平性假设不藏起来

TicketLock 示例里 `liveness` 的前提是显式的 `globalJustice Serve`，
而不是从 spec 的 `WF_v Enter` 假装导出。原则：**活性定理的 statement
必须显式列出它依赖的公平性**。这些假设到执行层翻译成部署前提
（"服务方最终放行每一张票"），是信任基文档的一部分。

## 4. 可执行管道（`Bft/Exec.lean`）

### 4.1 模式

`Next = ∨ᵢ Aᵢ` 的每个析取支拆为 guard（只读当前状态）+ update
（确定性更新），`GuardedAction` 打包 `fires`（guard ⇒ 关系成立）与
`det`（关系确定到 update）两个一致性证明。

### 4.2 可判定性是一等约束

lean-tla `StreamletExec` 的 `step` 是 `noncomputable`（guard 含存在量词）。
本设计把 `decGuard : ∀ l s, Decidable (guard l s)` 作为 `ExecSpec` 的字段：
**写不出可判定 guard 的动作就不能进执行层**。含存在量词的 guard
（如 "存在 quorum 投了票"）必须改写为有界判定（遍历有限节点集）——
这个改写本身是 refinement 义务的一部分。

### 4.3 正确性定理的精确内容

`run_invariant`：spec 的不变式覆盖所有可执行 run。**不提供**活性：
可执行系统的活性 = spec 活性定理 + 部署环境满足公平性假设（§3.3），
后者永远不可证明，只能显式声明。

### 4.4 信任基（诚实清单）

执行一个验证过的 BFT 参考实现时，信任基 = Lean 内核 + mathlib 公理 +
本库零 sorry 的定理 + **签名/密码学 FFI（公理化）** + **部署环境满足
显式列出的公平性假设** + Lean4 编译器与运行时。

## 5. 缺失与路线图

| 阶段 | 内容 | 状态 |
|---|---|---|
| 0 | 本草案：内核 + 引擎骨架 + 执行管道 + 端到端示例 | ✅ |
| 1 | 消除 sorry；`lake build Bft` 绿（1014 jobs，含 `CslibBridge`
    全部桥接引理） | ✅ 零 sorry |
| 2 | 义务规范化器（`Bft/Obligation.lean`）：`tla_ob` 规范化 +
    omega/grind 收尾、失败按层分类（temporal/action/finiteness/ranking/
    two-state）、`#tla_cex G to Q` 两状态反例（FinEnum 穷举）；
    冒烟测试 `Examples/TicketLock`（全管道 + `#eval`）与
    `Examples/ObligationDemo`（反例打印）进默认构建。自定义 grind
    patterns 留待 M3 按需补充 | ✅（1018 jobs 绿） |
| 3 | Rule 11 组合子（`leadsTo_exists` + `RelRankCert.forall_fin`：共享 H 与
    justice 动作的有限证书族 ⇒ `(∃ i, p i) ↝ q`）；证书库首个模板
    `Bft/Templates/Fifo.lean`（FIFO 队列位置排名 `List.idxOf`：C1 与
    有界性自动闭合，用户只证 hc2/hc3 两条行为级条件）；
    演示 `Examples/FifoQueue`（Nodup 不变量在 hc2/hc3 内复用、
    每元素活性、Rule 11 合并、执行层 `#eval` 冒烟） | ✅（1020 jobs 绿；
    Rule 10 的 LexRankCert 修正版已在 M1 落地） |
| 4 | 消息层 refinement 第一层（`Bft/Refine.lean`）：`StepSim`/`InitSim`
    步模拟 ⇒ `specSim_entails`（任意高层性质经抽象函数迁移，安全活性
    通用）、`refine_invariant` 不变量运输、`globalJustice_map` justice
    提升；`Packet`/`NetState` 消息汤模型（list，无 FIFO 假设）。
    演示 `Examples/BoundedCounter`（abs = 已服务 + 在途消息数，
    `n ≤ cap` 高层证一次、分布式系统免费继承；执行层 `#eval` 冒烟）。
    公平性保持显式（与 TicketLock 一致的诚实处理）；完整 Verdi 式
    网络语义（故障、复制）仍是缺口 | ✅（1022 jobs 绿） |
| 5 | 案例：Minimmit 投票核心全管道（`Bft/Examples/Minimmit.lean`）。
    模型：消息集合只增（`Finset` 消息汤）、诚实节点每视图至多一票
    （guard 拒绝双投）、拜占庭节点任意投票；n ≥ 5f+1、L-公证
    （n−f 票）/M-公证（2f+1 票）/nullify（2f+1 票）三个法定人数。
    安全：引擎引理 `exists_honest_inter`（两票集大小之和 > n+f ⇒
    交集中有诚实节点）一条驱动 X0（同视图 L-公证唯一）、X1（L-公证
    排除冲突 M-公证）、X2（L-公证视图不可 nullify）三条 quorum
    相交定理；`HonestUniq` 归纳不变量经 `init_invariant_stut` 提升为
    时序定理，`consistency` 把三条性质打包为 □ 陈述。执行层：标签
    化 ExecSpec（honest/byz）、`exec_next_refines`、`exec_safe` 免费
    继承不变量，`#eval` 冒烟（n=6, f=1，双投被拒、拜占庭 Equivocation
    达不到法定人数）。范围诚实声明：只建模投票核心——父块依赖、
    视图推进、contradiction-based nullify 与活性（M-公证引导视图
    收敛）留待后续里程碑 | ✅（1023 jobs 绿） |
| 6 | 内核贡献 CSLib；语法皮（`tla_var`、`[a|...]`）作为可替换层 | |

### 明确不做

- TLC 规模 model checking（symmetry、partial-order reduction）；
- PTL 决策过程（leads-to 通用自动机）；
- 见证全自动推断（δ 只做到模板级半自动）；
- PlusCal 式过程语法。

## 6. 与 lean-tla 的关系

思想、规则证明结构、RelRank 定理均继承自 lean-tla（其中
`rank_descent`/`finite_rank`/`ncard_decrease` 的证明是从其已机器检查
版本改编）。分歧点：`SI` typeclass（2.1）、`drop` 方向（2.2）、分层
simp（3.2）、可判定 guard 一等化（4.2）、公平性假设显式化（3.3）、
以及不做 DSL 语法皮优先（2.4）。若 lean-tla 作者愿意，两个项目最
好的归宿是合并后共同走 §5 的路线图。
