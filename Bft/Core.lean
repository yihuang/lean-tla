import Cslib.Foundations.Data.OmegaSequence.Init
import Cslib.Foundations.Data.OmegaSequence.Temporal

/-!
# Bft.Core — 语义内核（CSLib 版）

设计决策（docs/design.md §2，经 CSLib 源码调研后修正）：

* `Behavior = Cslib.ωSequence`。**不用** `ℕ → σ`：CSLib 的
  `@[simp] get_drop : (drop m s) n = s (m + n)` 已经把 pointwise normal
  form 做成 simp 标准形（drop 计数在前、索引在后，正是需要的方向），
  `drop_drop`/`drop_zero` 同已注册。lean-tla 的加法重写链来自显式展开
  `drop` 定义绕过了这些引理，不是 CSLib 的缺陷。
* 浅嵌入 `Pred σ := Behavior σ → Prop`，SI 走 typeclass（`Bft.Stutter`）。
* 状态层片段与 `Cslib.ωSequence.Temporal` 对齐：`Step`/`LeadsTo` 的
  pointwise 形式与本文件的 `leadsTo ⌜p⌝ ⌜q⌝` 在同一行为上等价，
  桥接引理在 `Bft/CslibBridge.lean`——证书结论可无损翻译成 CSLib 词汇。
-/

namespace Bft

/-- 无限行为。 -/
abbrev Behavior (σ : Type u) := Cslib.ωSequence σ
abbrev Pred (σ : Type u) := Behavior σ → Prop
abbrev StatePred (σ : Type u) := σ → Prop
abbrev Action (σ : Type u) := σ → σ → Prop

/-- 后缀。直接复用 CSLib，不自定义。 -/
abbrev drop {σ : Type u} (n : ℕ) (e : Behavior σ) : Behavior σ := e.drop n

/-! ## 三层提升 -/

def statePred {σ : Type u} (p : StatePred σ) : Pred σ := fun e => p (e 0)
def actionPred {σ : Type u} (a : Action σ) : Pred σ := fun e => a (e 0) (e 1)
def purePred {σ : Type u} (p : Prop) : Pred σ := fun _ => p

/-! ## 命题连接词 -/

def tlaAnd {σ : Type u} (F G : Pred σ) : Pred σ := fun e => F e ∧ G e
def tlaOr {σ : Type u} (F G : Pred σ) : Pred σ := fun e => F e ∨ G e
def tlaImp {σ : Type u} (F G : Pred σ) : Pred σ := fun e => F e → G e
def tlaNot {σ : Type u} (F : Pred σ) : Pred σ := fun e => ¬ F e
def tlaForall {σ : Type u} {α : Type v} (f : α → Pred σ) : Pred σ := fun e => ∀ a, f a e
def tlaExists {σ : Type u} {α : Type v} (f : α → Pred σ) : Pred σ := fun e => ∃ a, f a e

/-! ## 时序算子 -/

def always {σ : Type u} (F : Pred σ) : Pred σ := fun e => ∀ n, F (e.drop n)
def eventually {σ : Type u} (F : Pred σ) : Pred σ := fun e => ∃ n, F (e.drop n)
def later {σ : Type u} (F : Pred σ) : Pred σ := fun e => F (e.drop 1)
def leadsTo {σ : Type u} (P Q : Pred σ) : Pred σ := always (tlaImp P (eventually Q))

/-! ## 满足与蕴含 -/

def Valid {σ : Type u} (F : Pred σ) : Prop := ∀ e : Behavior σ, F e
def Entails {σ : Type u} (F G : Pred σ) : Prop := ∀ e : Behavior σ, F e → G e

/-! ## 动作、stuttering、公平性 -/

def Enabled {σ : Type u} (a : Action σ) : StatePred σ := fun s => ∃ s', a s s'

def Unchanged {σ : Type u} {α : Type v} (v : σ → α) : Action σ := fun s s' => v s' = v s

/-- `[A]_v`。 -/
def StutAction {σ : Type u} {α : Type v} (a : Action σ) (v : σ → α) : Action σ :=
  fun s s' => a s s' ∨ v s' = v s

/-- `⟨A⟩_v`。 -/
def AngleAction {σ : Type u} {α : Type v} (a : Action σ) (v : σ → α) : Action σ :=
  fun s s' => a s s' ∧ v s' ≠ v s

/-- `□[A]_v`。 -/
def stutAlways {σ : Type u} {α : Type v} (a : Action σ) (v : σ → α) : Pred σ :=
  always (actionPred (StutAction a v))

/-- `WF_v(A)`。 -/
def WF_v {σ : Type u} {α : Type v} (A : Action σ) (v : σ → α) : Pred σ :=
  always (tlaImp (always (statePred (Enabled (AngleAction A v))))
    (eventually (actionPred (AngleAction A v))))

/-- `SF_v(A)`。 -/
def SF_v {σ : Type u} {α : Type v} (A : Action σ) (v : σ → α) : Pred σ :=
  always (tlaImp (always (eventually (statePred (Enabled (AngleAction A v)))))
    (eventually (actionPred (AngleAction A v))))

/-- 全局 justice `□◇⟨r⟩`。 -/
def globalJustice {σ : Type u} (r : Action σ) : Pred σ :=
  always (eventually (actionPred r))

/-! ## Pointwise normal forms

时序公式在后缀处的取值归约为位置处的取值。CSLib 的 `get_drop`
（`@[simp]`）把 `(e.drop n) m` 归到 `e (n + m)`，所以这组引理的证明
全部是 `simp`；它们注册为 `@[simp]` 后，下游证明在时序/位置边界
不需要手工重写。 -/

@[simp] theorem statePred_drop {σ : Type u} (p : StatePred σ) (e : Behavior σ)
    (k : ℕ) : statePred p (e.drop k) = p (e k) := by
  simp [statePred]

@[simp] theorem actionPred_drop {σ : Type u} (a : Action σ) (e : Behavior σ)
    (k : ℕ) : actionPred a (e.drop k) = a (e k) (e (k + 1)) := by
  simp [actionPred]

@[simp] theorem eventually_statePred_drop {σ : Type u} (q : StatePred σ)
    (e : Behavior σ) (k : ℕ) :
    eventually (statePred q) (e.drop k) ↔ ∃ m, q (e (k + m)) := by
  simp [eventually, statePred]

@[simp] theorem eventually_actionPred_drop {σ : Type u} (r : Action σ)
    (e : Behavior σ) (k : ℕ) :
    eventually (actionPred r) (e.drop k) ↔ ∃ m, r (e (k + m)) (e (k + m + 1)) := by
  simp [eventually, actionPred]

/-- `◇` 的 tableau 公理（用于 Rule 7 链接）：`◇F` 于后缀 k 即
`F` 于 k 或 `◇F` 于 k+1。 -/
theorem eventually_unfold {σ : Type u} (F : Pred σ) (e : Behavior σ) (k : ℕ) :
    eventually F (e.drop k) ↔ F (e.drop k) ∨ eventually F (e.drop (k + 1)) := by
  simp only [eventually]
  constructor
  · rintro ⟨m, hm⟩
    cases m with
    | zero => exact Or.inl hm
    | succ m =>
        right
        refine ⟨m, ?_⟩
        rw [Cslib.ωSequence.drop_drop] at hm ⊢
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm
  · rintro (h | ⟨m, hm⟩)
    · exact ⟨0, h⟩
    · refine ⟨m + 1, ?_⟩
      rw [Cslib.ωSequence.drop_drop] at hm ⊢
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm

end Bft
