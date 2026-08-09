import Cslib.Foundations.Data.OmegaSequence.Init
import Cslib.Foundations.Data.OmegaSequence.Temporal

/-!
# Bft.Core — the semantic kernel (CSLib edition)

Design decisions (docs/bft-design.md §2, revised after reading the CSLib
sources):

* `Behavior = Cslib.ωSequence`. **Not** `ℕ → σ`: CSLib's
  `@[simp] get_drop : (drop m s) n = s (m + n)` already makes the pointwise
  normal form the simp normal form (drop-count first, index last — exactly
  the direction we need), and `drop_drop`/`drop_zero` are registered too.
  lean-tla's addition-rewrite chains came from explicitly unfolding the
  *definition* of `drop`, bypassing these lemmas — not a CSLib defect.
* Shallow embedding `Pred σ := Behavior σ → Prop`; stuttering invariance
  goes through a typeclass (`Bft.Stutter`).
* The state-level fragment aligns with `Cslib.ωSequence.Temporal`: the
  pointwise forms of `Step`/`LeadsTo` are equivalent to this file's
  `leadsTo ⌜p⌝ ⌜q⌝` on the same behavior — the bridge lemmas live in
  `Bft/CslibBridge.lean`, so certificate conclusions translate losslessly
  into CSLib vocabulary.
-/

namespace Bft

/-- Infinite behaviors. -/
abbrev Behavior (σ : Type u) := Cslib.ωSequence σ
abbrev Pred (σ : Type u) := Behavior σ → Prop
/-- State predicates are sets of states — the same type CSLib's
`Step`/`LeadsTo` take, so CSLib's grind-annotated lemma library applies
directly (`Set α` is defined as `α → Prop` in mathlib; this abbreviation
makes the set notation `s ∈ p`, `p ∩ q`, `p ∪ q`, `pᶜ`, `p ⊆ q` available
on state predicates, exactly as in `Cslib.ωSequence.Temporal`). -/
abbrev StatePred (σ : Type u) := Set σ
abbrev Action (σ : Type u) := σ → σ → Prop

/-- Suffix. Reuses CSLib directly; no custom definition. -/
abbrev drop {σ : Type u} (n : ℕ) (e : Behavior σ) : Behavior σ := e.drop n

/-! ## The three liftings -/

def statePred {σ : Type u} (p : StatePred σ) : Pred σ := fun e => p (e 0)
def actionPred {σ : Type u} (a : Action σ) : Pred σ := fun e => a (e 0) (e 1)
def purePred {σ : Type u} (p : Prop) : Pred σ := fun _ => p

/-! ## Propositional connectives -/

def tlaAnd {σ : Type u} (F G : Pred σ) : Pred σ := fun e => F e ∧ G e
def tlaOr {σ : Type u} (F G : Pred σ) : Pred σ := fun e => F e ∨ G e
def tlaImp {σ : Type u} (F G : Pred σ) : Pred σ := fun e => F e → G e
def tlaNot {σ : Type u} (F : Pred σ) : Pred σ := fun e => ¬ F e
def tlaForall {σ : Type u} {α : Type v} (f : α → Pred σ) : Pred σ := fun e => ∀ a, f a e
def tlaExists {σ : Type u} {α : Type v} (f : α → Pred σ) : Pred σ := fun e => ∃ a, f a e

/-! ## Temporal operators -/

def always {σ : Type u} (F : Pred σ) : Pred σ := fun e => ∀ n, F (e.drop n)
def eventually {σ : Type u} (F : Pred σ) : Pred σ := fun e => ∃ n, F (e.drop n)
def later {σ : Type u} (F : Pred σ) : Pred σ := fun e => F (e.drop 1)
def leadsTo {σ : Type u} (P Q : Pred σ) : Pred σ := always (tlaImp P (eventually Q))

/-! ## Satisfaction and entailment -/

def Valid {σ : Type u} (F : Pred σ) : Prop := ∀ e : Behavior σ, F e
def Entails {σ : Type u} (F G : Pred σ) : Prop := ∀ e : Behavior σ, F e → G e

/-! ## Actions, stuttering, fairness -/

def Enabled {σ : Type u} (a : Action σ) : StatePred σ := fun s => ∃ s', a s s'

def Unchanged {σ : Type u} {α : Type v} (v : σ → α) : Action σ := fun s s' => v s' = v s

/-- `[A]_v`. -/
def StutAction {σ : Type u} {α : Type v} (a : Action σ) (v : σ → α) : Action σ :=
  fun s s' => a s s' ∨ v s' = v s

/-- `⟨A⟩_v`. -/
def AngleAction {σ : Type u} {α : Type v} (a : Action σ) (v : σ → α) : Action σ :=
  fun s s' => a s s' ∧ v s' ≠ v s

/-- `□[A]_v`. -/
def stutAlways {σ : Type u} {α : Type v} (a : Action σ) (v : σ → α) : Pred σ :=
  always (actionPred (StutAction a v))

/-- `WF_v(A)`. -/
def WF_v {σ : Type u} {α : Type v} (A : Action σ) (v : σ → α) : Pred σ :=
  always (tlaImp (always (statePred (Enabled (AngleAction A v))))
    (eventually (actionPred (AngleAction A v))))

/-- `SF_v(A)`. -/
def SF_v {σ : Type u} {α : Type v} (A : Action σ) (v : σ → α) : Pred σ :=
  always (tlaImp (always (eventually (statePred (Enabled (AngleAction A v)))))
    (eventually (actionPred (AngleAction A v))))

/-- Global justice `□◇⟨r⟩`. -/
def globalJustice {σ : Type u} (r : Action σ) : Pred σ :=
  always (eventually (actionPred r))

/-! ## Pointwise normal forms

The value of a temporal formula at a suffix reduces to its value at a
position. CSLib's `get_drop` (`@[simp]`) sends `(e.drop n) m` to
`e (n + m)`, so every proof in this group is one `simp`; once registered as
`@[simp]`, downstream proofs need no manual rewriting at the
temporal/position boundary. -/

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

/-- The tableau axiom for `◇` (used by Rule 7 chaining): `◇F` at suffix k
is `F` at k or `◇F` at k+1. -/
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
