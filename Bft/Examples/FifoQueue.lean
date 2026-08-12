import Bft.Core
import Bft.Rules
import Bft.RelRank
import Bft.Exec
import Bft.Tactic
import Bft.Templates.Fifo

/-!
# Bft.Examples.FifoQueue — FIFO template and Rule-11 demo

A bounded FIFO queue over `Fin 3` demonstrating the M3 certificate library:

1. **Model layer**: `Init ∧ □[Next]_vars` with `Dequeue` (removes the head,
   logging it to `out`) and `Enqueue y` (appends, guarded by `y ∉ q` so the
   queue stays nodup).
2. **Safety**: `q.Nodup` by induction (`init_invariant_stut`); the invariant is
   then *reused* inside the liveness side conditions — the typical pattern for
   discharging template premises.
3. **Liveness, per element**: `FifoTemplate` instantiated with rank = queue
   position (`List.idxOf`), giving `x ∈ q ↝ x ∉ q` for every `x`.
4. **Rule 11**: a finite family of certificates `i ∈ q ↝ out ≠ []` combined by
   `RelRankCert.forall_fin` into `(∃ i, i ∈ q) ↝ out ≠ []`.
5. **Execution layer**: guarded actions, executable run, invariant transport.
-/

namespace Bft.Examples.FifoQueue

/-- State: the queue and an output log (head elements that were served). -/
structure St where
  q : List (Fin 3)
  out : List (Fin 3)
deriving Repr, DecidableEq

/-- Frame: all variables. -/
def vars (s : St) : St := s

/-! ## Model layer -/

/-- Serve the head element (when the queue is nonempty). -/
def Dequeue : Action St := fun s s' =>
  s.q ≠ [] ∧ s' = ⟨s.q.tail, s.out ++ s.q.take 1⟩

/-- Append a fresh element (guard keeps the queue nodup). -/
def Enqueue (y : Fin 3) : Action St := fun s s' =>
  y ∉ s.q ∧ s' = ⟨s.q ++ [y], s.out⟩

def Next : Action St := fun s s' => Dequeue s s' ∨ ∃ y, Enqueue y s s'

def Init : StatePred St := fun s => s.q = [] ∧ s.out = []

/-- Invariant: queue elements are distinct. -/
def Inv : StatePred St := fun s => s.q.Nodup

/-- The ambient spec predicate used by every certificate below. -/
def Hspec : Pred St := tlaAnd (statePred Init) (stutAlways Next vars)

/-! ## Safety -/

theorem init_inv : ∀ s, s ∈ Init → s ∈ Inv := by
  intro s hs
  change s.q.Nodup
  rw [hs.1]
  exact List.nodup_nil

theorem step_inv : ∀ s s', StutAction Next vars s s' → s ∈ Inv → s' ∈ Inv := by
  intro s s' hstep hinv
  rcases hstep with hnext | hstut
  swap
  · have : s' = s := hstut
    subst this
    exact hinv
  rcases hnext with ⟨hne, hs'⟩ | ⟨y, hg, hs'⟩
  · -- Dequeue: the tail of a nodup list is nodup
    subst hs'
    show (s.q.tail).Nodup
    change s.q.Nodup at hinv
    cases hq : s.q with
    | nil => exact absurd hq hne
    | cons h t =>
      rw [hq, List.nodup_cons] at hinv
      exact hinv.2
  · -- Enqueue: append a fresh element preserves nodup
    subst hs'
    show (s.q ++ [y]).Nodup
    rw [List.nodup_append]
    refine ⟨hinv, List.nodup_singleton y, fun a haq b hby hab => hg ?_⟩
    rw [List.mem_singleton] at hby
    exact (hby ▸ hab) ▸ haq

theorem safety : Entails Hspec (always (statePred Inv)) :=
  init_invariant_stut Init Next vars Inv init_inv step_inv

/-- The invariant at every time, for use inside liveness side conditions. -/
theorem nodup_of_H (e : Behavior St) (hE : Hspec e) (k : ℕ) : (e k).q.Nodup :=
  always_statePred_at (safety e hE)

/-! ## Liveness per element (FIFO template)

Rank = queue position `List.idxOf x`. C2/C3 case splits:

* `Enqueue`: the position of `x` is unchanged (`idxOf_append` + `if_pos`,
  since `x` is already in the queue);
* `Dequeue`: the queue is `h :: t` with `x ∈ t`; nodup forces `x ≠ h`, so the
  position drops by exactly one (`idxOf_cons` with the false beq branch). -/

/-- The template instance watching element `x`. -/
noncomputable def tmpl (x : Fin 3) : FifoTemplate St (Fin 3) where
  queue := St.q
  serve := Dequeue
  x := x
  H := Hspec
  hc2 := by
    intro e hE k hmem hmem'
    have hnd : (e k).q.Nodup := nodup_of_H e hE k
    have hN : StutAction Next vars (e k) (e (k + 1)) := stutAlways_step hE.2
    rcases hN with hnext | hstut
    · rcases hnext with ⟨hne, hs'⟩ | ⟨y, _hg, hs'⟩
      · -- Dequeue: position stays or drops by one
        rw [hs'] at hmem' ⊢
        show (e k).q.tail.idxOf x ≤ (e k).q.idxOf x
        cases hq : (e k).q with
        | nil => exact absurd hq hne
        | cons h t =>
          rw [hq] at hnd hmem'
          rw [List.nodup_cons] at hnd
          cases hhx : (h == x) with
          | true =>
            -- x = h, but x ∈ t contradicts nodup
            have hEq : h = x := eq_of_beq hhx
            exact absurd (hEq.symm ▸ hmem') hnd.1
          | false =>
            rw [List.idxOf_cons, hhx]
            exact Nat.le_succ _
      · -- Enqueue: position unchanged
        rw [hs']
        show ((e k).q ++ [y]).idxOf x ≤ (e k).q.idxOf x
        rw [List.idxOf_append, if_pos hmem]
    · -- Stutter: unchanged
      have : e (k + 1) = e k := hstut
      rw [this]
  hc3 := by
    intro e hE k _hmem hserve hmem'
    have hnd : (e k).q.Nodup := nodup_of_H e hE k
    rcases hserve with ⟨hne, hs'⟩
    rw [hs'] at hmem' ⊢
    show (e k).q.tail.idxOf x < (e k).q.idxOf x
    cases hq : (e k).q with
    | nil => exact absurd hq hne
    | cons h t =>
      rw [hq] at hnd hmem'
      rw [List.nodup_cons] at hnd
      cases hhx : (h == x) with
      | true =>
        have hEq : h = x := eq_of_beq hhx
        exact absurd (hEq.symm ▸ hmem') hnd.1
      | false =>
        rw [List.idxOf_cons, hhx]
        exact Nat.lt_succ_self _

/-- Every queued element is eventually served. -/
theorem elem_liveness (x : Fin 3) :
    Entails (tlaAnd Hspec (globalJustice Dequeue))
      (leadsTo (statePred {s | x ∈ s.q}) (statePred {s | x ∉ s.q})) :=
  (tmpl x).liveness

/-! ## Rule 11: finite family of certificates

Each certificate `i ∈ q ↝ out ≠ []` uses the same position rank; a `Dequeue`
step immediately discharges the goal (the head is logged to `out`), so C3's
left branch fires. The family shares `Hspec` and `Dequeue`, so
`RelRankCert.forall_fin` combines it into `(∃ i, i ∈ q) ↝ out ≠ []`. -/

/-- Certificate for "while `i` waits, some output is eventually produced". -/
noncomputable def outCert (i : Fin 3) :
    RelRankCert St {s | i ∈ s.q} {s | s.out ≠ []} where
  α := ℕ
  r := Dequeue
  φ := {s | i ∈ s.q}
  δ := fun s n => n < s.q.idxOf i
  R := fun s n => n < s.q.length
  H := Hspec
  finiteness := fun _e _n => Set.finite_lt_nat _
  c1 := fun _e _hE _k hp =>
    Or.inr ⟨hp, fun _n hn => Nat.lt_of_lt_of_le hn List.idxOf_le_length⟩
  c2 := by
    intro e hE k hφ
    simp at hφ
    have hN : StutAction Next vars (e k) (e (k + 1)) := stutAlways_step hE.2
    rcases hN with hnext | hstut
    · rcases hnext with ⟨hne, hs'⟩ | ⟨y, _hg, hs'⟩
      · -- Dequeue produces output: the goal holds at k+1
        left
        rw [hs']
        show (e k).out ++ (e k).q.take 1 ≠ []
        cases hq : (e k).q with
        | nil => exact absurd hq hne
        | cons h t =>
          intro hnil
          simp at hnil
      · -- Enqueue: position preserved
        right
        rw [hs']
        show (i ∈ (e k).q ++ [y]) ∧
          ∀ n, n < ((e k).q ++ [y]).idxOf i → n < (e k).q.idxOf i
        refine ⟨List.mem_append.2 (Or.inl hφ), fun n hn => ?_⟩
        rw [List.idxOf_append, if_pos hφ] at hn
        exact hn
    · have : e (k + 1) = e k := hstut
      right
      rw [this]
      exact ⟨hφ, fun _n hn => hn⟩
  c3 := by
    intro e _hE k _hφ hserve
    rcases hserve with ⟨hne, hs'⟩
    left
    rw [hs']
    show (e k).out ++ (e k).q.take 1 ≠ []
    cases hq : (e k).q with
    | nil => exact absurd hq hne
    | cons h t =>
      intro hnil
      simp at hnil

/-- Rule 11: if the queue is nonempty, some output is eventually produced. -/
theorem some_output :
    Entails (tlaAnd Hspec (globalJustice Dequeue))
      (leadsTo (statePred {s | ∃ i, i ∈ s.q}) (statePred {s | s.out ≠ []})) :=
  RelRankCert.forall_fin Hspec Dequeue outCert (fun _ => ⟨rfl, rfl⟩)

/-! ## Execution layer -/

inductive Lbl where
  | dequeue
  | enqueue (y : Fin 3)
deriving DecidableEq, Repr

def guard : Lbl → St → Prop
  | .dequeue, s => s.q ≠ []
  | .enqueue y, s => y ∉ s.q

instance : ∀ l s, Decidable (guard l s)
  | .dequeue, _s => inferInstanceAs (Decidable ¬ _)
  | .enqueue _y, _s => inferInstanceAs (Decidable ¬ _)

def update : Lbl → St → St
  | .dequeue, s => ⟨s.q.tail, s.out ++ s.q.take 1⟩
  | .enqueue y, s => ⟨s.q ++ [y], s.out⟩

def rel : Lbl → Action St
  | .dequeue => Dequeue
  | .enqueue y => Enqueue y

theorem fires : ∀ l s, guard l s → rel l s (update l s) := by
  intro l s hg
  cases l
  · exact ⟨hg, rfl⟩
  · exact ⟨hg, rfl⟩

theorem det : ∀ l s s', rel l s s' → s' = update l s := by
  intro l _s s' hrel
  cases l
  · exact hrel.2
  · exact hrel.2

/-- The executable spec. -/
def execSpec : ExecSpec St where
  lbl := Lbl
  actions := ⟨rel, guard, update, fires, det⟩
  decGuard := fun _l _s => inferInstance

/-- The executable `next` refines the model-layer `Next`. -/
theorem exec_next_refines : ∀ s s',
    StutAction execSpec.next (fun s => s) s s' → StutAction Next vars s s' := by
  intro s s' hstep
  rcases hstep with ⟨l, hrel⟩ | hstut
  · cases l
    · exact Or.inl (Or.inl hrel)
    · exact Or.inl (Or.inr ⟨_, hrel⟩)
  · exact Or.inr hstut

/-- Every executable run keeps the queue nodup, via `run_invariant`. -/
theorem exec_safe (s₀ : St) (hs₀ : Init s₀) (trace : List Lbl) :
    Inv (execSpec.run s₀ trace) := by
  apply execSpec.run_invariant Init Inv init_inv _ s₀ hs₀ trace
  intro s s' hstep hinv
  exact step_inv s s' (exec_next_refines s s' hstep) hinv

-- Smoke run: serve 0, try to re-enqueue 1 (guard fails, stutter), serve 1.
#eval execSpec.run ⟨[0, 1, 2], []⟩ [.dequeue, .enqueue 1, .dequeue]
  -- expect { q := [2], out := [0, 1] }

end Bft.Examples.FifoQueue
