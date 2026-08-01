import Leslie.Action

open TLA

/-! ## Symmetric Shared-Memory Protocol Specifications

    This file defines infrastructure for reasoning about symmetric
    shared-memory protocols — systems where `n` identical processes
    interact through a shared state. The key insight is that if the
    specification is symmetric under permutation of process indices,
    then it suffices to verify a property for process 0 and lift it
    to all processes.

    Definitions:
    - `SymState`: global state with shared component and per-process locals
    - `Perm`: permutations on `Fin n` (self-contained, no Mathlib dependency)
    - `SymState.perm`: permute a state by reindexing locals
    - `SymSharedSpec`: a parameterized shared-memory specification
    - `SymSharedSpec.toSpec`: instantiate to a concrete `Spec` for `n` processes
    - `SymSharedSpec.IsSymmetric`: symmetry conditions
    - `toSpec_perm_invariant`: permutation as refinement
    - `forall_from_focus`: lift a property from process 0 to all processes
-/

namespace SymShared

/-! ### Permutations on `Fin n` -/

/-- A permutation on `Fin n`, defined as a pair of inverse functions. -/
structure Perm (n : Nat) where
  fwd : Fin n → Fin n
  inv : Fin n → Fin n
  fwd_inv : ∀ i, fwd (inv i) = i
  inv_fwd : ∀ i, inv (fwd i) = i

namespace Perm

/-- The identity permutation. -/
def id (n : Nat) : Perm n where
  fwd := _root_.id
  inv := _root_.id
  fwd_inv _ := rfl
  inv_fwd _ := rfl

/-- Compose two permutations. -/
def comp {n : Nat} (π₁ π₂ : Perm n) : Perm n where
  fwd := π₁.fwd ∘ π₂.fwd
  inv := π₂.inv ∘ π₁.inv
  fwd_inv i := by
    show π₁.fwd (π₂.fwd (π₂.inv (π₁.inv i))) = i
    rw [π₂.fwd_inv, π₁.fwd_inv]
  inv_fwd i := by
    show π₂.inv (π₁.inv (π₁.fwd (π₂.fwd i))) = i
    rw [π₁.inv_fwd, π₂.inv_fwd]

/-- The inverse of a permutation. -/
def symm {n : Nat} (π : Perm n) : Perm n where
  fwd := π.inv
  inv := π.fwd
  fwd_inv := π.inv_fwd
  inv_fwd := π.fwd_inv

theorem fwd_injective {n : Nat} (π : Perm n) : Function.Injective π.fwd := by
  intro a b h
  have ha := π.inv_fwd a
  have hb := π.inv_fwd b
  rw [h] at ha
  exact ha.symm.trans hb

theorem inv_injective {n : Nat} (π : Perm n) : Function.Injective π.inv := by
  intro a b h
  have ha := π.fwd_inv a
  have hb := π.fwd_inv b
  rw [h] at ha
  exact ha.symm.trans hb

end Perm

/-! ### Symmetric State -/

/-- Global state for `n` processes: shared component plus per-process local state. -/
structure SymState (Shared Local : Type) (n : Nat) where
  shared : Shared
  locals : Fin n → Local

@[ext]
theorem SymState.ext {Shared Local : Type} {n : Nat}
    {s₁ s₂ : SymState Shared Local n}
    (h_shared : s₁.shared = s₂.shared)
    (h_locals : s₁.locals = s₂.locals) :
    s₁ = s₂ := by
  cases s₁ ; cases s₂ ; simp at * ; exact ⟨h_shared, h_locals⟩

/-- Permute a `SymState` by reindexing the local states via a permutation. -/
def SymState.perm {Shared Local : Type} {n : Nat}
    (π : Perm n) (s : SymState Shared Local n) : SymState Shared Local n where
  shared := s.shared
  locals := s.locals ∘ π.inv

theorem SymState.perm_id {Shared Local : Type} {n : Nat}
    (s : SymState Shared Local n) : s.perm (Perm.id n) = s := by
  apply SymState.ext rfl
  funext i ; rfl

theorem SymState.perm_comp {Shared Local : Type} {n : Nat}
    (π₁ π₂ : Perm n) (s : SymState Shared Local n) :
    (s.perm π₂).perm π₁ = s.perm (π₁.comp π₂) := by
  apply SymState.ext rfl
  rfl

theorem SymState.perm_symm_cancel {Shared Local : Type} {n : Nat}
    (π : Perm n) (s : SymState Shared Local n) :
    (s.perm π).perm π.symm = s := by
  unfold perm Perm.symm
  apply SymState.ext
  · rfl
  · funext i
    simp only [Function.comp]
    congr 1
    exact π.inv_fwd i

theorem SymState.perm_symm_cancel' {Shared Local : Type} {n : Nat}
    (π : Perm n) (s : SymState Shared Local n) :
    (s.perm π.symm).perm π = s := by
  unfold perm Perm.symm
  apply SymState.ext
  · rfl
  · funext i
    simp only [Function.comp]
    congr 1
    exact π.fwd_inv i

/-! ### Symmetric Shared-Memory Specification -/

/-- A symmetric shared-memory protocol specification.
    - `Shared`: the type of shared state
    - `Local`: the type of per-process local state
    - `ActType`: the type of action labels
    - `init_shared`: predicate on initial shared state
    - `init_local`: predicate on initial local state (same for all processes)
    - `step`: transition relation parameterized by process count, acting process,
      and action type -/
structure SymSharedSpec where
  Shared : Type
  Local : Type
  ActType : Type
  init_shared : Shared → Prop
  init_local : Local → Prop
  step : (n : Nat) → Fin n → ActType → SymState Shared Local n → SymState Shared Local n → Prop

/-- Instantiate a `SymSharedSpec` to a concrete `Spec` for `n` processes. -/
def SymSharedSpec.toSpec (spec : SymSharedSpec) (n : Nat) :
    Spec (SymState spec.Shared spec.Local n) where
  init := fun s => spec.init_shared s.shared ∧ ∀ i, spec.init_local (s.locals i)
  next := fun s s' => ∃ (i : Fin n) (a : spec.ActType), spec.step n i a s s'
  fair := []

/-! ### Symmetry Condition -/

/-- A `SymSharedSpec` is symmetric if both the initial condition and the
    step relation are invariant under process-index permutation. -/
structure SymSharedSpec.IsSymmetric (spec : SymSharedSpec) where
  /-- Permuting a valid initial state gives a valid initial state. -/
  init_perm : ∀ (n : Nat) (π : Perm n) (s : SymState spec.Shared spec.Local n),
    (spec.toSpec n).init s → (spec.toSpec n).init (s.perm π)
  /-- If the spec can step from `s` to `s'`, it can step from `s.perm π` to `s'.perm π`. -/
  step_perm : ∀ (n : Nat) (π : Perm n) (s s' : SymState spec.Shared spec.Local n),
    (spec.toSpec n).next s s' → (spec.toSpec n).next (s.perm π) (s'.perm π)

/-! ### Permutation as Refinement -/

/-- Permutation of process indices is a refinement mapping:
    the permuted system refines the original system (for safety). -/
theorem SymSharedSpec.toSpec_perm_invariant (spec : SymSharedSpec)
    (hsym : spec.IsSymmetric) (n : Nat) (π : Perm n) :
    refines_via (SymState.perm π) (spec.toSpec n).safety (spec.toSpec n).safety := by
  apply refinement_mapping_nostutter (spec.toSpec n) (spec.toSpec n) (SymState.perm π)
  · intro s hinit
    exact hsym.init_perm n π s hinit
  · intro s s' hnext
    exact hsym.step_perm n π s s' hnext

/-! ### Focus Theorem: From Process 0 to All Processes -/

/-- Swap permutation: swaps index `0` with index `i`, identity elsewhere. -/
private def Perm.swap0 {n : Nat} [NeZero n] (i : Fin n) : Perm n where
  fwd := fun j => if j = 0 then i else if j = i then 0 else j
  inv := fun j => if j = 0 then i else if j = i then 0 else j
  fwd_inv := by
    intro j
    show (if (if j = 0 then i else if j = i then (0 : Fin n) else j) = 0 then i
          else if (if j = 0 then i else if j = i then (0 : Fin n) else j) = i then 0
          else (if j = 0 then i else if j = i then (0 : Fin n) else j)) = j
    split <;> split <;> simp_all
  inv_fwd := by
    intro j
    show (if (if j = 0 then i else if j = i then (0 : Fin n) else j) = 0 then i
          else if (if j = 0 then i else if j = i then (0 : Fin n) else j) = i then 0
          else (if j = 0 then i else if j = i then (0 : Fin n) else j)) = j
    split <;> split <;> simp_all

/-- If a property `P` on (shared, local) holds always for process 0 under the safety
    specification, then (assuming symmetry) it holds always for all processes.

    The idea: for any process `i`, construct a swap permutation `π` that maps `0` to `i`.
    By `toSpec_perm_invariant`, the permuted execution also satisfies the safety spec.
    In the permuted execution, process 0's local state is the original process `i`'s
    local state, so the hypothesis `h0` gives us the property for process `i`. -/
theorem SymSharedSpec.forall_from_focus (spec : SymSharedSpec)
    (hsym : spec.IsSymmetric) (n : Nat) [NeZero n]
    (P : spec.Shared → spec.Local → Prop)
    (h0 : pred_implies (spec.toSpec n).safety
      [tlafml| □ ⌜ fun s => P s.shared (s.locals (0 : Fin n)) ⌝]) :
    pred_implies (spec.toSpec n).safety
      [tlafml| □ ⌜ fun s => ∀ i, P s.shared (s.locals i) ⌝] := by
  -- Given execution e satisfying safety, show the □∀ property
  intro e hsafety k
  -- Goal is: (state_pred (fun s => ∀ i, P s.shared (s.locals i))) (e.drop k)
  -- Which reduces to: ∀ i, P (e (0 + k)).shared ((e (0 + k)).locals i)
  show (fun s => ∀ i, P s.shared (s.locals i)) (e k)
  intro i
  -- Build the swap permutation that swaps 0 and i
  let π := Perm.swap0 i
  -- The permuted execution: e' m = (e m).perm π
  let e' : TLA.exec (SymState spec.Shared spec.Local n) :=
    TLA.exec.map (SymState.perm π) e
  -- Show e' satisfies safety using toSpec_perm_invariant
  have hsafety' : (spec.toSpec n).safety e' :=
    spec.toSpec_perm_invariant hsym n π e hsafety
  -- Apply h0 to e' to get the property for process 0 in the permuted execution
  have h0' := h0 e' hsafety' k
  -- h0' : (state_pred (fun s => P s.shared (s.locals 0))) (e'.drop k)
  -- which is: P (e' (0 + k)).shared ((e' (0 + k)).locals 0)
  -- Now e' (0 + k) = (e (0 + k)).perm π
  -- So e' (0 + k).shared = (e (0 + k)).shared
  -- And e' (0 + k).locals 0 = (e (0 + k)).locals (π.inv 0) = (e (0 + k)).locals i
  -- Therefore h0' gives us P (e (0 + k)).shared ((e (0 + k)).locals i)
  -- We need to show these are definitionally equal or provide the conversion
  change P ((e k).perm π).shared (((e k).perm π).locals (0 : Fin n)) at h0'
  rw [SymState.perm] at h0'
  simp only [Function.comp] at h0'
  -- h0' : P (e (0+k)).shared ((e (0+k)).locals (π.inv 0))
  -- π.inv 0 = i by definition of swap0
  have hinv0 : π.inv (0 : Fin n) = i := by simp [π, Perm.swap0]
  rw [hinv0] at h0'
  exact h0'

end SymShared
