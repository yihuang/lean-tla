import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import TlaDsl.Basic

namespace Tla

/-! # Finite-state model checking via `native_decide`

A minimal exhaustive invariant checker for finite-state TLA-style specs.
Given a finite state type, a decidable `next` relation and an invariant, the
checker computes the reachable-state fixpoint (the fixpoint is reached within
`Fintype.card` iterations) and reports whether every reachable state
satisfies the invariant.

`mcInvariant_sound` turns a successful check (`by native_decide`) into a
machine-checked invariant theorem over all behaviors, and `mcEntails` gives
the same result in DSL form (`Init ∧ □[Next]_v ⊢ □Inv`). This is the
TLC-style "run the model check, get the theorem" loop.
-/

variable {σ : Type u}

/-- One reachable-set step: add all one-step successors of the current set. -/
def reachStep [Fintype σ] [DecidableEq σ] (next : σ → σ → Prop) [DecidableRel next]
    (S : Finset σ) : Finset σ :=
  S ∪ S.biUnion fun s => Finset.univ.filter fun s' => next s s'

/-- Iterated reachable-set computation: `reachableN next S n` is the set of
states reachable from `S` in at most `n` steps. -/
def reachableN [Fintype σ] [DecidableEq σ] (next : σ → σ → Prop) [DecidableRel next]
    (S : Finset σ) : Nat → Finset σ
  | 0 => S
  | n + 1 => reachableN next (reachStep next S) n

/-- `reachStep` is monotone in the starting set. -/
theorem reachStep_mono [Fintype σ] [DecidableEq σ] (next : σ → σ → Prop) [DecidableRel next]
    {S T : Finset σ} (h : S ⊆ T) : reachStep next S ⊆ reachStep next T := by
  intro s hs
  rcases Finset.mem_union.mp hs with hsS | hsB
  · exact Finset.mem_union_left _ (h hsS)
  · rcases Finset.mem_biUnion.mp hsB with ⟨t, htS, hsf⟩
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨t, h htS, hsf⟩)

/-- The reachable set after `n + 1` iterations is the step-image of the set
after `n` iterations. -/
theorem reachableN_succ [Fintype σ] [DecidableEq σ] (next : σ → σ → Prop) [DecidableRel next]
    (S : Finset σ) (n : Nat) :
    reachableN next S (n + 1) = reachStep next (reachableN next S n) := by
  induction n generalizing S with
  | zero => rfl
  | succ n ih =>
      simpa [reachableN] using ih (reachStep next S)

/-- The reachable set grows by one iteration. -/
theorem reachableN_mem_mono [Fintype σ] [DecidableEq σ] (next : σ → σ → Prop)
    [DecidableRel next] (S : Finset σ) (n : Nat) :
    reachableN next S n ⊆ reachableN next S (n + 1) := by
  rw [reachableN_succ]
  exact Finset.subset_union_left

/-- The reachable set is monotone in the iteration count. -/
theorem reachableN_mono_le [Fintype σ] [DecidableEq σ] (next : σ → σ → Prop)
    [DecidableRel next] (S : Finset σ) {n m : Nat} (hnm : n ≤ m) :
    reachableN next S n ⊆ reachableN next S m := by
  induction m with
  | zero =>
      have hn0 : n = 0 := Nat.eq_zero_of_le_zero hnm
      subst hn0
      rfl
  | succ m ih =>
      by_cases hnm' : n ≤ m
      · exact le_trans (ih hnm') (reachableN_mem_mono next S m)
      · have hnm1 : n = m + 1 := le_antisymm hnm (Nat.succ_le_of_lt (Nat.lt_of_not_ge hnm'))
        subst hnm1
        rfl

/-- Once the reachable set stabilizes, it stays stable. -/
theorem reachableN_eq_stable [Fintype σ] [DecidableEq σ] (next : σ → σ → Prop)
    [DecidableRel next] (S : Finset σ) (n : Nat)
    (h : reachableN next S (n + 1) = reachableN next S n) :
    reachableN next S (n + 2) = reachableN next S (n + 1) := by
  calc
    reachableN next S (n + 2) = reachStep next (reachableN next S (n + 1)) := by
      rw [reachableN_succ]
    _ = reachStep next (reachableN next S n) := by rw [h]
    _ = reachableN next S (n + 1) := by rw [reachableN_succ]

/-- Stability at one point extends to all later iterations. -/
theorem reachableN_stable [Fintype σ] [DecidableEq σ] (next : σ → σ → Prop)
    [DecidableRel next] (S : Finset σ) {k : Nat}
    (h : reachableN next S (k + 1) = reachableN next S k) :
    ∀ m : Nat, k ≤ m → reachableN next S (m + 1) = reachableN next S m := by
  intro m
  induction m with
  | zero => intro hk; have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk; subst hk0; exact h
  | succ m ih =>
      intro hk
      by_cases hkm : k ≤ m
      · exact reachableN_eq_stable next S m (ih hkm)
      · have hkm1 : k = m + 1 := le_antisymm hk (Nat.succ_le_of_lt (Nat.lt_of_not_ge hkm))
        subst hkm1
        exact h

/-- A chain of strict increases must exhaust the state space. -/
theorem chain_size [Fintype σ] [DecidableEq σ] (next : σ → σ → Prop) [DecidableRel next]
    (S : Finset σ) {n : Nat} (h : ∀ i, i < n → reachableN next S i ⊂ reachableN next S (i + 1)) :
    (reachableN next S n).card ≥ n + (reachableN next S 0).card := by
  induction n with
  | zero => simp
  | succ n ih =>
      have ih' : (reachableN next S n).card ≥ n + (reachableN next S 0).card := by
        exact ih (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self n)))
      have hlt := h n (Nat.lt_succ_self n)
      have hcard : (reachableN next S n).card < (reachableN next S (n + 1)).card :=
        Finset.card_lt_card hlt
      omega

/-- The reachable set saturates within `Fintype.card` iterations. -/
theorem reachableN_saturates [Fintype σ] [DecidableEq σ] (next : σ → σ → Prop)
    [DecidableRel next] (S : Finset σ) :
    reachableN next S (Fintype.card σ + 1) = reachableN next S (Fintype.card σ) := by
  by_contra hne
  have hlt0 : reachableN next S (Fintype.card σ) ⊂ reachableN next S (Fintype.card σ + 1) := by
    refine lt_of_le_of_ne (reachableN_mem_mono next S (Fintype.card σ)) ?_
    intro heq
    exact hne heq.symm
  have hstrict : ∀ i, i < Fintype.card σ + 1 →
      reachableN next S i ⊂ reachableN next S (i + 1) := by
    intro i hi
    by_contra hnot
    have heq : reachableN next S (i + 1) = reachableN next S i := by
      apply le_antisymm
      · by_contra hrev
        exact hnot ⟨reachableN_mem_mono next S i, hrev⟩
      · exact reachableN_mem_mono next S i
    have hst := reachableN_stable next S heq (Fintype.card σ) (by omega)
    exact hne hst
  have hsz := chain_size next S (n := Fintype.card σ + 1) hstrict
  have huniv : (reachableN next S (Fintype.card σ + 1)).card ≤ Fintype.card σ :=
    Finset.card_le_univ _
  omega

/-- After saturation, all later iterates equal the saturated set. -/
theorem reachableN_saturates_from [Fintype σ] [DecidableEq σ] (next : σ → σ → Prop)
    [DecidableRel next] (S : Finset σ) {n : Nat} (hn : Fintype.card σ ≤ n) :
    reachableN next S n = reachableN next S (Fintype.card σ) := by
  have hst : ∀ m : Nat, Fintype.card σ ≤ m →
      reachableN next S (m + 1) = reachableN next S m :=
    reachableN_stable next S (reachableN_saturates next S)
  induction n with
  | zero =>
      have hc0 : Fintype.card σ = 0 := by omega
      simp [hc0]
  | succ n ih =>
      by_cases hcn : Fintype.card σ ≤ n
      · rw [hst n hcn, ih hcn]
      · have hn1 : n + 1 = Fintype.card σ := by omega
        rw [← hn1]

/-- Exhaustive invariant check: compute the reachable set and test the
invariant on every state. -/
def mcInvariant [Fintype σ] [DecidableEq σ]
    (init : σ → Prop) (next : σ → σ → Prop) (inv : σ → Prop)
    [∀ s, Decidable (init s)] [DecidableRel next]
    [∀ s, Decidable (inv s)] : Bool :=
  decide (∀ s : σ, s ∈ reachableN next (Finset.univ.filter init) (Fintype.card σ) → inv s)

/-- A successful model check is sound: it yields a machine-checked invariant
for every behavior of the spec. -/
theorem mcInvariant_sound [Fintype σ] [DecidableEq σ]
    (init : σ → Prop) (next : σ → σ → Prop) (inv : σ → Prop)
    [∀ s, Decidable (init s)] [DecidableRel next]
    [∀ s, Decidable (inv s)]
    (h : mcInvariant init next inv = true) :
    ∀ e : Behavior σ, init (e 0) → (∀ n, next (e n) (e (n + 1))) → ∀ n, inv (e n) := by
  intro e hinit hnext n
  have hmem0 : e n ∈ reachableN next (Finset.univ.filter init) n := by
    induction n with
    | zero => simp [reachableN, hinit]
    | succ n ih =>
        rw [reachableN_succ]
        simp [reachStep, Finset.mem_union, Finset.mem_biUnion]
        right
        refine ⟨e n, ih, ?_⟩
        simp [hnext n]
  have hmem : e n ∈ reachableN next (Finset.univ.filter init) (Fintype.card σ) := by
    by_cases hn : n ≤ Fintype.card σ
    · exact reachableN_mono_le next (Finset.univ.filter init) hn hmem0
    · have hsat : reachableN next (Finset.univ.filter init) n =
          reachableN next (Finset.univ.filter init) (Fintype.card σ) :=
        reachableN_saturates_from next (Finset.univ.filter init) (by omega)
      simpa [hsat] using hmem0
  have hall := of_decide_eq_true h
  exact hall (e n) hmem

/-- Model-checked invariant in DSL form: a successful check of
`Next ∨ Unchanged v` yields `Init ∧ □[Next]_v ⊢ □Inv`. -/
theorem mcEntails [Fintype σ] [DecidableEq σ] {α : Type v}
    (init : StatePred σ) (next : Action σ) (v : σ → α) (inv : StatePred σ)
    [∀ s, Decidable (init s)] [DecidableRel next] [∀ s, Decidable (inv s)]
    [∀ s s', Decidable (v s' = v s)]
    (h : mcInvariant init (fun s s' => next s s' ∨ v s' = v s) inv = true) :
    Entails (tlaAnd (statePred init) (stutAlways next v)) (always (statePred inv)) := by
  intro e he
  have h0 : init (e 0) := by simpa [tlaAnd, statePred] using he.1
  have hN : ∀ n, next (e n) (e (n + 1)) ∨ v (e (n + 1)) = v (e n) := by
    intro n
    simpa [stutAlways, always, actionPred, StutAction] using he.2 n
  have hs := mcInvariant_sound init (fun s s' => next s s' ∨ v s' = v s) inv h e h0 hN
  intro n
  simpa [statePred] using hs n

end Tla
