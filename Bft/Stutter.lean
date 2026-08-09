import Bft.Core

/-!
# Bft.Stutter — stuttering invariance as a typeclass

`SI F` (stutter-invariant) means the formula `F` is invariant under
insertion/deletion of single stutter steps. These two transformations
generate *finite* stuttering equivalence; the infinite stutter closure (the
full TLA semantics, corresponding to lean-tla's `SimFull` / run compression)
is not handled at this layer — see the honest account in
docs/bft-design.md §2.3.

Design: `SI` is a `Prop`-valued class with an instance per combinator.
Formulas produced by the DSL get their legality proofs automatically through
TC inference; a user-written raw `Pred` fails inference and is flagged at
the `refine` site — legality goes from "after-the-fact discipline" to
"checked at inference time".

Proof organization:

* `drop_insertAt`/`drop_removeAt`: exchange laws between suffixes and
  insertion/deletion (all `ext` + `omega`), stated in `ωSequence.drop`
  dot-notation so the head constants match the goals produced by unfolding
  `always`/`eventually`;
* `si_forall_suffix_imp`: the **master pattern lemma** — a formula of the
  shape `fun e => ∀ k, X (e.drop k) → Y (e.drop k)` is SI whenever `SI X`
  and `SI Y`. `leadsTo` (with `X = P, Y = ◇Q`), `WF_v`, and `SF_v` are all
  instances of it;
* the SI of `stutAlways` is a **direct pointwise argument** (not deep
  meta-theory): the inserted duplicate step satisfies the `Unchanged v`
  disjunct; after deleting a stutter step, every remaining step is still a
  step of the original behavior or a stutter.

## Boundary notes (errata from the first build)

* The deletion-crossing lemma takes `(removeAt e n).drop (k-1) = e.drop k`
  (`n < k`): deletion shifts everything from position `n` onward one step
  left;
* For insertion only the direction `(insertAt e n).drop k = e.drop (k-1)`
  (`n < k`) holds — `(insertAt e n).drop (k-1) = e.drop k` is **false** at
  `k-1 = n` (the head is `e n`, not `e (n+1)`), and the proofs must route
  around this tempting but false form.
-/

namespace Bft

/-- Delete position `n` (a legal stutter deletion only when `e n = e (n+1)`). -/
def removeAt {σ : Type u} (e : Behavior σ) (n : ℕ) : Behavior σ :=
  fun m => if m < n then e m else e (m + 1)

/-- Insert a copy of `e n` after position `n`: positions `n` and `n+1` are both `e n`. -/
def insertAt {σ : Type u} (e : Behavior σ) (n : ℕ) : Behavior σ :=
  fun m => if m ≤ n then e m else e (m - 1)

@[simp] theorem removeAt_apply {σ : Type u} (e : Behavior σ) (n m : ℕ) :
    removeAt e n m = if m < n then e m else e (m + 1) := rfl

@[simp] theorem insertAt_apply {σ : Type u} (e : Behavior σ) (n m : ℕ) :
    insertAt e n m = if m ≤ n then e m else e (m - 1) := rfl

/-- Finite-stuttering invariance. -/
def StutterInvariant {σ : Type u} (F : Pred σ) : Prop :=
  (∀ e n, e n = e (n + 1) → (F (removeAt e n) ↔ F e)) ∧
    (∀ e n, F (insertAt e n) ↔ F e)

/-- The typeclass wrapper: routes legality subgoals through instance inference. -/
class SI {σ : Type u} (F : Pred σ) : Prop where
  inv : StutterInvariant F

/-! ## Exchange laws for suffixes -/

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

/-- The deletion-legality condition at suffix level: if `e n = e (n+1)` and
`k ≤ n`, then `e.drop k` stutters at position `n - k`. -/
theorem drop_removeAt_cond {σ : Type u} (e : Behavior σ) {n k : ℕ}
    (hst : e n = e (n + 1)) (hk : k ≤ n) :
    (e.drop k) (n - k) = (e.drop k) (n - k + 1) := by
  have h1 : k + (n - k) = n := by omega
  have h2 : k + (n - k + 1) = n + 1 := by omega
  rw [Cslib.ωSequence.get_drop, Cslib.ωSequence.get_drop, h1, h2]
  exact hst

/-- Suffixes crossing the deletion point: for `n < k`,
`(removeAt e n).drop (k-1) = e.drop k`. -/
theorem drop_removeAt_pred {σ : Type u} (e : Behavior σ) {n k : ℕ} (hk : n < k) :
    (removeAt e n).drop (k - 1) = e.drop k := by
  ext m
  simp only [Cslib.ωSequence.get_drop, removeAt_apply]
  have h1 : ¬ k - 1 + m < n := by omega
  simp only [h1, if_false]
  congr 1
  omega

/-! ## Basic instances -/

/-- A state predicate reads only the head state; stuttering never changes the
head (deletion uses `e n = e (n+1)`). -/
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

/-- A pure proposition is independent of the behavior. -/
instance {σ : Type u} (p : Prop) : SI (purePred (σ := σ) p) where
  inv := ⟨fun _ _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

/-! ## Combinators preserve SI -/

/-- `□` preserves SI. -/
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

/-- `◇` preserves SI (the dual of `□`). -/
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

/-! ## The master pattern lemma: suffix-quantified implication preserves SI

`leadsTo`/`WF_v`/`SF_v` all have the shape `∀ k, X (e.drop k) → Y (e.drop k)`.
Note that `tlaImp` itself does **not** preserve SI (contravariance of
implication), but the suffix quantification locks it into a safe position. -/

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
      · -- Note: we must use `k + 1`, not `k - 1` — insertion shifts
        -- everything right, `(insertAt e n).drop (k+1) = e.drop k`.
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

/-- `leadsTo P Q = ∀ k, P (e.drop k) → ◇Q (e.drop k)`. -/
instance {σ : Type u} (P Q : Pred σ) [SI P] [SI Q] : SI (leadsTo P Q) where
  inv := si_forall_suffix_imp P (eventually Q)

/-! ## SI of `□[A]_v`: a direct pointwise argument -/

/-- `□[A]_v` is SI: the inserted duplicate step satisfies the `Unchanged v`
disjunct; after deleting a stutter step, every remaining step is still a step
of the original behavior (at the crossing point, via `e n = e (n+1)`). -/
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
            -- h1 : StutAction A v (e m) (e (m+1+1)); e (n+1) = e n (hst, symmetric)
            have e1 : m + 1 + 1 = n + 1 := by omega
            rw [e1, ← hst, ← hmn] at h1
            exact h1
        · by_cases hmn : m = n
          · subst hmn
            -- (e n, e (n+1)) is a stutter step: the Unchanged disjunct
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
          · -- m + 1 = n: crossing the deletion point; second component e (n+1) = e n
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
            -- the inserted duplicate step (e m, e m): the Unchanged disjunct
            rw [insertAt_apply, insertAt_apply, if_pos (le_refl m),
              if_neg (by omega : ¬ m + 1 ≤ m)]
            exact Or.inr rfl
          · rw [insertAt_apply, insertAt_apply, if_neg (by omega : ¬ m ≤ n),
              if_neg (by omega : ¬ m + 1 ≤ n)]
            have h1 := h (m - 1)
            rwa [show m - 1 + 1 = m from by omega] at h1

/-! ## SI of `WF_v` / `SF_v`

`eventually (actionPred ⟨A⟩_v)` is SI (even though `actionPred` itself is
not): `⟨A⟩_v` requires `v` to change, a stutter step can never fire it, so
insertion/deletion only shifts the firing position on either side. -/

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
        · -- m + 1 = n: removeAt's step m is (e m, e (n+1)), i.e. (e m, e n) by hst
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
        · -- m + 1 = n: the goal's second component is e (n+1) = e n by hst
          have e2 : m + 1 = n := by omega
          refine ⟨m, ?_⟩
          rw [removeAt_apply, removeAt_apply, if_pos hmn, if_neg hm1]
          have e1 : m + 1 + 1 = n + 1 := by omega
          rwa [e1, ← hst, ← e2]
        · by_cases hmn2 : m = n
          · -- e's step n is a stutter: `⟨A⟩_v` cannot fire — contradiction
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
        · -- the inserted stutter step does not fire `⟨A⟩_v` — contradiction
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

/-- `WF_v A v = ∀ k, (□⌜Enabled ⟨A⟩_v⌝) (e.drop k) → (◇⟨⟨A⟩_v⟩) (e.drop k)`. -/
instance {σ : Type u} {α : Type v} (A : Action σ) (v : σ → α) : SI (WF_v A v) where
  inv := si_forall_suffix_imp (always (statePred (Enabled (AngleAction A v))))
    (eventually (actionPred (AngleAction A v)))

/-- `SF_v A v = ∀ k, (□◇⌜Enabled ⟨A⟩_v⌝) (e.drop k) → (◇⟨⟨A⟩_v⟩) (e.drop k)`. -/
instance {σ : Type u} {α : Type v} (A : Action σ) (v : σ → α) : SI (SF_v A v) where
  inv := si_forall_suffix_imp
    (always (eventually (statePred (Enabled (AngleAction A v)))))
    (eventually (actionPred (AngleAction A v)))

end Bft
