import Leslie.Round
import Leslie.Gadgets.SetFn

/-! ## Quorum Systems

    Reusable quorum system abstraction parameterized over `Fin n`.
    Provides majority, threshold, and unanimous quorum instantiations,
    together with intersection proofs via `filter_disjoint_length_le`.
-/

open TLA

namespace TLA.Combinator

/-! ### Abstract Quorum System -/

/-- A quorum system over `Fin n`: a family of subsets (represented as
    `Fin n → Bool` predicates) closed under a quorum intersection property. -/
structure QuorumSystem (n : Nat) where
  /-- Predicate identifying which subsets are quorums. -/
  isQuorum : (Fin n → Bool) → Prop
  /-- Any two quorums share at least one common member. -/
  intersection : ∀ Q₁ Q₂, isQuorum Q₁ → isQuorum Q₂ →
    ∃ i, Q₁ i = true ∧ Q₂ i = true

/-! ### Counting utility -/

/-- Count the number of `true` entries in a `Fin n → Bool` predicate. -/
def countTrue {n : Nat} (f : Fin n → Bool) : Nat :=
  ((List.finRange n).filter f).length

/-! ### Majority Quorum -/

/-- A strict-majority quorum: more than half the processes. -/
def majorityQuorum (n : Nat) : QuorumSystem n where
  isQuorum := fun Q => countTrue Q * 2 > n
  intersection := by
    intro Q₁ Q₂ hQ₁ hQ₂
    by_contra h
    have h_disj : ∀ x : Fin n, ¬(Q₁ x = true ∧ Q₂ x = true) :=
      fun x hx => h ⟨x, hx⟩
    have hle := filter_disjoint_length_le Q₁ Q₂ (List.finRange n) h_disj
    simp only [List.length_finRange] at hle
    unfold countTrue at hQ₁ hQ₂
    omega

/-! ### Threshold Quorum -/

/-- A threshold quorum: count * den > num * n. This represents the threshold
    "more than num/den of all processes". For intersection to hold we need
    `num * 2 ≥ den` (i.e., threshold > 1/2). -/
def thresholdQuorum (n : Nat) (num den : Nat) (_h_pos : den > 0)
    (h_thresh : num * 2 ≥ den) : QuorumSystem n where
  isQuorum := fun Q => countTrue Q * den > num * n
  intersection := by
    intro Q₁ Q₂ hQ₁ hQ₂
    by_contra h
    have h_disj : ∀ x : Fin n, ¬(Q₁ x = true ∧ Q₂ x = true) :=
      fun x hx => h ⟨x, hx⟩
    have hle := filter_disjoint_length_le Q₁ Q₂ (List.finRange n) h_disj
    simp only [List.length_finRange] at hle
    unfold countTrue at hQ₁ hQ₂
    -- (filter Q₁).length * den > num * n  and  (filter Q₂).length * den > num * n
    -- (filter Q₁).length + (filter Q₂).length ≤ n  and  num * 2 ≥ den
    -- We need: ((filter Q₁).length + (filter Q₂).length) * den > 2 * num * n ≥ den * n
    -- But LHS ≤ n * den. Contradiction.
    -- Strategy: show n * den ≥ ... > ... ≥ n * den, contradiction.
    -- Step 1: (a + b) * den ≤ n * den (from a + b ≤ n)
    have h_ub : ((List.filter Q₁ (List.finRange n)).length +
                 (List.filter Q₂ (List.finRange n)).length) * den ≤ n * den :=
      Nat.mul_le_mul_right den hle
    -- Step 2: a * den + b * den = (a + b) * den
    have h_split : (List.filter Q₁ (List.finRange n)).length * den +
                   (List.filter Q₂ (List.finRange n)).length * den =
                   ((List.filter Q₁ (List.finRange n)).length +
                    (List.filter Q₂ (List.finRange n)).length) * den :=
      (Nat.add_mul _ _ _).symm
    -- Step 3: a * den + b * den > num * n + num * n (from hQ₁ and hQ₂)
    have h_lb : (List.filter Q₁ (List.finRange n)).length * den +
                (List.filter Q₂ (List.finRange n)).length * den >
                num * n + num * n := by omega
    -- Step 4: num * n + num * n ≥ den * n (since num * 2 ≥ den)
    --   num * 2 ≥ den  implies  num + num ≥ den  implies  (num + num) * n ≥ den * n
    have h_thresh_n : (num + num) * n ≥ den * n :=
      Nat.mul_le_mul_right n (by omega)
    have h_rewrite : num * n + num * n = (num + num) * n := (Nat.add_mul num num n).symm
    -- Combine: n * den ≥ (a+b)*den = a*den + b*den > 2*num*n ≥ den*n = n*den
    have h_comm : den * n = n * den := Nat.mul_comm den n
    omega

/-! ### Unanimous Quorum -/

/-- The unanimous quorum: every process must participate.
    Note: for `n = 0`, there are no elements of `Fin 0`, so the universal
    quantifier is vacuously true and any two "quorums" trivially intersect
    (the existential is also vacuously satisfied by Fin.elim0). -/
def unanimousQuorum (n : Nat) (hn : n > 0) : QuorumSystem n where
  isQuorum := fun Q => ∀ i, Q i = true
  intersection := by
    intro Q₁ Q₂ hQ₁ hQ₂
    exact ⟨⟨0, hn⟩, hQ₁ _, hQ₂ _⟩

/-! ### Utility Lemmas -/

/-- If Q is a quorum in the majority system, some element is true. -/
theorem exists_true_of_quorum {n : Nat} {Q : Fin n → Bool}
    (h : (majorityQuorum n).isQuorum Q) : ∃ i, Q i = true := by
  by_contra hall
  have hfalse : ∀ i : Fin n, Q i = false := by
    intro i; cases hq : Q i with
    | false => rfl
    | true => exfalso; exact hall ⟨i, hq⟩
  have hzero : countTrue Q = 0 := by
    unfold countTrue; simp [hfalse]
  simp only [majorityQuorum] at h
  omega

/-- Monotonicity for threshold quorums: if Q is a quorum and Q ⊆ Q', then
    Q' is also a quorum. -/
theorem quorum_monotone {n num den : Nat} {h_pos : den > 0}
    {h_thresh : num * 2 ≥ den}
    {Q Q' : Fin n → Bool}
    (hQ : (thresholdQuorum n num den h_pos h_thresh).isQuorum Q)
    (h_sub : ∀ i, Q i = true → Q' i = true) :
    (thresholdQuorum n num den h_pos h_thresh).isQuorum Q' := by
  simp only [thresholdQuorum] at hQ ⊢
  have hle : countTrue Q ≤ countTrue Q' := by
    unfold countTrue
    exact filter_length_mono (List.finRange n) Q Q' h_sub
  calc num * n < countTrue Q * den := hQ
    _ ≤ countTrue Q' * den := Nat.mul_le_mul_right den hle

/-- The majority quorum is a special case of threshold quorum (num=1, den=2). -/
theorem majorityQuorum_eq_threshold (n : Nat) :
    (majorityQuorum n).isQuorum = (thresholdQuorum n 1 2 (by omega) (by omega)).isQuorum := by
  funext Q
  simp only [majorityQuorum, thresholdQuorum]
  show (countTrue Q * 2 > n) = (countTrue Q * 2 > 1 * n)
  simp

end TLA.Combinator
