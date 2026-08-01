import Lean
import Leslie.Rules.Basic
import Leslie.Gadgets.TheoremDeriving

/-! Theorems about the leads-to operator. -/

open Classical

namespace TLA

section leads_to

variable {σ : Type u}

-- FIXME: any chance to make the following two lemmas more general
theorem leads_to_exists (Γ q : pred σ) (p : α → pred σ) :
  (∀ (x : α), (Γ) |-tla- ((p x) ↝ q)) ↔ (Γ) |-tla- ((tla_exists p) ↝ q) := by
  tla_unfold_simp ; aesop

theorem leads_to_pure_pred_and (Γ p q : pred σ) (φ : Prop) :
  (φ → (Γ) |-tla- (p ↝ q)) ↔ (Γ) |-tla- (⌞ φ ⌟ ∧ p ↝ q) := by
  tla_unfold_simp ; aesop

@[tla_derive]
theorem leads_to_conseq (p p' q q': pred σ) :
  |-tla- ((p' ⇒ p) → (q ⇒ q') → (p ↝ q) ⇒ (p' ↝ q')) := by
  tla_unfold_simp ; intro e h1 h2 k h k' hh'
  specialize h _ (h1 _ hh') ; rcases h with ⟨k1, h⟩ ; aesop

@[tla_derive]
theorem leads_to_trans (p q r : pred σ) :
  |-tla- ((p ↝ q) → (q ↝ r) → (p ↝ r)) := by
  tla_unfold_simp ; intro e h1 h2 k hh
  specialize h1 _ hh ; rcases h1 with ⟨k1, h1⟩
  specialize h2 _ h1 ; rcases h2 with ⟨k2, h2⟩
  exists (k1 + k2) ; rw [← Nat.add_assoc] ; assumption

theorem leads_to_combine (Γ Γ' p1 q1 p2 q2 : pred σ)
  (h1 : (□ Γ ∧ Γ') |-tla- (p1 ↝ q1))
  (h2 : (□ Γ ∧ Γ') |-tla- (p2 ↝ q2))
  (h1' : (q1 ∧ □ Γ) |-tla- □ q1) (h2' : (q2 ∧ □ Γ) |-tla- □ q2) :
  (□ Γ ∧ Γ') |-tla- (p1 ∧ p2 ↝ q1 ∧ q2) := by
  -- a semantic proof
  tla_unfold_simp ; intro e hΓ hΓ' k hp1 hp2
  specialize h1 _ hΓ hΓ' k hp1 ; rcases h1 with ⟨k1, h1⟩
  specialize h2 _ hΓ hΓ' k hp2 ; rcases h2 with ⟨k2, h2⟩
  exists k1 + k2
  specialize h1' _ h1 (by intro q ; rw [exec.drop_drop] ; apply hΓ) k2
  specialize h2' _ h2 (by intro q ; rw [exec.drop_drop] ; apply hΓ) k1
  simp [exec.drop_drop] at h1' h2'
  constructor ; rw [← Nat.add_assoc] ; assumption ; rw [Nat.add_comm k1 k2, ← Nat.add_assoc] ; assumption

@[tla_derive]
theorem leads_to_strengthen_lhs (p q inv : pred σ) :
  |-tla- (□ inv → (p ∧ inv ↝ q) → (p ↝ q)) := by
  tla_unfold_simp ; aesop

/-! ### Composition under a common hypothesis -/

/-- Chain two leads-to properties under a common hypothesis Γ.
    `(Γ ⊢ p ↝ q) ∧ (Γ ⊢ q ↝ r) → (Γ ⊢ p ↝ r)` -/
theorem leads_to_chain {Γ p q r : pred σ}
    (h1 : pred_implies Γ (leads_to p q))
    (h2 : pred_implies Γ (leads_to q r)) :
    pred_implies Γ (leads_to p r) :=
  fun e hΓ => leads_to_trans p q r e (h1 e hΓ) (h2 e hΓ)

/-- Chain three leads-to properties under a common hypothesis Γ. -/
theorem leads_to_chain3 {Γ p q r s : pred σ}
    (h1 : pred_implies Γ (leads_to p q))
    (h2 : pred_implies Γ (leads_to q r))
    (h3 : pred_implies Γ (leads_to r s)) :
    pred_implies Γ (leads_to p s) :=
  leads_to_chain h1 (leads_to_chain h2 h3)

/-- Disjunction elimination for leads-to under a common hypothesis. -/
theorem leads_to_or {Γ p1 p2 q : pred σ}
    (h1 : pred_implies Γ (leads_to p1 q))
    (h2 : pred_implies Γ (leads_to p2 q)) :
    pred_implies Γ (leads_to (tla_or p1 p2) q) :=
  fun e hΓ k hp => hp.elim (h1 e hΓ k) (h2 e hΓ k)

/-- Trivial leads-to: p ↝ p. -/
theorem leads_to_refl (Γ p : pred σ) :
    pred_implies Γ (leads_to p p) :=
  fun _ _ _k hp => ⟨0, (exec.drop_zero _).symm ▸ hp⟩

/-! ### Well-founded induction for leads-to

    These rules allow proving p ↝ q by providing a Nat-valued measure μ
    that decreases with each step. This is the TLA analogue of
    "proof by well-founded ordering" (Lamport). -/

/-- Well-founded induction for leads-to using a Nat-valued measure.
    If for every k > 0, p ∧ (μ = k) leads to q ∨ (p ∧ μ < k),
    and p ∧ (μ = 0) leads to q, then p leads to q.

    This is the standard TLA lattice rule: each step either achieves q
    or makes progress toward it by decreasing the measure. -/
theorem leads_to_via_nat {Γ : pred σ} {p q : pred σ}
    (μ : (Nat → σ) → Nat)
    (hstep : ∀ k : Nat, k > 0 →
      ∀ e, Γ e → ∀ i, p (e.drop i) → μ (e.drop i) = k →
        ∃ j, q (e.drop (i + j)) ∨ (p (e.drop (i + j)) ∧ μ (e.drop (i + j)) < k))
    (hbase : ∀ e, Γ e → ∀ i, p (e.drop i) → μ (e.drop i) = 0 →
        ∃ j, q (e.drop (i + j))) :
    pred_implies Γ (leads_to p q) := by
  intro e hΓ
  simp only [leads_to]
  -- Suffices: induct on μ using absolute positions in e
  suffices h : ∀ m k, μ (e.drop k) ≤ m → p (e.drop k) →
      ∃ j, q ((e.drop k).drop j) by
    intro k hp; exact h (μ (e.drop k)) k (Nat.le_refl _) hp
  intro m
  induction m with
  | zero =>
    intro k hle hp'
    obtain ⟨j, hj⟩ := hbase e hΓ k hp' (Nat.le_zero.mp hle)
    exact ⟨j, show q ((e.drop k).drop j) by rw [exec.drop_drop]; exact hj⟩
  | succ m ih =>
    intro k hle hp'
    by_cases hm : μ (e.drop k) = 0
    · obtain ⟨j, hj⟩ := hbase e hΓ k hp' hm
      exact ⟨j, show q ((e.drop k).drop j) by rw [exec.drop_drop]; exact hj⟩
    · obtain ⟨j, hj⟩ := hstep (μ (e.drop k)) (Nat.pos_of_ne_zero hm) e hΓ k hp' rfl
      rcases hj with hq | ⟨hp'', hlt⟩
      · exact ⟨j, show q ((e.drop k).drop j) by rw [exec.drop_drop]; exact hq⟩
      · have hle' : μ (e.drop (k + j)) ≤ m := by omega
        obtain ⟨j', hj'⟩ := ih (k + j) hle' hp''
        refine ⟨j + j', ?_⟩
        show q ((e.drop k).drop (j + j'))
        -- All exec.drop_drop collapses to e.drop (n) for some n
        simp only [exec.drop_drop] at hj' ⊢
        -- hj' : q (e (k + j + j')), goal: q (e (k + (j + j')))
        -- These are equal by Nat.add_assoc
        rwa [show k + j + j' = k + (j + j') from by omega] at hj'

/-- Lexicographic well-founded induction for leads_to using two Nat-valued measures.
    Each step either achieves q, or decreases μ₁, or keeps μ₁ the same and decreases μ₂.
    At (0, 0), the base case must achieve q.

    This generalizes `leads_to_via_nat` to lexicographic orderings, useful when
    progress on one dimension can reset the other (e.g., decreasing x while setting
    y to an arbitrary value). -/
theorem leads_to_via_lex {Γ : pred σ} {p q : pred σ}
    (μ₁ μ₂ : (Nat → σ) → Nat)
    (hstep : ∀ k₁ k₂ : Nat, (k₁ > 0 ∨ k₂ > 0) →
      ∀ e, Γ e → ∀ i, p (e.drop i) → μ₁ (e.drop i) = k₁ → μ₂ (e.drop i) = k₂ →
        ∃ j, q (e.drop (i + j)) ∨
          (p (e.drop (i + j)) ∧
            (μ₁ (e.drop (i + j)) < k₁ ∨
              (μ₁ (e.drop (i + j)) = k₁ ∧ μ₂ (e.drop (i + j)) < k₂))))
    (hbase : ∀ e, Γ e → ∀ i, p (e.drop i) → μ₁ (e.drop i) = 0 → μ₂ (e.drop i) = 0 →
        ∃ j, q (e.drop (i + j))) :
    pred_implies Γ (leads_to p q) := by
  -- Reduce to leads_to_via_nat with a combined measure.
  -- Use μ₁ as outer, then for each fixed μ₁, use μ₂ as inner.
  -- Encode: prove ∀ x, (p ∧ μ₁ = x) ↝ q by induction on x.
  -- For each x, prove (p ∧ μ₁ = x) ↝ q using leads_to_via_nat on μ₂.
  apply leads_to_via_nat μ₁
  · -- Outer step: μ₁ = k₁ > 0
    intro k₁ hk₁ e hΓ i hp hμ₁
    -- Use inner leads_to_via_nat on μ₂ to either achieve q or decrease μ₁
    -- For any μ₂ value, one step gives: q ∨ (μ₁ < k₁) ∨ (μ₁ = k₁ ∧ μ₂ decreased)
    -- The inner induction on μ₂ handles the (μ₁ = k₁ ∧ μ₂ decreased) case
    -- until μ₂ reaches 0, at which point the step MUST decrease μ₁ or achieve q
    -- Inner: show (p ∧ μ₁ = k₁) ↝ (q ∨ (p ∧ μ₁ < k₁))
    -- Use leads_to_via_nat on μ₂ for this
    suffices h : ∀ m₂ i', μ₂ (e.drop i') ≤ m₂ → p (e.drop i') → μ₁ (e.drop i') = k₁ →
        ∃ j, q (e.drop (i' + j)) ∨ (p (e.drop (i' + j)) ∧ μ₁ (e.drop (i' + j)) < k₁) by
      exact h (μ₂ (e.drop i)) i (Nat.le_refl _) hp hμ₁
    intro m₂
    induction m₂ with
    | zero =>
      intro i' hle hp' hμ₁'
      have hμ₂' : μ₂ (e.drop i') = 0 := Nat.le_zero.mp hle
      obtain ⟨j, hj⟩ := hstep k₁ 0 (Or.inl hk₁) e hΓ i' hp' hμ₁' hμ₂'
      rcases hj with hq | ⟨hp'', hlt⟩
      · exact ⟨j, Or.inl hq⟩
      · rcases hlt with hlt₁ | ⟨_, hlt₂⟩
        · exact ⟨j, Or.inr ⟨hp'', hlt₁⟩⟩
        · omega  -- μ₂ < 0 impossible
    | succ m₂ ih =>
      intro i' hle hp' hμ₁'
      by_cases hμ₂ : μ₂ (e.drop i') = 0
      · -- μ₂ = 0: same as zero case
        obtain ⟨j, hj⟩ := hstep k₁ 0 (Or.inl hk₁) e hΓ i' hp' hμ₁' hμ₂
        rcases hj with hq | ⟨hp'', hlt⟩
        · exact ⟨j, Or.inl hq⟩
        · rcases hlt with hlt₁ | ⟨_, hlt₂⟩
          · exact ⟨j, Or.inr ⟨hp'', hlt₁⟩⟩
          · omega
      · -- μ₂ > 0: one step
        obtain ⟨j, hj⟩ := hstep k₁ (μ₂ (e.drop i'))
          (Or.inr (Nat.pos_of_ne_zero hμ₂)) e hΓ i' hp' hμ₁' rfl
        rcases hj with hq | ⟨hp'', hlt⟩
        · exact ⟨j, Or.inl hq⟩
        · rcases hlt with hlt₁ | ⟨heq₁, hlt₂⟩
          · -- μ₁ decreased: done
            exact ⟨j, Or.inr ⟨hp'', hlt₁⟩⟩
          · -- μ₁ same, μ₂ decreased: apply IH
            have hle' : μ₂ (e.drop (i' + j)) ≤ m₂ := by omega
            obtain ⟨j', hj'⟩ := ih (i' + j) hle' hp'' heq₁
            exact ⟨j + j', by rw [show i' + (j + j') = i' + j + j' from by omega]; assumption⟩
  · -- Outer base: μ₁ = 0. Use inner leads_to_via_nat on μ₂.
    intro e hΓ i hp hμ₁
    -- Need: ∃ j, q (e.drop (i + j))
    suffices h : ∀ m₂ i', μ₂ (e.drop i') ≤ m₂ → p (e.drop i') → μ₁ (e.drop i') = 0 →
        ∃ j, q (e.drop (i' + j)) by
      exact h (μ₂ (e.drop i)) i (Nat.le_refl _) hp hμ₁
    intro m₂
    induction m₂ with
    | zero =>
      intro i' hle hp' hμ₁'
      exact hbase e hΓ i' hp' hμ₁' (Nat.le_zero.mp hle)
    | succ m₂ ih =>
      intro i' hle hp' hμ₁'
      by_cases hμ₂ : μ₂ (e.drop i') = 0
      · exact hbase e hΓ i' hp' hμ₁' hμ₂
      · obtain ⟨j, hj⟩ := hstep 0 (μ₂ (e.drop i'))
          (Or.inr (Nat.pos_of_ne_zero hμ₂)) e hΓ i' hp' hμ₁' rfl
        rcases hj with hq | ⟨hp'', hlt⟩
        · exact ⟨j, hq⟩
        · rcases hlt with hlt₁ | ⟨heq₁, hlt₂⟩
          · omega  -- μ₁ < 0 impossible
          · have hle' : μ₂ (e.drop (i' + j)) ≤ m₂ := by omega
            obtain ⟨j', hj'⟩ := ih (i' + j) hle' hp'' heq₁
            exact ⟨j + j', by rw [show i' + (j + j') = i' + j + j' from by omega]; assumption⟩

end leads_to

end TLA
