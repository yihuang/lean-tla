import Bft.Core
import Bft.Rules
import Bft.Exec
import Bft.Tactic

/-!
# Bft.Examples.Minimmit — Minimmit voting core (M5)

A model of the voting core of **Minimmit** (Chou, Lewis-Pye, O'Grady,
"Minimmit: Fast Finality with Even Faster Blocks", arXiv:2508.10862):

* `n ≥ 5f+1` processors, at most `f` Byzantine (`Byz`, `|Byz| ≤ f`).
* One round of votes per view, with **two quorum thresholds on the same
  vote**: `2f+1` votes yield an M-notarisation (view progression), `n−f`
  votes an L-notarisation (= finalisation); `2f+1` nullify votes nullify
  the view.
* Safety rests on quorum intersection (`exists_honest_inter`): two vote
  sets whose sizes sum to more than `n + f` share at least one honest
  processor, which votes at most once per view. This gives
  * `lnot_unique` — two L-notarisations in one view agree (X0);
  * `lnot_not_mnot` — an L-notarised block excludes conflicting
    M-notarisations (X1, uniqueness);
  * `lnot_not_null` — an L-notarised view cannot be nullified (X2).

Pipeline shape: the state is the growing message set; `HonestUniq`
(honest processors vote at most once per view) is the inductive invariant
(`init_invariant_stut`), and the consistency theorem packages X0–X2 as a
temporal `□` statement over reachable states. The executable layer runs
guarded vote actions; a smoke run shows an L-notarisation forming and a
double vote being rejected by the guard.

**Deliberate scope limits** (documented, not hidden): this is the voting
core, not full SMR — no parent blocks, proposal validity clauses, view
progression, or the "nullify by contradiction" retraction rule; and there
is no liveness statement (that requires a partial-synchrony model).
-/

namespace Bft.Examples.Minimmit

/-- A vote in a view: notarise a block, or nullify the view. -/
inductive Vote (Block : Type) where
  | notarize (b : Block)
  | nullify
deriving DecidableEq, Repr

variable (n f : ℕ) (Byz : Finset (Fin n)) {Block : Type} [DecidableEq Block]

/-- A vote message: voter, view, vote. -/
abbrev Msg (n : ℕ) (Block : Type) [DecidableEq Block] := Fin n × ℕ × Vote Block

/-- The state: the set of all vote messages sent so far (monotone growing;
certificates, once formed, persist). -/
structure LSt (n : ℕ) (Block : Type) [DecidableEq Block] where
  msgs : Finset (Msg n Block)

/-! ## Quorums -/

/-- Processors that notarised `b` in view `v`. -/
def notarizers (s : LSt n Block) (v : ℕ) (b : Block) : Finset (Fin n) :=
  (s.msgs.filter fun m => m.2.1 = v ∧ m.2.2 = .notarize b).image (·.1)

/-- Processors that nullified view `v`. -/
def nullifiers (s : LSt n Block) (v : ℕ) : Finset (Fin n) :=
  (s.msgs.filter fun m => m.2.1 = v ∧ m.2.2 = .nullify).image (·.1)

/-- The image keeps the cardinality: within one (view, vote) filter the
first projection is injective. -/
theorem notarizers_card (s : LSt n Block) (v : ℕ) (b : Block) :
    (notarizers n s v b).card =
      (s.msgs.filter fun m => m.2.1 = v ∧ m.2.2 = .notarize b).card := by
  apply Finset.card_image_of_injOn
  rintro ⟨x1, x2, x3⟩ hx ⟨y1, y2, y3⟩ hy hxy
  simp only [Finset.mem_coe, Finset.mem_filter] at hx hy
  simp only [Prod.mk.injEq] at ⊢
  exact ⟨hxy, hx.2.1.trans hy.2.1.symm, hx.2.2.trans hy.2.2.symm⟩

theorem nullifiers_card (s : LSt n Block) (v : ℕ) :
    (nullifiers n s v).card =
      (s.msgs.filter fun m => m.2.1 = v ∧ m.2.2 = .nullify).card := by
  apply Finset.card_image_of_injOn
  rintro ⟨x1, x2, x3⟩ hx ⟨y1, y2, y3⟩ hy hxy
  simp only [Finset.mem_coe, Finset.mem_filter] at hx hy
  simp only [Prod.mk.injEq] at ⊢
  exact ⟨hxy, hx.2.1.trans hy.2.1.symm, hx.2.2.trans hy.2.2.symm⟩

theorem mem_notarizers {s : LSt n Block} {v : ℕ} {b : Block} {i : Fin n} :
    i ∈ notarizers n s v b ↔ (i, v, .notarize b) ∈ s.msgs := by
  simp only [notarizers, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨j, v', w⟩, ⟨hjm, hv, hw⟩, rfl⟩
    have hv' : v' = v := hv
    have hw' : w = .notarize b := hw
    rw [hv', hw'] at hjm
    exact hjm
  · intro h
    exact ⟨(i, v, .notarize b), ⟨h, rfl, rfl⟩, rfl⟩

theorem mem_nullifiers {s : LSt n Block} {v : ℕ} {i : Fin n} :
    i ∈ nullifiers n s v ↔ (i, v, .nullify) ∈ s.msgs := by
  simp only [nullifiers, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨j, v', w⟩, ⟨hjm, hv, hw⟩, rfl⟩
    have hv' : v' = v := hv
    have hw' : w = .nullify := hw
    rw [hv', hw'] at hjm
    exact hjm
  · intro h
    exact ⟨(i, v, .nullify), ⟨h, rfl, rfl⟩, rfl⟩

/-- L-notarisation (finalisation): `n − f` notarise votes. -/
@[reducible] def LNot (s : LSt n Block) (v : ℕ) (b : Block) : Prop :=
  n - f ≤ (notarizers n s v b).card

/-- M-notarisation (view progression): `2f + 1` notarise votes. -/
@[reducible] def MNot (s : LSt n Block) (v : ℕ) (b : Block) : Prop :=
  2 * f + 1 ≤ (notarizers n s v b).card

/-- Nullification: `2f + 1` nullify votes. -/
@[reducible] def Null (s : LSt n Block) (v : ℕ) : Prop :=
  2 * f + 1 ≤ (nullifiers n s v).card

/-! ## Honest uniqueness invariant -/

/-- Honest processors vote at most once per view. -/
def HonestUniq (s : LSt n Block) : Prop :=
  ∀ i : Fin n, i ∉ Byz → ∀ v w₁ w₂,
    (i, v, w₁) ∈ s.msgs → (i, v, w₂) ∈ s.msgs → w₁ = w₂

/-! ## The quorum intersection engine -/

/-- Two vote sets whose sizes sum to more than `n + f` share at least one
honest processor. This single lemma drives all of X0–X2. -/
theorem exists_honest_inter (hB : Byz.card ≤ f) (qA qB : ℕ) {A B : Finset (Fin n)}
    (hA : qA ≤ A.card) (hBq : qB ≤ B.card) (hsum : n + f + 1 ≤ qA + qB) :
    ∃ i, i ∈ A ∧ i ∈ B ∧ i ∉ Byz := by
  have hunion : (A ∪ B).card ≤ n := by
    have h := Finset.card_le_univ (A ∪ B)
    rwa [Fintype.card_fin] at h
  have hinter := Finset.card_union_add_card_inter A B
  have hbig : f + 1 ≤ (A ∩ B).card := by omega
  have hsd := Finset.card_filter_add_card_filter_not (s := A ∩ B) (p := (· ∈ Byz))
  have hle : ((A ∩ B).filter (· ∈ Byz)).card ≤ Byz.card := by
    apply Finset.card_le_card
    intro x hx
    rw [Finset.mem_filter] at hx
    exact hx.2
  have hpos : 0 < ((A ∩ B).filter fun x => ¬ x ∈ Byz).card := by omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hi
  obtain ⟨hi1, hi2⟩ := Finset.mem_inter.mp hi.1
  exact ⟨i, hi1, hi2, hi.2⟩

/-! ## Safety theorems (state level) -/

/-- X0: two L-notarisations in the same view agree. -/
theorem lnot_unique (hn : 5 * f + 1 ≤ n) (hB : Byz.card ≤ f)
    {s : LSt n Block} (hinv : HonestUniq n Byz s) {v : ℕ} {b b' : Block}
    (hL : LNot n f s v b) (hL' : LNot n f s v b') : b = b' := by
  obtain ⟨i, hi1, hi2, hni⟩ :=
    exists_honest_inter n f Byz hB (n - f) (n - f) hL hL' (by omega)
  rw [mem_notarizers] at hi1 hi2
  have h := hinv i hni v _ _ hi1 hi2
  exact Vote.notarize.inj h

/-- X1 (uniqueness): an L-notarised block excludes any conflicting
M-notarisation in the same view. -/
theorem lnot_not_mnot (_hn : 5 * f + 1 ≤ n) (hB : Byz.card ≤ f)
    {s : LSt n Block} (hinv : HonestUniq n Byz s) {v : ℕ} {b b' : Block}
    (hne : b ≠ b') (hL : LNot n f s v b) : ¬ MNot n f s v b' := by
  intro hM
  obtain ⟨i, hi1, hi2, hni⟩ :=
    exists_honest_inter n f Byz hB (n - f) (2 * f + 1) hL hM (by omega)
  rw [mem_notarizers] at hi1 hi2
  have h := Vote.notarize.inj (hinv i hni v _ _ hi1 hi2)
  exact hne h

/-- X2: an L-notarised view cannot be nullified. -/
theorem lnot_not_null (_hn : 5 * f + 1 ≤ n) (hB : Byz.card ≤ f)
    {s : LSt n Block} (hinv : HonestUniq n Byz s) {v : ℕ} {b : Block}
    (hL : LNot n f s v b) : ¬ Null n f s v := by
  intro hN
  obtain ⟨i, hi1, hi2, hni⟩ :=
    exists_honest_inter n f Byz hB (n - f) (2 * f + 1) hL hN (by omega)
  rw [mem_notarizers] at hi1
  rw [mem_nullifiers] at hi2
  have h := hinv i hni v _ _ hi1 hi2
  simp at h

/-! ## Spec -/

/-- An honest processor casts its single vote of view `v`. -/
def HonestVote (i : Fin n) (v : ℕ) (w : Vote Block) :
    Action (LSt n Block) := fun s s' =>
  i ∉ Byz ∧
  (s.msgs.filter fun m => m.1 = i ∧ m.2.1 = v) = ∅ ∧
  s' = ⟨insert (i, v, w) s.msgs⟩

/-- A Byzantine processor votes arbitrarily (including equivocating). -/
def ByzVote (i : Fin n) (v : ℕ) (w : Vote Block) :
    Action (LSt n Block) := fun s s' =>
  i ∈ Byz ∧ s' = ⟨insert (i, v, w) s.msgs⟩

def Next : Action (LSt n Block) := fun s s' =>
  (∃ i v w, HonestVote n Byz i v w s s') ∨ (∃ i v w, ByzVote n Byz i v w s s')

def Init : StatePred (LSt n Block) := fun s => s.msgs = ∅

/-- Frame: all state. -/
def vars (s : LSt n Block) : LSt n Block := s

/-! ## The inductive invariant -/

theorem init_inv : ∀ s : LSt n Block, Init n s → HonestUniq n Byz s := by
  intro s hs i hni v w₁ w₂ h₁ _
  rw [hs] at h₁
  simp at h₁

theorem step_inv : ∀ s s' : LSt n Block,
    StutAction (Next n Byz (Block := Block)) (vars n) s s' →
    HonestUniq n Byz s → HonestUniq n Byz s' := by
  intro s s' hstep hinv j hj v' w₁ w₂ h₁ h₂
  rcases hstep with hnext | hstut
  swap
  · have : s' = s := hstut
    rw [this] at h₁ h₂
    exact hinv j hj v' w₁ w₂ h₁ h₂
  rcases hnext with ⟨i, v, w, hni, hguard, hs'⟩ | ⟨i, v, w, hbi, hs'⟩
  · -- Honest vote by i: j's messages are unchanged unless j = i, v' = v
    have hsm : s'.msgs = insert (i, v, w) s.msgs := by rw [hs']
    rw [hsm] at h₁ h₂
    rw [Finset.mem_insert] at h₁ h₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · -- both are the new vote
      have e1 : w₁ = w := congrArg (fun p : Fin n × ℕ × Vote Block => p.2.2) h₁
      have e2 : w₂ = w := congrArg (fun p : Fin n × ℕ × Vote Block => p.2.2) h₂
      rw [e1, e2]
    · -- w₁ new, w₂ old: the guard forbids any old vote of i in view v
      have hji : j = i := congrArg Prod.fst h₁
      have hvv : v' = v := congrArg (fun p : Fin n × ℕ × Vote Block => p.2.1) h₁
      have hmem : (j, v', w₂) ∈ s.msgs.filter (fun m => m.1 = i ∧ m.2.1 = v) :=
        Finset.mem_filter.mpr ⟨h₂, hji, hvv⟩
      rw [hguard] at hmem
      exact absurd hmem (Finset.notMem_empty _)
    · have hji : j = i := congrArg Prod.fst h₂
      have hvv : v' = v := congrArg (fun p : Fin n × ℕ × Vote Block => p.2.1) h₂
      have hmem : (j, v', w₁) ∈ s.msgs.filter (fun m => m.1 = i ∧ m.2.1 = v) :=
        Finset.mem_filter.mpr ⟨h₁, hji, hvv⟩
      rw [hguard] at hmem
      exact absurd hmem (Finset.notMem_empty _)
    · -- both old
      exact hinv j hj v' w₁ w₂ h₁ h₂
  · -- Byzantine vote by i ∈ Byz: j is honest, so j ≠ i and j's messages
    -- are unchanged
    have hsm : s'.msgs = insert (i, v, w) s.msgs := by rw [hs']
    rw [hsm] at h₁ h₂
    rw [Finset.mem_insert] at h₁ h₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · have hji : j = i := congrArg Prod.fst h₁
      exact absurd (hji.symm ▸ hbi) hj
    · have hji : j = i := congrArg Prod.fst h₁
      exact absurd (hji.symm ▸ hbi) hj
    · have hji : j = i := congrArg Prod.fst h₂
      exact absurd (hji.symm ▸ hbi) hj
    · exact hinv j hj v' w₁ w₂ h₁ h₂

/-- Every reachable state satisfies honest uniqueness. -/
theorem safety :
    Entails (tlaAnd (statePred (Init n (Block := Block)))
        (stutAlways (Next n Byz (Block := Block)) (vars n)))
      (always (statePred (HonestUniq n Byz))) :=
  init_invariant_stut (Init n (Block := Block)) (Next n Byz (Block := Block))
    (vars n) (HonestUniq n Byz) (init_inv n Byz) (step_inv n Byz)

/-- Consistency, packaged as a temporal statement: on every reachable
state, X0 (agreement of L-notarisations), X1 (no conflicting
M-notarisation) and X2 (no nullification) all hold. -/
theorem consistency (hn : 5 * f + 1 ≤ n) (hB : Byz.card ≤ f) :
    Entails (tlaAnd (statePred (Init n (Block := Block)))
        (stutAlways (Next n Byz (Block := Block)) (vars n)))
      (always (statePred fun s : LSt n Block =>
        (∀ v b b', LNot n f s v b → LNot n f s v b' → b = b') ∧
        (∀ v b b', b ≠ b' → LNot n f s v b → ¬ MNot n f s v b') ∧
        (∀ v b, LNot n f s v b → ¬ Null n f s v))) := by
  intro e hE k
  have hinv : HonestUniq n Byz (e k) := by
    have h := safety n Byz e hE k
    simpa [statePred] using h
  simp only [statePred, Cslib.ωSequence.get_drop, Nat.add_zero]
  exact ⟨fun _ _ _ => lnot_unique n f Byz hn hB hinv,
         fun _ _ _ => lnot_not_mnot n f Byz hn hB hinv,
         fun _ _ => lnot_not_null n f Byz hn hB hinv⟩

/-! ## Execution layer -/

/-- Labels: an honest or a Byzantine vote. -/
inductive Lbl (n : ℕ) (Block : Type) where
  | honest (i : Fin n) (v : ℕ) (w : Vote Block)
  | byz (i : Fin n) (v : ℕ) (w : Vote Block)
deriving DecidableEq

def guard : Lbl n Block → LSt n Block → Prop
  | .honest i v _w, s =>
      i ∉ Byz ∧ (s.msgs.filter fun m => m.1 = i ∧ m.2.1 = v) = ∅
  | .byz i _v _w, _s => i ∈ Byz

instance : ∀ (l : Lbl n Block) (s : LSt n Block), Decidable (guard n Byz l s)
  | .honest _ _ _, _s => inferInstanceAs (Decidable (_ ∧ _))
  | .byz _ _ _, _s => inferInstanceAs (Decidable (_ ∈ _))

def update : Lbl n Block → LSt n Block → LSt n Block
  | .honest i v w, s => ⟨insert (i, v, w) s.msgs⟩
  | .byz i v w, s => ⟨insert (i, v, w) s.msgs⟩

def rel : Lbl n Block → Action (LSt n Block)
  | .honest i v w => HonestVote n Byz i v w
  | .byz i v w => ByzVote n Byz i v w

theorem fires : ∀ (l : Lbl n Block) (s : LSt n Block),
    guard n Byz l s → rel n Byz l s (update n l s) := by
  intro l s hg
  cases l
  · exact ⟨hg.1, hg.2, rfl⟩
  · exact ⟨hg, rfl⟩

theorem det : ∀ (l : Lbl n Block) (s s' : LSt n Block),
    rel n Byz l s s' → s' = update n l s := by
  intro l _s s' hrel
  cases l
  · exact hrel.2.2
  · exact hrel.2

/-- The executable spec. -/
def execSpec : ExecSpec (LSt n Block) where
  lbl := Lbl n Block
  actions := ⟨rel n Byz, guard n Byz, update n, fires n Byz, det n Byz⟩
  decGuard := fun _l _s => inferInstance

/-- The executable `next` refines the model-layer `Next`. -/
theorem exec_next_refines : ∀ s s',
    StutAction (execSpec n Byz).next (fun s => s) s s' →
    StutAction (Next n Byz (Block := Block)) (vars n) s s' := by
  intro s s' hstep
  rcases hstep with ⟨l, hrel⟩ | hstut
  · cases l
    · exact Or.inl (Or.inl ⟨_, _, _, hrel⟩)
    · exact Or.inl (Or.inr ⟨_, _, _, hrel⟩)
  · exact Or.inr hstut

/-- Every executable run preserves honest uniqueness. -/
theorem exec_safe (s₀ : LSt n Block) (hs₀ : Init n s₀) (trace : List (Lbl n Block)) :
    HonestUniq n Byz ((execSpec n Byz).run s₀ trace) := by
  apply (execSpec n Byz).run_invariant (Init n) (HonestUniq n Byz) _ _ s₀ hs₀ trace
  · exact init_inv n Byz
  · intro s s' hstep hinv
    exact step_inv n Byz s s' (exec_next_refines n Byz s s' hstep) hinv

/-! ## Smoke run

`n = 6, f = 1` (so `5f + 1 = 6 ✓`), one Byzantine processor (5). Five
honest processors notarise block 0 in view 0 — an L-notarisation
(`n − f = 5`); a double vote by processor 0 is rejected by the guard, and
a Byzantine equivocation goes through but cannot reach any quorum. -/

#eval
  let Byz₁ : Finset (Fin 6) := {5}
  let spec := execSpec 6 Byz₁ (Block := Fin 2)
  let s : LSt 6 (Fin 2) := spec.run ⟨∅⟩
    [.honest 0 0 (.notarize 0), .honest 1 0 (.notarize 0),
     .honest 2 0 (.notarize 0), .honest 3 0 (.notarize 0),
     .honest 4 0 (.notarize 0),
     .honest 0 0 (.notarize 1),   -- double vote: guard rejects (stutter)
     .byz 5 0 (.notarize 1)]      -- Byzantine equivocation: accepted
  ((notarizers 6 s 0 0).card,     -- expect 5 (L-notarisation)
   (notarizers 6 s 0 1).card,     -- expect 1 (only the Byzantine vote)
   decide (LNot 6 1 s 0 0),       -- expect true
   decide (MNot 6 1 s 0 1))       -- expect false (needs 2f+1 = 3)

end Bft.Examples.Minimmit
