import TlaDsl.Basic

namespace Tla

/-! # TLA meta-theory: stuttering equivalence

The first meta-theory slice (see `docs/tla-meta-theory.md`): stuttering
equivalence on behaviors, the stuttering-invariance predicate, preservation
theorems for the DSL operators, and the quotient characterization of TLA
formulas (formulas = well-defined predicates on `Behavior / ≈`).

Scope note: `Sim` here is the *finite-stuttering* relation (delete or
duplicate finitely many equal-state runs). Full TLA also identifies
behaviors differing in infinitely many stuttering steps; that needs a
coinductive or block-based definition and is future work (likely with
mathlib). The finite case already captures the essential meta-theory.
-/

/-- Stuttering equivalence (finite version): behaviors are equivalent up to
deleting or inserting finitely many repeated states. -/
inductive Sim {σ : Type u} : Behavior σ → Behavior σ → Prop
  | refl (e : Behavior σ) : Sim e e
  | stepL (e f : Behavior σ) : e 0 = e 1 → Sim (e.drop 1) f → Sim e f
  | stepR (e f : Behavior σ) : f 0 = f 1 → Sim e (f.drop 1) → Sim e f

namespace Sim

/-- Stuttering-equivalent behaviors agree on their first state. -/
theorem first {σ : Type u} {e f : Behavior σ} (h : Sim e f) : e 0 = f 0 := by
  induction h with
  | refl e => rfl
  | stepL e f hst hs ih =>
      have htail : (e.drop 1) 0 = f 0 := ih
      have he1 : e 1 = f 0 := by simpa [Behavior.drop] using htail
      exact hst ▸ he1
  | stepR e f hst hs ih =>
      have htail : e 0 = (f.drop 1) 0 := ih
      have he0 : e 0 = f 1 := by simpa [Behavior.drop] using htail
      exact he0 ▸ hst.symm

/-- If the left behavior stutters, the stutter can be dropped. -/
theorem drop_left {σ : Type u} {e f : Behavior σ} (h : Sim e f) (hst : e 0 = e 1) :
    Sim (e.drop 1) f := by
  induction h with
  | refl e => exact Sim.stepR (e.drop 1) e hst (Sim.refl (e.drop 1))
  | stepL e f hst' hs ih => exact hs
  | stepR e f hst' hs ih => exact Sim.stepR (e.drop 1) f hst' (ih hst)

/-- If the right behavior stutters, the stutter can be dropped. -/
theorem drop_right {σ : Type u} {e f : Behavior σ} (h : Sim e f) (hst : f 0 = f 1) :
    Sim e (f.drop 1) := by
  induction h with
  | refl f => exact Sim.stepL f (f.drop 1) hst (Sim.refl (f.drop 1))
  | stepL e f hst' hs ih => exact Sim.stepL e (f.drop 1) hst' (ih hst)
  | stepR e f hst' hs ih => exact hs

/-- Stuttering equivalence is transitive. -/
theorem trans {σ : Type u} {e f g : Behavior σ} (h : Sim e f) (k : Sim f g) : Sim e g := by
  induction h with
  | refl e => exact k
  | stepL e f hst hs ih => exact Sim.stepL e g hst (ih k)
  | stepR e f hst hs ih => exact ih (drop_left k hst)

/-- Stuttering equivalence is symmetric. -/
theorem symm {σ : Type u} {e f : Behavior σ} (h : Sim e f) : Sim f e := by
  induction h with
  | refl e => exact Sim.refl e
  | stepL e f hst hs ih =>
      have hde : Sim (e.drop 1) e := Sim.stepR (e.drop 1) e hst (Sim.refl (e.drop 1))
      exact Sim.trans ih hde
  | stepR e f hst hs ih =>
      have hdf : Sim f (f.drop 1) := Sim.stepL f (f.drop 1) hst (Sim.refl (f.drop 1))
      exact Sim.trans hdf ih

instance setoid (σ : Type u) : Setoid (Behavior σ) where
  r := Sim
  iseqv := ⟨Sim.refl, Sim.symm, Sim.trans⟩

end Sim

/-- The stuttering quotient: behaviors identified up to finite stuttering. -/
abbrev StutQuot (σ : Type u) := Quot (Sim : Behavior σ → Behavior σ → Prop)

/-- Given a matching of two behaviors, any suffix of the left one matches some
suffix of the right one. -/
theorem sim_suffix_left {σ : Type u} {e f : Behavior σ} (h : Sim e f) :
    ∀ n : Nat, ∃ m : Nat, Sim (e.drop n) (f.drop m) := by
  intro n
  induction h generalizing n with
  | refl e =>
      refine ⟨n, ?_⟩
      exact Sim.refl (e.drop n)
  | stepL e f hst hs ih =>
      cases n with
      | zero =>
          refine ⟨0, ?_⟩
          simpa using (Sim.stepL e f hst hs)
      | succ n =>
          rcases ih n with ⟨m, hm⟩
          refine ⟨m, ?_⟩
          simpa [Behavior.drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hm
  | stepR e f hst hs ih =>
      cases n with
      | zero =>
          refine ⟨0, ?_⟩
          simpa using (Sim.stepR e f hst hs)
      | succ n =>
          rcases ih (n + 1) with ⟨m, hm⟩
          refine ⟨m + 1, ?_⟩
          simpa [Behavior.drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hm

/-- Given a matching of two behaviors, any suffix of the right one matches some
suffix of the left one. -/
theorem sim_suffix_right {σ : Type u} {e f : Behavior σ} (h : Sim e f) :
    ∀ m : Nat, ∃ n : Nat, Sim (e.drop n) (f.drop m) := by
  intro m
  rcases sim_suffix_left (Sim.symm h) m with ⟨n, h'⟩
  refine ⟨n, ?_⟩
  exact Sim.symm h'

/-- A formula is stuttering invariant if it cannot distinguish
stuttering-equivalent behaviors. -/
def StutInv {σ : Type u} (F : Pred σ) : Prop :=
  ∀ e f : Behavior σ, Sim e f → (F e ↔ F f)

/-! ## Preservation theorems -/

theorem stutinv_statePred {σ : Type u} (p : StatePred σ) : StutInv (statePred p) := by
  intro e f h
  constructor <;> intro hpf
  · simpa [statePred] using (Sim.first h ▸ hpf)
  · simpa [statePred] using (Sim.first h ▸ hpf)

theorem stutinv_purePred {σ : Type u} (p : Prop) : StutInv (purePred (σ := σ) p) := by
  intro e f h
  simp [purePred]

theorem stutinv_and {σ : Type u} {F G : Pred σ} (hF : StutInv F) (hG : StutInv G) :
    StutInv (tlaAnd F G) := by
  intro e f h
  constructor <;> intro hfg
  · exact ⟨(hF e f h).1 hfg.1, (hG e f h).1 hfg.2⟩
  · exact ⟨(hF e f h).2 hfg.1, (hG e f h).2 hfg.2⟩

theorem stutinv_or {σ : Type u} {F G : Pred σ} (hF : StutInv F) (hG : StutInv G) :
    StutInv (tlaOr F G) := by
  intro e f h
  constructor <;> intro hfg
  · exact hfg.elim (fun hFe => Or.inl ((hF e f h).1 hFe)) (fun hGe => Or.inr ((hG e f h).1 hGe))
  · exact hfg.elim (fun hFf => Or.inl ((hF e f h).2 hFf)) (fun hGf => Or.inr ((hG e f h).2 hGf))

theorem stutinv_not {σ : Type u} {F : Pred σ} (hF : StutInv F) : StutInv (tlaNot F) := by
  intro e f h
  constructor
  · intro hnf hFf
    exact hnf ((hF e f h).2 hFf)
  · intro hnf hFe
    exact hnf ((hF e f h).1 hFe)

theorem stutinv_imp {σ : Type u} {F G : Pred σ} (hF : StutInv F) (hG : StutInv G) :
    StutInv (tlaImp F G) := by
  intro e f h
  constructor
  · intro hfg hFf
    exact (hG e f h).1 (hfg ((hF e f h).2 hFf))
  · intro hfg hFe
    exact (hG e f h).2 (hfg ((hF e f h).1 hFe))

theorem stutinv_iff {σ : Type u} {F G : Pred σ} (hF : StutInv F) (hG : StutInv G) :
    StutInv (tlaIff F G) := by
  intro e f h
  constructor <;> intro hfg
  · constructor
    · intro hFf
      exact (hG e f h).1 (hfg.1 ((hF e f h).2 hFf))
    · intro hGf
      exact (hF e f h).1 (hfg.2 ((hG e f h).2 hGf))
  · constructor
    · intro hFe
      exact (hG e f h).2 (hfg.1 ((hF e f h).1 hFe))
    · intro hGe
      exact (hF e f h).2 (hfg.2 ((hG e f h).1 hGe))

theorem stutinv_always {σ : Type u} {F : Pred σ} (hF : StutInv F) : StutInv (always F) := by
  intro e f h
  constructor <;> intro hA
  · intro m
    rcases sim_suffix_right h m with ⟨n, hsim⟩
    exact (hF (e.drop n) (f.drop m) hsim).1 (hA n)
  · intro n
    rcases sim_suffix_left h n with ⟨m, hsim⟩
    exact (hF (e.drop n) (f.drop m) hsim).2 (hA m)

theorem stutinv_eventually {σ : Type u} {F : Pred σ} (hF : StutInv F) : StutInv (eventually F) := by
  intro e f h
  constructor <;> intro hE
  · rcases hE with ⟨n, hFn⟩
    rcases sim_suffix_left h n with ⟨m, hsim⟩
    exact ⟨m, (hF (e.drop n) (f.drop m) hsim).1 hFn⟩
  · rcases hE with ⟨m, hFm⟩
    rcases sim_suffix_right h m with ⟨n, hsim⟩
    exact ⟨n, (hF (e.drop n) (f.drop m) hsim).2 hFm⟩

theorem stutinv_leadsTo {σ : Type u} {P Q : Pred σ} (hP : StutInv P) (hQ : StutInv Q) :
    StutInv (leadsTo P Q) := by
  unfold leadsTo
  exact stutinv_always (stutinv_imp hP (stutinv_eventually hQ))

/-! ## The quotient characterization -/

namespace StutInv

/-- A stuttering-invariant formula descends to the quotient. -/
def lift {σ : Type u} {F : Pred σ} (hF : StutInv F) : StutQuot σ → Prop :=
  Quot.lift F (fun e f hsim => propext (hF e f hsim))

theorem lift_apply {σ : Type u} {F : Pred σ} (hF : StutInv F) (e : Behavior σ) :
    hF.lift (Quot.mk Sim e) = F e := by
  simp [StutInv.lift]

end StutInv

/-- Stuttering-invariant formulas are exactly the well-defined predicates on
the stuttering quotient. -/
theorem stutinv_descends {σ : Type u} (F : Pred σ) :
    StutInv F ↔
      ∃ G : StutQuot σ → Prop,
        (∀ e : Behavior σ, G (Quot.mk Sim e) = F e) ∧
          ∀ G' : StutQuot σ → Prop, (∀ e : Behavior σ, G' (Quot.mk Sim e) = F e) → G' = G := by
  constructor
  · intro hF
    refine ⟨hF.lift, ?_⟩
    constructor
    · intro e
      exact hF.lift_apply e
    · intro G hG
      funext q
      refine Quot.ind (β := fun q => G q = hF.lift q) ?_ q
      intro e
      calc
        G (Quot.mk Sim e) = F e := hG e
        _ = hF.lift (Quot.mk Sim e) := (hF.lift_apply e).symm
  · rintro ⟨G, hG, _⟩
    intro e f hsim
    have hq : Quot.mk Sim e = Quot.mk Sim f := Quot.sound hsim
    constructor <;> intro hFe
    · simpa [(hG e).symm, hG f, hq] using hFe
    · simpa [(hG f).symm, hG e, hq.symm] using hFe

/-! ## Some basic proof-calculus theorems -/

theorem entails_always_self {σ : Type u} (F : Pred σ) : Entails (always F) F := by
  intro e h
  simpa using h 0

theorem entails_always_always {σ : Type u} (F : Pred σ) : Entails (always F) (always (always F)) := by
  intro e h n m
  simpa [Behavior.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h (n + m)

theorem entails_eventually_self {σ : Type u} (F : Pred σ) : Entails F (eventually F) := by
  intro e h
  refine ⟨0, ?_⟩
  simpa using h

/-- Leads-to consequence: `□(P' ⇒ P)`, `□(Q ⇒ Q')` and `P ↝ Q` yield `P' ↝ Q'`. -/
theorem leadsTo_consequence {σ : Type u} {P P' Q Q' : Pred σ} :
    Entails (tlaAnd (tlaAnd (always (tlaImp P' P)) (always (tlaImp Q Q'))) (leadsTo P Q))
      (leadsTo P' Q') := by
  intro e h n hP'
  have h1 : ∀ n, P' (e.drop n) → P (e.drop n) := by simpa [always, tlaImp] using h.1.1
  have h2 : ∀ n, Q (e.drop n) → Q' (e.drop n) := by simpa [always, tlaImp] using h.1.2
  have hPQ : ∀ n, P (e.drop n) → eventually Q (e.drop n) := by
    simpa [leadsTo, always, tlaImp] using h.2
  rcases hPQ n (h1 n hP') with ⟨m, hQ⟩
  refine ⟨m, ?_⟩
  simpa [Behavior.drop] using h2 (n + m) (by simpa [Behavior.drop] using hQ)

/-! # Slice 2: near-stuttering invariance and actions

Pre-formulas (actions) are not stuttering invariant, but they are *nearly*
stuttering invariant: their truth transfers between behaviors that agree on
the first state and have stuttering-equivalent tails. This is exactly the
condition under which `□[A]_v`, `◇⟨A⟩_v`, `WF_v(A)` and `SF_v(A)` become
full TLA formulas (stuttering invariant).
-/

/-- Near-stuttering invariance for an action (pre-formula). -/
def NstutInv {σ : Type u} (A : Action σ) : Prop :=
  ∀ e f : Behavior σ, e 0 = f 0 → Sim (e.drop 1) (f.drop 1) →
    (A (e 0) (e 1) ↔ A (f 0) (f 1))

/-- Step-level suffix matching: for each index there is a matching index such
that either the next steps also match, or the left next step matches the same
right position (a stutter on the right). -/
theorem sim_step {σ : Type u} {e f : Behavior σ} (h : Sim e f) :
    ∀ n : Nat, ∃ m : Nat,
      Sim (e.drop n) (f.drop m) ∧
        (Sim (e.drop (n + 1)) (f.drop (m + 1)) ∨ Sim (e.drop (n + 1)) (f.drop m)) := by
  intro n
  induction h generalizing n with
  | refl e =>
      refine ⟨n, Sim.refl (e.drop n), Or.inl (Sim.refl (e.drop (n + 1)))⟩
  | stepL e f hst hs ih =>
      cases n with
      | zero =>
          refine ⟨0, ?_, Or.inr ?_⟩
          · simpa using (Sim.stepL e f hst hs)
          · simpa using hs
      | succ n =>
          rcases ih n with ⟨m, hm₁, hm₂⟩
          refine ⟨m, ?_, ?_⟩
          · simpa [Behavior.drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hm₁
          · cases hm₂ with
            | inl h₂ =>
                exact Or.inl (by simpa [Behavior.drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h₂)
            | inr h₂ =>
                exact Or.inr (by simpa [Behavior.drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h₂)
  | stepR e f hst hs ih =>
      cases n with
      | zero =>
          rcases ih 0 with ⟨m, hm₁, hm₂⟩
          refine ⟨m + 1, ?_, ?_⟩
          · simpa [Behavior.drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hm₁
          · cases hm₂ with
            | inl h₂ =>
                exact Or.inl (by simpa [Behavior.drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h₂)
            | inr h₂ =>
                exact Or.inr (by simpa [Behavior.drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h₂)
      | succ n =>
          rcases ih (n + 1) with ⟨m, hm₁, hm₂⟩
          refine ⟨m + 1, ?_, ?_⟩
          · simpa [Behavior.drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hm₁
          · cases hm₂ with
            | inl h₂ =>
                exact Or.inl (by simpa [Behavior.drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h₂)
            | inr h₂ =>
                exact Or.inr (by simpa [Behavior.drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h₂)

/-- `Unchanged v` is nearly stuttering invariant. -/
theorem nstutinv_unchanged {σ : Type u} {α : Type v} (v : σ → α) :
    NstutInv (Unchanged v) := by
  intro e f hfirst htail
  have hv1 : v (e 1) = v (f 1) := by simpa [Behavior.drop] using congrArg v (Sim.first htail)
  have hv0 : v (e 0) = v (f 0) := congrArg v hfirst
  constructor <;> intro h
  · simpa [Unchanged, hv1, hv0] using h
  · simpa [Unchanged, hv1, hv0] using h

/-- `⟨A⟩_v` is nearly stuttering invariant if `A` is. -/
theorem nstutinv_angle {σ : Type u} {α : Type v} (A : Action σ) (v : σ → α)
    (hA : NstutInv A) : NstutInv (AngleAction A v) := by
  intro e f hfirst htail
  have hv1 : v (e 1) = v (f 1) := by simpa [Behavior.drop] using congrArg v (Sim.first htail)
  have hv0 : v (e 0) = v (f 0) := congrArg v hfirst
  constructor <;> intro h
  · simp [AngleAction] at h
    exact ⟨(hA e f hfirst htail).1 h.1, by simpa [hv1, hv0] using h.2⟩
  · simp [AngleAction] at h
    exact ⟨(hA e f hfirst htail).2 h.1, by simpa [hv1, hv0] using h.2⟩

/-- `[A]_v = A ∨ Unchanged v` is nearly stuttering invariant if `A` is. -/
theorem nstutinv_stutAction {σ : Type u} {α : Type v} (A : Action σ) (v : σ → α)
    (hA : NstutInv A) : NstutInv (StutAction A v) := by
  intro e f hfirst htail
  have hv1 : v (e 1) = v (f 1) := by simpa [Behavior.drop] using congrArg v (Sim.first htail)
  have hv0 : v (e 0) = v (f 0) := congrArg v hfirst
  constructor <;> intro h
  · simp [StutAction] at h
    rcases h with hAe | hve
    · exact Or.inl ((hA e f hfirst htail).1 hAe)
    · exact Or.inr (by simpa [hv1, hv0] using hve)
  · simp [StutAction] at h
    rcases h with hAf | hvf
    · exact Or.inl ((hA e f hfirst htail).2 hAf)
    · exact Or.inr (by simpa [hv1, hv0] using hvf)

/-- `◇⟨A⟩_v` is stuttering invariant if `A` is nearly stuttering invariant. -/
theorem stutinv_eventually_angle {σ : Type u} {α : Type v} (A : Action σ) (v : σ → α)
    (hA : NstutInv A) : StutInv (eventually (actionPred (AngleAction A v))) := by
  have hB : NstutInv (AngleAction A v) := nstutinv_angle A v hA
  intro e f h
  constructor <;> intro hE
  · rcases hE with ⟨n, hBn⟩
    simp [actionPred, AngleAction] at hBn
    rcases sim_step h n with ⟨m, hmn, hmnnext⟩
    rcases hmnnext with hnext | hsame
    · exact ⟨m, (hB (e.drop n) (f.drop m) (Sim.first hmn) (by simpa [Behavior.drop] using hnext)).1 hBn⟩
    · have he1 : (e.drop n) 1 = (e.drop n) 0 := by
        have h1 : e (n + 1) = f m := by simpa [Behavior.drop] using (Sim.first hsame)
        have h2 : e n = f m := by simpa [Behavior.drop] using (Sim.first hmn)
        simpa [Behavior.drop] using h1.trans h2.symm
      exact False.elim (hBn.2 (by simpa [Behavior.drop] using (congrArg v he1)))
  · rcases hE with ⟨m, hBm⟩
    simp [actionPred, AngleAction] at hBm
    rcases sim_step (Sim.symm h) m with ⟨n, hmn, hmnnext⟩
    rcases hmnnext with hnext | hsame
    · exact ⟨n, (hB (f.drop m) (e.drop n) (Sim.first hmn) (by simpa [Behavior.drop] using hnext)).1 hBm⟩
    · have hf1 : (f.drop m) 1 = (f.drop m) 0 := by
        have h1 : f (m + 1) = e n := by simpa [Behavior.drop] using (Sim.first hsame)
        have h2 : f m = e n := by simpa [Behavior.drop] using (Sim.first hmn)
        simpa [Behavior.drop] using h1.trans h2.symm
      exact False.elim (hBm.2 (by simpa [Behavior.drop] using (congrArg v hf1)))

/-- `□[A]_v` is stuttering invariant if `A` is nearly stuttering invariant. -/
theorem stutinv_stutAlways {σ : Type u} {α : Type v} (A : Action σ) (v : σ → α)
    (hA : NstutInv A) : StutInv (stutAlways A v) := by
  have hB : NstutInv (StutAction A v) := nstutinv_stutAction A v hA
  intro e f h
  constructor <;> intro hAll
  · intro m
    rcases sim_step (Sim.symm h) m with ⟨n, hmn, hmnnext⟩
    rcases hmnnext with hnext | hsame
    · exact (hB (f.drop m) (e.drop n) (Sim.first hmn) (by simpa [Behavior.drop] using hnext)).2 (hAll n)
    · have hf1 : (f.drop m) 1 = (f.drop m) 0 := by
        have h1 : f (m + 1) = e n := by simpa [Behavior.drop] using (Sim.first hsame)
        have h2 : f m = e n := by simpa [Behavior.drop] using (Sim.first hmn)
        simpa [Behavior.drop] using h1.trans h2.symm
      exact Or.inr (congrArg v hf1)
  · intro n
    rcases sim_step h n with ⟨m, hmn, hmnnext⟩
    rcases hmnnext with hnext | hsame
    · exact (hB (e.drop n) (f.drop m) (Sim.first hmn) (by simpa [Behavior.drop] using hnext)).2 (hAll m)
    · have he1 : (e.drop n) 1 = (e.drop n) 0 := by
        have h1 : e (n + 1) = f m := by simpa [Behavior.drop] using (Sim.first hsame)
        have h2 : e n = f m := by simpa [Behavior.drop] using (Sim.first hmn)
        simpa [Behavior.drop] using h1.trans h2.symm
      exact Or.inr (congrArg v he1)

/-- Weak fairness is stuttering invariant if the action is nearly so. -/
theorem stutinv_WF_v {σ : Type u} {α : Type v} (A : Action σ) (v : σ → α)
    (hA : NstutInv A) : StutInv (WF_v A v) := by
  unfold WF_v
  exact stutinv_always
    (stutinv_imp (stutinv_always (stutinv_statePred (Enabled (AngleAction A v))))
      (stutinv_eventually_angle A v hA))

/-- Strong fairness is stuttering invariant if the action is nearly so. -/
theorem stutinv_SF_v {σ : Type u} {α : Type v} (A : Action σ) (v : σ → α)
    (hA : NstutInv A) : StutInv (SF_v A v) := by
  unfold SF_v
  exact stutinv_always
    (stutinv_imp (stutinv_always (stutinv_eventually (stutinv_statePred (Enabled (AngleAction A v)))))
      (stutinv_eventually_angle A v hA))

end Tla
