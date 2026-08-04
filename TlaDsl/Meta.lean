import TlaDsl.Basic
import TlaDsl.SimFull

namespace Tla

/-! # TLA meta-theory: stuttering equivalence

The first meta-theory slice (see `docs/tla-meta-theory.md`): stuttering
equivalence on behaviors, the stuttering-invariance predicate, preservation
theorems for the DSL operators, and the quotient characterization of TLA
formulas (formulas = well-defined predicates on `Behavior / ≈`).

Scope note: `Sim` here is the *finite-stuttering* relation (delete or
duplicate finitely many equal-state runs). Full TLA also identifies
behaviors differing in infinitely many stuttering steps; that is handled by
`SimFull` (`TlaDsl/SimFull.lean`, run-compression based) with its own
preservation theorems. The finite case captures the essential meta-theory;
the full case lives in the second half of this file and in `SimFull`.
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
      have he1 : e 1 = f 0 := by simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail
      exact hst ▸ he1
  | stepR e f hst hs ih =>
      have htail : e 0 = (f.drop 1) 0 := ih
      have he0 : e 0 = f 1 := by simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail
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
          simpa [Cslib.ωSequence.drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hm
  | stepR e f hst hs ih =>
      cases n with
      | zero =>
          refine ⟨0, ?_⟩
          simpa using (Sim.stepR e f hst hs)
      | succ n =>
          rcases ih (n + 1) with ⟨m, hm⟩
          refine ⟨m + 1, ?_⟩
          simpa [Cslib.ωSequence.drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hm

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
  simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h (n + m)

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
  simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h2 (n + m) (by simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hQ)

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
          · simpa [Cslib.ωSequence.drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hm₁
          · cases hm₂ with
            | inl h₂ =>
                exact Or.inl (by simpa [Cslib.ωSequence.drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h₂)
            | inr h₂ =>
                exact Or.inr (by simpa [Cslib.ωSequence.drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h₂)
  | stepR e f hst hs ih =>
      cases n with
      | zero =>
          rcases ih 0 with ⟨m, hm₁, hm₂⟩
          refine ⟨m + 1, ?_, ?_⟩
          · simpa [Cslib.ωSequence.drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hm₁
          · cases hm₂ with
            | inl h₂ =>
                exact Or.inl (by simpa [Cslib.ωSequence.drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h₂)
            | inr h₂ =>
                exact Or.inr (by simpa [Cslib.ωSequence.drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h₂)
      | succ n =>
          rcases ih (n + 1) with ⟨m, hm₁, hm₂⟩
          refine ⟨m + 1, ?_, ?_⟩
          · simpa [Cslib.ωSequence.drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hm₁
          · cases hm₂ with
            | inl h₂ =>
                exact Or.inl (by simpa [Cslib.ωSequence.drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h₂)
            | inr h₂ =>
                exact Or.inr (by simpa [Cslib.ωSequence.drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h₂)

/-- `Unchanged v` is nearly stuttering invariant. -/
theorem nstutinv_unchanged {σ : Type u} {α : Type v} (v : σ → α) :
    NstutInv (Unchanged v) := by
  intro e f hfirst htail
  have hv1 : v (e 1) = v (f 1) := by simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using congrArg v (Sim.first htail)
  have hv0 : v (e 0) = v (f 0) := congrArg v hfirst
  constructor <;> intro h
  · simpa [Unchanged, hv1, hv0] using h
  · simpa [Unchanged, hv1, hv0] using h

/-- `⟨A⟩_v` is nearly stuttering invariant if `A` is. -/
theorem nstutinv_angle {σ : Type u} {α : Type v} (A : Action σ) (v : σ → α)
    (hA : NstutInv A) : NstutInv (AngleAction A v) := by
  intro e f hfirst htail
  have hv1 : v (e 1) = v (f 1) := by simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using congrArg v (Sim.first htail)
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
  have hv1 : v (e 1) = v (f 1) := by simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using congrArg v (Sim.first htail)
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
    · exact ⟨m, (hB (e.drop n) (f.drop m) (Sim.first hmn)
        (by simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext)).1
        (by simpa [AngleAction, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hBn)⟩
    · have he1 : (e.drop n) 1 = (e.drop n) 0 := by
        have h1 : e (n + 1) = f m := by simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (Sim.first hsame)
        have h2 : e n = f m := by simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (Sim.first hmn)
        simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h1.trans h2.symm
      exact False.elim (hBn.2 (by simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (congrArg v he1)))
  · rcases hE with ⟨m, hBm⟩
    simp [actionPred, AngleAction] at hBm
    rcases sim_step (Sim.symm h) m with ⟨n, hmn, hmnnext⟩
    rcases hmnnext with hnext | hsame
    · exact ⟨n, (hB (f.drop m) (e.drop n) (Sim.first hmn)
        (by simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext)).1
        (by simpa [AngleAction, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hBm)⟩
    · have hf1 : (f.drop m) 1 = (f.drop m) 0 := by
        have h1 : f (m + 1) = e n := by simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (Sim.first hsame)
        have h2 : f m = e n := by simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (Sim.first hmn)
        simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h1.trans h2.symm
      exact False.elim (hBm.2 (by simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (congrArg v hf1)))

/-- `□[A]_v` is stuttering invariant if `A` is nearly stuttering invariant. -/
theorem stutinv_stutAlways {σ : Type u} {α : Type v} (A : Action σ) (v : σ → α)
    (hA : NstutInv A) : StutInv (stutAlways A v) := by
  have hB : NstutInv (StutAction A v) := nstutinv_stutAction A v hA
  intro e f h
  constructor <;> intro hAll
  · intro m
    rcases sim_step (Sim.symm h) m with ⟨n, hmn, hmnnext⟩
    rcases hmnnext with hnext | hsame
    · exact (hB (f.drop m) (e.drop n) (Sim.first hmn) (by simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext)).2 (hAll n)
    · have hf1 : (f.drop m) 1 = (f.drop m) 0 := by
        have h1 : f (m + 1) = e n := by simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (Sim.first hsame)
        have h2 : f m = e n := by simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (Sim.first hmn)
        simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h1.trans h2.symm
      exact Or.inr (congrArg v hf1)
  · intro n
    rcases sim_step h n with ⟨m, hmn, hmnnext⟩
    rcases hmnnext with hnext | hsame
    · exact (hB (e.drop n) (f.drop m) (Sim.first hmn) (by simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext)).2 (hAll m)
    · have he1 : (e.drop n) 1 = (e.drop n) 0 := by
        have h1 : e (n + 1) = f m := by simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (Sim.first hsame)
        have h2 : e n = f m := by simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (Sim.first hmn)
        simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h1.trans h2.symm
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

/-! # Slice 4: refinement, hiding, canonical forms -/

/-- Concrete spec `conc` refines abstract spec `abs` via state mapping `f`:
every concrete behavior, mapped through `f`, satisfies the abstract spec. -/
def RefinesVia {σ : Type u} {τ : Type v} (f : τ → σ) (conc : Pred τ) (abs : Pred σ) : Prop :=
  ∀ e : Behavior τ, conc e → abs (Cslib.ωSequence.map f e)

/-- Abadi–Lamport safety refinement: if every concrete step (or `v`-stutter)
maps to an abstract step (or `u`-stutter), and initial states map, then the
concrete spec refines the abstract one. -/
theorem refinement_mapping {σ τ : Type u} {α β : Type v}
    (initA : StatePred σ) (nextA : Action σ) (u : σ → α)
    (initC : StatePred τ) (nextC : Action τ) (v : τ → β)
    (f : τ → σ)
    (hinit : ∀ s, initC s → initA (f s))
    (hstep : ∀ s s', (nextC s s' ∨ v s' = v s) → (nextA (f s) (f s') ∨ u (f s') = u (f s))) :
    RefinesVia f (tlaAnd (statePred initC) (stutAlways nextC v))
      (tlaAnd (statePred initA) (stutAlways nextA u)) := by
  intro e he
  constructor
  · exact hinit (e 0) (by simpa [statePred] using he.1)
  · intro n
    have h2 : ∀ n, actionPred (StutAction nextC v) (e.drop n) := by
      simpa [stutAlways, always] using he.2
    have hstepC : StutAction nextC v (e n) (e (n + 1)) := by
      simpa [actionPred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h2 n
    simpa [StutAction, actionPred, Cslib.ωSequence.drop, Cslib.ωSequence.map, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (hstep (e n) (e (n + 1)) hstepC)

/-- Abadi–Lamport refinement with an auxiliary invariant: when the step
correspondence only holds on *reachable* states, thread a concrete invariant
`inv` — implied by `initC`, preserved by every step — into the step case.
This is the form needed for refinements like Paxos → Consensus, where the
mapping's behavior (e.g. "at most one value chosen") is itself an invariant. -/
theorem refinement_mapping_inv {σ τ : Type u} {α β : Type v}
    (initA : StatePred σ) (nextA : Action σ) (u : σ → α)
    (initC : StatePred τ) (nextC : Action τ) (v : τ → β)
    (inv : StatePred τ) (f : τ → σ)
    (hinit : ∀ s, initC s → initA (f s))
    (hinitinv : ∀ s, initC s → inv s)
    (hinv : ∀ s s', (nextC s s' ∨ v s' = v s) → inv s → inv s')
    (hstep : ∀ s s', inv s → (nextC s s' ∨ v s' = v s) →
      (nextA (f s) (f s') ∨ u (f s') = u (f s))) :
    RefinesVia f (tlaAnd (statePred initC) (stutAlways nextC v))
      (tlaAnd (statePred initA) (stutAlways nextA u)) := by
  intro e he
  have h2 : ∀ n, actionPred (StutAction nextC v) (e.drop n) := by
    simpa [stutAlways, always] using he.2
  have hinvAll : ∀ k : Nat, inv (e k) := by
    intro k
    induction k with
    | zero => exact hinitinv (e 0) (by simpa [statePred] using he.1)
    | succ k ih =>
        have hstepC : StutAction nextC v (e k) (e (k + 1)) := by
          simpa [actionPred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h2 k
        exact hinv (e k) (e (k + 1)) hstepC ih
  constructor
  · exact hinit (e 0) (by simpa [statePred] using he.1)
  · intro n
    have hstepC : StutAction nextC v (e n) (e (n + 1)) := by
      simpa [actionPred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h2 n
    have hmap : StutAction nextA u (f (e n)) (f (e (n + 1))) :=
      hstep (e n) (e (n + 1)) (hinvAll n) hstepC
    simpa [StutAction, actionPred, Cslib.ωSequence.drop, Cslib.ωSequence.map, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmap

/-- Abadi–Lamport refinement with liveness: if the initial/step mapping
conditions hold and the liveness conjunct `LC` is preserved by the mapping
(`hL`), then the canonical-form specs refine. This is the full
`Init ∧ □[Next]_v ∧ L` refinement theorem (Theorem 1 of Abadi–Lamport,
including the liveness part). -/
theorem refinement_mapping_liveness {σ τ : Type u} {α β : Type v}
    (initA : StatePred σ) (nextA : Action σ) (u : σ → α)
    (initC : StatePred τ) (nextC : Action τ) (v : τ → β)
    (LC : Pred τ) (LA : Pred σ) (f : τ → σ)
    (hinit : ∀ s, initC s → initA (f s))
    (hstep : ∀ s s', (nextC s s' ∨ v s' = v s) →
      (nextA (f s) (f s') ∨ u (f s') = u (f s)))
    (hL : ∀ e : Behavior τ, LC e → LA (Cslib.ωSequence.map f e)) :
    RefinesVia f
      (tlaAnd (tlaAnd (statePred initC) (stutAlways nextC v)) LC)
      (tlaAnd (tlaAnd (statePred initA) (stutAlways nextA u)) LA) := by
  intro e he
  exact ⟨refinement_mapping initA nextA u initC nextC v f hinit hstep e ⟨he.1.1, he.1.2⟩, hL e he.2⟩

/-- Refinement is transitive. -/
theorem refines_via_trans {σ τ υ : Type u} (f : τ → σ) (g : υ → τ)
    (conc : Pred υ) (mid : Pred τ) (abs : Pred σ)
    (h1 : RefinesVia g conc mid) (h2 : RefinesVia f mid abs) :
    RefinesVia (f ∘ g) conc abs := by
  intro e he
  exact h2 (Cslib.ωSequence.map g e) (h1 e he)

/-- Refinement is reflexive. -/
theorem refines_via_refl {σ : Type u} (F : Pred σ) : RefinesVia (fun s => s) F F := by
  intro e he
  have hmap : Cslib.ωSequence.map (fun s => s) e = e := by
    rfl
  rw [hmap]
  exact he

/-! ## Flexible existential quantification (`\EE`, hiding) -/

/-- Extend a behavior with a state function's values. -/
def Extend {σ : Type u} {τ : Type v} (x : σ → τ) (e : Behavior σ) : Behavior (σ × τ) :=
  fun n => (e n, x (e n))

/-- `\EE x : F` (hiding): F holds on some extension of the behavior. -/
def EEx {σ : Type u} {τ : Type v} (F : Pred (σ × τ)) : Pred σ :=
  fun e => ∃ x : σ → τ, F (Extend x e)

/-- Stuttering equivalence is preserved by extending with a state function. -/
theorem Sim.map {σ : Type u} {τ : Type v} (x : σ → τ) {e f : Behavior σ} (h : Sim e f) :
    Sim (Extend x e) (Extend x f) := by
  induction h with
  | refl e => exact Sim.refl (Extend x e)
  | stepL e f hst hs ih =>
      have htail : (Extend x e).drop 1 = Extend x (e.drop 1) := by
        rfl
      exact Sim.stepL (Extend x e) (Extend x f) (by simp [Extend, hst])
        (by simpa [htail] using ih)
  | stepR e f hst hs ih =>
      have htail : (Extend x f).drop 1 = Extend x (f.drop 1) := by
        rfl
      exact Sim.stepR (Extend x e) (Extend x f) (by simp [Extend, hst])
        (by simpa [htail] using ih)

/-- Hiding preserves stuttering invariance: if `F` is stuttering invariant,
so is `\EE x : F`. -/
theorem stutinv_eex {σ : Type u} {τ : Type v} {F : Pred (σ × τ)} (hF : StutInv F) :
    StutInv (EEx F) := by
  intro e f hsim
  constructor <;> intro hE
  · rcases hE with ⟨x, hFx⟩
    exact ⟨x, (hF (Extend x e) (Extend x f) (Sim.map x hsim)).1 hFx⟩
  · rcases hE with ⟨x, hFx⟩
    exact ⟨x, (hF (Extend x e) (Extend x f) (Sim.map x hsim)).2 hFx⟩

/-- Hiding is monotone. -/
theorem eex_mono {σ : Type u} {τ : Type v} {F G : Pred (σ × τ)} (h : Entails F G) :
    Entails (EEx F) (EEx G) := by
  intro e hE
  rcases hE with ⟨x, hFx⟩
  exact ⟨x, h (Extend x e) hFx⟩

/-- Hiding internal variables is refinement-sound: if the concrete spec
(with internal state `ι` visible) refines the abstract one by projecting
away the internal state, then the hidden spec still refines the abstract
one. This is the `\EE`/internal-variable half of Abadi–Lamport. -/
theorem hiding_refines {σ ι : Type u} (conc : Pred (σ × ι)) (abs : Pred σ)
    (h : RefinesVia (fun st : σ × ι => st.1) conc abs) :
    Entails (EEx conc) abs := by
  intro e hE
  rcases hE with ⟨x, hFx⟩
  have hmap : Cslib.ωSequence.map (fun st : σ × ι => st.1) (Extend x e) = e := by
    ext n
    simp [Cslib.ωSequence.map, Extend]
  exact (hmap ▸ h (Extend x e) hFx)

/-! ## Canonical-form lemmas -/

/-- `□` distributes over `∧`. -/
theorem always_and {σ : Type u} (F G : Pred σ) :
    always (tlaAnd F G) = tlaAnd (always F) (always G) := by
  funext e
  apply propext
  constructor
  · intro h
    exact ⟨fun n => (h n).1, fun n => (h n).2⟩
  · intro h n
    exact ⟨h.1 n, h.2 n⟩

/-- `◇` distributes over `∨`. -/
theorem eventually_or {σ : Type u} (F G : Pred σ) :
    eventually (tlaOr F G) = tlaOr (eventually F) (eventually G) := by
  funext e
  apply propext
  constructor
  · intro h
    rcases h with ⟨n, hFG⟩
    rcases hFG with hF | hG
    · exact Or.inl ⟨n, hF⟩
    · exact Or.inr ⟨n, hG⟩
  · intro h
    rcases h with hF | hG
    · rcases hF with ⟨n, hFn⟩
      exact ⟨n, Or.inl hFn⟩
    · rcases hG with ⟨n, hGn⟩
      exact ⟨n, Or.inr hGn⟩

/-- The canonical form `Init ∧ □[Next]_v ∧ L` entails its initial-state part. -/
theorem spec_init {σ : Type u} {α : Type v} (init : StatePred σ) (next : Action σ)
    (v : σ → α) (L : Pred σ) :
    Entails (tlaAnd (tlaAnd (statePred init) (stutAlways next v)) L) (statePred init) := by
  intro e h
  exact h.1.1

/-- The canonical form entails its next-state part. -/
theorem spec_stutAlways {σ : Type u} {α : Type v} (init : StatePred σ) (next : Action σ)
    (v : σ → α) (L : Pred σ) :
    Entails (tlaAnd (tlaAnd (statePred init) (stutAlways next v)) L) (stutAlways next v) := by
  intro e h
  exact h.1.2

/-- The canonical form entails its liveness part. -/
theorem spec_fair {σ : Type u} {α : Type v} (init : StatePred σ) (next : Action σ)
    (v : σ → α) (L : Pred σ) :
    Entails (tlaAnd (tlaAnd (statePred init) (stutAlways next v)) L) L := by
  intro e h
  exact h.2

/-! # Slice 5: the full stuttering equivalence (action-level migration)

The `StutInvFull` preservation theorems live in `TlaDsl/SimFull.lean`; the
action-level slice migrates here: `NstutInvFull` (the `SimFull` analogue of
`NstutInv`) and the `WF_v`/`SF_v`/`◇⟨A⟩_v`/`□[A]_v` preservation theorems,
which use `SimFull.sim_step`. `SimFull.map` closes the migration with
refinement-side extension.
-/

/-- Near-stuttering invariance for the full equivalence. -/
def NstutInvFull {σ : Type u} (A : Action σ) : Prop :=
  ∀ e f : Behavior σ, e 0 = f 0 → SimFull (e.drop 1) (f.drop 1) →
    (A (e 0) (e 1) ↔ A (f 0) (f 1))

theorem nstutinv_full_unchanged {σ : Type u} {α : Type v} (v : σ → α) :
    NstutInvFull (Unchanged v) := by
  intro e f hfirst htail
  have hv1 : v (e 1) = v (f 1) := by
    simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      congrArg v (SimFull.first htail)
  have hv0 : v (e 0) = v (f 0) := congrArg v hfirst
  constructor <;> intro h
  · simpa [Unchanged, hv1, hv0] using h
  · simpa [Unchanged, hv1, hv0] using h

theorem nstutinv_full_angle {σ : Type u} {α : Type v} (A : Action σ) (v : σ → α)
    (hA : NstutInvFull A) : NstutInvFull (AngleAction A v) := by
  intro e f hfirst htail
  have hv1 : v (e 1) = v (f 1) := by
    simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      congrArg v (SimFull.first htail)
  have hv0 : v (e 0) = v (f 0) := congrArg v hfirst
  constructor <;> intro h
  · simp [AngleAction] at h
    exact ⟨(hA e f hfirst htail).1 h.1, by simpa [hv1, hv0] using h.2⟩
  · simp [AngleAction] at h
    exact ⟨(hA e f hfirst htail).2 h.1, by simpa [hv1, hv0] using h.2⟩

theorem nstutinv_full_stutAction {σ : Type u} {α : Type v} (A : Action σ) (v : σ → α)
    (hA : NstutInvFull A) : NstutInvFull (StutAction A v) := by
  intro e f hfirst htail
  have hv1 : v (e 1) = v (f 1) := by
    simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      congrArg v (SimFull.first htail)
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

/-- `◇⟨A⟩_v` is fully stuttering invariant if `A` is nearly so. -/
theorem stutinv_full_eventually_angle {σ : Type u} {α : Type v} (A : Action σ) (v : σ → α)
    (hA : NstutInvFull A) : StutInvFull (eventually (actionPred (AngleAction A v))) := by
  have hB : NstutInvFull (AngleAction A v) := nstutinv_full_angle A v hA
  intro e f h
  constructor <;> intro hE
  · rcases hE with ⟨n, hBn⟩
    simp [actionPred, AngleAction] at hBn
    rcases SimFull.sim_step h n with ⟨m, hmn, hmnnext⟩
    rcases hmnnext with hnext | hsame
    · exact ⟨m, (hB (e.drop n) (f.drop m) (SimFull.first hmn)
        (by simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext)).1
        (by simpa [AngleAction, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hBn)⟩
    · have he1 : (e.drop n) 1 = (e.drop n) 0 := by
        have h1 : e (n + 1) = f m := by
          simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (SimFull.first hsame)
        have h2 : e n = f m := by
          simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (SimFull.first hmn)
        simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h1.trans h2.symm
      exact False.elim (hBn.2 (by simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (congrArg v he1)))
  · rcases hE with ⟨m, hBm⟩
    simp [actionPred, AngleAction] at hBm
    rcases SimFull.sim_step (SimFull.symm h) m with ⟨n, hmn, hmnnext⟩
    rcases hmnnext with hnext | hsame
    · exact ⟨n, (hB (f.drop m) (e.drop n) (SimFull.first hmn)
        (by simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext)).1
        (by simpa [AngleAction, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hBm)⟩
    · have hf1 : (f.drop m) 1 = (f.drop m) 0 := by
        have h1 : f (m + 1) = e n := by
          simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (SimFull.first hsame)
        have h2 : f m = e n := by
          simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (SimFull.first hmn)
        simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h1.trans h2.symm
      exact False.elim (hBm.2 (by simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (congrArg v hf1)))

/-- `□[A]_v` is fully stuttering invariant if `A` is nearly so. -/
theorem stutinv_full_stutAlways {σ : Type u} {α : Type v} (A : Action σ) (v : σ → α)
    (hA : NstutInvFull A) : StutInvFull (stutAlways A v) := by
  have hB : NstutInvFull (StutAction A v) := nstutinv_full_stutAction A v hA
  intro e f h
  constructor <;> intro hAll
  · intro m
    rcases SimFull.sim_step (SimFull.symm h) m with ⟨n, hmn, hmnnext⟩
    rcases hmnnext with hnext | hsame
    · exact (hB (f.drop m) (e.drop n) (SimFull.first hmn)
        (by simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext)).2 (hAll n)
    · have hf1 : (f.drop m) 1 = (f.drop m) 0 := by
        have h1 : f (m + 1) = e n := by
          simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (SimFull.first hsame)
        have h2 : f m = e n := by
          simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (SimFull.first hmn)
        simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h1.trans h2.symm
      exact Or.inr (congrArg v hf1)
  · intro n
    rcases SimFull.sim_step h n with ⟨m, hmn, hmnnext⟩
    rcases hmnnext with hnext | hsame
    · exact (hB (e.drop n) (f.drop m) (SimFull.first hmn)
        (by simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext)).2 (hAll m)
    · have he1 : (e.drop n) 1 = (e.drop n) 0 := by
        have h1 : e (n + 1) = f m := by
          simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (SimFull.first hsame)
        have h2 : e n = f m := by
          simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (SimFull.first hmn)
        simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h1.trans h2.symm
      exact Or.inr (congrArg v he1)

/-- Weak fairness is fully stuttering invariant if the action is nearly so. -/
theorem stutinv_full_WF_v {σ : Type u} {α : Type v} (A : Action σ) (v : σ → α)
    (hA : NstutInvFull A) : StutInvFull (WF_v A v) := by
  unfold WF_v
  exact stutinv_full_always
    (stutinv_full_imp (stutinv_full_always (stutinv_full_statePred (Enabled (AngleAction A v))))
      (stutinv_full_eventually_angle A v hA))

/-- Strong fairness is fully stuttering invariant if the action is nearly so. -/
theorem stutinv_full_SF_v {σ : Type u} {α : Type v} (A : Action σ) (v : σ → α)
    (hA : NstutInvFull A) : StutInvFull (SF_v A v) := by
  unfold SF_v
  exact stutinv_full_always
    (stutinv_full_imp (stutinv_full_always
      (stutinv_full_eventually (stutinv_full_statePred (Enabled (AngleAction A v)))))
      (stutinv_full_eventually_angle A v hA))

/-! ## `SimFull.map`: extending with a state function -/

/-- `Extend` preserves the change structure. -/
theorem nextBlock_extend {σ : Type u} {τ : Type v} (x : σ → τ) (e : Behavior σ) (n : Nat) :
    nextBlock (Extend x e) n = nextBlock e n := by
  unfold nextBlock
  by_cases hc : ∃ m, n ≤ m ∧ e (m + 1) ≠ e m
  · have hc' : ∃ m, n ≤ m ∧ (Extend x e) (m + 1) ≠ (Extend x e) m := by
      rcases hc with ⟨m, hm1, hm2⟩
      exact ⟨m, hm1, by simp [Extend, hm2]⟩
    rw [dif_pos hc', dif_pos hc]
    congr 1
    exact @Nat.find_congr'
      (fun m => n ≤ m ∧ (Extend x e) (m + 1) ≠ (Extend x e) m)
      (fun m => n ≤ m ∧ e (m + 1) ≠ e m)
      (fun a => @instDecidableAnd (n ≤ a) ((Extend x e) (a + 1) ≠ (Extend x e) a)
        (Nat.decLe n a)
        (@instDecidableNot ((Extend x e) (a + 1) = (Extend x e) a) (Classical.propDecidable _)))
      (fun a => @instDecidableAnd (n ≤ a) (e (a + 1) ≠ e a)
        (Nat.decLe n a)
        (@instDecidableNot (e (a + 1) = e a) (Classical.propDecidable _)))
      hc' hc
      (by
        intro m
        constructor
        · intro hm
          exact ⟨hm.1, by intro hEq; exact hm.2 (by simp [Extend, hEq])⟩
        · intro hm
          exact ⟨hm.1, by simp [Extend, hm.2]⟩)
  · have hc' : ¬ ∃ m, n ≤ m ∧ (Extend x e) (m + 1) ≠ (Extend x e) m := by
      intro hc2
      rcases hc2 with ⟨m, hm1, hm2⟩
      apply hc
      refine ⟨m, hm1, ?_⟩
      intro hEq
      apply hm2
      simp [Extend, hEq]
    rw [dif_neg hc, dif_neg hc']

/-- `Extend` preserves the block structure. -/
theorem BlockStart_extend {σ : Type u} {τ : Type v} (x : σ → τ) (e : Behavior σ) (k : Nat) :
    BlockStart (Extend x e) k = BlockStart e k := by
  induction k with
  | zero => simp [BlockStart]
  | succ k ih =>
      simp [BlockStart, nextBlock_extend, ih]

namespace SimFull

/-- Extending both behaviors with a state function preserves the equivalence. -/
theorem map {σ : Type u} {τ : Type v} (x : σ → τ) {e f : Behavior σ} (h : SimFull e f) :
    SimFull (Extend x e) (Extend x f) := by
  unfold SimFull
  funext k
  have hc : e (BlockStart e k) = f (BlockStart f k) := by
    have hc0 := congrFun h k
    simpa [Compress] using hc0
  have hbe : BlockStart (Extend x e) k = BlockStart e k := BlockStart_extend x e k
  have hbf : BlockStart (Extend x f) k = BlockStart f k := BlockStart_extend x f k
  simp [Compress, hbe, hbf]
  simp [Extend, hc]

end SimFull

/-- Hiding preserves full stuttering invariance: if `F` is invariant under
the full equivalence, so is `\EE x : F`. -/
theorem stutinv_full_eex {σ : Type u} {τ : Type v} {F : Pred (σ × τ)} (hF : StutInvFull F) :
    StutInvFull (EEx F) := by
  intro e f hsim
  constructor <;> intro hE
  · rcases hE with ⟨x, hFx⟩
    exact ⟨x, (hF (Extend x e) (Extend x f) (SimFull.map x hsim)).1 hFx⟩
  · rcases hE with ⟨x, hFx⟩
    exact ⟨x, (hF (Extend x e) (Extend x f) (SimFull.map x hsim)).2 hFx⟩

end Tla
