import TlaDsl.Meta
import TlaDsl.Rules
import TlaDsl.Coercion
import TlaDsl.Tactic
import TlaDsl.TlaVar
import TlaDsl.LTSRefine

open scoped Tla

/-! # Liveness refinement: prepare–accept consensus under weak fairness

A Paxos-flavoured follow-up to `RefinementLiveness.lean`. The **abstract**
spec decides a value in one step (`decided = none ∧ decided' = some 1`);
weak fairness proves `decided = none ↝ decided = some 1`. The **concrete**
spec implements the decision as two rounds through a `phase` machine and a
prepared `value` — prepare, then accept — where the accept commits the
prepared value. We show:

* `conc_refines_abs`: the concrete refines the abstract by projection
  (`decided`), but the step correspondence only holds on *reachable*
  states — the value must be the prepared `1` and `decided` must be
  `none`/`some 1` — so this uses the invariant-threaded mapping theorem
  (`refinement_mapping_inv`) with `Inv`, the protocol invariant;
* `wf_conc_to_abs`: the concrete weak fairness implies the abstract one on
  the mapped behavior. The first angle step is a prepare, the next is an
  accept — so the concrete eventually decides; after that the abstract
  angle action is disabled forever (the `decided = none` guard), making the
  abstract fairness hold vacuously;
* `conc_leadsTo`: the abstract liveness transfers through the refinement
  (`leadsTo_refines`), so the concrete spec satisfies
  `decided = none ↝ decided = some 1`.
-/

namespace TlaDsl.Examples.PrepareAcceptConsensus

namespace Abs

structure St where
  decided : Option Nat
deriving Repr

tla_var St decided

/-- The abstract spec: decide the value `1` in one step (only while
undecided). -/
@[simp] def Init : Tla.StatePred St := [p| decided = none]
@[simp] def Next : Tla.Action St := [a| decided = none ∧ decided' = some 1]

def Spec : Tla.Pred St := [t| Init ∧ □[Next]_decided]
def SpecWF : Tla.Pred St := [t| (Init ∧ □[Next]_decided) ∧ Tla.WF_v Next decided]

/-- WF1: from `decided = none`, the counter reaches `decided = some 1`. -/
theorem step :
    Tla.Entails (Tla.tlaAnd (Tla.stutAlways Next decided) (Tla.WF_v Next decided))
      (Tla.leadsTo (Tla.statePred (fun s : St => s.decided = none))
        (Tla.statePred (fun s : St => s.decided = some 1))) := by
  tla_wf1

/-- The abstract liveness theorem with the initial state included. -/
theorem spec_leadsTo :
    Tla.Entails SpecWF
      (Tla.leadsTo (Tla.statePred (fun s : St => s.decided = none))
        (Tla.statePred (fun s : St => s.decided = some 1))) := by
  intro e hSpec
  have hbase : Tla.tlaAnd (Tla.stutAlways Next decided) (Tla.WF_v Next decided) e := by
    simpa [SpecWF] using ⟨hSpec.1.2, hSpec.2⟩
  exact step e hbase

end Abs

namespace Conc

structure St where
  phase : Nat
  value : Nat
  decided : Option Nat
deriving Repr

tla_var St phase value decided

/-- Round 1: prepare the value `1` (invisible to `decided`). -/
@[simp] def Prepare : Tla.Action St :=
  [a| phase = 0 ∧ phase' = 1 ∧ value' = 1 ∧ decided' = decided]

/-- Round 2: accept — commit the prepared value and reset the phase. -/
@[simp] def Accept : Tla.Action St :=
  [a| phase = 1 ∧ phase' = 0 ∧ value' = value ∧ decided' = some value]

@[simp] def Next : Tla.Action St := [a| Prepare ∨ Accept]
@[simp] def Vars : St → Nat × Nat × Option Nat := fun s => (s.phase, s.value, s.decided)

@[simp] def Init : Tla.StatePred St := [p| phase = 0 ∧ decided = none]

def Spec : Tla.Pred St := [t| Init ∧ □[Next]_Vars]
def SpecWF : Tla.Pred St := [t| (Init ∧ □[Next]_Vars) ∧ Tla.WF_v Next Vars]

/-- The protocol invariant: the phase machine stays in `{0, 1}`, `decided`
is never a value other than `1`, and when the accept round is armed the
prepared value is `1`. -/
def Inv (s : St) : Prop :=
  (s.phase = 0 ∨ s.phase = 1) ∧
  (s.decided = none ∨ s.decided = some 1) ∧ (s.phase = 1 → s.value = 1)

lemma prepare_phase {s s' : St} (hP : Prepare s s') :
    s'.phase = 1 ∧ s'.value = 1 ∧ s'.decided = s.decided := by
  tla_unfold
  exact ⟨hP.2.1, hP.2.2.1, hP.2.2.2⟩

lemma accept_phase {s s' : St} (hA : Accept s s') :
    s'.phase = 0 ∧ s'.value = s.value ∧ s'.decided = some s.value := by
  tla_unfold
  exact ⟨hA.2.1, hA.2.2.1, hA.2.2.2⟩

/-- The invariant holds initially. -/
lemma inv_init0 (s : St) (hInit : Init s) : Inv s := by
  tla_unfold
  simp [Inv] at hInit ⊢
  exact ⟨Or.inl hInit.1, Or.inl hInit.2, fun h => by simp [hInit.1] at h⟩

/-- The invariant is preserved by every step. -/
lemma inv_step0 (s s' : St) (hstep : Next s s' ∨ Vars s' = Vars s) (hinv : Inv s) :
    Inv s' := by
  rcases hstep with hnext | hstut
  · tla_unfold
    rcases hnext with hP | hA
    · -- prepare: phase → 1, value → 1, decided unchanged
      rcases hinv with ⟨hph, hdec, hval⟩
      rcases hph with h0 | h1
      · constructor
        · exact Or.inr hP.2.1
        · constructor
          · simpa [hP.2.2.2] using hdec
          · intro _
            exact hP.2.2.1
      · exfalso
        omega
    · -- accept: phase → 0, decided → some value (= 1 by the invariant)
      rcases hinv with ⟨hph, hdec, hval⟩
      rcases hph with h0 | h1
      · exfalso
        omega
      · constructor
        · exact Or.inl hA.2.1
        · constructor
          · right
            rw [hA.2.2.2]
            exact congrArg some (hval hA.1)
          · intro hph
            simp [hA.2.1] at hph
  · have hph' : s'.phase = s.phase := by
      simpa [Vars] using congrArg (fun p : Nat × Nat × Option Nat => p.1) hstut
    have hdec' : s'.decided = s.decided := by
      simpa [Vars] using congrArg (fun p : Nat × Nat × Option Nat => p.2.2) hstut
    have hval' : s'.value = s.value := by
      simpa [Vars] using congrArg (fun p : Nat × Nat × Option Nat => p.2.1) hstut
    rcases hinv with ⟨hph, hdec, hval⟩
    constructor
    · rcases hph with h0 | h1
      · exact Or.inl (by simpa [hph'] using h0)
      · exact Or.inr (by simpa [hph'] using h1)
    · constructor
      · rcases hdec with hnone | hsome
        · exact Or.inl (by simpa [hdec'] using hnone)
        · exact Or.inr (by simpa [hdec'] using hsome)
      · intro hph
        have hph0 : s.phase = 1 := by simpa [hph'] using hph
        have hv : s.value = 1 := hval hph0
        simpa [hval'] using hv

/-- The invariant holds at every state of a behavior. -/
lemma inv_all (e : Tla.Behavior St) (hInit : Init (e 0))
    (hN : Tla.stutAlways Next Vars e) : ∀ m, Inv (e m) := by
  intro m
  induction m with
  | zero => exact inv_init0 (e 0) hInit
  | succ m ih =>
      have hstep : Next (e m) (e (m + 1)) ∨ Vars (e (m + 1)) = Vars (e m) := by
        simpa [Tla.stutAlways, Tla.always, Tla.actionPred, Tla.StutAction,
          Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hN m
      exact inv_step0 (e m) (e (m + 1)) hstep ih

/-- Under the invariant, the concrete angle action is enabled: from phase
`0` the raise fires, from phase `1` the accept fires. -/
lemma enabled_all (s : St) (hinv : Inv s) : Tla.Enabled (Tla.AngleAction Next Vars) s := by
  rcases hinv with ⟨hph, hdec, hval⟩
  rcases hph with h0 | h1
  · refine ⟨{ phase := 1, value := 1, decided := s.decided }, ?_⟩
    constructor
    · tla_unfold
      simp [h0]
    · tla_unfold
      simp [h0]
  · refine ⟨{ phase := 0, value := s.value, decided := some s.value }, ?_⟩
    constructor
    · tla_unfold
      simp [h1]
    · tla_unfold
      simp [h1]

/-- In a concrete behavior, a non-angle step does not change the frame. -/
lemma frame_stable_between (e : Tla.Behavior St)
    (hN : Tla.stutAlways Next Vars e) {a b : Nat} (hab : a ≤ b)
    (hno : ∀ i, a ≤ i → i < b →
      ¬ Tla.AngleAction Next Vars (e i) (e (i + 1))) :
    Vars (e b) = Vars (e a) := by
  apply Tla.step_eq_of_all e Vars hab
  intro i hi hlt
  have hstep : Next (e i) (e (i + 1)) ∨ Vars (e (i + 1)) = Vars (e i) := by
    simpa [Tla.stutAlways, Tla.always, Tla.actionPred, Tla.StutAction,
      Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hN i
  rcases hstep with hNc | hstut
  · by_contra hne
    exact hno i hi hlt ⟨hNc, hne⟩
  · exact hstut

/-- Under the concrete spec's weak fairness, the protocol eventually
decides: the first angle step is a prepare, the next is an accept, and the
accept commits the prepared value `1`. From then on the prepared value
stays `1`, which the liveness transfer uses to show `decided` is stable. -/
lemma decides_eventually (e : Tla.Behavior St)
    (hInit : Init (e 0)) (hN : Tla.stutAlways Next Vars e)
    (hInvAll : ∀ m, Inv (e m)) (hWF : Tla.WF_v Next Vars e) :
    ∃ D : Nat, (e (D + 1)).decided = some 1 ∧ (e D).decided = none ∧
      ∀ m, D + 1 ≤ m → (e m).value = 1 := by
  classical
  have hWF' : ∀ n, (Tla.always (Tla.statePred (Tla.Enabled (Tla.AngleAction Next Vars)))
        (e.drop n)) → Tla.eventually (Tla.actionPred (Tla.AngleAction Next Vars)) (e.drop n) := by
    simpa [Tla.WF_v, Tla.always, Tla.tlaImp] using hWF
  have hEnAlways : ∀ m, Tla.always (Tla.statePred (Tla.Enabled (Tla.AngleAction Next Vars)))
      (e.drop m) := by
    intro m
    simpa [Tla.always, Tla.statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using fun k => enabled_all (e (m + k)) (hInvAll (m + k))
  have hAng : ∀ m, ∃ j, Tla.AngleAction Next Vars (e (m + j)) (e (m + j + 1)) := by
    intro m
    rcases hWF' m (hEnAlways m) with ⟨j, hj⟩
    exact ⟨j, by
      simpa [Tla.actionPred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hj⟩
  -- the first angle step is a prepare (the phase is still 0)
  let j0 := Nat.find (p := fun j => Tla.AngleAction Next Vars (e j) (e (j + 1)))
    (by simpa using hAng 0)
  have hj0 : Tla.AngleAction Next Vars (e j0) (e (j0 + 1)) :=
    Nat.find_spec (p := fun j => Tla.AngleAction Next Vars (e j) (e (j + 1)))
      (by simpa using hAng 0)
  have hmin0 : ∀ j < j0, ¬ Tla.AngleAction Next Vars (e j) (e (j + 1)) :=
    by
      intro j hj
      exact Nat.find_min (p := fun j => Tla.AngleAction Next Vars (e j) (e (j + 1)))
        (by simpa using hAng 0) (by simpa [j0] using hj)
  have hstab0 : Vars (e j0) = Vars (e 0) := by
    apply frame_stable_between e hN
    · omega
    · intro i hi hlt
      exact hmin0 i hlt
  have hphase0 : (e j0).phase = 0 := by
    have hst : (e j0).phase = (e 0).phase := by
      simpa [Vars] using congrArg (fun p : Nat × Nat × Option Nat => p.1) hstab0
    exact hst.trans hInit.1
  have hprep : (e (j0 + 1)).phase = 1 ∧ (e (j0 + 1)).value = 1 ∧
      (e (j0 + 1)).decided = (e j0).decided := by
    rcases hj0.1 with hP | hA
    · exact prepare_phase hP
    · exfalso
      simp [hphase0] at hA
  -- the next angle step is an accept
  let j1 := Nat.find (p := fun j => Tla.AngleAction Next Vars (e (j0 + 1 + j)) (e (j0 + 1 + j + 1)))
    (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hAng (j0 + 1))
  have hj1 : Tla.AngleAction Next Vars (e (j0 + 1 + j1)) (e (j0 + 1 + j1 + 1)) :=
    Nat.find_spec (p := fun j =>
      Tla.AngleAction Next Vars (e (j0 + 1 + j)) (e (j0 + 1 + j + 1)))
      (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hAng (j0 + 1))
  have hmin1 : ∀ j < j1, ¬ Tla.AngleAction Next Vars (e (j0 + 1 + j)) (e (j0 + 1 + j + 1)) :=
    by
      intro j hj
      exact Nat.find_min (p := fun j =>
        Tla.AngleAction Next Vars (e (j0 + 1 + j)) (e (j0 + 1 + j + 1)))
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hAng (j0 + 1))
        (by simpa [j1] using hj)
  have hstab1 : Vars (e (j0 + 1 + j1)) = Vars (e (j0 + 1)) := by
    apply frame_stable_between e hN
    · omega
    · intro i hi hlt
      have hj : i - (j0 + 1) < j1 := by omega
      have hnot := hmin1 (i - (j0 + 1)) hj
      have h1 : j0 + 1 + (i - (j0 + 1)) = i := by omega
      rw [h1] at hnot
      exact hnot
  have hphase1 : (e (j0 + 1 + j1)).phase = 1 := by
    have hst : (e (j0 + 1 + j1)).phase = (e (j0 + 1)).phase := by
      simpa [Vars] using congrArg (fun p : Nat × Nat × Option Nat => p.1) hstab1
    exact hst.trans hprep.1
  have hdec : (e (j0 + 1 + j1 + 1)).decided = some 1 := by
    rcases hj1.1 with hP | hA
    · exfalso
      simp [hphase1] at hP
    · have hacc := accept_phase hA
      have hval : (e (j0 + 1 + j1)).value = 1 := by
        have hst : (e (j0 + 1 + j1)).value = (e (j0 + 1)).value := by
          simpa [Vars] using congrArg (fun p : Nat × Nat × Option Nat => p.2.1) hstab1
        exact hst.trans hprep.2.1
      rw [hacc.2.2]
      exact congrArg some hval
  have hdec0 : (e (j0 + 1 + j1)).decided = none := by
    have hst : (e (j0 + 1 + j1)).decided = (e (j0 + 1)).decided := by
      simpa [Vars] using congrArg (fun p : Nat × Nat × Option Nat => p.2.2) hstab1
    have hkeep : (e (j0 + 1)).decided = none := by
      have hst0 : (e j0).decided = (e 0).decided := by
        simpa [Vars] using congrArg (fun p : Nat × Nat × Option Nat => p.2.2) hstab0
      exact hprep.2.2.trans (hst0.trans hInit.2)
    exact hst.trans hkeep
  let D := j0 + 1 + j1
  refine ⟨D, ?_, ?_, ?_⟩
  · have hidx : j0 + 1 + j1 + 1 = D + 1 := by simp [D]
    rw [hidx] at hdec
    exact hdec
  · simpa [D] using hdec0
  · -- the prepared value stays `1` from the first prepare on
    intro m hm
    have hval0 : ∀ m, j0 + 1 ≤ m → (e m).value = 1 := by
      intro m hm0
      induction m, hm0 using Nat.le_induction with
      | base =>
          exact hprep.2.1
      | succ m hm ih =>
          have hstep : Next (e m) (e (m + 1)) ∨ Vars (e (m + 1)) = Vars (e m) := by
            simpa [Tla.stutAlways, Tla.always, Tla.actionPred, Tla.StutAction,
              Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hN m
          rcases hstep with hNc | hstut
          · rcases hNc with hP | hA
            · exact (prepare_phase hP).2.1
            · exact (accept_phase hA).2.1.trans ih
          · have hkeep : (e (m + 1)).value = (e m).value := by
              simpa [Vars] using congrArg (fun p : Nat × Nat × Option Nat => p.2.1) hstut
            exact hkeep.trans ih
    exact hval0 m (by omega)

end Conc

/-! ## The refinement -/

/-- The refinement mapping: project away the phase and the prepared value. -/
def f : Conc.St → Abs.St := fun s => { decided := s.decided }

theorem init_refines : ∀ s, Conc.Init s → Abs.Init (f s) := by
  intro s hs
  tla_unfold
  simp [f] at hs ⊢
  exact hs.2

/-- The step correspondence holds on reachable (invariant) states. -/
theorem step_refines : ∀ s s', Conc.Inv s → (Conc.Next s s' ∨ Conc.Vars s' = Conc.Vars s) →
    (Abs.Next (f s) (f s') ∨ Abs.decided (f s') = Abs.decided (f s)) := by
  intro s s' hinv h
  rcases h with hnext | hstut
  · tla_unfold
    rcases hnext with hP | hA
    · -- prepare: decided unchanged
      right
      simp [f] at hP ⊢
      exact hP.2.2.2
    · -- accept: decided becomes `some value`; under the invariant this is
      -- either a real decision (from `none`) or a stutter (already `some 1`)
      rcases hinv with ⟨hph, hdec, hval⟩
      have hval1 : s.value = 1 := hval hA.1
      rcases hdec with hnone | hsome
      · left
        simp [f]
        exact ⟨hnone, by simpa [hval1] using hA.2.2.2⟩
      · right
        simp [f]
        simp [hA.2.2.2, hval1, hsome]
  · right
    have hdec' : s'.decided = s.decided := by
      simpa [Conc.Vars] using congrArg (fun p : Nat × Nat × Option Nat => p.2.2) hstut
    simp [f, hdec']

/-- Safety refinement, invariant-threaded: the concrete spec refines the
abstract one. -/
theorem conc_refines_abs : Tla.RefinesVia f Conc.Spec Abs.Spec := by
  unfold Conc.Spec Abs.Spec
  exact Tla.refinement_mapping_inv Abs.Init Abs.Next Abs.decided Conc.Init Conc.Next Conc.Vars
    Conc.Inv f init_refines Conc.inv_init0 Conc.inv_step0 step_refines

/-- **Liveness refinement**: the concrete weak fairness implies the
abstract weak fairness on the mapped behavior. The concrete fairness forces
an accept, and after the decision the abstract angle action (guarded by
`decided = none`) is disabled forever, so the abstract fairness holds
vacuously. -/
theorem wf_conc_to_abs (e : Tla.Behavior Conc.St) (hSpec : Conc.SpecWF e) :
    Tla.WF_v Abs.Next Abs.decided (Cslib.ωSequence.map f e) := by
  have hInit0 : Conc.Init (e 0) := by
    simpa [Conc.Init, Tla.statePred] using hSpec.1.1
  have hN : Tla.stutAlways Conc.Next Conc.Vars e := by simpa [Conc.SpecWF] using hSpec.1.2
  have hWF : Tla.WF_v Conc.Next Conc.Vars e := by simpa [Conc.SpecWF] using hSpec.2
  have hInvAll : ∀ m, Conc.Inv (e m) := Conc.inv_all e hInit0 hN
  rcases Conc.decides_eventually e hInit0 hN hInvAll hWF with ⟨D, hD1, hD0, hvalConst⟩
  -- after the decision the mapped abstract angle is never enabled
  have hDisable : ∀ m, D + 1 ≤ m →
      ¬ Tla.Enabled (Tla.AngleAction Abs.Next Abs.decided) ((Cslib.ωSequence.map f e) m) := by
    intro m hm
    have hdec : ((Cslib.ωSequence.map f e) m).decided = some 1 := by
      -- decided stays `some 1` from `D + 1` on: every step preserves it
      induction m, hm using Nat.le_induction with
      | base =>
          simpa [f] using hD1
      | succ m hm ih =>
          have hstep : Conc.Next (e m) (e (m + 1)) ∨ Conc.Vars (e (m + 1)) = Conc.Vars (e m) := by
            simpa [Tla.stutAlways, Tla.always, Tla.actionPred, Tla.StutAction,
              Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hN m
          rcases hstep with hNc | hstut
          · tla_unfold
            rcases hNc with hP | hA
            · -- prepare keeps decided
              have hkeep : (e (m + 1)).decided = (e m).decided :=
                (Conc.prepare_phase hP).2.2
              simpa [f, hkeep] using ih
            · -- accept sets decided to `some value`; the value is still `1`
              have hval : (e m).value = 1 := hvalConst m (by omega)
              simp [f, hA.2.2.2, hval]
          · have hkeep : (e (m + 1)).decided = (e m).decided := by
              simpa [Conc.Vars] using congrArg (fun p : Nat × Nat × Option Nat => p.2.2) hstut
            simpa [f, hkeep] using ih
    intro hEn
    rcases hEn with ⟨s', hs'⟩
    tla_unfold
    simp [hdec] at hs'
  -- the abstract fairness: the enabledness premise is false at every suffix
  simp [Tla.WF_v, Tla.always, Tla.tlaImp]
  intro n hPremise
  by_cases hn : n ≤ D + 1
  · have hP : Tla.Enabled (Tla.AngleAction Abs.Next Abs.decided)
        ((Cslib.ωSequence.map f e) (n + (D + 1 - n))) := by
      have hP' := hPremise (D + 1 - n)
      simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hP'
    have hidx : n + (D + 1 - n) = D + 1 := by omega
    rw [hidx] at hP
    exact False.elim (hDisable (D + 1) (le_refl (D + 1)) hP)
  · have hP : Tla.Enabled (Tla.AngleAction Abs.Next Abs.decided)
        ((Cslib.ωSequence.map f e) n) := by
      have hP' := hPremise 0
      simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hP'
    exact False.elim (hDisable n (by omega) hP)

/-- The full canonical-form refinement, liveness included. -/
theorem conc_refines_abs_wf : Tla.RefinesVia f Conc.SpecWF Abs.SpecWF := by
  intro e hSpec
  have hInit0 : Conc.Init (e 0) := by
    simpa [Conc.Init, Tla.statePred] using hSpec.1.1
  have hInvAll : ∀ m, Conc.Inv (e m) := Conc.inv_all e hInit0 (by simpa [Conc.SpecWF] using hSpec.1.2)
  exact ⟨Tla.refinement_mapping_inv Abs.Init Abs.Next Abs.decided Conc.Init Conc.Next Conc.Vars
    Conc.Inv f init_refines Conc.inv_init0 Conc.inv_step0 step_refines e ⟨hSpec.1.1, hSpec.1.2⟩,
    wf_conc_to_abs e hSpec⟩

/-- The concrete spec satisfies the same liveness as the abstract one:
`decided = none` leads to `decided = some 1` — by transferring the abstract
leads-to through the refinement. -/
theorem conc_leadsTo :
    Tla.Entails Conc.SpecWF
      (Tla.leadsTo (Tla.statePred (fun s : Conc.St => s.decided = none))
        (Tla.statePred (fun s : Conc.St => s.decided = some 1))) := by
  simpa [f] using
    (Tla.leadsTo_refines f (fun s : Abs.St => s.decided = none)
      (fun s : Abs.St => s.decided = some 1)
      Conc.SpecWF Abs.SpecWF conc_refines_abs_wf Abs.spec_leadsTo)

/-! ## The deep LTS form

The examples are the interface: the invariant-threaded simulation, the
generic image-finiteness lemma and the invariant-threaded refinement
theorem (all in `TlaDsl/LTSRefine.lean`) absorb the machinery, so the deep
statements below are just the protocol facts from above, re-stated. -/

/-- The invariant-threaded step correspondence is a forward simulation on
reachable states. -/
theorem conc_refines_abs_lts :
    Cslib.LTS.IsSimulation (Tla.SpecLTS Conc.Next Conc.Vars)
      (Tla.SpecLTS Abs.Next Abs.decided) (fun s t => f s = t ∧ Conc.Inv s) := by
  exact Tla.sim_inv_of_step Abs.Next Abs.decided Conc.Next Conc.Vars f Conc.Inv
    (by
      intro s s' hinv hs
      simpa [Tla.StutAction] using step_refines s s' hinv (by simpa [Tla.StutAction] using hs))
    (by
      intro s s' hinv hs
      exact Conc.inv_step0 s s' (by simpa [Tla.StutAction] using hs) hinv)

/-- The concrete LTS is image-finite even though its state space is
infinite: the frame is injective and the action has at most two successors
(the prepare and accept targets). -/
lemma conc_imageFinite : (Tla.SpecLTS Conc.Next Conc.Vars).ImageFinite := by
  apply Tla.specLTS_imageFinite_of_step
  · -- the frame `(phase, value, decided)` determines the state
    intro s s' h
    cases s with
    | mk ph v d =>
        cases s' with
        | mk ph' v' d' =>
            have h1 : ph = ph' := by
              simpa [Conc.Vars] using congrArg (fun p : Nat × Nat × Option Nat => p.1) h
            have h2 : v = v' := by
              simpa [Conc.Vars] using congrArg (fun p : Nat × Nat × Option Nat => p.2.1) h
            have h3 : d = d' := by
              simpa [Conc.Vars] using congrArg (fun p : Nat × Nat × Option Nat => p.2.2) h
            subst ph'
            subst v'
            subst d'
            rfl
  · -- at most two action successors
    intro s
    let t1 : Conc.St := { phase := 1, value := 1, decided := s.decided }
    let t2 : Conc.St := { phase := 0, value := s.value, decided := some s.value }
    have hsub : {s' : Conc.St | Conc.Next s s'} ⊆ ({t1, t2} : Set Conc.St) := by
      intro s' hs'
      tla_unfold
      rcases hs' with hP | hA
      · left
        cases s' with
        | mk ph' v' d' =>
            cases s with
            | mk ph0 v0 d0 =>
                have hph : ph' = 1 := by simpa using hP.2.1
                have hv : v' = 1 := by simpa using hP.2.2.1
                have hd : d' = d0 := by simpa using hP.2.2.2
                simp [t1, hph, hv, hd]
      · right
        cases s' with
        | mk ph' v' d' =>
            cases s with
            | mk ph0 v0 d0 =>
                have hph : ph' = 0 := by simpa using hA.2.1
                have hv : v' = v0 := by simpa using hA.2.2.1
                have hd : d' = some v0 := by simpa using hA.2.2.2
                simp [t2, hph, hv, hd]
    exact Set.Finite.subset (by exact (Set.finite_singleton t2).insert t1) hsub

/-- The canonical-form safety refinement, re-proved through the LTS layer
with the invariant-threaded simulation. -/
theorem conc_refines_abs_lts_refines : Tla.RefinesVia f Conc.Spec Abs.Spec := by
  unfold Conc.Spec Abs.Spec
  exact Tla.refinement_mapping_inv_lts Abs.Init Abs.Next Abs.decided Conc.Init Conc.Next Conc.Vars
    Conc.Inv f init_refines Conc.inv_init0
    (by
      intro s s' hinv hs
      simpa [Tla.StutAction] using step_refines s s' hinv (by simpa [Tla.StutAction] using hs))
    (by
      intro s s' hinv hs
      exact Conc.inv_step0 s s' (by simpa [Tla.StutAction] using hs) hinv)

end TlaDsl.Examples.PrepareAcceptConsensus
