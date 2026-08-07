import TlaDsl.Meta
import TlaDsl.Rules
import TlaDsl.Coercion
import TlaDsl.Tactic
import TlaDsl.TlaVar

open scoped Tla

/-! # Liveness refinement: a two-phase counter under weak fairness

The Abadi–Lamport liveness-refinement pattern, end to end. The **abstract**
spec is a counter that increments one step at a time; weak fairness on the
increment action proves `x = 0 ↝ x = 2` (one WF1 step per rank, chained by
`leads_to_via_nat`). The **concrete** spec implements each increment as a
two-phase handshake through an internal `flag` (raise the flag, then
increment), so the abstract step is not atomic. We show:

* `conc_refines_abs`: the concrete spec refines the abstract one by
  projecting away the flag (safety refinement via the mapping theorem);
* `wf_conc_to_abs`: the concrete weak fairness on the handshake implies the
  abstract weak fairness on the mapped behavior — the substantive part,
  since the handshake steps alternate between flag-raising (a `x`-stutter)
  and incrementing;
* `conc_leadsTo`: the abstract liveness transfers through the refinement
  (`leadsTo_refines`), so the concrete spec satisfies the same
  `x = 0 ↝ x = 2`.

The two namespaces keep the bracket notation readable: inside `Abs`,
`x` is the abstract variable; inside `Conc`, `x` and `flag` are the
concrete ones.
-/

namespace TlaDsl.Examples.HandshakeRefinement

namespace Abs

structure St where
  x : Nat
deriving Repr

tla_var St x

/-- The abstract spec: `x` increments by one. -/
@[simp] def Init : Tla.StatePred St := [p| x = 0]
@[simp] def Next : Tla.Action St := [a| x' = x + 1]

def Spec : Tla.Pred St := [t| Init ∧ □[Next]_x]
def SpecWF : Tla.Pred St := [t| (Init ∧ □[Next]_x) ∧ Tla.WF_v Next x]

/-- WF1 step: from `x = n`, the counter reaches `n + 1`. -/
theorem step (n : Nat) :
    Tla.Entails (Tla.tlaAnd (Tla.stutAlways Next x) (Tla.WF_v Next x))
      (Tla.leadsTo (Tla.statePred (fun s : St => s.x = n))
        (Tla.statePred (fun s : St => s.x = n + 1))) := by
  tla_wf1

/-- `x = 0` leads to `x = 2` under the abstract spec's weak fairness:
two WF1 steps chained, packaged as the rank-function theorem. -/
theorem leadsTo :
    Tla.Entails (Tla.tlaAnd (Tla.stutAlways Next x) (Tla.WF_v Next x))
      (Tla.leadsTo (Tla.statePred (fun s : St => s.x = 0))
        (Tla.statePred (fun s : St => s.x = 2))) := by
  apply Tla.leads_to_via_nat (p := fun s : St => s.x = 0)
    (q := fun s : St => s.x = 2) (f := fun s : St => 2 - s.x)
  intro k
  by_cases hk : k = 2
  · subst k
    intro e hSpec n hp
    have hp0 : (e n).x = 0 := by
      simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_comm] using hp.1
    have h01 : Tla.leadsTo (Tla.statePred (fun s : St => s.x = 0))
        (Tla.statePred (fun s : St => s.x = 1)) e := step 0 e hSpec
    have h12 : Tla.leadsTo (Tla.statePred (fun s : St => s.x = 1))
        (Tla.statePred (fun s : St => s.x = 2)) e := step 1 e hSpec
    have h02 : Tla.leadsTo (Tla.statePred (fun s : St => s.x = 0))
        (Tla.statePred (fun s : St => s.x = 2)) e :=
      Tla.leadsTo_trans_entails _ _ _ e ⟨h01, h12⟩
    rcases h02 n (by simpa [Tla.statePred] using hp0) with ⟨j, hj⟩
    refine ⟨j, ?_⟩
    exact Or.inl (by
      simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hj)
  · -- rank `k ≠ 2`: the premise `x = 0 ∧ 2 - x = k` is uninhabited
    intro e hSpec n hp
    have hx0 : (e n).x = 0 := by
      simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_comm] using hp.1
    have hrank : 2 - (e n).x = k := by
      simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_comm] using hp.2
    have : k = 2 := by omega
    exact False.elim (hk this)

end Abs

namespace Conc

structure St where
  x : Nat
  flag : Nat
deriving Repr

tla_var St x flag

/-- The concrete spec: raise the flag (invisible to `x`), then increment. -/
@[simp] def Init : Tla.StatePred St := [p| x = 0 ∧ flag = 0]
@[simp] def Next : Tla.Action St :=
  [a| (flag = 0 ∧ x' = x ∧ flag' = 1) ∨
      (flag ≠ 0 ∧ x' = x + 1 ∧ flag' = 0)]
@[simp] def Vars : St → Nat × Nat := fun s => (s.x, s.flag)

def Spec : Tla.Pred St := [t| Init ∧ □[Next]_Vars]
def SpecWF : Tla.Pred St := [t| (Init ∧ □[Next]_Vars) ∧ Tla.WF_v Next Vars]

/-- The increment phase is the only phase that changes `x`. -/
lemma inc_phase {s s' : St} (hflag : s.flag ≠ 0) (hNc : Next s s') :
    s'.x = s.x + 1 := by
  tla_unfold
  rcases hNc with hRaise | hInc
  · exfalso
    simp [hflag] at hRaise
  · simp [hInc]

/-- The raise phase flips the flag and leaves `x` alone. -/
lemma raise_phase {s s' : St} (hflag : s.flag = 0) (hNc : Next s s') :
    s'.flag = 1 ∧ s'.x = s.x := by
  tla_unfold
  rcases hNc with hRaise | hInc
  · simp [hflag] at hRaise
    exact ⟨hRaise.2, hRaise.1⟩
  · exfalso
    simp [hflag] at hInc

/-- The concrete angle action is enabled from every state. -/
lemma enabled_all (s : St) : Tla.Enabled (Tla.AngleAction Next Vars) s := by
  by_cases hf : s.flag = 0
  · refine ⟨{ x := s.x, flag := 1 }, ?_⟩
    tla_unfold
    simp [hf]
  · refine ⟨{ x := s.x + 1, flag := 0 }, ?_⟩
    tla_unfold
    simp [hf]

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

/-- After an angle step that raised the flag, the next angle step
(guaranteed by `hnext`) is an increment. -/
lemma increment_after_raise (e : Tla.Behavior St)
    (hN : Tla.stutAlways Next Vars e)
    {m : Nat} (hm : Tla.AngleAction Next Vars (e m) (e (m + 1)))
    (hflag : (e m).flag = 0)
    (hnext : ∃ j, Tla.AngleAction Next Vars (e (m + 1 + j)) (e (m + 2 + j))) :
    ∃ j, (e (m + 1 + j)).x = (e (m + j)).x + 1 := by
  classical
  -- the raise at `m` leaves the flag true
  have hflag' : (e (m + 1)).flag = 1 :=
    (raise_phase hflag hm.1).1
  -- the first angle step after `m + 1`
  let j0 := Nat.find hnext
  have hj0 : Tla.AngleAction Next Vars (e (m + 1 + j0)) (e (m + 2 + j0)) :=
    Nat.find_spec hnext
  have hmin : ∀ j < j0, ¬ Tla.AngleAction Next Vars (e (m + 1 + j)) (e (m + 2 + j)) :=
    by
      intro j hj
      exact Nat.find_min (p := fun n =>
        Tla.AngleAction Next Vars (e (m + 1 + n)) (e (m + 2 + n)))
        hnext (by simpa [j0] using hj)
  -- the frame is unchanged from `m + 1` to the pre-state of that step
  have hstab : Vars (e (m + 1 + j0)) = Vars (e (m + 1)) := by
    apply frame_stable_between e hN
    · omega
    · intro i hi hlt
      have hj : i - (m + 1) < j0 := by omega
      have hnot := hmin (i - (m + 1)) hj
      have h1 : m + 1 + (i - (m + 1)) = i := by omega
      have h2 : m + 2 + (i - (m + 1)) = i + 1 := by omega
      rw [h1, h2] at hnot
      exact hnot
  have hflag0 : (e (m + 1 + j0)).flag = 1 := by
    have hst : (e (m + 1 + j0)).flag = (e (m + 1)).flag := by
      simpa [Vars] using congrArg Prod.snd hstab
    exact hst ▸ hflag'
  -- so the angle step at `m + 1 + j0` is the increment phase
  have hinc : (e (m + 2 + j0)).x = (e (m + 1 + j0)).x + 1 :=
    inc_phase (by omega : (e (m + 1 + j0)).flag ≠ 0) hj0.1
  refine ⟨j0 + 1, ?_⟩
  have hi1 : m + 1 + (j0 + 1) = m + (2 + j0) := by omega
  have hi2 : m + (j0 + 1) = m + (1 + j0) := by omega
  rw [hi1, hi2]
  simpa [Nat.add_assoc, Nat.add_comm] using hinc

/-- Under the concrete spec's weak fairness, `x` increases infinitely
often. -/
lemma increments_infinitely (e : Tla.Behavior St)
    (hN : Tla.stutAlways Next Vars e)
    (hWF : Tla.WF_v Next Vars e) :
    ∀ m : Nat, ∃ j, (e (m + j + 1)).x = (e (m + j)).x + 1 := by
  intro m
  have hWF' : ∀ n, (Tla.always (Tla.statePred (Tla.Enabled (Tla.AngleAction Next Vars)))
        (e.drop n)) → Tla.eventually (Tla.actionPred (Tla.AngleAction Next Vars)) (e.drop n) := by
    simpa [Tla.WF_v, Tla.always, Tla.tlaImp] using hWF
  have hEnAlways : Tla.always (Tla.statePred (Tla.Enabled (Tla.AngleAction Next Vars))) (e.drop m) := by
    simpa [Tla.always, Tla.statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using fun k => enabled_all (e (m + k))
  rcases hWF' m hEnAlways with ⟨j1, hj1⟩
  have hangle : Tla.AngleAction Next Vars (e (m + j1)) (e (m + j1 + 1)) := by
    simpa [Tla.actionPred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hj1
  by_cases hf : (e (m + j1)).flag = 0
  · -- flag = 0: a raise; the next angle step increments
    have hnext : ∃ j, Tla.AngleAction Next Vars (e (m + j1 + 1 + j)) (e (m + j1 + 2 + j)) := by
      have hEn' : Tla.always (Tla.statePred (Tla.Enabled (Tla.AngleAction Next Vars)))
          (e.drop (m + j1 + 1)) := by
        simpa [Tla.always, Tla.statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using fun k => enabled_all (e (m + j1 + 1 + k))
      rcases hWF' (m + j1 + 1) hEn' with ⟨j2, hj2⟩
      exact ⟨j2, by
        simpa [Tla.actionPred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hj2⟩
    rcases increment_after_raise e hN (m := m + j1) hangle hf hnext with ⟨j, hinc⟩
    refine ⟨j1 + j, ?_⟩
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hinc
  · -- flag ≠ 0: already an increment
    exact ⟨j1, inc_phase hf hangle.1⟩

end Conc

/-! ## The refinement -/

/-- The refinement mapping: project away the internal flag. -/
def f : Conc.St → Abs.St := fun s => { x := s.x }

theorem init_refines : ∀ s, Conc.Init s → Abs.Init (f s) := by
  intro s hs
  tla_unfold
  simp [f] at hs ⊢
  exact hs.1

theorem step_refines : ∀ s s', (Conc.Next s s' ∨ Conc.Vars s' = Conc.Vars s) →
    (Abs.Next (f s) (f s') ∨ Abs.x (f s') = Abs.x (f s)) := by
  intro s s' h
  rcases h with hnext | hstut
  · tla_unfold
    rcases hnext with hRaise | hInc
    · right
      simp [f] at hRaise ⊢
      exact hRaise.2.1
    · left
      simp [f] at hInc ⊢
      exact hInc.2.1
  · right
    have hx' : s'.x = s.x := by simpa [Conc.Vars] using congrArg Prod.fst hstut
    simp [f, hx']

/-- Safety refinement: the concrete spec refines the abstract one. -/
theorem conc_refines_abs : Tla.RefinesVia f Conc.Spec Abs.Spec := by
  unfold Conc.Spec Abs.Spec
  refine_via f
  · exact init_refines
  · exact step_refines

/-- **Liveness refinement**: the concrete weak fairness implies the
abstract weak fairness on the mapped behavior. The concrete angle steps
alternate between flag-raising (an `x`-stutter) and incrementing, so the
concrete fairness — infinitely many handshake steps — yields infinitely
many `x`-changes. -/
theorem wf_conc_to_abs (e : Tla.Behavior Conc.St) (hSpec : Conc.SpecWF e) :
    Tla.WF_v Abs.Next Abs.x (Cslib.ωSequence.map f e) := by
  have hN : Tla.stutAlways Conc.Next Conc.Vars e := by
    simpa [Conc.SpecWF] using hSpec.1.2
  have hWF : Tla.WF_v Conc.Next Conc.Vars e := by
    simpa [Conc.SpecWF] using hSpec.2
  -- the abstract angle action is always enabled
  have hEnAbs : ∀ s : Abs.St, Tla.Enabled (Tla.AngleAction Abs.Next Abs.x) s := by
    intro s
    refine ⟨{ x := s.x + 1 }, ?_⟩
    tla_unfold
  -- the abstract WF conclusion: an abstract angle step after every suffix
  have hInc : ∀ m, ∃ j, (e (m + j + 1)).x = (e (m + j)).x + 1 :=
    Conc.increments_infinitely e hN hWF
  simp [Tla.WF_v, Tla.always, Tla.tlaImp]
  intro n hEn
  rcases hInc n with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  -- the increment at `n + j` is an abstract angle step on the mapped
  -- behavior
  simp [Tla.actionPred, Tla.AngleAction, Cslib.ωSequence.drop, Nat.add_comm]
  constructor
  · -- the abstract action fires
    tla_unfold
    simpa [f, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj
  · -- the frame (x) changes
    simp [f]
    intro hEq
    have h' : (e (n + (j + 1))).x = (e (n + j)).x + 1 := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj
    omega

/-- The full canonical-form refinement, liveness included. -/
theorem conc_refines_abs_wf : Tla.RefinesVia f Conc.SpecWF Abs.SpecWF := by
  intro e hSpec
  exact ⟨Tla.refinement_mapping Abs.Init Abs.Next Abs.x Conc.Init Conc.Next Conc.Vars f
    init_refines step_refines e ⟨hSpec.1.1, hSpec.1.2⟩, wf_conc_to_abs e hSpec⟩

/-- The abstract liveness theorem with the initial state included (the
form the refinement transfer consumes). -/
theorem abs_spec_leadsTo :
    Tla.Entails Abs.SpecWF
      (Tla.leadsTo (Tla.statePred (fun s : Abs.St => s.x = 0))
        (Tla.statePred (fun s : Abs.St => s.x = 2))) := by
  intro e hSpec
  have hbase : Tla.tlaAnd (Tla.stutAlways Abs.Next Abs.x) (Tla.WF_v Abs.Next Abs.x) e := by
    simpa [Abs.SpecWF] using ⟨hSpec.1.2, hSpec.2⟩
  exact Abs.leadsTo e hbase

/-- The concrete spec satisfies the same liveness as the abstract one:
`x = 0` leads to `x = 2` — by transferring the abstract leads-to through
the refinement. -/
theorem conc_leadsTo :
    Tla.Entails Conc.SpecWF
      (Tla.leadsTo (Tla.statePred (fun s : Conc.St => s.x = 0))
        (Tla.statePred (fun s : Conc.St => s.x = 2))) := by
  simpa [f] using
    (Tla.leadsTo_refines f (fun s : Abs.St => s.x = 0) (fun s : Abs.St => s.x = 2)
      Conc.SpecWF Abs.SpecWF conc_refines_abs_wf abs_spec_leadsTo)

end TlaDsl.Examples.HandshakeRefinement
