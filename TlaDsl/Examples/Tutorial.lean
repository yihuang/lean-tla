import TlaDsl.Tactic
import TlaDsl.TlaVar
import TlaDsl.Coercion
import TlaDsl.Meta

open scoped Tla

/-! # The spec-authoring walkthrough

One small protocol, all the way through the DSL's workflow. The concrete
spec is a synchronized two-counter (`x` and `y` always equal, incrementing
one step at a time); the abstract spec forgets `y`. We show, in order:

1. the state and `tla_var` variables;
2. the spec in `[p|]/[a|]/[t|]` brackets;
3. an invariant, proved with `tla_inv_step`;
4. liveness `x = 0 ↝ x = 1` with `tla_wf1`;
5. the safety refinement with `refine_via`;
6. the liveness transfer with `Tla.leadsTo_refines`.

Each step names the tool it uses and where the real-scale versions live.
The full workflow is discussed in `docs/spec-authoring.md`.
-/

namespace TlaDsl.Examples.Tutorial

/-! ## 1. The state and the variables

`tla_var` declares the state functions and registers `[simp]` lemmas, so
the bracket notation below reads like pseudocode and `simp`/`grind` see
through them. -/

namespace Conc

structure St where
  x : Nat
  y : Nat
deriving Repr

tla_var St x y

@[simp] def Init : Tla.StatePred St := [p| x = 0 ∧ y = 0]
@[simp] def Next : Tla.Action St := [a| x' = x + 1 ∧ y' = y + 1]
@[simp] def Vars : St → Nat × Nat := fun s => (s.x, s.y)

def Spec : Tla.Pred St := [t| Init ∧ □[Next]_Vars]
def SpecWF : Tla.Pred St := [t| (Init ∧ □[Next]_Vars) ∧ Tla.WF_v Next Vars]

end Conc

namespace Abs

structure St where
  x : Nat
deriving Repr

tla_var St x

@[simp] def Init : Tla.StatePred St := [p| x = 0]
@[simp] def Next : Tla.Action St := [a| x' = x + 1]

def Spec : Tla.Pred St := [t| Init ∧ □[Next]_x]
def SpecWF : Tla.Pred St := [t| (Init ∧ □[Next]_x) ∧ Tla.WF_v Next x]

end Abs

/-! ## 3. An invariant with `tla_inv_step`

Write the invariant as a structure (one field per conjunct). After the
step is expressed as `s' = ...`, `tla_inv_step` splits the structure, finds
the pre-state invariant hypothesis and discharges every field it can; what
remains is the genuinely new fact. -/

structure Inv (s : Conc.St) : Prop where
  sync : s.x = s.y

theorem inv_init : ∀ s, Conc.Init s → Inv s := by
  intro s hs
  tla_unfold
  exact ⟨hs.1.trans hs.2.symm⟩

theorem inv_step : ∀ s s', Inv s → (Conc.Next s s' ∨ Conc.Vars s' = Conc.Vars s) → Inv s' := by
  intro s s' hinv hstep
  rcases hstep with hnext | hstut
  · tla_unfold
    rcases hnext with ⟨hx, hy⟩
    have hs' : s' = { x := s.x + 1, y := s.y + 1 } := by
      cases s' with
      | mk x' y' =>
          cases s with
          | mk x0 y0 =>
              have hx' : x' = x0 + 1 := by simpa using hx
              have hy' : y' = y0 + 1 := by simpa using hy
              simp [hx', hy']
    subst s'
    tla_inv_step
    -- tla_inv_step discharges the field itself (`x + 1 = y + 1` from
    -- `x = y` by cancellation)
  · have hs' : s' = s := by
      cases s' with
      | mk x' y' =>
          cases s with
          | mk x0 y0 =>
              have hx' : x' = x0 := by
                simpa [Conc.Vars] using congrArg Prod.fst hstut
              have hy' : y' = y0 := by
                simpa [Conc.Vars] using congrArg Prod.snd hstut
              simp [hx', hy']
    subst s'
    exact hinv

/-! ## 4. Liveness with `tla_wf1`

`tla_wf1` applies Lamport's WF1 rule and grinds the three obligations
(the `[N]_v`-step case, the `⟨A⟩_v`-step case and enabledness) — here they
all close automatically. For progress that takes several steps, chain
WF1 applications with `Tla.leads_to_via_nat` (see
`TlaDsl/Examples/Countdown.lean` or `RefinementLiveness.lean`). -/

theorem abs_step (n : Nat) :
    Tla.Entails (Tla.tlaAnd (Tla.stutAlways Abs.Next Abs.x) (Tla.WF_v Abs.Next Abs.x))
      (Tla.leadsTo (Tla.statePred (fun s : Abs.St => s.x = n))
        (Tla.statePred (fun s : Abs.St => s.x = n + 1))) := by
  tla_wf1

theorem abs_leadsTo :
    Tla.Entails Abs.SpecWF
      (Tla.leadsTo (Tla.statePred (fun s : Abs.St => s.x = 0))
        (Tla.statePred (fun s : Abs.St => s.x = 1))) := by
  intro e hSpec
  have hbase : Tla.tlaAnd (Tla.stutAlways Abs.Next Abs.x) (Tla.WF_v Abs.Next Abs.x) e := by
    simpa [Abs.SpecWF] using ⟨hSpec.1.2, hSpec.2⟩
  exact abs_step 0 e hbase

/-! ## 5. The safety refinement with `refine_via`

The refinement mapping projects the hidden variable away. `refine_via`
applies the Abadi–Lamport mapping theorem, leaving the initial-state and
step-correspondence obligations. (When the correspondence only holds on
reachable states, use `refine_via_inv` — see
`TlaDsl/Examples/RefinementConsensus.lean`.) -/

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
    rcases hnext with ⟨hx, hy⟩
    left
    simp [f, hx]
  · right
    have hx' : s'.x = s.x := by simpa [Conc.Vars] using congrArg Prod.fst hstut
    simp [f, hx']

theorem conc_refines_abs : Tla.RefinesVia f Conc.Spec Abs.Spec := by
  unfold Conc.Spec Abs.Spec
  refine_via f
  · exact init_refines
  · exact step_refines

/-! ## 6. The liveness transfer with `Tla.leadsTo_refines`

The full refinement includes the fairness: the concrete weak fairness
implies the abstract one on the mapped behavior (here trivially — every
concrete step changes `x` — for protocols with internal phases the proof
is the substantive part, see `RefinementLiveness.lean`). Then
`leadsTo_refines` lifts the abstract leads-to to the concrete spec. -/

theorem wf_conc_to_abs (e : Tla.Behavior Conc.St) (hSpec : Conc.SpecWF e) :
    Tla.WF_v Abs.Next Abs.x (Cslib.ωSequence.map f e) := by
  have hWF : Tla.WF_v Conc.Next Conc.Vars e := by simpa [Conc.SpecWF] using hSpec.2
  -- the abstract and concrete angle actions are always enabled
  have hEnAbs : ∀ s : Abs.St, Tla.Enabled (Tla.AngleAction Abs.Next Abs.x) s := by
    intro s
    refine ⟨{ x := s.x + 1 }, ?_⟩
    tla_unfold
  have hEnConc : ∀ s : Conc.St, Tla.Enabled (Tla.AngleAction Conc.Next Conc.Vars) s := by
    intro s
    refine ⟨{ x := s.x + 1, y := s.y + 1 }, ?_⟩
    tla_unfold
  have hWF' : ∀ n, (Tla.always (Tla.statePred (Tla.Enabled (Tla.AngleAction Conc.Next Conc.Vars)))
        (e.drop n)) → Tla.eventually (Tla.actionPred (Tla.AngleAction Conc.Next Conc.Vars)) (e.drop n) := by
    simpa [Tla.WF_v, Tla.always, Tla.tlaImp] using hWF
  simp [Tla.WF_v, Tla.always, Tla.tlaImp]
  intro n hEn
  have hEnAlways : Tla.always (Tla.statePred (Tla.Enabled (Tla.AngleAction Conc.Next Conc.Vars)))
      (e.drop n) := by
    simpa [Tla.always, Tla.statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using fun k => hEnConc (e (n + k))
  rcases hWF' n hEnAlways with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  -- the concrete angle step at `n + j` changes `x`, so it is an abstract
  -- angle step on the mapped behavior
  have hangle : Tla.AngleAction Conc.Next Conc.Vars (e (n + j)) (e (n + j + 1)) := by
    simpa [Tla.actionPred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hj
  simp [Tla.actionPred, Tla.AngleAction, Cslib.ωSequence.drop, Nat.add_comm]
  constructor
  · tla_unfold
    simp [f]
    have hidx : n + (j + 1) = n + j + 1 := by omega
    rw [hidx]
    simp [Nat.add_comm, hangle.1.1]
  · intro hEq
    simp [f] at hEq
    have hx' : (e (n + (j + 1))).x = (e (n + j)).x + 1 := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hangle.1.1
    omega

theorem conc_refines_abs_wf : Tla.RefinesVia f Conc.SpecWF Abs.SpecWF := by
  intro e hSpec
  exact ⟨Tla.refinement_mapping Abs.Init Abs.Next Abs.x Conc.Init Conc.Next Conc.Vars f
    init_refines step_refines e ⟨hSpec.1.1, hSpec.1.2⟩, wf_conc_to_abs e hSpec⟩

theorem conc_leadsTo :
    Tla.Entails Conc.SpecWF
      (Tla.leadsTo (Tla.statePred (fun s : Conc.St => s.x = 0))
        (Tla.statePred (fun s : Conc.St => s.x = 1))) := by
  simpa [f] using
    (Tla.leadsTo_refines f (fun s : Abs.St => s.x = 0) (fun s : Abs.St => s.x = 1)
      Conc.SpecWF Abs.SpecWF conc_refines_abs_wf abs_leadsTo)

end TlaDsl.Examples.Tutorial
