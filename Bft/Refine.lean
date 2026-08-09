/-
Copyright (c) 2026 lean-tla contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Refinement: global-function spec → local state + messages (M4)

The first layer of the message-layer gap: trace-level refinement from a
low-level system (local node state + an unordered message soup) to a
high-level "global function" spec, via an abstraction function.

* `StepSim` — every low-level stuttering step maps to a high-level
  stuttering step of the abstract state;
* `InitSim` — low-level initial states map to high-level initial states;
* `specSim_entails` — any property `P` of the high-level spec (safety *or*
  liveness, since `P` is arbitrary) holds of the abstracted low-level
  behavior;
* `refine_invariant` — the common special case, transporting an invariant;
* `globalJustice_map` — lifting justice through the abstraction: the
  caller exhibits occurrences of the high-level action on abstract states.
  Low-level fairness is *not* derived here; as in the rest of the library,
  fairness assumptions stay explicit at the use site.

The low-level side typically uses `NetState`: per-node local state plus the
in-flight packets (a list — no FIFO assumption; reordering and duplication
are representable).
-/
import Bft.Core
import Bft.Rules

namespace Bft

variable {σ : Type u} {τ : Type v} {α : Type w₁} {β : Type w₂}

/-- Behavior mapping through an abstraction: `Cslib.ωSequence.map`. -/
abbrev Behavior.map (abs : τ → σ) (e : Behavior τ) : Behavior σ :=
  Cslib.ωSequence.map abs e

/-- Step-level simulation: every low-level stuttering step (frame `lv`)
maps to a high-level stuttering step (frame `gv`) of the abstract state. -/
def StepSim (abs : τ → σ) (lv : τ → α) (LNext : Action τ)
    (gv : σ → β) (GNext : Action σ) : Prop :=
  ∀ t t', StutAction LNext lv t t' → StutAction GNext gv (abs t) (abs t')

/-- Init-level simulation: low-level initial states abstract to high-level
initial states. -/
def InitSim (abs : τ → σ) (LInit : StatePred τ) (GInit : StatePred σ) : Prop :=
  ∀ t, LInit t → GInit (abs t)

/-- The stuttering-step machine simulates through the abstraction, at every
suffix of the behavior. -/
theorem StepSim.stutAlways {abs : τ → σ} {lv : τ → α} {LNext : Action τ}
    {gv : σ → β} {GNext : Action σ}
    (hsim : StepSim abs lv LNext gv GNext) (e : Behavior τ) :
    stutAlways LNext lv e → stutAlways GNext gv (Behavior.map abs e) := by
  intro hE n
  have h := hE n
  rw [actionPred_drop] at h ⊢
  rw [Cslib.ωSequence.get_map, Cslib.ωSequence.get_map]
  exact hsim _ _ h

/-- Master refinement theorem: anything that follows from the high-level
spec follows, through the abstraction, from the low-level spec. -/
theorem specSim_entails {abs : τ → σ} {lv : τ → α} {LNext : Action τ}
    {gv : σ → β} {GNext : Action σ}
    {LInit : StatePred τ} {GInit : StatePred σ}
    (hinit : InitSim abs LInit GInit) (hstep : StepSim abs lv LNext gv GNext)
    (P : Pred σ)
    (hG : Entails (tlaAnd (statePred GInit) (stutAlways GNext gv)) P) :
    Entails (tlaAnd (statePred LInit) (stutAlways LNext lv))
      (fun e => P (Behavior.map abs e)) := by
  intro e hE
  apply hG
  constructor
  · exact hinit _ hE.1
  · exact hstep.stutAlways _ hE.2

/-- Invariant transport: a high-level safety theorem gives the corresponding
low-level invariant for free. -/
theorem refine_invariant {abs : τ → σ} {lv : τ → α} {LNext : Action τ}
    {gv : σ → β} {GNext : Action σ}
    {LInit : StatePred τ} {GInit : StatePred σ}
    (hinit : InitSim abs LInit GInit) (hstep : StepSim abs lv LNext gv GNext)
    (GInv : StatePred σ)
    (hG : Entails (tlaAnd (statePred GInit) (stutAlways GNext gv))
      (always (statePred GInv))) :
    Entails (tlaAnd (statePred LInit) (stutAlways LNext lv))
      (always (statePred fun t => GInv (abs t))) := by
  intro e hE n
  have h := specSim_entails hinit hstep _ hG e hE n
  rw [statePred_drop, Cslib.ωSequence.get_map] at h
  rw [statePred_drop]
  exact h

/-- Justice lifts through an abstraction: to get `□◇⟨r⟩` on the abstracted
behavior, exhibit an occurrence of `r` on the abstract states after every
time `k`. (Where the occurrences come from — typically a low-level fairness
assumption plus a progress proof — stays at the use site.) -/
theorem globalJustice_map {abs : τ → σ} {r : Action σ} (e : Behavior τ)
    (h : ∀ k, ∃ m, r (abs (e (k + m))) (abs (e (k + m + 1)))) :
    globalJustice r (Behavior.map abs e) := by
  intro n
  obtain ⟨m, hm⟩ := h n
  refine ⟨m, ?_⟩
  rw [Cslib.ωSequence.drop_drop, actionPred_drop,
    Cslib.ωSequence.get_map, Cslib.ωSequence.get_map]
  exact hm

/-! ## Message soup -/

/-- A packet in flight. -/
structure Packet (ι : Type u) (γ : Type v) where
  src : ι
  dst : ι
  body : γ
deriving Repr, DecidableEq

/-- Network state: per-node local state plus the in-flight packets.
The message soup is a plain list — no FIFO assumption; reordering and
duplication are representable, matching the usual asynchronous network
model (Verdi-style). -/
structure NetState (ι : Type u) (Node : ι → Type w) (γ : Type v) where
  nodes : ∀ i, Node i
  msgs : List (Packet ι γ)

end Bft
