import TlaDsl.Meta
import TlaDsl.SimBridge

open Classical

namespace Tla

/-! # Lamport's representation theorem: the canonical form (tractable slice)

Lamport's representation theorem: every stuttering-invariant formula `F` is
stuttering-equivalent to a **canonical spec** `∃ x, Init ∧ □[N]_x ∧ L` with
a hidden variable `x`. This file proves the tractable slice the meta-theory
doc scopes: the canonical construction for the DSL's operator closure, with
the canonical spec built per operator.

The construction is behavioral: a canonical spec lives on `State σ H =
σ × H` (the visible state plus the hidden value), and `F` is *realized* by
it when every `F`-behavior is the projection of a canonical behavior and
vice versa (`Realizes`). Proved here:

* `realizes_statePred` — `⌜p⌝` is realized by the trivial spec (the hidden
  value is the unit, `Init` forces `p` at the first state);
* `realizes_box` — `□⌜p⌝` is realized with a hidden Boolean tracking
  "`p` holds everywhere so far": `Init (x = true ∧ p)`, `N: x' = x ∧ p`,
  no liveness;
* `realizes_diamond` — `◇⌜p⌝` is realized with a hidden Boolean tracking
  "`p` already seen": `Init x = p`, `N: x' = x ∨ p`, `L: ◇ (x = true)` —
  the liveness part is exactly what makes `◇` a liveness operator;
* `realizes_and` — the composition: if `F` and `G` are realized, so is
  `F ∧ G`, with the product hidden variable and the component-wise
  `Init`/`N`/`L` (the transition allows either component to step while the
  other stutters, so the two realizations align).

The remaining Boolean/temporal combinations (negation, disjunction,
implication, nested operators) need the full history construction — a
hidden variable per subformula with a consistency action — which is the
general quotient-based statement: `StutInvFull` formulas descend to
`StutQuotFull`, and every such formula has a canonical realization.
-/

namespace Canonical

/-- The hidden-variable state: the visible state plus the hidden value. -/
abbrev State (σ : Type u) (H : Type w) := σ × H

/-- Project the hidden-variable state onto the visible state. -/
def proj {σ : Type u} {H : Type w} : State σ H → σ := Prod.fst

/-- The canonical spec shape `Init ∧ □[N]_x ∧ L` over the hidden-variable
state (the stuttering frame is the whole pair). -/
def Spec {σ : Type u} {H : Type w} (Init : StatePred (State σ H))
    (N : Action (State σ H)) (L : Pred (State σ H)) : Pred (State σ H) :=
  tlaAnd (statePred Init) (tlaAnd (stutAlways N (fun s : State σ H => s)) L)

/-- `F` is realized by the canonical spec with hidden values in `H`: every
`F`-behavior is the projection of a canonical behavior, and every canonical
behavior projects to an `F`-behavior. -/
def Realizes {σ : Type u} {H : Type w} (F : Pred σ)
    (Init : StatePred (State σ H)) (N : Action (State σ H))
    (L : Pred (State σ H)) : Prop :=
  ∀ e : Behavior σ, F e ↔ ∃ e' : Behavior (State σ H), Spec Init N L e' ∧
    Cslib.ωSequence.map proj e' = e

/-- A projection equality of behaviors is pointwise: `ωSequence` is a
structure, not a function type, so `congrFun` does not apply. -/
lemma map_proj_apply {σ : Type u} {H : Type w} {e' : Behavior (State σ H)}
    {e : Behavior σ} (h : Cslib.ωSequence.map proj e' = e) (n : Nat) : (e' n).1 = e n := by
  have h' := congrArg (fun w : Cslib.ωSequence σ => w n) h
  simpa [proj, Cslib.ωSequence.map] using h'

/-! ## The base case: `⌜p⌝` -/

/-- The trivial canonical spec for a state predicate: the hidden value is
the unit and `Init` forces `p` at the first state. -/
def unitInit {σ : Type u} (p : StatePred σ) : StatePred (State σ PUnit) :=
  fun s => p s.1 ∧ s.2 = ()

/-- The vacuous transition of the unit-hidden spec. -/
def unitN {σ : Type u} : Action (State σ PUnit) := fun _ _ => True

theorem realizes_statePred (p : StatePred σ) :
    Realizes (statePred p) (unitInit p) (unitN (σ := σ))
      (tlaTrue : Pred (State σ PUnit)) := by
  intro e
  constructor
  · intro hpe
    refine ⟨Cslib.ωSequence.map (fun s : σ => (s, ())) e, ?_, ?_⟩
    · constructor
      · simp [unitInit, statePred, Cslib.ωSequence.map]
        exact hpe
      · constructor
        · intro n
          simp [actionPred, StutAction, unitN, Cslib.ωSequence.map]
        · simp [tlaTrue, purePred]
    · ext n
      simp [proj, Cslib.ωSequence.map]
  · rintro ⟨e', hS, hproj⟩
    have h0 := map_proj_apply hproj 0
    exact by simpa [statePred, h0] using hS.1.1

/-! ## `□⌜p⌝`: the hidden variable tracks "`p` everywhere so far" -/

/-- `Init` for `□⌜p⌝`: `p` holds at the first state and the hidden flag is
set. -/
def boxInit {σ : Type u} (p : StatePred σ) : StatePred (State σ Bool) :=
  fun s => p s.1 ∧ s.2 = true

/-- `N` for `□⌜p⌝`: the flag stays set exactly while `p` continues to
hold. -/
def boxN {σ : Type u} (p : StatePred σ) : Action (State σ Bool) :=
  fun s s' => s'.2 = s.2 ∧ p s'.1

theorem realizes_box (p : StatePred σ) :
    Realizes (always (statePred p)) (boxInit p) (boxN p)
      (tlaTrue : Pred (State σ Bool)) := by
  intro e
  constructor
  · intro hp
    refine ⟨Cslib.ωSequence.map (fun s : σ => (s, true)) e, ?_, ?_⟩
    · constructor
      · simp [boxInit, statePred, Cslib.ωSequence.map]
        exact hp 0
      · constructor
        · intro n
          simp [actionPred, StutAction, boxN, Cslib.ωSequence.map]
          left
          simpa [Tla.statePred, Tla.actionPred, Cslib.ωSequence.drop,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp (n + 1)
        · simp [tlaTrue, purePred]
    · ext n
      simp [proj, Cslib.ωSequence.map]
  · rintro ⟨e', hS, hproj⟩
    have hproj' : ∀ n, (e' n).1 = e n := map_proj_apply hproj
    have hmain : ∀ n, (e' n).2 = true ∧ p (e n) := by
      intro n
      induction n with
      | zero =>
          constructor
          · exact hS.1.2
          · simpa [hproj' 0] using hS.1.1
      | succ n ih =>
          rcases ih with ⟨hx, hp⟩
          have hstep := hS.2.1 n
          rcases hstep with hbox | hstut
          · constructor
            · have hbox1 : (e' (n + 1)).2 = (e' n).2 := by
                simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
                  Nat.add_left_comm] using hbox.1
              rw [hbox1, hx]
            · have hb : p ((e' (n + 1)).1) := by
                simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
                  Nat.add_left_comm] using hbox.2
              simpa [hproj' (n + 1)] using hb
          · constructor
            · have hstut1 : e' (n + 1) = e' n := by
                simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
                  Nat.add_left_comm] using hstut
              rw [hstut1, hx]
            · have hstut1 : e' (n + 1) = e' n := by
                simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
                  Nat.add_left_comm] using hstut
              have heq : e (n + 1) = e n := by
                calc
                  e (n + 1) = (e' (n + 1)).1 := (hproj' (n + 1)).symm
                  _ = (e' n).1 := by rw [hstut1]
                  _ = e n := hproj' n
              rw [heq]
              exact hp
    intro n
    simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using (hmain n).2

/-! ## `◇⌜p⌝`: the hidden variable tracks "`p` already seen" -/

/-- `Init` for `◇⌜p⌝`: the flag is exactly whether `p` holds at the first
state. -/
def diaInit {σ : Type u} (p : StatePred σ) : StatePred (State σ Bool) :=
  fun s => s.2 = decide (p s.1)

/-- `N` for `◇⌜p⌝`: once the flag is set it stays set, and it is set by
any `p`-state. -/
def diaN {σ : Type u} (p : StatePred σ) : Action (State σ Bool) :=
  fun s s' => s'.2 = s.2 ∨ p s'.1

theorem realizes_diamond (p : StatePred σ) :
    Realizes (eventually (statePred p)) (diaInit p) (diaN p)
      (eventually (statePred (fun s : State σ Bool => s.2 = true))) := by
  intro e
  constructor
  · intro hp
    rcases hp with ⟨n, hpn⟩
    -- the hidden flag at position `m`: "`p` has occurred at or before `m`"
    refine ⟨(fun m : Nat => (e m, decide (∃ k : Nat, k ≤ m ∧ p (e k)))), ?_, ?_⟩
    · constructor
      · -- Init: the flag at 0 is exactly `p (e 0)`
        simp [diaInit, statePred]
      · constructor
        · intro m
          have hdia' : diaN p (e m, decide (∃ k : Nat, k ≤ m ∧ p (e k)))
              (e (m + 1), decide (∃ k : Nat, k ≤ m + 1 ∧ p (e k))) := by
            by_cases hp' : p (e (m + 1))
            · exact Or.inr hp'
            · left
              have hiff : (∃ k : Nat, k ≤ m + 1 ∧ p (e k)) ↔ (∃ k : Nat, k ≤ m ∧ p (e k)) := by
                constructor
                · rintro ⟨k, hk, hpk⟩
                  have hk' : k ≤ m := by
                    by_contra hkm
                    have hkeq : k = m + 1 := by omega
                    subst k
                    exact hp' hpk
                  exact ⟨k, hk', hpk⟩
                · rintro ⟨k, hk, hpk⟩
                  exact ⟨k, by omega, hpk⟩
              simp [hiff]
          simp [actionPred, StutAction, Cslib.ωSequence.drop, Nat.add_comm]
          exact Or.inl hdia'
        · refine ⟨n, ?_⟩
          have hpn' : p (e n) := by
            simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using hpn
          have hw : ∃ k : Nat, k ≤ n ∧ p (e k) := ⟨n, le_rfl, hpn'⟩
          have hflag : ((fun m : Nat => (e m, decide (∃ k : Nat, k ≤ m ∧ p (e k)))) n).2 = true := by
            change decide (∃ k : Nat, k ≤ n ∧ p (e k)) = true
            exact decide_eq_true hw
          simp [statePred, Cslib.ωSequence.drop, Nat.add_comm, hflag]
    · ext m; simp [proj]
  · rintro ⟨e', hS, hproj⟩
    have hL : ∃ m : Nat, (e' m).2 = true := by
      simpa [eventually, statePred, Cslib.ωSequence.drop, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hS.2.2
    let m0 : Nat := Nat.find (p := fun m => (e' m).2 = true) hL
    have hspec : (e' m0).2 = true := Nat.find_spec (p := fun m => (e' m).2 = true) hL
    have hmin : ∀ j : Nat, j < m0 → ¬ (e' j).2 = true := by
      intro j hj hj'
      have hle : m0 ≤ j := by
        simpa [m0] using Nat.find_min' hL (m := j) hj'
      omega
    by_cases hz : m0 = 0
    · have hspec0 : (e' 0).2 = true := by
        simpa [m0, hz] using hspec
      have hd : decide (p (e 0)) = true := by
        have h1 : (e' 0).2 = decide (p (e 0)) := by
          simpa [diaInit, statePred, map_proj_apply hproj 0] using hS.1
        rw [← h1]
        exact hspec0
      exact ⟨0, of_decide_eq_true hd⟩
    · have hpos : 0 < m0 := Nat.pos_of_ne_zero hz
      have hn : ¬ (e' (m0 - 1)).2 = true := hmin (m0 - 1) (by omega)
      have hx0 : (e' (m0 - 1)).2 = false := by
        by_cases hb : (e' (m0 - 1)).2 = true
        · exact False.elim (hn hb)
        · cases hb2 : (e' (m0 - 1)).2
          · rfl
          · exact False.elim (hn (by simp [hb2]))
      have hstep := hS.2.1 (m0 - 1)
      have hmm : m0 - 1 + 1 = m0 := by omega
      have hmm' : 1 + (m0 - 1) = m0 := by omega
      have hstep' : Tla.StutAction (diaN p) (fun s : State σ Bool => s) (e' (m0 - 1)) (e' m0) := by
        simpa [Tla.actionPred, Cslib.ωSequence.drop, hmm'] using hstep
      have hm0 : (e' m0).1 = e m0 := map_proj_apply hproj m0
      rcases hstep' with hdia | hstut
      · refine ⟨m0, ?_⟩
        have hx' : (e' m0).2 = (e' (m0 - 1)).2 ∨ p (e m0) := by
          simpa [diaN, hm0] using hdia
        have hp0 : p (e m0) := hx'.resolve_left (by simp [hx0, hspec])
        simpa [Tla.statePred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hp0
      · -- the stutter case: `m0 - 1` also has the flag set — contradiction
        have hx1 : (e' (m0 - 1)).2 = (e' m0).2 := by simp [hstut]
        exact False.elim (hn (hx1.trans hspec))

/-! ## The composition: `F ∧ G` (product hidden variable) -/

/-- Forget the second hidden component. -/
def dropH2 {σ : Type u} {H1 H2 : Type w} : State σ (H1 × H2) → State σ H1 :=
  fun s => (s.1, s.2.1)

/-- Forget the first hidden component. -/
def dropH1 {σ : Type u} {H1 H2 : Type w} : State σ (H1 × H2) → State σ H2 :=
  fun s => (s.1, s.2.2)

/-- The product transition: either component takes its own step while the
other is unchanged, or both step together. This is what lets two
realizations run side by side even though their stutter steps need not
align. -/
def andN {σ : Type u} {H1 H2 : Type w}
    (N1 : Action (State σ H1)) (N2 : Action (State σ H2)) : Action (State σ (H1 × H2)) :=
  fun s s' =>
    (N1 (dropH2 s) (dropH2 s') ∧ dropH1 s' = dropH1 s) ∨
    (N2 (dropH1 s) (dropH1 s') ∧ dropH2 s' = dropH2 s) ∨
    (N1 (dropH2 s) (dropH2 s') ∧ N2 (dropH1 s) (dropH1 s'))

theorem realizes_and {σ : Type u} {H1 H2 : Type w}
    {F : Pred σ} {Init1 : StatePred (State σ H1)} {N1 : Action (State σ H1)}
    {L1 : Pred (State σ H1)} (hF : Realizes F Init1 N1 L1)
    {G : Pred σ} {Init2 : StatePred (State σ H2)} {N2 : Action (State σ H2)}
    {L2 : Pred (State σ H2)} (hG : Realizes G Init2 N2 L2) :
    Realizes (tlaAnd F G)
      (fun s => Init1 (dropH2 s) ∧ Init2 (dropH1 s))
      (andN N1 N2)
      (fun e => L1 (Cslib.ωSequence.map dropH2 e) ∧ L2 (Cslib.ωSequence.map dropH1 e)) := by
  intro e
  constructor
  · rintro ⟨hFe, hGe⟩
    rcases (hF e).1 hFe with ⟨eF, hSF, hprojF⟩
    rcases (hG e).1 hGe with ⟨eG, hSG, hprojG⟩
    let e' : Behavior (State σ (H1 × H2)) :=
      fun n => ((eF n).1, ((eF n).2, (eG n).2))
    refine ⟨e', ?_, ?_⟩
    · constructor
      · simp [statePred]
        constructor
        · simpa [statePred, e', dropH2] using hSF.1
        · have hfst0 : (eF 0).1 = (eG 0).1 :=
            (map_proj_apply hprojF 0).trans (map_proj_apply hprojG 0).symm
          simpa [statePred, e', dropH1, hfst0] using hSG.1
      · constructor
        · intro n
          have hstepF : Tla.StutAction N1 (fun s : State σ H1 => s) (eF n) (eF (n + 1)) := by
            simpa [Tla.actionPred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using hSF.2.1 n
          have hstepG : Tla.StutAction N2 (fun s : State σ H2 => s) (eG n) (eG (n + 1)) := by
            simpa [Tla.actionPred, Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using hSG.2.1 n
          have hfst_n : (eF n).1 = (eG n).1 :=
            (map_proj_apply hprojF n).trans (map_proj_apply hprojG n).symm
          have hfst_n1 : (eF (n + 1)).1 = (eG (n + 1)).1 :=
            (map_proj_apply hprojF (n + 1)).trans (map_proj_apply hprojG (n + 1)).symm
          rcases hstepF with hF1 | hFs
          · rcases hstepG with hG1 | hGs
            · -- both components take a real step
              left; right; right
              constructor
              · simpa [e', dropH2] using hF1
              · simpa [e', dropH1, hfst_n, hfst_n1] using hG1
            · -- F steps, G stutters: the visible part of `eF` is constant
              -- because `eG` stutters and both project onto the same `e`
              have hfst' : (eF (n + 1)).1 = (eF n).1 := by
                calc
                  (eF (n + 1)).1 = e (n + 1) := map_proj_apply hprojF (n + 1)
                  _ = e n := by
                    calc
                      e (n + 1) = (eG (n + 1)).1 := (map_proj_apply hprojG (n + 1)).symm
                      _ = (eG n).1 := congrArg Prod.fst hGs
                      _ = e n := map_proj_apply hprojG n
                  _ = (eF n).1 := (map_proj_apply hprojF n).symm
              left; left
              constructor
              · simpa [e', dropH2] using hF1
              · simp [e', dropH1, hfst', hGs]
          · rcases hstepG with hG1 | hGs
            · -- F stutters, G steps
              left; right; left
              constructor
              · simpa [e', dropH1, hfst_n, hfst_n1] using hG1
              · simp [e', dropH2, hFs]
            · -- both stutter
              right
              simp [e', hFs, hGs]
        · constructor
          · have hmap : Cslib.ωSequence.map dropH2 e' = eF := by
              ext n <;> simp [Cslib.ωSequence.map, e', dropH2]
            simpa [hmap] using hSF.2.2
          · have hmap : Cslib.ωSequence.map dropH1 e' = eG := by
              ext n
              · have hfst : (eF n).1 = (eG n).1 :=
                  (map_proj_apply hprojF n).trans (map_proj_apply hprojG n).symm
                simp [Cslib.ωSequence.map, e', dropH1, hfst]
              · simp [Cslib.ωSequence.map, e', dropH1]
            simpa [hmap] using hSG.2.2
    · ext n
      simpa [e', proj] using map_proj_apply hprojF n
  · rintro ⟨e', hS, hproj⟩
    let eF : Behavior (State σ H1) := Cslib.ωSequence.map dropH2 e'
    let eG : Behavior (State σ H2) := Cslib.ωSequence.map dropH1 e'
    have hprojF : Cslib.ωSequence.map proj eF = e := by
      ext n
      simpa [eF, dropH2, proj] using map_proj_apply hproj n
    have hprojG : Cslib.ωSequence.map proj eG = e := by
      ext n
      simpa [eG, dropH1, proj] using map_proj_apply hproj n
    have hSF : Spec Init1 N1 L1 eF := by
      constructor
      · simp [eF, statePred]
        exact hS.1.1
      · constructor
        · intro n
          have hstep := hS.2.1 n
          rcases hstep with hand | hstut
          · rcases hand with hd1 | hd2
            · left
              simpa [eF, dropH2] using hd1.1
            · rcases hd2 with hd2' | hd3
              · right
                exact hd2'.2
              · left
                simpa [eF, dropH2] using hd3.1
          · right
            exact congrArg dropH2 hstut
        · simp [eF]
          exact hS.2.2.1
    have hSG : Spec Init2 N2 L2 eG := by
      constructor
      · simp [eG, statePred]
        exact hS.1.2
      · constructor
        · intro n
          have hstep := hS.2.1 n
          rcases hstep with hand | hstut
          · rcases hand with hd1 | hd2
            · -- `N1` steps and the `H1` component stutters: `eG` stutters
              right
              exact hd1.2
            · rcases hd2 with hd2' | hd3
              · left
                simpa [eG, dropH1] using hd2'.1
              · left
                simpa [eG, dropH1] using hd3.2
          · right
            exact congrArg dropH1 hstut
        · simp [eG]
          exact hS.2.2.2
    exact ⟨(hF e).2 ⟨eF, hSF, hprojF⟩, (hG e).2 ⟨eG, hSG, hprojG⟩⟩

end Canonical

end Tla
