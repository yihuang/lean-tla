import Bft.Core
import Bft.Rules
import Bft.RelRank
import Bft.Exec
import Bft.Tactic

/-!
# Bft.Examples.TicketLock — end-to-end pipeline smoke test

One spec, three layers of the pipeline:

1. **Model layer**: TLA-style spec (`Init ∧ □[Next]_vars ∧ WF_v(Enter)`);
2. **Proof layer**: safety (inductive invariant) + liveness (a `RelRankCert`
   certificate whose rank is the number of tickets ahead of us);
3. **Execution layer**: `GuardedAction` splits guard/update, the step function
   compiles to executable code, and `run_invariant` extends the safety theorem
   to every executable run without re-proving.

Deliberately minimal: the waiting phase of a single-process ticket lock
(isomorphic to lean-tla's example of the same name, for comparing proof
sizes across the two designs).
-/

namespace Bft.Examples.TicketLock

/-- State: program counter (1 = waiting, 2 = critical section), our ticket,
the ticket currently being served. -/
structure St where
  pc : ℕ
  t : ℕ
  served : ℕ
deriving Repr, DecidableEq

/-- Frame: all variables. -/
def vars (s : St) : St := s

/-! ## Model layer -/

/-- The server releases the next ticket (when it is not ours). -/
def Serve : Action St := fun s s' =>
  ¬ (s.pc = 1 ∧ s.served = s.t) ∧
  s' = { s with served := s.served + 1 }

/-- Enter the critical section when our ticket is served. -/
def Enter : Action St := fun s s' =>
  s.pc = 1 ∧ s.served = s.t ∧
  s' = { s with pc := 2 }

def Next : Action St := fun s s' => Serve s s' ∨ Enter s s'

def Init : StatePred St := fun s => s.pc = 1 ∧ s.served ≤ s.t

/-- Invariant: while waiting, our ticket is not behind the served counter. -/
def Inv : StatePred St := fun s => s.pc = 1 → s.served ≤ s.t

/-- Goal: reach the critical section. -/
def Goal : StatePred St := fun s => s.pc = 2

/-! ## Safety -/

theorem init_inv : ∀ s, s ∈ Init → s ∈ Inv := fun _s hs _ => hs.2

theorem step_inv : ∀ s s', StutAction Next vars s s' → s ∈ Inv → s' ∈ Inv := by
  intro s s' hstep hinv hpc'
  rcases hstep with hnext | hstut
  swap
  · -- Stutter step: the state is unchanged
    have : s' = s := hstut
    subst this
    exact hinv hpc'
  rcases hnext with ⟨hG, hs'⟩ | ⟨hpc, hserve, hs'⟩
  · -- Serve step: s'.pc = s.pc = 1, and s.served < s.t (the guard excludes equality)
    subst hs'
    have hpc : s.pc = 1 := hpc'
    have hlt : s.served < s.t := by
      rcases Nat.lt_or_ge s.served s.t with h | h
      · exact h
      · have heq : s.served = s.t := Nat.le_antisymm (hinv hpc) h
        exact absurd ⟨hpc, heq⟩ hG
    exact Nat.succ_le_of_lt hlt
  · -- Enter step: s'.pc = 2, contradicting the premise
    subst hs'; simp at hpc'

theorem safety :
    Entails (tlaAnd (statePred Init) (stutAlways Next vars))
      (always (statePred Inv)) :=
  init_invariant_stut Init Next vars Inv init_inv step_inv

/-! ## Liveness (RelRank certificate)

The rank: `δ s i ↔ i < s.t - s.served ∧ s.pc = 1` — the tickets ahead of us,
numbered by position. One `Serve` step removes ticket 0 from the set. The
envelope `R s i ↔ i < s.t` is finite at every time, discharging Rule 5's
finiteness premise. -/

/-- Ranking: the tickets still ahead of us. -/
def δ (s : St) (i : ℕ) : Prop := i < s.t - s.served ∧ s.pc = 1

/-- Envelope: the number of tickets ahead never exceeds `t`. -/
def R (s : St) (i : ℕ) : Prop := i < s.t

theorem R_finite : ∀ e : Behavior St, ∀ n : ℕ,
    Set.Finite {i | R (e n) i} := by
  intro e n
  exact Set.Finite.subset (Set.finite_lt_nat (e n).t) (fun i hi => hi)

/-- Waiting predicate (the φ of the C premises): waiting + valid ticket order. -/
def φ : StatePred St := fun s => s.pc = 1 ∧ s.served ≤ s.t

theorem c1 : ∀ e : Behavior St,
    (tlaAnd (statePred Init) (tlaAnd (stutAlways Next vars) (WF_v Enter vars))) e →
    ∀ k : ℕ, e k ∈ φ →
    e k ∈ Goal ∨ (e k ∈ φ ∧ ∀ i, δ (e k) i → R (e k) i) := by
  intro e _hE k hφ
  exact Or.inr ⟨hφ, fun i hi => Nat.lt_of_lt_of_le hi.1 (Nat.sub_le _ _)⟩

theorem c2 : ∀ e : Behavior St,
    (tlaAnd (statePred Init) (tlaAnd (stutAlways Next vars) (WF_v Enter vars))) e →
    ∀ k : ℕ, e k ∈ φ →
    e (k + 1) ∈ Goal ∨ (e (k + 1) ∈ φ ∧ Conserves δ (e k) (e (k + 1))) := by
  intro e hE k hφ
  have hN : StutAction Next vars (e k) (e (k + 1)) := by
    have := hE.2.1 k
    simpa [stutAlways, always] using this
  rcases hN with hnext | hstut
  · rcases hnext with ⟨hG, hs'⟩ | ⟨hpc, hserve, hs'⟩
    · -- Serve step: pc unchanged, served+1; the remaining δ elements stay in
      -- the old set (conserve); φ is preserved by the invariant
      right
      have hs1 : (e (k + 1)).pc = (e k).pc := by rw [hs']
      have hs2 : (e (k + 1)).t = (e k).t := by rw [hs']
      have hs3 : (e (k + 1)).served = (e k).served + 1 := by rw [hs']
      have hlt : (e k).served < (e k).t := by
        rcases Nat.lt_or_ge (e k).served (e k).t with h | h
        · exact h
        · exact absurd ⟨hφ.1, Nat.le_antisymm hφ.2 h⟩ hG
      refine ⟨?_, fun i hi => ?_⟩
      · change (e (k + 1)).pc = 1 ∧ (e (k + 1)).served ≤ (e (k + 1)).t
        rw [hs1, hs2, hs3]
        exact ⟨hφ.1, by omega⟩
      · rw [δ, hs1, hs2, hs3] at hi
        rw [δ]
        exact ⟨by omega, hφ.1⟩
    · -- Enter step: Goal reached
      left
      change (e (k + 1)).pc = 2
      rw [hs']
  · -- Stutter step: everything preserved
    right
    have : e (k + 1) = e k := hstut
    rw [this]
    exact ⟨hφ, fun _ hi => hi⟩

theorem c3 : ∀ e : Behavior St,
    (tlaAnd (statePred Init) (tlaAnd (stutAlways Next vars) (WF_v Enter vars))) e →
    ∀ k : ℕ, e k ∈ φ → Serve (e k) (e (k + 1)) →
    e (k + 1) ∈ Goal ∨ Reduces δ (e k) (e (k + 1)) := by
  intro e _hE k hφ hserve
  right
  -- Serve removes the *last* waiting ticket t-served-1 from δ: the guard
  -- gives served < t, and after the step the bound is t-(served+1).
  have hlt : (e k).served < (e k).t := by
    rcases Nat.lt_or_ge (e k).served (e k).t with h | h
    · exact h
    · exact absurd ⟨hφ.1, Nat.le_antisymm hφ.2 h⟩ hserve.1
  have hs2 : (e (k + 1)).t = (e k).t := by rw [hserve.2]
  have hs3 : (e (k + 1)).served = (e k).served + 1 := by rw [hserve.2]
  refine ⟨(e k).t - (e k).served - 1, ⟨by omega, hφ.1⟩, ?_⟩
  simp only [δ, hs2, hs3]
  omega

/-- The certificate: under the spec environment, `φ ↝ Goal`
(with justice action `Serve`). -/
noncomputable def waitCert : RelRankCert St φ Goal where
  α := ℕ
  r := Serve
  φ := φ
  δ := δ
  R := R
  H := tlaAnd (statePred Init) (tlaAnd (stutAlways Next vars) (WF_v Enter vars))
  finiteness := R_finite
  c1 := c1
  c2 := c2
  c3 := c3

/-- Note: the certificate's justice is `□◇⟨Serve⟩`, which must be discharged by
the spec's fairness assumptions. A complete spec would include `WF_v(Serve)`
(the server is fair too); this minimal spec only carries `WF_v(Enter)`, so the
theorem takes `globalJustice Serve` as an explicit premise. This is the
deliberately honest treatment: fairness assumptions are never hidden. -/
theorem liveness :
    Entails (tlaAnd waitCert.H (globalJustice Serve))
      (leadsTo (statePred φ) (statePred Goal)) :=
  waitCert.toLeadsTo

/-! ## Execution layer -/

inductive Lbl where
  | serve | enter
deriving DecidableEq, Repr

def guard : Lbl → St → Prop
  | .serve, s => ¬ (s.pc = 1 ∧ s.served = s.t)
  | .enter, s => s.pc = 1 ∧ s.served = s.t

instance : ∀ l s, Decidable (guard l s)
  | .serve, _s => inferInstanceAs (Decidable ¬ _)
  | .enter, _s => inferInstanceAs (Decidable (_ ∧ _))

def update : Lbl → St → St
  | .serve, s => { s with served := s.served + 1 }
  | .enter, s => { s with pc := 2 }

def rel : Lbl → Action St
  | .serve => Serve
  | .enter => Enter

/-- guard/update agree with the relational semantics: by definition unfolding. -/
theorem fires : ∀ l s, guard l s → rel l s (update l s) := by
  intro l s hg
  cases l
  · exact ⟨hg, rfl⟩
  · exact ⟨hg.1, hg.2, rfl⟩

theorem det : ∀ l s s', rel l s s' → s' = update l s := by
  intro _l _s s' hrel
  cases _l
  · exact hrel.2
  · exact hrel.2.2

/-- The executable spec. -/
def execSpec : ExecSpec St where
  lbl := Lbl
  actions := ⟨rel, guard, update, fires, det⟩
  decGuard := fun _l _s => inferInstance

/-- The executable step (compilable: decidable guard, computable update). -/
def step (s : St) (l : Lbl) : St := execSpec.step s l

/-- The executable `next` refines the model-layer `Next`. -/
theorem exec_next_refines : ∀ s s',
    StutAction execSpec.next (fun s => s) s s' → StutAction Next vars s s' := by
  intro s s' hstep
  rcases hstep with ⟨l, hrel⟩ | hstut
  · cases l
    · exact Or.inl (Or.inl hrel)
    · exact Or.inl (Or.inr hrel)
  · exact Or.inr hstut

/-- Every executable run satisfies `Inv`. The model-layer safety theorem is
extended to the execution layer via `run_invariant` — no re-proof. -/
theorem exec_safe (s₀ : St) (hs₀ : Init s₀) (trace : List Lbl) :
    Inv (execSpec.run s₀ trace) := by
  apply execSpec.run_invariant Init Inv init_inv _ s₀ hs₀ trace
  intro s s' hstep hinv
  exact step_inv s s' (exec_next_refines s s' hstep) hinv

-- Smoke run: s₀ = waiting with ticket 1, service at 0; serve once, then enter.
#eval step (step ⟨1, 1, 0⟩ .serve) .enter  -- expect { pc := 2, t := 1, served := 1 }

end Bft.Examples.TicketLock
