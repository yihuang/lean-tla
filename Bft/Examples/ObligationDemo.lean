import Bft.Obligation
import Bft.Tactic

/-!
# Bft.Examples.ObligationDemo — the M2 obligation layer in action

Three checks, all evaluated at build time:

1. `#tla_cex` finds a genuine counterexample pair for a *false* two-state
   obligation over a finite state space;
2. `#tla_cex` answers `none` for a *true* one;
3. `tla_ob` discharges a normalized C2-shaped obligation (intro + unfold +
   omega) without manual arithmetic.
-/

namespace Bft.Examples.ObligationDemo

/-- A tiny finite state: a program counter (3 values) and a flag. -/
abbrev St := Fin 3 × Fin 2

/-- The (false) claim "the flag never changes while pc stays fixed".
`#tla_cex` prints the witness pair. -/
abbrev G : St → St → Prop := fun s s' => s.1 = s'.1

abbrev Qfalse : St → St → Prop := fun s s' => s.2 = s'.2

-- expect: some ((pc, 0), (pc, 1)) — same pc, flipped flag
#tla_cex G to Qfalse

/-- The (true) claim "pc never changes under the same relation". -/
abbrev Qtrue : St → St → Prop := fun s s' => s.1 = s'.1

-- expect: none
#tla_cex G to Qtrue

/-! ## `tla_ob` on a certificate-shaped obligation -/

/-- A mini ranking over the finite state: δ holds of the flag value while
pc = 0. The step relation `Rel` forces pc 0 → 1 and conserves everything
else; the C2-shaped obligation closes by `tla_ob` alone. -/
abbrev Rel : St → St → Prop := fun s s' => s'.1 = 1 ∧ s'.2 = s.2

abbrev δ (s : St) (i : Fin 2) : Prop := s.1 = 0 ∧ i = s.2

example : ∀ s s' : St, Rel s s' → s.1 = 0 →
    (s'.1 = 1 ∧ Conserves δ s s') := by
  tla_ob

end Bft.Examples.ObligationDemo
