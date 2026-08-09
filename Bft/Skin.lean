import Bft.Skin.Basic
import Bft.Skin.Notation
import Bft.Skin.Coercion
import Bft.Skin.TlaVar
import Bft.Skin.Prime
import Bft.Skin.Pretty

/-! # Bft.Skin — the syntax skin, a replaceable layer

Everything in `Bft/Skin/` is presentation: it changes how specs *read*,
never what they *mean*. The layer provides:

* `tla_var St x y` — declare state functions and the default frame `vars`;
* `[p| ...]` / `[a| ...]` — pseudocode state predicates and actions with
  primed variables, lifted type-directed so anything Lean elaborates works
  inside (operators, binders, membership, named state-first predicates);
* `[t| ...]` — temporal formulas with invisible lifting of state predicates
  and actions, `□[A]_v`, `WF_(v)(A)`, `□◇⟨A⟩_v`;
* `[c| Byz, p | body]` — the honest-processor guard sugar;
* scoped TLA notation (`open scoped Bft`) and pretty-printing that renders
  goals back in bracket form.

Deleting `Bft/Skin/` and the corresponding import in `Bft.lean` leaves the
whole proof library (`Bft.Core` … `Bft.Templates`) untouched — every theorem
is stated in kernel vocabulary; the skin only sweetens the writing.
See `Bft/Examples/SkinCounter.lean` for the full arc.
-/
