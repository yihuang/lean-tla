# Spec authoring in TlaDsl

A walkthrough of the full workflow, from a bare state type to a proved
liveness theorem *and* a refinement that transfers it. The runnable version
of everything below is
[`TlaDsl/Examples/Tutorial.lean`](../TlaDsl/Examples/Tutorial.lean) — read
the two side by side. The examples are the user-facing interface: each tool
below has a small worked example and a real-scale one, and the library is
shaped so the examples stay short.

## The arc

```
state + tla_var  →  spec in brackets  →  invariant  →  liveness  →  refinement
     (the model)      (Init/Next/□[N]_v)   (tla_inv_step)  (tla_wf1/rank)  (refine_via,
                                                                             leadsTo_refines)
```

## 1. The state and the variables

```lean
structure StConc where
  x : Nat
  y : Nat
deriving Repr

tla_var StConc x y
```

`tla_var` declares the state functions (`x : StConc → Nat`, ...), the
default stuttering frame `vars`, and `[simp]` `_apply` lemmas, so the
brackets below read like pseudocode and `simp`/`grind`/`omega` see through
them. Proofs should use plain `simp`/`tla_unfold` — do not list a
generated variable explicitly (`simp [x]` is unsupported).

## 2. The spec in brackets

```lean
@[simp] def Init : Tla.StatePred StConc := [p| x = 0 ∧ y = 0]
@[simp] def Next : Tla.Action StConc := [a| x' = x + 1 ∧ y' = y + 1]
@[simp] def Vars : StConc → Nat × Nat := fun s => (s.x, s.y)

def Spec : Tla.Pred StConc := [t| Init ∧ □[Next]_Vars]
def SpecWF : Tla.Pred StConc := [t| (Init ∧ □[Next]_Vars) ∧ Tla.WF_v Next Vars]
```

* `[p| ...]`/`[a| ...]` are dedicated elaborators: they introduce the
  state (and pre/post states for actions) and lift every identifier of
  state-function type, so `x'` is the post-state value of `x`. Anything
  Lean elaborates works inside — operators, `∀/∃` binders, `∈`, named

`[t| ...]` is the temporal formula: state predicates and actions lift
invisibly (`Init` becomes `⌜Init⌝`, a bare `Next` becomes `□ actionPred
Next`), so a fairness spec reads like TLA:

```lean
def Spec : Tla.Pred St := [t| Init ∧ □ Next ∧ □◇ Poll1A ∧ □◇ Poll2]
def SpecParam : Tla.Pred St := [t| Init ∧ □ Next ∧ ∀ p : Nat, □◇ Poll p]
```

* `□` is `always`, `◇` is `eventually`, `□[A]_v` is the stuttering-closed
  `stutAlways A v` (the canonical TLA step form), and typed `∀`/`∃`
  binders become the temporal `tlaForall`/`tlaExists` — so parameterized
  fairness (`∀ p, □◇ Poll p`) needs no lambda boilerplate. The invisible
  lifting is the two `Coe` instances in `TlaDsl/Coercion.lean` (state
  predicates via `statePred`, actions via `actionPred`).
  state-first predicates (`NotarizedBy n b e` inside `[p| ...]`).
* `[t| ...]` rewrites the propositional connectives to the temporal ones;
  `□[Next]_Vars` is stuttering closure, `WF_v` weak fairness.
* The two-frame convention: write derived predicates *state-first*
  (`def ChainNotarized (s : St) ...`) so they compose with the brackets,
  and put shared proof-relevant predicates in plain definitions (brackets
  are for the spec/action layer).

## 3. An invariant with `tla_inv_step`

Write the invariant as a structure (one field per conjunct) and prove its
step case after expressing the step as `s' = ...`:

```lean
structure Inv (s : StConc) : Prop where
  sync : s.x = s.y

theorem inv_step : ∀ s s', Inv s → (Next s s' ∨ Vars s' = Vars s) → Inv s' := by
  intro s s' hinv hstep
  rcases hstep with hnext | hstut
  · tla_unfold
    rcases hnext with ⟨hx, hy⟩
    have hs' : s' = { x := s.x + 1, y := s.y + 1 } := by
      cases s' <;> cases s <;> simp [hx, hy]
    subst s'
    tla_inv_step          -- splits the structure, finds hInv, closes the field
                          -- (`x + 1 = y + 1` from `x = y` by cancellation)
  · ...
```

`tla_inv_step` splits the invariant, finds the pre-state hypothesis and
per field tries (1) a definitional-equality check, (2)
`simpa [transformer] using <pre-state field>`, (3) a convention-named
preservation lemma `⟨field⟩_⟨action⟩`. What remains is what the action
really changes (if anything). Real scale: Streamlet's 12-field invariant in
`TlaDsl/Examples/StreamletLiveness.lean` goes from 12 bullets per action to
one call plus the genuinely-changed fields.

## 4. Liveness with `tla_wf1` (and friends)

```lean
theorem abs_step (n : Nat) :
    Tla.Entails (tlaAnd (stutAlways NextAbs x) (WF_v NextAbs x))
      (leadsTo (statePred (fun s => s.x = n)) (statePred (fun s => s.x = n + 1))) := by
  tla_wf1
```

`tla_wf1` applies Lamport's WF1 rule and grinds the three obligations.
The liveness engines, in increasing power:

| Engine | Tool | When |
|---|---|---|
| WF1 / SF1 | `tla_wf1`, `tla_sf1`, `tla_sf1_standard` | one action, one fairness assumption |
| rank function | `tla_leads_to_via_nat f` | progress = a well-founded measure strictly decreasing (ticket locks, countdowns) |
| relational rank | `tla_rel_rank φ δ R` | McMillan's finite-envelope rankings, no well-founded domain (queues, cascades — the north-star) |

The goal display shows state predicates and actions as `[p| ...]` /
`[a| ...]` (see `TlaDsl/Pretty.lean`), so mid-proof goals read like the
spec.

## 5. Refinement with `refine_via`

```lean
def f : StConc → StAbs := fun s => { x := s.x }

theorem conc_refines_abs : Tla.RefinesVia f Conc.Spec Abs.Spec := by
  unfold Conc.Spec Abs.Spec
  refine_via f            -- initial-state and step-correspondence goals
  · exact init_refines
  · exact step_refines
```

`refine_via` applies the Abadi–Lamport mapping theorem; `refine_via_inv`
threads a concrete invariant for protocols whose step correspondence only
holds on reachable states (Paxos-style prepare/accept:
`TlaDsl/Examples/RefinementConsensus.lean`).

## 6. Liveness transfer with `Tla.leadsTo_refines`

The refinement's liveness half: prove the concrete fairness implies the
abstract one on the mapped behavior (`wf_conc_to_abs`), assemble the full
canonical-form refinement, and transfer:

```lean
theorem conc_leadsTo : Entails Conc.SpecWF (leadsTo (x = 0) (x = 1)) := by
  simpa [f] using
    (Tla.leadsTo_refines f ... Conc.SpecWF Abs.SpecWF conc_refines_abs_wf abs_leadsTo)
```

The fairness transfer is where the protocol's real content lives: for a
two-phase concrete spec it is the alternation argument
(`RefinementLiveness.lean`), for a decide-once protocol the vacuity after
the decision (`RefinementConsensus.lean`). The deep LTS/FLTS forms
(simulations, image-finiteness, executable step functions) are in
`TlaDsl/LTSRefine.lean` and demonstrated in
`TlaDsl/Examples/RefinementLivenessLTS.lean` — the same facts, re-stated
in the executable vocabulary, each a few lines because the machinery is in
the library.

## Conventions and gotchas

* Write state-first predicates; keep the invariant a structure; name
  preservation lemmas `⟨field⟩_⟨action⟩` and `tla_inv_step` will find
  them.
* `Bool` literals do not work inside brackets (`true`/`false` are the
  proposition constants) — use `Nat` flags or `= false`.
* The papercuts (the `rcases ... ⟨rfl, rfl⟩` subst trap, `by omega` in
  argument position, non-definitional `ωSequence` suffix conversions, the
  `Block` namespace/type collision) are documented with fixes and
  mini-utilities (`tla_rcases_subst`, `tla_drop_simpa`) in
  [`gotchas.md`](gotchas.md).

## Where to look next

* The full proof UX log and measurement: [`ux-notes.md`](ux-notes.md).
* The north-star (relational rankings at scale) and its milestones:
  [`north-star.md`](north-star.md).
* The design-space and meta-theory notes:
  [`design-space.md`](design-space.md), [`tla-meta-theory.md`](tla-meta-theory.md).
