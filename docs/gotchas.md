# Lean gotchas in TLA-flavored proofs

These are the papercuts that cost real debugging time while writing the
Paxos and Streamlet proofs. None is a DSL bug; all are Lean behavior that
surprised us repeatedly. Each entry has the symptom, the cause, and the
fix, plus the mini-utility that automates the fix where one exists.

## 1. `rcases h with ⟨rfl, rfl⟩` eliminates the *wrong* variable

**Symptom.** After `by_cases hje : j = i ∧ e' = b.epoch`, writing

```lean
· rcases hje with ⟨rfl, rfl⟩
  have hb' : b' = b := ...
  exact hLongest C ((notarizedBy_votes_eq hpres).2 hC)   -- references `i`
```

fails with `unknown identifier 'i'` — the `rfl` pattern substitutes the
variable on the **right** of each equality, so `j = i` eliminates `i` (and
`e' = b.epoch` eliminates `b.epoch`).

**Cause.** `rfl` as an `rcases` pattern is an *equation eliminator*, not a
name picker: it substitutes one side of the equality, and Lean picks the
right-hand side. If either variable is still referenced later (in the
state `vote s i b`, say), the reference dies with it.

**Fix.** Name the equality hypotheses and substitute the left-hand
variables explicitly:

```lean
· rcases hje with ⟨hji, he'⟩
  subst j
  subst e'
```

**Utility.** `tla_rcases_subst h` does exactly that — it reads the
conjunction's left-hand-side variables from the hypothesis type and
substitutes them by name, keeping the right-hand-side variables alive:

```lean
· tla_rcases_subst hje
```

It accepts one or two equalities (`h : a = b` or `h : a = b ∧ c = d`).

**Corollary.** `subst h1` on `h1 : j = i` is *not* the safe direction
either — Lean's `subst` on a hypothesis substitutes the right-hand side,
the same trap as `rfl`. Always substitute by the **left-hand variable
name** (`subst j`), or use `tla_rcases_subst`.

## 2. `by omega` fails with "No usable constraints" in argument position

**Symptom.**

```lean
have hb0ne : b0 ≠ Block.genesis := proposal_ne_genesis_of hInv hp0 (by omega)
```

fails with `No usable constraints` even though the arithmetic is trivial.

**Cause.** The expected type of the `by omega` hole still contains an
unassigned metavariable when `omega` runs (here, the epoch argument of
`proposal_ne_genesis_of`), so `omega` has no usable constraints to reason
about.

**Fix.** Name the argument so the metavariable is resolved before the
arithmetic runs:

```lean
have hb0ne : b0 ≠ Block.genesis := proposal_ne_genesis_of hInv hp0
  (by omega : b0.epoch ≠ 0)   -- or: (show b0.epoch ≠ 0 by omega)
```

More generally: if `by omega` (or `by grind`) reports "No usable
constraints" in argument position, annotate the expected type or bind the
argument in a named `have` first.

## 3. `ωSequence` suffix conversions are not definitional

**Symptom.** `(e.drop n) j` and `e (n + j)` are the same state but not
definitionally equal, so `exact` fails and `simpa` needs the drop lemmas
and Nat reassociations spelled out:

```lean
have hp0 : ... := by
  simpa [Cslib.ωSequence.drop, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using hnone
```

**Cause.** `ωSequence.drop` is a definition over `Nat` addition, and the
index arithmetic `(n + j) + k = n + (j + k)` is a theorem, not definitional
equality. Every suffix-level premise or conclusion of a `leadsTo` needs
this conversion.

**Fix.** Use the bundled conversion tactic:

```lean
have hp0 : ... := by tla_drop_simpa using hnone
```

`tla_drop_simpa` (with or without `using`) bundles
`[Tla.statePred, Tla.actionPred, Tla.always, Cslib.ωSequence.drop,
Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]` — the exact set the
proofs kept repeating. When the goal is already a state-level fact, the
state-level rules (`Tla.leadsTo_at`, `Tla.inv_all_of_spec`) avoid most of
these conversions in the first place.

## 4. Namespace/type collisions (`Block` the namespace vs `Block` the type)

**Symptom.** Inside `namespace ... Streamlet.Block`, the *type* `Block`
and the *namespace* `Block` coexist; unqualified references can resolve to
the wrong one, and `Block.genesis` / `b.pred` / `Block.epoch_pos_ne_genesis`
can be confused.

**Cause.** Lean allows a namespace and a type to share a name; resolution
prefers the most recently opened scope, so the meaning of `Block` depends
on where you are.

**Fix.** Keep the type and its namespace apart by convention: name the
type `Block` and its lemmas in a *different* namespace (or accept the
collision and always qualify the ambiguous constants). When a constant
looks like it should exist but resolves weirdly, check which `Block` is in
scope.

## 5. Tactic-writing note: `withMainContext`

When writing your own `elab`-level tactics, remember that the term
context's local context is only synced to the goal inside
`withMainContext`. A tactic that reads hypotheses with `getLCtx` /
`getLocalDeclFromUserName` at the top level sees the *original* theorem
context — the variables introduced by `intro`/`rcases`/`by_cases` are
invisible. Wrap the body in `withMainContext do ...`.
