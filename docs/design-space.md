# Deep-embedding TLA+ in Lean 4: a design-space exploration

*Working title: Lean/TLA+.* Status: design notes, not an implementation.

> **Read this first:** [`deep-vs-dsl.md`](deep-vs-dsl.md) asks the strategic
> question this document skips — whether a deep embedding is worth it at all
> versus a native Lean DSL. The layers below are still the right blueprint,
> but read them as the *internal semantics/oracle* architecture of a
> TLA-flavored DSL unless the project's goals (importing `.tla` specs,
> meta-theory of TLA+) actually demand a full deep embedding.

This document maps the design space for a **deep embedding of TLA+** in Lean 4,
using the Isabelle/TLA+ line of work as the primary reference and identifying
where mathlib and CSLib change the cost/benefit calculus. It ends with a
concrete recommended architecture and a phased plan. Nothing here is final;
the point is to make the options, tradeoffs, and prior art explicit so we can
pick a coherent design and start building.

---

## 1. The problem, in one paragraph

TLA+ is *untyped* and *set-theoretic*: every expression denotes a set, `3 ∪
TRUE` is a legal expression, and `CHOOSE` is a deterministic Hilbert epsilon
with an extensionality axiom. Its dynamic part is TLA, a linear-time temporal
logic whose distinguishing feature is *stuttering invariance*: formulas must
not distinguish behaviors that differ only by repeated states. Lean 4 is a
dependently typed calculus with a strongly typed standard library (mathlib).
So the central design problem is not "how do we write `□` and `◇`" — that is
easy in any embedding — but:

1. how to represent TLA+'s untyped set-theoretic values faithfully in a typed
   logic (or how to justify not doing so);
2. where stuttering lives: in the semantics of a relation on behaviors, in
   syntax (`[A]_v`), or in a quotient of behaviors;
3. how deep the syntax should go, i.e., what meta-theorems we want to be able
   to state and prove (stuttering invariance of *all* formulas, canonical
   forms, soundness of a proof calculus);
4. what proof architecture makes TLA+ proofs tractable, given that Lean is a
   general-purpose proof assistant rather than a proof-obligation manager;
5. how much of the TLA+ standard library (Naturals, Sequences, FiniteSets,
   Bags, Functions, Relations, records/tuples) to rebuild versus reuse from
   mathlib, and where CSLib's concurrency infrastructure slots in.

## 2. Why Isabelle/TLA+ is the reference, and what each of its three flavors taught us

There are three distinct Isabelle-based artifacts, and all three are relevant:

### 2.1 Isabelle/HOL/TLA (in the Isabelle distribution; Merz, late 1990s)

The oldest artifact: an embedding of **TLA the logic** (not TLA+ the
language) in HOL. Per Merz's own notes, it is "based on a complete
axiomatization of the 'raw' (stuttering-sensitive) variant of TLA." Its
structure:

- `Intensional.thy`: a `world` typeclass and machinery for "lifting" HOL
  connectives into a possible-world/modal language;
- `Stfun.thy`, `Action.thy`, `Init.thy`: state functions, actions, and the
  conversion from non-temporal to temporal formulas;
- `TLA.thy`: the temporal proof system as axioms;
- examples: the increment example, buffer composition, and the RPC-Memory
  case study.

Lessons: (a) lifting ordinary connectives onto a modal layer is a great
ergonomics trick (Lean can do the same with typeclasses or, better, a scoped
syntax category like Leslie's `tlafml`); (b) *axiomatizing* the temporal
logic is what you do when you cannot define the semantics; modern preference
is definitional, and in Lean we can afford to be definitional (see §5, axis
E).

### 2.2 The AFP entry "A Definitional Encoding of TLA\* in Isabelle/HOL" (Grov & Merz, 2011)

The most instructive single reference for semantics. It is explicitly a
**shallow** embedding, and its authors say why (from `Semantics.thy`):

> A shallow embedding represents TLA\* using Isabelle/HOL predicates, while a
> deep embedding would represent TLA\* formulas and pre-formulas as mutually
> inductive datatypes. ... since our target is system verification rather than
> proving meta-properties of TLA\*, which requires a deep embedding, a shallow
> embedding is more fit for purpose.

Key definitions:

- `'a seq = nat ⇒ 'a` (behaviors);
- `'a formula = seq ⇒ bool`, `stfun = 'a ⇒ 'b` (state functions);
- `always F = λs. ∀n. (s|⇩s n) ⊨ F`, `nexts`, `before`/`after`, `unch`,
  `action P v = λs. ∀i. (s|⇩s i ⊨ P) ∨ (s|⇩s i ⊨ unch v)`;
- stuttering similarity `σ ≈ τ` and the predicates `stutinv` (stuttering
  invariance) and `nstutinv` (near-stuttering invariance, the correct
  precondition for action formulas), with per-operator preservation theorems:
  `STUTINV $F`, `NSTUTINV F$`, `STUTINV □F`, `STUTINV □[P]_v` given
  `NSTUTINV P`, and preservation under every connective.

Lessons: (a) in a shallow embedding, stuttering invariance cannot be proved
generically — you must prove it operator by operator. The deep-embedding
question is exactly whether we can promote this from a long list of lemmas to
one structural induction theorem; (b) the distinction `stutinv` vs
`nstutinv` is the right way to think about pre-formulas and must survive any
design; (c) behaviors as `nat → state` is simple and sufficient — coinductive
streams are not needed.

### 2.3 TLAPS, and its Isabelle/TLA+ object logic backend

TLAPS is the production TLA+ proof system: a Proof Manager interprets
hierarchical proofs and emits proof obligations (POs), dispatched to backends:

- **SMT** (Z3/cvc5/veriT), via a translation of TLA+ set theory into
  many-sorted first-order logic (Merz & Vanzetto, "Encoding TLA+ set theory
  into many-sorted first-order logic"): *one* sort for all TLA+ expressions,
  Boolification, CHOOSE axiomatized, TLA+ functions axiomatized (domain,
  application, `IsAFcn`), arithmetic treated as partial, and a preprocessing
  step of *type synthesis* that annotates the obligation with dependent/
  refinement types to make the SMT solver effective;
- **Zenon**: a tableau prover for FOL with sets and functions;
- **Isabelle/TLA+**: "a faithful encoding of the set theory of TLA+ as an
  object logic" in Isabelle — i.e., a *deep* embedding of TLA+'s language
  (syntax + set theory semantics as axioms) in the logical framework, and the
  most trusted backend;
- **LS4**: a decision procedure for propositional temporal logic, used for
  the temporal proof steps that none of the other backends can handle.

Lessons: (a) the *untyped semantics + typed proof obligations* split is the
proven way to keep TLA+ faithful while making automation work. Vanzetto's
thesis ("Proof Automation and Type Synthesis for Set Theory in the Context of
TLA+", 2014) is the canonical account; (b) a proof assistant backend is
valuable not only for interactivity but as the *trusted* core; (c) in TLAPS
the SMT results are checked by the PM only in limited ways, which is why
proof-producing backends were pursued. In Lean, *everything* is kernel-checked,
so `grind` can play SMT's role without a trust gap; (d) the PTL fragment
benefits from a dedicated decision procedure — a future reflection tactic for
Lean (§5, axis E).

## 3. State of the art in Lean (as of mid-2026): what already exists

Two Lean 4 TLA embeddings exist, both shallow, both with typed states, both
derived from `coq-tla`:

- **Lentil** (verse-lab/Lentil): a direct port of coq-tla's definitions and
  proof rules (always, leads-to, weak fairness, big operators) plus a proof
  mode. `exec σ := Nat → σ`, `pred σ := exec σ → Prop`.
- **Leslie** (rupakm/leslie): a substantial shallow framework for verifying
  concurrent/distributed systems: `Spec` = init/next/fairness; stuttering is
  modeled by an explicit disjunct (`□⟨next ∨ s = s'⟩`, i.e.
  `Spec.safety_stutter`); refinement mappings and the Abadi–Lamport safety
  theorem via `exec.map`/`refines_via`; forward simulation relations; CIVL
  layered refinement with mover types; round-based (Heard-Of) models with
  cutoff theorems; a `tlafml` syntax category with macro notation for TLA
  formulas; tactics (`tla_unfold`, modal tactics); examples up to Paxos,
  cache-coherence protocols, and VR view-change.

What these do *not* provide — and what a deep embedding would add:

- no representation of TLA+ expressions/set theory (state is a fixed Lean
  type, so `CHOOSE`, comprehension, and untyped functions have no home);
- no semantic stuttering equivalence: `≈` on behaviors is not defined;
  stuttering is syntactic sugar (`s = s'`), so one cannot state, let alone
  prove, that *every* TLA formula is stuttering invariant, nor reason about
  refinement via true stuttering equivalence;
- no flexible-variable quantification `\EE x : F`;
- no meta-theory (canonical forms, soundness of the rule set);
- no path from an existing `.tla` spec to Lean.

So the design space we are exploring is precisely the ground between these
shallow embeddings and a full TLAPS-style deep embedding, with mathlib and
CSLib as leverage.

## 4. The target language: a precise inventory

Whatever the design, these are the things a faithful embedding must handle.
(Sources: Lamport's *Specifying Systems*; Merz, "The Specification Language
TLA+", 2008; Merz & Vanzetto, *Encoding TLA+ set theory into MS-FOL*.)

**Expressions** (all values are sets):

- set constructs: `{}`, `{a, b}`, `SUBSET S`, `UNION S`, `{x ∈ S : P}`
  (separation), `{e : x ∈ S}` (replacement-style), `CHOOSE x : P` with the
  two axioms `(∃x P(x)) ⇔ P(CHOOSE x : P(x))` and
  `(∀x P(x) ⇔ Q(x)) ⇒ CHOOSE x:P(x) = CHOOSE x:Q(x)`;
- functions: `[x ∈ S ↦ e]`, `f[x]`, `DOMAIN f`, `IsAFcn f`, `[S → T]`;
  application outside the domain is defined but unspecified; tuples and
  records are functions;
- arithmetic: numerals, `Nat`, `Int`, `-`, `+`, `<`, `..`; specified only on
  integers; on other values the result is an arbitrary set ("silly
  expressions" like `3 ∪ TRUE` are legal);
- `IF ... THEN ... ELSE ...`, propositional and quantified formulas (which
  are themselves expressions: `TRUE`/`FALSE` are sets), `=`, `∈`.

**State level**: a state assigns values to variables; state functions are
functions from states to values (`x`, `x'`, `f[x]`); actions are relations on
states (`A`); `Enabled A`; `Unchanged v`; `[A]_v` and `⟨A⟩_v`.

**Temporal level**: behaviors (`Nat → State`); `□`, `◇`, `□[A]_v`, `⟨A⟩_v`,
`WF_v(A)`, `SF_v(A)`, `P ↝ Q` (leads-to), until variants, and the flexible
quantifier `\EE x : F` (hiding). Validity `⊢ F`.

**Specification level**: modules; `CONSTANTS`, `VARIABLES`, assumptions,
definitions (including higher-order operators, i.e., operator parameters);
`INSTANCE` with substitution; the standard modules (Naturals, Integers,
Sequences, FiniteSets, Bags, Functions, Relations); specs in canonical form
`Init ∧ □[Next]_v ∧ L`; refinement via implication of formulas; the TLA+2
hierarchical proof language.

**Meta-theory worth having** (the deep embedding's payoff): every closed
well-formed TLA formula is stuttering invariant; canonical forms; the
standard temporal proof rules (box induction, leads-to, WF1/SF1, `\EE`
intro/elim) are *derived* from the semantics; soundness of refinement
mappings (Abadi–Lamport).

## 5. The design axes

### Axis A — Embedding depth

| Option | What it is | Pros | Cons |
|---|---|---|---|
| **A1. Shallow** | formulas are Lean predicates on behaviors; connectives are Lean connectives (Leslie, Lentil, coq-tla, AFP TLA\*) | trivial to build; full tactic power; notation via macros | cannot express untyped TLA+ syntax or set theory; no meta-theorems; no faithful `\EE`; specs are hand-translated |
| **A2. Definitional deep** | a deep AST for TLA+ expressions and formulas, with a *semantics defined in Lean*; validity is semantic; proof rules are derived lemmas | faithful; kernel-checked end-to-end; can state/prove stuttering invariance of all formulas; can parse real `.tla` | significant engineering; automation must be built on top of the denotation |
| **A3. Deep + object-level calculus** | additionally represent the proof language (TLA+2 proofs) as objects, TLAPS-PM style, with obligations as first-class | closest to TLAPS; supports tooling (proof managers, SMT export) | heavy; in Lean the host proof language already gives structured proofs, so this is mostly redundant |

**Recommendation: A2 for the core.** A3's useful parts (structured proofs,
obligation-oriented tactics) can be layered onto A2 as tactics/DSL. A1
remains a legitimate *user-facing* convenience layer for quick specs, as
Leslie demonstrates, but it is not the deep embedding.

### Axis B — The value universe and typing

This is the heart of the design. TLA+ is untyped; Lean is not.

| Option | What it is | Pros | Cons |
|---|---|---|---|
| **B1. Typed states** | state = one fixed Lean type, variables get Lean types (all current Lean work) | maximum automation; ergonomic | not TLA+; every spec needs a manual translation and loses untyped generality |
| **B2. Bespoke `Val`** | a universal value type with injections (`Val.nat`, `Val.set`, `Val.fn`, ...) | control over the universe | reinvents set theory badly; injection/coercion pain; no extensionality for free |
| **B3. mathlib ZFC** | values are `ZFSet` (mathlib's model of ZFC: `PSet` quotiented by extensional equivalence, with `Class := Set ZFSet`, separation, and choice proved from Lean's choice) | *faithful*: every TLA+ value is a set; `∈`, comprehension, `SUBSET`, `UNION`, `CHOOSE` are already there; thousands of lines of set theory to reuse | heavier terms; automation on `ZFSet` is harder than on `ℕ`; universe levels (`ZFSet.{u} : Type (u+1)`); some TLA+ specifics (functions-with-domain vs sets-of-pairs, partial arithmetic) still need lifting |
| **B4. Typed elaboration on top** | semantics stays untyped (B3), but a *typing layer* annotates expressions with Lean types and generates type obligations for proofs — TLAPS's type synthesis, adapted | proofs live in a typed fragment where `omega`/`linarith`/`grind` work; semantic faithfulness untouched | two layers to maintain; obligation generation is real work |

**Recommendation: B3 semantics + B4 elaboration.** This is the honest
translation of the TLAPS lesson into Lean, with mathlib's ZFC replacing
TLAPS's axiomatized object logic. Isabelle/ZF (Paulson's deep embedding of ZF
in HOL) and Aczel's sets-as-trees are the historical templates; mathlib's
ZFC is the Lean-native version of the same idea, and it is already there.

Two TLA+ specifics need a decision under B3:

- *Functions.* TLA+ in *Specifying Systems* defines functions as sets of
  ordered pairs; TLAPS's proof-language fragment axiomatizes them as
  primitive (`[x ∈ S ↦ e]`, `f[x]`, `DOMAIN`). For a ZFSet universe, the
  sets-of-pairs encoding is the natural one (mathlib ZFC already has ordered
  pairs and functions-as-graphs machinery), but a primitive-function layer
  with typed elaboration is closer to TLAPS's SMT encoding and easier to
  automate. A pragmatic middle: primitive functions at the semantic level,
  with a proof that they coincide with graphs of pairs when the domain is a
  set.
- *Partiality.* `+`, `f[x]` outside the domain, `CHOOSE` on empty classes are
  all total *functions* whose values are unspecified. The mathlib-ZFC design
  totalizes them with `Classical.choice`, which is exactly TLA+'s semantics
  (every expression denotes *some* set). Typed elaboration then keeps proof
  goals well-behaved by restricting to well-typed fragments and generating
  definedness side conditions where needed.

### Axis C — Syntax and binding

Options for the AST:

- **C1. Raw syntax + typing relation** (SANY/TLAPS style): one untyped AST for
  expressions and formulas, a separate typing judgment used for elaboration.
  Faithful to TLA+ but you carry the typing relation everywhere.
- **C2. Intrinsically typed syntax**: syntax carries Lean types by
  construction. Impossible for full TLA+ without losing untyped legality
  (`3 ∪ TRUE`), unless the typing is a *semantic* refinement type over the
  untyped AST.
- **C3. Well-scoped binding** (de Bruijn or locally nameless): the practical
  middle; binders are `CHOOSE x : P`, comprehension, `[x ∈ S ↦ e]`, and
  `\EE x : F`, plus *operator* parameters (higher-order operators) and module
  instantiation with substitution. CSLib has already built locally-nameless
  machinery for its λ-calculi, including `HasContext`/congruence support for
  substitution — direct reuse.

**Recommendation: C3, with two syntactic categories (expression, formula) as
in TLAPS, and C1-style semantic typing for elaboration (axis B4).** The
user-facing surface should additionally offer A1-style notation (Leslie's
`tlafml` shows the pattern), and — as a later milestone — a parser for real
TLA+ modules that generates the AST (see §8).

### Axis D — Where stuttering lives

This is the axis where the deep embedding earns its keep.

| Option | What it is | Consequences |
|---|---|---|
| **D1. Per-operator lemmas** | semantic similarity `≈` plus `stutinv`/`nstutinv` preservation theorems (AFP TLA\*) | works, but no generic theorem; each new operator needs manual preservation proof |
| **D2. Syntactic stutter steps** | specs use `next ∨ s = s'` (Leslie) | pragmatic; refinement is easy; but it is *not* TLA semantics (stuttering-invariance is a semantic property, and `[A]_v` is not definable as a disjunction over arbitrary `v`) |
| **D3. Quotient semantics** | `StutQuot := Quot ≈`; a TLA formula is a predicate on the quotient, with well-definedness proved by structural induction over the deep syntax | the clean formalization: stuttering invariance of *all* formulas becomes one theorem; `\EE` and refinement are naturally statements about the quotient; mathlib gives `Quot`/`Setoid` + quotient induction |

**Recommendation: D3 as the core semantics**, with D1-style lemmas retained
for automation and D2 available as sugar. Concretely:

```lean
-- sketch, not yet typechecked
def Behavior (σ : Type u) := Nat → σ

-- stuttering similarity: coinductive-style relation allowing
-- deletion/duplication of equal-state runs
def Sim {σ} : Behavior σ → Behavior σ → Prop := ...
instance {σ} : Setoid (Behavior σ) where
  r := Sim
  iseqv := ...

abbrev StutQuot (σ : Type u) := Quot (Sim : Setoid (Behavior σ))

-- a TLA formula is a predicate on the quotient
abbrev TlaFormula (σ : Type u) := StutQuot σ → Prop
```

Then the central meta-theorem, provable by induction on the deep syntax, is:
every closed, well-formed formula denotes a well-defined predicate on
`StutQuot`, i.e. `denoteF F` is `Sim`-invariant. In the AFP embedding this
statement cannot even be formulated. (Mathlib's `Quot`, `Setoid`, and
quotient-induction APIs, plus `simp`-friendly extensionality, make this
feasible; the coinductive flavor of `Sim` is where CSLib's bisimulation
library — which already develops weak bisimulation and trace equivalence for
LTSs — can be borrowed wholesale.)

Actions and `[A]_v` sit on top: `Unchanged v := v' = v`; `⟨A⟩_v := A ∧ v' ≠
v`; `□[A]_v := □(A ∨ Unchanged v)`. `\EE x : F` becomes existential
quantification over state functions (`σ → Value`), and the quotient design
must prove that the existential respects `Sim` — the standard TLA result,
now a theorem rather than a convention.

### Axis E — Proof architecture and automation

| Option | Role in TLAPS | Lean equivalent |
|---|---|---|
| **E1. Semantic proofs** | Isabelle backend, Zenon | `simp`/`aesop`/`grind` on the denotation; `omega`/`linarith`/`ring_nf` for arithmetic; everything kernel-checked |
| **E2. Derived rule set** | the temporal axioms (in HOL/TLA) or LS4 | STL/TLA rules (`box-induction`, leads-to, `WF1`/`SF1`, `\EE` intro/elim) proved from the semantics and exposed as lemmas + tactic hooks, following Lentil's `Rules/` and Leslie's `Rules/WF` structure |
| **E3. Reflection/decision** | LS4 (propositional temporal logic); TLC (model checking) | a small verified PTL decision procedure using `native_decide`/reflection; finite-instance model checking for decidable fragments (Leslie has a design sketch for a model-checking tactic) |

**Recommendation: E1 as foundation, E2 as the ergonomics layer, E3 as a
stretch milestone.** The important architectural point, borrowed from CSLib's
manifesto, is that automation is a design constraint, not an afterthought:
definitions should be chosen so that routine obligations fall to `grind`
(which, unlike TLAPS's SMT backend, produces kernel-verified proofs with no
trust gap), and repeated bespoke proof patterns are treated as design
feedback.

## 6. Concrete mathlib / CSLib leverage

The same features that made mathlib attractive for mathematics make the
following mapping natural:

| TLA+ feature | mathlib facility |
|---|---|
| untyped values, `∈`, comprehension, `SUBSET`, `UNION`, `CHOOSE` | `Mathlib.SetTheory.ZFC` (`ZFSet`, `Class`, separation, `ZFSet.choice`) |
| `Nat`, `Int`, arithmetic, `a..b` | `ℕ`, `ℤ`, `Finset.Icc`, `omega`, `linarith`, `ring_nf` |
| `FiniteSets`, `Cardinality`, `Bags` | `Finset`, `Multiset`, `Fintype` |
| sequences/tuples | `List`, `Vector`, `Fin`, `Prod` (records as `Structure`-encoded functions) |
| functions `[S → T]` | `S → T`, `Function`, `Equiv`, `FunLike` |
| behaviors | `Nat → σ` (as in all prior art); mathlib's coinductive `Stream'`/`Seq` as an alternative; `Filter.atTop` gives "eventually/always" vocabulary |
| `P ↝ Q` (leads-to), reachability | `Relation.TransGen`/`ReflTransGen`; `CompleteLattice`, `GaloisConnection`, `FixedPoints` for the temporal lattice and fixpoint views of `↝` |
| stuttering quotient | `Quot`, `Setoid`, quotient induction, extensionality |
| `⊢` on formulas as a preorder | mathlib order APIs (the TLA lattice `□/◇` has useful lattice structure) |
| model checking finite instances | `Decidable`, `native_decide` |
| tactics for set/FO obligations | `grind`, `aesop`, `simp`, `omega` |

And CSLib specifically:

| Need | CSLib facility |
|---|---|
| actions as transition systems; reachability; multi-step | `LTS`, `ReductionSystem`, `MTr`, image/multistep theorems (proved with `grind`) |
| stuttering similarity as a behavioral relation | bisimilarity/similarity/trace-equivalence library; weak bisimulation (stuttering abstraction is morally weak-trace equivalence, with stutter steps playing `τ`'s role) |
| deep-syntax binders and substitution | locally nameless infrastructure from the λ-calculus developments; `HasContext`/`Congruence` typeclasses |
| automation culture | grind-first design, scoped `grind` rule sets, CI/linters — a template for how to structure a TLA+ library |

Two remarks. First, CSLib does not (yet) contain a TLA+ or temporal-logic
module — this is a gap we would be filling, not duplicating. Second, the
weak-bisimulation analogy is not just cosmetic: Abadi–Lamport refinement
under stuttering is a trace-inclusion statement on stuttering-equivalence
classes, so CSLib's trace/weak-bisimulation results are a plausible engine for
the refinement layer.

## 7. Recommended architecture (layered)

```
TLA.Standard    Naturals, Integers, Sequences, FiniteSets, Bags, Functions,
                Relations   (mostly thin wrappers over mathlib)
TLA.Spec        modules, CONSTANTS/VARIABLES, definitions, INSTANCE,
                refinement mappings (Abadi–Lamport) over StutQuot
TLA.Rules       derived STL/action/leads-to/WF/SF/EEx rules + tactic library
TLA.Elab        semantic typing: TLA+ expression/type obligation elaboration
                (TLAPS type synthesis, adapted to Lean)
TLA.Syntax      deep AST (expr/formula), locally nameless, two categories
TLA.Action      state functions, Unchanged, [A]_v, ⟨A⟩_v, Enabled
TLA.Core        Behavior, Sim, StutQuot, ⊨, □, ◇, ↝, WF, SF, \EE, validity
                (the semantic heart, provably stutter-invariant)
Mathlib/CSLib   ZFC, sets/finsets/multisets, arithmetic, order, Quot,
                Relation, LTS, bisimulation, locally nameless, grind
```

Ordered roughly bottom-up:

1. **`TLA.Core`** — behaviors, `Sim`, `StutQuot`, semantic connectives and
   modalities, validity. Typed-state first (`σ` abstract), exactly as in
   coq-tla/Lentil, but with the quotient; this is small and immediately
   testable, and it already subsumes (and generalizes) Lentil.
2. **`TLA.Action`** — state functions, `[A]_v`/`⟨A⟩_v`, `Enabled`, `WF`/`SF`,
   `↝`; derive the standard rules as theorems (Lentil's `Rules/` files are
   the roadmap; Leslie's `WF1` and leads-to infrastructure show the Lean-side
   patterns).
3. **`TLA.Syntax` + `TLA.Elab`** — the deep AST with two categories, and the
   typing/elaboration layer. This is where the "deep" claim is earned: the
   structural-induction stuttering-invariance theorem, and the bridge from
   untyped semantics to typed automation.
4. **`TLA.Standard`** — TLA+ standard modules over mathlib; this is where ZFC
   (`ZFSet`) enters for the *values* of variables, or (phase-1 compromise) a
   typed value universe with the ZFC option behind a namespace.
5. **`TLA.Spec` + `TLA.Rules` tactics** — specs, refinement, proof ergonomics.
6. **Tooling** — TLA+ notation in Lean (Leslie's `tlafml` pattern), then a
   `.tla` parser generating the AST; finite model checking via
   `native_decide`.

### Phasing and risks

- Phase 0 (weeks): `TLA.Core` + `TLA.Action` with typed states; port Lentil's
  rules; quotient stuttering meta-theorem for the semantic layer. Deliverable:
  a library where "formula implies formula" is a Lean theorem and stuttering
  invariance is stated once, not per-operator.
- Phase 1: `TLA.Syntax`/`TLA.Elab` for a *typed* fragment (Nat, Int,
  records, sequences) with semantic typing; stuttering-invariance by
  induction over syntax. Deliverable: the meta-theorem, and a small verified
  spec (e.g., the increment example, a buffer, 2PC safety).
- Phase 2: ZFC-based untyped values (`ZFSet`), CHOOSE, comprehension,
  functions; TLA+ standard modules. Deliverable: faithful semantics for the
  full non-temporal language; "silly expressions" well-defined.
- Phase 3: `\EE`, refinement mapping theorems over `StutQuot`, WF/SF liveness
  at scale; tactic library. Deliverable: a Paxos-level verification in the
  deep embedding.
- Phase 4 (stretch): `.tla` parser, PTL decision procedure, model checking.

Principal risks:

- **ZFC heaviness**: `ZFSet` terms are opaque and automation is slower; the
  typed-elaboration layer exists precisely to keep the *proof* terms in
  `ℕ`/`Finset`/`Function` land. If ZFC proves too slow, fall back to a
  smaller `Val` universe for Phase 2 and keep ZFC as the semantic target.
- **CHOOSE determinism**: TLA+'s extensionality axiom for `CHOOSE` must hold
  definitionally; with `ZFSet.choice` it follows from set extensionality, but
  under typed elaboration `Classical.choose` on predicates needs care
  (choose from a set, not from a proposition, where possible).
- **Partial arithmetic**: totalize like TLAPS (unspecified outside integers)
  and keep definedness side conditions in `TLA.Elab`.
- **`Sim` as a quotient**: quotient induction over a coinductive-flavored
  relation is the subtlest part of `TLA.Core`; CSLib's bisimulation results
  should be ported/parameterized first to de-risk it.
- **mathlib churn**: ZFC and `Stream'`/`Seq` APIs move; pin a toolchain and
  follow CSLib's CI model.
- **Scope creep**: the full TLA+ standard library is large; the wrapper layer
  must stay thin, with mathlib doing the work (that is the point of the
  exercise).

## 8. Open questions worth deciding early

- Do we *parse* `.tla` files (external parser → AST) or write specs directly
  in Lean notation? Recommendation: Lean notation first (Leslie's `tlafml` is
  proof it works), a real parser only if/when existing TLA+ specs need to be
  imported.
- How faithful must the semantics be for `3 ∪ TRUE`-style expressions?
  Recommendation: fully defined via ZFC, but invisible in practice because of
  `TLA.Elab`.
- Is the value universe `ZFSet` from day one, or typed states first?
  Recommendation: typed states first (fast feedback, matches existing work),
  ZFC as Phase 2, with `TLA.Core` parametric over the state type so the swap
  is localized.
- Should this build on Leslie or fork? Recommendation: *do not* fork Leslie
  (it is shallow and its `Spec`/stuttering design is exactly what we are
  replacing), but reuse its notation macros, tactics, and example corpus as
  the test suite for the deep embedding. Lentil's rules are the baseline for
  `TLA.Rules`.
- Where does CSLib's concurrency theory connect first? Recommendation:
  `TLA.Action` as an `LTS` instance (single label or label-free), and the
  refinement layer on top of weak-bisimulation/trace results.

## 9. What success looks like

1. One theorem: every closed well-formed TLA formula is stuttering invariant
   (formally: `denoteF F` respects `Sim`, or `F : StutQuot → Prop` is
   well-typed) — the statement the shallow embeddings cannot make.
2. The standard TLA proof rules (`□`-induction, `↝`, `WF1`/`SF1`, `\EE`) as
   derived theorems, so "TLA proof" and "Lean proof" coincide.
3. A faithfully modeled real spec (Paxos or 2PC or an MSI cache protocol) with
   a machine-checked refinement proof, written in TLA+ notation, reusing
   mathlib's set theory and arithmetic and CSLib's LTS/bisimulation layer.
4. A measurable reuse story: the ZFC/order/finset/relation machinery should
   make the Lean development *smaller* than the Isabelle/TLA+ equivalents.

## References (saved under docs/research/)

See `docs/research/README.md` for the full index with URLs. Core items:

- Lamport, *Specifying Systems* (Addison-Wesley, 2002) — `papers/specifying-systems-lamport.pdf`
- Lamport, *The Temporal Logic of Actions* (TOPLAS 1994) — `papers/tla-lamport.pdf`
- Merz, *On the Logic of TLA+* (2003) and *The Specification Language TLA+*
  (2008) — `papers/merz-*.pdf`
- Grov & Merz, *A Definitional Encoding of TLA\* in Isabelle/HOL* (AFP 2011) —
  `papers/afp-tla-definitional-encoding.pdf`, `web/afp-tla-semantics.html`
- Merz's Isabelle/TLA page and TLAPS design supplement — `web/isabelle-tla-merz.html`,
  `web/tlaps-design-supplement.html`
- Chaudhuri, Doligez, Lamport & Merz, *A TLA+ Proof System* —
  `papers/tla-proof-system-chaudhuri-doligez-lamport-merz.pdf`
- Merz & Vanzetto, *Encoding TLA+ set theory into many-sorted first-order
  logic* — `papers/tla2smt-merz-vanzetto.pdf`
- Vanzetto, *Proof Automation and Type Synthesis for Set Theory in the
  Context of TLA+* (PhD thesis, 2014) — `papers/vanzetto-thesis.pdf`
- coq-tla, Lentil, Leslie sources — `vendor/`
- CSLib Spine paper (Henson & Montesi), mathlib ZFC, CSLib LTS —
  `papers/cslib-spine-henson-montesi.pdf`, `refs/mathlib-zfc-basic.lean`,
  `refs/cslib-lts-basic.lean`
