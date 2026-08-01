# Deep embedding vs. a native Lean DSL: which specification language should we build?

*Companion to [`design-space.md`](design-space.md). The question: if the end
goal is a **specification language similar to TLA+ in Lean 4**, is a deep
embedding of TLA+ worth the effort, compared to designing a new DSL directly
in Lean?*

## TL;DR

Probably not — *as the user-facing language*. The goal "a specification
language similar to TLA+ in Lean" is better served by a **native Lean DSL**
that keeps TLA's *methodology and temporal semantics* (spec = formula,
refinement = implication, stuttering, fairness, `\EE`) while using Lean's
typed values instead of TLA+'s untyped set theory. The one part of a deep
embedding worth building is a small **reference semantics** ("deep where it
counts") against which the DSL's elaboration is proved *conformant* on a
well-typed fragment — a conformance theorem instead of a full deep toolchain.
A full deep embedding (syntax, parser, untyped values, proof calculus) is
only worth it if the goal is importing existing `.tla` specs verbatim,
claiming exact conformance to TLAPS/TLC semantics, or proving meta-properties
*of TLA+ itself* — and those are different projects.

## 1. The question conflates two decisions

"Deep embed TLA+" and "design a new DSL" are answers to two different
questions that get collapsed into one:

1. **Language source**: do we represent *TLA+ the language* (its syntax,
   grammar, parser, module system), or do we invent a new language whose
   syntax lives in Lean?
2. **Semantic distance**: how close do we want the semantics to be to TLA+'s
   — the stuttering quotient, `[A]_v`, `\EE`, fairness, and, at the deepest
   level, the untyped ZF set theory with `CHOOSE` and partially-defined
   operators?

A "deep embedding" is the combination *TLA+ source × faithful-to-TLA+
semantics*. But the DSL option is not one point: it ranges from
"TLA-flavored notation with simplified semantics" (Leslie today) to
"TLA-like temporal semantics, typed values" (what this document recommends)
to "typed DSL proved equivalent to a formal TLA+ reference semantics on a
typed fragment" (the recommended synthesis). So the real question is not
*deep or DSL*; it is *how much of TLA+ do we actually need, and where should
the boundary sit*.

## 2. What "similar to TLA+" can mean: goal profiles

| Profile | Requirement | Implication for design |
|---|---|---|
| **P1. Methodology + notation** | specs written as `Init ∧ □[Next]_v ∧ L`; refinement as implication; TLA-looking symbols (`□`, `◇`, `↝`, `\EE`) | cheap DSL; semantics can even be simplified (explicit stutter steps) |
| **P2. Temporal semantics** | stuttering invariance as a *semantic* property (behaviors up to `≈`), `[A]_v`/`Unchanged`, `WF`/`SF`, `\EE` over state functions, leads-to | DSL with a stuttering quotient (`StutQuot := Quot Sim`); still typed values; all definable in Lean |
| **P3. Untyped values** | every expression denotes a set; `CHOOSE`, comprehension over the universe, `3 ∪ TRUE` legal; functions with domains; partial arithmetic | forces a deep *value* layer (e.g., mathlib `ZFSet`) and a typing/elaboration layer to keep proofs sane |
| **P4. Language fidelity** | parse existing `.tla` modules; semantics coincides with TLAPS/TLC on the nose; meta-theory of TLA+ (stuttering invariance of *all* formulas, canonical forms) | full deep embedding: AST, parser, module system, standard library, proof calculus or exact-reference semantics |

The key observation: **P2 is achievable in a DSL at moderate cost, and P2 is
what makes TLA *TLA*** (stuttering, refinement, fairness). P3 is where the
cost explodes, and P4 is where the project stops being "a spec language" and
becomes "a formalization of TLA+".

## 3. What the field's track record says

- **Grov & Merz chose shallow on purpose.** The AFP TLA\* entry explicitly
  argues that since "our target is system verification rather than proving
  meta-properties of TLA\*, which requires a deep embedding, a shallow
  embedding is more fit for purpose." Our stated goal ("specification
  language similar to TLA+") is squarely in their position, not TLAPS's.
- **Even that shallow embedding saw little use.** Merz (tlaplus list, Dec
  2023): "The two examples provided in the AFP illustrate how the embedding
  in Isabelle can be used, but I don't think anybody else used the theories.
  ... Personally, I would recommend using TLAPS rather than that encoding."
  Lifting-based ergonomics in a proof assistant turned out to be worse than a
  dedicated proof-obligation system. Lesson for Lean: ergonomics and
  automation must be designed in from the start — a DSL with native Lean
  goals has a fundamental ergonomic advantage over anything that routes
  proofs through a denotation.
- **No one has built a usable deep TLA+ embedding in any proof assistant**
  (Isabelle, Coq, Lean, Agda) in the ~20 years since TLAPS started — TLAPS
  itself is not an embedding but a proof-obligation manager over backends.
  The Coq and Lean attempts (coq-tla, Lentil, Leslie) are all shallow and
  typed. That is strong prior evidence about the cost curve.
- **But the concepts embed fine when values are typed.** Leslie's corpus
  (Paxos, cache coherence, VR view-change, Heard-Of models with cutoff
  theorems) shows that a typed, TLA-flavored framework carries serious
  distributed-algorithm verification. What Leslie gives up is not the
  methodology but the *language* and the *untyped values*.

## 4. Cost comparison (honest estimates, order of magnitude)

| Option | Engineering cost | Main cost drivers |
|---|---|---|
| DSL-P1 (Leslie-style) | weeks–months | notation macros, `Spec` structure, refinement theorem, tactics — mostly done already by Leslie/Lentil |
| DSL-P2 (+ semantic stuttering) | months | `Sim`, `StutQuot`, `[A]_v`/`Unchanged`, `\EE` over typed state functions, WF/SF/leads-to rules, quotient meta-lemmas; CSLib bisimulation + mathlib `Quot` absorb much of it |
| Deep values (P3) | large (years-scale for the full language) | untyped universe (`ZFSet`), `CHOOSE` determinism, partial arithmetic, functions-with-domain, records/tuples, and — the real tax — a typing/elaboration layer so that *proofs* do not have to live in untyped land |
| Deep full (P4) | very large | everything in P3 plus parser, module system/instantiation, standard-library mapping, TLA+2 proof language, maintenance; and the "hidden" cost that every proof obligation routes through denotations unless an elaboration layer and its soundness proof are built |

Two cost observations:

- The expensive part of "deep" is not the semantics — mathlib's ZFC gives
  `ZFSet`, `Class`, separation, and choice essentially for free — it is the
  **proof engineering** around denotations. Every user goal must be
  `denote F σ → denote G σ`, and every rewrite must pass through the
  denotation unless an elaboration layer (with its own soundness proof)
  recovers typed reasoning.
- A DSL pays neither tax: goals are ordinary Lean propositions over ordinary
  types, and `omega`/`linarith`/`grind`/`simp` just work. This is the single
  largest advantage, and it compounds over every proof in the library.

## 5. Benefits comparison

| Criterion | Native DSL | Full deep embedding |
|---|---|---|
| Proof automation | excellent (native types, all mathlib tactics) | poor unless a typed elaboration layer is built and trusted/proved |
| Ergonomics (docs, `#check`, `#eval`, notation) | excellent; syntax is ours to design | constrained by TLA+ grammar and by the AST |
| Data modeling | typed sets/functions/records from mathlib; decidability for free | untyped ZF values; typed sugar needed for usability |
| Model checking (TLC-like) | `native_decide`/`decide` on finite instances, directly on typed specs | needs a decision procedure for denotations or extraction to TLC |
| Existing TLA+ specs | must be hand-translated (trust gap) | importable verbatim |
| Conformance to TLAPS/TLC semantics | claim only with a conformance proof (see §7) | guaranteed by construction |
| Meta-theory of TLA+ | out of scope (but DSL can prove stuttering invariance of *its own* operators) | the point of the exercise |
| Verified implementations / extraction | same language, direct connection (e.g., CSLib program logics, Lean code) | two worlds to bridge |
| Total cost | moderate, incremental | very large, all-or-nothing |

## 6. What "similar to TLA+" really buys us, and what it doesn't

TLA+'s power comes from four things, and they do not all require the deep
route:

1. **Specifications are formulas; properties are formulas; verification is
   implication.** Fully expressible in a DSL (and already in Leslie).
2. **Stuttering, and hence refinement and abstraction.** Expressible in a DSL
   as a semantic quotient — actually the *cleanest* way to state it (one
   `Quot Sim` instead of Leslie's `s = s'` disjunct, which is only correct
   when the state *is* the observation).
3. **Set-theoretic data modeling.** This is where TLA+ is untyped and Lean is
   typed. For most specification work, typed data is a *feature*: TLA+ users
   write type invariants anyway (TLAPS synthesizes types; Apalache requires
   them). The genuinely TLA+-specific bits — `CHOOSE`, comprehension over
   the universe, "silly expressions" — are almost never exercised by real
   specs, which live in a well-typed fragment.
4. **Simplicity and stable notation.** A DSL can copy the notation
   (`tlafml` proves it) and the design discipline (canonical form
   `Init ∧ □[Next]_v ∧ L`, "specify first, refine later") without copying
   the syntax.

What only the deep route gives you: the *standard* — the ability to say "this
Lean formula *is* a TLA+ formula", to reuse the ecosystem (existing specs,
TLC traces, TLAPS proofs, TLA+ education), and to prove things *about* the
language. If none of those are load-bearing, you are paying for insurance you
never collect.

## 7. The synthesis worth building: DSL + conformance oracle

Deep and DSL are not mutually exclusive. The recommended architecture:

1. **The DSL is the product** (P2): typed states, behaviors, `Sim`,
   `StutQuot`, `□`, `◇`, `[A]_v`, `WF`/`SF`, `↝`, `\EE` over typed state
   functions, `Spec`/refinement theorems, TLA notation, `native_decide`
   model checking. This is essentially "Leslie with real stuttering
   semantics", and it is the layer users write and prove in.
2. **A small deep reference semantics is the oracle** (P3, restricted):
   an AST + denotation for a *well-typed fragment* of TLA+ (naturals,
   integers, finite sets, sequences, records, arithmetic, bounded
   comprehension) over `ZFSet` values, with the TLA+ operators interpreted
   per the reference (Merz 2008; tla2smt). No parser, no proof calculus, no
   module system — just enough syntax to say what TLA+ means.
3. **The conformance theorem closes the loop**: the DSL's elaboration is
   proved to agree with the oracle on the fragment — a *verified
   translation* rather than a deep toolchain. Users get typed ergonomics;
   the project gets a machine-checked claim of "faithful to TLA+ semantics
   where it matters."

This inverts the previous design document's emphasis: instead of a deep core
with typed sugar bolted on (and obligations generated for users), the typed
DSL is the core and the deep semantics is an internal, mostly invisible
guarantee. Note this only works if the fragment restriction is acceptable —
which, per §3, it almost always is.

## 8. Decision framework

Ask these questions in order:

1. **Will users import existing `.tla` specs?** If yes and conformance must
   be exact, you need the full deep route (or an unverified front-end
   translator, see below). If imports are nice-to-have, build the front-end
   later as a translation *to the DSL*, cross-checked by model checking the
   source with TLC and the translation with `native_decide`.
2. **Is meta-theory of TLA+ a goal** (proving things *about* TLA+ itself —
   completeness, canonical forms, "all formulas are stuttering invariant")?
   Then deep embed — but recognize the project has changed: it is now a
   formalization project whose product is theorems about TLA+, not a spec
   language.
3. **Is automation the top priority?** Then DSL, decisively; the deep route
   only becomes competitive after a sound, usable elaboration layer — which
   is the hard part.
4. **Do we need to interoperate with TLC/TLAPS evidence?** Model-checking
   evidence can be regenerated inside Lean (finite instances + `decide`);
   TLAPS proofs cannot be imported into either design without work.
5. **What is the budget?** A usable DSL-P2 with the conformance oracle is a
   realistic year-scale project with incremental value at every phase; the
   full deep route is multi-year with little usable value until late.

## 9. Recommendation

**Build the native DSL with faithful temporal semantics (P2), and add the
reference-semantics conformance oracle (§7) as phase two.** Design the DSL's
semantics and notation so that its well-typed fragment is *intended* to
coincide with TLA+'s, and make the divergence from TLA+ explicit and
documented: typed values instead of untyped sets, `CHOOSE` restricted (or
defined as `Classical.choose` over typed domains with a definedness
obligation), functions as typed functions, arithmetic total. If a concrete
need for existing specs arises, add an unverified `.tla` → DSL front-end with
heavy cross-checking; if a claim of exact conformance ever becomes the
product, upgrade the oracle from a fragment to the full language.

> **Where to go next:** [`implementation-strategies.md`](implementation-strategies.md)
> turns this recommendation into a build plan — gap analysis of the existing
> Lean projects, the key notation/semantics decisions, a priority-ordered
> improvement list, and a phased roadmap with UX acceptance criteria.

Keep the deep-embedding blueprint ([`design-space.md`](design-space.md)) in
the drawer: its `TLA.Core`/`TLA.Action`/`TLA.Syntax`/`TLA.Elab` layers are
exactly the oracle architecture, and its mathlib/CSLib leverage analysis
applies unchanged. The difference is who talks to whom: users talk to the
DSL; the deep semantics talks to no one — it just certifies.

## References

- Grov & Merz, *A Definitional Encoding of TLA\* in Isabelle/HOL* (AFP 2011)
  — the explicit shallow-over-deep rationale (`docs/research/papers/afp-tla-definitional-encoding.pdf`).
- Merz, tlaplus mailing list, Dec 2023 — the AFP embedding's lack of use and
  the recommendation to prefer TLAPS (`docs/research/web/tlaplus-afp-embedding-discussion.html`).
- Merz, *The Specification Language TLA+* (2008) — the reference semantics
  (`docs/research/papers/merz-the-specification-language-tla+2008.pdf`).
- Merz & Vanzetto, *Encoding TLA+ set theory into many-sorted first-order
  logic* — the typed-fragment pragmatics (`docs/research/papers/tla2smt-merz-vanzetto.pdf`).
