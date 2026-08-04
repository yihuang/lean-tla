# Research artifacts for Lean/TLA+

Downloaded 2026-08-01 for the deep-embedding design work in
[`../design-space.md`](../design-space.md). Everything here is third-party
material kept for local reference; see each entry for provenance and license
status. PDFs are the authors' online versions unless noted.

## Papers (papers/)

| File | Item | Source |
|---|---|---|
| `specifying-systems-lamport.pdf` | L. Lamport, *Specifying Systems: The TLA+ Language and Tools for Hardware and Software Engineers*, Addison-Wesley, 2002 (full book PDF) | https://lamport.azurewebsites.net/tla/book-02-08-08.pdf |
| `tla-lamport.pdf` | L. Lamport, *The Temporal Logic of Actions*, ACM TOPLAS 16(3), 1994 | https://lamport.azurewebsites.net/pubs/lamport-actions.pdf |
| `tla-proof-system-chaudhuri-doligez-lamport-merz.pdf` | K. Chaudhuri, D. Doligez, L. Lamport, S. Merz, *A TLA+ Proof System* (KEAPPA 2008; arXiv:0811.1914) | https://arxiv.org/pdf/0811.1914 |
| `tla2smt-merz-vanzetto.pdf` | S. Merz, H. Vanzetto, *Encoding TLA+ set theory into many-sorted first-order logic* (2015; arXiv:1508.03838) | https://arxiv.org/pdf/1508.03838 |
| `vanzetto-thesis.pdf` | H. Vanzetto, *Proof Automation and Type Synthesis for Set Theory in the Context of TLA+*, PhD thesis, Université de Lorraine, 2014 | https://hal.univ-lorraine.fr/tel-01751181v1/preview/DDOC_T_2014_0208_VANZETTO.pdf |
| `merz-on-the-logic-of-tla+.pdf` | S. Merz, *On the Logic of TLA+*, Computers and Informatics 22, 2003 (note: §2.4 erratum; superseded by the 2008 chapter) | https://homepages.loria.fr/SMerz/papers/tla+logic.pdf |
| `merz-the-specification-language-tla+2008.pdf` | S. Merz, *The Specification Language TLA+*, in *Logics of Specification Languages*, Springer, 2008 | https://homepages.loria.fr/SMerz/papers/tla+logic2008.pdf |
| `afp-tla-definitional-encoding.pdf` | G. Grov, S. Merz, *A Definitional Encoding of TLA\* in Isabelle/HOL*, Archive of Formal Proofs, 2011 (entry PDF) | https://www.isa-afp.org/browser_info/current/AFP/TLA/document.pdf |
| `cslib-spine-henson-montesi.pdf` | C. Henson, F. Montesi, *Computer Science as Infrastructure: the Spine of the Lean Computer Science Library (CSLib)* (arXiv:2602.15078) | https://arxiv.org/pdf/2602.15078v1 |
| `multimmit-extending-blocks-faster-finality.pdf` | A. Lewis-Pye, P. O'Grady, *Multimmit: Extending Blocks for Faster Finality* (arXiv:2607.21021v2, draft 2026-08-02) | https://arxiv.org/pdf/2607.21021v2 |
| `minimmit-fast-finality-even-faster-blocks.pdf` | B. Kobayashi Chou, A. Lewis-Pye, P. O'Grady, *Minimmit: Fast Finality with Even Faster Blocks* (arXiv:2508.10862, 2025) | https://arxiv.org/pdf/2508.10862 |

## Web pages (web/)

| File | Item | Source |
|---|---|---|
| `isabelle-tla-merz.html` | Merz's Isabelle/TLA page (HOL/TLA in the Isabelle distribution; design notes; completeness) | https://members.loria.fr/SMerz/projects/isabelle-tla/ |
| `tlaps-design-supplement.html` | Supplementary material on the design of TLAPS (SMT and Isabelle backends) | https://members.loria.fr/Stephan.Merz/projects/tlaps/index.html |
| `afp-tla-semantics.html` | AFP TLA theory `Semantics` (shallow embedding, stutinv/nstutinv, full proofs) | https://www.isa-afp.org/browser_info/current/AFP/TLA/Semantics.html |
| `merz-on-the-logic-of-tla+.html` | Paper landing page (abstract, erratum, BibTeX) | https://homepages.loria.fr/SMerz/papers/tla+logic.html |
| `coq-tla-defs.html` | coq-tla `defs.html`: TLA predicates over executions in Coq | https://tchajed.github.io/coq-tla/defs.html |
| `leslie-reservoir.html` | Leslie (TLA in Lean 4) Reservoir project page: features, structure, examples | https://reservoir.lean-lang.org/@rupakm/leslie |
| `tlaplus-constant-lean-zulip.html` | Zulip thread: Lean's equivalence of TLA+'s CONSTANT | https://leanprover-community.github.io/archive/stream/236449-Program-verification/topic/Lean's.20equivalence.20of.20TLA.2B's.20CONSTANT.html |
| `lamport-science-of-concurrent-programs.html` | Lamport's *A Science of Concurrent Programs* book page (final draft, 2024/25) | https://lamport.azurewebsites.net/tla/science-book.html |
| `tlaplus-afp-embedding-discussion.html` | tlaplus list, Dec 2023: Merz on the AFP TLA\* shallow embedding (why it was little used; TLAPS recommended) | https://discuss.tlapl.us/msg05769.html |
| `multimmit-extending-blocks-faster-finality.html` | arXiv HTML rendering of the Multimmit paper (with `multimmit-extending-blocks-faster-finality.txt` plain-text extraction) | https://arxiv.org/abs/2607.21021 |

## Vendored sources (vendor/)

Shallow clones (`.git` removed) for local study:

| Dir | Project | Source |
|---|---|---|
| `leslie/` | Leslie — shallow TLA embedding in Lean 4 (refinement, CIVL layers, HO model, cutoff) | https://github.com/rupakm/leslie |
| `lentil/` | Lentil — TLA in Lean 4, port of coq-tla definitions/rules + proof mode | https://github.com/verse-lab/Lentil |
| `coq-tla/` | coq-tla — TLA embedding in Coq (definitions, liveness rules, examples) | https://github.com/tchajed/coq-tla |

## Source files (refs/)

| File | Item | Source |
|---|---|---|
| `mathlib-zfc-basic.lean` | mathlib ZFC: `ZFSet` (PSet quotiented by extensional equivalence), classes, choice | https://raw.githubusercontent.com/leanprover-community/mathlib4/master/Mathlib/SetTheory/ZFC/Basic.lean |
| `cslib-lts-basic.lean` | CSLib `LTS` (labelled transition systems): structure, multistep, images, finiteness classes | https://raw.githubusercontent.com/leanprover/cslib/main/Cslib/Foundations/Semantics/LTS/Basic.lean |
| `cslib-readme.md` | CSLib README (scope, aims, dependency setup) | https://raw.githubusercontent.com/leanprover/cslib/main/README.md |

## Not saved

- TLAPS Isabelle-backend theories: the pretty-printed theories are part of the
  TLAPS distribution (https://tla.msr-inria.inria.fr/tlaps/), not replicated
  here; the design is described in `vanzetto-thesis.pdf` and
  `tlaps-design-supplement.html`.
- Full mathlib/CSLib: use as dependencies, not vendored.
