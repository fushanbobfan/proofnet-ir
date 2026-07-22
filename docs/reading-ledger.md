# Reading ledger

This ledger records what was actually inspected, how duplicate material was
handled, and which claims were allowed to influence the implementation. It is
not a bibliography-by-title: the purpose is to keep the research chain
auditable.

## Corpus boundary

The inventory covers the seven original research PDFs in the parent knowledge
folder and the short `Rowling's chat history.txt` project brief. Course
homework, rendered page images, temporary text extractions, and the DOCX/HTML/
PDF renderings of the same Chinese `paper1` guide are not counted as additional
sources.

All original PDFs were extracted to searchable text without modifying the
source files. A section/theorem sweep was performed across the full extracted
corpus. Close reading is complete for the two project-specific ProofNet
documents, *Geometry of Neuroscience*, Pfenning, and the project chat. The
Pfenning audit covers every unique page in both ordered text and rendered-image
form. The remaining larger book and adjacent papers have a structural pass plus
targeted close readings recorded below. Further cover-to-cover close reading
remains an ongoing research task and must not be represented as finished.

| Source | Physical pages | Extracted words | Coverage in this pass | SHA-256 prefix |
|---|---:|---:|---|---|
| Pfenning, *Linear Logic* | 336 physical / 168 unique | 122,044 | [completed page audit](source-pages/pfenning-linear-logic.md) records ordered text reading and rendered-image inspection of all 168 unique pages | `5d5a29d68c13` |
| Manin, *A Course in Mathematical Logic for Mathematicians* | 389 | 186,440 | [ordered page audit](source-pages/manin-mathematical-logic.md) now covers physical pages 1-192, including visual checks of physical pages 99-100; prior contents/theorem sweep and Chapter IX §§1-6 close read retained | `79baf1ed4e81` |
| *Proof Nets as Graphical Proof Objects* | 20 | 7,990 | direct end-to-end reading and visual inspection | `8166b610c3b8` |
| *ProofNet-IR Research Plan* | 19 | 5,904 | direct end-to-end reading and visual inspection | `4c934e603f8a` |
| Marcolli, Berwick, Chomsky, *Syntax-Semantics Interface* | 75 | 44,391 | full section/proposition sweep; introduction, operadic/tree sections, transformer discussion, and conclusion close read | `ed4daccfdf3e` |
| *Geometry of Neuroscience* | 33 | 15,797 | complete page-by-page text reading and visual inspection; [page matrix](source-pages/geometry-of-neuroscience.md) records every page and the strict claim boundary | `e7730b0731bb` |
| Park, *Open Book Decompositions with Page a Four-Punctured Sphere* | 76 | 25,013 | full theorem sweep; introduction, main statements, proof architecture, and concluding open question close read; Chinese guide checked against the source | `7b756a8759e1` |

### Duplicate-page finding

`linearlogic.pdf` contains two exact repetitions, confirmed independently by
SHA-256 hashes of both decoded PDF content streams and extracted page text:
physical pages 11-20 repeat pages 1-10 with offset 10, and physical pages
179-336 repeat pages 21-178 with offset 158. Every duplicate group has exactly
two members. The reading unit is therefore 168 unique pages, not the previously
reported 178 or the 336 physical pages. The file-level hash above remains the
hash of the unaltered original PDF.

## Source notes and project consequences

### Pfenning: operational proof-theory baseline

- The sequent calculus separates unrestricted resource factories from linear
  resources and requires every linear hypothesis to be consumed exactly once.
- Cut admissibility is not merely a metatheoretic nicety: it removes arbitrary
  lemma guessing and yields the subformula discipline needed for a finite
  benchmark fragment.
- Proof search distinguishes conjunctive, disjunctive, resource, universal,
  and existential choices. In MLL, resource splitting is the central hard
  choice.
- Focusing removes rule-order choices for strongly invertible connectives while
  preserving soundness and completeness. Therefore ProofNet-IR must be compared
  with focused cut-free search, not only with a deliberately weak unfocused
  tactic baseline.
- Proof terms and independent type checking motivate the project's trust path:
  an external graph proposer is untrusted; the reconstructed term and Lean
  kernel are authoritative.

### Manin: graph languages are formal languages

- Manin explicitly contrasts linear strings with nonlinear languages such as
  drawings, scores, and decorated graphs.
- Chapter IX treats graphs as combinatorial objects and categories, not as
  informal pictures. Models/interpretations are functors on categories of
  decorated graphs.
- The distinction between evaluating a fixed program and composing new
  programs suggests that a ProofNet IR should expose both certificate checking
  and graph composition.
- Contraction and localization identify programs that differ only by
  associative regrouping. Applying this to proof bureaucracy is a project
  inference, not a theorem stated by Manin.

### Proof-net exposition and research plan

- Formula occurrences must be explicit: equal formula labels at different
  locations are not interchangeable resources.
- Local link legality is insufficient. For unit-free MLL without Mix, every
  par switching must be connected and acyclic, equivalently a tree.
- Desequentialization forgets irrelevant rule order; sequentialization is the
  reverse existence theorem and the principal unfinished v0.1 obligation.
- The proposed persistent/linear context split belongs after the verified MLL
  core. It must not be silently folded into the current certificate semantics.
- The project documents are design inputs, not external evidence of empirical
  gains. The chat identifies the first and third files as generated drafts, so
  every mathematical claim used by code is independently checked or stated as
  an assumption/open obligation.

### Syntax-semantics interface

- Rooted trees, forests, Hopf-algebra cuts, operads, and semiring-valued parsing
  give a precise vocabulary for compositional structure and local/global
  transformations.
- The paper treats language-model attention as a possible inverse-problem
  instrument but also stresses that architecture-dependent experimental
  behavior is not a linguistic theory.
- This is conceptual support for a compositional graph IR. It is not evidence
  that proof nets improve theorem-proving success or efficiency.

### Geometry of neuroscience

- The text repeatedly connects local definitions to global invariants:
  expansion turns local parity checks into global distance, graph Laplacians
  connect edge-local variation to global spectrum, and directed flag complexes
  distinguish missing edges from higher-dimensional cavities.
- The language section represents Merge by rooted trees/forests and admissible
  cuts, reinforcing the usefulness of explicit composition and decomposition.
- These analogies improve mathematical vocabulary but do not enter the
  trusted proof of correctness.
- The complete [33-page audit](source-pages/geometry-of-neuroscience.md)
  confirms that the notes contain no proof-net correctness, sequentialization,
  desequentialization, canonicalization, or performance theorem. They cannot
  be used as evidence for those claims.

### Four-punctured-sphere open books

- The paper combines mapping-class normal forms, open-book foliations, contact
  invariants, and bordered Floer gluing. Its main classification separates
  tightness from non-vanishing of the Heegaard Floer contact invariant.
- The proof is dependency-rich and diagram-heavy, so it is a candidate for a
  later hierarchical proof-graph case study.
- It is deliberately excluded from the first MLL implementation fragment; a
  premature encoding would confound proof-graph evaluation with a large amount
  of domain formalization.

## Visual verification

Selected pages across the corpus, plus every page of *Geometry of
Neuroscience*, were rendered and inspected for content that plain-text
extraction can corrupt:

- the two-axiom tensor/par proof net and the Danos-Regnier switching statement;
- the ProofNet-IR sequentialization and persistent/linear-context formulas;
- Pfenning's linear/unrestricted sequent judgment and focusing phases;
- Manin's formal graph definition using flags, tails, and edges;
- Park's four-punctured-sphere mapping-class formulas and surface diagram.
- all 33 pages and all ten numbered figures in *Geometry of Neuroscience*.

The rendered formulas agree with the descriptions used in the repository.

## Reading-driven implementation constraints

1. Keep occurrences and link incidence explicit.
2. Separate executable finite checking from declarative graph semantics.
3. Prove checker soundness before using generated certificates.
4. Treat general sequentialization as a theorem, never as a parser side effect.
5. Benchmark against focused cut-free proof search.
6. Measure proof identity only after defining a canonical net isomorphism or
   canonical serialization.
7. Keep later persistent hypotheses, contraction, and weakening explicit.
