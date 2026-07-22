# Local literature map

## Review question

Can a proof-net-inspired, kernel-checked graph intermediate representation
remove inessential tactic order, support local repair, and remain useful as a
proof-structure dataset even if it does not improve end-to-end solve rate?

## Local screening

The parent knowledge folder was inventoried on 2026-07-21. Included sources are
papers, books, and project research notes with mathematical or architectural
relevance. Course homework, rendered page images, temporary extraction files,
and format duplicates of the same Chinese guide were excluded from the
research-source count.

| Source | Type | Main contribution | Project use |
|---|---|---|---|
| Frank Pfenning, *Linear Logic* (2002 draft) | textbook/notes | Linear natural deduction, sequent calculus, cut elimination, focusing, proof search, linear lambda calculus, dependent linear type theory | Formal prerequisites and search baselines |
| Yu. I. Manin, *A Course in Mathematical Logic for Mathematicians*, 2nd ed. (2010) | textbook | Formal languages, truth/deducibility, computability, and the explicit contrast between linear strings and nonlinear graph languages | Original motivation; formal-language and graph-language framing |
| *Proof Nets as Graphical Proof Objects* (2026) | technical exposition | Formula occurrences, switchings, Danos-Regnier correctness, contraction, sequentialization, proof identity | Direct checker specification |
| *ProofNet-IR Research Plan* (2026) | project plan | Verified graph IR, MLL-Core/LeanProp/LeanStruct staging, trust model, datasets, evaluation | Initial requirements, revised into testable milestones here |
| Marcolli, Berwick, Chomsky, *Syntax-Semantics Interface: An Algebraic Model* (arXiv:2311.06189) | preprint | Hopf/Rota-Baxter/operadic and geometric models of Merge, parsing, semantics, and attention | Adjacent evidence that tree/graph/algebra IRs can expose composition; not evidence for proof-net gains |
| *Geometry of Neuroscience* (2026 expository notes) | expository notes | Fractals, graph Laplacians, random graphs, variational methods, GFFs, contact geometry, and algebraic language models | Broad mathematical training; graph and energy intuitions, not a proof-net foundation |
| Harahm Park, *Open Book Decompositions with Page a Four-Punctured Sphere* | research paper | Contact-topological classification using open books, monodromy, foliations, and bordered Floer invariants | Complex-proof case study only; outside the first implementation fragment |

## Cross-source synthesis

1. Manin supplies the motivating problem: formal languages are conventionally
   linear strings while important mathematical languages are decorated graphs.
2. Pfenning supplies the operational proof-theory baseline: resource-sensitive
   contexts, cut-free sequent calculus, focusing, and proof search.
3. The proof-net exposition supplies the concrete global criterion: local link
   legality is insufficient; every par switching must be a tree.
4. The ProofNet-IR plan turns that criterion into an untrusted-certificate
   pipeline ending in the Lean kernel.
5. The syntax-semantics paper is conceptually adjacent but does not establish
   theorem-proving efficiency. Its algebraic treatment warns against equating
   “graphical” with “automatically easier to search.”
6. The neuroscience and contact-topology sources provide graph-rich and
   dependency-rich mathematics, but they belong to later case-study work.

## Evidence gaps

- There is no local experimental evidence yet that graph prediction beats
  tactic generation.
- The plan's redundancy-collapse ratio needs an exact combinatorial definition
  and a tractable estimator.
- General proof-net correctness beyond unit-free MLL is not canonical; units,
  additives, exponentials, and quantifiers each change the representation.
- Finite reachability is proved sound with respect to an inductive walk
  semantics, but the converse/completeness direction remains open.
- Full sequentialization remains the central proof obligation for v0.1.

## Reading record

All seven source PDFs have been converted to searchable text without modifying
the originals. The two ProofNet documents were directly read end to end. The
remaining books and papers have been structurally indexed, and section-level
reading notes are being expanded as implementation reaches the corresponding
concepts. Claims used by code are checked against the original local text, not
accepted from local-model summaries.
