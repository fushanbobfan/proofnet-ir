# Local literature map

## Review question

Can a proof-net-inspired, kernel-checked graph intermediate representation
remove inessential tactic order, support local repair, and remain useful as a
proof-structure dataset even if it does not improve end-to-end solve rate?

## Local screening

The parent knowledge folder was inventoried on 2026-07-21 and live-rescanned on
2026-07-28 with no added, removed, or hash-changed research source. Included
sources are papers, books, and project research notes with mathematical or
architectural relevance. Course homework, rendered page images, temporary
extraction files, and format duplicates of the same Chinese guide were excluded
from the research-source count.
The table also records one metadata/abstract-only journal follow-up as an
explicit unread gate; that row is not part of the local-source count.

| Source | Type | Main contribution | Project use |
|---|---|---|---|
| Frank Pfenning, *Linear Logic* (2002 draft) | textbook/notes | Linear natural deduction, sequent calculus, cut elimination, focusing, proof search, linear lambda calculus, dependent linear type theory | Formal prerequisites and search baselines |
| Yu. I. Manin, *A Course in Mathematical Logic for Mathematicians*, 2nd ed. (2010) | textbook | Formal languages, truth/deducibility, computability, and the explicit contrast between linear strings and nonlinear graph languages | Original motivation; formal-language and graph-language framing |
| *Proof Nets as Graphical Proof Objects* (2026) | technical exposition | Formula occurrences, switchings, Danos-Regnier correctness, contraction, sequentialization, proof identity | Direct checker specification |
| Stefano Guerrini, *Correctness of Multiplicative Proof Nets is Linear* (LICS 1999) | supplemental primary paper | Danos contractibility as token unification; ready/waiting links; sequential unification and special union-find | Exact source for the v0.9 unification rules and the boundary of any future linearity claim |
| Stefano Guerrini, *A linear algorithm for MLL proof net correctness and sequentialization* (TCS 2011) | official metadata/abstract only; full text unread | Abstract describes the full-detail journal presentation of the 1999 algorithm | Follow-up reading gate only; not a locally read PDF and not authority for resolving the current `W` indexing conflict |
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
7. Guerrini 1999 supplies the primary operational rules behind the new
   unification path. The current eager repeated-scan implementation matches
   Figure 5 but does not inherit the linear sequential strategy of Figures
   7--8. Within Figure 7, the prose defines `W` on inactive boundaries and
   `unify` reads the old predecessor, while the printed `new` writes the fresh
   top. ProofNet-IR keeps the literal update only for audit and uses a separately
   identified, kernel-checked operational interpretation that initializes the
   old active boundary and leaves the fresh top undefined. This is not an
   author-confirmed erratum.
8. The official metadata and abstract for Guerrini 2011 were checked, but the
   full text was inaccessible and unread. It is a follow-up reading gate, not
   a locally read source or evidence resolving the 1999 display/prose conflict.
9. Pfenning's focusing result changes the experimental baseline: comparison
   against naive rule enumeration alone would exaggerate the benefit of
   quotienting harmless inference order.

## Evidence gaps

- There is no local experimental evidence yet that graph prediction beats
  tactic generation.
- The plan's redundancy-collapse ratio needs an exact combinatorial definition
  and a tractable estimator.
- General proof-net correctness beyond unit-free MLL is not canonical; units,
  additives, exponentials, and quantifiers each change the representation.
- Finite reachability and tree checking now have full iff theorems against both
  the fuel-indexed and unbounded inductive-walk semantics; the former open
  walk-normalization obligation was discharged by kernel-checked loop erasure.
- Reverse sequentialization of every checker-accepted unit-free, cut-free MLL
  net is now kernel checked via `sequentialization_of_check` and
  `generallySequentializable`. Broader logic fragments and library-readiness
  validation remain separate obligations.
- For the separate Figure-7 scheduler, the operational `W` domain is proved,
  and exact empty/init/operational-new execution history now carries tag iff
  recorded touch, global submitted-slot non-reuse, and reservation-count
  alignment. Exact local `concl`/`nop`/`wait` now preserve the reservation
  invariant; `wait` performs only an initialized-cell cons at the exact
  raw-age `sigma` boundary and does not establish global payload ownership.
  Ready/waiting payload ownership, `forward`/`unify`, full-history integration,
  full-rule reachability, progress, and pure-worklist completeness remain open.

## Reading record

All seven source PDFs have been converted to searchable text without modifying
the originals. A corpus-wide section/theorem sweep and completed ordered
reading are recorded in [reading-ledger.md](reading-ledger.md) and the
[coverage audit](source-coverage-audit.md). Page matrices cover Pfenning,
Manin, Marcolli et al., *Geometry of Neuroscience*, and Park; the shorter
ProofNet documents and Rowling chat were read directly end to end. The matrices
also identify adjacent sources that cannot support core logic claims. Claims
used by code are checked against the original local text, not accepted from
local-model summaries.

The later Guerrini primary-source audit is supplemental to that frozen local
corpus: all ten pages of extracted text and Figures 1--8 were inspected, and
the implementation/claim boundary is recorded separately in
[guerrini-unification-audit.md](guerrini-unification-audit.md).
The 2011 journal follow-up appears in the map only because its official
metadata and abstract were checked; its inaccessible full text was not read
and is excluded from the local-PDF coverage count.

The resulting controlled evaluation design is specified in
[experiment-protocol.md](experiment-protocol.md).
