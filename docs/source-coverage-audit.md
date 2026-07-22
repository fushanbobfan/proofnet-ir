# Local source coverage audit

Audit date: 2026-07-21

## Review question

Which claims in the local corpus are required to justify ProofNet-IR's MLL
semantics, correctness criterion, sequentialization boundary, library design,
and empirical hypothesis, and what has actually been read closely enough to
support those claims?

## Inventory and screening

The workspace contains 15 PDFs. Seven UCLA `131BH` homework/submission PDFs are
coursework artifacts and are not project literature. `paper1_中文讲解.pdf` is a
derived guide to `paper1.pdf`, not an independent source. The project corpus is
therefore seven original PDFs plus the complete short Rowling chat brief.

```text
PDFs inventoried                                      15
Coursework PDFs excluded                              7
Derived duplicate-format guide merged                 1
Original project sources included                     7
Physical pages in included PDFs                     948
Exact repeated pages in linearlogic.pdf             158
Approximate unique physical pages                   790
```

All seven PDFs have extractable text. One page in the Manin scan has no
extractable text and requires visual/OCR treatment.

## Honest coverage matrix

| Source | Pages | Current evidence | Status |
|---|---:|---|---|
| Pfenning, *Linear Logic* | 336 physical; 178 unique after exact repetition | complete contents/theorem sweep; close reading of cut-free calculus, cut elimination, focusing, proof search, and proof terms; selected pages visually checked | not read cover to cover |
| Manin, *A Course in Mathematical Logic for Mathematicians* | 389 | contents/theorem sweep; prefaces and Chapter IX sections 1-6 close read; graph pages visually checked | not read cover to cover |
| *Proof Nets as Graphical Proof Objects* | 20 | complete end-to-end reading and selected-page visual verification | complete |
| *ProofNet-IR Research Plan* | 19 | complete end-to-end reading and selected-page visual verification | complete, but treated as a generated design input rather than authority |
| Marcolli, Berwick, Chomsky, *Syntax-Semantics Interface* | 75 | section/proposition sweep and targeted close readings | not read cover to cover |
| *Geometry of Neuroscience* | 33 | theorem/section sweep and targeted graph/topology/language readings | not read cover to cover |
| Park, *Open Book Decompositions with Page a Four-Punctured Sphere* | 76 | theorem sweep and targeted proof-architecture reading; diagrams sampled visually | not read cover to cover |
| `Rowling_s chat history.txt` | short text | read completely | complete |

Consequently, the statement "all local papers and textbooks were seriously
read in full" is false at this checkpoint. Two project-specific PDFs and the
chat are complete; five larger or adjacent sources have structured and
targeted coverage only.

## Reading protocol required before completion

For each incomplete source:

1. record every chapter/section and physical-page interval;
2. read extracted text page by page, recording definitions, theorem statements,
   hypotheses, proof dependencies, counterexamples, and project consequences;
3. render and visually inspect every page containing proof nets, inference
   rules, commutative diagrams, graphs, tables, or extraction anomalies;
4. distinguish source theorems from project inferences;
5. record a completion line only when every unique page has been accounted for;
6. recheck every code-level mathematical claim against the resulting matrix.

This document is a coverage ledger, not evidence that the remaining reading is
already complete.
