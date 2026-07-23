# Local source coverage audit

Audit date: 2026-07-22

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
Exact repeated pages in linearlogic.pdf             168
Approximate unique physical pages                   780
```

All seven PDFs have extractable text. One page in the Manin scan has no
extractable text and requires visual/OCR treatment.

## Honest coverage matrix

| Source | Pages | Current evidence | Status |
|---|---:|---|---|
| Pfenning, *Linear Logic* | 336 physical; 168 unique after exact repetition | complete ordered text reading and rendered-image inspection of all 168 unique pages in a [page matrix](source-pages/pfenning-linear-logic.md) | complete |
| Manin, *A Course in Mathematical Logic for Mathematicians* | 389 | complete ordered text reading in a [page matrix](source-pages/manin-mathematical-logic.md), including visual inspection of the extraction-empty cover, Kochen-Specker graphs on pages 99-100, and graph-language pages 307-313; the final interval was also checked for substantive embedded images | complete |
| *Proof Nets as Graphical Proof Objects* | 20 | complete end-to-end reading and selected-page visual verification | complete |
| *ProofNet-IR Research Plan* | 19 | complete end-to-end reading and selected-page visual verification | complete, but treated as a generated design input rather than authority |
| Marcolli, Berwick, Chomsky, *Syntax-Semantics Interface* | 75 | complete ordered text reading and rendered inspection of all 19 numbered figures and three algebraic tables in a [page matrix](source-pages/marcolli-syntax-semantics.md) | complete |
| *Geometry of Neuroscience* | 33 | complete ordered text reading and visual inspection of all 33 pages and Figures 1--10; [page matrix and claim boundary](source-pages/geometry-of-neuroscience.md) | complete, but adjacent generated exposition rather than core authority |
| Park, *Open Book Decompositions with Page a Four-Punctured Sphere* | 76 | complete ordered text reading and rendered inspection of pages 1--74, covering every mathematical diagram, code listing, and data table; [page matrix and claim boundary](source-pages/park-four-punctured-sphere.md) | complete |
| `Rowling_s chat history.txt` | short text | read completely | complete |

Consequently, all seven original project PDFs and the complete Rowling chat
have now been read in full under the recorded protocol. This is a corpus
coverage result, not a mathematical endorsement of every source or a claim
that every source supports ProofNet-IR: Park and the generated adjacent
expositions contain no theorem that strengthens the core MLL results.

## Reading protocol used for completion

For each source:

1. record every chapter/section and physical-page interval;
2. read extracted text page by page, recording definitions, theorem statements,
   hypotheses, proof dependencies, counterexamples, and project consequences;
3. render and visually inspect every page containing proof nets, inference
   rules, commutative diagrams, graphs, tables, or extraction anomalies;
4. distinguish source theorems from project inferences;
5. record a completion line only when every unique page has been accounted for;
6. recheck every code-level mathematical claim against the resulting matrix.

The linked page matrices are the evidence behind the completion claim. This
ledger does not turn adjacent sources into proof-net authorities and does not
replace kernel checking of the implementation.

## Supplemental primary-source audit

On 2026-07-23 the project added Stefano Guerrini's ten-page LICS 1999 paper
*Correctness of Multiplicative Proof Nets is Linear* as external primary
literature for the contraction/unification implementation. It is not counted
among the seven original user-provided PDFs above. The complete extracted text
and all eight figures were inspected. The local audit copy's SHA-256 is
`47c2b9fe82c73db3bcbb5c0dab183cb2130c9c446a1ae0f9c72fe59e53cbb149`.

The audit confirms the exact axiom/start, unary-par/forward, and
binary-tensor/unify rules, the waiting-par/deadlocked-tensor distinction, the
total-marking/single-thread acceptance condition, and the extra worklist,
`NEXTAXIOM`, and special union-find structure needed for the paper's linear
theorem. The code-level mapping and nonclaims are recorded in
[guerrini-unification-audit.md](guerrini-unification-audit.md).
