# Local source coverage audit

Audit date: 2026-07-22; live inventory and hashes refreshed 2026-07-28

## Review question

Which claims in the local corpus are required to justify ProofNet-IR's MLL
semantics, correctness criterion, sequentialization boundary, library design,
and empirical hypothesis, and what has actually been read closely enough to
support those claims?

## Inventory and screening

The workspace currently contains 16 PDFs. Seven UCLA `131BH`
homework/submission PDFs are coursework artifacts and are not project
literature. `paper1_中文讲解.pdf` is a derived guide to `paper1.pdf`, not an
independent source. The original project corpus is therefore seven PDFs plus
the complete short Rowling chat brief; the later Guerrini primary-source audit
is the sixteenth PDF and is tracked separately below.

```text
PDFs inventoried                                      16
Coursework PDFs excluded                              7
Derived duplicate-format guide merged                 1
Original project sources included                     7
Supplemental primary source included                   1
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
| Guerrini, *A linear algorithm for MLL proof net correctness and sequentialization* (TCS 2011) | not locally held | official metadata and abstract checked; full text inaccessible and unread | metadata-only follow-up, excluded from PDF/page/hash counts |

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

The linked page matrices are the evidence behind the completion claim. A live
2026-07-28 rescan again found the same 16 PDFs, with no new, removed, or
changed research source. Its SHA-256 refresh matched every original-source
prefix recorded in `reading-ledger.md` and the full Guerrini digest below.
The same bounded scan classified all 39 Markdown candidates as ten
ledger/map/page-matrix/Guerrini-audit artifacts and 29 project
design/release/architecture documents, not new external papers or books. The
DOCX/HTML Chinese guide remains a duplicate-format derivative, temporary text
files remain extractions, and the Rowling brief is unchanged. This ledger does
not turn adjacent sources into proof-net authorities and does not replace
kernel checking of the implementation.

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

The same audit records an internal Figure-7 indexing conflict: the 1999 prose
defines `W` on inactive `σ` boundaries and `unify` reads the old predecessor,
whereas the printed `new` writes the fresh active top. The literal transition
is retained only for source comparison. Production code uses a documented
project interpretation that initializes the old active boundary and leaves the
fresh top undefined, with kernel-checked `OperationalWaitingDomain`
preservation. This is not presented as an author-confirmed erratum.
The invariant does not by itself establish payload ownership or reachability.
The exact empty/init/operational-new execution history separately proves tag
provenance, global submitted-slot non-reuse, and reservation-count alignment
for that fragment. Executable `concl`/`nop`/`wait`/`forward`/`unify`,
full-rule reachability, progress, and pure-worklist completeness remain open.

On 2026-07-28 the official metadata and abstract were checked for Guerrini,
[*A linear algorithm for MLL proof net correctness and
sequentialization*](https://www.sciencedirect.com/science/article/pii/S0304397510007127),
*Theoretical Computer Science* 412(20), 2011,
DOI `10.1016/j.tcs.2010.12.021`. The abstract describes a full-detail account
of the 1999 algorithm. The full text could not be accessed and was not read;
the record therefore does not change the 16-PDF inventory, included-page
counts, completion claims, or the status of the 1999 indexing conflict.
