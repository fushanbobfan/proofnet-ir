# Local source coverage audit

Audit date: 2026-07-22; live PDF/chat inventory and hashes refreshed 2026-08-06

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
2026-08-06 PDF/chat rescan again found the same 16 PDFs, with no new, removed,
or changed research source. Its SHA-256 refresh matched every original-source
prefix recorded in `reading-ledger.md` and the full Guerrini digest below; the
Rowling chat matched the full digest recorded there. The broader 2026-07-28
bounded scan classified all 39 Markdown candidates as ten
ledger/map/page-matrix/Guerrini-audit artifacts and 29 project
design/release/architecture documents, not new external papers or books. The
DOCX/HTML Chinese guide remains a duplicate-format derivative, temporary text
files remain extractions, and the Rowling brief was unchanged in the current
rescan. This ledger does
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
for that fragment. Exact local `concl`/`nop`/`wait`/`forward` are now
executable with
proof-carrying canonical consumer/conclusion views; local `wait` resolves the
mate raw age through `sigmaBoundary?` and prepends only to an initialized
cell. Forward now also has an independent Boolean-free direct rule and exact
executable correspondence; its `Nodup` condition is explicitly a fail-closed
list shape rather than the paper's non-strict raw-age guard. Conditional
state-only queue ownership is preserved under the supplied invariant. The
arbitrary-payload atomic `UnifyPayload` transition now also preserves the full
occurrence-exact state-only invariant on every successful step: the input
invariant yields pre-activation freshness/provenance, each stored par activation
establishes exact ownership, and the final forest covers the payload. A
separate input-only predicate proves conditional applicability under the full
invariant, but not invariant-alone enabledness or unconditional reachability.
A canonical priority dispatcher and proof-carrying certified history now
integrate every implemented successful rule family and prove exact canonical
reservation-event counting against final `nextAge`. Structural route
reconstruction now recovers the exact proof-relevant
source-left run and terminal-partner exclusion. Canonical reservation counting
derives strict fresh capacity for that exact run; an exact axiom-endpoint
queue-history theorem derives both post-pop endpoint absences without claiming
that arbitrary queued connective conclusions are tagged. Hence canonical and
certified histories prove `NewEnabled ↔ NewInputNecessary` while retaining the
exact route as an explicit premise. The implementation now classifies every
structurally well-formed in-bounds source-left search as either a
formula-budget exact run or a nonempty tag/raw-mark blocker on a visited
stored-left occurrence or the terminal axiom partner. Source shape,
singletonhood, and fuel are discharged structurally; queue separation and
fresh capacity remain post-run. Canonical history plus the complete invariant
now classifies each exact blocker further: a tag failure is a prior exact
history touch, while a raw-mark failure is either the current selected-head
update or an old raw-marked occurrence with occurrence-exact ownership in a
live component. The three alternatives may overlap. An explicit universal
no-obstruction premise yields the exact run and the established
`NewInputNecessary`/`NewEnabled` bridges, but deriving that premise from
correctness and certified history is still open. The exact historical-event
touch subcase is excluded when its current representative equals the active
head representative, and the active-region order layer below classifies every
remaining touch as strictly older. Global older-event separation and old
marked-owner blockers remain. Authentic reservation-event touch is now exactly
equivalent to membership in that event's complete structural source-left
region under structural well-formedness. This reverse direction reconstructs
only the successful run stored by the event and supplies no new current-owner,
representative-order, created-region, or progress fact. This checkpoint is an
implementation consequence of the already-audited source semantics and does
not record a new literature reading. The resulting event-touch predicate is
now proved equivalent to the older-region separation invariant under the same
structural assumption, with identical ledger/candidate/current-representative
quantification. That is a proof-interface normalization, not a new paper claim
or a proof that the invariant is globally available. The active-region order
layer now derives a further code consequence: an authentic event touch in the
active mate region must be strictly older in representative and raw-age order,
and a supplied older-event separation invariant therefore makes the complete
region tag-fresh. It does not add a literature reading or provide the route,
readiness, queue/capacity, or global-invariant witnesses still needed for
enabledness. A further kernel-checked code consequence decomposes a historical
touch of any future tensor conclusion into a mate touch or queued-head touch;
for the active candidate the conditional tag-freshness theorem eliminates the
mate branch. This is not a new literature reading, does not prove the
conclusion untouched, and leaves the head-touch/raw-mark obstruction open. The
strictly older queued-head residue is now packaged as
`OlderEventFutureWorkTouchSeparated`. Together with the separate mate-region
law and structural well-formedness it yields strict candidate-conclusion
non-touch. Empty, structurally well-formed init, and Prepared/concl/nop
preservation are proved. This is another kernel-checked code
consequence, not a new literature reading or evidence that canonical histories
satisfy the new invariant. The successful typed New case is now a further
kernel-checked code consequence: retained candidates transport, old-event
touch of a created endpoint contradicts canonical history disjointness, and
the fresh event cannot be strictly older. It requires the supplied prior
invariant and is not evidence of global availability. The successful typed
Wait case is conditionally preserved under the candidate-indexed
`WaitCreatedHeadTouchSeparated` premise. Retained candidates transport and the
inserted conclusion is exactly the residual old-event/head obligation. This is
also a code consequence rather than a literature result, and it does not derive
the residual from scheduler invariants, history, or reachability. The successful
typed Forward case is conditionally preserved under the candidate-indexed
`ForwardCreatedHeadTouchSeparated` residual, with retained work transported
through Prepared and exact Forward representative equality. It is likewise a
code consequence and does not derive the residual. The successful typed
UnifyPayload case is conditionally preserved under the candidate-indexed
`UnifyPayloadCreatedHeadTouchSeparated` residual. Survivor and moved candidates
transport through the prior invariant after strict output order excludes the
retired active class; the inserted conclusion is the sole residual case. This
is also a code consequence, not a literature result, and does not derive the
residual. Global invariant and all three residuals' availability,
same-boundary target paths, raw seams, and progress remain open. A further
kernel-checked code consequence now connects the two supplied separation
invariants to retained commitment geometry. Under the complete scheduler
invariant, the child-event untouched callback follows automatically for an
adjacent edge whose child boundary is strictly older than a future candidate;
strict sigma ordering extends this to a positive interval from only strict
oldness of its final boundary. This is not a new literature result and does not
derive global invariant availability, cover the equal-boundary case, recover
queue origin, close a raw seam, or prove progress. The availability-reduction
layer now consumes the existing
structural search and those code invariants: it proves `NewSourceRegionInput`
or an exact old marked owner, then `NewEnabled` or that owner. This is another
code consequence rather than a new literature reading. The subsequent
raw-mark separation layer turns owner exclusion into a precise state
invariant, proves its empty/initial and Prepared/concl/nop cases, and derives
active-region no-mark/no-owner from it. That is also a code consequence, not a
new literature reading. Global preservation of the mate-region and
older-raw-mark separation invariants through candidate-creating rules remains
open. The future-head-touch invariant is preserved through New and
conditionally through Wait, Forward, and UnifyPayload under their exact
residuals; global availability of the invariant and all three transition-local
residuals remains open. The New raw-mark branch is now conditionally
transported: switching acyclicity removes
the selected-mark/created-candidate case, and
`NewRetainedRawMarksSeparated` names the sole remaining retained-mark seam.
This is a kernel-checked code consequence, not a new literature reading or a
proof that canonical histories satisfy the seam. The Wait raw-mark branch is
also conditionally transported: the typed age order eliminates the selected
mark, and `WaitRetainedRawMarksSeparated` names the retained-mark seam. This is
again a kernel-checked code consequence, not a new literature reading or proof
that canonical histories satisfy the seam. The Forward raw-mark branch is
likewise conditionally transported: selected and inserted work share the same
active raw age, and `ForwardRetainedRawMarksSeparated` names the sole
retained-mark seam. This is a kernel-checked code consequence, not a new
literature reading or proof that canonical histories satisfy the seam. The
UnifyPayload raw-mark branch is now conditionally transported as well: strict
output order excludes the retired active class, and
`UnifyPayloadCreatedRawMarksSeparated` names the inserted-candidate seam. The
covering origin alternatives need not be exclusive. This is again a
kernel-checked code consequence, not new literature reading or evidence that
canonical histories satisfy the seam. Canonical histories now have an exact
raw-mark event provenance layer: every final
concrete mark is the selection of an authentic typed dispatcher branch, and
the one-step effect is exactly old-or-current-event. This is a kernel-checked
code consequence, not a new literature reading. It does not identify raw marks
with `NEXTAXIOM` touches and does not by itself supply queue origin,
vertex-level commitment paths, target avoidance, or any created-candidate
seam. An independent kernel-checked commitment-spine layer now proves that
every adjacent pair in the final retained `sigma` is backed by the exact
historical `new` event stored at the child raw-age ledger slot. This closes
allocation ancestry only and is not a new literature reading. Ownership
through a complete reachable transition system remains open, but a new
kernel-checked code consequence now gives the local raw-mark reservation
anchor: each concrete mark and both endpoints of its same-age reservation event
share one exact owned carrier, with contained paths to both endpoints. This is
not a new literature reading. A further kernel-checked code consequence now
composes one exact adjacent retained commitment edge from the parent event's
left endpoint to the child event's left endpoint, retaining the historical
`new` step and both owned anchors. This too is not a new literature reading.
A further kernel-checked code consequence conditionally makes that single edge
avoid a supplied future tensor conclusion when the exact child ledger event is
explicitly known not to touch it. This is not a new literature reading and does
not derive the untouched law. A further kernel-checked code consequence now
composes explicit adjacent avoiding witnesses across any positive-length
retained-`sigma` interval. It matches exact middle ledger events and uses
verified loop erasure; this too is not new literature reading. Global
availability of the untouched laws and edge callbacks, unconditional
whole-history instantiation, queue origin, the four raw seams, later-state
totality, progress, and pure-worklist completeness remain open.

On 2026-07-28 the official metadata and abstract were checked for Guerrini,
[*A linear algorithm for MLL proof net correctness and
sequentialization*](https://www.sciencedirect.com/science/article/pii/S0304397510007127),
*Theoretical Computer Science* 412(20), 2011,
DOI `10.1016/j.tcs.2010.12.021`. The abstract describes a full-detail account
of the 1999 algorithm. The full text could not be accessed and was not read;
the record therefore does not change the 16-PDF inventory, included-page
counts, completion claims, or the status of the 1999 indexing conflict.
