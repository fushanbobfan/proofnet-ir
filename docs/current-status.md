# Current status

> **Replacement policy:** this page contains one rolling mathematics
> checkpoint. Update it in place; do not append checkpoint history here.

This page is the replaceable status record for the rolling research branch.
It is updated in place when a new mathematics checkpoint supersedes the
previous one.
Historical checkpoints belong in [CHANGELOG.md](../CHANGELOG.md), proof design
belongs in [v0.10-design.md](v0.10-design.md), and stable release guarantees
belong in the corresponding release audit.

Status date: 2026-08-19

## Version tracks

| Track | Revision | Status | Authority |
| --- | --- | --- | --- |
| Stable library | `v0.9.0` / `9b7dc3d104af8f57ea9123aab2e61b42e05d2216` | Released | [v0.9.0 release audit](v0.9-release-audit.md) |
| Rolling research | `v0.10.0-dev`; latest proof checkpoint `38ce23c98d77f7fc625805809ddaf28ba30a3ae0` | Active | This page and the exact commit |

Documentation-only commits may descend from the proof checkpoint without
changing its mathematical authority. The stable release and rolling branch
make different claims. A downstream consumer that needs reproducibility should
pin `v0.9.0`. The `main` branch is the integration surface for ongoing Figure-7
scheduler and completeness work.

## Stable v0.9.0 result

For the documented unit-free, cut-free MLL certificate model, v0.9.0 provides:

- occurrence-aware graph semantics, including parallel stored-edge identity;
- an executable Boolean checker proved equivalent to independent structural
  and switching-tree correctness;
- checked desequentialization from cut-free derivations;
- complete checker-free sequentialization for every accepted certificate;
- ordered-conclusion `ProofNetEquivalent` canonical identity and stable wire
  formats;
- sound eager and worklist unification fast paths whose exact wrappers retain
  the complete recursive sequentializer as fallback;
- generated API documentation, checked consumers, compatibility contracts,
  property/fuzz/differential/performance gates, and release-pinned consumption.

The exact release guarantees, receipts, and non-goals are frozen in the
[v0.9.0 release audit](v0.9-release-audit.md).

## Rolling main result

The current checkpoint establishes an indexed marked-tensor predecessor
invariant for every ready or waiting future-work occurrence. It proves the
empty/init/Prepared/Concl/Nop/New/Wait/Forward branch prefix and uses the
invariant to contradict the preceding ready-head residual when the required
state hypotheses are supplied.

Primary public declarations:

```text
ProofNetIR.SequentialFigure7.SigmaImmediatePredecessorAt
ProofNetIR.SequentialFigure7.OlderMarkedTensorPredecessorInvariant
ProofNetIR.SequentialFigure7.OlderMarkedTensorPredecessorInvariant.readyHead_predecessor_of_boundary_lt
ProofNetIR.SequentialFigure7.empty_olderMarkedTensorPredecessorInvariant
ProofNetIR.SequentialFigure7.InitialReservationStep.olderMarkedTensorPredecessorInvariant
ProofNetIR.SequentialFigure7.PreparedStep.olderMarkedTensorPredecessorInvariant
ProofNetIR.SequentialFigure7.ConclStep.olderMarkedTensorPredecessorInvariant
ProofNetIR.SequentialFigure7.NopStep.olderMarkedTensorPredecessorInvariant
ProofNetIR.SequentialFigure7.CanonicalTagHistory.new_olderMarkedTensorPredecessorInvariant
ProofNetIR.SequentialFigure7.CanonicalTagHistory.wait_olderMarkedTensorPredecessorInvariant
ProofNetIR.SequentialFigure7.CanonicalTagHistory.markedMate_sigmaImmediatePredecessor_of_childAnchor
ProofNetIR.SequentialFigure7.CanonicalTagHistory.forward_olderMarkedTensorPredecessorInvariant
```

`OlderMarkedTensorPredecessorInvariant` quantifies over every `FutureWorkAt`,
including every member of every retained ready bucket and every initialized
waiting payload. When a marked tensor mate's current representative is strictly
below the work's current representative, `SigmaImmediatePredecessorAt` records
adjacent sigma positions ending at the work boundary together with the exact
mate-boundary lookup.

The empty state satisfies the predicate vacuously, and every successful initial
reservation establishes it because the raw-mark array remains empty. Prepared,
`concl`, and `nop` preserve a supplied prior invariant under the input
`SchedulerInvariant`. Canonical `new` preservation additionally requires
`Certificate.DeclarativelyCorrect` and an authentic `CanonicalTagHistory`; old
work transports across the fresh append, while a created endpoint's already
marked tensor mate is forced to the prior active boundary immediately below the
fresh boundary.

Canonical `wait` preservation uses the same correctness, scheduler, history,
typed dispatch, and `WaitStep` witnesses. Retained work transports through the
prepared middle state. For the inserted par conclusion, private Wait-specific
geometry internal to the module constructs the destination anchor, closes the
strict commitment interval by finite maximality, and proves that any strictly
older marked tensor mate occupies the immediate predecessor boundary. No
`FutureNewCandidateAt.mate_unmarked` premise is used.

The source-visible child-anchor bridge packages the common maximality argument:
given strict older-event separation and an exact child-event anchor, it returns
the marked mate's indexed immediate predecessor. It does not establish either
premise or any rule's applicability. Canonical `forward` preservation supplies
those premises privately for the inserted par conclusion and transports
retained work through the prepared prefix. It requires declarative correctness,
the complete scheduler invariant, canonical history, typed dispatch and
`ForwardStep` witnesses, and a supplied prior predecessor invariant.

For a supplied `ReadyHeadInput`, the projection combines the new invariant with
the complete `SchedulerInvariant`. The fields of
`ReadyHeadMarkedTensorPredecessorGap` provide the tensor consumer, mate mark,
exact `sigmaBoundary?` lookup, and strict active-boundary inequality. The
projection therefore constructs `SigmaPredecessorInput`, contradicting the
gap's own `no_predecessor` field. This is a consumer-level consequence of the
public declarations; no unconditional gap-elimination premise is hidden in the
state invariant.

Exact signatures are maintained in the
[generated API reference](api-reference.md#older-marked-tensor-predecessor-branch-prefix).
This remains a branch-prefix result, not a full canonical-history theorem:
`unifyPayload` is the first open preservation branch.

## What the rolling theorem does not prove

This checkpoint does not establish any of the following:

- construction of a relevant `ExecutedHistory`, reachable state, or
  `ReadyHeadInput`;
- a proof that every relevant semantic nonterminal state presents a ready head;
- preservation of `OlderMarkedTensorPredecessorInvariant` through
  `unifyPayload`;
- full canonical-history availability of the new invariant;
- unconditional elimination of `ReadyHeadMarkedTensorPredecessorGap` without
  the invariant and complete scheduler hypotheses;
- global preservation of the mate-region or older-raw-mark invariant families;
- any of the explicit New/Wait/Forward/UnifyPayload created-candidate raw seams
  or the queue-origin laws that would discharge them;
- exhaustive enabledness of the canonical dispatcher;
- dispatcher progress or later-state totality;
- pure-worklist completeness;
- removal of the complete recursive fallback;
- faithful whole-program `NEXTAXIOM`/token-age scheduling; or
- a Guerrini-style whole-program linear bound.

These are research gates, not undocumented assumptions. Their current proof
plan is maintained in [v0.10-design.md](v0.10-design.md) and
[roadmap.md](roadmap.md).

## Verification receipt

The exact rolling checkpoint is:

```text
commit  38ce23c98d77f7fc625805809ddaf28ba30a3ae0
tree    fa1f9810918bc4c8aa08c8195269c18e744702d8
stage   marked-tensor predecessor preservation through canonical Forward
delta   18 files, +1028/-72
```

Local verification on the committed bytes:

- full `lake build`: 435/435 jobs;
- Lean source audit: zero `sorry`/`admit` findings across 210 Lean files;
- generated API reference: current;
- the runnable predecessor consumer: passed under `--trust=0`, invokes the nine
  branch-prefix declarations, constructs the indexed carrier, and derives
  `False` from an actual gap's `no_predecessor` field;
- the runnable Wait-preservation consumer: passed under `--trust=0`, invokes
  the tenth public declaration, applies the preserved invariant, destructures
  `SigmaImmediatePredecessorAt`, and consumes all four carrier fields;
- the runnable Forward-preservation consumer: passed under `--trust=0`, invokes
  the public bridge and Forward theorem, applies the preserved invariant, and
  consumes all four indexed predecessor fields;
- facade, API manifest, and axiom-audit entry points: passed under `--trust=0`;
- public declaration audit: 900 declarations total;
- audit classes: 617 full-classical, 25 axiom-free, 123 `propext`-only,
  and 135 `propext` plus `Quot.sound`;
- `empty_olderMarkedTensorPredecessorInvariant` depends exactly on `[propext]`;
- the other six original branch-prefix theorems and the Wait, bridge, and
  Forward theorems depend exactly on
  `[propext, Classical.choice, Quot.sound]`;
- independent proof and integrated-checkpoint reviews reported no actionable
  P0, P1, P2, or P3 findings.

Exact-head GitHub verification:

- workflow: `Lean CI`;
- run: [32256887987](https://github.com/fushanbobfan/proofnet-ir/actions/runs/32256887987);
- build job: [96080550086](https://github.com/fushanbobfan/proofnet-ir/actions/runs/32256887987/job/96080550086);
- exact head: `38ce23c98d77f7fc625805809ddaf28ba30a3ae0`;
- result: 36 successful steps, zero failures, one expected release-ref-only
  skip; run duration 8m47s (`13:13:34Z`-`13:22:21Z`) and build-job duration
  8m43s (`13:13:37Z`-`13:22:20Z`).

## Current library-readiness position

The stable v0.9.0 surface is independently consumable for its exact model.
The rolling branch retains and continuously checks:

- one public umbrella import, `import ProofNetIR`;
- a generated declaration reference;
- source and tag-pinned downstream consumers;
- compatibility and migration contracts for public wire formats;
- checked parsing of untrusted certificate and LeanProp data;
- deterministic unit, property, fuzz, differential, reconstruction, and
  performance gates;
- exact trust-boundary and no-placeholder audits;
- preregistered experiment artifacts and publication-boundary checks.

This does not make the project a mature broad proof-net library. The supported
logic remains unit-free, cut-free MLL; there is no claim for units, Mix, cuts
or cut elimination, additives, exponentials, quantifiers, a general Lean
tactic, arbitrary graph-isomorphism canonicalization, external adoption, or
independent research validation.

## Empirical status

The committed deterministic matched experiment uses 1,000 generated tasks and
an equal 1,000-unit method budget:

| Method | Solved |
| --- | ---: |
| Focused sequent search | 760/1000 |
| Formula-skeleton proof-net generation | 1000/1000 |
| One-edit checker-guided repair | 1000/1000 |

The methods receive deliberately different structural help, consume zero model
tokens, and do not establish a general proof-net advantage.

The amended 180-task model study reports:

| Method | Solved |
| --- | ---: |
| Focused search | 85/180 |
| Net generation | 160/180 |
| Constructed distance-ordered repair | 180/180 |
| Model direct | 117/180 |
| Model repair | 2/180 |

The exact protocols, frozen artifacts, timing amendments, costs, failure modes,
and limitations live under `experiments/` and in
[experiment-protocol.md](experiment-protocol.md). These finite studies are
not ordinary Lean theorem-proving benchmarks and are not evidence of external
deployment.

## Open macro gates

The project goal remains open. The principal outstanding gates are:

1. extend `OlderMarkedTensorPredecessorInvariant` through `unifyPayload`, then
   package full canonical-history preservation so the ready-head residual is
   eliminated wherever that history is available;
2. prove that every relevant semantic nonterminal certified state supplies a
   ready head;
3. close the separate queue-origin and New/Wait/Forward/UnifyPayload
   created-candidate laws needed by the global mate-region and raw-mark
   preservation families;
4. derive exhaustive nonterminal dispatcher progress and later-state totality;
5. prove pure-worklist completeness and remove the recursive fallback without
   weakening the accepted-certificate theorem;
6. implement and verify faithful `NEXTAXIOM`/token-age scheduling and its
   whole-program complexity;
7. continue the traceable, page/chapter-level literature matrix without
   treating file discovery or structural scans as completed reading;
8. preserve public API, migration, downstream, experiment, and release gates
   as the mathematical surface grows.

## Navigation

- Proof design: [v0.10-design.md](v0.10-design.md)
- Architecture: [architecture.md](architecture.md)
- Trust boundary: [trust-model.md](trust-model.md)
- Readiness limits: [library-readiness-audit.md](library-readiness-audit.md)
- Research roadmap: [roadmap.md](roadmap.md)
- Literature inventory: [reading-ledger.md](reading-ledger.md)
- Source coverage: [source-coverage-audit.md](source-coverage-audit.md)
- Generated API: [api-reference.md](api-reference.md)
- Stable release: [v0.9-release-audit.md](v0.9-release-audit.md)
- Historical checkpoints: [CHANGELOG.md](../CHANGELOG.md)
