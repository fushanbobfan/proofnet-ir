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
| Rolling research | `v0.10.0-dev`; latest proof checkpoint `8939aa90a460a9e4aa89a76795f6fa0511ee733c`; latest finite-audit evidence `1e46573141a8ad683cc539480f18c92992bda60c` | Active | This page and the exact commits |

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

The current checkpoint proves that supplied branch-local continuation credit
always has a finite normalized exit. `MarkedConclusionChain` records the ascent
through concretely marked, non-global connective conclusions. Formula
complexity increases strictly at every step and remains bounded by the
certificate's intrinsic complexity budget, so a
`MarkedNonconclusionContinuation` receipt ends as a `ContinuationExit`: an
unmarked raw mate, scheduled future-conclusion work, or a concretely marked
global conclusion.

At a drained active boundary, the scheduler invariant turns the open exits into
sharper endpoint facts. A raw mate is structurally non-global and unmarked. A
future conclusion is unmarked and queued at a boundary strictly older than the
active top. The marked-global case remains an explicit terminal alternative.
This is finite normalization of supplied evidence, not a construction of a
history, an endpoint-locality proof, or a progress theorem.

`LocalizedContinuationExit` is the separate endpoint-owned carrier. It has
only raw-mate and future-conclusion constructors, binds the selected endpoint
to one component frontier, and deliberately has no marked-global constructor.
`ActiveTopContinuationExitLocalized` asks for such a receipt at every marked
nonconclusion on the active frontier. This predicate is sufficient only: the
checkpoint neither claims it is necessary nor derives it from correctness,
reachability, or a supplied canonical history, and it proves no arbitrary
history or locality existence theorem.

The checkpoint's new public surface is exactly three carriers, one predicate,
and six theorem boundaries:

```text
ProofNetIR.SequentialFigure7.MarkedConclusionChain
ProofNetIR.SequentialFigure7.ContinuationExit
ProofNetIR.SequentialFigure7.LocalizedContinuationExit
ProofNetIR.SequentialFigure7.ActiveTopContinuationExitLocalized
ProofNetIR.SequentialFigure7.MarkedNonconclusionContinuation.continuationExit
ProofNetIR.SequentialFigure7.FutureWorkAt.rawAge_lt_active_of_activeTopDrained
ProofNetIR.SequentialFigure7.ContinuationExit.elim_of_activeTopDrained
ProofNetIR.SequentialFigure7.LocalizedContinuationExit.continuationExit
ProofNetIR.SequentialFigure7.activeTopMarkedNonconclusionDebt_of_continuationExitLocalized
ProofNetIR.SequentialFigure7.SchedulerInvariant.allMarked_of_activeTopDrained_of_continuationExitLocalized
```

The first reduction theorem requires exactly structural well-formedness,
queued-vertex unmarkedness, and endpoint locality to obtain
`ActiveTopMarkedNonconclusionDebt`. The second combines declarative
correctness, the complete scheduler invariant, `ActiveTopDrained`, and the same
locality law to derive `core.allMarked = true`. Thus the checkpoint packages an
exact sufficient completion route while leaving its missing endpoint-ownership
premise visible.

### Finite ready-head boundary audit

A separately committed bounded replay now classifies each visited state after
successful initialization as marking-incomplete or fully marked and checks
exact typed ready-head reconstruction before invoking the dispatcher. In the
default replay, all 22,590 incomplete states had a ready head and a successful
dispatch, while all 594 dispatch-none stops were fully marked. The extended
replay classified 95,190 incomplete states and 1,254 fully marked stops in the
same way. The cross-variant replay classified 1,172,208 incomplete states and
10,608 fully marked stops.

Across all three modes, the incomplete-without-head,
incomplete-dispatch-none, cycle, and truncation counters were zero. Any future
violation produces a replayable certificate, state, event history, and rule
trace rather than only an aggregate count. These results are bounded
falsification evidence, not a proof of semantic nonterminal-to-ready-head
coverage or progress. Exact counters and scope are maintained in
[performance.md](performance.md).

Exact signatures are maintained in the generated API reference for the
[active-top marked-nonconclusion debt](api-reference.md#active-top-marked-nonconclusion-debt),
[branch-local continuation credit](api-reference.md#branch-local-continuation-credit),
[continuation-credit preservation](api-reference.md#continuation-credit-preservation),
and the new
[endpoint-localized continuation exits](api-reference.md#endpoint-localized-continuation-exits).
The first open proof step is to derive active-top debt or another
history-compatible sufficient completion law from a correct supplied canonical
history. Endpoint locality remains an explicit sufficient assumption not
supplied by that history. Only after a sound bridge is available can the
drained reduction contribute to an unconditional progress or completion
argument.

## What the rolling theorem does not prove

This checkpoint does not establish any of the following:

- construction or existence of a relevant `ExecutedHistory`, reachable state,
  `CanonicalTagHistory`, or `ReadyHeadInput`;
- necessity of `ActiveTopContinuationExitLocalized`, or its derivation from
  declarative correctness, reachability, or supplied canonical history;
- endpoint-locality or active-top-debt preservation through complete canonical
  histories;
- the selected-away witness for Nop or Wait, or the exact non-global tail law
  for global-created Forward or UnifyPayload, from supplied history and
  correctness;
- an unconditional reachable-state proof that `ActiveTopDrained` implies
  `core.allMarked = true`, semantic completion, or terminality without the
  endpoint-locality sufficient law (or some replacement completion premise);
- an exclusivity theorem for the exact-dispatch / active-top-drained
  disjunction;
- a proof that every relevant semantic nonterminal state presents a ready head;
- unconditional elimination of `ReadyHeadMarkedTensorPredecessorGap` without
  the invariant and complete scheduler hypotheses;
- global preservation of the mate-region or older-raw-mark invariant families;
- the remaining global created-candidate raw seams or queue-origin laws needed
  by those separate invariant families;
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

The exact rolling proof checkpoint is:

```text
commit    8939aa90a460a9e4aa89a76795f6fa0511ee733c
tree      7ba1d5c0db32c0169bda73c5abe4f19d821cb838
parent    536d3fc0b820e2ae71ce70ba834af5b6a5b9a715
stage     finite endpoint-localized continuation exits
delta     17 paths, +1000/-46
manifest  586A23C0780BAA1EC31E43186D8776EF31D8A739E3A9B9BE21E318EF12387F65
```

The checkpoint source receipts are:

```text
source         2E1F129EDF8C2B5D7B53A7FE413DFA87AC928D6A8C8B3B9A7EA863BA34AE7708
consumer       CE20C98A1AB821DAB6070F372C87211F9DF86D0807939BAE6801AED76032587E
generated API  49E277D33DF487FA9076589BA618A14BDB89FC5938D70D31537CDA3F6E3A5DFE
```

The separately committed finite-audit evidence is:

```text
commit    1e46573141a8ad683cc539480f18c92992bda60c
tree      e953ef9fe8ef185cea4b5ac5399c6396ca25643b
parent    e7983468736a8a156c2a51985a68828efe26dfae
stage     finite ready-head and dispatch-none replay classification
delta     3 files, +369/-48
manifest  4BBAB7FC99D03D2612459A0FD9291990313A05A184F2572A581BC93C6E49DFDD
```

Local verification on the committed bytes:

- full `lake build`: 472/472 jobs in 94.985 seconds;
- Lean source audit: zero actual `sorry`/`admit` findings across 225 Lean
  files;
- generated API reference: current at 52 sections and 1,588 declarations;
- the runnable endpoint-localized continuation consumer destructed all three
  carriers, consumed the locality predicate, exercised all six theorem
  boundaries, and emitted exactly
  `Figure-7 endpoint-localized continuation reduction: kernel-green`;
- public declaration audit: 946 declarations total: 656 full-classical, 25
  axiom-free, 127 `propext`-only, and 138 `propext` plus `Quot.sound`;
- independent final reviews reported zero P0, P1, P2, or P3 findings;
- the default, extended, and cross-variant progress audits passed with every
  incomplete visited state carrying an exact ready head and successful
  dispatch, every dispatch-none stop fully marked, and zero missing-head,
  incomplete-dispatch-none, cycle, or truncation findings;
- facade, generated API, consumer, and axiom-audit entry points passed under
  the checkpoint's trust-zero and warnings-as-errors gates.

Exact-head proof GitHub verification:

- workflow: `Lean CI`;
- event/ref: `push` / `main`;
- run: [32316380132](https://github.com/fushanbobfan/proofnet-ir/actions/runs/32316380132);
- build job: [96269371407](https://github.com/fushanbobfan/proofnet-ir/actions/runs/32316380132/job/96269371407);
- exact head: `8939aa90a460a9e4aa89a76795f6fa0511ee733c`;
- result: 36 successful steps, zero failures, and one expected release-ref-only
  skip;
- run: `2026-08-20T00:12:10Z`-`2026-08-20T00:25:05Z` (12m55s);
- build job: `2026-08-20T00:12:14Z`-`2026-08-20T00:25:05Z`
  (12m51s).

Exact-head finite-audit GitHub verification:

- workflow: `Lean CI`;
- run: [32273794767](https://github.com/fushanbobfan/proofnet-ir/actions/runs/32273794767);
- build job: [96136251609](https://github.com/fushanbobfan/proofnet-ir/actions/runs/32273794767/job/96136251609);
- exact head: `1e46573141a8ad683cc539480f18c92992bda60c`;
- result: 36 successful steps, zero failures, one expected release-ref-only
  skip; run duration 11m21s (`16:04:18Z`-`16:15:39Z`) and build-job duration
  11m17s (`16:04:21Z`-`16:15:38Z`).

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

1. derive `ActiveTopMarkedNonconclusionDebt` or another history-compatible
   sufficient completion law from a correct supplied canonical history; then
   obtain the unconditional reachable-state `ActiveTopDrained → core.allMarked
   = true` corollary and use marking incompleteness to exclude the residual.
   `ActiveTopContinuationExitLocalized` remains an explicit sufficient
   assumption not supplied by history. The finite exit theorem does not yet
   provide endpoint ownership, and progress, completion, terminality,
   later-state totality, and arbitrary history existence remain open;
2. close the separate queue-origin and remaining created-candidate laws needed
   by the global mate-region and raw-mark preservation families;
3. derive exhaustive nonterminal dispatcher progress and later-state totality;
4. prove pure-worklist completeness and remove the recursive fallback without
   weakening the accepted-certificate theorem;
5. implement and verify faithful `NEXTAXIOM`/token-age scheduling and its
   whole-program complexity;
6. continue the traceable, page/chapter-level literature matrix without
   treating file discovery or structural scans as completed reading;
7. preserve public API, migration, downstream, experiment, and release gates
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
