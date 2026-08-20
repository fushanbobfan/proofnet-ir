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
| Rolling research | `v0.10.0-dev`; latest proof checkpoint `b65409addd9c51df6458e6ffd8a6db4d0e384425`; latest finite-audit evidence `1e46573141a8ad683cc539480f18c92992bda60c` | Active | This page and the exact commits |

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

The current checkpoint proves an exact obstruction to the unrestricted
same-component endpoint-locality law. For every successful typed
`WaitStep certificate before after`, a supplied
`SchedulerInvariant certificate before` implies
`¬ ActiveTopContinuationExitLocalized certificate after`. The theorem is
conditional on the typed Wait transition; it does not construct a transition
or show that any reachable canonical history contains one.

The proof isolates the two impossible localized exits at the Wait output. The
selected active-frontier premise is marked, and its consumer's conclusion is
unmarked waiting work. A raw-mate exit would require the already marked mate to
be unmarked. A future-conclusion exit would place the same unmarked conclusion
in the active component frontier and hence in ready work, contradicting the
scheduler invariant's separation of ready and waiting vertices.

Consequently, `ActiveTopContinuationExitLocalized` cannot be preserved as an
unrestricted invariant through successful Wait transitions. This conclusion
does not require declarative correctness and proves neither reachability nor
post-Wait drainedness. It also does not refute direct
`ActiveTopMarkedNonconclusionDebt`, a locality law restricted to an appropriate
drained state, a temporal or cross-component law, or another sufficient
completion route.

The checkpoint's new public surface is exactly one theorem boundary:

```text
ProofNetIR.SequentialFigure7.WaitStep.not_activeTopContinuationExitLocalized
```

The preceding continuation-exit results remain valid. In particular,
structural well-formedness, queued-vertex unmarkedness, and a supplied
`ActiveTopContinuationExitLocalized` receipt still imply
`ActiveTopMarkedNonconclusionDebt`; declarative correctness, the complete
scheduler invariant, `ActiveTopDrained`, and the same supplied receipt still
imply `core.allMarked = true`. The obstruction limits where that sufficient
hypothesis can hold; it does not weaken either conditional implication.

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
[endpoint-localized continuation exits](api-reference.md#endpoint-localized-continuation-exits),
and the current
[Wait endpoint-locality obstruction](api-reference.md#wait-endpoint-locality-obstruction).
The first open proof step is to derive active-top debt directly from a correct
supplied canonical history, formulate and preserve a Wait-compatible drained,
temporal, or cross-component weakening, or establish another sufficient
completion law. Only after a sound bridge is available can the drained
reduction contribute to an unconditional progress or completion argument.

## What the rolling theorem does not prove

This checkpoint does not establish any of the following:

- construction or existence of a relevant `ExecutedHistory`, reachable state,
  `CanonicalTagHistory`, `ReadyHeadInput`, or successful Wait transition;
- that any reachable canonical history contains a Wait, or that the output of a
  supplied Wait is active-top drained;
- necessity of `ActiveTopContinuationExitLocalized`, or its derivation from
  declarative correctness, reachability, or supplied canonical history;
- direct active-top-debt preservation through complete canonical histories, or
  preservation of a Wait-compatible drained, temporal, or cross-component
  locality law;
- the selected-away witness for Nop or Wait, or the exact non-global tail law
  for global-created Forward or UnifyPayload, from supplied history and
  correctness;
- an unconditional reachable-state proof that `ActiveTopDrained` implies
  `core.allMarked = true`, semantic completion, or terminality without a
  compatible sufficient completion premise;
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
commit    b65409addd9c51df6458e6ffd8a6db4d0e384425
tree      c8737affdecb5e5fe86381014588d0a19feb142a
parent    80a3107a0b12a724d0bad42cd4e45e737f350a82
stage     Wait-output endpoint-locality obstruction
delta     17 paths, +532/-65
manifest  405DEB7AAA3A782B48D4123DCEBBF5B879D56E2634A2EF1EFCD286AE44381DDA
```

The manifest hashes canonical
`path<TAB>UPPER_SHA256<TAB>blob<LF>` records for the committed delta.

The checkpoint source receipts are:

```text
source         1C4AEC37CAF25E3AB653772395B41F85269D390AD15A1AC6D9A75C69C6960FBD
consumer       1F7C24B318852569FBB11B6AD978A2F1C75BAA30B9B604DA12B75FB5ED175515
generated API  A61828AC7FD8F1DF52C1D53BD4CA6C172089F35A32E427F6995B0BFDB11591B6
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

- full `lake build`: 477/477 jobs;
- Lean source audit: zero actual `sorry`/`admit` findings across 227 Lean
  files;
- generated API reference: current at 53 sections and 1,589 declarations;
- the runnable Wait-obstruction consumer invoked the public theorem, reduced an
  assumed output-locality receipt to `False`, and emitted exactly
  `Figure-7 wait-output endpoint-locality obstruction: kernel-green`;
- public declaration audit: 947 declarations total: 657 full-classical, 25
  axiom-free, 127 `propext`-only, and 138 `propext` plus `Quot.sound`;
- the default, extended, and cross-variant progress audits passed with every
  incomplete visited state carrying an exact ready head and successful
  dispatch, every dispatch-none stop fully marked, and zero missing-head,
  incomplete-dispatch-none, cycle, or truncation findings;
- facade, generated API, consumer, and axiom-audit entry points passed under
  the checkpoint's trust-zero and warnings-as-errors gates.

Exact-head proof GitHub verification:

- workflow: `Lean CI`;
- event/ref: `push` / `main`;
- run: [32320379041](https://github.com/fushanbobfan/proofnet-ir/actions/runs/32320379041);
- build job: [96281231734](https://github.com/fushanbobfan/proofnet-ir/actions/runs/32320379041/job/96281231734);
- exact head: `b65409addd9c51df6458e6ffd8a6db4d0e384425`;
- result: 36 successful steps, zero failures, and one expected release-ref-only
  skip;
- run: `2026-08-20T01:15:51Z`-`2026-08-20T01:28:38Z` (12m47s);
- build job: `2026-08-20T01:15:55Z`-`2026-08-20T01:28:38Z`
  (12m43s).

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

1. derive `ActiveTopMarkedNonconclusionDebt` directly from a correct supplied
   canonical history, formulate and preserve a Wait-compatible drained,
   temporal, or cross-component weakening, or prove another sufficient
   completion law; then obtain the unconditional reachable-state
   `ActiveTopDrained → core.allMarked = true` corollary and use marking
   incompleteness to exclude the residual. The unrestricted
   `ActiveTopContinuationExitLocalized` law is refuted after every supplied
   successful typed Wait from a scheduler-invariant input, so it cannot be the
   unchanged full-history invariant. The obstruction proves neither reachable
   Wait existence nor post-Wait drainedness, and progress, completion,
   terminality, later-state totality, and arbitrary history existence remain
   open;
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
