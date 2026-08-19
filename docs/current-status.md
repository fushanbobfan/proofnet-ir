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
| Rolling research | `v0.10.0-dev`; latest proof checkpoint `cd3ad0f8ea17be50d5ba2333816d33187f483609` | Active | This page and the exact commit |

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

The current checkpoint isolates the exact residual left after classifying all
six rule families for a supplied Figure-7 ready head.

Primary public theorems:

```text
ProofNetIR.SequentialFigure7.CanonicalTagHistory.readyHead_priorityEnabled_or_markedTensorPredecessorGap
ProofNetIR.SequentialFigure7.ReachableByImplementedDispatcher.readyHead_dispatch_or_markedTensorPredecessorGap
```

The history-indexed theorem takes all of the following supplied inputs:

- `Certificate.DeclarativelyCorrect`;
- the complete state-only `SchedulerInvariant`;
- an authentic `CanonicalTagHistory`;
- and a `ReadyHeadInput` for the current state.

It returns an inclusive disjunction:

1. some fixed-priority branch is `PriorityEnabled`; or
2. an exact marked tensor has a retained mate boundary strictly below the
   active top, but no `SigmaPredecessorInput` identifies that boundary with the
   active top's immediate predecessor.

The second branch is stored in
`ReadyHeadMarkedTensorPredecessorGap`: it retains the exact tensor consumer,
concrete mate mark, `sigmaBoundary?` lookup, strict boundary inequality, and
the negated immediate-predecessor witness. The alternatives are not claimed to
be exclusive, and the carrier alone does not state that dispatch fails.

Stable heads reconstruct their existing enabled branch. An unmarked tensor
uses the active-region theorem to obtain input-only `NewEnabled`. A marked
tensor with exact sigma adjacency obtains `UnifyPayloadEnabled`; otherwise the
proof shows that its mate still resolves to a strictly older retained boundary
and returns the precise gap. Under `ReachableByImplementedDispatcher`, the
positive branch is lowered to an actual `dispatch? = some result` equation.

The bounded replay audit checked 6,198 default and 26,658 extended selected
marked-tensor ready heads. Every observed mate had the exact predecessor, so
both runs recorded zero gaps, zero missing previous tops, and zero boundary
mismatches. This is deterministic regression evidence, not a universal proof
that the residual is uninhabited.

## What the rolling theorem does not prove

This checkpoint does not establish any of the following:

- construction or existence of a canonical history or `ReadyHeadInput`;
- a proof that every relevant semantic nonterminal state presents a ready head;
- exclusivity of the disjunction or universal unreachability of the gap;
- the active-top-bucket queue-origin invariant needed to eliminate the gap;
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
commit  cd3ad0f8ea17be50d5ba2333816d33187f483609
tree    67b9e7006202176bd051093c8112a6c224277d94
stage   ready-head priority dispatch residual and predecessor-gap audit
delta   19 files, +1058/-103
```

Local verification on the committed bytes:

- full `lake build`: 418/418 jobs;
- Lean source audit: zero `sorry`/`admit` findings across 203 Lean files;
- generated API reference: current;
- the runnable ready-head residual consumer: passed under `--trust=0` and
  invokes both public theorems while destructuring both branches;
- facade, API manifest, and axiom-audit entry points: passed under `--trust=0`;
- default replay: 23,184 reachable states, 6,198 marked-tensor ready heads,
  6,198 exact predecessors, and zero gaps;
- extended replay: 96,444 reachable states, 26,658 marked-tensor ready heads,
  26,658 exact predecessors, and zero gaps;
- public declaration audit: 890 declarations total;
- audit classes: 608 full-classical, 25 axiom-free, 122 `propext`-only,
  and 135 `propext` plus `Quot.sound`;
- both new public theorems depend only on
  `[propext, Classical.choice, Quot.sound]`;
- every detected explicit theorem input is load-bearing under the
  minimal-hypothesis audit;
- independent proof and integrated-checkpoint reviews reported no actionable
  P0, P1, P2, or P3 findings.

Exact-head GitHub verification:

- workflow: `Lean CI`;
- run: [32238279967](https://github.com/fushanbobfan/proofnet-ir/actions/runs/32238279967);
- build job: [96023016555](https://github.com/fushanbobfan/proofnet-ir/actions/runs/32238279967/job/96023016555);
- exact head: `cd3ad0f8ea17be50d5ba2333816d33187f483609`;
- result: 36 successful steps, zero failures, one expected release-ref-only
  skip; run duration 12m21s and build-job duration 12m16s.

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

1. prove a history-preserved predecessor invariant for every member of the
   active top ready bucket, then specialize it to eliminate the exact gap;
2. prove that every relevant semantic nonterminal certified state supplies a
   ready head;
3. close the queue-origin and New/Wait/Forward/UnifyPayload created-candidate
   laws needed by the global mate-region and raw-mark preservation families;
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
