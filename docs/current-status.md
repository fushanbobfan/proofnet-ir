# Current status

> **Replacement policy:** this page contains one rolling mathematics
> checkpoint. Update it in place; do not append checkpoint history here.

This page is the replaceable status record for the rolling research branch.
It is updated in place when a new mathematics checkpoint supersedes the
previous one.
Historical checkpoints belong in [CHANGELOG.md](../CHANGELOG.md), proof design
belongs in [v0.10-design.md](v0.10-design.md), and stable release guarantees
belong in the corresponding release audit.

Status date: 2026-08-20

## Version tracks

| Track | Revision | Status | Authority |
| --- | --- | --- | --- |
| Stable library | `v0.9.0` / `9b7dc3d104af8f57ea9123aab2e61b42e05d2216` | Released | [v0.9.0 release audit](v0.9-release-audit.md) |
| Rolling research | `v0.10.0-dev`; proof `c56dfce`; audit `1e46573` | Active | This page/commits |

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

The current checkpoint specializes the normalized parent escape to actual Nop
and Wait failures. The preceding source and continuation-credit normalizers
remain valid: when the prepared non-global ready-tail witness is absent, they
map a correct, canonically recorded parent escape to
`ActiveCarrierParentTemporalOutcome`. The new typed-step theorems then rule out
the selected-head raw case. Nop uses its unmarked-mate guard; Wait uses the
strict raw-age order of its concretely marked mate.

The strengthened `ActiveCarrierParentExternalTemporalOutcome` therefore has
only three cases. An unmarked raw endpoint lies outside the active owned
carrier. Future parent work lies outside that carrier at a strictly older raw
boundary. A concretely marked parent conclusion lies outside the carrier and
has a strictly older representative. The last case can continue a connective
chain, and “outside” is component-local rather than global. The carrier is a
failure reduction, not re-entry, a ready-tail witness, residual elimination,
history-tail proof, or derivation of `ActiveTopDebtTailLaw`.

The preceding queue/history-tail checkpoint remains valid. For supplied typed
Nop and Wait steps, its iff theorems identify post-step debt with the exact
non-global `remainingTop` witness, assuming the input scheduler invariant and
prior debt. Its reset-aware `CanonicalTagHistory.ActiveTopDebtTailLaw` still
packages all six branch obligations, and its endpoint theorem still derives
debt only from a supplied instance of that law. Correctness plus canonical
history has not yet been proved to produce the law.

The earlier Wait obstruction also remains valid: every successful typed Wait
from a scheduler-invariant input refutes unrestricted
`ActiveTopContinuationExitLocalized` at its output. It rules out that unchanged
same-component locality carrier, but neither refutes direct debt nor supplies
the required queue-tail or parent re-entry argument.

Within `ProofNetIR.SequentialFigure7`, the checkpoint's new public surface is
exactly four declaration boundaries:

```text
ActiveCarrierParentExternalTemporalOutcome
ActiveCarrierParentExternalTemporalOutcome.temporalOutcome
NopStep.externalParentTemporalOutcome_of_no_readyTail
WaitStep.externalParentTemporalOutcome_of_no_readyTail
```

The earlier parent-escape, source-temporal, debt, history-tail,
continuation-exit, common temporal-outcome, and conditional all-marked results
remain valid. The new reduction removes one selected-head alternative but does
not make any conditional implication unconditional.

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
[active-top debt branch residuals](api-reference.md#active-top-debt-branch-residuals),
[active-top debt ready-tail normalization](api-reference.md#active-top-debt-ready-tail-normalization),
[active-top debt history-tail law](api-reference.md#active-top-debt-history-tail-law),
[active-top debt parent escape](api-reference.md#active-top-debt-parent-escape),
[parent-escape temporal residual](api-reference.md#active-top-debt-parent-escape-temporal-residual),
[parent temporal outcome](api-reference.md#active-top-debt-parent-temporal-outcome),
[external parent outcome](api-reference.md#active-top-debt-parent-external-temporal-outcome),
[branch-local continuation credit](api-reference.md#branch-local-continuation-credit),
[continuation-credit preservation](api-reference.md#continuation-credit-preservation),
[endpoint-localized continuation exits](api-reference.md#endpoint-localized-continuation-exits),
and the retained
[Wait endpoint-locality obstruction](api-reference.md#wait-endpoint-locality-obstruction).
The first open proof step is now a first-reentry or ownership law for an
external raw or strictly older outcome, or a proof that the normalized failure
already carries a distinct active ready-tail payer. The remaining
global-created Forward/UnifyPayload alternatives must also be derived.
Together these are the missing implication from correctness plus canonical
tag history to `ActiveTopDebtTailLaw`. Only after that law is established can
the debt and drained reductions contribute to an unconditional progress or
completion argument.

## What the rolling theorem does not prove

This checkpoint does not establish any of the following:

- construction or existence of a relevant `ExecutedHistory`, reachable state,
  `CanonicalTagHistory`, `ReadyHeadInput`, or successful Nop or Wait transition;
- impossibility of `ActiveCarrierParentEscape`, exclusivity between an escape
  and a valid non-global ready-tail witness, or a proof that an escaped parent
  re-enters the active carrier;
- elimination of `ActiveCarrierParentExternalTemporalOutcome`, including a
  theorem that an external raw or older endpoint re-enters the active carrier
  or supplies a distinct ready-tail payer;
- terminality of the temporal outcome; in particular, its marked case may
  continue through another submitted connective;
- the failure-conditioned first-reentry, ownership, or ordered
  distinct-payment law needed to turn the external-only outcome into the
  missing queue-tail result;
- derivation of `ActiveTopDebtTailLaw` from declarative correctness,
  reachability, or the matching canonical tag history;
- existence of the exact non-global `remainingTop` witness for Nop or Wait, or
  the exact global-created tail alternative for Forward or UnifyPayload, from
  supplied correctness and history;
- endpoint debt from canonical history alone, without the explicit tail-law
  premise;
- that any reachable canonical history contains a Wait, or that the output of a
  supplied Wait is active-top drained;
- necessity of `ActiveTopContinuationExitLocalized`, or its derivation from
  declarative correctness, reachability, or supplied canonical history;
- preservation of another Wait-compatible drained, temporal, or
  cross-component locality law;
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
commit    c56dfce2c015b57106b931edf7538be7c7c2d95b
tree      9984c611e755c736c0eefa23e9cfd0ee6a474c62
parent    5e9db7d1c20a47507cd7aca8bce7eb7ce9295209
stage     active-top debt external parent temporal outcome
delta     17 paths, +776/-21
manifest  C4754741D1078EA786795693D356904F688AB3EF51EC1E8BCF66EC96328A7E3C
```

The manifest hashes canonical
`path<TAB>UPPER_SHA256<TAB>blob<LF>` records for the committed delta.

The checkpoint source receipts are:

```text
source         8C7082E0A9CAF1E2DB633FC5EE985B361D04BFA3486CB6E595A88975673A0283
consumer       4F47C460520C40ACE1B8CFD21A5677204DE2BDCB51D0675B5635E46154858475
generated API  07351DE378A0FA20C711AC5B7C62A01D21598A619B3D9EC58DC3BFDDE36719E2
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

- full `lake build`: 504/504 jobs;
- Lean source audit: zero actual `sorry`/`admit` findings across 238 Lean
  files;
- generated API reference: current at 59 sections and 1,610 declarations;
- the runnable external-temporal-outcome consumer destructured all three
  carrier cases, exercised the forgetful theorem and both typed-step
  reductions, and
  emitted exactly
  `active-top debt external parent temporal outcome: kernel-green`;
- public theorem audit: 959 entries total: 668 full-classical, 25
  axiom-free, 128 `propext`-only, and 138 `propext` plus `Quot.sound`;
- the default, extended, and cross-variant progress audits passed with every
  incomplete visited state carrying an exact ready head and successful
  dispatch, every dispatch-none stop fully marked, and zero missing-head,
  incomplete-dispatch-none, cycle, or truncation findings;
- facade, generated API, consumer, and axiom-audit entry points passed under
  the checkpoint's trust-zero and warnings-as-errors gates.

Exact-head proof GitHub verification:

- workflow: `Lean CI`;
- event/ref: `push` / `main`;
- run: [32341704666](https://github.com/fushanbobfan/proofnet-ir/actions/runs/32341704666);
- build job: [96341955337][proof-job];
- exact head: `c56dfce2c015b57106b931edf7538be7c7c2d95b`;
- result: 36 successful steps, zero failures, and one expected release-ref-only
  skip;
- run: `2026-08-20T06:56:06Z`-`2026-08-20T07:09:22Z` (13m16s);
- build job: `2026-08-20T06:56:09Z`-`2026-08-20T07:09:22Z`
  (13m13s).

[proof-job]: https://github.com/fushanbobfan/proofnet-ir/actions/runs/32341704666/job/96341955337

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

1. derive a first-reentry or ownership law for the external raw or strictly
   older temporal outcome, or derive a distinct active ready-tail payer
   directly; then derive the remaining global-created Forward/UnifyPayload
   alternatives;
   equivalently, prove that correctness plus `CanonicalTagHistory` implies
   `ActiveTopDebtTailLaw`. Only after that gate may endpoint debt combine with
   active-top drainedness and marking incompleteness in an unconditional
   progress argument. The unrestricted `ActiveTopContinuationExitLocalized`
   law remains refuted after every supplied successful typed Wait from a
   scheduler-invariant input, so it cannot replace the tail law. Reachable Wait
   existence, post-Wait drainedness, unconditional `allMarked`, progress,
   completion, terminality, later-state totality, and arbitrary history
   existence remain open;
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
