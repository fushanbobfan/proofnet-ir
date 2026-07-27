# Guerrini unification implementation audit

## Source and scope

This audit uses Stefano Guerrini, *Correctness of Multiplicative Proof Nets is
Linear* (LICS 1999), ten pages, downloaded from the primary paper record on
2026-07-23. The local audit copy has SHA-256
`47c2b9fe82c73db3bcbb5c0dab183cb2130c9c446a1ae0f9c72fe59e53cbb149`.
The complete extracted text and all eight figures were inspected. The paper is
supplemental primary literature; it was not one of the seven original PDFs
placed in the parent knowledge folder.

The paper treats multiplicative proof structures without constants and also
allows cuts through a dummy-link encoding. ProofNet-IR v0.9 currently
formalizes only the cut-free, unit-free fragment, so dummy links and cut
handling are outside the implemented state machine.

## Exact link mapping

Guerrini's abstract link classes map to the current certificate syntax as
follows:

| Guerrini link | Switching behavior | ProofNet-IR link |
|---|---|---|
| axiom | edge between its two conclusions | `Link.axiom` |
| unary | retain one premise-to-conclusion edge | `Link.par` |
| binary | retain both premise-to-conclusion edges | `Link.tensor` |
| dummy | no switching edge; represents a cut target | unsupported |

Figure 5 gives three unification rules:

1. `start`: assign a fresh token to both conclusions of an unmarked axiom;
2. `forward`: fire a unary/par link only when both premises yield the same
   current token class, then mark its conclusion with that class;
3. `unify`: fire a binary/tensor link only when its premises yield distinct
   token classes, merge those classes, then mark its conclusion.

An armed binary link whose premises already yield the same token is a
permanent deadlock. An armed unary link whose premises yield different tokens
waits because a later binary merge can make it ready. Definition 11 and
Proposition 12 characterize correctness by a total marking whose partition has
one thread. Proposition 15 and Theorem 16 concern the more disciplined
sequential strategy of Figures 7 and 8 and its linear implementation.

## What the code implements

`ProofNetIR/Unification.lean` implements a deterministic, eager-start
unification pass:

- all axiom threads are initialized;
- connective links are scanned left to right;
- ready par and tensor links fire according to Figure 5;
- scans repeat until no progress or the link-count fuel is exhausted;
- every token class carries a partial `CutFreeDerivation` and exact occurrence
  frontier;
- a successful single component is exchanged to the submitted ordered
  conclusion boundary.

The generated tree is not trusted. `unificationReconstruct?` submits it to the
independent `verifyDerivation?` boundary, which rechecks structural
well-formedness, formula inference, desequentialization, and intrinsic
`ProofNetEquivalent` identity.

Library callers can use the detailed `unificationDerivationCandidate` and
`unificationReconstruct` forms to receive a stable `UnificationErrorCode`,
message, and input counts. Except for `malformedInput`, these diagnostics mean
that the deterministic tier did not produce a verified result; they are not
logical rejections. The `?` forms are convenience wrappers.

The corresponding `WithStats` forms retain exact eager-scan counters. Their
result type contains proof fields
`passes ≤ |links|` and `linkVisits = passes * |links|`; the public axiom-free
theorem `UnificationCandidateResult.linkVisitsBound` derives the scoped
quadratic link-visit bound. This is not a total runtime theorem: frontier
lookup, representative traversal, independent verification, and fallback are
outside the counter.

An event-driven prototype now precomputes which links consume each occurrence.
It initially enqueues connectives once, enqueues only consumers of newly
marked conclusions, stores armed unequal-token pars in a deduplicated waiting
set, and requeues that set after a tensor union. Candidates still cross
`verifyDerivation?`. Lean proves worklist fast-path soundness, its fallback
wrapper equal to `check`, and a conservative `n(n+4)+1` link-attempt cap.
Current `main` additionally proves that structural single-consumer ownership,
distinct successful firings, and the bounded waiting registry keep all
successful insertions within that cap, and exact insertion/pop accounting
forces the canonical final queue to be empty. Scheduler coverage then gives an
exact witness for every submitted but unfired connective in that quiescent
state: an idle premise, a distinct-thread registered par, or a same-thread
tensor deadlock.
Selecting an unassigned conclusion of least formula complexity now refines
that result. Structural well-formedness recovers its concrete source link,
strict premise complexity makes both premises assigned, and the remaining
witness is therefore an exact submitted distinct-thread waiting par or
same-thread tensor deadlock. The abstract semantics now proves that every
semantic thread stays connected inside the active all-left reference
subgraph, and that invariant is transported through the concrete canonical
worklist run. Declarative reference-switching acyclicity then excludes the
same-thread tensor branch: its two fixed edges would close the active thread
path into an edge-simple cycle. The only remaining correct-state obstruction
is an exact distinct-thread waiting par. The converse direction is now also
kernel checked. Every reachable marking is causally closed, each active
retained reference edge stays inside one semantic thread, and therefore an
active reference walk between marked occurrences exists exactly when their
raw tokens share one union-find class. The two premises of the remaining
waiting par are consequently proved to have no active reference walk between
them. Exact occurrence-aware tree-edge exchange now flips only that submitted
par and constructs a reference simple path between its premises which avoids
the par conclusion. The absence of an active walk therefore yields a concrete
unmarked internal occurrence on this path, distinct from both premises and
the conclusion. The current first-frontier theorem strengthens this to an
exact retained edge occurrence directed from a marked source into an unmarked
target, together with an entirely active prefix. Exact active-component/thread
correspondence proves that this source carries the waiting par's left token.
Reading the path backward selects the last inactive frontier and proves that
its marked target carries the right-premise token. The two distinct boundary
occurrences form one exact ordered decomposition of the reference path.
Exact retained-edge/source-link lookup, completed axiom
initialization, and causal closure classify that occurrence as a forward
premise-to-conclusion edge of a concrete submitted par or tensor. Quiescent
scheduler coverage now refines the par case to either an unassigned omitted
premise or two distinct registered tokens, and refines the tensor case to an
unassigned opposite premise after excluding the same-thread deadlock. This
classification now holds at both sides of the bracketed region. What remains
is narrower still: cutting at the first unmarked-to-marked reentry proves
that every intervening path occurrence has two unmarked endpoints, while both
boundary orientations retain exact scheduler classifications. The global
progress argument now also retains the globally minimum-complexity unassigned
waiting conclusion. Strict premise descent normalizes each boundary to a
target rank above that minimum or another exact registered distinct-thread
par. The general chase now retains a composable proof object containing the
exact submitted source connective and selected premise at every downward
step, rather than discarding the structural route after deriving its endpoint
rank. Iterating the resulting dependency on the finite formula carrier
produces a concrete nonempty closed segment. Every structural step is now
lifted to the exact full occurrence-graph edge from connective conclusion to
selected premise. Nontrivial chases compose into vertex-simple paths whose
edges are all traversed backward and whose internal turns are consequently
cusp-free. A state-indexed reachability witness retains that every visited
formula occurrence remains unassigned. The scheduler frontier is also lifted
occurrence-exactly, and the first nontrivial chase edge is proved not to
reverse it immediately. An exact-index classifier for the deterministic mask
now distinguishes the retained axiom, tensor, and left-par occurrences
without quotienting parallel edge values. Structural typing excludes the
axiom case at a formula tail, and unique producer ownership synchronizes the
frontier producer with the first tail producer. Thus each nontrivial turn is
proved to be a genuine par cusp or a tensor-colored free turn. Every dependency
is now also packaged as a composable complete-graph segment from its source
waiting conclusion to its target, using the exact source-par incidence,
retained reference-prefix lift, and all-backward formula tail. The finite
closed dependency family is kernel-concatenated into a genuinely nonempty
closed occurrence-aware `fullGraph` walk. Any adjacent-segment reverse pair is
now tied to the exact retained reflexive frontier occurrence and the same
stored full-edge index is proved to annotate the next waiting par. A generic
exact-occurrence cancellation lemma and its dependency-level specialization
remove one such pair while preserving the endpoints, all remaining
occurrences, and the nesting witness. A terminating exact-occurrence
normalization now repeatedly cancels internal pairs and rotates a reversing
last/first pair. It reduces the nonempty dependency obstruction to a closed
walk that is either empty or cyclically nonbacktracking, with every surviving
occurrence inherited from the original walk. The empty branch is not an
artifact: nested out-and-back tree walks genuinely normalize away. The
normalizer now retains a proof-relevant tree of every internal cancellation
and rotated closing cancellation. Lean proves that, for every directed-edge
value represented in an empty-normalizing dependency obstruction, the reverse
orientation of the same stored edge also occurs there. This is exact-index
membership, not yet a bijection between list positions. The scheduler-level
theorem exposes that trace and membership result directly. Segment
classification also proves every forward-oriented occurrence in the
concatenated obstruction is retained by the all-left reference switching.
Consequently, an empty normal form forces every original edge index to be
reference-retained: a backward occurrence inherits retention from its
forward reverse. The scheduler theorem now transports the original nonempty
closed exact-occurrence walk into the deterministic reference switching, and
the public `DeclarativelyCorrect.referenceSwitchingTree` theorem packages that
graph's `IsTree` proof. This reduces the empty branch to a fully retained nested
reference-tree walk but does not by itself rule that walk out: nested
backtracking remains possible in a tree. The nonempty branch is sharper too:
exact masking preserves cyclic nonbacktracking, every valid occurrence
switching is proved a tree, and par-pair sparsity would place the entire
obstruction in one such switching. Lean therefore extracts a concrete par whose
two exact premise occurrences survive and uses all-left forward retention to
prove that its omitted right occurrence is traversed backward. The remaining
empty branch now exposes an exact internal-or-closing cancellation site in the
original traversal. Lean proves cyclically nonbacktracking inputs are fixed by
normalization and proves that an internal cancellation in an append of two
individually nonbacktracking pieces must cross their unique junction. The
selected dependency-segment decomposition is now retained as an indexed finite
family with every segment's scheduler endpoint classifications. Lean localizes
the site to an adjacent or cyclic junction and proves that its incoming
occurrence is simultaneously the preceding dependency's retained reflexive
end and the following waiting par's stored left incidence. Each dependency now
also retains its exact first marked-to-unmarked frontier and proves every
preceding path endpoint assigned. Thus any forward occurrence entering an
unassigned vertex is exactly that frontier. Structural producer uniqueness and
the registered waiting-par premises force a frontier entering another waiting
par to be reflexive, with no nontrivial formula-premise tail. In the fully
cancelling simple cycle, Lean pairs every source reverse with the unique cyclic
predecessor's exact last occurrence and proves every segment ends at its
reflexive frontier. The remaining argument must exclude the resulting
multi-node cycle of retained reference paths and waiting-par incidences and
transport turn classifications around the concrete nonempty obstruction into
an excluded edge-simple switching cycle or forbidden nesting in a correct
quiescent state.

This prototype is not the sequential strategy of Figures 7--8. It starts all
axioms eagerly, uses a flat waiting set, and has no `NEXTAXIOM`, token-age
stack, interval partition, or specialized union-find invariant. The attempt
cap is no longer merely imposed by fuel: its scheduler sufficiency is proved.
That result now rules out tensor deadlock on a correct nonfinal net and
identifies the remaining waiting par as an exact active-component separation;
the separation is now localized to a conclusion-avoiding reference path with
a genuine unmarked internal occurrence, and every subsequent formula chase
retains all exact connective/premise steps through its terminal waiting par.
The global correct-state progress theorem remains open.

Lean currently proves:

```text
unificationReconstruct? = some result → check = true
unificationFastCheck = true → check = true
unificationCheck = check
unificationCheck = true ↔ DeclarativelyCorrect
```

The default exact decision tries the event-driven worklist, then the eager
scan, then the already complete checker-free recursive sequentializer. None of
those branches enumerates switching graphs.

## What is not yet proved

The following stronger claims are intentionally absent:

- `unificationFastCheck = check`;
- completeness or confluence of the eager repeated-scan schedule;
- a polynomial, quasi-linear, or linear bound for the hybrid
  `unificationCheck`;
- a polynomial bound for the complete candidate-plus-verifier execution; the
  current proved quadratic statement counts eager link-list visits only;
- equivalence between this eager implementation and the sequential stack,
  waiting-set, `NEXTAXIOM`, and special union-find algorithm in Figures 7--8;
- support for cuts, dummy links, units, Mix, additives, or exponentials.

The current repeated scan can take a quadratic number of link visits before
independent derivation verification. A fast-path miss invokes the exhaustive
recursive fallback. Therefore citing Guerrini's Theorem 16 as a complexity
theorem for the present executable would be incorrect.

## Differential evidence

`proofnet_ir_unification_audit` checks 1,500 deterministic certificates:

- 250 derivation-generated positives;
- their 250 reversed-link variants;
- their 250 reversed-boundary variants;
- 750 malformed missing-link, duplicate-link, or invalid-axiom mutations.

It additionally checks a structurally well-formed but disconnected
two-axiom sentinel and requires the stable `nonUniqueThread` diagnostic. The
first recorded Windows run reported 750/750 positive fast-path hits, zero
positive misses, zero false positives, and exact hybrid/reference agreement.
This is regression evidence, not the missing fast-path completeness theorem.
The main 291-case performance workload and the 18-case repeated-label stress
suite also require the deterministic fast path to return a proof-bearing
result.

A second positive-only counterexample search now covers 7,200 reordered
derivation-generated certificates from 1,200 seeds, depths zero through seven,
up to 447 formula occurrences and 319 links. It observed no fast-path miss in
the current recorded run. The source theorem
`CutFreeDerivation.desequentialize?_check` establishes acceptance of each base
certificate; the order variants preserve the same occurrences and links.
This finite search is intentionally kept separate from the universal
completeness theorem.

The same two gates now also require the event-driven worklist. They observed
750/750 and 7,200/7,200 worklist hits, respectively, with zero false positives
or positive misses. The larger search recorded at most 995 link attempts and
691 waiting requeues. These remain finite regression results.

## Remaining formalization route

1. State the operational one-step relation independently of the executable
   scan and prove that every fired component denotes the corresponding parsing
   substructure.
2. Use full-switching connectivity plus causal closure to exclude the
   unmarked internal region now exposed on the exact reference path between
   the remaining waiting par premises; same-thread tensor deadlock is already
   excluded by the active-path switching-cycle theorem. Exact retained-edge
   transport, par-cusp/tensor-free boundary classification, composable
   dependency segments, a nonempty closed `fullGraph` walk, internal
   nonbacktracking of every individual segment, the fact that any inter-segment
   immediate reversal forces a reflexive preceding formula chase, the exact
   retained-frontier/next-waiting-par occurrence binding, one-step
   occurrence-preserving cancellation, and terminating internal-plus-cyclic
   normalization to an empty or cyclically nonbacktracking closed walk are now
   proved. The exact first frontier and its assigned prefix are now retained;
   a frontier entering a registered waiting par is proved reflexive; and every
   segment of the fully cancelling simple cycle is paired with its unique
   cyclic predecessor and ends reflexively. The occurrence-indexed segment
   witness is now preserved through that family: deleting each exact
   source/frontier pair gives a deterministic residual core whose endpoints
   share a live token, whose successor incidence is exact, and whose every
   edge has assigned endpoints before the first inactive frontier. Each core
   is now also kernel-proved nonempty: otherwise adjacent waiting pars would
   consume one exact premise and structural one-parent ownership would collapse
   two distinct simple-cycle nodes. Removing the exact source/frontier
   boundaries preserves no-immediate-reverse, so the deterministic active
   family now consists of nonempty internally nonbacktracking cores. Those
   indexed cores are now composed into a nonempty closed full-graph walk whose
   last endpoint returns to the first core's exact source-premise base. Every
   core occurrence is reference-kept, so a nonempty cyclically nonbacktracking
   normal form would contradict the reference switching tree. The core-only
   walk is now proved to normalize to empty, with an exact reversal localized
   to a cyclic junction between two nonempty internally reduced cores. That
   cyclic witness is now reindexed to one exact dependency step and reconciled
   with both complete segment decompositions. The two consecutive segments
   contain the exact contiguous word
   `inner, outer, outer.reverse, inner.reverse`, and segment
   nonbacktracking proves the two layers do not degenerate into one pair. Both
   original full-segment witnesses are now retained at that indexed step.
   Each `core ++ frontier` is pointwise aligned with its exact reference-
   switching prefix, and the successor prefix is proved to start with the
   inner occurrence's exact reverse. The exact multi-par flip is now local and
   compositional: every reflexive dependency has a vertex-simple
   backward-right-par/reversed-strict-suffix replacement which avoids the
   target waiting par's exact retained left occurrence. The replacements form
   a nonempty closed cyclically nonbacktracking full-graph walk, and Lean proves
   all internal, adjacent-segment, and closing transitions cusp-free. The
   immediate proof obligation is now the global repeated-vertex/nesting
   argument: ordinary loop erasure is insufficient because it can create a
   new closing cusp by re-pairing incidences at the erased vertex. In the
   nonempty branch, the proof must still
   transport the turn evidence into an excluded edge-simple switching cycle or
   forbidden nesting.
3. Prove the deterministic schedule complete, yielding
   `unificationFastCheck = check` and removing the recursive fallback.
4. Replace eager axiom starts and flat waiting requeues with the Figure-7 stack
   discipline; the current flat scheduler's fuel is already proved sufficient.
5. Only after `NEXTAXIOM`, token-age, waiting-stack, and union-find invariants are
   formalized should the library expose a Guerrini-linear complexity theorem.
