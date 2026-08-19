# README information-architecture relocation ledger

This ledger records the zero-loss reorganization of the historical monolithic
README. It is an audit artifact for the documentation-only change, not a new
rolling research log.

Source baseline:

```text
commit       5e59d120d55fa1f2125b0edc37c374dda3739642
README blob  0ffaf22c
lines        2695
words        22079
```

## Ownership rule

| Information | Canonical owner |
| --- | --- |
| Project entry, quick use, stable/current distinction, navigation | `README.md` |
| One rolling mathematics checkpoint and receipt | `docs/current-status.md` |
| Historical checkpoints | `CHANGELOG.md` |
| Active proof plan and rejected routes | `docs/v0.10-design.md` |
| Stable module and data-flow architecture | `docs/architecture.md` |
| Trust and logical dependency boundary | `docs/trust-model.md` |
| Maturity and reuse limits | `docs/library-readiness-audit.md` |
| Generated declarations | `docs/api-reference.md` |
| Wire/API compatibility and migrations | `docs/compatibility.md` |
| Developer commands and contribution workflow | `CONTRIBUTING.md` |
| Literature inventory and reading state | `docs/reading-ledger.md` |
| Claim-to-source correspondence | `docs/source-coverage-audit.md` |
| Research/release sequence | `docs/roadmap.md` |

## Complete range relocation

Line numbers below refer to the source baseline above.

| Old README lines | Subject | Destination after reorganization |
| ---: | --- | --- |
| 1–12 | Identity and stable release banner | Compressed in README; full guarantee in `docs/v0.9-release-audit.md` |
| 14–93 | Closing-core endpoint replay and the flat token-age counterexample | Proof design in `docs/v0.10-design.md`; checkpoint history in CHANGELOG |
| 95–232 | Delayed Figure-7 New/Unify/enabledness/dispatcher/progress layers | Stable structure in architecture; proof plan in v0.10 design; chronology in CHANGELOG |
| 233–438 | Fresh capacity, queue history, blockers, source-left and reservation geometry | Architecture and v0.10 design; historical introductions in CHANGELOG |
| 439–769 | Cross-representative invariants, touch order, advance, rule preservation, queued-head availability | Architecture/v0.10 design; checkpoint sequence in CHANGELOG |
| 770–927 | Priority/NewEnabled, finite audits, tag/raw/history state | Current conclusion and receipt in current-status; limits in readiness/performance; history in CHANGELOG |
| 929–1056 | Local direct/executable rules and production primitives | Architecture, v0.10 design, and generated API reference |
| 1058–1160 | NEXTAXIOM, routes, delayed state, initialization, and reservation bridge | Architecture and v0.10 design |
| 1162–1335 | Reservation/Scheduler invariants, component provenance, and exact operational-New regression | Architecture, trust model, readiness audit, and v0.10 design |
| 1337–1670 | Flat-worklist proof chain, counterexamples, and rejected routes | v0.10 design, CHANGELOG, performance, and readiness audit |
| 1671–1743 | Maximality state and open gates | Full current record in current-status; bounded derived summary in README |
| 1745–1793 | Stable v0.9 compact criterion and hybrid guarantees | Compact stable summary in README; details in release audit, architecture, and performance |
| 1795–1799 | v0.8 historical state | CHANGELOG and frozen v0.8 release audit |
| 1801–1805 | Research hypothesis and kernel trust | Retained in the README's motivation and trust sections |
| 1807–1843 | Stable checker and graph capabilities | Stable guarantee summary in README; architecture/API for detail |
| 1844–2060 | Rolling worklist and scheduler theorem inventory | Current-status, architecture, v0.10 design, and CHANGELOG |
| 2061–2195 | Stable reconstruction, canonicalization, parsing, and runtime APIs | README API tour, tutorial, compatibility, architecture, and generated API |
| 2196–2225 | Experimental LeanProp bridge | Architecture, trust model, compatibility, and v0.6 release audit |
| 2227–2249 | Public axiom/audit totals | Current-status and trust model; removed from README |
| 2251–2265 | Maturity and scope limits | Short README non-goals; full readiness audit |
| 2267–2306 | Trust path and checked parser example | Short README trust diagram; trust model and tutorial for detail |
| 2307–2395 | Development commands and Windows 4551 fallback | CONTRIBUTING; `lakefile.toml`/CI remain executable authorities |
| 2396–2629 | Hand-maintained repository/module map | README directory map; architecture for concepts; CONTRIBUTING for discovery |
| 2630–2641 | Deterministic matched experiment | README qualified headline; frozen report and experiment protocol |
| 2643–2659 | Amended model experiment | README link; frozen report, performance, and CHANGELOG |
| 2661–2691 | Documentation links | Rebuilt as the README documentation map |
| 2693–2695 | License | Retained in README |

## Stale inventories deliberately retired

The old README's command matrix and source map were already incomplete at the
source baseline. They omitted the newest Maximality executable, module, and
consumer, and the source map covered only a subset of tracked Lean files.

They were not copied into another static list. Instead:

- `lakefile.toml` owns executable/default target registration;
- `.github/workflows/ci.yml` owns CI execution order;
- `ProofNetIR.lean` owns the public import graph;
- `ProofNetIRAPIDocs.lean` owns generated public API selection;
- `ProofNetIRAxiomAudit.lean` and `scripts/audit_axioms.py` own trust coverage;
- architecture explains layers without pretending to be an exhaustive file
  listing;
- CONTRIBUTING documents how to discover the exact current registries.

This replacement preserves the useful information while removing a known
source of drift.

## Claim locks

The reorganization is valid only while all of these remain explicit:

- stable v0.9.0 covers the documented unit-free, cut-free MLL model;
- general accepted-certificate sequentialization remains complete through the
  recursive fallback;
- canonical identity preserves ordered conclusions under its explicit
  equivalence, not arbitrary graph isomorphism;
- the rolling Maximality result is an inclusive path-or-equal-stored-left-
  callback-failure alternative;
- callback failure does not imply that an avoiding path is absent;
- queue origin, mate-region/global raw-mark availability, created-candidate raw
  seams, reachable enabledness, progress, pure-worklist completeness, fallback
  removal, token-age scheduling, and whole-program linearity remain open;
- deterministic and model experiment figures retain their task-specific
  limitations;
- the project remains a research library without an external-adoption or
  independent-validation claim;
- agent-assisted development provenance remains explicit.

## Acceptance contract

The documentation-only change must satisfy:

1. only `README.md`, `CONTRIBUTING.md`, `CHANGELOG.md`, and Markdown below
   `docs/` may differ from the proof baseline;
2. generated `docs/api-reference.md` is not hand-edited;
3. README remains between 400 and 600 lines;
4. its marked rolling-main summary contains 5–20 nonempty content lines;
5. README contains no rolling SHA, CI job history, axiom-count receipt, or
   exhaustive theorem/module/test inventory;
6. current-status names exactly one proof checkpoint and treats a later
   documentation commit as a descendant, not a new mathematics checkpoint;
7. every relative Markdown link resolves;
8. the stable/current/open-gate distinctions above survive review;
9. `git diff --check` passes;
10. the generated API drift check remains current.

The relocation ledger itself is documentation infrastructure. Future ordinary
proof checkpoints should update current-status in place and should not append
new rows here unless the information architecture changes again.
