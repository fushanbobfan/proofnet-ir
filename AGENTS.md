# Agent notes

Start with [docs/current-status.md](docs/current-status.md) (revision,
verification receipts, open gates) and [docs/goal-ledger.md](docs/goal-ledger.md)
(every claim with its evidence). Development commands and gates are in
[CONTRIBUTING.md](CONTRIBUTING.md); `.github/workflows/ci.yml` is
authoritative. The Lean-scale continuation, and the handoff notes of
2026-09-22 covering both repositories, are in
[proof-graphs](https://github.com/fushanbobfan/proof-graphs) (`HANDOFF.md`).

- `warningAsError` is on: a warning is a failed gate. Public declarations
  carry docstrings.
- Before pushing: `lake build`, the `--trust=0` recheck of touched modules,
  `python scripts/audit_axioms.py`, `lake exe proofnet_ir_api_docs --check`,
  and `python scripts/check_convergence.py --base origin/main --head HEAD`
  (line caps on maintained prose, at most one new module per change, a new
  public theorem named in one prose home only).
- Experiments under `experiments/` are preregistered and frozen: changes go
  through amendment files, and each experiment has a `--check-committed`
  that CI runs.
- Release tags are never moved and history is never rewritten. Commit
  subjects state the change in one line, with no tool or assistant
  attribution.
