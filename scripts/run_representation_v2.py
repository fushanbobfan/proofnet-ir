#!/usr/bin/env python3
"""Representation-as-target model study v0.2: stable identifiers, grammar constraints, generous budget.

  python scripts/run_representation_v2.py --self-test
  python scripts/run_representation_v2.py --pilot
  python scripts/run_representation_v2.py --register
  python scripts/run_representation_v2.py --run
  python scripts/run_representation_v2.py --check-committed

The model, the corpus, and the decoding settings are representation-v0.1's, with three changes that separate
the representation from the conditions around it: every answer is decoded under a grammar that admits only
its arm's JSON shapes, the budget is 8,192 completion tokens instead of 1,024, and a third arm writes the
derivation over stable subformula labels instead of positions that shift after every rule. Arms:

- `proof`: representation-v0.1's position-based derivation, prompt and rendering unchanged;
- `proofIds`: the same derivations over labels (atoms a0, a1, ..., connectives c0, c1, ... in reading order),
  converted to the position format before Lean verifies them;
- `net`: representation-v0.1's axiom linking, prompt and rendering unchanged.

Every proposal is verified by `proofnet_ir_representation_verify`, as in v0.1. `--self-test` checks the label
conversion on hand-made derivations with Lean; `--pilot` runs development sequents only.
"""

from __future__ import annotations

import argparse
import copy
import json
import math
import statistics
import subprocess
import sys
import time
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_representation_study as v1  # noqa: E402

ROOT = v1.ROOT
EXPERIMENT = ROOT / "experiments" / "representation-v0.2"
PREREG = EXPERIMENT / "preregistration.json"
RESPONSES = EXPERIMENT / "raw-responses.jsonl"
RESULTS = EXPERIMENT / "results.jsonl"
SUMMARY = EXPERIMENT / "summary.json"
REPORT = EXPERIMENT / "report.md"
IMPLEMENTATIONS = {
    "verifier": ROOT / "ProofNetIRRepresentationVerify.lean",
    "v01Runner": ROOT / "scripts" / "run_representation_study.py",
    "runner": ROOT / "scripts" / "run_representation_v2.py",
}
MODEL_MAX_TOKENS = 8192
MODEL_TIMEOUT_SECONDS = 1800
ARMS = ("proof", "proofIds", "net")
CUTOFFS = (64, 128, 256, 512, 1024, 2048, 4096, 8192)

PROOF_IDS_SYSTEM = (
    "You prove one-sided sequents of unit-free, cut-free multiplicative linear logic (MLL). "
    "Formulas are atoms with a sign (a+ is the atom, a- its dual), tensors (A ⊗ B), and pars (A ⅋ B). "
    "Every subformula carries a fixed label: atoms a0, a1, ... and connectives c0, c1, ..., and a sequent is a set "
    "of labels. A proof is a tree of rule applications, written top-down from the goal sequent. Rules: axiom closes "
    "a sequent that is exactly two dual atoms (same name, opposite sign); par on the label of a par A ⅋ B in the "
    "sequent replaces it by the labels of A and B; tensor on the label of a tensor A ⊗ B in the sequent lists the "
    "labels of the OTHER formulas that go with A (the rest go with B); the left premise is A with the listed "
    "formulas, the right premise is B with the rest. Every premise is itself a proof object, never a list of "
    "formulas. Reply with one JSON object and no prose, using exactly these shapes: "
    '{"rule":"axiom"} | {"rule":"par","on":LABEL,"premise":PROOF} | '
    '{"rule":"tensor","on":LABEL,"left":[labels],"leftPremise":PROOF,"rightPremise":PROOF} | {"rule":"unprovable"}. '
    "Example. Sequent: c0:(a0:a+ ⊗ a1:b+), c1:(a2:a- ⅋ a3:b-). Proof: "
    '{"rule":"par","on":"c1","premise":{"rule":"tensor","on":"c0","left":["a2"],"leftPremise":{"rule":"axiom"},'
    '"rightPremise":{"rule":"axiom"}}} '
    "(after the par the sequent is c0, a2, a3; the tensor sends a2 with a0 and a3 with a1; both premises are axioms)."
)

GRAMMARS = {
    "proof": r'''root ::= proof | "{\"rule\":\"unprovable\"}"
proof ::= "{\"rule\":\"axiom\"}" | "{\"rule\":\"par\",\"at\":" num ",\"premise\":" proof "}" | "{\"rule\":\"tensor\",\"at\":" num ",\"left\":[" nums "],\"leftPremise\":" proof ",\"rightPremise\":" proof "}"
nums ::= (num ("," num)*)?
num ::= [0-9] | [1-9] [0-9]+
''',
    "proofIds": r'''root ::= proof | "{\"rule\":\"unprovable\"}"
proof ::= "{\"rule\":\"axiom\"}" | "{\"rule\":\"par\",\"on\":" label ",\"premise\":" proof "}" | "{\"rule\":\"tensor\",\"on\":" label ",\"left\":[" labels "],\"leftPremise\":" proof ",\"rightPremise\":" proof "}"
labels ::= (label ("," label)*)?
label ::= "\"" [ac] ([0-9] | [1-9] [0-9]+) "\""
''',
    "net": r'''root ::= "{\"pairs\":[" pair ("," pair)* "]}" | "{\"unprovable\":true}"
pair ::= "[" num "," num "]"
num ::= [0-9] | [1-9] [0-9]+
''',
}


# Labelled rendering and conversion to positions

def label_tree(formula: dict[str, Any], counters: list[int]) -> dict[str, Any]:
    """A copy of the formula with a `label` on every node: atoms a0, a1, ... and connectives c0, c1, ... in
    reading order (the atoms' numbers are the net rendering's occurrence numbers)."""
    if formula["kind"] == "atom":
        out = dict(formula, label=f"a{counters[0]}")
        counters[0] += 1
        return out
    out = {"kind": formula["kind"], "label": f"c{counters[1]}"}
    counters[1] += 1
    out["left"] = label_tree(formula["left"], counters)
    out["right"] = label_tree(formula["right"], counters)
    return out


def labelled(sequent: list[dict[str, Any]]) -> list[dict[str, Any]]:
    counters = [0, 0]
    return [label_tree(f, counters) for f in sequent]


def render_labelled_formula(formula: dict[str, Any]) -> str:
    if formula["kind"] == "atom":
        return f"{formula['label']}:{formula['name']}{'+' if formula['positive'] else '-'}"
    symbol = "⊗" if formula["kind"] == "tensor" else "⅋"
    return (f"{formula['label']}:({render_labelled_formula(formula['left'])} {symbol} "
            f"{render_labelled_formula(formula['right'])})")


def render_ids(sequent: list[dict[str, Any]]) -> str:
    return ("Sequent, one formula per line, every subformula labelled:\n"
            + "\n".join(render_labelled_formula(f) for f in labelled(sequent)))


def to_positions(proposal: Any, sequent: list[dict[str, Any]]) -> dict[str, Any]:
    """The labelled derivation in representation-v0.1's position format; ValueError names the first rule that
    does not apply."""
    nodes: dict[str, dict[str, Any]] = {}

    def index(formula: dict[str, Any]) -> None:
        nodes[formula["label"]] = formula
        if formula["kind"] != "atom":
            index(formula["left"])
            index(formula["right"])
    top = labelled(sequent)
    for f in top:
        index(f)

    def convert(proof: Any, current: list[str]) -> dict[str, Any]:
        if not isinstance(proof, dict):
            raise ValueError("a premise is not a proof object")
        rule = proof.get("rule")
        if rule == "axiom":
            return {"rule": "axiom"}
        label = proof.get("on")
        if label not in current:
            raise ValueError(f"{rule} on {label!r}, which is not in the sequent")
        at = current.index(label)
        node = nodes[label]
        if rule == "par":
            if node["kind"] != "par":
                raise ValueError(f"par on {label}, which is not a par")
            rest = current[:at] + [node["left"]["label"], node["right"]["label"]] + current[at + 1:]
            return {"rule": "par", "at": at, "premise": convert(proof.get("premise"), rest)}
        if rule == "tensor":
            if node["kind"] != "tensor":
                raise ValueError(f"tensor on {label}, which is not a tensor")
            chosen = proof.get("left")
            if not isinstance(chosen, list) or any(c not in current or c == label for c in chosen) \
                    or len(set(chosen)) != len(chosen):
                raise ValueError(f"tensor on {label} lists formulas not in the sequent")
            others = [c for c in current if c != label]
            left = [c for c in others if c in chosen]
            right = [c for c in others if c not in chosen]
            return {"rule": "tensor", "at": at, "left": [current.index(c) for c in left],
                    "leftPremise": convert(proof.get("leftPremise"), [node["left"]["label"]] + left),
                    "rightPremise": convert(proof.get("rightPremise"), [node["right"]["label"]] + right)}
        raise ValueError(f"unknown rule {rule!r}")

    return convert(proposal, [f["label"] for f in top])


# Model calls

def request_body(sequent: list[dict[str, Any]], arm: str) -> dict[str, Any]:
    system = {"proof": v1.PROOF_SYSTEM, "proofIds": PROOF_IDS_SYSTEM, "net": v1.NET_SYSTEM}[arm]
    user = render_ids(sequent) if arm == "proofIds" else v1.render_task(sequent)
    return {"model": v1.MODEL_ID, "messages": [{"role": "system", "content": system},
                                               {"role": "user", "content": user}],
            "temperature": 0, "seed": v1.MODEL_SEED, "max_tokens": MODEL_MAX_TOKENS,
            "chat_template_kwargs": {"enable_thinking": False}, "grammar": GRAMMARS[arm]}


def call_model(task: dict[str, Any], arm: str) -> dict[str, Any]:
    body = request_body(task["sequent"], arm)
    encoded = json.dumps(body, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    request = urllib.request.Request(v1.MODEL_ENDPOINT, data=encoded, headers={"Content-Type": "application/json"},
                                     method="POST")
    started = time.perf_counter_ns()
    try:
        with urllib.request.urlopen(request, timeout=MODEL_TIMEOUT_SECONDS) as response:
            result = json.loads(response.read().decode("utf-8"))
        if isinstance(result, dict) and "model" in result:
            result["model"] = v1.MODEL_ID
        error = None
    except (urllib.error.URLError, TimeoutError, json.JSONDecodeError) as exception:
        result, error = None, f"{type(exception).__name__}: {exception}"
    return {"id": task["id"], "arm": arm, "requestSha256": v1.sha256_text(encoded.decode("utf-8")),
            "elapsedMs": (time.perf_counter_ns() - started) / 1_000_000, "error": error, "response": result}


def finish_reason(response: dict[str, Any] | None) -> str | None:
    try:
        return response["choices"][0].get("finish_reason")  # type: ignore[index]
    except (KeyError, IndexError, TypeError):
        return None


# Evaluation

def evaluate(tasks: list[dict[str, Any]], responses: dict[tuple[str, str], dict[str, Any]]) -> list[dict[str, Any]]:
    rows = []
    for task in tasks:
        for arm in ARMS:
            response = responses[(task["id"], arm)]
            claim, proposal, tokens = v1.classify(response["response"])
            row = {"id": task["id"], "arm": arm, "stratum": v1.stratum(task), "sequent": task["sequent"],
                   "expectedProvable": task["expectedProvable"], "claim": claim, "proposal": proposal,
                   "completionTokens": tokens, "finishReason": finish_reason(response["response"]),
                   "elapsedMs": response["elapsedMs"], "error": response["error"], "conversion": None}
            if arm == "proofIds" and claim == "provable":
                try:
                    row["converted"] = to_positions(proposal, task["sequent"])
                except ValueError as problem:
                    row["conversion"] = str(problem)
            rows.append(row)
    lean_rows = []
    for row in rows:
        if row["claim"] != "provable" or row["conversion"]:
            continue
        kind = "net" if row["arm"] == "net" else "proof"
        proposal = row.get("converted", row["proposal"])
        lean_rows.append({"id": row["id"], "arm": row["arm"], "sequent": row["sequent"], "claim": "provable",
                          "kind": kind, "proposal": proposal})
    verdicts = verify(lean_rows)
    for row in rows:
        verdict = verdicts.get((row["id"], row["arm"]))
        row["valid"] = bool(verdict and verdict["valid"])
        row["reason"] = row["conversion"] or (verdict["reason"] if verdict else "")
        row["correct"] = row["valid"] if row["expectedProvable"] else row["claim"] == "unprovable"
        del row["sequent"]
        row.pop("converted", None)
    return rows


def verify(rows: list[dict[str, Any]]) -> dict[tuple[str, str], dict[str, Any]]:
    payload = "".join(json.dumps({"id": f"{r['id']}|{r['arm']}", "sequent": r["sequent"], "kind": r["kind"],
                                  "proposal": r["proposal"]}, separators=(",", ":")) + "\n" for r in rows)
    if not payload:
        return {}
    completed = subprocess.run([v1.find_lake(), "exe", "proofnet_ir_representation_verify"], cwd=ROOT,
                               input=payload, capture_output=True, text=True, encoding="utf-8", check=True)
    out = {}
    for line in completed.stdout.splitlines():
        if line.startswith("{"):
            verdict = json.loads(line)
            task_id, arm = verdict["id"].rsplit("|", 1)
            out[(task_id, arm)] = verdict
    return out


def sign_test(wins: int, losses: int) -> float:
    n = wins + losses
    return 1.0 if n == 0 else sum(math.comb(n, k) for k in range(wins, n + 1)) / 2 ** n


def summarize(rows: list[dict[str, Any]]) -> dict[str, Any]:
    by = {(r["id"], r["arm"]): r for r in rows}
    ids = sorted({r["id"] for r in rows})
    positives = [i for i in ids if by[(i, "net")]["expectedProvable"]]
    negatives = [i for i in ids if not by[(i, "net")]["expectedProvable"]]
    arms: dict[str, Any] = {}
    for arm in ARMS:
        mine = [r for r in rows if r["arm"] == arm]
        valid_tokens = sorted(by[(i, arm)]["completionTokens"] for i in positives if by[(i, arm)]["valid"])
        arms[arm] = {
            "validOnPositives": sum(by[(i, arm)]["valid"] for i in positives),
            "unprovableOnPositives": sum(by[(i, arm)]["claim"] == "unprovable" for i in positives),
            "unprovableOnNegatives": sum(by[(i, arm)]["claim"] == "unprovable" for i in negatives),
            "unparseable": sum(r["claim"] == "unparseable" for r in mine),
            "truncated": sum(r["finishReason"] == "length" for r in mine),
            "conversionFailures": sum(bool(r["conversion"]) for r in mine),
            "errors": sum(bool(r["error"]) for r in mine),
            "medianTokensValid": statistics.median(valid_tokens) if valid_tokens else None,
            "medianTokensAll": statistics.median(r["completionTokens"] for r in mine),
            "successByTokens": {str(t): sum(1 for i in positives if by[(i, arm)]["valid"]
                                             and by[(i, arm)]["completionTokens"] <= t) for t in CUTOFFS},
            "reasons": dict(sorted({(r["reason"] or "")[:60]: 0 for r in mine}.items())),
        }
        for r in mine:
            key = (r["reason"] or "")[:60]
            arms[arm]["reasons"][key] += 1
    strata: dict[str, Any] = {}
    for r in rows:
        entry = strata.setdefault(r["stratum"], {a: {"tasks": 0, "valid": 0, "unprovable": 0} for a in ARMS})
        entry[r["arm"]]["tasks"] += 1
        entry[r["arm"]]["valid"] += r["valid"]
        entry[r["arm"]]["unprovable"] += r["claim"] == "unprovable"

    def paired(first: str, second: str) -> dict[str, Any]:
        wins = sum(1 for i in positives if by[(i, first)]["valid"] and not by[(i, second)]["valid"])
        losses = sum(1 for i in positives if by[(i, second)]["valid"] and not by[(i, first)]["valid"])
        return {"first": first, "second": second, "firstValid": arms[first]["validOnPositives"],
                "secondValid": arms[second]["validOnPositives"], "firstOnly": wins, "secondOnly": losses,
                "oneSidedP": sign_test(wins, losses)}

    h72, h73 = paired("proofIds", "proof"), paired("net", "proofIds")
    return {
        "experiment": "representation-v0.2",
        "preregistrationSha256": v1.sha256_file(PREREG) if PREREG.exists() else None,
        "tasks": len(ids), "positives": len(positives), "negatives": len(negatives),
        "arms": arms, "strata": dict(sorted(strata.items())),
        "hypotheses": {
            "H72": {"test": h72, "supported": h72["firstValid"] > h72["secondValid"]},
            "H73": {"test": h73, "supported": h73["firstValid"] > h73["secondValid"]},
        },
        "checks": {"C18": {"truncated": sum(a["truncated"] for a in arms.values()),
                           "holds": all(a["truncated"] == 0 for a in arms.values())},
                   "C19": {"errors": sum(a["errors"] for a in arms.values()),
                           "holds": all(a["errors"] == 0 for a in arms.values())}},
        "resultsSha256": v1.sha256_file(RESULTS) if RESULTS.exists() else None,
        "responsesSha256": v1.sha256_file(RESPONSES) if RESPONSES.exists() else None,
    }


def self_test() -> int:
    """Hand-made labelled derivations, converted and verified by Lean, and conversion failures named."""
    def at(n: str, p: bool = True) -> dict[str, Any]:
        return {"kind": "atom", "name": n, "positive": p}

    def t(l: dict[str, Any], r: dict[str, Any]) -> dict[str, Any]:
        return {"kind": "tensor", "left": l, "right": r}

    def par(l: dict[str, Any], r: dict[str, Any]) -> dict[str, Any]:
        return {"kind": "par", "left": l, "right": r}

    a, na, b, nb = at("a"), at("a", False), at("b"), at("b", False)
    cases = [
        ("example", [t(a, b), par(na, nb)],
         {"rule": "par", "on": "c1", "premise": {"rule": "tensor", "on": "c0", "left": ["a2"],
                                                 "leftPremise": {"rule": "axiom"}, "rightPremise": {"rule": "axiom"}}},
         True),
        ("wrong split", [t(a, b), par(na, nb)],
         {"rule": "par", "on": "c1", "premise": {"rule": "tensor", "on": "c0", "left": ["a3"],
                                                 "leftPremise": {"rule": "axiom"}, "rightPremise": {"rule": "axiom"}}},
         False),
        ("identity", [a, na], {"rule": "axiom"}, True),
        ("par of an atom", [a, na], {"rule": "par", "on": "a0", "premise": {"rule": "axiom"}}, False),
        ("nested", [par(t(a, b), at("c")), t(par(na, nb), at("c", False))],
         {"rule": "par", "on": "c0", "premise": {"rule": "tensor", "on": "c2", "left": ["c1"],
          "leftPremise": {"rule": "par", "on": "c3", "premise": {"rule": "tensor", "on": "c1", "left": ["a3"],
                          "leftPremise": {"rule": "axiom"}, "rightPremise": {"rule": "axiom"}}},
          "rightPremise": {"rule": "axiom"}}}, True),
    ]
    failures = 0
    rows = []
    for name, sequent, proof, expected in cases:
        try:
            converted = to_positions(proof, sequent)
        except ValueError as problem:
            ok = not expected
            failures += not ok
            print(json.dumps({"case": name, "conversion": str(problem), "ok": ok}))
            continue
        rows.append({"id": name, "arm": "proofIds", "sequent": sequent, "kind": "proof", "proposal": converted,
                     "expected": expected})
    verdicts = verify(rows)
    for row in rows:
        valid = verdicts[(row["id"], "proofIds")]["valid"]
        ok = valid == row["expected"]
        failures += not ok
        print(json.dumps({"case": row["id"], "valid": valid, "ok": ok}))
    print(render_ids(cases[4][1]))
    return 1 if failures else 0


def collect(tasks: list[dict[str, Any]], partial_path: Path | None) -> dict[tuple[str, str], dict[str, Any]]:
    responses: dict[tuple[str, str], dict[str, Any]] = {}
    if partial_path and partial_path.is_file():
        for line in partial_path.read_text(encoding="utf-8").splitlines():
            if line.strip():
                row = json.loads(line)
                responses[(row["id"], row["arm"])] = row
    for task in tasks:
        for arm in ARMS:
            key = (task["id"], arm)
            if key in responses and responses[key]["error"] is None:
                continue
            responses[key] = call_model(task, arm)
            if partial_path:
                v1.write_lf(partial_path, "".join(json.dumps(responses[k], ensure_ascii=False, separators=(",", ":"))
                                                  + "\n" for k in sorted(responses)))
            print(json.dumps({"id": task["id"], "arm": arm, "tokens": v1.classify(responses[key]["response"])[2],
                              "error": responses[key]["error"]}), flush=True)
    return responses


def pilot_tasks() -> list[dict[str, Any]]:
    """Development sequents outside the corpus: generated bases at seed 950000, two per depth 2 and 3, with unique
    and one-label names; each positive and its first connective flip."""
    import run_matched_search as matched
    completed = subprocess.run([v1.find_lake(), "exe", "proofnet_ir_pruned_search", "--dev-bases", "950000", "2"],
                               cwd=ROOT, capture_output=True, text=True, encoding="utf-8", check=True)
    tasks = []
    for base in (json.loads(l) for l in completed.stdout.splitlines() if l.startswith("{")):
        if base["depth"] not in (2, 3):
            continue
        for mode in ("unique", "one-label"):
            sequent = [matched.rename(f, matched.name_map(base["sequent"], mode)) for f in base["sequent"]]
            flipped = matched.flip_at(sequent, matched.connective_positions(sequent)[0])
            for suffix, seq, provable in (("positive", sequent, True), ("negative", flipped, False)):
                tasks.append({"id": f"pilot-{base['seed']}-{mode}-{suffix}", "depth": base["depth"],
                              "labelMode": mode, "expectedProvable": provable, "sequent": seq})
    return tasks


def registration_payload(tasks: list[dict[str, Any]]) -> dict[str, Any]:
    strata: dict[str, int] = {}
    for task in tasks:
        strata[v1.stratum(task)] = strata.get(v1.stratum(task), 0) + 1
    return {
        "experiment": "representation-v0.2",
        "question": "does representation-v0.1's lead of nets over derivations survive when derivations use stable "
                    "labels instead of shifting positions, every answer is decoded under its format's grammar, and "
                    "the budget is 8,192 tokens",
        "arms": {"proof": "representation-v0.1's position-based derivation, prompt and rendering unchanged",
                 "proofIds": "the same derivations over stable subformula labels, rendered with every subformula "
                             "labelled, converted to the position format before Lean verifies them",
                 "net": "representation-v0.1's axiom linking, prompt and rendering unchanged"},
        "corpus": {"path": "experiments/model-v0.2/corpus.jsonl", "sha256": v1.sha256_file(v1.CORPUS_SOURCE),
                   "taskCount": len(tasks), "strata": dict(sorted(strata.items()))},
        "model": {"id": v1.MODEL_ID, "endpoint": v1.MODEL_ENDPOINT, "temperature": 0, "seed": v1.MODEL_SEED,
                  "maxTokens": MODEL_MAX_TOKENS, "thinking": False, "grammar": "each arm's GBNF grammar"},
        "promptSha256": {"proofSystem": v1.sha256_text(v1.PROOF_SYSTEM), "proofIdsSystem":
                         v1.sha256_text(PROOF_IDS_SYSTEM), "netSystem": v1.sha256_text(v1.NET_SYSTEM)},
        "grammarSha256": {arm: v1.sha256_text(g) for arm, g in GRAMMARS.items()},
        "implementationSha256": {name: v1.sha256_file(path) for name, path in IMPLEMENTATIONS.items()},
        "scoring": "as representation-v0.1: a positive is correct only when Lean verifies the proposal, a negative "
                   "only when the answer is unprovable; a labelled derivation whose rules do not apply to the "
                   "sequent is invalid without reaching Lean",
        "hypotheses": {
            "H72": "on positives, proofIds has more Lean-verified proposals than proof",
            "H73": "on positives, net has more Lean-verified proposals than proofIds",
        },
        "checks": {"C18": "no answer stops at the 8,192-token budget", "C19": "no request fails"},
        "report": "per arm: verified positives, unprovable answers on positives and on negatives, unparseable and "
                  "truncated answers, conversion failures, the rejection reasons, median tokens, and verified "
                  "positives within 64, 128, ..., 8,192 completion tokens; exact one-sided sign tests on the "
                  "positives each arm alone verifies",
        "developmentChecksBeforeRegistration": [
            "--self-test: five hand-made labelled derivations, three verified by Lean and two rejected as expected",
            "--pilot: development sequents outside the corpus (bases at seed 950000; 8 positives and 8 negatives), "
            "all three arms: no proposal in any arm verified; the proof and proofIds arms answered provable on all 16 "
            "and every derivation was rejected (a rule on a position or label that does not hold its connective, or "
            "that names formulas not in the sequent); the net arm answered unprovable on 12 and gave 4 linkings that Lean "
            "rejected; no answer reached 1,100 tokens and none failed",
        ],
        "resultsAbsentAtRegistration": True,
        "registeredLocalDate": time.strftime("%Y-%m-%d") + " America/Los_Angeles",
    }


def write_report(summary: dict[str, Any]) -> None:
    lines = ["# Representation-as-target model study v0.2", "",
             "Three output formats, one model at temperature zero without thinking, each answer decoded under its",
             "format's grammar with 8,192 completion tokens; frozen in `preregistration.json` (SHA-256",
             f"`{summary['preregistrationSha256']}`).", "",
             f"Tasks: {summary['tasks']} ({summary['positives']} positives, {summary['negatives']} negatives).", "",
             "| Arm | Verified positives | Unprovable on positives / negatives | Unparseable | Truncated | "
             "Median tokens (verified) |", "| --- | ---: | --- | ---: | ---: | ---: |"]
    for arm in ARMS:
        a = summary["arms"][arm]
        lines.append(f"| {arm} | {a['validOnPositives']} | {a['unprovableOnPositives']} / {a['unprovableOnNegatives']} | "
                     f"{a['unparseable']} | {a['truncated']} | {a['medianTokensValid']} |")
    lines += ["", "Verified positives within a token budget:", "",
              "| Arm | " + " | ".join(str(t) for t in CUTOFFS) + " |", "| --- |" + " ---: |" * len(CUTOFFS)]
    for arm in ARMS:
        lines.append(f"| {arm} | " + " | ".join(str(summary["arms"][arm]["successByTokens"][str(t)])
                                               for t in CUTOFFS) + " |")
    lines += ["", "| Stratum | " + " | ".join(f"{a} valid/unprovable" for a in ARMS) + " |",
              "| --- |" + " --- |" * len(ARMS)]
    for name, entry in summary["strata"].items():
        lines.append(f"| {name} | " + " | ".join(f"{entry[a]['valid']}/{entry[a]['unprovable']}" for a in ARMS) + " |")
    h = summary["hypotheses"]
    lines += ["", "## Hypotheses", ""]
    for name, words in (("H72", "proofIds verifies more positives than proof"),
                        ("H73", "net verifies more positives than proofIds")):
        t = h[name]["test"]
        lines.append(f"- {name} ({words}): supported: {h[name]['supported']}; {t['firstValid']} vs {t['secondValid']}, "
                     f"{t['firstOnly']} and {t['secondOnly']} verified by one arm alone (one-sided p {t['oneSidedP']:.3g}).")
    lines += ["", f"Checks: C18 {summary['checks']['C18']}; C19 {summary['checks']['C19']}.", "",
              "## Interpretation boundary", "",
              "One quantized local model on held-out unit-free, cut-free MLL sequents. The result concerns which output",
              "format this model produces correctly under these conditions, not models in general or proof assistants."]
    v1.write_lf(REPORT, "\n".join(lines) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--self-test", action="store_true")
    mode.add_argument("--pilot", action="store_true")
    mode.add_argument("--register", action="store_true")
    mode.add_argument("--run", action="store_true")
    mode.add_argument("--check-committed", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        return self_test()
    if args.pilot:
        tasks = pilot_tasks()
        rows = evaluate(tasks, collect(tasks, None))
        for row in rows:
            print(json.dumps({k: row[k] for k in ("id", "arm", "claim", "valid", "reason", "completionTokens",
                                                  "finishReason")}, ensure_ascii=False))
        return 0
    tasks = v1.load_corpus()
    if args.register:
        if RESULTS.exists() or RESPONSES.exists():
            raise SystemExit("results already exist; registration must precede them")
        EXPERIMENT.mkdir(parents=True, exist_ok=True)
        v1.write_lf(PREREG, json.dumps(registration_payload(tasks), indent=1, sort_keys=True, ensure_ascii=False) + "\n")
        print(f"registered {len(tasks)} tasks: {PREREG}")
        return 0
    prereg = json.loads(PREREG.read_text(encoding="utf-8"))
    frozen = registration_payload(tasks)
    for field in ("corpus", "promptSha256", "grammarSha256"):
        if prereg[field] != frozen[field]:
            raise SystemExit(f"{field} changed since registration")
    for name in ("verifier", "v01Runner"):
        if prereg["implementationSha256"][name] != v1.sha256_file(IMPLEMENTATIONS[name]):
            raise SystemExit(f"implementation {name} changed since registration")
    if args.run:
        responses = collect(tasks, RESPONSES)
        rows = evaluate(tasks, responses)
        v1.write_lf(RESULTS, "".join(json.dumps(r, ensure_ascii=False, separators=(",", ":")) + "\n" for r in rows))
        summary = summarize(rows)
        v1.write_lf(SUMMARY, json.dumps(summary, indent=1) + "\n")
        write_report(summary)
        print(json.dumps(summary["hypotheses"]))
        return 0
    responses = {}
    for line in RESPONSES.read_text(encoding="utf-8").splitlines():
        if line.strip():
            row = json.loads(line)
            responses[(row["id"], row["arm"])] = row
    rows = evaluate(tasks, responses)
    committed = [json.loads(line) for line in RESULTS.read_text(encoding="utf-8").splitlines() if line.strip()]
    if json.loads(json.dumps(rows, ensure_ascii=False)) != committed:
        raise SystemExit("the committed results do not follow from the committed responses")
    summary = json.loads(SUMMARY.read_text(encoding="utf-8"))
    if summary != json.loads(json.dumps(summarize(committed))):
        raise SystemExit("the committed summary does not follow from the committed results")
    print(f"representation-v0.2-check-ok: tasks={summary['tasks']} rows={len(committed)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
