#!/usr/bin/env python3
"""Audit the model-v0.2 publication-only metadata redaction.

The experiment was originally committed with a machine-local GGUF path in five
tracked artifact families.  History is intentionally retained.  This checker
loads the byte-exact source artifacts from Git, verifies their recorded hashes,
and proves that the publication copies differ only in the enumerated metadata
fields plus the derived content hashes.  The original wire-request hashes stay
untouched; new canonical hashes bind the same requests to the public model
alias.  Historical requests are reconstructed here without importing the
published runner, and both runner transformations are fixed byte pairs in this
checker.  The checker implementation is the explicit repo-local trust root;
independent authentication must come from external protected review/CI or a
signed release policy, not a checker self-hash.
"""

from __future__ import annotations

import ast
import copy
import hashlib
import json
import re
import subprocess
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
OUTPUT_DIR = ROOT / "experiments" / "model-v0.2"
RECEIPT_PATH = OUTPUT_DIR / "publication-redaction-amendment-1.json"
SOURCE_COMMIT = "605648ea12598ed4f713976a7448dc77762a42b8"
RECEIPT_VERSION = "model-v0.2-publication-redaction-amendment-1"
TASK_COUNT = 180
MODEL_ALIAS = "qwen3.6-35b-a3b-ud-q4_k_xl"
MODEL_ARTIFACT_FILE_NAME = "Qwen3.6-35B-A3B-UD-Q4_K_XL.gguf"
MODEL_ARTIFACT_SHA256 = (
    "707a55a8a4397ecde44de0c499d3e68c1ad1d240d1da65826b4949d1043f4450"
)
MODEL_SEED = 20_260_723
MODEL_MAX_TOKENS = 128

DIRECT_SYSTEM = """You solve one unit-free cut-free MLL proof-net task. Reply with one JSON object and no prose. If unprovable: {\"c\":\"U\",\"pairs\":[]}. If provable: {\"c\":\"P\",\"pairs\":[[a,b],...]}. Pair every atom vertex exactly once with the same name and opposite sign. Fixed t/p links and ordered conclusions stay unchanged. The Danos-Regnier checker tests every par switching."""

REPAIR_SYSTEM = """You repair one unit-free cut-free MLL proof-net task. Reply with one JSON object and no prose. If the sequent is unprovable: {\"c\":\"U\",\"pairs\":[]}. If provable: {\"c\":\"P\",\"pairs\":[[a,b],...]}. Replace the supplied R axiom matching with a complete matching. Pair every atom vertex exactly once with the same name and opposite sign. Fixed t/p links and ordered conclusions stay unchanged. The Danos-Regnier checker tests every par switching."""

CORPUS_REL = "experiments/model-v0.2/corpus.jsonl"
PREREG_REL = "experiments/model-v0.2/preregistration.json"
PROTOCOL_REL = "experiments/model-v0.2/protocol-amendment-1.json"
RAW_REL = "experiments/model-v0.2/raw-responses.jsonl"
RESULTS_REL = "experiments/model-v0.2/results.jsonl"
SUMMARY_REL = "experiments/model-v0.2/summary.json"
FROZEN_RUNNER_REL = "scripts/run_model_experiment.py"
AMENDED_RUNNER_REL = "scripts/run_model_experiment_amended.py"

REDACTED_FILES = (
    FROZEN_RUNNER_REL,
    AMENDED_RUNNER_REL,
    PREREG_REL,
    PROTOCOL_REL,
    RAW_REL,
    RESULTS_REL,
    SUMMARY_REL,
)

EXPECTED_RUNNER_HASHES = {
    FROZEN_RUNNER_REL: {
        "originalSha256": "63b0e1f806b82da1cb03da1a578a3a2196605d292541b77225f65118e5a17a92",
        "publishedSha256": "394761dd2a49eb139d263a1dbb2809ad1915bf37cfedbe0988a86eaacfd58ee6",
    },
    AMENDED_RUNNER_REL: {
        "originalSha256": "4e2819087f5c270463579aeac9bcae9b9d2619f29961c31c9ed3f505655fb2a8",
        "publishedSha256": "78b7ae31e2ba8d9171f1708e1c49b2355121a26015b723ef1ce24956a0d7bd64",
    },
}

EXPECTED_ALLOWED_ARTIFACT_CHANGES = {
    PREREG_REL: [
        "/model/id",
        "/model/artifactFileName (added)",
        "/model/artifactSha256 (added)",
        "/model/artifactSha256Status (added)",
        "/publicationRedaction (added)",
    ],
    PROTOCOL_REL: ["/publicationRedaction (added)"],
    RAW_REL: [
        "/*/response/model",
        "/*/canonicalRequestSha256 (added)",
    ],
    RESULTS_REL: [
        "/*/modelDirect/responseModel",
        "/*/modelRepair/responseModel",
    ],
    SUMMARY_REL: [
        "/model/requestedId",
        "/model/responseModels",
        "/model/artifactFileName (added)",
        "/model/artifactSha256 (added)",
        "/model/artifactSha256Status (added)",
        "/preregistrationSha256",
        "/protocolAmendmentSha256",
        "/rawResponsesSha256",
        "/resultsSha256",
        "/publicationRedaction (added)",
    ],
    FROZEN_RUNNER_REL: [
        "exact source/published byte pair fixed by the checker",
        "stable public model alias and artifact identity",
        "runtime request-id override separated from publication metadata",
        "canonical request hash emission and redaction validation bridge",
    ],
    AMENDED_RUNNER_REL: [
        "exact source/published byte pair fixed by the checker",
        "published-artifact hash and redaction validation bridge",
        "publication metadata emission and historical-runner clarification",
    ],
}

EXPECTED_VALIDATION_POLICY = {
    "command": "python scripts/validate_model_publication_redaction.py",
    "mutationRegressionCommand": (
        "python scripts/test_model_publication_redaction.py"
    ),
    "requiresFullGitHistory": True,
    "runnerTransformEnforcement": (
        "checker-hardcoded-byte-exact-source-published-pairs"
    ),
    "trackedAbsoluteGgufPathScan": True,
    "trustBoundary": (
        "the reviewed checker implementation is the remaining repo-local trust "
        "root; independent authentication requires external protected review/CI "
        "or a signed release policy, not a checker self-hash"
    ),
}

WINDOWS_DRIVE_GGUF = re.compile(
    r"(?i)(?<![A-Za-z0-9_])[A-Z]:[\\/][^\r\n\"<>]*?\.gguf"
)
UNC_GGUF = re.compile(
    r"(?i)(?<![A-Za-z0-9_:\\/])(?:\\\\|//)"
    r"[^\\/\r\n\"<>]+[\\/][^\r\n\"<>]*?\.gguf"
)
POSIX_GGUF = re.compile(
    r"(?i)(?<![A-Za-z0-9_:/\\])/(?!/)[^\r\n\"<>]*?\.gguf"
)
FILE_URI_GGUF = re.compile(
    r"(?i)(?<![A-Za-z0-9_])file:(?://|/)[^\r\n\"<>]*?\.gguf"
)

EXPECTED_HISTORICAL_INTEGRITY = {
    "canonicalRequestSha256": (
        "added in all 360 raw rows as the hash of the same request with only "
        "model.id replaced by the stable alias"
    ),
    "historyRewrite": False,
    "originalArtifacts": (
        "byte-exact artifacts remain available at sourceCommit and are verified "
        "by originalSha256"
    ),
    "originalRequestSha256": (
        "retained byte-for-byte in all 360 raw rows as the hash of the request "
        "actually sent"
    ),
}

EXPECTED_MATHEMATICAL_RESULTS = {
    "leanVerification": {
        "accepted": 92,
        "rejected": 184,
        "sequentialized": 92,
        "uniqueInputs": 276,
    },
    "methodSuccesses": {
        "algorithmicRepair": 180,
        "focused": 85,
        "modelDirect": 117,
        "modelRepair": 2,
        "netGeneration": 160,
    },
    "rawRequestSha256Retained": 360,
    "scope": (
        "all task inputs, response contents, method outcomes, timings, token "
        "counts, checker results, and sequentialization results are unchanged"
    ),
    "taskCount": 180,
}

EXPECTED_MODEL_ARTIFACT = {
    "artifactFileName": MODEL_ARTIFACT_FILE_NAME,
    "sha256": MODEL_ARTIFACT_SHA256,
    "sha256Status": "verified-local-artifact-2026-07-28",
    "sizeBytes": 22_360_456_160,
    "verificationBoundary": (
        "SHA-256 computed from the local artifact; the untracked machine path "
        "is intentionally not published"
    ),
}

EXPECTED_REASON = (
    "remove a machine-specific absolute GGUF path from publication artifacts "
    "without changing model identity, responses, scores, or mathematical "
    "conclusions"
)
EXPECTED_REGISTERED_LOCAL_DATE = "2026-07-28 America/Los_Angeles"
EXPECTED_SOURCE_COMMIT_MEANING = (
    "last public commit containing the unredacted machine-local metadata; "
    "history is retained and not rewritten"
)
EXPECTED_RECEIPT_KEYS = {
    "allowedArtifactChanges",
    "files",
    "historicalIntegrity",
    "mathematicalResultsUnchanged",
    "modelArtifact",
    "reason",
    "registeredLocalDate",
    "sourceCommit",
    "sourceCommitMeaning",
    "stableModelAlias",
    "validation",
    "version",
}


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def compact_json(value: object) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def sha256_text(value: str) -> str:
    return sha256_bytes(value.encode("utf-8"))


def git_bytes(commit: str, relative_path: str) -> bytes:
    result = subprocess.run(
        ["git", "show", f"{commit}:{relative_path}"],
        cwd=ROOT,
        check=False,
        capture_output=True,
    )
    if result.returncode != 0:
        message = result.stderr.decode("utf-8", errors="replace").strip()
        raise AssertionError(
            f"cannot load {relative_path} from source commit {commit}: {message}"
        )
    return result.stdout


def reject_duplicate_object(
    pairs: list[tuple[str, Any]],
) -> dict[str, Any]:
    value: dict[str, Any] = {}
    for key, item in pairs:
        if key in value:
            raise AssertionError(f"duplicate JSON key: {key}")
        value[key] = item
    return value


def strict_json_loads(text: str, label: str) -> Any:
    try:
        return json.loads(text, object_pairs_hook=reject_duplicate_object)
    except json.JSONDecodeError as exception:
        raise AssertionError(f"invalid JSON in {label}: {exception}") from exception
    except AssertionError as exception:
        raise AssertionError(f"{label}: {exception}") from exception


def load_json_bytes(
    payload: bytes, label: str = "JSON object"
) -> dict[str, Any]:
    value = strict_json_loads(payload.decode("utf-8"), label)
    if not isinstance(value, dict):
        raise AssertionError(f"expected a JSON object in {label}")
    return value


def load_jsonl_bytes(
    payload: bytes, label: str = "JSONL payload"
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for position, line in enumerate(payload.decode("utf-8").splitlines()):
        if not line:
            continue
        row = strict_json_loads(line, f"{label} row {position}")
        if not isinstance(row, dict):
            raise AssertionError(f"expected a JSON object in {label} row {position}")
        rows.append(row)
    return rows


def assert_equal(actual: object, expected: object, label: str) -> None:
    if actual != expected:
        raise AssertionError(f"publication redaction drifted outside {label}")


def receipt_pointer(receipt: dict[str, Any]) -> dict[str, str]:
    return {
        "receipt": RECEIPT_PATH.name,
        "version": str(receipt["version"]),
    }


def artifact_fields(receipt: dict[str, Any]) -> dict[str, str]:
    artifact = receipt["modelArtifact"]
    return {
        "artifactFileName": str(artifact["artifactFileName"]),
        "artifactSha256": str(artifact["sha256"]),
        "artifactSha256Status": str(artifact["sha256Status"]),
    }


def validate_receipt_policy(receipt: dict[str, Any]) -> None:
    if set(receipt) != EXPECTED_RECEIPT_KEYS:
        raise AssertionError("publication-redaction receipt key inventory mismatch")
    if receipt.get("version") != RECEIPT_VERSION:
        raise AssertionError("publication-redaction receipt version mismatch")
    if receipt.get("sourceCommit") != SOURCE_COMMIT:
        raise AssertionError("publication-redaction source commit mismatch")
    if receipt.get("stableModelAlias") != MODEL_ALIAS:
        raise AssertionError("stable model alias mismatch")
    if receipt.get("modelArtifact") != EXPECTED_MODEL_ARTIFACT:
        raise AssertionError("publication-redaction model artifact metadata mismatch")
    if receipt.get("historicalIntegrity") != EXPECTED_HISTORICAL_INTEGRITY:
        raise AssertionError("publication-redaction historical-integrity metadata mismatch")
    if (
        receipt.get("mathematicalResultsUnchanged")
        != EXPECTED_MATHEMATICAL_RESULTS
    ):
        raise AssertionError("publication-redaction mathematical metadata mismatch")
    if receipt.get("reason") != EXPECTED_REASON:
        raise AssertionError("publication-redaction reason mismatch")
    if receipt.get("registeredLocalDate") != EXPECTED_REGISTERED_LOCAL_DATE:
        raise AssertionError("publication-redaction registration date mismatch")
    if receipt.get("sourceCommitMeaning") != EXPECTED_SOURCE_COMMIT_MEANING:
        raise AssertionError("publication-redaction source-commit meaning mismatch")
    files = receipt.get("files")
    if not isinstance(files, dict) or set(files) != set(REDACTED_FILES):
        raise AssertionError("publication-redaction file inventory mismatch")
    for relative, record in files.items():
        if not isinstance(record, dict) or set(record) != {
            "originalSha256",
            "publishedSha256",
        }:
            raise AssertionError(
                f"publication-redaction file record schema mismatch: {relative}"
            )
        for field in ("originalSha256", "publishedSha256"):
            value = record[field]
            if not isinstance(value, str) or re.fullmatch(
                r"[0-9a-f]{64}", value
            ) is None:
                raise AssertionError(
                    f"publication-redaction file hash format mismatch: "
                    f"{relative} {field}"
                )
    if receipt.get("allowedArtifactChanges") != EXPECTED_ALLOWED_ARTIFACT_CHANGES:
        raise AssertionError("publication-redaction allowed-change policy mismatch")
    if "validatorSha256" in receipt.get("validation", {}):
        raise AssertionError("checker self-hash must not be treated as a trust root")
    if receipt.get("validation") != EXPECTED_VALIDATION_POLICY:
        raise AssertionError("publication-redaction validation policy mismatch")


def validate_preregistration(
    original: dict[str, Any],
    published: dict[str, Any],
    receipt: dict[str, Any],
) -> None:
    expected = copy.deepcopy(original)
    expected["model"]["id"] = receipt["stableModelAlias"]
    expected["model"].update(artifact_fields(receipt))
    expected["publicationRedaction"] = receipt_pointer(receipt)
    assert_equal(published, expected, "preregistration model metadata")


def validate_corpus(
    source_payload: bytes,
    published_payload: bytes,
    expected_sha256: str,
) -> None:
    if sha256_bytes(source_payload) != expected_sha256:
        raise AssertionError(
            "source-commit corpus hash does not match preregistration"
        )
    if published_payload != source_payload:
        raise AssertionError(
            "published corpus changed during metadata-only redaction"
        )


def historical_render_task(task: dict[str, Any], mode: str) -> str:
    if mode not in {"direct", "repair"}:
        raise AssertionError(f"unknown raw-response mode: {mode}")
    skeleton = task["skeleton"]
    atoms = []
    for vertex, value in enumerate(skeleton["formulas"]):
        if value["kind"] == "atom":
            atoms.append(
                f"{vertex}:{value['name']}{'+' if value['positive'] else '-'}"
            )
    fixed = []
    for link in skeleton["links"]:
        if link["kind"] == "axiom":
            continue
        prefix = "t" if link["kind"] == "tensor" else "p"
        fixed.append(
            f"{prefix}{int(link['left'])},{int(link['right'])}>"
            f"{int(link['conclusion'])}"
        )
    fields = [
        f"id={task['id']}",
        "A=" + ",".join(atoms),
        "F=" + ";".join(fixed),
        "C=" + ",".join(str(int(value)) for value in skeleton["conclusions"]),
    ]
    if mode == "repair":
        fields.append(
            "R="
            + ",".join(
                f"{int(link['left'])}-{int(link['right'])}"
                for link in task["repairSourceAxioms"]
            )
        )
    return " ".join(fields)


def historical_request_body(
    task: dict[str, Any], mode: str, historical_model_id: str
) -> dict[str, Any]:
    if mode not in {"direct", "repair"}:
        raise AssertionError(f"unknown raw-response mode: {mode}")
    system = DIRECT_SYSTEM if mode == "direct" else REPAIR_SYSTEM
    return {
        "model": historical_model_id,
        "messages": [
            {"role": "system", "content": system},
            {"role": "user", "content": historical_render_task(task, mode)},
        ],
        "temperature": 0,
        "seed": MODEL_SEED,
        "max_tokens": MODEL_MAX_TOKENS,
        "chat_template_kwargs": {"enable_thinking": False},
    }


def canonical_request_sha256(
    historical_body: dict[str, Any], alias: str
) -> str:
    canonical_body = copy.deepcopy(historical_body)
    if "model" not in canonical_body:
        raise AssertionError("historical request body has no model field")
    canonical_body["model"] = alias
    return sha256_text(compact_json(canonical_body))


def validate_raw_responses(
    original: list[dict[str, Any]],
    published: list[dict[str, Any]],
    receipt: dict[str, Any],
    historical_model_id: str,
    tasks: list[dict[str, Any]],
) -> None:
    if len(original) != TASK_COUNT * 2 or len(published) != len(original):
        raise AssertionError("raw-response row count drifted")
    tasks_by_id = {str(task["id"]): task for task in tasks}
    if len(tasks_by_id) != TASK_COUNT:
        raise AssertionError("source-commit corpus task count drifted")
    alias = receipt["stableModelAlias"]
    for position, (old_row, new_row) in enumerate(zip(original, published, strict=True)):
        task = tasks_by_id.get(str(old_row["id"]))
        if task is None:
            raise AssertionError(f"unknown raw-response task: {old_row['id']}")
        mode = str(old_row["mode"])
        historical_body = historical_request_body(
            task,
            mode,
            historical_model_id,
        )
        historical_request_sha256 = sha256_text(
            compact_json(historical_body)
        )
        if old_row.get("requestSha256") != historical_request_sha256:
            raise AssertionError(
                f"historical requestSha256 cannot be reconstructed at row {position}"
            )
        expected = copy.deepcopy(old_row)
        response = expected.get("response")
        if isinstance(response, dict) and "model" in response:
            response["model"] = alias
        expected["canonicalRequestSha256"] = canonical_request_sha256(
            historical_body,
            alias,
        )
        if new_row.get("requestSha256") != old_row.get("requestSha256"):
            raise AssertionError(
                f"historical requestSha256 changed at raw row {position}"
            )
        assert_equal(new_row, expected, f"raw-response row {position} metadata")


def validate_results(
    original: list[dict[str, Any]],
    published: list[dict[str, Any]],
    receipt: dict[str, Any],
) -> None:
    if len(original) != TASK_COUNT or len(published) != len(original):
        raise AssertionError("result row count drifted")
    alias = receipt["stableModelAlias"]
    for position, (old_row, new_row) in enumerate(zip(original, published, strict=True)):
        expected = copy.deepcopy(old_row)
        expected["modelDirect"]["responseModel"] = alias
        expected["modelRepair"]["responseModel"] = alias
        assert_equal(new_row, expected, f"result row {position} model metadata")


def validate_protocol(
    original: dict[str, Any],
    published: dict[str, Any],
    receipt: dict[str, Any],
) -> None:
    expected = copy.deepcopy(original)
    artifact = receipt["modelArtifact"]
    expected["publicationRedaction"] = {
        "artifactFileName": artifact["artifactFileName"],
        "artifactSha256": artifact["sha256"],
        "artifactSha256Status": artifact["sha256Status"],
        "publishedRawResponsesSha256": receipt["files"][RAW_REL][
            "publishedSha256"
        ],
        "publishedValidationRunnerSha256": receipt["files"][
            AMENDED_RUNNER_REL
        ]["publishedSha256"],
        "receipt": RECEIPT_PATH.name,
        "sourceCommit": receipt["sourceCommit"],
        "stableModelAlias": receipt["stableModelAlias"],
        "version": receipt["version"],
    }
    assert_equal(published, expected, "protocol publication metadata")


def validate_summary(
    original: dict[str, Any],
    published: dict[str, Any],
    receipt: dict[str, Any],
) -> None:
    expected = copy.deepcopy(original)
    expected["preregistrationSha256"] = receipt["files"][PREREG_REL][
        "publishedSha256"
    ]
    expected["protocolAmendmentSha256"] = receipt["files"][PROTOCOL_REL][
        "publishedSha256"
    ]
    expected["rawResponsesSha256"] = receipt["files"][RAW_REL][
        "publishedSha256"
    ]
    expected["resultsSha256"] = receipt["files"][RESULTS_REL][
        "publishedSha256"
    ]
    expected["model"]["requestedId"] = receipt["stableModelAlias"]
    expected["model"]["responseModels"] = [receipt["stableModelAlias"]]
    expected["model"].update(artifact_fields(receipt))
    expected["publicationRedaction"] = receipt_pointer(receipt)
    assert_equal(published, expected, "summary metadata and derived hashes")


def validate_mathematical_receipt(
    summary: dict[str, Any], receipt: dict[str, Any]
) -> None:
    recorded = receipt["mathematicalResultsUnchanged"]
    observed_successes = {
        method: int(values["successes"])
        for method, values in summary["methods"]["overall"].items()
    }
    assert_equal(
        observed_successes,
        recorded["methodSuccesses"],
        "recorded method successes",
    )
    assert_equal(
        summary["leanVerification"],
        recorded["leanVerification"],
        "recorded Lean verification",
    )
    if int(recorded["taskCount"]) != int(summary["taskCount"]):
        raise AssertionError("recorded task count drifted")
    if int(recorded["rawRequestSha256Retained"]) != TASK_COUNT * 2:
        raise AssertionError("historical request-hash retention count drifted")


def validate_runner_transform_pairs(
    originals: dict[str, bytes],
    published: dict[str, bytes],
    receipt: dict[str, Any],
) -> None:
    """Enforce the reviewed runner transformation as two exact byte pairs."""

    records = receipt.get("files", {})
    for relative, expected in EXPECTED_RUNNER_HASHES.items():
        if records.get(relative) != expected:
            raise AssertionError(
                f"runner transform receipt is not the fixed allowlist: {relative}"
            )
        source_payload = originals.get(relative)
        published_payload = published.get(relative)
        if source_payload is None or published_payload is None:
            raise AssertionError(f"runner transform payload is missing: {relative}")
        if sha256_bytes(source_payload) != expected["originalSha256"]:
            raise AssertionError(f"runner source is not the fixed allowlist: {relative}")
        if sha256_bytes(published_payload) != expected["publishedSha256"]:
            raise AssertionError(
                f"runner publication is not the fixed allowlist: {relative}"
            )
        try:
            ast.parse(source_payload.decode("utf-8"), filename=f"{SOURCE_COMMIT}:{relative}")
            ast.parse(published_payload.decode("utf-8"), filename=relative)
        except (SyntaxError, UnicodeDecodeError) as exception:
            raise AssertionError(
                f"runner transform is not valid UTF-8 Python: {relative}"
            ) from exception


def absolute_gguf_matches(text: str) -> list[str]:
    variants = [text]
    for normalized in (
        text.replace("\\\\", "\\"),
        text.replace("\\/", "/"),
        text.replace("\\\\", "\\").replace("\\/", "/"),
    ):
        if normalized not in variants:
            variants.append(normalized)
    matches: set[str] = set()
    for variant in variants:
        for pattern in (
            WINDOWS_DRIVE_GGUF,
            UNC_GGUF,
            POSIX_GGUF,
            FILE_URI_GGUF,
        ):
            matches.update(match.group(0) for match in pattern.finditer(variant))
    return sorted(matches)


def absolute_gguf_matches_bytes(payload: bytes) -> list[str]:
    """Scan UTF-8, UTF-16, and opaque tracked payloads fail-closed.

    The Latin-1 fallback preserves every ASCII byte, so an otherwise invalid
    UTF-8 or binary payload cannot hide an ASCII absolute model path. UTF-16
    variants cover BOM-tagged text and common untagged two-byte encodings.
    """

    decoded: list[str] = []
    if payload.startswith((b"\xff\xfe", b"\xfe\xff")):
        try:
            decoded.append(payload.decode("utf-16"))
        except UnicodeDecodeError:
            pass
    try:
        decoded.append(payload.decode("utf-8"))
    except UnicodeDecodeError:
        decoded.append(payload.decode("latin-1"))
    if b"\0" in payload and len(payload) % 2 == 0:
        for encoding in ("utf-16-le", "utf-16-be"):
            try:
                candidate = payload.decode(encoding)
            except UnicodeDecodeError:
                continue
            if candidate not in decoded:
                decoded.append(candidate)
    matches: set[str] = set()
    for text in decoded:
        matches.update(absolute_gguf_matches(text))
    return sorted(matches)


def scan_tracked_absolute_gguf_paths() -> None:
    result = subprocess.run(
        ["git", "ls-files", "-z"],
        cwd=ROOT,
        check=True,
        capture_output=True,
    )
    leaks: list[str] = []
    for raw_name in result.stdout.split(b"\0"):
        if not raw_name:
            continue
        relative = raw_name.decode("utf-8")
        path = ROOT / relative
        if not path.is_file():
            continue
        if absolute_gguf_matches_bytes(path.read_bytes()):
            leaks.append(relative)
    if leaks:
        raise AssertionError(
            "tracked machine-absolute GGUF path remains in: "
            + ", ".join(sorted(leaks))
        )


def validate_publication_redaction(scan_tracked: bool = True) -> None:
    if not RECEIPT_PATH.is_file():
        raise AssertionError("publication-redaction receipt is missing")
    receipt = load_json_bytes(
        RECEIPT_PATH.read_bytes(),
        "publication-redaction receipt",
    )
    validate_receipt_policy(receipt)

    ancestor = subprocess.run(
        ["git", "merge-base", "--is-ancestor", SOURCE_COMMIT, "HEAD"],
        cwd=ROOT,
        check=False,
        capture_output=True,
    )
    if ancestor.returncode != 0:
        raise AssertionError(
            "publication source commit is unavailable or is not an ancestor; "
            "fetch full history before auditing"
        )

    files = receipt.get("files", {})
    if set(files) != set(REDACTED_FILES):
        raise AssertionError("publication-redaction file inventory mismatch")
    originals: dict[str, bytes] = {}
    published_payloads: dict[str, bytes] = {}
    for relative in REDACTED_FILES:
        source_payload = git_bytes(SOURCE_COMMIT, relative)
        current_path = ROOT / relative
        if not current_path.is_file():
            raise AssertionError(f"published file is missing: {relative}")
        current_payload = current_path.read_bytes()
        record = files[relative]
        if sha256_bytes(source_payload) != record.get("originalSha256"):
            raise AssertionError(f"original file hash mismatch: {relative}")
        if sha256_bytes(current_payload) != record.get("publishedSha256"):
            raise AssertionError(f"published file hash mismatch: {relative}")
        originals[relative] = source_payload
        published_payloads[relative] = current_payload

    validate_runner_transform_pairs(originals, published_payloads, receipt)

    original_prereg = load_json_bytes(originals[PREREG_REL])
    published_prereg = load_json_bytes(
        (ROOT / PREREG_REL).read_bytes(),
        "published preregistration",
    )
    validate_preregistration(original_prereg, published_prereg, receipt)
    source_corpus = git_bytes(SOURCE_COMMIT, CORPUS_REL)
    current_corpus_path = ROOT / CORPUS_REL
    if not current_corpus_path.is_file():
        raise AssertionError("published corpus is missing")
    validate_corpus(
        source_corpus,
        current_corpus_path.read_bytes(),
        str(original_prereg["corpusSha256"]),
    )
    if sha256_text(DIRECT_SYSTEM) != original_prereg["promptSha256"]["directSystem"]:
        raise AssertionError("fixed historical direct prompt hash mismatch")
    if sha256_text(REPAIR_SYSTEM) != original_prereg["promptSha256"]["repairSystem"]:
        raise AssertionError("fixed historical repair prompt hash mismatch")
    source_tasks = load_jsonl_bytes(source_corpus)

    original_raw = load_jsonl_bytes(originals[RAW_REL])
    published_raw = load_jsonl_bytes((ROOT / RAW_REL).read_bytes())
    validate_raw_responses(
        original_raw,
        published_raw,
        receipt,
        str(original_prereg["model"]["id"]),
        source_tasks,
    )

    original_results = load_jsonl_bytes(originals[RESULTS_REL])
    published_results = load_jsonl_bytes((ROOT / RESULTS_REL).read_bytes())
    validate_results(original_results, published_results, receipt)

    original_protocol = load_json_bytes(originals[PROTOCOL_REL])
    published_protocol = load_json_bytes(
        (ROOT / PROTOCOL_REL).read_bytes(),
        "published protocol amendment",
    )
    validate_protocol(original_protocol, published_protocol, receipt)

    original_summary = load_json_bytes(originals[SUMMARY_REL])
    published_summary = load_json_bytes(
        (ROOT / SUMMARY_REL).read_bytes(),
        "published summary",
    )
    validate_summary(original_summary, published_summary, receipt)
    validate_mathematical_receipt(published_summary, receipt)

    prereg_commit = str(published_protocol["originalPreregistrationCommit"])
    registered_prereg = git_bytes(prereg_commit, PREREG_REL)
    if sha256_bytes(registered_prereg) != files[PREREG_REL]["originalSha256"]:
        raise AssertionError("original preregistration commit no longer matches")
    if (
        original_prereg["implementationSha256"]["runner"]
        != files[FROZEN_RUNNER_REL]["originalSha256"]
    ):
        raise AssertionError("historical preregistered runner hash mismatch")
    if (
        original_protocol["amendedRunnerSha256"]
        != files[AMENDED_RUNNER_REL]["originalSha256"]
    ):
        raise AssertionError("historical amended runner hash mismatch")
    if (
        original_protocol["rawResponsesSha256"]
        != files[RAW_REL]["originalSha256"]
    ):
        raise AssertionError("historical frozen raw-response hash mismatch")

    if scan_tracked:
        scan_tracked_absolute_gguf_paths()
    print(
        "model-publication-redaction-valid: source history retained, "
        "360 historical request hashes unchanged, canonical request hashes "
        "current, mathematical results unchanged, no tracked absolute GGUF path"
    )


def main() -> int:
    validate_publication_redaction()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
