#!/usr/bin/env python3
"""Negative regressions for the model-v0.2 publication-redaction checker.

The tests mutate in-memory payloads only.  They deliberately update the
mutable receipt alongside runner mutations to prove that the checker's fixed
source/published byte pairs, rather than a self-declared receipt hash, are the
enforcement boundary.
"""

from __future__ import annotations

import copy
from collections.abc import Callable

import validate_model_publication_redaction as checker


def expect_failure(
    label: str,
    action: Callable[[], None],
    message_fragment: str,
) -> None:
    try:
        action()
    except AssertionError as exception:
        if message_fragment not in str(exception):
            raise AssertionError(
                f"{label} failed for the wrong reason: {exception}"
            ) from exception
        return
    raise AssertionError(f"{label} unexpectedly passed")


def mutate_once(payload: bytes, old: bytes, new: bytes, label: str) -> bytes:
    if payload.count(old) != 1:
        raise AssertionError(f"{label} fixture is not unique")
    return payload.replace(old, new, 1)


def assert_runner_mutation_rejected(
    label: str,
    relative: str,
    mutated_payload: bytes,
    originals: dict[str, bytes],
    published: dict[str, bytes],
    receipt: dict[str, object],
) -> None:
    mutated_published = dict(published)
    mutated_published[relative] = mutated_payload
    mutated_receipt = copy.deepcopy(receipt)
    files = mutated_receipt["files"]
    if not isinstance(files, dict):
        raise AssertionError("receipt file inventory fixture is invalid")
    record = files[relative]
    if not isinstance(record, dict):
        raise AssertionError("receipt runner record fixture is invalid")
    record["publishedSha256"] = checker.sha256_bytes(mutated_payload)
    expect_failure(
        label,
        lambda: checker.validate_runner_transform_pairs(
            originals,
            mutated_published,
            mutated_receipt,
        ),
        "fixed allowlist",
    )


def main() -> int:
    checker.validate_publication_redaction()
    receipt = checker.load_json_bytes(
        checker.RECEIPT_PATH.read_bytes(),
        "publication-redaction receipt",
    )
    if "validatorSha256" in receipt.get("validation", {}):
        raise AssertionError("checker self-hash reappeared in the receipt")
    self_hash_receipt = copy.deepcopy(receipt)
    self_hash_receipt["validation"]["validatorSha256"] = "0" * 64
    expect_failure(
        "checker self-hash",
        lambda: checker.validate_receipt_policy(self_hash_receipt),
        "self-hash",
    )
    receipt_metadata_mutations = {
        "artifact-size": ("modelArtifact", "sizeBytes", 1),
        "artifact-boundary": (
            "modelArtifact",
            "verificationBoundary",
            "not independently verified",
        ),
        "historical-integrity": (
            "historicalIntegrity",
            "historyRewrite",
            True,
        ),
        "mathematical-scope": (
            "mathematicalResultsUnchanged",
            "scope",
            "all results may have changed",
        ),
    }
    for label, (section, field, value) in receipt_metadata_mutations.items():
        mutated = copy.deepcopy(receipt)
        mutated[section][field] = value
        expect_failure(
            f"receipt-{label}",
            lambda mutated=mutated: checker.validate_receipt_policy(mutated),
            "mismatch",
        )
    reason_mutation = copy.deepcopy(receipt)
    reason_mutation["reason"] = "unrelated rewrite"
    expect_failure(
        "receipt-reason",
        lambda: checker.validate_receipt_policy(reason_mutation),
        "reason mismatch",
    )
    extra_file_key = copy.deepcopy(receipt)
    extra_file_key["files"][checker.PREREG_REL]["unvalidated"] = True
    expect_failure(
        "receipt-file-record-extra-key",
        lambda: checker.validate_receipt_policy(extra_file_key),
        "file record schema mismatch",
    )
    duplicate_json_fixtures = {
        "duplicate-prereg-key": b'{"model":{},"model":{}}',
        "duplicate-raw-key": b'{"elapsedMs":1,"elapsedMs":2}\n',
        "duplicate-receipt-key": b'{"version":"first","version":"second"}',
    }
    for label, payload in duplicate_json_fixtures.items():
        loader = (
            checker.load_jsonl_bytes
            if label == "duplicate-raw-key"
            else checker.load_json_bytes
        )
        expect_failure(
            label,
            lambda loader=loader, payload=payload: loader(payload, label),
            "duplicate JSON key",
        )

    originals = {
        relative: checker.git_bytes(checker.SOURCE_COMMIT, relative)
        for relative in checker.EXPECTED_RUNNER_HASHES
    }
    published = {
        relative: (checker.ROOT / relative).read_bytes()
        for relative in checker.EXPECTED_RUNNER_HASHES
    }
    checker.validate_runner_transform_pairs(originals, published, receipt)

    frozen = published[checker.FROZEN_RUNNER_REL]
    runner_mutations = {
        "runner-seed-plus-one": mutate_once(
            frozen,
            b"MODEL_SEED = 20_260_723",
            b"MODEL_SEED = 20_260_724",
            "seed",
        ),
        "runner-prompt-change": mutate_once(
            frozen,
            b"You solve one unit-free cut-free MLL proof-net task.",
            b"You solve exactly one unit-free cut-free MLL proof-net task.",
            "prompt",
        ),
        "runner-request-field-change": mutate_once(
            frozen,
            b'"max_tokens": MODEL_MAX_TOKENS,',
            b'"max_tokens": MODEL_MAX_TOKENS + 1,',
            "request field",
        ),
        "runner-scoring-change": mutate_once(
            frozen,
            (
                b'result["success"] = not bool(task["expectedProvable"]) '
                b"and within_time"
            ),
            (
                b'result["success"] = not bool(task["expectedProvable"]) '
                b"or within_time"
            ),
            "scoring",
        ),
    }
    for label, payload in runner_mutations.items():
        assert_runner_mutation_rejected(
            label,
            checker.FROZEN_RUNNER_REL,
            payload,
            originals,
            published,
            receipt,
        )

    amended = published[checker.AMENDED_RUNNER_REL]
    assert_runner_mutation_rejected(
        "amended-runner-byte-change",
        checker.AMENDED_RUNNER_REL,
        amended + b"\n# unreviewed mutation\n",
        originals,
        published,
        receipt,
    )

    original_prereg = checker.load_json_bytes(
        checker.git_bytes(checker.SOURCE_COMMIT, checker.PREREG_REL)
    )
    source_corpus = checker.git_bytes(checker.SOURCE_COMMIT, checker.CORPUS_REL)
    checker.validate_corpus(
        source_corpus,
        (checker.ROOT / checker.CORPUS_REL).read_bytes(),
        str(original_prereg["corpusSha256"]),
    )
    mutated_corpus = source_corpus.replace(
        b'"id":"model-0-positive"',
        b'"id":"model-X-positive"',
        1,
    )
    if mutated_corpus == source_corpus:
        raise AssertionError("corpus mutation fixture did not change the source")
    expect_failure(
        "published-corpus-mutation",
        lambda: checker.validate_corpus(
            source_corpus,
            mutated_corpus,
            str(original_prereg["corpusSha256"]),
        ),
        "published corpus changed",
    )
    tasks = checker.load_jsonl_bytes(
        source_corpus
    )
    original_raw = checker.load_jsonl_bytes(
        checker.git_bytes(checker.SOURCE_COMMIT, checker.RAW_REL)
    )
    published_raw = checker.load_jsonl_bytes(
        (checker.ROOT / checker.RAW_REL).read_bytes()
    )

    raw_field_mutation = copy.deepcopy(published_raw)
    raw_field_mutation[0]["elapsedMs"] = (
        float(raw_field_mutation[0]["elapsedMs"]) + 1.0
    )
    expect_failure(
        "non-allowed raw field",
        lambda: checker.validate_raw_responses(
            original_raw,
            raw_field_mutation,
            receipt,
            str(original_prereg["model"]["id"]),
            tasks,
        ),
        "raw-response row 0 metadata",
    )

    historical_hash_mutation = copy.deepcopy(published_raw)
    historical_hash_mutation[0]["requestSha256"] = "0" * 64
    expect_failure(
        "historical request hash",
        lambda: checker.validate_raw_responses(
            original_raw,
            historical_hash_mutation,
            receipt,
            str(original_prereg["model"]["id"]),
            tasks,
        ),
        "historical requestSha256 changed at raw row 0",
    )

    file_name = "private-model." + "gguf"
    absolute_fixtures = {
        "windows-drive": "E:" + "\\private\\" + file_name,
        "windows-apostrophe": "C:" + "\\Users\\O'Brien\\models\\" + file_name,
        "posix": "/" + "home/alice/models/" + file_name,
        "posix-apostrophe": "/" + "home/o'brien/models/" + file_name,
        "unc": "\\" + "\\server\\private\\" + file_name,
        "unc-apostrophe": (
            "\\" + "\\server\\O'Brien\\private\\" + file_name
        ),
        "file-posix": "file:" + "///home/alice/models/" + file_name,
        "file-unc": "file:" + "//server/private/" + file_name,
        "json-escaped-posix": (
            "\\" + "/home\\" + "/alice\\" + "/models\\" + "/" + file_name
        ),
    }
    for label, fixture in absolute_fixtures.items():
        if not checker.absolute_gguf_matches(fixture):
            raise AssertionError(f"{label} absolute GGUF path was not detected")
    relative_fixtures = (
        file_name,
        "models/" + file_name,
        "https://example.invalid/models/" + file_name,
    )
    for fixture in relative_fixtures:
        if checker.absolute_gguf_matches(fixture):
            raise AssertionError(f"relative/URL GGUF fixture was a false positive")
    byte_path = "D:" + "\\private\\" + file_name
    byte_fixtures = {
        "utf16-le": byte_path.encode("utf-16"),
        "invalid-utf8-ascii-path": b"\xff\xfeinvalid:" + byte_path.encode("ascii"),
    }
    for label, fixture in byte_fixtures.items():
        if not checker.absolute_gguf_matches_bytes(fixture):
            raise AssertionError(f"{label} absolute GGUF path was not detected")

    print(
        "model-publication-redaction-mutations-ok: checker self-hash rejected, "
        "receipt metadata fixed, duplicate JSON and corpus drift rejected, "
        "runner seed/prompt/request/scoring drift rejected, raw/hash drift "
        "rejected, drive/POSIX/UNC/file/JSON-escaped paths (including "
        "apostrophes and UTF-16/invalid-UTF8 carriers) detected without "
        "relative/HTTP URL false positives"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
