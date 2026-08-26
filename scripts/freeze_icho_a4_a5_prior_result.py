#!/usr/bin/env python3
"""Freeze reviewed A4/A5 answers as a small result file for A6.

The acceptance rule is intentionally narrow: both existing reviewer gates pass,
the current Lean files compile with zero open sorries, and every requested
output contains a concrete non-refusal answer. No independent receipt,
cross-redraft credential, source-contract capability, environment verifier UID,
or axiom audit is involved.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
import subprocess
import sys
import tempfile
import unicodedata
from collections.abc import Callable, Mapping, Sequence
from pathlib import Path
from typing import Any

from archon.commands.loop.prior_result_dependency import (
    SCHEMA_VERSION as PRIOR_RESULT_SCHEMA_VERSION,
    build_prior_result_dependency_context,
    build_validation_lineage_bindings,
    canonical_prior_result_value_sha256,
    validate_prior_result_dependency_context,
    validate_prior_result_dependency_context_self,
)


A3 = "icho_2026_t1_a3"
A4 = "icho_2026_t1_a4"
A5 = "icho_2026_t1_a5"
A6 = "icho_2026_t1_a6"
PRODUCER_IDS = (A4, A5)
CONSUMER_BUNDLE_IDS = (A3, A6)
BUNDLE_REL = Path("icho_2026_source/questions_only.jsonl")
MANIFEST_REL = Path("isolation_manifest.json")
FORMAL_GATE_REL = Path(".archon/formalization-review-gate.json")
PROOF_GATE_REL = Path(".archon/proof-review-gate.json")
EXPECTED_OUTPUTS: dict[str, tuple[tuple[str, str, str], ...]] = {
    A4: (
        ("metal_q_identity", "classification", ""),
        ("hydrated_c_formula", "formula", ""),
        ("compound_d_formula", "formula", ""),
    ),
    A5: (
        ("compound_e_structure", "classification", ""),
        ("compound_f_structure", "classification", ""),
        ("compound_g_structure", "classification", ""),
    ),
}

_SHA_RE = re.compile(r"^[0-9a-f]{64}$", re.ASCII)
_MAX_JSON_BYTES = 16 * 1024 * 1024
_MAX_LEAN_BYTES = 8 * 1024 * 1024
_REFUSAL_MARKERS = (
    "cannot determine", "can't determine", "unable to determine",
    "cannot conclude", "insufficient evidence", "insufficient information",
    "not enough information", "indeterminate", "undetermined", "unknown",
    "fail-closed", "fail closed", "withheld", "no conclusion",
    "无法确定", "不能确定", "无法判断", "不能判断", "证据不足",
    "信息不足", "不足以", "不确定", "拒绝作答", "拒答",
)

CurrentCompileChecker = Callable[[Path, str, str], Mapping[str, Any]]


class FreezePriorResultError(ValueError):
    """The reviewed producer results cannot be frozen."""


def _fail(message: str) -> None:
    raise FreezePriorResultError(message)


def _canonical(value: object) -> bytes:
    try:
        return (
            json.dumps(
                value, ensure_ascii=False, sort_keys=True,
                separators=(",", ":"), allow_nan=False,
            )
            + "\n"
        ).encode("utf-8")
    except (TypeError, ValueError, UnicodeEncodeError, RecursionError) as exc:
        raise FreezePriorResultError("value is not finite canonical JSON") from exc


def _value_sha256(value: object) -> str:
    digest = canonical_prior_result_value_sha256(value)
    if not isinstance(digest, str) or _SHA_RE.fullmatch(digest) is None:
        _fail("core canonical hash is invalid")
    return digest


def _bytes_sha256(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def _sha(value: object, label: str) -> str:
    if not isinstance(value, str) or _SHA_RE.fullmatch(value) is None:
        _fail(f"{label} must be a lowercase SHA-256")
    return value


def _contains_refusal(value: object) -> bool:
    if isinstance(value, str):
        normalized = " ".join(
            unicodedata.normalize("NFKC", value).casefold().split()
        )
        return any(marker in normalized for marker in _REFUSAL_MARKERS)
    if isinstance(value, Mapping):
        return any(_contains_refusal(item) for item in value.values())
    if isinstance(value, Sequence) and not isinstance(
        value, (str, bytes, bytearray)
    ):
        return any(_contains_refusal(item) for item in value)
    return False


def _is_concrete_output(raw_value: object, display_value: object) -> bool:
    if (
        raw_value is None
        or isinstance(raw_value, bool)
        or not isinstance(display_value, str)
        or not display_value.strip()
        or _contains_refusal(raw_value)
        or _contains_refusal(display_value)
    ):
        return False
    if isinstance(raw_value, str):
        return bool(raw_value.strip())
    if isinstance(raw_value, (Mapping, Sequence)) and not isinstance(
        raw_value, (str, bytes, bytearray)
    ):
        return bool(raw_value)
    return True


def _strict_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate JSON key")
        result[key] = value
    return result


def _reject_constant(value: str) -> None:
    raise ValueError(f"non-finite JSON constant {value!r}")


def _read_plain_bytes(path: Path, *, maximum: int, label: str) -> bytes:
    try:
        before = path.lstat()
    except OSError as exc:
        raise FreezePriorResultError(f"{label} is missing: {path}") from exc
    if (
        stat.S_ISLNK(before.st_mode)
        or not stat.S_ISREG(before.st_mode)
        or before.st_nlink != 1
        or before.st_size > maximum
    ):
        _fail(f"{label} is not a bounded unique regular file: {path}")
    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0)
    flags |= getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(path, flags)
    except OSError as exc:
        raise FreezePriorResultError(f"cannot open {label}: {path}") from exc
    try:
        metadata = os.fstat(descriptor)
        if (
            not stat.S_ISREG(metadata.st_mode)
            or metadata.st_nlink != 1
            or metadata.st_size > maximum
            or (metadata.st_dev, metadata.st_ino)
            != (before.st_dev, before.st_ino)
        ):
            _fail(f"{label} changed while being opened: {path}")
        remaining = maximum + 1
        chunks: list[bytes] = []
        while remaining:
            chunk = os.read(descriptor, min(remaining, 1024 * 1024))
            if not chunk:
                break
            chunks.append(chunk)
            remaining -= len(chunk)
        payload = b"".join(chunks)
        if len(payload) > maximum:
            _fail(f"{label} exceeds its byte limit: {path}")
        return payload
    finally:
        os.close(descriptor)


def _parse_json(payload: bytes, *, label: str) -> Any:
    try:
        return json.loads(
            payload.decode("utf-8", "strict"),
            object_pairs_hook=_strict_pairs,
            parse_constant=_reject_constant,
        )
    except (ValueError, UnicodeDecodeError, RecursionError) as exc:
        raise FreezePriorResultError(f"{label} is not strict JSON") from exc


def _read_json(path: Path, *, label: str) -> tuple[dict[str, Any], bytes]:
    payload = _read_plain_bytes(path, maximum=_MAX_JSON_BYTES, label=label)
    value = _parse_json(payload, label=label)
    if not isinstance(value, dict):
        _fail(f"{label} must be a JSON object")
    return value, payload


def _read_jsonl(path: Path, *, label: str) -> tuple[list[dict[str, Any]], bytes]:
    payload = _read_plain_bytes(path, maximum=_MAX_JSON_BYTES, label=label)
    try:
        text = payload.decode("utf-8", "strict")
    except UnicodeDecodeError as exc:
        raise FreezePriorResultError(f"{label} is not UTF-8") from exc
    rows: list[dict[str, Any]] = []
    for index, line in enumerate(text.splitlines(), start=1):
        if not line.strip():
            continue
        value = _parse_json(line.encode("utf-8"), label=f"{label} line {index}")
        if not isinstance(value, dict):
            _fail(f"{label} line {index} must be an object")
        rows.append(value)
    return rows, payload


def _trusted_directory(
    raw: Path, *, label: str, controller_uid: int
) -> Path:
    if raw.is_symlink():
        _fail(f"{label} must not be a symlink")
    try:
        root = raw.resolve(strict=True)
        metadata = root.lstat()
    except OSError as exc:
        raise FreezePriorResultError(f"{label} is missing: {raw}") from exc
    if (
        not stat.S_ISDIR(metadata.st_mode)
        or metadata.st_uid != controller_uid
        or metadata.st_mode & 0o022
    ):
        _fail(f"{label} must be controller-owned and not group/world writable")
    return root


def _target(source_id: str) -> str:
    return f"IChO2026Problems/problem_{source_id}.lean"


def _answer_relative(target: str) -> str:
    stem = target.removesuffix(".lean").replace("/", "_")
    return f".archon/task_results/{stem}.answer.json"


def _validate_manifest(
    root: Path,
    *,
    expected_ids: Sequence[str],
    bundle_sha256: str,
    bundle_size: int,
    label: str,
) -> bytes:
    manifest, payload = _read_json(root / MANIFEST_REL, label=f"{label} manifest")
    target_ids = manifest.get("target_ids")
    blind = manifest.get("blind_bundle")
    if (
        manifest.get("schema_version") != 1
        or manifest.get("protocol") != "icho-problem-only-solver-seed-v1"
        or manifest.get("source_revision_disclosed") is not False
        or target_ids != list(expected_ids)
        or manifest.get("target_ids_sha256") != _value_sha256(list(expected_ids))
        or manifest.get("blind_bundle_sha256") != bundle_sha256
        or not isinstance(blind, Mapping)
        or blind.get("path") != BUNDLE_REL.as_posix()
        or blind.get("row_count") != len(expected_ids)
        or blind.get("sha256") != bundle_sha256
        or blind.get("size") != bundle_size
    ):
        _fail(f"{label} isolation manifest is stale or not answer-blind")
    return payload


def _load_bundle(
    root: Path, *, expected_ids: Sequence[str], label: str
) -> tuple[dict[str, dict[str, Any]], bytes, bytes]:
    rows, payload = _read_jsonl(root / BUNDLE_REL, label=f"{label} bundle")
    ids = [row.get("id") for row in rows]
    if ids != list(expected_ids) or len(ids) != len(set(ids)):
        _fail(f"{label} target order/cardinality is not exact")
    for row in rows:
        if (
            row.get("schema_version") != 1
            or row.get("evaluation_mode") != "answer_blind"
            or row.get("official_answer_seen") is not False
            or row.get("phase") != "solve"
        ):
            _fail(f"{label} row {row.get('id')!r} is not answer-blind")
    digest = _bytes_sha256(payload)
    manifest_payload = _validate_manifest(
        root,
        expected_ids=expected_ids,
        bundle_sha256=digest,
        bundle_size=len(payload),
        label=label,
    )
    return {str(row["id"]): row for row in rows}, payload, manifest_payload


def _problem_pdf_sha256(row: Mapping[str, Any], *, label: str) -> str:
    assets = row.get("problem_assets")
    if not isinstance(assets, list):
        _fail(f"{label} has no problem asset ledger")
    hashes = [
        item.get("sha256")
        for item in assets
        if isinstance(item, Mapping) and item.get("kind") == "problem_pdf"
    ]
    if len(hashes) != 1:
        _fail(f"{label} must bind exactly one problem PDF")
    return _sha(hashes[0], f"{label} problem PDF hash")


def _previous_part_ids(row: Mapping[str, Any], *, label: str) -> list[str]:
    previous = row.get("previous_parts")
    if not isinstance(previous, list):
        _fail(f"{label} previous_parts must be a list")
    result: list[str] = []
    for index, item in enumerate(previous):
        if not isinstance(item, Mapping) or not isinstance(item.get("source_id"), str):
            _fail(f"{label} previous_parts[{index}] is invalid")
        result.append(str(item["source_id"]))
    if len(result) != len(set(result)):
        _fail(f"{label} previous_parts contains duplicates")
    return result


def _validate_requested_output_contract(
    row: Mapping[str, Any], *, source_id: str
) -> None:
    values = row.get("requested_outputs")
    expected = EXPECTED_OUTPUTS[source_id]
    if not isinstance(values, list) or len(values) != len(expected):
        _fail(f"{source_id} requested-output count is not exact")
    observed: list[tuple[object, object, object]] = []
    for value in values:
        if not isinstance(value, Mapping):
            _fail(f"{source_id} requested output is not an object")
        observed.append((value.get("id"), value.get("kind"), value.get("unit")))
    if observed != list(expected):
        _fail(f"{source_id} requested-output inventory drifted")


def _validate_answer(
    workspace: Path,
    *,
    source_id: str,
    target: str,
    expected_sha256: str,
) -> list[dict[str, Any]]:
    path = workspace / _answer_relative(target)
    answer, payload = _read_json(path, label=f"{source_id} answer submission")
    if _bytes_sha256(payload) != expected_sha256:
        _fail(f"{source_id} answer submission hash is stale")
    if set(answer) != {"schema_version", "id", "official_answer_seen", "outputs"}:
        _fail(f"{source_id} answer submission has unexpected fields")
    if (
        answer.get("schema_version") != 1
        or answer.get("id") != source_id
        or answer.get("official_answer_seen") is not False
    ):
        _fail(f"{source_id} answer submission is not blind/exact")
    outputs = answer.get("outputs")
    expected = EXPECTED_OUTPUTS[source_id]
    if not isinstance(outputs, list) or len(outputs) != len(expected):
        _fail(f"{source_id} answer output count is not exact")
    normalized: list[dict[str, Any]] = []
    observed: list[tuple[object, object, object]] = []
    for index, output in enumerate(outputs):
        if not isinstance(output, Mapping) or set(output) != {
            "id", "kind", "raw_value", "display_value", "unit"
        }:
            _fail(f"{source_id} answer outputs[{index}] has invalid fields")
        observed.append((output.get("id"), output.get("kind"), output.get("unit")))
        raw_value = output.get("raw_value")
        display_value = output.get("display_value")
        _canonical(raw_value)
        if not _is_concrete_output(raw_value, display_value):
            _fail(
                f"{source_id} answer outputs[{index}] is not a concrete "
                "non-refusal answer"
            )
        normalized.append({
            "output_id": output["id"],
            "kind": output["kind"],
            "raw_value": raw_value,
            "display_value": display_value,
            "unit": output["unit"],
        })
    if observed != list(expected):
        _fail(f"{source_id} answer output inventory/order drifted")
    return normalized


def _gate_targets(
    gate: Mapping[str, Any], *, expected_targets: Sequence[str], label: str
) -> Mapping[str, Any]:
    targets = gate.get("targets")
    if not isinstance(targets, Mapping) or set(targets) != set(expected_targets):
        _fail(f"{label} does not contain exactly the A4/A5 targets")
    return targets


def _simple_compile_audit(
    value: object, *, source_id: str, target: str, candidate_sha256: str
) -> dict[str, Any]:
    fields = {
        "schema_version", "kind", "target", "candidate_sha256", "source_size",
        "status", "compiles", "returncode", "sorry_count",
        "stdout_sha256", "stderr_sha256",
    }
    if not isinstance(value, Mapping) or set(value) != fields:
        _fail(f"{source_id} current compile audit has invalid fields")
    if (
        value.get("schema_version") != 1
        or value.get("kind") != "current_exact_source_compile_sorry_audit"
        or value.get("target") != target
        or value.get("candidate_sha256") != candidate_sha256
        or type(value.get("source_size")) is not int
        or value.get("source_size") < 1
        or value.get("status") != "passed"
        or value.get("compiles") is not True
        or type(value.get("returncode")) is not int
        or value.get("returncode") != 0
        or type(value.get("sorry_count")) is not int
        or value.get("sorry_count") != 0
    ):
        _fail(f"{source_id} current Lean compile/zero-sorry check failed")
    _sha(value.get("stdout_sha256"), f"{source_id} compile stdout hash")
    _sha(value.get("stderr_sha256"), f"{source_id} compile stderr hash")
    return {
        "status": "passed",
        "candidate_sha256": candidate_sha256,
        "returncode": 0,
        "sorry_count": 0,
    }


def build_frozen_prior_result(
    *,
    producer_workspace: Path,
    producer_seed: Path,
    consumer_seed: Path,
    producer_inventory_sha256: str,
    consumer_inventory_sha256: str,
    current_compile_checker: CurrentCompileChecker,
    controller_uid: int | None = None,
) -> dict[str, Any]:
    """Build the minimal A4/A5 result object."""

    uid = os.geteuid() if controller_uid is None else controller_uid
    if type(uid) is not int or uid < 0:
        _fail("controller UID is invalid")
    workspace = _trusted_directory(
        Path(producer_workspace), label="producer workspace", controller_uid=uid
    )
    producer_seed = _trusted_directory(
        Path(producer_seed), label="producer seed", controller_uid=uid
    )
    consumer_seed = _trusted_directory(
        Path(consumer_seed), label="consumer seed", controller_uid=uid
    )
    producer_inventory_sha256 = _sha(
        producer_inventory_sha256, "producer inventory hash"
    )
    consumer_inventory_sha256 = _sha(
        consumer_inventory_sha256, "consumer inventory hash"
    )

    producer_rows, producer_bundle, producer_manifest = _load_bundle(
        producer_seed, expected_ids=PRODUCER_IDS, label="producer seed"
    )
    workspace_rows, workspace_bundle, workspace_manifest = _load_bundle(
        workspace, expected_ids=PRODUCER_IDS, label="producer workspace"
    )
    if (
        workspace_bundle != producer_bundle
        or workspace_manifest != producer_manifest
        or workspace_rows != producer_rows
    ):
        _fail("producer workspace source projection differs from its seed")
    consumer_rows, consumer_bundle, _consumer_manifest = _load_bundle(
        consumer_seed, expected_ids=CONSUMER_BUNDLE_IDS, label="consumer seed"
    )
    producer_bundle_sha256 = _bytes_sha256(producer_bundle)
    consumer_bundle_sha256 = _bytes_sha256(consumer_bundle)

    for source_id in PRODUCER_IDS:
        _validate_requested_output_contract(
            producer_rows[source_id], source_id=source_id
        )
    consumer = consumer_rows[A6]
    if _previous_part_ids(consumer, label=A6) != list(PRODUCER_IDS):
        _fail("A6 does not depend on exact ordered A4/A5")
    problem_id = consumer.get("problem_id")
    shared_context = consumer.get("shared_context")
    if not isinstance(problem_id, str) or not problem_id:
        _fail("A6 problem_id is missing")
    if not isinstance(shared_context, str) or not shared_context:
        _fail("A6 shared_context is missing")
    pdf_sha256 = _problem_pdf_sha256(consumer, label=A6)
    for source_id in PRODUCER_IDS:
        row = producer_rows[source_id]
        if (
            row.get("problem_id") != problem_id
            or _problem_pdf_sha256(row, label=source_id) != pdf_sha256
        ):
            _fail(f"{source_id} is not in the exact A6 source lineage")

    bindings = build_validation_lineage_bindings(
        problem_id=problem_id,
        problem_pdf_sha256=pdf_sha256,
        shared_context_sha256=_value_sha256(shared_context),
        producer_bundle_sha256=producer_bundle_sha256,
        consumer_bundle_sha256=consumer_bundle_sha256,
        producer_inventory_sha256=producer_inventory_sha256,
        consumer_inventory_sha256=consumer_inventory_sha256,
    )
    if set(bindings) != {"producer", "consumer"}:
        _fail("could not build the A4/A5-to-A6 source binding")

    formal_gate, formal_gate_payload = _read_json(
        workspace / FORMAL_GATE_REL, label="formalization review gate"
    )
    proof_gate, proof_gate_payload = _read_json(
        workspace / PROOF_GATE_REL, label="proof review gate"
    )
    targets = tuple(_target(source_id) for source_id in PRODUCER_IDS)
    formal_targets = _gate_targets(
        formal_gate, expected_targets=targets, label="formalization review gate"
    )
    proof_targets = _gate_targets(
        proof_gate, expected_targets=targets, label="proof review gate"
    )

    snapshots: list[dict[str, Any]] = []
    frozen_files: list[tuple[Path, bytes, int, str]] = []
    for source_id, target in zip(PRODUCER_IDS, targets, strict=True):
        formal_record = formal_targets[target]
        proof_record = proof_targets[target]
        if (
            not isinstance(formal_record, Mapping)
            or formal_record.get("status") != "passed"
        ):
            _fail(f"{source_id} did not pass formalization semantic review")
        if (
            not isinstance(proof_record, Mapping)
            or proof_record.get("status") != "solved"
            or proof_record.get("proof_review_route") not in {None, "solved"}
        ):
            _fail(f"{source_id} did not pass proof semantic review")

        module_path = workspace / target
        module_payload = _read_plain_bytes(
            module_path, maximum=_MAX_LEAN_BYTES,
            label=f"{source_id} Lean module",
        )
        module_sha256 = _bytes_sha256(module_payload)
        if proof_record.get("candidate_sha256") != module_sha256:
            _fail(f"{source_id} proof review is stale for current Lean bytes")

        answer_path = workspace / _answer_relative(target)
        answer_bytes = _read_plain_bytes(
            answer_path, maximum=_MAX_JSON_BYTES,
            label=f"{source_id} answer submission",
        )
        payloads = _validate_answer(
            workspace, source_id=source_id, target=target,
            expected_sha256=_bytes_sha256(answer_bytes),
        )
        try:
            compile_value = current_compile_checker(
                workspace, target, module_sha256
            )
        except FreezePriorResultError:
            raise
        except Exception as exc:
            raise FreezePriorResultError(
                f"{source_id} current Lean compile check did not run"
            ) from exc
        compile_audit = _simple_compile_audit(
            compile_value, source_id=source_id, target=target,
            candidate_sha256=module_sha256,
        )

        typed_exports = [{
            "export_id": (
                f"certified_prior_result:{source_id}:{payload['output_id']}"
            ),
            "result_payload": payload,
            "result_payload_sha256": _value_sha256(payload),
        } for payload in payloads]
        previous_ids = _previous_part_ids(
            producer_rows[source_id], label=source_id
        )
        snapshots.append({
            "schema_version": PRIOR_RESULT_SCHEMA_VERSION,
            "controller_binding": bindings["producer"],
            "source_id": source_id,
            "source_record_sha256": _value_sha256(
                producer_rows[source_id]
            ),
            "previous_part_source_ids": previous_ids,
            "previous_part_source_ids_sha256": _value_sha256(previous_ids),
            "source_bundle_sha256": producer_bundle_sha256,
            "answer_submission_sha256": _bytes_sha256(answer_bytes),
            "official_answer_seen": False,
            "module": target,
            "module_sha256": module_sha256,
            "formalization_review": {"status": "passed"},
            "proof_review": {"status": "solved"},
            "compile_audit": compile_audit,
            "typed_exports": typed_exports,
        })
        frozen_files.extend((
            (module_path, module_payload, _MAX_LEAN_BYTES,
             f"{source_id} Lean module"),
            (answer_path, answer_bytes, _MAX_JSON_BYTES,
             f"{source_id} answer submission"),
        ))

    consumer_record_sha256 = _value_sha256(consumer)
    receipt = build_prior_result_dependency_context(
        consumer_target=_target(A6),
        consumer_source_record=consumer,
        consumer_source_record_sha256=consumer_record_sha256,
        consumer_controller_binding=bindings["consumer"],
        producer_snapshots=snapshots,
    )
    if not receipt:
        _fail("result builder rejected A4/A5")
    error = validate_prior_result_dependency_context_self(receipt)
    if error:
        _fail(f"result builder returned invalid JSON: {error}")
    error = validate_prior_result_dependency_context(
        receipt,
        consumer_target=_target(A6),
        consumer_source_record=consumer,
        consumer_source_record_sha256=consumer_record_sha256,
        consumer_controller_binding=bindings["consumer"],
        producer_snapshots=snapshots,
    )
    if error:
        _fail(f"A4/A5 results changed during freeze: {error}")

    for path, expected, maximum, label in frozen_files:
        if _read_plain_bytes(
            path, maximum=maximum, label=f"final {label} recheck"
        ) != expected:
            _fail(f"{label} changed during freeze")
    for relative, expected, label in (
        (FORMAL_GATE_REL, formal_gate_payload, "formalization review gate"),
        (PROOF_GATE_REL, proof_gate_payload, "proof review gate"),
    ):
        if _read_plain_bytes(
            workspace / relative, maximum=_MAX_JSON_BYTES,
            label=f"final {label} recheck",
        ) != expected:
            _fail(f"{label} changed during freeze")
    return receipt


def _write_exclusive_bytes(path: Path, payload: bytes) -> None:
    descriptor = os.open(
        path,
        os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_CLOEXEC", 0),
        0o600,
    )
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
    except BaseException:
        try:
            os.close(descriptor)
        except OSError:
            pass
        raise


def lean_current_compile_audit(
    workspace: Path,
    target: str,
    expected_sha256: str,
    *,
    lake_bin: Path,
    timeout_seconds: int = 120,
) -> Mapping[str, Any]:
    """Compile exact final bytes and count open sorries."""

    expected_sha256 = _sha(expected_sha256, "compile candidate hash")
    payload = _read_plain_bytes(
        workspace / target, maximum=_MAX_LEAN_BYTES, label="compile target"
    )
    if not payload or _bytes_sha256(payload) != expected_sha256:
        _fail("compile target hash is stale/empty")
    with tempfile.TemporaryDirectory(prefix="icho-a4-a5-compile-") as raw:
        probe = Path(raw) / Path(target).name
        _write_exclusive_bytes(probe, payload)
        from archon.commands.loop.sorry_count import file_open_sorry_count
        sorry_count = file_open_sorry_count(probe)
        try:
            completed = subprocess.run(
                [str(lake_bin), "env", "lean", str(probe)],
                cwd=workspace, check=False, stdin=subprocess.PIPE,
                capture_output=True, timeout=timeout_seconds,
                env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"},
            )
        except (OSError, subprocess.TimeoutExpired) as exc:
            raise FreezePriorResultError(
                "current Lean compile/zero-sorry check did not run"
            ) from exc
        if _read_plain_bytes(
            probe, maximum=_MAX_LEAN_BYTES,
            label="compile probe postcheck",
        ) != payload:
            _fail("compile probe changed during check")
    if _read_plain_bytes(
        workspace / target, maximum=_MAX_LEAN_BYTES,
        label="compile target postcheck",
    ) != payload:
        _fail("compile target changed during check")
    if type(sorry_count) is not int:
        _fail("current exact-source sorry count is unknown")
    passed = completed.returncode == 0 and sorry_count == 0
    return {
        "schema_version": 1,
        "kind": "current_exact_source_compile_sorry_audit",
        "target": target,
        "candidate_sha256": expected_sha256,
        "source_size": len(payload),
        "status": "passed" if passed else "failed",
        "compiles": completed.returncode == 0,
        "returncode": completed.returncode,
        "sorry_count": sorry_count,
        "stdout_sha256": _bytes_sha256(completed.stdout),
        "stderr_sha256": _bytes_sha256(completed.stderr),
    }


def _trusted_executable(path: Path, *, label: str, controller_uid: int) -> Path:
    if not path.is_absolute() or path.is_symlink():
        _fail(f"{label} must be an absolute non-symlink path")
    try:
        resolved = path.resolve(strict=True)
        metadata = resolved.lstat()
    except OSError as exc:
        raise FreezePriorResultError(f"{label} is missing") from exc
    if (
        not stat.S_ISREG(metadata.st_mode)
        or metadata.st_nlink != 1
        or metadata.st_uid != controller_uid
        or metadata.st_mode & 0o022
        or not os.access(resolved, os.X_OK)
    ):
        _fail(f"{label} must be controller-owned, unique, executable, and read-only")
    return resolved


def write_staged_receipt(
    output: Path,
    receipt: Mapping[str, Any],
    *,
    controller_uid: int | None = None,
) -> str:
    """Atomically write canonical controller-owned 0600 staging bytes."""

    uid = os.geteuid() if controller_uid is None else controller_uid
    error = validate_prior_result_dependency_context_self(receipt)
    if error:
        _fail(f"refusing to write an invalid receipt: {error}")
    output = Path(output)
    parent = output.parent
    parent.mkdir(mode=0o700, parents=True, exist_ok=True)
    parent = _trusted_directory(parent, label="receipt output directory", controller_uid=uid)
    output = parent / output.name
    if output.exists() or output.is_symlink():
        _fail("staged receipt output already exists")
    payload = _canonical(dict(receipt))
    descriptor, raw_tmp = tempfile.mkstemp(prefix=f".{output.name}.", dir=parent)
    temporary = Path(raw_tmp)
    try:
        os.fchmod(descriptor, 0o600)
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        metadata = temporary.lstat()
        if (
            not stat.S_ISREG(metadata.st_mode)
            or metadata.st_nlink != 1
            or metadata.st_uid != uid
            or stat.S_IMODE(metadata.st_mode) != 0o600
        ):
            _fail("temporary receipt is not controller-owned 0600")
        if output.exists() or output.is_symlink():
            _fail("staged receipt output appeared during write")
        os.replace(temporary, output)
        directory_fd = os.open(parent, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
        try:
            os.fsync(directory_fd)
        finally:
            os.close(directory_fd)
    finally:
        temporary.unlink(missing_ok=True)
    metadata = output.lstat()
    if (
        not stat.S_ISREG(metadata.st_mode)
        or metadata.st_nlink != 1
        or metadata.st_uid != uid
        or stat.S_IMODE(metadata.st_mode) != 0o600
        or output.read_bytes() != payload
    ):
        _fail("staged receipt post-write verification failed")
    return _bytes_sha256(payload)


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--producer-workspace", type=Path, required=True)
    parser.add_argument("--producer-seed", type=Path, required=True)
    parser.add_argument("--consumer-seed", type=Path, required=True)
    parser.add_argument("--producer-inventory-sha256", required=True)
    parser.add_argument("--consumer-inventory-sha256", required=True)
    parser.add_argument("--lake-bin", type=Path, required=True)
    parser.add_argument("--axiom-checker", type=Path, help=argparse.SUPPRESS)
    parser.add_argument("--lean-timeout-seconds", type=int, default=120)
    parser.add_argument("--output", type=Path, required=True)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    arguments = _parser().parse_args(argv)
    try:
        if os.geteuid() != 0:
            _fail("controller freezer must run as root")
        if arguments.lean_timeout_seconds < 1:
            _fail("Lean timeout must be positive")
        lake_bin = _trusted_executable(
            arguments.lake_bin, label="--lake-bin", controller_uid=0
        )

        def compile_checker(
            workspace: Path, target: str, candidate_sha256: str
        ) -> Mapping[str, Any]:
            return lean_current_compile_audit(
                workspace, target, candidate_sha256, lake_bin=lake_bin,
                timeout_seconds=arguments.lean_timeout_seconds,
            )

        receipt = build_frozen_prior_result(
            producer_workspace=arguments.producer_workspace,
            producer_seed=arguments.producer_seed,
            consumer_seed=arguments.consumer_seed,
            producer_inventory_sha256=arguments.producer_inventory_sha256,
            consumer_inventory_sha256=arguments.consumer_inventory_sha256,
            current_compile_checker=compile_checker,
            controller_uid=0,
        )
        file_sha256 = write_staged_receipt(
            arguments.output, receipt, controller_uid=0
        )
        print(json.dumps({
            "status": "a4_a5_results_staged",
            "output": str(arguments.output.resolve()),
            "mode": "0600",
            "consumer": A6,
            "producers": list(PRODUCER_IDS),
            "receipt_sha256": receipt["receipt_sha256"],
            "file_sha256": file_sha256,
        }, sort_keys=True))
        return 0
    except FreezePriorResultError as exc:
        print(f"FATAL: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
