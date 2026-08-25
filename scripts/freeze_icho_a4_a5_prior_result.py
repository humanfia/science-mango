#!/usr/bin/env python3
"""Freeze hard-green IChO T1-A4/A5 results for the single T1-A6 consumer.

This is a controller-only operation.  It reads the stopped producer campaign,
checks the exact formal/proof/compile/axiom/answer artifacts, asks Lean for the
type of one deterministic primary result declaration per requested output,
and delegates receipt construction to ``prior_result_dependency``.

The resulting file is a controller staging artifact (0600).  The stage-2
installer is responsible for copying its canonical bytes into the consumer
workspace as a root-owned 0444 receipt before ``physics-formalize`` starts.
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
from collections.abc import Callable, Mapping, Sequence
from pathlib import Path
from typing import Any

from archon.commands.loop.prior_result_dependency import (
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

# This inventory is intentionally duplicated at the controller boundary.  A
# changed bundle contract must fail closed rather than silently changing what
# A6 inherits.
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
_DECL_RE = re.compile(
    r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$",
    re.ASCII,
)
_ANSI_RE = re.compile(r"\x1b\[[0-9;]*m")
_AXIOM_FINDING_RE = re.compile(
    r"⚠\s+(?P<decl>[A-Za-z0-9_.]+)\s+uses non-standard axiom:\s+(?P<axiom>[A-Za-z0-9_.]+)"
)
_MAX_JSON_BYTES = 16 * 1024 * 1024
_MAX_LEAN_BYTES = 8 * 1024 * 1024
_MAX_TYPE_BYTES = 16 * 1024

DeclarationTypeChecker = Callable[
    [Path, str, str, Sequence[str]], Mapping[str, str]
]
CurrentCompileChecker = Callable[[Path, str, str], Mapping[str, Any]]
CurrentAxiomChecker = Callable[[Path, str, str], Mapping[str, Any]]
UidProcessChecker = Callable[[int], bool]


class FreezePriorResultError(ValueError):
    """The producer artifacts cannot be frozen into a trusted receipt."""


def _fail(message: str) -> None:
    raise FreezePriorResultError(message)


def _canonical(value: object) -> bytes:
    try:
        return (
            json.dumps(
                value,
                ensure_ascii=False,
                sort_keys=True,
                separators=(",", ":"),
                allow_nan=False,
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
        if (
            raw_value is None
            or not isinstance(display_value, str)
            or not display_value.strip()
        ):
            _fail(f"{source_id} answer outputs[{index}] has no exact value")
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


def _validate_source_contract(
    value: object,
    *,
    source_id: str,
    target: str,
    candidate_sha256: str,
    bundle_sha256: str,
    source_record_sha256: str,
    answer_sha256: str,
) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        _fail(f"{source_id} review has no source contract")
    expected = {
        "schema_version": 1,
        "contract_kind": "native_problem_input_only",
        "authority": "problem-only",
        "evaluation_mode": "answer_blind",
        "target": target,
        "source_bundle": BUNDLE_REL.as_posix(),
        "source_bundle_sha256": bundle_sha256,
        "source_record_id": source_id,
        "source_record_sha256": source_record_sha256,
        "answer_submission": _answer_relative(target),
        "answer_submission_sha256": answer_sha256,
        "candidate": target,
        "candidate_sha256": candidate_sha256,
    }
    for key, expected_value in expected.items():
        if value.get(key) != expected_value:
            _fail(f"{source_id} source contract is stale: {key}")
    return value


def _gate_targets(
    gate: Mapping[str, Any], *, expected_targets: Sequence[str], label: str
) -> Mapping[str, Any]:
    targets = gate.get("targets")
    if not isinstance(targets, Mapping) or set(targets) != set(expected_targets):
        _fail(f"{label} does not contain exactly the A4/A5 targets")
    return targets


def _certificate_requested_outputs(certificate: Mapping[str, Any]) -> object:
    direct = certificate.get("requested_outputs")
    if direct is not None:
        return direct
    nested = certificate.get("blind_review_certificate")
    return nested.get("requested_outputs") if isinstance(nested, Mapping) else None


def _primary_result_declarations(
    certificate: Mapping[str, Any], *, source_id: str
) -> dict[str, str]:
    independent = certificate.get("independent_rederivation")
    if not isinstance(independent, Mapping):
        _fail(f"{source_id} formal certificate has no independent rederivation")
    entries = independent.get("requested_outputs")
    expected_ids = [item[0] for item in EXPECTED_OUTPUTS[source_id]]
    if not isinstance(entries, list) or [
        entry.get("id") if isinstance(entry, Mapping) else None for entry in entries
    ] != expected_ids:
        _fail(f"{source_id} formal output derivations are incomplete/out of order")
    result: dict[str, str] = {}
    all_declarations: set[str] = set()
    for entry in entries:
        assert isinstance(entry, Mapping)
        carriers = entry.get("lean_carriers")
        reported = carriers.get("reported_result") if isinstance(carriers, Mapping) else None
        if (
            not isinstance(reported, list)
            or not reported
            or len(reported) != len(set(map(str, reported)))
            or any(
                not isinstance(item, str) or _DECL_RE.fullmatch(item) is None
                for item in reported
            )
        ):
            _fail(f"{source_id} output {entry.get('id')} has invalid reported_result")
        primary = reported[0]
        if primary in all_declarations:
            _fail(f"{source_id} primary result declaration is shared by two outputs")
        all_declarations.update(reported)
        result[str(entry["id"])] = primary

    covered = _certificate_requested_outputs(certificate)
    if not isinstance(covered, list) or [
        item.get("output_id") if isinstance(item, Mapping) else None
        for item in covered
    ] != expected_ids:
        _fail(f"{source_id} formal requested-output audit is incomplete")
    for item in covered:
        assert isinstance(item, Mapping)
        if (
            item.get("status") not in {"covered", "passed"}
            or item.get("submission_status") != "matched"
            or item.get("reporting_policy_status") != "matched"
        ):
            _fail(f"{source_id} requested output did not pass formal audit")
    return result


def _validate_no_answer_key_fields(value: Mapping[str, Any], *, label: str) -> None:
    for key in ("official_answer_alignment", "source_inconsistency"):
        if value.get(key) is not None:
            _fail(f"{label} unexpectedly carries {key}")


def _compile_audit(
    proof_record: Mapping[str, Any], *, source_id: str, candidate_sha256: str
) -> dict[str, Any]:
    iteration = proof_record.get("last_review_iter")
    events = proof_record.get("repair_events")
    if type(iteration) is not int or iteration < 1 or not isinstance(events, list):
        _fail(f"{source_id} proof has no final compile event")
    matching = [
        event for event in events
        if isinstance(event, Mapping)
        and event.get("iteration") == iteration
        and event.get("candidate_sha256") == candidate_sha256
        and event.get("resulting_status") == "solved"
    ]
    if len(matching) != 1:
        _fail(f"{source_id} proof has no unique solved compile event")
    preflight = matching[0].get("preflight")
    if not isinstance(preflight, Mapping):
        _fail(f"{source_id} solved event has no preflight")
    if (
        preflight.get("status") != "passed"
        or preflight.get("compiles") is not True
        or type(preflight.get("returncode")) is not int
        or preflight.get("returncode") != 0
        or type(preflight.get("sorry_count")) is not int
        or preflight.get("sorry_count") != 0
    ):
        _fail(f"{source_id} compile/sorry preflight is not hard-green")
    return {
        "status": "passed",
        "candidate_sha256": candidate_sha256,
        "audit_sha256": _value_sha256(dict(preflight)),
        "returncode": 0,
        "sorry_count": 0,
    }


def _axiom_audit(
    workspace: Path,
    proof_record: Mapping[str, Any],
    *,
    source_id: str,
    target: str,
    candidate_sha256: str,
) -> dict[str, Any]:
    iteration = proof_record.get("last_review_iter")
    if type(iteration) is not int or iteration < 1:
        _fail(f"{source_id} has no valid proof iteration for axiom audit")
    path = workspace / ".archon/logs" / f"iter-{iteration:03d}" / "axiom-sweep.json"
    audit, payload = _read_json(path, label=f"{source_id} axiom audit")
    target_files = audit.get("targetFiles")
    failed_files = audit.get("failedFiles")
    laundering = audit.get("sorryLaunderings")
    nonstandard = audit.get("otherNonStandardAxioms")
    if (
        audit.get("ran") is not True
        or audit.get("error") is not None
        or not isinstance(target_files, list)
        or not target_files
        or len(target_files) != len(set(target_files))
        or target not in target_files
        or type(audit.get("filesChecked")) is not int
        or audit.get("filesChecked") != len(target_files)
        or failed_files != []
        or laundering != []
        or nonstandard != []
    ):
        _fail(f"{source_id} axiom audit did not cleanly cover the exact target")
    return {
        "status": "passed",
        "candidate_sha256": candidate_sha256,
        "audit_sha256": _bytes_sha256(payload),
        "sorry_launderings": [],
        "nonstandard_axioms": [],
    }


def _current_compile_audit(
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
        _fail(f"{source_id} current compile/sorry audit is not hard-green")
    _sha(value.get("stdout_sha256"), f"{source_id} compile stdout hash")
    _sha(value.get("stderr_sha256"), f"{source_id} compile stderr hash")
    return {
        "status": "passed",
        "candidate_sha256": candidate_sha256,
        "audit_sha256": _value_sha256(dict(value)),
        "returncode": 0,
        "sorry_count": 0,
    }


def _current_axiom_audit(
    value: object, *, source_id: str, target: str, candidate_sha256: str
) -> dict[str, Any]:
    fields = {
        "schema_version", "kind", "target", "candidate_sha256", "status",
        "ran", "returncode", "files_checked", "declarations_checked",
        "target_files", "failed_files", "sorry_launderings",
        "nonstandard_axioms", "stdout_sha256", "stderr_sha256",
    }
    if not isinstance(value, Mapping) or set(value) != fields:
        _fail(f"{source_id} current axiom audit has invalid fields")
    if (
        value.get("schema_version") != 1
        or value.get("kind") != "current_exact_source_axiom_audit"
        or value.get("target") != target
        or value.get("candidate_sha256") != candidate_sha256
        or value.get("status") != "passed"
        or value.get("ran") is not True
        or type(value.get("returncode")) is not int
        or value.get("returncode") != 0
        or type(value.get("files_checked")) is not int
        or value.get("files_checked") != 1
        or type(value.get("declarations_checked")) is not int
        or value.get("declarations_checked") < 1
        or value.get("target_files") != [target]
        or value.get("failed_files") != []
        or value.get("sorry_launderings") != []
        or value.get("nonstandard_axioms") != []
    ):
        _fail(f"{source_id} current axiom audit is not hard-green/exact")
    _sha(value.get("stdout_sha256"), f"{source_id} axiom stdout hash")
    _sha(value.get("stderr_sha256"), f"{source_id} axiom stderr hash")
    return {
        "status": "passed",
        "candidate_sha256": candidate_sha256,
        "audit_sha256": _value_sha256(dict(value)),
        "sorry_launderings": [],
        "nonstandard_axioms": [],
    }


def _validate_terminal_campaign(
    workspace: Path, *, producer_bundle_sha256: str
) -> tuple[dict[str, Any], bytes]:
    campaign, payload = _read_json(
        workspace.parent / "campaign.json", label="producer terminal campaign"
    )
    native = campaign.get("native")
    grounding = campaign.get("grounding")
    if (
        campaign.get("schema_version") != 1
        or campaign.get("pipeline") != "archon-native-answer-blind-full32"
        or campaign.get("workspace") != str(workspace)
        or type(campaign.get("row_count")) is not int
        or campaign.get("row_count") != 2
        or campaign.get("bundle_sha256") != producer_bundle_sha256
        or campaign.get("target_lifecycle") is not True
        or campaign.get("status") != "succeeded"
        or campaign.get("phase") not in {"loop", "complete"}
        or type(campaign.get("returncode")) is not int
        or campaign.get("returncode") != 0
        or not isinstance(grounding, Mapping)
        or type(grounding.get("complete")) is not int
        or grounding.get("complete") != 2
        or not isinstance(native, Mapping)
        or native.get("complete") is not True
        or native.get("formalization_review") != {"passed": 2}
        or native.get("proof_review") != {"solved": 2}
        or native.get("lake_build_ok") is not True
        or type(native.get("sorry_count")) is not int
        or native.get("sorry_count") != 0
    ):
        _fail("producer campaign is not terminal hard-green for exact A4/A5")
    return campaign, payload


def _uid_has_process(uid: int) -> bool:
    """Return whether any current Linux process carries the dedicated UID."""

    if type(uid) is not int or uid < 0:
        _fail("solver UID is invalid")
    proc = Path("/proc")
    try:
        entries = tuple(proc.iterdir())
    except OSError as exc:
        raise FreezePriorResultError("cannot audit dedicated solver processes") from exc
    for entry in entries:
        if not entry.name.isdigit():
            continue
        try:
            status_payload = (entry / "status").read_text(
                encoding="utf-8", errors="strict"
            )
        except FileNotFoundError:
            continue
        except (OSError, UnicodeError) as exc:
            raise FreezePriorResultError(
                "cannot audit dedicated solver process status"
            ) from exc
        uid_line = next(
            (line for line in status_payload.splitlines() if line.startswith("Uid:")),
            None,
        )
        if uid_line is None:
            _fail("dedicated solver process has no UID ledger")
        values = uid_line.removeprefix("Uid:").split()
        if len(values) != 4 or any(not value.isdigit() for value in values):
            _fail("dedicated solver process UID ledger is invalid")
        if uid in {int(value) for value in values}:
            return True
    return False


def _require_solver_quiescent(
    solver_uid: int, checker: UidProcessChecker, *, stage: str
) -> None:
    if type(solver_uid) is not int or solver_uid < 0:
        _fail("solver UID is invalid")
    try:
        active = checker(solver_uid)
    except FreezePriorResultError:
        raise
    except Exception as exc:
        raise FreezePriorResultError(
            f"cannot check solver quiescence {stage}"
        ) from exc
    if type(active) is not bool:
        _fail("solver process checker returned a non-boolean result")
    if active:
        _fail(f"dedicated solver UID still has a process {stage}")


def _review_and_exports(
    workspace: Path,
    *,
    source_id: str,
    source_row: Mapping[str, Any],
    producer_bundle_sha256: str,
    formal_record: Mapping[str, Any],
    proof_record: Mapping[str, Any],
    declaration_type_checker: DeclarationTypeChecker,
    current_compile_checker: CurrentCompileChecker,
    current_axiom_checker: CurrentAxiomChecker,
) -> dict[str, Any]:
    target = _target(source_id)
    module_payload = _read_plain_bytes(
        workspace / target, maximum=_MAX_LEAN_BYTES, label=f"{source_id} Lean module"
    )
    module_sha256 = _bytes_sha256(module_payload)
    formal_candidate_sha256 = _sha(
        formal_record.get("candidate_sha256"),
        f"{source_id} formal candidate hash",
    )
    if (
        formal_record.get("status") != "passed"
        or proof_record.get("status") != "solved"
        or proof_record.get("proof_review_route") not in {None, "solved"}
        or proof_record.get("candidate_sha256") != module_sha256
    ):
        _fail(f"{source_id} formal/proof/final candidate is not hard-green/bound")

    certificate = formal_record.get("certificate")
    proof_certificate = proof_record.get("blind_review_certificate")
    if not isinstance(certificate, Mapping) or not isinstance(proof_certificate, Mapping):
        _fail(f"{source_id} review certificate is missing")
    # A proof repair may legitimately replace the formalization-pass module.
    # Keep that earlier certificate internally bound to its own candidate; the
    # proof gate, compile/axiom audits, and Lean #check below bind the final one.
    if certificate.get("candidate_sha256") != formal_candidate_sha256:
        _fail(f"{source_id} formal certificate candidate hash is stale")
    if certificate.get("status") not in {None, "passed"}:
        _fail(f"{source_id} formal certificate itself is not passing")
    _validate_no_answer_key_fields(certificate, label=f"{source_id} formal certificate")
    _validate_no_answer_key_fields(proof_record, label=f"{source_id} proof record")
    _validate_no_answer_key_fields(proof_certificate, label=f"{source_id} proof certificate")

    source_record_sha256 = _value_sha256(dict(source_row))
    answer_rel = _answer_relative(target)
    answer_payload = _read_plain_bytes(
        workspace / answer_rel,
        maximum=_MAX_JSON_BYTES,
        label=f"{source_id} answer submission",
    )
    answer_sha256 = _bytes_sha256(answer_payload)
    formal_contract = _validate_source_contract(
        certificate.get("source_contract"),
        source_id=source_id,
        target=target,
        candidate_sha256=formal_candidate_sha256,
        bundle_sha256=producer_bundle_sha256,
        source_record_sha256=source_record_sha256,
        answer_sha256=answer_sha256,
    )
    proof_contract = _validate_source_contract(
        proof_record.get("source_contract"),
        source_id=source_id,
        target=target,
        candidate_sha256=module_sha256,
        bundle_sha256=producer_bundle_sha256,
        source_record_sha256=source_record_sha256,
        answer_sha256=answer_sha256,
    )
    _validate_source_contract(
        proof_certificate.get("source_contract"),
        source_id=source_id,
        target=target,
        candidate_sha256=module_sha256,
        bundle_sha256=producer_bundle_sha256,
        source_record_sha256=source_record_sha256,
        answer_sha256=answer_sha256,
    )
    payloads = _validate_answer(
        workspace,
        source_id=source_id,
        target=target,
        expected_sha256=answer_sha256,
    )
    declarations = _primary_result_declarations(certificate, source_id=source_id)
    ordered_declarations = [
        declarations[output_id] for output_id, _kind, _unit in EXPECTED_OUTPUTS[source_id]
    ]
    # Historical events remain required, but they do not attest the bytes being
    # frozen now.  Fresh controller probes below are the receipt audit evidence.
    _compile_audit(
        proof_record, source_id=source_id, candidate_sha256=module_sha256
    )
    _axiom_audit(
        workspace,
        proof_record,
        source_id=source_id,
        target=target,
        candidate_sha256=module_sha256,
    )
    try:
        compile_value = current_compile_checker(workspace, target, module_sha256)
    except FreezePriorResultError:
        raise
    except Exception as exc:
        raise FreezePriorResultError(
            f"{source_id} current compile/sorry audit did not run"
        ) from exc
    compile_audit = _current_compile_audit(
        compile_value,
        source_id=source_id,
        target=target,
        candidate_sha256=module_sha256,
    )
    try:
        axiom_value = current_axiom_checker(workspace, target, module_sha256)
    except FreezePriorResultError:
        raise
    except Exception as exc:
        raise FreezePriorResultError(
            f"{source_id} current axiom audit did not run"
        ) from exc
    axiom_audit = _current_axiom_audit(
        axiom_value,
        source_id=source_id,
        target=target,
        candidate_sha256=module_sha256,
    )
    try:
        types = declaration_type_checker(
            workspace, target, module_sha256, ordered_declarations
        )
    except FreezePriorResultError:
        raise
    except Exception as exc:
        raise FreezePriorResultError(
            f"{source_id} Lean declaration type check failed"
        ) from exc
    if not isinstance(types, Mapping) or set(types) != set(ordered_declarations):
        _fail(f"{source_id} Lean type checker returned an incomplete declaration map")
    module_after = _read_plain_bytes(
        workspace / target,
        maximum=_MAX_LEAN_BYTES,
        label=f"{source_id} Lean module post-audit",
    )
    if module_after != module_payload:
        _fail(f"{source_id} Lean module changed during current audits")

    typed_exports: list[dict[str, Any]] = []
    for payload, declaration in zip(payloads, ordered_declarations, strict=True):
        expected_type = types.get(declaration)
        if (
            not isinstance(expected_type, str)
            or not expected_type.strip()
            or len(expected_type.encode("utf-8")) > _MAX_TYPE_BYTES
        ):
            _fail(f"{source_id} declaration {declaration} has no exact checked type")
        expected_type = expected_type.strip()
        typed_exports.append({
            "export_id": (
                f"certified_prior_result:{source_id}:{payload['output_id']}"
            ),
            "module": target,
            "module_sha256": module_sha256,
            "declaration": declaration,
            "expected_type": expected_type,
            "expected_type_sha256": _value_sha256(expected_type),
            "result_payload": payload,
            "result_payload_sha256": _value_sha256(payload),
        })

    previous_ids = _previous_part_ids(source_row, label=source_id)
    return {
        "source_id": source_id,
        "source_record_sha256": source_record_sha256,
        "previous_part_source_ids": previous_ids,
        "previous_part_source_ids_sha256": _value_sha256(previous_ids),
        "source_bundle_sha256": producer_bundle_sha256,
        "answer_submission_sha256": answer_sha256,
        "official_answer_seen": False,
        "module": target,
        "module_sha256": module_sha256,
        "formalization_review": {
            "status": "passed",
            "candidate_sha256": formal_candidate_sha256,
            "certificate_sha256": _value_sha256(dict(certificate)),
            "source_contract_sha256": _value_sha256(dict(formal_contract)),
            "source_bundle_sha256": producer_bundle_sha256,
            "source_record_sha256": source_record_sha256,
            "answer_submission_sha256": answer_sha256,
            "official_answer_seen": False,
        },
        "proof_review": {
            "status": "solved",
            "candidate_sha256": module_sha256,
            "certificate_sha256": _value_sha256(dict(proof_certificate)),
            "source_contract_sha256": _value_sha256(dict(proof_contract)),
            "source_bundle_sha256": producer_bundle_sha256,
            "source_record_sha256": source_record_sha256,
            "answer_submission_sha256": answer_sha256,
            "official_answer_seen": False,
        },
        "compile_audit": compile_audit,
        "axiom_audit": axiom_audit,
        "typed_exports": typed_exports,
    }


def build_frozen_prior_result(
    *,
    producer_workspace: Path,
    producer_seed: Path,
    consumer_seed: Path,
    producer_inventory_sha256: str,
    consumer_inventory_sha256: str,
    declaration_type_checker: DeclarationTypeChecker,
    current_compile_checker: CurrentCompileChecker,
    current_axiom_checker: CurrentAxiomChecker,
    solver_uid: int = 26319,
    uid_process_checker: UidProcessChecker = _uid_has_process,
    controller_uid: int | None = None,
) -> dict[str, Any]:
    """Validate current artifacts and return the canonical A4/A5 receipt."""

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
    _require_solver_quiescent(
        solver_uid, uid_process_checker, stage="before freeze"
    )

    producer_rows, producer_bundle, producer_manifest = _load_bundle(
        producer_seed, expected_ids=PRODUCER_IDS, label="producer seed"
    )
    producer_bundle_sha256 = _bytes_sha256(producer_bundle)
    _campaign, campaign_payload = _validate_terminal_campaign(
        workspace, producer_bundle_sha256=producer_bundle_sha256
    )
    workspace_rows, workspace_bundle, workspace_manifest = _load_bundle(
        workspace, expected_ids=PRODUCER_IDS, label="producer workspace"
    )
    if (
        workspace_bundle != producer_bundle
        or workspace_manifest != producer_manifest
        or workspace_rows != producer_rows
    ):
        _fail("producer workspace source projection differs from its sealed seed")
    consumer_rows, consumer_bundle, _consumer_manifest = _load_bundle(
        consumer_seed, expected_ids=CONSUMER_BUNDLE_IDS, label="consumer seed"
    )
    consumer_bundle_sha256 = _bytes_sha256(consumer_bundle)

    for source_id in PRODUCER_IDS:
        _validate_requested_output_contract(producer_rows[source_id], source_id=source_id)
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
            _fail(f"{source_id} is not in the exact A6 problem/PDF lineage")

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
        _fail("core could not build the validation lineage")

    formal_gate, _ = _read_json(
        workspace / FORMAL_GATE_REL, label="formalization review gate"
    )
    proof_gate, _ = _read_json(workspace / PROOF_GATE_REL, label="proof review gate")
    targets = tuple(_target(source_id) for source_id in PRODUCER_IDS)
    formal_targets = _gate_targets(
        formal_gate, expected_targets=targets, label="formalization review gate"
    )
    proof_targets = _gate_targets(
        proof_gate, expected_targets=targets, label="proof review gate"
    )

    snapshots: list[dict[str, Any]] = []
    for source_id, target in zip(PRODUCER_IDS, targets, strict=True):
        formal_record = formal_targets[target]
        proof_record = proof_targets[target]
        if not isinstance(formal_record, Mapping) or not isinstance(proof_record, Mapping):
            _fail(f"{source_id} gate record is invalid")
        body = _review_and_exports(
            workspace,
            source_id=source_id,
            source_row=producer_rows[source_id],
            producer_bundle_sha256=producer_bundle_sha256,
            formal_record=formal_record,
            proof_record=proof_record,
            declaration_type_checker=declaration_type_checker,
            current_compile_checker=current_compile_checker,
            current_axiom_checker=current_axiom_checker,
        )
        snapshots.append({
            "schema_version": 1,
            "controller_binding": bindings["producer"],
            **body,
        })

    consumer_record_sha256 = _value_sha256(consumer)
    receipt = build_prior_result_dependency_context(
        consumer_target=_target(A6),
        consumer_source_record=consumer,
        consumer_source_record_sha256=consumer_record_sha256,
        consumer_controller_binding=bindings["consumer"],
        producer_snapshots=snapshots,
    )
    if not receipt:
        _fail("core rejected the hard-green A4/A5 snapshots")
    error = validate_prior_result_dependency_context_self(receipt)
    if error:
        _fail(f"core built an invalid receipt: {error}")
    error = validate_prior_result_dependency_context(
        receipt,
        consumer_target=_target(A6),
        consumer_source_record=consumer,
        consumer_source_record_sha256=consumer_record_sha256,
        consumer_controller_binding=bindings["consumer"],
        producer_snapshots=snapshots,
    )
    if error:
        _fail(f"receipt is stale against current artifacts: {error}")
    for snapshot in snapshots:
        target = snapshot["module"]
        expected_sha256 = snapshot["module_sha256"]
        payload = _read_plain_bytes(
            workspace / target,
            maximum=_MAX_LEAN_BYTES,
            label=f"{snapshot['source_id']} final Lean module recheck",
        )
        if _bytes_sha256(payload) != expected_sha256:
            _fail(f"{snapshot['source_id']} Lean module changed during freeze")
    _final_campaign, final_campaign_payload = _validate_terminal_campaign(
        workspace, producer_bundle_sha256=producer_bundle_sha256
    )
    if final_campaign_payload != campaign_payload:
        _fail("producer campaign changed during freeze")
    _require_solver_quiescent(
        solver_uid, uid_process_checker, stage="after freeze"
    )
    return receipt


def lean_declaration_types(
    workspace: Path,
    target: str,
    expected_sha256: str,
    declarations: Sequence[str],
    *,
    lake_bin: Path,
    timeout_seconds: int = 120,
) -> Mapping[str, str]:
    """Append #check to exact final source bytes; never consult a stale olean."""

    if not declarations or len(declarations) != len(set(declarations)):
        _fail("Lean type check requires unique declarations")
    if any(_DECL_RE.fullmatch(item) is None for item in declarations):
        _fail("Lean type check received an invalid declaration")
    if not target.endswith(".lean") or target.startswith("/") or ".." in Path(target).parts:
        _fail("Lean type check target is unsafe")
    expected_sha256 = _sha(expected_sha256, "Lean type-check candidate hash")
    target_payload = _read_plain_bytes(
        workspace / target,
        maximum=_MAX_LEAN_BYTES,
        label="Lean type-check target",
    )
    if _bytes_sha256(target_payload) != expected_sha256:
        _fail("Lean type-check target hash is stale")
    commands: list[str] = []
    for declaration in declarations:
        commands.extend([
            "set_option pp.universes true in",
            "set_option pp.explicit true in",
            "set_option format.width 1000000 in",
            f"#check {declaration}",
        ])
    suffix = ("\n".join(commands) + "\n").encode("utf-8")
    source = target_payload
    if source and not source.endswith(b"\n"):
        source += b"\n"
    source += b"\n" + suffix
    with tempfile.TemporaryDirectory(prefix="icho-a4-a5-typecheck-") as raw:
        check_path = Path(raw) / "CheckCertifiedExports.lean"
        descriptor = os.open(
            check_path,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_CLOEXEC", 0),
            0o600,
        )
        try:
            with os.fdopen(descriptor, "wb") as stream:
                stream.write(source)
                stream.flush()
                os.fsync(stream.fileno())
        except BaseException:
            try:
                os.close(descriptor)
            except OSError:
                pass
            raise
        try:
            completed = subprocess.run(
                [str(lake_bin), "env", "lean", str(check_path)],
                cwd=workspace,
                check=False,
                capture_output=True,
                text=True,
                timeout=timeout_seconds,
                env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"},
            )
        except (OSError, subprocess.TimeoutExpired) as exc:
            raise FreezePriorResultError("Lean declaration type check did not run") from exc
    target_after = _read_plain_bytes(
        workspace / target,
        maximum=_MAX_LEAN_BYTES,
        label="Lean type-check target postcheck",
    )
    if target_after != target_payload:
        _fail("Lean type-check target changed during exact-source check")
    if completed.returncode != 0 or completed.stderr.strip():
        _fail(
            "Lean declaration type check failed: "
            f"rc={completed.returncode} stderr={completed.stderr[-2000:].strip()}"
        )
    remaining = [line.strip() for line in completed.stdout.splitlines() if line.strip()]
    result: dict[str, str] = {}
    for declaration in declarations:
        prefix = f"{declaration} : "
        matches = [line for line in remaining if line.startswith(prefix)]
        if len(matches) != 1:
            _fail(f"Lean did not print one exact type for {declaration}")
        expected_type = matches[0][len(prefix):].strip()
        if not expected_type or len(expected_type.encode("utf-8")) > _MAX_TYPE_BYTES:
            _fail(f"Lean printed an invalid type for {declaration}")
        result[declaration] = expected_type
        remaining.remove(matches[0])
    if remaining:
        _fail("Lean type-check output contained unexpected lines")
    return result


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
    """Compile an exact private copy and scan those same bytes for placeholders."""

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
                cwd=workspace,
                check=False,
                stdin=subprocess.PIPE,
                capture_output=True,
                timeout=timeout_seconds,
                env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"},
            )
        except (OSError, subprocess.TimeoutExpired) as exc:
            raise FreezePriorResultError("current compile/sorry audit did not run") from exc
        if _read_plain_bytes(
            probe, maximum=_MAX_LEAN_BYTES, label="compile probe postcheck"
        ) != payload:
            _fail("compile probe changed during audit")
    after = _read_plain_bytes(
        workspace / target, maximum=_MAX_LEAN_BYTES, label="compile target postcheck"
    )
    if after != payload:
        _fail("compile target changed during audit")
    if type(sorry_count) is not int:
        _fail("current exact-source sorry count is unknown")
    return {
        "schema_version": 1,
        "kind": "current_exact_source_compile_sorry_audit",
        "target": target,
        "candidate_sha256": expected_sha256,
        "source_size": len(payload),
        "status": (
            "passed" if completed.returncode == 0 and sorry_count == 0 else "failed"
        ),
        "compiles": completed.returncode == 0,
        "returncode": completed.returncode,
        "sorry_count": sorry_count,
        "stdout_sha256": _bytes_sha256(completed.stdout),
        "stderr_sha256": _bytes_sha256(completed.stderr),
    }


def lean_current_axiom_audit(
    workspace: Path,
    target: str,
    expected_sha256: str,
    *,
    lake_bin: Path,
    axiom_checker: Path,
    timeout_seconds: int = 1800,
) -> Mapping[str, Any]:
    """Run the bundled axiom checker on a private exact-source copy."""

    expected_sha256 = _sha(expected_sha256, "axiom candidate hash")
    payload = _read_plain_bytes(
        workspace / target, maximum=_MAX_LEAN_BYTES, label="axiom target"
    )
    if not payload or _bytes_sha256(payload) != expected_sha256:
        _fail("axiom target hash is stale/empty")
    if lake_bin.name != "lake":
        _fail("axiom audit requires a trusted executable named lake")
    with tempfile.TemporaryDirectory(prefix="icho-a4-a5-axiom-") as raw:
        probe = Path(raw) / Path(target).name
        _write_exclusive_bytes(probe, payload)
        path_value = str(lake_bin.parent)
        inherited_path = os.environ.get("PATH")
        if inherited_path:
            path_value += os.pathsep + inherited_path
        try:
            completed = subprocess.run(
                [str(axiom_checker), str(probe), "--report-only"],
                cwd=workspace,
                check=False,
                stdin=subprocess.PIPE,
                capture_output=True,
                timeout=timeout_seconds,
                env={
                    **os.environ,
                    "PATH": path_value,
                    "PYTHONDONTWRITEBYTECODE": "1",
                },
            )
        except (OSError, subprocess.TimeoutExpired) as exc:
            raise FreezePriorResultError("current axiom audit did not run") from exc
        if _read_plain_bytes(
            probe, maximum=_MAX_LEAN_BYTES, label="axiom probe postcheck"
        ) != payload:
            _fail("axiom checker did not restore its exact source probe")
    after = _read_plain_bytes(
        workspace / target, maximum=_MAX_LEAN_BYTES, label="axiom target postcheck"
    )
    if after != payload:
        _fail("axiom target changed during audit")
    try:
        stdout = completed.stdout.decode("utf-8", "strict")
        stderr = completed.stderr.decode("utf-8", "strict")
    except UnicodeDecodeError as exc:
        raise FreezePriorResultError("axiom checker output is not UTF-8") from exc
    clean = _ANSI_RE.sub("", stdout)
    file_matches = re.findall(
        r"^\s*Files checked:\s*(\d+)\s*$", clean, flags=re.MULTILINE
    )
    declaration_matches = re.findall(
        r"^\s*Declarations checked:\s*(\d+)\s*$", clean, flags=re.MULTILINE
    )
    files_checked = int(file_matches[0]) if len(file_matches) == 1 else 0
    declarations_checked = (
        int(declaration_matches[0]) if len(declaration_matches) == 1 else 0
    )
    findings = [
        {"decl": match.group("decl"), "axiom": match.group("axiom")}
        for match in _AXIOM_FINDING_RE.finditer(clean)
    ]
    laundering = [
        finding for finding in findings
        if str(finding["axiom"]).lower().startswith("sorryax")
    ]
    nonstandard = [finding for finding in findings if finding not in laundering]
    passed = (
        completed.returncode == 0
        and not stderr.strip()
        and files_checked == 1
        and declarations_checked > 0
        and "All files use only standard axioms" in clean
        and not findings
    )
    return {
        "schema_version": 1,
        "kind": "current_exact_source_axiom_audit",
        "target": target,
        "candidate_sha256": expected_sha256,
        "status": "passed" if passed else "failed",
        "ran": True,
        "returncode": completed.returncode,
        "files_checked": files_checked,
        "declarations_checked": declarations_checked,
        "target_files": [target],
        "failed_files": [] if passed else [target],
        "sorry_launderings": laundering,
        "nonstandard_axioms": nonstandard,
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
    parser.add_argument("--axiom-checker", type=Path, required=True)
    parser.add_argument("--lean-timeout-seconds", type=int, default=120)
    parser.add_argument("--axiom-timeout-seconds", type=int, default=1800)
    parser.add_argument("--solver-uid", type=int, default=26319)
    parser.add_argument("--output", type=Path, required=True)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    arguments = _parser().parse_args(argv)
    try:
        if os.geteuid() != 0:
            _fail("controller freezer must run as root")
        if (
            arguments.lean_timeout_seconds < 1
            or arguments.axiom_timeout_seconds < 1
        ):
            _fail("Lean/axiom timeouts must be positive")
        if arguments.solver_uid < 1:
            _fail("--solver-uid must be a positive dedicated UID")
        lake_bin = _trusted_executable(
            arguments.lake_bin, label="--lake-bin", controller_uid=0
        )
        axiom_checker = _trusted_executable(
            arguments.axiom_checker, label="--axiom-checker", controller_uid=0
        )

        def checker(
            workspace: Path,
            target: str,
            candidate_sha256: str,
            declarations: Sequence[str],
        ) -> Mapping[str, str]:
            return lean_declaration_types(
                workspace,
                target,
                candidate_sha256,
                declarations,
                lake_bin=lake_bin,
                timeout_seconds=arguments.lean_timeout_seconds,
            )

        def compile_checker(
            workspace: Path, target: str, candidate_sha256: str
        ) -> Mapping[str, Any]:
            return lean_current_compile_audit(
                workspace,
                target,
                candidate_sha256,
                lake_bin=lake_bin,
                timeout_seconds=arguments.lean_timeout_seconds,
            )

        def axiom_auditor(
            workspace: Path, target: str, candidate_sha256: str
        ) -> Mapping[str, Any]:
            return lean_current_axiom_audit(
                workspace,
                target,
                candidate_sha256,
                lake_bin=lake_bin,
                axiom_checker=axiom_checker,
                timeout_seconds=arguments.axiom_timeout_seconds,
            )

        receipt = build_frozen_prior_result(
            producer_workspace=arguments.producer_workspace,
            producer_seed=arguments.producer_seed,
            consumer_seed=arguments.consumer_seed,
            producer_inventory_sha256=arguments.producer_inventory_sha256,
            consumer_inventory_sha256=arguments.consumer_inventory_sha256,
            declaration_type_checker=checker,
            current_compile_checker=compile_checker,
            current_axiom_checker=axiom_auditor,
            solver_uid=arguments.solver_uid,
            controller_uid=0,
        )
        file_sha256 = write_staged_receipt(
            arguments.output, receipt, controller_uid=0
        )
        print(json.dumps({
            "status": "controller_receipt_staged",
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
