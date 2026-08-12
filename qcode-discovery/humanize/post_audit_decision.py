"""Replay the first four Stage-1 audits and choose the next experiment.

The reviewer or an external controller may invoke this module, but reviewer
prose never votes on the decision.  A ready decision is emitted only after the
four round commits, their policy-v6 transactions, all 24 selected candidates,
and all 24 formal audit outcomes have been replayed.  Missing, unresolved, or
inconsistent evidence fails closed.

Run it with::

    python -m humanize.post_audit_decision \
      --run-root results/humanize/<source-run-id> \
      --output results/humanize/<source-run-id>/post-r4-decision.json
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import re
import stat
import sys
from collections.abc import Callable, Mapping, Sequence
from pathlib import Path
from typing import Any

from .audit_state import (
    AuditOutcome,
    AuditStateError,
    authoritative_candidate_digest,
    classify_evaluation,
)
from .flow import (
    CANDIDATE_BATCH_POLICY_AUDIT_FUNNEL_VERSION,
    CANDIDATE_BATCH_POLICY_VERSION,
    ROUND_TRANSACTION_PROTOCOL_VERSION,
    ROUND_TRANSACTION_SCHEMA_VERSION,
    RoundTransactionError,
    _checkpoint_descriptor,
    _replayable_search_lower_bound_for_audit,
)
from .reviewer import ReviewError, validate_review
from .state import atomic_write_json, code_key


POST_AUDIT_DECISION_SCHEMA_VERSION = 1
POST_AUDIT_DECISION_KIND = "qcode-post-r4-audit-decision-v1"
POST_AUDIT_DECISION_ROUNDS = (1, 2, 3, 4)
POST_AUDIT_REQUIRED_AUDITS = 24
POST_AUDIT_AUDITS_PER_ROUND = 6
POST_AUDIT_LB_PER_ROUND = 5
POST_AUDIT_REQUIRED_LB_AUDITS = 20
POST_AUDIT_LOW_UPPER_BOUND = 8
POST_AUDIT_LOW_UPPER_NUMERATOR = 4
POST_AUDIT_LOW_UPPER_DENOMINATOR = 5
POST_AUDIT_TERMINAL_NUMERATOR = 9
POST_AUDIT_TERMINAL_DENOMINATOR = 10
POST_AUDIT_SURVIVOR_NUMERATOR = 1
POST_AUDIT_SURVIVOR_DENOMINATOR = 5
POST_AUDIT_MIN_SURVIVORS = 4
POST_AUDIT_TARGET_MODE = "scalar-fom-strict-v1"
POST_AUDIT_SOURCE_REPRESENTATION = "css-bb-twisted-torus-generator-v1"

DEFAULT_BROADER_DESIGN = Path(
    "configs/post_r4_broader_published_volume_coverage_design.v1.json"
)
DEFAULT_LADDER_DESIGN = Path(
    "configs/post_r4_bounded_target_aware_ladder_design.v1.json"
)

_SHA256 = re.compile(r"[0-9a-f]{64}")

OutcomeClassifier = Callable[[Mapping[str, Any]], AuditOutcome]
LowerBoundReplayer = Callable[[dict[str, Any]], int | None]
DigestAuthority = Callable[[Mapping[str, Any]], str]
CheckpointAuthority = Callable[
    [Path, Path, int | None],
    dict[str, Any],
]


class PostAuditDecisionError(ValueError):
    """The post-R4 evidence cannot authorize a next experiment."""

    classification = "POST_R4_EVIDENCE_INVALID"

    def __init__(self, code: str, message: str):
        super().__init__(message)
        self.code = code


class PostAuditDecisionNotReady(PostAuditDecisionError):
    """The fourth round has not reached its durable commit boundary yet."""

    classification = "POST_R4_EVIDENCE_NOT_READY"


def _fail(code: str, message: str) -> None:
    raise PostAuditDecisionError(code, message)


def _pending(code: str, message: str) -> None:
    raise PostAuditDecisionNotReady(code, message)


def _canonical_json(value: Any) -> bytes:
    try:
        return json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        ).encode("utf-8")
    except (TypeError, ValueError) as exc:
        _fail("NON_CANONICAL_JSON", "decision evidence is not strict JSON")
        raise AssertionError("unreachable") from exc


def _canonical_sha256(value: Any) -> str:
    return hashlib.sha256(_canonical_json(value)).hexdigest()


def _sealed_payload(value: dict[str, Any]) -> dict[str, Any]:
    sealed = copy.deepcopy(value)
    sealed["decision_sha256"] = _canonical_sha256(sealed)
    return sealed


def _strict_json_bytes(payload: bytes, label: str) -> Any:
    def reject_constant(value: str) -> None:
        raise ValueError(f"non-finite constant {value}")

    def reject_duplicate_keys(
        pairs: list[tuple[str, Any]],
    ) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"duplicate key {key!r}")
            result[key] = value
        return result

    try:
        return json.loads(
            payload.decode("utf-8"),
            parse_constant=reject_constant,
            object_pairs_hook=reject_duplicate_keys,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
        _fail("MALFORMED_JSON", f"{label} is not strict JSON: {exc}")
        raise AssertionError("unreachable") from exc


def _reject_symlink_components(path: Path, label: str) -> None:
    absolute = Path(os.path.abspath(path))
    current = Path(absolute.anchor)
    for component in absolute.parts[1:]:
        current /= component
        try:
            mode = os.lstat(current).st_mode
        except FileNotFoundError:
            _pending("MISSING_ARTIFACT", f"{label} is missing")
        except OSError as exc:
            _fail("UNSAFE_ARTIFACT", f"cannot inspect {label}: {exc}")
        if stat.S_ISLNK(mode):
            _fail("UNSAFE_ARTIFACT", f"{label} may not contain symlinks")


def _read_regular_bytes(path: Path, label: str) -> bytes:
    absolute = Path(os.path.abspath(path))
    _reject_symlink_components(absolute, label)
    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(
        os, "O_NOFOLLOW", 0
    )
    try:
        descriptor = os.open(absolute, flags)
    except FileNotFoundError:
        _pending("MISSING_ARTIFACT", f"{label} is missing")
        raise AssertionError("unreachable")
    except OSError as exc:
        _fail("UNSAFE_ARTIFACT", f"cannot open {label}: {exc}")
        raise AssertionError("unreachable")
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            _fail("UNSAFE_ARTIFACT", f"{label} must be a regular file")
        chunks: list[bytes] = []
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                break
            chunks.append(chunk)
        after = os.fstat(descriptor)
        if (
            before.st_dev != after.st_dev
            or before.st_ino != after.st_ino
            or before.st_size != after.st_size
            or before.st_mtime_ns != after.st_mtime_ns
        ):
            _fail("ARTIFACT_CHANGED", f"{label} changed while it was read")
        return b"".join(chunks)
    finally:
        os.close(descriptor)


def _read_json_object(path: Path, label: str) -> tuple[dict[str, Any], bytes]:
    payload = _read_regular_bytes(path, label)
    value = _strict_json_bytes(payload, label)
    if not isinstance(value, dict):
        _fail("MALFORMED_JSON", f"{label} must contain a JSON object")
    return value, payload


def _read_jsonl(path: Path, label: str) -> tuple[list[dict[str, Any]], bytes]:
    payload = _read_regular_bytes(path, label)
    if payload and not payload.endswith(b"\n"):
        _fail("PARTIAL_JSONL", f"{label} is not newline terminated")
    rows: list[dict[str, Any]] = []
    for index, line in enumerate(payload.splitlines(), start=1):
        if not line:
            _fail("MALFORMED_JSONL", f"{label} contains an empty record")
        value = _strict_json_bytes(line, f"{label} row {index}")
        if not isinstance(value, dict):
            _fail("MALFORMED_JSONL", f"{label} row {index} is not an object")
        rows.append(value)
    return rows, payload


def _identity(payload: bytes, *, rows: int | None = None) -> dict[str, Any]:
    value: dict[str, Any] = {
        "sha256": hashlib.sha256(payload).hexdigest(),
        "bytes": len(payload),
    }
    if rows is not None:
        value["rows"] = rows
    return value


def _stream_file_identity(path: Path, label: str) -> dict[str, Any]:
    """Hash a large committed JSONL without retaining it in memory."""

    absolute = Path(os.path.abspath(path))
    _reject_symlink_components(absolute, label)
    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(
        os, "O_NOFOLLOW", 0
    )
    try:
        descriptor = os.open(absolute, flags)
    except FileNotFoundError:
        _pending("MISSING_ARTIFACT", f"{label} is missing")
        raise AssertionError("unreachable")
    except OSError as exc:
        _fail("UNSAFE_ARTIFACT", f"cannot open {label}: {exc}")
        raise AssertionError("unreachable")
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            _fail("UNSAFE_ARTIFACT", f"{label} must be a regular file")
        digest = hashlib.sha256()
        size = 0
        rows = 0
        final_byte = b""
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                break
            digest.update(chunk)
            size += len(chunk)
            rows += chunk.count(b"\n")
            final_byte = chunk[-1:]
        after = os.fstat(descriptor)
        if (
            before.st_dev != after.st_dev
            or before.st_ino != after.st_ino
            or before.st_size != after.st_size
            or before.st_mtime_ns != after.st_mtime_ns
        ):
            _fail("ARTIFACT_CHANGED", f"{label} changed while it was hashed")
        if size and final_byte != b"\n":
            _fail("PARTIAL_JSONL", f"{label} is not newline terminated")
        return {"sha256": digest.hexdigest(), "bytes": size, "rows": rows}
    finally:
        os.close(descriptor)


def _stream_range_identity(
    path: Path,
    *,
    start: int,
    end: int,
    label: str,
) -> dict[str, Any]:
    absolute = Path(os.path.abspath(path))
    _reject_symlink_components(absolute, label)
    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(
        os, "O_NOFOLLOW", 0
    )
    try:
        descriptor = os.open(absolute, flags)
    except FileNotFoundError:
        _pending("MISSING_ARTIFACT", f"{label} is missing")
        raise AssertionError("unreachable")
    except OSError as exc:
        _fail("UNSAFE_ARTIFACT", f"cannot open {label}: {exc}")
        raise AssertionError("unreachable")
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode) or end > before.st_size:
            _fail("SOURCE_RANGE_INVALID", f"{label} range is unavailable")
        os.lseek(descriptor, start, os.SEEK_SET)
        remaining = end - start
        digest = hashlib.sha256()
        rows = 0
        final_byte = b""
        while remaining:
            chunk = os.read(descriptor, min(1024 * 1024, remaining))
            if not chunk:
                _fail("SOURCE_RANGE_INVALID", f"{label} ended inside its range")
            remaining -= len(chunk)
            digest.update(chunk)
            rows += chunk.count(b"\n")
            final_byte = chunk[-1:]
        after = os.fstat(descriptor)
        if before.st_dev != after.st_dev or before.st_ino != after.st_ino:
            _fail("ARTIFACT_CHANGED", f"{label} was replaced while it was read")
        if end > after.st_size:
            _fail("ARTIFACT_CHANGED", f"{label} shrank while it was read")
        if end > start and final_byte != b"\n":
            _fail("PARTIAL_JSONL", f"{label} range is not newline terminated")
        return {
            "sha256": digest.hexdigest(),
            "bytes": end - start,
            "rows": rows,
        }
    finally:
        os.close(descriptor)


def _strict_positive_int(value: Any, label: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < 1:
        _fail("INVALID_FIELD", f"{label} must be a positive integer")
    return value


def _strict_nonnegative_int(value: Any, label: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        _fail("INVALID_FIELD", f"{label} must be a non-negative integer")
    return value


def _valid_sha256(value: Any, label: str) -> str:
    if not isinstance(value, str) or _SHA256.fullmatch(value) is None:
        _fail("INVALID_HASH", f"{label} must be a lowercase SHA-256 digest")
    return value


def _fixed_recorded_path(value: Any, expected: Path, label: str) -> None:
    if not isinstance(value, str) or not value:
        _fail("INVALID_PATH_BINDING", f"{label} has no recorded path")
    recorded = Path(os.path.abspath(value))
    fixed = Path(os.path.abspath(expected))
    if recorded != fixed:
        _fail("INVALID_PATH_BINDING", f"{label} path disagrees with its boundary")


def _state_prefix(state: Mapping[str, Any]) -> dict[str, Any]:
    if state.get("schema_version") != 1:
        _fail("STATE_SCHEMA", "state.json has an unsupported schema")
    run_id = state.get("run_id")
    if not isinstance(run_id, str) or not run_id:
        _fail("STATE_SCHEMA", "state.json has no run_id")
    if state.get("round_transaction_version") != (
        ROUND_TRANSACTION_PROTOCOL_VERSION
    ):
        _fail("STATE_SCHEMA", "state.json is not on transaction protocol v3")
    current_round = state.get("current_round")
    if (
        isinstance(current_round, bool)
        or not isinstance(current_round, int)
        or current_round < len(POST_AUDIT_DECISION_ROUNDS)
    ):
        _pending("ROUND_4_NOT_COMMITTED", "Round 4 is not durably committed")
    raw_rounds = state.get("rounds")
    if not isinstance(raw_rounds, list):
        _fail("STATE_SCHEMA", "state.json rounds must be an array")
    by_number: dict[int, dict[str, Any]] = {}
    for raw in raw_rounds:
        if not isinstance(raw, dict):
            _fail("STATE_SCHEMA", "state.json contains a non-object round summary")
        number = raw.get("round")
        if isinstance(number, bool) or not isinstance(number, int) or number < 1:
            _fail("STATE_SCHEMA", "state.json contains an invalid round number")
        if number in by_number:
            _fail("STATE_SCHEMA", "state.json contains duplicate round summaries")
        by_number[number] = raw
    missing = [number for number in POST_AUDIT_DECISION_ROUNDS if number not in by_number]
    if missing:
        _pending("ROUND_SUMMARY_MISSING", "Round 4 summary is not committed")
    config = state.get("config")
    if not isinstance(config, dict):
        _fail("STATE_CONFIG", "state.json has no bound Stage-1 config")
    expected_config = {
        "target_mode": POST_AUDIT_TARGET_MODE,
        "model": "gpt-5.6-sol",
        "reasoning_effort": "xhigh",
        "search_representation_id": POST_AUDIT_SOURCE_REPRESENTATION,
        "milp_top": POST_AUDIT_AUDITS_PER_ROUND,
    }
    for field, expected in expected_config.items():
        if config.get(field) != expected:
            _fail("STATE_CONFIG", f"state.json config {field} is not {expected!r}")
    return {
        "schema_version": state["schema_version"],
        "run_id": run_id,
        "round_transaction_version": state["round_transaction_version"],
        "config": expected_config,
        "rounds": [copy.deepcopy(by_number[number]) for number in POST_AUDIT_DECISION_ROUNDS],
    }


def _round_summary(prefix: Mapping[str, Any], number: int) -> dict[str, Any]:
    rounds = prefix["rounds"]
    assert isinstance(rounds, list)
    summary = rounds[number - 1]
    assert isinstance(summary, dict)
    return summary


def _validate_transaction(
    *,
    run_root: Path,
    repo_dir: Path,
    run_id: str,
    round_number: int,
    previous_transaction: Mapping[str, Any] | None,
    checkpoint_authority: CheckpointAuthority,
) -> tuple[dict[str, Any], dict[str, Any]]:
    round_dir = run_root / "rounds" / f"round-{round_number:03d}"
    transaction_path = round_dir / "evolution-transaction.json"
    transaction, transaction_payload = _read_json_object(
        transaction_path,
        f"Round {round_number} transaction",
    )
    expected_header = {
        "schema_version": ROUND_TRANSACTION_SCHEMA_VERSION,
        "protocol_version": ROUND_TRANSACTION_PROTOCOL_VERSION,
        "run_id": run_id,
        "round": round_number,
        "mode": "openevolve",
        "status": "committed",
        "candidate_batch_policy_version": (
            CANDIDATE_BATCH_POLICY_AUDIT_FUNNEL_VERSION
        ),
    }
    for field, expected in expected_header.items():
        if transaction.get(field) != expected:
            _fail(
                "TRANSACTION_BOUNDARY",
                f"Round {round_number} transaction {field} is not {expected!r}",
            )
    if CANDIDATE_BATCH_POLICY_VERSION != (
        CANDIDATE_BATCH_POLICY_AUDIT_FUNNEL_VERSION
    ):
        _fail("SELECTOR_VERSION", "current source no longer defaults to policy v6")
    if not isinstance(transaction.get("committed_at"), str):
        _fail("TRANSACTION_BOUNDARY", f"Round {round_number} has no commit time")

    batch_path = round_dir / "candidate-batch.jsonl"
    _fixed_recorded_path(
        transaction.get("candidate_batch"),
        batch_path,
        f"Round {round_number} candidate batch",
    )
    batch_identity = _stream_file_identity(
        batch_path,
        f"Round {round_number} candidate batch",
    )
    if transaction.get("candidate_batch_identity") != batch_identity:
        _fail(
            "CANDIDATE_BATCH_HASH",
            f"Round {round_number} candidate batch changed after commit",
        )

    start = _strict_nonnegative_int(
        transaction.get("candidate_start_offset"),
        f"Round {round_number} candidate_start_offset",
    )
    end = _strict_nonnegative_int(
        transaction.get("candidate_end_offset"),
        f"Round {round_number} candidate_end_offset",
    )
    if end <= start:
        _fail("SOURCE_RANGE_INVALID", f"Round {round_number} source range is empty")
    if previous_transaction is None:
        if start != 0 or transaction.get("base_checkpoint") is not None:
            _fail("TRANSACTION_CHAIN", "Round 1 is not a fresh transaction")
    else:
        if start != previous_transaction.get("candidate_end_offset"):
            _fail("TRANSACTION_CHAIN", "candidate source ranges are not contiguous")
        if transaction.get("base_checkpoint") != previous_transaction.get(
            "result_checkpoint"
        ):
            _fail("TRANSACTION_CHAIN", "checkpoint chain is not contiguous")

    raw_source_path = transaction.get("candidate_log")
    if not isinstance(raw_source_path, str) or not raw_source_path:
        _fail("INVALID_PATH_BINDING", "transaction candidate_log is invalid")
    source_path = Path(os.path.abspath(raw_source_path))
    evolution_root = repo_dir / "results" / "evolution"
    try:
        source_path.relative_to(evolution_root)
    except ValueError:
        _fail("INVALID_PATH_BINDING", "candidate_log escapes results/evolution")
    source_identity = _stream_range_identity(
        source_path,
        start=start,
        end=end,
        label=f"Round {round_number} candidate source",
    )
    if (
        transaction.get("candidate_source_sha256") != source_identity["sha256"]
        or transaction.get("candidate_source_rows") != source_identity["rows"]
    ):
        _fail(
            "CANDIDATE_SOURCE_HASH",
            f"Round {round_number} source slice changed after commit",
        )

    for field, filename in (
        ("completion_marker", "openevolve-completed.json"),
        ("completion_witness", "openevolve-slice-witness.json"),
    ):
        artifact_path = round_dir / filename
        _fixed_recorded_path(
            transaction.get(field),
            artifact_path,
            f"Round {round_number} {field}",
        )
        artifact = _read_regular_bytes(
            artifact_path,
            f"Round {round_number} {field}",
        )
        recorded_hash = _valid_sha256(
            transaction.get(f"{field}_sha256"),
            f"Round {round_number} {field}_sha256",
        )
        if hashlib.sha256(artifact).hexdigest() != recorded_hash:
            _fail(
                "COMPLETION_HASH",
                f"Round {round_number} {field} changed after commit",
            )

    result = transaction.get("result_checkpoint")
    if not isinstance(result, dict):
        _fail("CHECKPOINT_BOUNDARY", f"Round {round_number} has no checkpoint")
    expected_iteration = _strict_positive_int(
        transaction.get("expected_result_iteration"),
        f"Round {round_number} expected_result_iteration",
    )
    result_path = result.get("path")
    if not isinstance(result_path, str) or not result_path:
        _fail("CHECKPOINT_BOUNDARY", f"Round {round_number} checkpoint path is invalid")
    checkpoint_path = Path(os.path.abspath(result_path))
    try:
        checkpoint_path.relative_to(evolution_root)
    except ValueError:
        _fail("INVALID_PATH_BINDING", "checkpoint escapes results/evolution")
    try:
        observed_checkpoint = checkpoint_authority(
            checkpoint_path.parent.parent,
            checkpoint_path,
            expected_iteration,
        )
    except (OSError, ValueError, RoundTransactionError) as exc:
        _fail(
            "CHECKPOINT_BOUNDARY",
            f"Round {round_number} checkpoint replay failed: {exc}",
        )
    if result != observed_checkpoint:
        _fail(
            "CHECKPOINT_BOUNDARY",
            f"Round {round_number} checkpoint changed after commit",
        )

    evidence = {
        "round": round_number,
        "transaction": _identity(transaction_payload),
        "candidate_source": {
            "start_offset": start,
            "end_offset": end,
            **source_identity,
        },
        "candidate_batch": batch_identity,
        "completion_marker_sha256": transaction["completion_marker_sha256"],
        "completion_witness_sha256": transaction["completion_witness_sha256"],
        "result_checkpoint": copy.deepcopy(result),
        "candidate_batch_policy_version": transaction[
            "candidate_batch_policy_version"
        ],
    }
    return transaction, evidence


def _default_checkpoint_authority(
    output_dir: Path,
    checkpoint: Path,
    expected_iteration: int | None,
) -> dict[str, Any]:
    return _checkpoint_descriptor(
        output_dir,
        checkpoint,
        expected_iteration=expected_iteration,
    )


def _validate_review_binding(
    *,
    round_number: int,
    round_dir: Path,
    summary: Mapping[str, Any],
) -> dict[str, Any]:
    review, payload = _read_json_object(
        round_dir / "review.json",
        f"Round {round_number} review",
    )
    try:
        validated = validate_review(review, require_current=True)
    except ReviewError as exc:
        _fail("REVIEW_BINDING", f"Round {round_number} review is invalid: {exc}")
    binding = summary.get("review_binding")
    expected = {
        "schema_version": 1,
        "artifact_sha256": hashlib.sha256(payload).hexdigest(),
        "artifact_bytes": len(payload),
        "review_schema_version": 2,
        "search_action": copy.deepcopy(validated["search_action"]),
    }
    if binding != expected:
        _fail(
            "REVIEW_BINDING",
            f"Round {round_number} review changed after the state commit",
        )
    if (
        summary.get("review_verdict") != validated["verdict"]
        or summary.get("review_summary") != validated["summary"]
    ):
        _fail("REVIEW_BINDING", f"Round {round_number} review summary is inconsistent")
    return _identity(payload)


def _validate_summary_milp_binding(
    *,
    round_number: int,
    summary: Mapping[str, Any],
    milp_identity: Mapping[str, Any],
    exact_distances: list[int],
) -> None:
    if summary.get("round") != round_number:
        _fail("ROUND_SUMMARY", f"Round {round_number} summary has the wrong number")
    if summary.get("milp_audited") != milp_identity["rows"]:
        _fail("ROUND_SUMMARY", f"Round {round_number} audit count is inconsistent")
    expected_source = {
        "source_milp_sha256": milp_identity["sha256"],
        "source_milp_bytes": milp_identity["bytes"],
        "source_milp_rows": milp_identity["rows"],
    }
    sealed = summary.get("sealed_exact_audit")
    expected_sealed = {
        "schema_version": 1,
        "basis": "sealed-formal-audit-attempts",
        **expected_source,
        "exact_count": len(exact_distances),
        "exact_distances": sorted(exact_distances),
    }
    if sealed != expected_sealed:
        _fail(
            "ROUND_SUMMARY",
            f"Round {round_number} sealed exact summary disagrees with MILP evidence",
        )
    feedback = summary.get("failure_direction_feedback")
    if not isinstance(feedback, dict) or any(
        feedback.get(field) != value for field, value in expected_source.items()
    ):
        _fail(
            "ROUND_SUMMARY",
            f"Round {round_number} failure feedback is not bound to MILP evidence",
        )


def _normalize_outcome(value: Any, label: str) -> AuditOutcome:
    if isinstance(value, AuditOutcome):
        return value
    try:
        return AuditOutcome(value)
    except (TypeError, ValueError) as exc:
        _fail("AUDIT_CLASSIFICATION", f"{label} returned an invalid outcome")
        raise AssertionError("unreachable") from exc


def _trusted_upper_bound(row: Mapping[str, Any], outcome: AuditOutcome) -> int:
    if outcome is AuditOutcome.EXACT:
        return _strict_positive_int(row.get("d"), "exact audit distance")
    if outcome is AuditOutcome.THRESHOLD_REJECTED:
        return _strict_positive_int(
            row.get("threshold_proof_distance"),
            "threshold proof distance",
        )
    _fail("UNRESOLVED_AUDIT", "unresolved audit has no trusted upper bound")
    raise AssertionError("unreachable")


def _candidate_identity(
    row: Mapping[str, Any],
    *,
    digest_authority: DigestAuthority,
    label: str,
) -> tuple[str, str]:
    try:
        key = code_key(dict(row))
        digest = digest_authority(row)
    except (AuditStateError, KeyError, TypeError, ValueError) as exc:
        _fail("CANDIDATE_IDENTITY", f"{label} identity replay failed: {exc}")
    if not isinstance(key, str) or len(key) != 20:
        _fail("CANDIDATE_IDENTITY", f"{label} code key is invalid")
    if not isinstance(digest, str) or _SHA256.fullmatch(digest) is None:
        _fail("CANDIDATE_IDENTITY", f"{label} canonical digest is invalid")
    return key, digest


def _validate_round_audits(
    *,
    round_number: int,
    round_dir: Path,
    classifier: OutcomeClassifier,
    lower_bound_replayer: LowerBoundReplayer,
    digest_authority: DigestAuthority,
) -> tuple[list[dict[str, Any]], dict[str, Any], list[int]]:
    selected, selected_payload = _read_jsonl(
        round_dir / "selected.jsonl",
        f"Round {round_number} selection",
    )
    audited, milp_payload = _read_jsonl(
        round_dir / "milp.jsonl",
        f"Round {round_number} MILP evidence",
    )
    if len(selected) != POST_AUDIT_AUDITS_PER_ROUND:
        _pending(
            "AUDIT_SAMPLE_INCOMPLETE",
            f"Round {round_number} does not have six selected candidates",
        )
    if len(audited) != len(selected):
        _pending(
            "AUDIT_SAMPLE_INCOMPLETE",
            f"Round {round_number} does not have six completed audit rows",
        )

    selected_by_identity: dict[tuple[str, str], dict[str, Any]] = {}
    lower_bounds: dict[tuple[str, str], int] = {}
    exploration_count = 0
    for index, row in enumerate(selected):
        identity = _candidate_identity(
            row,
            digest_authority=digest_authority,
            label=f"Round {round_number} selected row {index + 1}",
        )
        if identity in selected_by_identity:
            _fail("DUPLICATE_AUDIT", f"Round {round_number} selection is not distinct")
        selected_by_identity[identity] = row
        try:
            replayed_lower = lower_bound_replayer(row)
        except Exception as exc:
            _fail(
                "LOWER_BOUND_REPLAY",
                f"Round {round_number} selected lower-bound replay failed: {exc}",
            )
        claimed_lower = row.get("distance_lower_bound")
        if replayed_lower is not None:
            if (
                isinstance(replayed_lower, bool)
                or not isinstance(replayed_lower, int)
                or replayed_lower < 5
                or claimed_lower != replayed_lower
            ):
                _fail(
                    "LOWER_BOUND_REPLAY",
                    f"Round {round_number} selected lower bound is inconsistent",
                )
            lower_bounds[identity] = replayed_lower
        else:
            if claimed_lower is not None:
                _fail(
                    "LOWER_BOUND_REPLAY",
                    f"Round {round_number} lower-bound claim was not replayable",
                )
            if (
                row.get("candidate_persistence_lane")
                != "winner_capable_quick_exploration"
                or row.get("winner_capable_parameters") is not True
            ):
                _fail(
                    "SELECTION_COHORT",
                    f"Round {round_number} non-LB selection is not the exploration slot",
                )
            exploration_count += 1
    if (
        len(lower_bounds) != POST_AUDIT_LB_PER_ROUND
        or exploration_count != 1
    ):
        _fail(
            "SELECTION_COHORT",
            f"Round {round_number} is not a five-LB plus one-exploration sample",
        )

    records: list[dict[str, Any]] = []
    exact_distances: list[int] = []
    audited_identities: set[tuple[str, str]] = set()
    for index, row in enumerate(audited):
        identity = _candidate_identity(
            row,
            digest_authority=digest_authority,
            label=f"Round {round_number} audit row {index + 1}",
        )
        if identity not in selected_by_identity:
            _fail("AUDIT_SELECTION_MISMATCH", f"Round {round_number} audited an unselected code")
        if identity in audited_identities:
            _fail("DUPLICATE_AUDIT", f"Round {round_number} audit rows are not distinct")
        audited_identities.add(identity)
        attempt = row.get("audit_attempt")
        if (
            not isinstance(attempt, dict)
            or attempt.get("schema_version") != 2
            or attempt.get("round") != round_number
            or not isinstance(attempt.get("evidence"), dict)
            or row.get("candidate_key") != identity[0]
        ):
            _fail(
                "AUDIT_BOUNDARY",
                f"Round {round_number} audit row lacks a formal round binding",
            )
        try:
            outcome = _normalize_outcome(
                classifier(row),
                f"Round {round_number} audit row {index + 1}",
            )
        except PostAuditDecisionError:
            raise
        except Exception as exc:
            _fail(
                "AUDIT_REPLAY",
                f"Round {round_number} formal audit replay failed: {exc}",
            )
        if not outcome.terminal:
            _pending(
                "UNRESOLVED_AUDIT",
                f"Round {round_number} still contains an UNKNOWN audit",
            )
        upper_bound = _trusted_upper_bound(row, outcome)
        cohort = "lower_bound" if identity in lower_bounds else "exploration"
        if outcome is AuditOutcome.EXACT:
            exact_distances.append(upper_bound)
        records.append({
            "round": round_number,
            "candidate_key": identity[0],
            "canonical_digest": identity[1],
            "cohort": cohort,
            "replayed_lower_bound": lower_bounds.get(identity),
            "outcome": outcome.value,
            "trusted_upper_bound": upper_bound,
            "trusted_upper_bound_le_8": (
                cohort == "lower_bound"
                and upper_bound <= POST_AUDIT_LOW_UPPER_BOUND
            ),
        })
    if audited_identities != set(selected_by_identity):
        _fail("AUDIT_SELECTION_MISMATCH", f"Round {round_number} did not audit its full selection")
    records.sort(key=lambda row: (row["candidate_key"], row["canonical_digest"]))
    artifacts = {
        "selected": _identity(selected_payload, rows=len(selected)),
        "milp": _identity(milp_payload, rows=len(audited)),
    }
    return records, artifacts, sorted(exact_distances)


def _relative_config_identity(repo_dir: Path, path: Path) -> dict[str, Any]:
    absolute = Path(os.path.abspath(path if path.is_absolute() else repo_dir / path))
    try:
        relative = absolute.relative_to(repo_dir)
    except ValueError:
        _fail("NEXT_EXPERIMENT_CONFIG", "next-experiment artifact escapes the repository")
    payload = _read_regular_bytes(absolute, f"next-experiment artifact {relative}")
    return {"path": relative.as_posix(), **_identity(payload)}


def _validate_broader_design(
    *,
    repo_dir: Path,
    path: Path,
) -> dict[str, Any]:
    absolute = Path(os.path.abspath(path if path.is_absolute() else repo_dir / path))
    raw, _payload = _read_json_object(absolute, "published-volume coverage design")
    expected = {
        "schema_version": 1,
        "kind": "qcode-broader-published-volume-coverage-design-v1",
        "implementation_status": "installed_reviewed",
        "launchable": True,
        "required_experiment_id": (
            "qcode-twisted-torus-published-volume-coverage-v2-gpt56sol"
        ),
        "required_representation_id": (
            "css-bb-twisted-torus-published-volume-generator-v2"
        ),
        "target_mode": POST_AUDIT_TARGET_MODE,
        "model": "gpt-5.6-sol",
        "reasoning_effort": "xhigh",
        "max_total_workers": 12,
        "candidate_batch_policy_version": 6,
    }
    for field, value in expected.items():
        if raw.get(field) != value:
            _fail(
                "NEXT_EXPERIMENT_DESIGN",
                f"published-volume design {field} is not {value!r}",
            )
    if raw.get("excluded_aliases") != [
        "css-bb-cover-algebra-generator-v2",
        "css-bb-novel-ansatz-generator-v2",
    ]:
        _fail(
            "NEXT_EXPERIMENT_DESIGN",
            "published-volume design does not exclude the known q=0 aliases",
        )
    expected_coverage = {
        "target_volumes": [105, 124, 126, 127, 132, 147, 170],
        "target_shapes": 41,
        "all_shapes_with_pareto": 44,
        "contracted_twist_strata": 822,
        "seed_rows": 3627,
        "thin_lattice": [1, 127],
        "thin_twists": [25],
        "stage2_deep_lattices": 11,
    }
    if raw.get("coverage_contract") != expected_coverage:
        _fail(
            "NEXT_EXPERIMENT_DESIGN",
            "published-volume coverage contract is not the reviewed contract",
        )
    expected_paths = (
        "configs/five_stage_campaign."
        "twisted_torus_published_volume_v2_gpt56sol_20260812.json",
        "evolve/config_twisted_torus_published.yaml",
        "evolve/seed_solution_twisted_torus_published.py",
        "evaluation/twisted_torus_published_anchors.v1.json",
        "results/known_code_registry.json",
        "evaluation/search_contract.py",
        "evolve/openevolve_evaluator.py",
        "evolve/run_evolution.py",
        "humanize/flow.py",
        "humanize/reviewer.py",
    )
    installed = raw.get("installed_artifacts")
    if (
        not isinstance(installed, list)
        or [item.get("path") for item in installed if isinstance(item, dict)]
        != list(expected_paths)
    ):
        _fail(
            "NEXT_EXPERIMENT_DESIGN",
            "published-volume installed artifact manifest is incomplete",
        )
    installed_identities: list[dict[str, Any]] = []
    for index, expected_path in enumerate(expected_paths):
        descriptor = installed[index]
        if (
            not isinstance(descriptor, dict)
            or set(descriptor) != {"path", "sha256"}
            or descriptor.get("path") != expected_path
            or not isinstance(descriptor.get("sha256"), str)
            or _SHA256.fullmatch(descriptor["sha256"]) is None
        ):
            _fail(
                "NEXT_EXPERIMENT_DESIGN",
                "published-volume installed artifact descriptor is malformed",
            )
        observed = _relative_config_identity(repo_dir, Path(expected_path))
        if observed["sha256"] != descriptor["sha256"]:
            _fail(
                "NEXT_EXPERIMENT_DESIGN",
                f"published-volume installed artifact changed: {expected_path}",
            )
        installed_identities.append(observed)

    pipeline, _pipeline_payload = _read_json_object(
        repo_dir / expected_paths[0], "published-volume pipeline config"
    )
    stage1 = pipeline.get("stage1")
    stage3 = pipeline.get("stage3")
    if (
        pipeline.get("run_id") != raw["required_experiment_id"]
        or pipeline.get("resume") is not True
        or pipeline.get("target_mode") != raw["target_mode"]
        or pipeline.get("max_total_workers") != raw["max_total_workers"]
        or not isinstance(stage1, dict)
        or stage1.get("model") != raw["model"]
        or stage1.get("reasoning_effort") != raw["reasoning_effort"]
        or stage1.get("search_representation_id")
        != raw["required_representation_id"]
        or stage1.get("evolution_config") != expected_paths[1]
        or stage1.get("evolution_seed") != expected_paths[2]
        or stage1.get("milp_top") != 6
        or stage1.get("codex_cli") is not True
        or not isinstance(stage3, dict)
        or stage3.get("backend") != raw["required_stage3_backend"]
    ):
        _fail(
            "NEXT_EXPERIMENT_DESIGN",
            "published-volume pipeline config violates the reviewed launch contract",
        )
    return {
        **_relative_config_identity(repo_dir, absolute),
        "required_experiment_id": raw["required_experiment_id"],
        "required_representation_id": raw["required_representation_id"],
        "target_mode": raw["target_mode"],
        "candidate_batch_policy_version": raw[
            "candidate_batch_policy_version"
        ],
        "model": raw["model"],
        "reasoning_effort": raw["reasoning_effort"],
        "max_total_workers": raw["max_total_workers"],
        "required_stage3_backend": raw["required_stage3_backend"],
        "implementation_status": raw["implementation_status"],
        "installed_artifacts": installed_identities,
        "coverage_contract": copy.deepcopy(expected_coverage),
        "launchable": True,
        "started": False,
    }


def _validate_ladder_design(*, repo_dir: Path, path: Path) -> dict[str, Any]:
    absolute = Path(os.path.abspath(path if path.is_absolute() else repo_dir / path))
    raw, _payload = _read_json_object(absolute, "bounded-ladder design")
    if (
        raw.get("schema_version") != 1
        or raw.get("kind") != "qcode-bounded-target-aware-ladder-design-v1"
        or raw.get("implementation_status") != "design_only"
        or raw.get("launchable") is not False
        or raw.get("thresholds") != [6, 8, "required_distance_minus_1"]
        or raw.get("all_pool_scan_allowed") is not False
    ):
        _fail("LADDER_DESIGN", "bounded-ladder design violates its safety contract")
    return {
        **_relative_config_identity(repo_dir, absolute),
        "implementation_status": raw["implementation_status"],
        "launchable": False,
        "started": False,
        "thresholds": copy.deepcopy(raw["thresholds"]),
        "all_pool_scan_allowed": False,
    }


def build_post_r4_decision(
    *,
    run_root: Path,
    repo_dir: Path | None = None,
    broader_design: Path = DEFAULT_BROADER_DESIGN,
    ladder_design: Path = DEFAULT_LADDER_DESIGN,
    classifier: OutcomeClassifier = classify_evaluation,
    lower_bound_replayer: LowerBoundReplayer = (
        _replayable_search_lower_bound_for_audit
    ),
    digest_authority: DigestAuthority = authoritative_candidate_digest,
    checkpoint_authority: CheckpointAuthority = _default_checkpoint_authority,
) -> dict[str, Any]:
    """Return a self-hashed, evidence-only post-R4 decision.

    The function has no process-control side effects.  In particular, it does
    not stop the source run and does not start the selected experiment.
    """

    selected_repo = (
        Path(__file__).resolve().parent.parent
        if repo_dir is None
        else Path(os.path.abspath(repo_dir))
    )
    selected_root = Path(os.path.abspath(run_root))
    if (
        selected_root.parent.name != "humanize"
        or selected_root.parent.parent.name != "results"
    ):
        _fail(
            "RUN_BOUNDARY",
            "source run root must be results/humanize/<run-id>",
        )
    evidence_repo = selected_root.parent.parent.parent
    _reject_symlink_components(selected_repo, "repository")
    _reject_symlink_components(evidence_repo, "evidence repository")
    _reject_symlink_components(selected_root, "source run root")

    state_path = selected_root / "state.json"
    state_before, _state_payload = _read_json_object(state_path, "state.json")
    prefix_before = _state_prefix(state_before)
    source_run_id = prefix_before["run_id"]
    if selected_root.name != source_run_id:
        _fail("RUN_BOUNDARY", "source run directory does not match state run_id")

    broader = _validate_broader_design(
        repo_dir=selected_repo,
        path=broader_design,
    )
    ladder = _validate_ladder_design(
        repo_dir=selected_repo,
        path=ladder_design,
    )

    all_records: list[dict[str, Any]] = []
    round_evidence: list[dict[str, Any]] = []
    previous_transaction: dict[str, Any] | None = None
    for number in POST_AUDIT_DECISION_ROUNDS:
        round_dir = selected_root / "rounds" / f"round-{number:03d}"
        transaction, transaction_evidence = _validate_transaction(
            run_root=selected_root,
            repo_dir=evidence_repo,
            run_id=source_run_id,
            round_number=number,
            previous_transaction=previous_transaction,
            checkpoint_authority=checkpoint_authority,
        )
        records, artifact_evidence, exact_distances = _validate_round_audits(
            round_number=number,
            round_dir=round_dir,
            classifier=classifier,
            lower_bound_replayer=lower_bound_replayer,
            digest_authority=digest_authority,
        )
        summary = _round_summary(prefix_before, number)
        milp_identity = artifact_evidence["milp"]
        _validate_summary_milp_binding(
            round_number=number,
            summary=summary,
            milp_identity=milp_identity,
            exact_distances=exact_distances,
        )
        artifact_evidence["review"] = _validate_review_binding(
            round_number=number,
            round_dir=round_dir,
            summary=summary,
        )
        round_evidence.append({
            **transaction_evidence,
            **artifact_evidence,
            "state_round_summary_sha256": _canonical_sha256(summary),
        })
        all_records.extend(records)
        previous_transaction = transaction

    state_after, _ = _read_json_object(state_path, "state.json replay")
    prefix_after = _state_prefix(state_after)
    if prefix_after != prefix_before:
        _fail(
            "STATE_COMMIT_CHANGED",
            "the sealed R1-R4 state prefix changed during decision replay",
        )

    candidate_keys = [record["candidate_key"] for record in all_records]
    canonical_digests = [record["canonical_digest"] for record in all_records]
    if (
        len(all_records) != POST_AUDIT_REQUIRED_AUDITS
        or len(set(candidate_keys)) != POST_AUDIT_REQUIRED_AUDITS
        or len(set(canonical_digests)) != POST_AUDIT_REQUIRED_AUDITS
    ):
        _fail(
            "AUDIT_SAMPLE_NOT_DISTINCT",
            "R1-R4 do not contain 24 definition- and structure-distinct audits",
        )

    terminal_count = sum(
        record["outcome"]
        in {AuditOutcome.EXACT.value, AuditOutcome.THRESHOLD_REJECTED.value}
        for record in all_records
    )
    unknown_count = len(all_records) - terminal_count
    lower_bound_records = [
        record for record in all_records if record["cohort"] == "lower_bound"
    ]
    if len(lower_bound_records) != POST_AUDIT_REQUIRED_LB_AUDITS:
        _fail("SELECTION_COHORT", "R1-R4 do not contain 20 replayed LB audits")
    low_upper_count = sum(
        record["trusted_upper_bound_le_8"] for record in lower_bound_records
    )
    survivor_count = len(lower_bound_records) - low_upper_count

    terminal_gate = (
        terminal_count * POST_AUDIT_TERMINAL_DENOMINATOR
        >= len(all_records) * POST_AUDIT_TERMINAL_NUMERATOR
    )
    low_upper_gate = (
        low_upper_count * POST_AUDIT_LOW_UPPER_DENOMINATOR
        >= len(lower_bound_records) * POST_AUDIT_LOW_UPPER_NUMERATOR
    )
    significant_survivors = (
        survivor_count >= POST_AUDIT_MIN_SURVIVORS
        and survivor_count * POST_AUDIT_SURVIVOR_DENOMINATOR
        >= len(lower_bound_records) * POST_AUDIT_SURVIVOR_NUMERATOR
    )
    if not terminal_gate or unknown_count != 0:
        _pending("UNRESOLVED_AUDIT", "the terminal/UNKNOWN decision gate is not closed")

    if low_upper_gate:
        action = "broader_published_volume_coverage"
        reason_code = "LB_LOW_WEIGHT_FAILURE_RATE_AT_LEAST_80_PERCENT"
        next_experiment = broader
    elif significant_survivors:
        action = "bounded_ladder"
        reason_code = "SIGNIFICANT_LB_SURVIVOR_COHORT"
        next_experiment = ladder
    else:
        _fail(
            "DECISION_INCONCLUSIVE",
            "evidence passes terminal gates but neither action threshold is met",
        )

    all_records.sort(
        key=lambda row: (row["round"], row["candidate_key"], row["canonical_digest"])
    )
    metrics = {
        "selected_audits": len(all_records),
        "distinct_candidate_keys": len(set(candidate_keys)),
        "distinct_canonical_digests": len(set(canonical_digests)),
        "terminal_audits": terminal_count,
        "terminal_rate": {
            "numerator": terminal_count,
            "denominator": len(all_records),
        },
        "unknown_audits": unknown_count,
        "lower_bound_audits": len(lower_bound_records),
        "trusted_upper_bound_le_8": low_upper_count,
        "trusted_upper_bound_le_8_rate": {
            "numerator": low_upper_count,
            "denominator": len(lower_bound_records),
        },
        "lb_without_trusted_upper_bound_le_8": survivor_count,
        "significant_survivors": significant_survivors,
    }
    decision = {
        "schema_version": POST_AUDIT_DECISION_SCHEMA_VERSION,
        "kind": POST_AUDIT_DECISION_KIND,
        "status": "ready",
        "source_run_id": source_run_id,
        "source_representation_id": POST_AUDIT_SOURCE_REPRESENTATION,
        "target_mode": POST_AUDIT_TARGET_MODE,
        "evidence_window": {
            "rounds": list(POST_AUDIT_DECISION_ROUNDS),
            "required_distinct_terminal_audits": POST_AUDIT_REQUIRED_AUDITS,
            "required_lower_bound_audits": POST_AUDIT_REQUIRED_LB_AUDITS,
            "candidate_batch_policy_version": 6,
            "state_commit_sha256": _canonical_sha256(prefix_before),
            "round_artifacts_sha256": _canonical_sha256(round_evidence),
        },
        "thresholds": {
            "low_upper_bound": POST_AUDIT_LOW_UPPER_BOUND,
            "published_volume_coverage_low_upper_rate": {
                "numerator": POST_AUDIT_LOW_UPPER_NUMERATOR,
                "denominator": POST_AUDIT_LOW_UPPER_DENOMINATOR,
            },
            "minimum_terminal_rate": {
                "numerator": POST_AUDIT_TERMINAL_NUMERATOR,
                "denominator": POST_AUDIT_TERMINAL_DENOMINATOR,
            },
            "required_unknown_count": 0,
            "significant_survivor_rate": {
                "numerator": POST_AUDIT_SURVIVOR_NUMERATOR,
                "denominator": POST_AUDIT_SURVIVOR_DENOMINATOR,
            },
            "significant_survivor_minimum_count": POST_AUDIT_MIN_SURVIVORS,
        },
        "metrics": metrics,
        "decision": {
            "action": action,
            "reason_code": reason_code,
            "machine_evidence_authoritative": True,
            "reviewer_text_votes": False,
            "reviewer_or_controller_may_trigger": True,
            "launch_authorized": bool(next_experiment["launchable"]),
            "started": False,
        },
        "next_experiment": next_experiment,
        "round_evidence": round_evidence,
        "audits": all_records,
    }
    return _sealed_payload(decision)


def _blocked_payload(
    *,
    run_root: Path,
    error: PostAuditDecisionError,
) -> dict[str, Any]:
    value = {
        "schema_version": POST_AUDIT_DECISION_SCHEMA_VERSION,
        "kind": POST_AUDIT_DECISION_KIND,
        "status": "not_ready" if isinstance(error, PostAuditDecisionNotReady) else "blocked",
        "source_run_id": Path(run_root).name,
        "decision": {
            "action": "none",
            "machine_evidence_authoritative": True,
            "reviewer_text_votes": False,
            "reviewer_or_controller_may_trigger": True,
            "launch_authorized": False,
            "started": False,
        },
        "error": {
            "classification": error.classification,
            "code": error.code,
            "message": str(error),
        },
    }
    return _sealed_payload(value)


def _print_json(value: Any, *, stream: Any = sys.stdout) -> None:
    print(
        json.dumps(value, ensure_ascii=False, indent=2, allow_nan=False),
        file=stream,
        flush=True,
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run-root", type=Path, required=True)
    parser.add_argument(
        "--repo-dir",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
    )
    parser.add_argument("--broader-design", type=Path, default=DEFAULT_BROADER_DESIGN)
    parser.add_argument("--ladder-design", type=Path, default=DEFAULT_LADDER_DESIGN)
    parser.add_argument("--output", type=Path)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        decision = build_post_r4_decision(
            run_root=args.run_root,
            repo_dir=args.repo_dir,
            broader_design=args.broader_design,
            ladder_design=args.ladder_design,
        )
        exit_code = 0
    except PostAuditDecisionError as exc:
        decision = _blocked_payload(run_root=args.run_root, error=exc)
        exit_code = 3 if isinstance(exc, PostAuditDecisionNotReady) else 2
    if args.output is not None:
        atomic_write_json(args.output, decision)
    _print_json(decision, stream=sys.stdout if exit_code == 0 else sys.stderr)
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
