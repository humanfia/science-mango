"""Problem-only answer submissions and controller-side freeze receipts.

The native Archon workflow proves Lean declarations, but a proved declaration
is not itself a uniform, machine-readable exam answer.  This module defines the
small answer artifact written by a target worker and the trusted freeze step
that binds it to the problem-only row, current Lean file, and Review gates.

The implementation deliberately has no grader or official-answer input.
"""

from __future__ import annotations

import hashlib
import json
import math
import os
import re
import stat
import tempfile
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence


SCHEMA_VERSION = 1
FREEZE_PROTOCOL = "archon-native-answer-submission-freeze-v1"
FORMALIZATION_GATE_FILENAME = "formalization-review-gate.json"
PROOF_GATE_FILENAME = "proof-review-gate.json"

_TARGET_ID = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_.-]*$")
_SUBMISSION_FIELDS = {
    "schema_version",
    "id",
    "official_answer_seen",
    "outputs",
}
_OUTPUT_FIELDS = {"id", "kind", "raw_value", "display_value", "unit"}
_FORBIDDEN_ROW_FIELDS = {"answer", "grader", "official_answer", "rubric", "solution"}
_MAX_BUNDLE_BYTES = 64 * 1024 * 1024
_MAX_SUBMISSION_BYTES = 1024 * 1024
_MAX_GATE_BYTES = 64 * 1024 * 1024
_MAX_LEAN_BYTES = 64 * 1024 * 1024
_MAX_RAW_STRING_LENGTH = 64 * 1024
_SHA256 = re.compile(r"^[0-9a-f]{64}$")
_INTEGER_DISPLAY = re.compile(r"^[+-]?[0-9]+$")
_NUMERIC_DISPLAY = re.compile(
    r"^[+-]?(?:(?:[0-9]+(?:\.[0-9]*)?)|(?:\.[0-9]+))"
    r"(?:[eE][+-]?[0-9]+)?$"
)
_NUMERIC_TIMES_TEN_DISPLAY = re.compile(
    r"^[+-]?(?:(?:[0-9]+(?:\.[0-9]*)?)|(?:\.[0-9]+))"
    r"[ \t]*×[ \t]*10\^[+-]?[0-9]+$"
)
_REPORTING_POLICIES = {
    "formula": frozenset({"exact_symbolic"}),
    "classification": frozenset({"exact_symbolic"}),
    "finite_set": frozenset({"exact_symbolic"}),
    "integer": frozenset({"exact_integer"}),
    "numeric": frozenset({"decimal_places", "significant_figures"}),
}
_INVALID_SUBMISSION_CODES = frozenset(
    {
        "unsafe_file",
        "size_limit",
        "invalid_json",
        "invalid_contract",
    }
)


class AnswerSubmissionError(ValueError):
    """A problem-only submission cannot be validated or frozen safely."""


def _fail(message: str) -> None:
    raise AnswerSubmissionError(message)


def _validate_target_id(target_id: object) -> str:
    if not isinstance(target_id, str) or not _TARGET_ID.fullmatch(target_id):
        _fail(f"invalid target id: {target_id!r}")
    return target_id


def answer_submission_relative_path(target_id: str) -> Path:
    """Return the only worker-writable answer path for ``target_id``."""

    target_id = _validate_target_id(target_id)
    slug = f"IChO2026Problems_problem_{target_id}"
    return Path(".archon") / "task_results" / f"{slug}.answer.json"


def answer_submission_path(workspace: Path | str, target_id: str) -> Path:
    """Return a target's answer path below a workspace without resolving it."""

    return Path(workspace) / answer_submission_relative_path(target_id)


def lean_target_relative_path(target_id: str) -> Path:
    """Return the native Lean target path corresponding to a blind row id."""

    target_id = _validate_target_id(target_id)
    return Path("IChO2026Problems") / f"problem_{target_id}.lean"


def _sha256(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def _canonical_json_bytes(value: Any) -> bytes:
    try:
        return (
            json.dumps(
                value,
                ensure_ascii=False,
                sort_keys=True,
                separators=(",", ":"),
            )
            + "\n"
        ).encode("utf-8")
    except (UnicodeEncodeError, ValueError, RecursionError) as exc:
        raise AnswerSubmissionError(
            "JSON value cannot be canonicalized safely"
        ) from exc


def _pretty_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + "\n"
    ).encode("utf-8")


def _plain_directory(path: Path, *, label: str) -> Path:
    if path.is_symlink():
        _fail(f"{label} must not be a symbolic link: {path}")
    try:
        resolved = path.resolve(strict=True)
    except OSError as exc:
        raise AnswerSubmissionError(f"{label} is unavailable: {path}") from exc
    if not resolved.is_dir():
        _fail(f"{label} is not a directory: {path}")
    return resolved


def _read_regular_file(path: Path, *, label: str, limit: int) -> bytes:
    if path.is_symlink():
        _fail(f"{label} must not be a symbolic link: {path}")
    try:
        metadata = path.stat()
    except OSError as exc:
        raise AnswerSubmissionError(f"{label} is unavailable: {path}") from exc
    if not stat.S_ISREG(metadata.st_mode) or metadata.st_nlink != 1:
        _fail(f"{label} must be a single-linked regular file: {path}")
    if metadata.st_size > limit:
        _fail(f"{label} exceeds the {limit}-byte limit: {path}")
    try:
        payload = path.read_bytes()
    except OSError as exc:
        raise AnswerSubmissionError(f"cannot read {label}: {path}") from exc
    if len(payload) > limit:
        _fail(f"{label} exceeds the {limit}-byte limit: {path}")
    return payload


def _capture_solver_payload(
    path: Path, *, root: Path, limit: int
) -> tuple[str, bytes | None, str | None]:
    """Read an untrusted solver artifact without turning it into a batch error."""

    try:
        relative = path.relative_to(root)
    except ValueError:
        return "invalid", None, "unsafe_file"
    current = root
    for part in relative.parts[:-1]:
        current /= part
        try:
            metadata = current.lstat()
        except FileNotFoundError:
            return "missing", None, "missing"
        except OSError:
            return "invalid", None, "unsafe_file"
        if current.is_symlink() or not stat.S_ISDIR(metadata.st_mode):
            return "invalid", None, "unsafe_file"

    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0)
    nofollow = getattr(os, "O_NOFOLLOW", 0)
    if nofollow:
        flags |= nofollow
    if path.is_symlink():
        return "invalid", None, "unsafe_file"
    try:
        descriptor = os.open(path, flags)
    except FileNotFoundError:
        return "missing", None, "missing"
    except OSError:
        return "invalid", None, "unsafe_file"
    try:
        metadata = os.fstat(descriptor)
        if not stat.S_ISREG(metadata.st_mode) or metadata.st_nlink != 1:
            return "invalid", None, "unsafe_file"
        if metadata.st_size > limit:
            return "invalid", None, "size_limit"
        chunks: list[bytes] = []
        remaining = limit + 1
        while remaining:
            chunk = os.read(descriptor, min(remaining, 1024 * 1024))
            if not chunk:
                break
            chunks.append(chunk)
            remaining -= len(chunk)
        payload = b"".join(chunks)
        if len(payload) > limit:
            return "invalid", None, "size_limit"
        return "valid", payload, None
    except OSError:
        return "invalid", None, "unsafe_file"
    finally:
        os.close(descriptor)


def _inside(path: Path, root: Path) -> bool:
    try:
        path.relative_to(root)
    except ValueError:
        return False
    return True


def _parse_json_object(payload: bytes, *, label: str) -> dict[str, Any]:
    try:
        value = json.loads(payload)
    except (UnicodeDecodeError, ValueError, RecursionError) as exc:
        raise AnswerSubmissionError(f"{label} is not valid UTF-8 JSON") from exc
    if not isinstance(value, dict):
        _fail(f"{label} must contain one JSON object")
    return value


def _bundle_rows(payload: bytes) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for line_number, line in enumerate(payload.splitlines(), start=1):
        if not line.strip():
            _fail(f"questions-only bundle contains a blank line at {line_number}")
        rows.append(_parse_json_object(line, label=f"questions-only row {line_number}"))
    if not rows:
        _fail("questions-only bundle is empty")
    return rows


def _requested_output_contracts(
    row: Mapping[str, Any], *, target_id: str
) -> tuple[dict[str, Any], ...]:
    if row.get("official_answer_seen") is not False:
        _fail(f"problem-only row {target_id} requires official_answer_seen=false")
    leaked = sorted(_FORBIDDEN_ROW_FIELDS.intersection(row))
    if leaked:
        _fail(
            f"problem-only row {target_id} contains forbidden field(s): "
            + ", ".join(leaked)
        )
    outputs = row.get("requested_outputs")
    if not isinstance(outputs, list) or not outputs:
        _fail(f"problem-only row {target_id} has no requested_outputs")
    normalized: list[dict[str, Any]] = []
    seen: set[str] = set()
    for index, output in enumerate(outputs):
        if not isinstance(output, Mapping):
            _fail(f"problem-only row {target_id} output {index} is not an object")
        output_id = output.get("id")
        kind = output.get("kind")
        unit = output.get("unit")
        reporting_policy = output.get("reporting_policy")
        if (
            not isinstance(output_id, str)
            or not _TARGET_ID.fullmatch(output_id)
        ):
            _fail(f"problem-only row {target_id} output {index} has an invalid id")
        if output_id in seen:
            _fail(f"problem-only row {target_id} repeats output id {output_id!r}")
        if not isinstance(kind, str) or kind not in _REPORTING_POLICIES:
            _fail(f"problem-only row {target_id}/{output_id} has an invalid kind")
        if not isinstance(unit, str):
            _fail(f"problem-only row {target_id}/{output_id} has an invalid unit")
        if not isinstance(reporting_policy, Mapping):
            _fail(
                f"problem-only row {target_id}/{output_id} has an invalid "
                "reporting_policy"
            )
        policy_kind = reporting_policy.get("kind")
        if policy_kind not in _REPORTING_POLICIES[kind]:
            _fail(
                f"problem-only row {target_id}/{output_id} has an unsafe "
                f"kind/reporting_policy pair: {kind}/{policy_kind}"
            )
        if policy_kind in {"decimal_places", "significant_figures"}:
            digits = reporting_policy.get("digits")
            minimum = 0 if policy_kind == "decimal_places" else 1
            if (
                isinstance(digits, bool)
                or not isinstance(digits, int)
                or not minimum <= digits <= 100
            ):
                _fail(
                    f"problem-only row {target_id}/{output_id} has invalid "
                    "reporting digits"
                )
        seen.add(output_id)
        normalized.append(
            {
                "id": output_id,
                "kind": kind,
                "unit": unit,
                "reporting_policy_kind": policy_kind,
            }
        )
    return tuple(normalized)


def _validate_answer_value(value: Any, *, field: str) -> None:
    if isinstance(value, bool) or value is None:
        _fail(f"{field} must be a non-boolean scalar")
    if isinstance(value, str):
        if not value.strip() or len(value) > _MAX_RAW_STRING_LENGTH:
            _fail(f"{field} must not be empty")
        return
    if isinstance(value, int):
        return
    if isinstance(value, float) and math.isfinite(value):
        return
    _fail(f"{field} must be a finite JSON string or number")


def _validate_output_values(
    output: Mapping[str, Any], *, target_id: str, contract: Mapping[str, Any]
) -> None:
    """Validate the small scalar value surface without interpreting chemistry."""

    output_id = contract["id"]
    kind = contract["kind"]
    raw_value = output.get("raw_value")
    display_value = output.get("display_value")
    _validate_answer_value(
        raw_value,
        field=f"submission {target_id}/{output_id}.raw_value",
    )
    if not isinstance(display_value, str) or not display_value.strip():
        _fail(
            f"submission {target_id}/{output_id}.display_value must be a "
            "non-empty JSON string"
        )
    if len(display_value) > _MAX_RAW_STRING_LENGTH:
        _fail(f"submission {target_id}/{output_id}.display_value is too long")
    if kind == "integer" and not (
        isinstance(raw_value, int) and not isinstance(raw_value, bool)
        or isinstance(raw_value, str)
    ):
        _fail(
            f"submission {target_id}/{output_id}.raw_value must be an integer "
            "or exact symbolic string"
        )
    if kind in {"formula", "classification", "finite_set"} and not isinstance(
        raw_value, str
    ):
        _fail(
            f"submission {target_id}/{output_id}.raw_value must be a string "
            f"for kind={kind}"
        )
    if kind == "integer" and not _INTEGER_DISPLAY.fullmatch(display_value):
        _fail(
            f"submission {target_id}/{output_id}.display_value must be a "
            "lexical integer"
        )
    if kind == "numeric" and not (
        _NUMERIC_DISPLAY.fullmatch(display_value)
        or _NUMERIC_TIMES_TEN_DISPLAY.fullmatch(display_value)
    ):
        _fail(
            f"submission {target_id}/{output_id}.display_value must be a "
            "finite decimal or scientific value"
        )


def validate_answer_submission(
    submission: Mapping[str, Any],
    *,
    row: Mapping[str, Any],
    target_id: str,
) -> dict[str, Any]:
    """Validate and normalize one answer against its problem-only row."""

    target_id = _validate_target_id(target_id)
    if set(submission) != _SUBMISSION_FIELDS:
        missing = sorted(_SUBMISSION_FIELDS - set(submission))
        extra = sorted(set(submission) - _SUBMISSION_FIELDS)
        pieces = []
        if missing:
            pieces.append(f"missing {missing}")
        if extra:
            pieces.append(f"unexpected {extra}")
        _fail(f"submission {target_id} has invalid fields: {'; '.join(pieces)}")
    if submission.get("schema_version") != SCHEMA_VERSION:
        _fail(f"submission {target_id} requires schema_version={SCHEMA_VERSION}")
    if submission.get("id") != target_id:
        _fail(f"submission id does not match target {target_id}")
    if submission.get("official_answer_seen") is not False:
        _fail(f"submission {target_id} requires official_answer_seen=false")

    expected = _requested_output_contracts(row, target_id=target_id)
    outputs = submission.get("outputs")
    if not isinstance(outputs, list) or len(outputs) != len(expected):
        _fail(
            f"submission {target_id} must contain exactly {len(expected)} output(s)"
        )

    normalized_outputs: list[dict[str, Any]] = []
    for index, (output, contract) in enumerate(zip(outputs, expected, strict=True)):
        if not isinstance(output, Mapping) or set(output) != _OUTPUT_FIELDS:
            _fail(f"submission {target_id} output {index} has invalid fields")
        for field in ("id", "kind", "unit"):
            if output.get(field) != contract[field]:
                _fail(
                    f"submission {target_id} output {index} {field} does not "
                    "match requested_outputs"
                )
        _validate_output_values(
            output, target_id=target_id, contract=contract
        )
        normalized_outputs.append(dict(output))

    return {
        "schema_version": SCHEMA_VERSION,
        "id": target_id,
        "official_answer_seen": False,
        "outputs": normalized_outputs,
    }


def _capture_submission(
    root: Path, *, row: Mapping[str, Any], target_id: str
) -> tuple[dict[str, Any], str | None]:
    rel = answer_submission_relative_path(target_id)
    path = root / rel
    status, payload, error_code = _capture_solver_payload(
        path, root=root, limit=_MAX_SUBMISSION_BYTES
    )
    base: dict[str, Any] = {
        "status": status,
        "path": rel.as_posix(),
        "file_sha256": _sha256(payload) if payload is not None else None,
    }
    if status == "missing":
        base["error_code"] = "missing"
        return base, None
    if status == "invalid":
        if error_code not in _INVALID_SUBMISSION_CODES:
            error_code = "unsafe_file"
        base["error_code"] = error_code
        return base, None
    assert payload is not None
    try:
        parsed = json.loads(payload)
    except (
        UnicodeDecodeError,
        ValueError,
        RecursionError,
    ):
        base.update({"status": "invalid", "error_code": "invalid_json"})
        return base, None
    if not isinstance(parsed, Mapping):
        base.update({"status": "invalid", "error_code": "invalid_contract"})
        return base, None
    try:
        normalized = validate_answer_submission(
            parsed, row=row, target_id=target_id
        )
        canonical_sha256 = _sha256(_canonical_json_bytes(normalized))
    except (AnswerSubmissionError, RecursionError):
        base.update({"status": "invalid", "error_code": "invalid_contract"})
        return base, None
    base.update(
        {
            "canonical_sha256": canonical_sha256,
            "value": normalized,
        }
    )
    return base, _sha256(payload)


def _capture_lean(root: Path, *, target_id: str) -> tuple[dict[str, Any], str | None]:
    rel = lean_target_relative_path(target_id)
    status, payload, error_code = _capture_solver_payload(
        root / rel, root=root, limit=_MAX_LEAN_BYTES
    )
    snapshot: dict[str, Any] = {
        "status": status,
        "path": rel.as_posix(),
        "sha256": _sha256(payload) if payload is not None else None,
    }
    if status != "valid":
        snapshot["error_code"] = error_code
        return snapshot, None
    assert payload is not None
    return snapshot, _sha256(payload)


def _review_source_contracts(
    record: Mapping[str, Any],
) -> tuple[list[tuple[str, Mapping[str, Any]]], bool]:
    found: list[tuple[str, Mapping[str, Any]]] = []
    malformed = False

    def add(container: Mapping[str, Any], field: str, location: str) -> None:
        nonlocal malformed
        if field not in container:
            return
        contract = container[field]
        if isinstance(contract, Mapping):
            found.append((location, contract))
        else:
            malformed = True

    add(record, "source_contract", "source_contract")
    certificate = record.get("certificate")
    if certificate is not None:
        if isinstance(certificate, Mapping):
            add(certificate, "source_contract", "certificate.source_contract")
            nested_blind = certificate.get("blind_review_certificate")
            if nested_blind is not None:
                if isinstance(nested_blind, Mapping):
                    add(
                        nested_blind,
                        "source_contract",
                        "certificate.blind_review_certificate.source_contract",
                    )
                else:
                    malformed = True
        else:
            malformed = True
    blind = record.get("blind_review_certificate")
    if blind is not None:
        if isinstance(blind, Mapping):
            add(
                blind,
                "source_contract",
                "blind_review_certificate.source_contract",
            )
        else:
            malformed = True
    return found, malformed


def _source_contract_binding(
    contract: Mapping[str, Any],
    *,
    target_id: str,
    target_rel: str,
    bundle_rel: str,
    bundle_sha256: str,
    record_sha256: str,
    submission_rel: str,
    submission_sha256: str | None,
) -> tuple[bool, str | None]:
    expected = {
        "schema_version": 1,
        "contract_kind": "native_problem_input_only",
        "authority": "problem-only",
        "evaluation_mode": "answer_blind",
        "target": target_rel,
        "source_bundle": bundle_rel,
        "source_bundle_sha256": bundle_sha256,
        "source_record_id": target_id,
        "source_record_sha256": record_sha256,
        "answer_submission": submission_rel,
        "answer_submission_sha256": submission_sha256,
        "candidate": target_rel,
    }
    if submission_sha256 is None or any(
        contract.get(key) != value for key, value in expected.items()
    ):
        return False, None
    candidate = contract.get("candidate_sha256")
    if not isinstance(candidate, str) or not _SHA256.fullmatch(candidate):
        return False, None
    return True, candidate


def _empty_gate_snapshot(status: str) -> dict[str, Any]:
    return {
        "status": status,
        "candidate_sha256": None,
        "candidate_matches_current_lean": False,
        "candidate_matches_source_contract": False,
        "source_contract_status": status,
        "source_contract_locations": [],
        "answer_submission_sha256": None,
    }


def _load_gate_snapshot(
    state_dir: Path,
    *,
    filename: str,
    target_rel: str,
    required_status: str,
    lean_sha256: str | None,
    target_id: str,
    bundle_rel: str,
    bundle_sha256: str,
    record_sha256: str,
    submission_rel: str,
    submission_sha256: str | None,
) -> dict[str, Any]:
    path = state_dir / filename
    artifact_status, payload, _ = _capture_solver_payload(
        path, root=state_dir.parent, limit=_MAX_GATE_BYTES
    )
    if artifact_status == "missing":
        return _empty_gate_snapshot("missing")
    if artifact_status != "valid" or payload is None:
        return _empty_gate_snapshot("malformed")
    try:
        state = json.loads(payload)
    except (
        UnicodeDecodeError,
        ValueError,
        RecursionError,
    ):
        return _empty_gate_snapshot("malformed")
    if not isinstance(state, Mapping):
        return _empty_gate_snapshot("malformed")
    targets = state.get("targets")
    if not isinstance(targets, Mapping):
        return _empty_gate_snapshot("malformed")
    record = targets.get(target_rel)
    if record is None:
        return _empty_gate_snapshot("missing")
    if not isinstance(record, Mapping):
        return _empty_gate_snapshot("malformed")
    status_value = record.get("status")
    if not isinstance(status_value, str) or not status_value.strip():
        return _empty_gate_snapshot("malformed")
    bounded_status = (
        required_status
        if status_value.strip() == required_status
        else f"not_{required_status}"
    )
    candidate = record.get("candidate_sha256")
    if not isinstance(candidate, str) or not _SHA256.fullmatch(candidate):
        return _empty_gate_snapshot("malformed")
    contracts, malformed = _review_source_contracts(record)
    locations = [location for location, _ in contracts]
    bindings = [
        _source_contract_binding(
            contract,
            target_id=target_id,
            target_rel=target_rel,
            bundle_rel=bundle_rel,
            bundle_sha256=bundle_sha256,
            record_sha256=record_sha256,
            submission_rel=submission_rel,
            submission_sha256=submission_sha256,
        )
        for _, contract in contracts
    ]
    contract_candidates = {
        contract_candidate
        for bound, contract_candidate in bindings
        if bound and contract_candidate is not None
    }
    all_bound = (
        bool(contracts)
        and not malformed
        and all(bound for bound, _ in bindings)
        and len(contract_candidates) == 1
    )
    contract_candidate = next(iter(contract_candidates), None)
    candidate_matches_contract = all_bound and candidate == contract_candidate
    source_status = (
        "malformed"
        if malformed
        else "missing"
        if not contracts
        else "bound"
        if all_bound
        else "unbound"
    )
    return {
        "status": bounded_status,
        "candidate_sha256": candidate,
        "candidate_matches_current_lean": (
            lean_sha256 is not None and candidate == lean_sha256
        ),
        "candidate_matches_source_contract": candidate_matches_contract,
        "source_contract_status": source_status,
        "source_contract_locations": locations,
        "answer_submission_sha256": (
            submission_sha256 if all_bound else None
        ),
    }


def _existing_freeze_matches(path: Path, payload: bytes) -> bool:
    try:
        metadata = path.lstat()
    except FileNotFoundError:
        return False
    except OSError as exc:
        raise AnswerSubmissionError(
            f"freeze output is unavailable: {path}"
        ) from exc
    if not stat.S_ISREG(metadata.st_mode):
        _fail(f"freeze output must be a regular file or absent: {path}")
    try:
        existing = path.read_bytes()
    except OSError as exc:
        raise AnswerSubmissionError(f"cannot read freeze output: {path}") from exc
    if existing != payload:
        _fail(f"freeze output already exists with different contents: {path}")
    return True


def _atomic_create_once(path: Path, payload: bytes) -> None:
    parent = _plain_directory(path.parent, label="freeze output parent")
    if _existing_freeze_matches(path, payload):
        return
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{path.name}.", suffix=".tmp", dir=parent
    )
    temporary = Path(temporary_name)
    installed = False
    try:
        os.fchmod(descriptor, 0o600)
        with os.fdopen(descriptor, "wb", closefd=True) as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        descriptor = -1
        try:
            os.link(temporary, path, follow_symlinks=False)
            installed = True
        except FileExistsError:
            if not _existing_freeze_matches(path, payload):
                _fail(f"freeze output creation raced: {path}")
        if installed:
            directory_fd = os.open(parent, os.O_RDONLY | os.O_DIRECTORY)
            try:
                os.fsync(directory_fd)
            finally:
                os.close(directory_fd)
    finally:
        if descriptor >= 0:
            os.close(descriptor)
        if temporary.exists() or temporary.is_symlink():
            temporary.unlink()


def freeze_answer_submissions(
    workspace: Path | str,
    bundle_path: Path | str,
    target_ids: Sequence[str] | Iterable[str],
    output_path: Path | str,
) -> dict[str, Any]:
    """Validate and atomically freeze answer submissions outside a workspace.

    The caller must quiesce the campaign before invoking this function.  The
    returned receipt hashes the exact freeze file written to ``output_path``.
    """

    root = _plain_directory(Path(workspace), label="workspace")
    ids = tuple(_validate_target_id(target_id) for target_id in target_ids)
    if not ids or len(set(ids)) != len(ids):
        _fail("target_ids must be a nonempty sequence without duplicates")

    bundle = Path(bundle_path)
    if bundle.is_symlink():
        _fail(f"questions-only bundle must not be a symbolic link: {bundle}")
    try:
        bundle = bundle.resolve(strict=True)
    except OSError as exc:
        raise AnswerSubmissionError(
            f"questions-only bundle is unavailable: {bundle_path}"
        ) from exc
    if not _inside(bundle, root) or bundle.name != "questions_only.jsonl":
        _fail("bundle_path must name questions_only.jsonl inside the workspace")
    bundle_payload = _read_regular_file(
        bundle, label="questions-only bundle", limit=_MAX_BUNDLE_BYTES
    )
    rows = _bundle_rows(bundle_payload)
    rows_by_id: dict[str, dict[str, Any]] = {}
    for row in rows:
        target_id = row.get("id")
        if not isinstance(target_id, str) or not _TARGET_ID.fullmatch(target_id):
            _fail("questions-only bundle contains a row with an invalid id")
        if target_id in rows_by_id:
            _fail(f"questions-only bundle repeats target id {target_id}")
        rows_by_id[target_id] = row
    if tuple(rows_by_id) != ids:
        _fail("questions-only bundle ids/order must exactly equal target_ids")

    # Bundle contracts are trusted controller inputs: any malformed or unsafe
    # output contract aborts before solver artifacts are captured.
    for target_id in ids:
        _requested_output_contracts(rows_by_id[target_id], target_id=target_id)
    bundle_rel = bundle.relative_to(root).as_posix()
    bundle_sha256 = _sha256(bundle_payload)

    output = Path(output_path)
    if not output.is_absolute():
        output = output.absolute()
    try:
        resolved_output_parent = output.parent.resolve(strict=True)
    except OSError as exc:
        raise AnswerSubmissionError(
            f"freeze output parent is unavailable: {output.parent}"
        ) from exc
    resolved_output = resolved_output_parent / output.name
    if _inside(resolved_output, root):
        _fail("freeze output must be outside the solver workspace")

    frozen_targets: list[dict[str, Any]] = []
    state_dir = root / ".archon"
    counts = {"valid": 0, "missing": 0, "invalid": 0, "certified": 0}
    for target_id in ids:
        row = rows_by_id[target_id]
        submission_rel = answer_submission_relative_path(target_id)
        submission, submission_sha256 = _capture_submission(
            root, row=row, target_id=target_id
        )
        counts[submission["status"]] += 1

        lean_rel = lean_target_relative_path(target_id)
        target_rel = lean_rel.as_posix()
        lean, lean_sha256 = _capture_lean(root, target_id=target_id)
        record_sha256 = _sha256(_canonical_json_bytes(row))
        common_gate_args = {
            "state_dir": state_dir,
            "target_rel": target_rel,
            "lean_sha256": lean_sha256,
            "target_id": target_id,
            "bundle_rel": bundle_rel,
            "bundle_sha256": bundle_sha256,
            "record_sha256": record_sha256,
            "submission_rel": submission_rel.as_posix(),
            "submission_sha256": submission_sha256,
        }
        formal = _load_gate_snapshot(
            filename=FORMALIZATION_GATE_FILENAME,
            required_status="passed",
            **common_gate_args,
        )
        proof = _load_gate_snapshot(
            filename=PROOF_GATE_FILENAME,
            required_status="solved",
            **common_gate_args,
        )
        same_answer_sha = (
            submission_sha256 is not None
            and formal["answer_submission_sha256"] == submission_sha256
            and proof["answer_submission_sha256"] == submission_sha256
        )
        lean_certified = bool(
            submission["status"] == "valid"
            and lean["status"] == "valid"
            and formal["status"] == "passed"
            and formal["source_contract_status"] == "bound"
            and formal["candidate_matches_source_contract"]
            # The formal Review may legitimately certify an earlier Lean body.
            and proof["status"] == "solved"
            and proof["source_contract_status"] == "bound"
            and proof["candidate_matches_source_contract"]
            and proof["candidate_matches_current_lean"]
            and same_answer_sha
        )
        if lean_certified:
            counts["certified"] += 1
        frozen_targets.append(
            {
                "id": target_id,
                "blind_record_sha256": record_sha256,
                "submission": submission,
                "lean": lean,
                "gates": {
                    "formalization_review": formal,
                    "proof_review": proof,
                },
                "lean_certified": lean_certified,
            }
        )

    freeze = {
        "schema_version": SCHEMA_VERSION,
        "protocol": FREEZE_PROTOCOL,
        "official_answer_seen": False,
        "bundle": {
            "path": bundle_rel,
            "sha256": bundle_sha256,
        },
        "target_ids": list(ids),
        "counts": counts,
        "targets": frozen_targets,
    }
    payload = _pretty_json_bytes(freeze)
    _atomic_create_once(resolved_output, payload)
    return {
        "output_path": str(resolved_output),
        "output_sha256": _sha256(payload),
        "target_count": len(frozen_targets),
        "counts": counts,
        "valid_count": counts["valid"],
        "missing_count": counts["missing"],
        "invalid_count": counts["invalid"],
        "certified_count": counts["certified"],
    }


__all__ = [
    "AnswerSubmissionError",
    "FREEZE_PROTOCOL",
    "SCHEMA_VERSION",
    "answer_submission_path",
    "answer_submission_relative_path",
    "freeze_answer_submissions",
    "lean_target_relative_path",
    "validate_answer_submission",
]
