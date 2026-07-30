#!/usr/bin/env python3
"""Rank, deduplicate, and deeply audit a pool of qLDPC candidates."""

from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import math
import os
import stat
import struct
import sys
import time
import uuid
from collections import deque
from concurrent.futures import FIRST_COMPLETED, ProcessPoolExecutor, wait
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Iterable, Mapping

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation.bb_code import (
    build_bb_code,
    get_code_params_fast,
    validate_terms,
)
from evaluation.certificate_dispatch import build_certificate, verify_certificate
from evaluation.final_gate import classify_win, minimum_winning_distance
from evaluation.process_hard_wall import (
    DEFAULT_TERMINATION_GRACE_S,
    positive_wall_timeout,
    terminate_process_pool,
)
from evaluation.proof_runtime import (
    SOLVER_RUNTIME_PACKAGES,
    proof_runtime_fingerprint,
)
from evaluation.proof_triage import (
    candidate_identity,
    deduplicate_ranked,
    normalize_record,
    rank_record,
    stable_sort_key,
)
from evaluation.registry import (
    DEFAULT_REGISTRY,
    check_code_novelty,
    load_registry,
)
from evaluation.selection_ledger import (
    SELECTION_LEDGER_GATE as SHARED_SELECTION_LEDGER_GATE,
    SELECTION_LEDGER_SCHEMA_VERSION as SHARED_SELECTION_LEDGER_SCHEMA_VERSION,
    install_pending_page,
    make_scan_evidence,
    make_selection_page,
    new_selection_ledger,
    snapshot_identity_sha256,
    validate_selection_ledger,
)
from humanize.audit_state import (
    AuditOutcome,
    AuditStateError,
    classify_evaluation,
)
from scripts.screen_frontier_candidate import (
    STAGE3_GATE,
    claim_from_threshold_artifact,
)
from scripts.screen_frontier_xor import (
    TERMINAL_STATUSES,
    load_replayable_sectors,
    solve_sector,
    verify_bb_translation_symmetry,
    write_artifact,
)


PROJECT = Path(__file__).resolve().parent.parent
DEFAULT_KNOWN_ANSWER = PROJECT / "results" / "known_answer_gate.json"
CACHE_SCHEMA_VERSION = 2
SELECTION_LEDGER_SCHEMA_VERSION = SHARED_SELECTION_LEDGER_SCHEMA_VERSION
SELECTION_LEDGER_GATE = SHARED_SELECTION_LEDGER_GATE
RANKED_SNAPSHOT_SCHEMA_VERSION = 1
RANKED_SNAPSHOT_GATE = "qldpc-stage2-ranked-snapshot"
RANKED_SNAPSHOT_CHUNK_ROWS = 128
CERTIFIABLE_PROOF_STATUSES = frozenset({
    "THRESHOLD_PROVEN",
    "EXACT_PROVEN",
})
_TRUSTED_STAGE1_OUTCOME = "_trusted_stage1_outcome"
_AUTHORITATIVE_GEOMETRY = "authoritative_geometry"
_INPUT_TERMINAL_MARKERS = (
    _TRUSTED_STAGE1_OUTCOME,
    "trusted_stage1_audit",
    "campaign_selected",
    "campaign_audit",
    "campaign_skip_reason",
    "campaign_skip_error",
)


class NoveltyReplayError(RuntimeError):
    """The authoritative novelty checker could not produce trusted evidence."""


@dataclass(frozen=True)
class AuditConfig:
    """Serializable configuration for one candidate-audit worker."""

    state_dir: Path
    solver_timeout_s: float = 300
    solver_workers: int = 4
    seed: int = 0
    resume: bool = True
    certify: bool = True
    known_answer_artifact: Path = DEFAULT_KNOWN_ANSWER
    certificate_timeout_per_logical_s: float = 300
    certificate_total_timeout_s: float = 7200
    certificate_solver_workers: int = 1
    verification_timeout_per_logical_s: float = 300
    verification_total_timeout_s: float = 7200
    candidate_hard_timeout_s: float | None = None
    certificate_hard_timeout_s: float | None = None
    hard_wall_termination_grace_s: float = DEFAULT_TERMINATION_GRACE_S


def _atomic_write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(
        f".{path.name}.{os.getpid()}.{uuid.uuid4().hex}.tmp",
    )
    try:
        with temporary.open("w") as stream:
            stream.write(text)
            stream.flush()
            os.fsync(stream.fileno())
        temporary.replace(path)
        try:
            directory_fd = os.open(path.parent, os.O_RDONLY)
        except OSError:
            directory_fd = None
        if directory_fd is not None:
            try:
                os.fsync(directory_fd)
            finally:
                os.close(directory_fd)
    finally:
        temporary.unlink(missing_ok=True)


def _atomic_write_bytes(path: Path, payload: bytes) -> None:
    """Atomically replace one binary cache artifact and fsync its directory."""

    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(
        f".{path.name}.{os.getpid()}.{uuid.uuid4().hex}.tmp",
    )
    try:
        with temporary.open("wb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        temporary.replace(path)
        try:
            directory_fd = os.open(path.parent, os.O_RDONLY)
        except OSError:
            directory_fd = None
        if directory_fd is not None:
            try:
                os.fsync(directory_fd)
            finally:
                os.close(directory_fd)
    finally:
        temporary.unlink(missing_ok=True)


def atomic_write_json(path: Path, value: Mapping[str, Any]) -> None:
    """Atomically write one JSON object."""

    _atomic_write_text(path, json.dumps(value, indent=2) + "\n")


def atomic_write_jsonl(
    path: Path,
    rows: Iterable[Mapping[str, Any]],
) -> None:
    """Atomically write JSONL without exposing a partially written ranking."""

    _atomic_write_text(
        path,
        "".join(json.dumps(dict(row), sort_keys=True) + "\n" for row in rows),
    )


def read_candidate_jsonl(
    paths: Iterable[Path],
) -> tuple[list[dict[str, Any]], list[str]]:
    """Read candidate objects and retain a source path for every input row."""

    records: list[dict[str, Any]] = []
    sources: list[str] = []
    for path in paths:
        with path.open() as stream:
            for line_number, line in enumerate(stream, start=1):
                if not line.strip():
                    continue
                try:
                    value = json.loads(line)
                except json.JSONDecodeError as exc:
                    raise ValueError(
                        f"{path}:{line_number}: invalid JSON: {exc.msg}",
                    ) from exc
                if not isinstance(value, dict):
                    raise ValueError(
                        f"{path}:{line_number}: candidate must be an object",
                    )
                records.append(value)
                sources.append(str(path))
    return records, sources


def _trusted_stage1_outcome(
    record: Mapping[str, Any],
    required_distance: int,
) -> tuple[str | None, bool]:
    """Replay a formal Stage 1 audit before using it as a priority lane."""

    attempt = record.get("audit_attempt")
    if not isinstance(attempt, Mapping) or attempt.get("schema_version") != 2:
        return None, False
    outcome = classify_evaluation(record)
    if outcome is AuditOutcome.THRESHOLD_REJECTED:
        return "REJECTED", True
    if outcome is not AuditOutcome.EXACT:
        return None, True
    try:
        n = int(record["n"])
        k = int(record["k"])
        d = int(record["d"])
    except (KeyError, TypeError, ValueError) as exc:
        raise AuditStateError("formal Stage 1 exact row has invalid n/k/d") from exc
    gate = classify_win(n, k, d)
    expected = minimum_winning_distance(n, k)
    if expected != required_distance:
        raise AuditStateError("formal Stage 1 threshold binding changed")
    return (
        "THRESHOLD_PROVEN" if gate["passed"] is True else "REJECTED",
        True,
    )


def _promote_trusted_stage1_rows(
    ranked: list[dict[str, Any]],
    prepared: list[dict[str, Any]],
    sources: list[str],
) -> tuple[list[dict[str, Any]], dict[str, int]]:
    """Replace each duplicate group with its formally replayed Stage 1 row."""

    trusted: dict[str, dict[str, Any]] = {}
    for line_number, (record, source) in enumerate(
        zip(prepared, sources, strict=True),
        start=1,
    ):
        outcome = record.get(_TRUSTED_STAGE1_OUTCOME)
        if outcome not in {"THRESHOLD_PROVEN", "REJECTED"}:
            continue
        promoted = rank_record(record, source=source, line_number=line_number)
        digest = str(promoted["triage_identity"]["canonical_digest"])
        current = trusted.get(digest)
        if (
            current is not None
            and current[_TRUSTED_STAGE1_OUTCOME] != outcome
        ):
            raise ValueError(
                "formal Stage 1 audits disagree for one canonical candidate"
            )
        promoted[_TRUSTED_STAGE1_OUTCOME] = outcome
        trusted[digest] = promoted

    counts = {
        "trusted_stage1_winners": 0,
        "trusted_stage1_rejections": 0,
    }
    result: list[dict[str, Any]] = []
    for existing in ranked:
        digest = str(existing["triage_identity"]["canonical_digest"])
        promoted = trusted.get(digest)
        if promoted is None:
            result.append(existing)
            continue
        row = dict(promoted)
        identity = dict(existing["triage_identity"])
        identity["source_identity"] = promoted["triage_identity"][
            "source_identity"
        ]
        row["triage_identity"] = identity
        outcome = str(row.pop(_TRUSTED_STAGE1_OUTCOME))
        k = int(row["k"])
        expected = max(2 * k, 1)
        score = dict(row["proof_score"])
        if outcome == "THRESHOLD_PROVEN":
            score.update({
                "status": "THRESHOLD_PROVEN",
                "rejected": False,
                "expected_directions": expected,
                "completed_directions": expected,
                "threshold_safe_directions": expected,
                "threshold_safe_fraction": 1.0,
                "coverage": 1.0,
                "dual_coverage": 1.0,
                "min_dual_ratio": 1.0,
                "terminal_dual_ratio": 1.0,
                "rank_vector": [expected, 1.0, 1.0, 1.0, 1.0],
            })
            counts["trusted_stage1_winners"] += 1
        else:
            score.update({
                "status": "REJECTED",
                "rejected": True,
                "completed_directions": expected,
                "coverage": 1.0,
                "rank_vector": [0, -1.0, -1.0, 1.0, 0.0],
            })
            counts["trusted_stage1_rejections"] += 1
        row["proof_score"] = score
        row["trusted_stage1_audit"] = {
            "validated": True,
            "outcome": outcome,
            "audit_attempt_schema": 2,
        }
        result.append(row)
    result.sort(key=stable_sort_key)
    return result, counts


def _demote_input_identity_claims(
    record: Mapping[str, Any],
) -> dict[str, Any]:
    """Keep caller identity metadata as provenance, never as a dedup key."""

    sanitized = dict(record)
    sanitized.pop("_input_identity_advisory", None)
    advisory = {
        name: sanitized.pop(name)
        for name in (
            "canonical_digest",
            "bliss_hash",
            "novelty",
            "structural_novelty",
            "triage_identity",
        )
        if name in sanitized
    }
    if advisory:
        sanitized["_input_identity_advisory"] = advisory
    for wrapper in ("claim", "candidate"):
        nested = sanitized.get(wrapper)
        if isinstance(nested, Mapping):
            sanitized[wrapper] = _demote_input_identity_claims(nested)
    return sanitized


def _normalise_bb_terms(value: Any, label: str) -> list[tuple[int, int]]:
    """Return a strict integer exponent list for an authoritative rebuild."""

    if not isinstance(value, (list, tuple)):
        raise TypeError(f"{label}_terms must be a sequence")
    terms: list[tuple[int, int]] = []
    for index, term in enumerate(value):
        if (
            not isinstance(term, (list, tuple))
            or len(term) != 2
            or any(type(item) is not int for item in term)
        ):
            raise TypeError(
                f"{label}_terms[{index}] must contain two integer exponents"
            )
        left, right = term
        terms.append((left, right))
    return terms


def _authoritative_css_geometry(
    record: Mapping[str, Any],
    cache: dict[str, tuple[int, int]],
) -> tuple[dict[str, Any], int, int]:
    """Rebuild one CSS BB construction and overwrite untrusted reported n/k."""

    normalized = normalize_record(record)
    required = ("ell", "m", "A_terms", "B_terms")
    missing = [name for name in required if normalized.get(name) is None]
    if missing:
        raise ValueError(
            "candidate lacks BB construction fields: " + ", ".join(missing)
        )
    if type(normalized["ell"]) is not int or type(normalized["m"]) is not int:
        raise TypeError("ell and m must be integers")
    ell = normalized["ell"]
    m = normalized["m"]
    if ell <= 0 or m <= 0:
        raise ValueError("ell and m must be positive")
    a_terms = _normalise_bb_terms(normalized["A_terms"], "A")
    b_terms = _normalise_bb_terms(normalized["B_terms"], "B")
    validate_terms(ell, m, a_terms, "A")
    validate_terms(ell, m, b_terms, "B")
    construction_sha256 = _json_sha256({
        "ell": ell,
        "m": m,
        "A_terms": a_terms,
        "B_terms": b_terms,
    })
    parameters = cache.get(construction_sha256)
    if parameters is None:
        code = build_bb_code(ell, m, a_terms, b_terms)
        rebuilt_n, rebuilt_k = get_code_params_fast(code)
        if type(rebuilt_n) is not int or type(rebuilt_k) is not int:
            raise ValueError(
                "rebuilt BB code returned non-integer n/k parameters"
            )
        parameters = (rebuilt_n, rebuilt_k)
        cache[construction_sha256] = parameters
    rebuilt_n, rebuilt_k = parameters

    updated = dict(normalized)
    reported_n = updated.get("n")
    reported_k = updated.get("k")
    updated.update({
        "ell": ell,
        "m": m,
        "A_terms": [list(term) for term in a_terms],
        "B_terms": [list(term) for term in b_terms],
        "n": rebuilt_n,
        "k": rebuilt_k,
        _AUTHORITATIVE_GEOMETRY: {
            "reconstructed": True,
            "construction_sha256": construction_sha256,
            "n": rebuilt_n,
            "k": rebuilt_k,
            "reported_n": reported_n,
            "reported_k": reported_k,
            "reported_n_matches": (
                type(reported_n) is int and reported_n == rebuilt_n
            ),
            "reported_k_matches": (
                type(reported_k) is int and reported_k == rebuilt_k
            ),
        },
    })
    return updated, rebuilt_n, rebuilt_k


def _demote_untrusted_proof_evidence(
    row: Mapping[str, Any],
    *,
    reported_required_distance: Any,
    required_distance: int,
) -> dict[str, Any]:
    """Move every unsealed proof/status assertion out of the ranking domain."""

    updated = dict(row)
    proof_fields = (
        "directions",
        "direction",
        "sectors",
        "expected_directions",
        "completed_directions",
        "status",
        "proof_score",
        "d_is_exact",
        "milp_attempted",
        "milp_details",
        "distance_trusted",
        "distance_source",
        "audit_attempt",
    )
    advisory = {
        name: updated.pop(name)
        for name in proof_fields
        if name in updated
    }
    if reported_required_distance is not None:
        advisory["required_distance"] = reported_required_distance
    updated["required_distance"] = required_distance
    if not advisory:
        return updated
    updated["input_proof_advisory"] = {
        "trusted": False,
        "reason": (
            "input proof/status fields were not replayed from a sealed "
            "Stage 1 audit"
        ),
        "evidence": advisory,
    }
    return updated


def _demote_input_terminal_markers(
    row: Mapping[str, Any],
) -> dict[str, Any]:
    """Strip terminal campaign state that only this process may generate."""

    updated = dict(row)
    advisory = {
        name: updated.pop(name)
        for name in _INPUT_TERMINAL_MARKERS
        if name in updated
    }
    if advisory:
        updated["input_terminal_marker_advisory"] = {
            "trusted": False,
            "reason": (
                "terminal campaign markers are accepted only after local "
                "formal replay"
            ),
            "evidence": advisory,
        }
    return updated


def _is_trusted_terminal_rejection(row: Mapping[str, Any]) -> bool:
    trusted = row.get("trusted_stage1_audit")
    return bool(
        isinstance(trusted, Mapping)
        and trusted.get("validated") is True
        and trusted.get("outcome") == "REJECTED"
    )


def _ranked_selection_key(row: Mapping[str, Any]) -> tuple[Any, ...]:
    """Preserve proof priority, then rank proof ties by search upside."""

    proof_key = stable_sort_key(row)
    try:
        n = row.get("n")
        k = row.get("k")
        d = row.get("d")
        if any(
            isinstance(value, bool) or not isinstance(value, int)
            for value in (n, k, d)
        ):
            raise TypeError
        if n <= 0 or k <= 0 or d <= 0:
            raise ValueError
        estimated_fom = k * d * d / n
        if not math.isfinite(estimated_fom):
            raise ValueError
    except (TypeError, ValueError, OverflowError, ZeroDivisionError):
        estimated_fom = 0.0
    # stable_sort_key's final two fields are deterministic identities. Insert
    # this advisory upper-bound tie-break immediately before them; it never
    # outranks actual lower-bound proof progress.
    return (*proof_key[:-2], -estimated_fom, *proof_key[-2:])


def rank_candidate_files(
    paths: Iterable[Path],
) -> tuple[list[dict[str, Any]], dict[str, int]]:
    """Load, proof-rank, and canonical-deduplicate all candidate files."""

    records, sources = read_candidate_jsonl(paths)
    prepared: list[dict[str, Any]] = []
    prepared_sources: list[str] = []
    ineligible_records = 0
    malformed_records = 0
    invalid_audit_records = 0
    geometry_cache: dict[str, tuple[int, int]] = {}
    for record, source in zip(records, sources, strict=True):
        enriched = _demote_input_identity_claims(record)
        try:
            normalized = normalize_record(enriched)
            if normalized.get("C_terms") or normalized.get("D_terms"):
                # The current proof path does not support non-CSS candidates.
                # Retain a rankable row so selection records an explicit global
                # incompleteness instead of silently dropping it.
                n = normalized.get("n")
                k = normalized.get("k")
                if (
                    isinstance(n, bool)
                    or not isinstance(n, int)
                    or isinstance(k, bool)
                    or not isinstance(k, int)
                    or n <= 0
                    or k <= 0
                ):
                    raise TypeError(
                        "unsupported non-CSS candidate requires positive integer n/k"
                    )
                authoritative = dict(normalized)
                authoritative[_AUTHORITATIVE_GEOMETRY] = {
                    "reconstructed": False,
                    "unsupported": "NONCSS",
                    "reported_n": n,
                    "reported_k": k,
                }
            else:
                authoritative, n, k = _authoritative_css_geometry(
                    enriched, geometry_cache
                )
            if n <= 0 or k <= 0:
                ineligible_records += 1
                continue
            required_distance = minimum_winning_distance(n, k)
        except (KeyError, TypeError, ValueError, OverflowError):
            malformed_records += 1
            continue

        # Stage 1 search rows intentionally contain distance and parameter
        # estimates. Derive n, k, and the proof threshold from the rebuilt
        # construction; caller-supplied geometry is provenance only.
        # Registry/canonical metadata came from an external JSONL row and is
        # not authenticated.  In particular it must not merge two distinct
        # constructions before Stage 2 has rebuilt both of them.
        authoritative = _demote_input_terminal_markers(authoritative)
        reported_required_distance = authoritative.get("required_distance")
        authoritative["required_distance"] = required_distance
        try:
            trusted_outcome, sealed_evidence = _trusted_stage1_outcome(
                authoritative,
                required_distance,
            )
        except AuditStateError as exc:
            # A broken seal is malformed evidence, not a reason to discard the
            # independently reconstructable candidate.
            invalid_audit_records += 1
            authoritative["input_audit_advisory"] = {
                "trusted": False,
                "error": str(exc),
            }
            trusted_outcome = None
            sealed_evidence = False
        if not sealed_evidence:
            authoritative = _demote_untrusted_proof_evidence(
                authoritative,
                reported_required_distance=reported_required_distance,
                required_distance=required_distance,
            )
        if trusted_outcome is not None:
            authoritative[_TRUSTED_STAGE1_OUTCOME] = trusted_outcome
        prepared.append(authoritative)
        prepared_sources.append(source)

    ranked = deduplicate_ranked(prepared, prepared_sources)
    ranked, trusted_counts = _promote_trusted_stage1_rows(
        ranked,
        prepared,
        prepared_sources,
    )

    ranked.sort(key=_ranked_selection_key)
    eligible = [
        row for row in ranked
        if not _is_trusted_terminal_rejection(row)
    ]
    counts = {
        "input_records": len(records),
        "unique_candidates": len(ranked),
        "duplicate_records": len(prepared) - len(ranked),
        "rejected_candidates": len(ranked) - len(eligible),
        "eligible_candidates": len(eligible),
    }
    if ineligible_records:
        counts["ineligible_records"] = ineligible_records
    if malformed_records:
        counts["malformed_records"] = malformed_records
    if invalid_audit_records:
        counts["malformed_records"] = (
            counts.get("malformed_records", 0) + invalid_audit_records
        )
        counts["invalid_stage1_audit_records"] = invalid_audit_records
    counts.update({
        key: value for key, value in trusted_counts.items() if value
    })
    return ranked, counts


def validate_worker_budget(
    candidate_workers: int,
    solver_workers: int,
    max_total_workers: int,
) -> None:
    """Reject configurations that can oversubscribe the solver budget."""

    if candidate_workers < 1:
        raise ValueError("candidate_workers must be positive")
    if not 1 <= solver_workers <= 8:
        raise ValueError("solver_workers must be between 1 and 8")
    if max_total_workers < 1:
        raise ValueError("max_total_workers must be positive")
    requested = candidate_workers * solver_workers
    if requested > max_total_workers:
        raise ValueError(
            "candidate_workers * solver_workers exceeds max_total_workers "
            f"({candidate_workers} * {solver_workers} = {requested} > "
            f"{max_total_workers})",
        )


def safe_digest(canonical_digest: str) -> str:
    """Map an opaque canonical digest to a path-safe, fixed-width token."""

    return hashlib.sha256(str(canonical_digest).encode()).hexdigest()


def _file_sha256(path: Path | str) -> str | None:
    """Hash a cache dependency, preserving a stable missing-file marker."""

    digest = hashlib.sha256()
    try:
        with Path(path).open("rb") as stream:
            while chunk := stream.read(1024 * 1024):
                digest.update(chunk)
    except OSError:
        return None
    return digest.hexdigest()


def _json_sha256(value: Mapping[str, Any]) -> str:
    encoded = json.dumps(
        dict(value),
        sort_keys=True,
        separators=(",", ":"),
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def _ranked_chunk_index_sha256(
    chunks: Iterable[Mapping[str, Any]],
) -> str:
    """Hash the ordered random-access chunk index canonically."""

    encoded = json.dumps(
        [dict(chunk) for chunk in chunks],
        sort_keys=True,
        separators=(",", ":"),
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def _is_sha256(value: Any) -> bool:
    return bool(
        isinstance(value, str)
        and len(value) == 64
        and all(character in "0123456789abcdef" for character in value)
    )


solver_runtime_fingerprint = proof_runtime_fingerprint


def certificate_source_fingerprint() -> str:
    """Bind certificate caches to all code and registry inputs they execute."""

    paths = {
        Path(__file__).resolve(),
        PROJECT / "scripts" / "audit_direction_pool.py",
        PROJECT / "scripts" / "finalize_challenge.py",
        PROJECT / "tests" / "verify_known_answer_gate.py",
        PROJECT / "results" / "known_code_registry.json",
        PROJECT / "humanize" / "audit_state.py",
        PROJECT / "humanize" / "state.py",
        *(PROJECT / "evaluation").rglob("*.py"),
    }
    digest = hashlib.sha256()
    for path in sorted(paths, key=lambda item: item.relative_to(PROJECT).as_posix()):
        relative = path.relative_to(PROJECT).as_posix().encode("utf-8")
        payload = path.read_bytes()
        digest.update(len(relative).to_bytes(8, "big"))
        digest.update(relative)
        digest.update(len(payload).to_bytes(8, "big"))
        digest.update(payload)
    return digest.hexdigest()


def state_paths(
    state_dir: Path,
    canonical_digest: str,
) -> dict[str, Path]:
    token = safe_digest(canonical_digest)
    return {
        "audit": state_dir / "xor" / f"{token}.json",
        "certificate": state_dir / "certificates" / f"{token}.json",
        "certificate_metadata": (
            state_dir / "certificates" / f"{token}.cache.json"
        ),
        "verification": state_dir / "certificates" / f"{token}.verify.json",
        "certificate_checkpoint": (
            state_dir / "checkpoints" / f"{token}.build.json"
        ),
        "verification_checkpoint": (
            state_dir / "checkpoints" / f"{token}.verify.json"
        ),
    }


def _construction_candidate(
    ranked: Mapping[str, Any],
    canonical_digest: str,
) -> dict[str, Any]:
    """Remove triage-only evidence while retaining construction provenance."""

    required = ("ell", "m", "A_terms", "B_terms", "required_distance")
    missing = [name for name in required if ranked.get(name) is None]
    if missing:
        raise ValueError(
            "XOR audit requires BB construction fields: "
            + ", ".join(missing),
        )
    retained = (
        "source",
        "trial",
        "ansatz",
        "ell",
        "m",
        "A_terms",
        "B_terms",
        "C_terms",
        "D_terms",
        "n",
        "k",
        "required_distance",
        "max_row_weight",
        "max_qubit_degree",
        "tanner_components",
        "novelty",
        "canonical_digest",
    )
    candidate = {
        name: ranked[name]
        for name in retained
        if name in ranked and ranked[name] is not None
    }
    candidate.setdefault("canonical_digest", canonical_digest)
    return candidate


def _load_json_object(path: Path) -> dict[str, Any] | None:
    try:
        value = json.loads(path.read_text())
    except (OSError, TypeError, ValueError):
        return None
    return value if isinstance(value, dict) else None


def _ranked_snapshot_paths(ledger_path: Path) -> tuple[Path, Path, Path]:
    """Return fixed cache paths derived only from the trusted ledger path."""

    prefix = f"{ledger_path.name}.ranked-snapshot"
    return (
        ledger_path.with_name(f"{prefix}.jsonl"),
        ledger_path.with_name(f"{prefix}.offsets"),
        ledger_path.with_name(f"{prefix}.manifest.json"),
    )


def _stat_identity(metadata: os.stat_result) -> dict[str, int]:
    return {
        "device": int(metadata.st_dev),
        "inode": int(metadata.st_ino),
        "bytes": int(metadata.st_size),
        "mtime_ns": int(metadata.st_mtime_ns),
    }


def _regular_file_identity(path: Path, *, label: str) -> dict[str, Any]:
    """Hash one stable regular file without accepting a final symlink."""

    try:
        before = path.lstat()
    except OSError as exc:
        raise ValueError(f"{label} is unavailable: {path}") from exc
    if stat.S_ISLNK(before.st_mode) or not stat.S_ISREG(before.st_mode):
        raise ValueError(f"{label} must be a regular non-symlink file: {path}")
    digest = _file_sha256(path)
    try:
        after = path.lstat()
    except OSError as exc:
        raise ValueError(f"{label} changed while hashing: {path}") from exc
    if digest is None or _stat_identity(before) != _stat_identity(after):
        raise ValueError(f"{label} changed while hashing: {path}")
    return {
        "path": str(path.resolve(strict=True)),
        "stat": _stat_identity(after),
        "sha256": digest,
    }


def _ranked_snapshot_binding(paths: Iterable[Path]) -> dict[str, Any]:
    """Bind a ranked pool to immutable inputs, ranking code, and runtime."""

    payload = {
        "schema_version": RANKED_SNAPSHOT_SCHEMA_VERSION,
        "gate": RANKED_SNAPSHOT_GATE,
        "inputs": [
            _regular_file_identity(Path(path), label="candidate input")
            for path in paths
        ],
        # This covers this script, every evaluation source, Humanize audit
        # dependencies, and the registry. Keep the explicit registry identity
        # so the cache contract remains inspectable.
        "source_fingerprint": certificate_source_fingerprint(),
        "solver_runtime": solver_runtime_fingerprint(),
        "known_code_registry": _regular_file_identity(
            Path(DEFAULT_REGISTRY),
            label="known-code registry",
        ),
    }
    return {**payload, "binding_sha256": _json_sha256(payload)}


def _current_file_matches_identity(
    expected: Mapping[str, Any],
    *,
    label: str,
) -> bool:
    path_text = expected.get("path")
    expected_stat = expected.get("stat")
    expected_sha256 = expected.get("sha256")
    if (
        not isinstance(path_text, str)
        or not isinstance(expected_stat, Mapping)
        or not _is_sha256(expected_sha256)
    ):
        return False
    path = Path(path_text)
    try:
        before = path.lstat()
    except OSError:
        return False
    if (
        not stat.S_ISREG(before.st_mode)
        or stat.S_ISLNK(before.st_mode)
        or _stat_identity(before) != dict(expected_stat)
    ):
        return False
    digest = _file_sha256(path)
    try:
        after = path.lstat()
    except OSError:
        return False
    return bool(
        digest == expected_sha256
        and stat.S_ISREG(after.st_mode)
        and not stat.S_ISLNK(after.st_mode)
        and _stat_identity(before) == _stat_identity(after)
    )


def _binding_dependencies_unchanged(
    binding: Mapping[str, Any],
    paths: Iterable[Path],
) -> bool:
    """Replay input bytes plus live source/runtime hashes before cache reuse."""

    expected_inputs = binding.get("inputs")
    input_paths = tuple(Path(path) for path in paths)
    if (
        not isinstance(expected_inputs, list)
        or len(expected_inputs) != len(input_paths)
    ):
        return False
    for path, expected in zip(input_paths, expected_inputs, strict=True):
        if (
            not isinstance(expected, Mapping)
            or expected.get("path") != str(path.resolve(strict=False))
            or not _current_file_matches_identity(
                expected,
                label="candidate input",
            )
        ):
            return False
    registry = binding.get("known_code_registry")
    if (
        not isinstance(registry, Mapping)
        or not _current_file_matches_identity(
            registry,
            label="known-code registry",
        )
    ):
        return False
    try:
        return bool(
            binding.get("source_fingerprint")
            == certificate_source_fingerprint()
            and binding.get("solver_runtime") == solver_runtime_fingerprint()
        )
    except OSError:
        return False


def _validate_ranked_snapshot_rows(
    rows: list[dict[str, Any]],
    counts: Mapping[str, Any],
) -> None:
    """Validate the full pool once, before publishing its manifest."""

    seen: set[str] = set()
    previous_key: tuple[Any, ...] | None = None
    terminal_seen = False
    eligible = 0
    for row in rows:
        identity = row.get("triage_identity")
        score = row.get("proof_score")
        digest = (
            identity.get("canonical_digest")
            if isinstance(identity, Mapping)
            else None
        )
        if (
            not isinstance(identity, Mapping)
            or not isinstance(score, Mapping)
            or not isinstance(digest, str)
            or not digest
            or digest in seen
        ):
            raise ValueError("ranked snapshot contains an invalid identity")
        key = _ranked_selection_key(row)
        if previous_key is not None and key < previous_key:
            raise ValueError("ranked snapshot is not in canonical rank order")
        terminal = _is_trusted_terminal_rejection(row)
        if terminal:
            terminal_seen = True
        elif terminal_seen:
            raise ValueError(
                "ranked snapshot has an eligible row after terminal rejections"
            )
        else:
            eligible += 1
        seen.add(digest)
        previous_key = key

    _validate_ranked_snapshot_counts(
        counts,
        rows=len(rows),
        eligible_rows=eligible,
    )


def _validate_ranked_snapshot_counts(
    counts: Mapping[str, Any],
    *,
    rows: int,
    eligible_rows: int,
) -> dict[str, int]:
    """Validate every count and the exact arithmetic used by Stage 2."""

    required = {
        "input_records",
        "unique_candidates",
        "duplicate_records",
        "rejected_candidates",
        "eligible_candidates",
    }
    if (
        not isinstance(counts, Mapping)
        or not required.issubset(counts)
        or any(not isinstance(key, str) or not key for key in counts)
        or any(
            isinstance(value, bool)
            or not isinstance(value, int)
            or value < 0
            for value in counts.values()
        )
    ):
        raise ValueError("ranked snapshot counts must be non-negative integers")
    normalized = {str(key): int(value) for key, value in counts.items()}
    input_records = normalized["input_records"]
    unique_candidates = normalized["unique_candidates"]
    duplicate_records = normalized["duplicate_records"]
    rejected_candidates = normalized["rejected_candidates"]
    eligible_candidates = normalized["eligible_candidates"]
    if (
        unique_candidates != rows
        or eligible_candidates != eligible_rows
        or rejected_candidates != rows - eligible_rows
        or unique_candidates + duplicate_records > input_records
    ):
        raise ValueError("ranked snapshot counts are arithmetically inconsistent")
    invalid_audits = normalized.get("invalid_stage1_audit_records", 0)
    malformed = normalized.get("malformed_records", 0)
    ineligible = normalized.get("ineligible_records", 0)
    if (
        invalid_audits > malformed
        or input_records
        != (
            unique_candidates
            + duplicate_records
            + ineligible
            + malformed
            - invalid_audits
        )
    ):
        raise ValueError("ranked snapshot input accounting is inconsistent")
    return normalized


@dataclass(frozen=True)
class RankedSnapshot:
    snapshot_path: Path
    offsets_path: Path
    manifest_path: Path
    binding: dict[str, Any]
    identity: dict[str, Any]
    counts: dict[str, int]
    rows: int
    eligible_rows: int
    snapshot_stat: dict[str, int]
    offsets_stat: dict[str, int]
    chunks: tuple[dict[str, Any], ...]


def _cache_path_is_safe(path: Path, *, label: str) -> bool:
    if path.is_symlink():
        raise ValueError(f"{label} may not be a symlink")
    if path.exists() and not path.is_file():
        raise ValueError(f"{label} must be a regular file")
    return path.is_file()


def _load_ranked_snapshot(
    ledger_path: Path,
    input_paths: Iterable[Path],
) -> RankedSnapshot | None:
    """Load a manifest-bound random-access snapshot without scanning its rows."""

    snapshot_path, offsets_path, manifest_path = _ranked_snapshot_paths(
        ledger_path
    )
    for path, label in (
        (snapshot_path, "ranked snapshot"),
        (offsets_path, "ranked snapshot offset index"),
        (manifest_path, "ranked snapshot manifest"),
    ):
        _cache_path_is_safe(path, label=label)
    manifest = _load_json_object(manifest_path)
    if manifest is None:
        return None
    unsigned_manifest = dict(manifest)
    manifest_sha256 = unsigned_manifest.pop("manifest_sha256", None)
    if (
        not _is_sha256(manifest_sha256)
        or manifest_sha256 != _json_sha256(unsigned_manifest)
    ):
        return None
    binding = manifest.get("binding")
    counts = manifest.get("counts")
    identity = manifest.get("identity")
    snapshot_stat = manifest.get("snapshot_stat")
    offsets_stat = manifest.get("offsets_stat")
    chunks = manifest.get("chunks")
    chunk_rows = manifest.get("chunk_rows")
    rows = manifest.get("snapshot_rows")
    eligible_rows = (
        counts.get("eligible_candidates")
        if isinstance(counts, Mapping)
        else None
    )
    if isinstance(binding, Mapping):
        unsigned_binding = dict(binding)
        embedded_binding_sha256 = unsigned_binding.pop(
            "binding_sha256",
            None,
        )
    else:
        unsigned_binding = {}
        embedded_binding_sha256 = None
    if (
        manifest.get("schema_version") != RANKED_SNAPSHOT_SCHEMA_VERSION
        or manifest.get("gate") != RANKED_SNAPSHOT_GATE
        or not isinstance(binding, Mapping)
        or manifest.get("binding_sha256") != binding.get("binding_sha256")
        or binding.get("schema_version") != RANKED_SNAPSHOT_SCHEMA_VERSION
        or binding.get("gate") != RANKED_SNAPSHOT_GATE
        or not _is_sha256(embedded_binding_sha256)
        or embedded_binding_sha256 != _json_sha256(unsigned_binding)
        or not isinstance(counts, Mapping)
        or not isinstance(identity, Mapping)
        or not isinstance(snapshot_stat, Mapping)
        or not isinstance(offsets_stat, Mapping)
        or chunk_rows != RANKED_SNAPSHOT_CHUNK_ROWS
        or not isinstance(chunks, list)
        or isinstance(rows, bool)
        or not isinstance(rows, int)
        or rows < 0
        or isinstance(eligible_rows, bool)
        or not isinstance(eligible_rows, int)
        or not 0 <= eligible_rows <= rows
        or not snapshot_path.is_file()
        or not offsets_path.is_file()
        or _stat_identity(snapshot_path.lstat()) != dict(snapshot_stat)
        or _stat_identity(offsets_path.lstat()) != dict(offsets_stat)
        or offsets_path.stat().st_size != (rows + 1) * 8
        or identity.get("binding_sha256") != binding.get("binding_sha256")
        or identity.get("rows") != rows
        or identity.get("eligible_rows") != eligible_rows
        or not _is_sha256(identity.get("counts_sha256"))
        or identity.get("counts_sha256") != _json_sha256(counts)
        or identity.get("chunk_rows") != RANKED_SNAPSHOT_CHUNK_ROWS
        or not _is_sha256(identity.get("snapshot_sha256"))
        or not _is_sha256(identity.get("offsets_sha256"))
        or not _is_sha256(identity.get("chunk_index_sha256"))
        or identity.get("chunk_index_sha256")
        != _ranked_chunk_index_sha256(
            chunk for chunk in chunks if isinstance(chunk, Mapping)
        )
        or not _binding_dependencies_unchanged(binding, input_paths)
    ):
        return None
    try:
        normalized_counts = _validate_ranked_snapshot_counts(
            counts,
            rows=rows,
            eligible_rows=eligible_rows,
        )
    except ValueError:
        return None
    expected_chunks = math.ceil(rows / RANKED_SNAPSHOT_CHUNK_ROWS)
    if len(chunks) != expected_chunks:
        return None
    normalized_chunks: list[dict[str, Any]] = []
    previous_snapshot_end = 0
    for chunk_number, chunk in enumerate(chunks):
        if not isinstance(chunk, Mapping):
            return None
        start_row = chunk.get("start_row")
        end_row = chunk.get("end_row")
        snapshot_start = chunk.get("snapshot_start")
        snapshot_end = chunk.get("snapshot_end")
        offsets_start = chunk.get("offsets_start")
        offsets_end = chunk.get("offsets_end")
        expected_start = chunk_number * RANKED_SNAPSHOT_CHUNK_ROWS
        expected_end = min(
            expected_start + RANKED_SNAPSHOT_CHUNK_ROWS,
            rows,
        )
        integer_fields = (
            start_row,
            end_row,
            snapshot_start,
            snapshot_end,
            offsets_start,
            offsets_end,
        )
        if (
            any(
                isinstance(value, bool) or not isinstance(value, int)
                for value in integer_fields
            )
            or start_row != expected_start
            or end_row != expected_end
            or snapshot_start != previous_snapshot_end
            or not snapshot_start < snapshot_end
            or snapshot_end > snapshot_stat.get("bytes", -1)
            or offsets_start != start_row * 8
            or offsets_end != (end_row + 1) * 8
            or offsets_end > offsets_stat.get("bytes", -1)
            or not _is_sha256(chunk.get("snapshot_sha256"))
            or not _is_sha256(chunk.get("offsets_sha256"))
        ):
            return None
        normalized_chunks.append(dict(chunk))
        previous_snapshot_end = snapshot_end
    if previous_snapshot_end != snapshot_stat.get("bytes"):
        return None
    loaded = RankedSnapshot(
        snapshot_path=snapshot_path,
        offsets_path=offsets_path,
        manifest_path=manifest_path,
        binding=dict(binding),
        identity=dict(identity),
        counts=normalized_counts,
        rows=rows,
        eligible_rows=eligible_rows,
        snapshot_stat=dict(snapshot_stat),
        offsets_stat=dict(offsets_stat),
        chunks=tuple(normalized_chunks),
    )
    try:
        _validate_ranked_snapshot_eligible_boundary(loaded)
    except (OSError, TypeError, ValueError):
        return None
    return loaded


def _write_ranked_snapshot(
    ledger_path: Path,
    binding: Mapping[str, Any],
    ranked: list[dict[str, Any]],
    counts: Mapping[str, int],
) -> RankedSnapshot:
    """Commit snapshot/index bytes first and their validating manifest last."""

    snapshot_path, offsets_path, manifest_path = _ranked_snapshot_paths(
        ledger_path
    )
    for path, label in (
        (snapshot_path, "ranked snapshot"),
        (offsets_path, "ranked snapshot offset index"),
        (manifest_path, "ranked snapshot manifest"),
    ):
        _cache_path_is_safe(path, label=label)
    _validate_ranked_snapshot_rows(ranked, counts)

    encoded_rows = [
        (json.dumps(row, sort_keys=True) + "\n").encode("utf-8")
        for row in ranked
    ]
    offsets = [0]
    for payload in encoded_rows:
        offsets.append(offsets[-1] + len(payload))
    snapshot_payload = b"".join(encoded_rows)
    offsets_payload = b"".join(
        struct.pack(">Q", offset) for offset in offsets
    )
    chunks: list[dict[str, Any]] = []
    for start_row in range(
        0,
        len(ranked),
        RANKED_SNAPSHOT_CHUNK_ROWS,
    ):
        end_row = min(
            start_row + RANKED_SNAPSHOT_CHUNK_ROWS,
            len(ranked),
        )
        snapshot_start = offsets[start_row]
        snapshot_end = offsets[end_row]
        offsets_start = start_row * 8
        offsets_end = (end_row + 1) * 8
        chunks.append({
            "start_row": start_row,
            "end_row": end_row,
            "snapshot_start": snapshot_start,
            "snapshot_end": snapshot_end,
            "snapshot_sha256": hashlib.sha256(
                snapshot_payload[snapshot_start:snapshot_end],
            ).hexdigest(),
            "offsets_start": offsets_start,
            "offsets_end": offsets_end,
            "offsets_sha256": hashlib.sha256(
                offsets_payload[offsets_start:offsets_end],
            ).hexdigest(),
        })
    _atomic_write_bytes(snapshot_path, snapshot_payload)
    _atomic_write_bytes(offsets_path, offsets_payload)

    # Full byte verification happens once, before the manifest makes this cache
    # reusable. Later pages bind immutable inode/stat identities and take shared
    # locks instead of rehashing the entire pool.
    snapshot_sha256 = _file_sha256(snapshot_path)
    offsets_sha256 = _file_sha256(offsets_path)
    if (
        snapshot_sha256 != hashlib.sha256(snapshot_payload).hexdigest()
        or offsets_sha256 != hashlib.sha256(offsets_payload).hexdigest()
    ):
        raise ValueError("ranked snapshot bytes changed during commit")
    snapshot_stat = _stat_identity(snapshot_path.lstat())
    offsets_stat = _stat_identity(offsets_path.lstat())
    normalized_counts = _validate_ranked_snapshot_counts(
        counts,
        rows=len(ranked),
        eligible_rows=int(counts["eligible_candidates"]),
    )
    identity = {
        "binding_sha256": binding["binding_sha256"],
        "snapshot_sha256": snapshot_sha256,
        "offsets_sha256": offsets_sha256,
        "chunk_index_sha256": _ranked_chunk_index_sha256(chunks),
        "chunk_rows": RANKED_SNAPSHOT_CHUNK_ROWS,
        "rows": len(ranked),
        "eligible_rows": normalized_counts["eligible_candidates"],
        "counts_sha256": _json_sha256(normalized_counts),
    }
    manifest_payload = {
        "schema_version": RANKED_SNAPSHOT_SCHEMA_VERSION,
        "gate": RANKED_SNAPSHOT_GATE,
        "binding": dict(binding),
        "binding_sha256": binding["binding_sha256"],
        "identity": identity,
        "snapshot_rows": len(ranked),
        "snapshot_stat": snapshot_stat,
        "offsets_stat": offsets_stat,
        "chunk_rows": RANKED_SNAPSHOT_CHUNK_ROWS,
        "chunks": chunks,
        "counts": normalized_counts,
        "created_at": time.time(),
    }
    manifest = {
        **manifest_payload,
        "manifest_sha256": _json_sha256(manifest_payload),
    }
    atomic_write_json(manifest_path, manifest)
    loaded = _load_ranked_snapshot(
        ledger_path,
        [Path(item["path"]) for item in binding["inputs"]],
    )
    if loaded is None:
        raise ValueError("ranked snapshot did not replay after commit")
    return loaded


def prepare_ranked_snapshot(
    paths: Iterable[Path],
    *,
    ledger_path: Path,
) -> tuple[RankedSnapshot, bool]:
    """Rank once per immutable binding and cache no solver-derived verdicts."""

    input_paths = tuple(Path(path) for path in paths)
    cached = _load_ranked_snapshot(ledger_path, input_paths)
    if cached is not None:
        return cached, True

    binding = _ranked_snapshot_binding(input_paths)
    ranked, counts = rank_candidate_files(input_paths)
    # Full hashes close mutation during the expensive rank/dedup build.
    if _ranked_snapshot_binding(input_paths) != binding:
        raise ValueError("candidate inputs changed while ranking")
    return (
        _write_ranked_snapshot(
            ledger_path,
            binding,
            ranked,
            counts,
        ),
        False,
    )


def _novelty_source_fingerprint() -> str:
    """Hash the code paths that reconstruct and canonicalize CSS candidates."""

    paths = {
        Path(__file__).resolve(),
        PROJECT / "evaluation" / "bb_code.py",
        PROJECT / "evaluation" / "registry.py",
        PROJECT / "evaluation" / "structural_dedup.py",
        PROJECT / "evaluation" / "tanner_equivalence.py",
    }
    digest = hashlib.sha256()
    for path in sorted(
        paths,
        key=lambda item: item.relative_to(PROJECT).as_posix(),
    ):
        relative = path.relative_to(PROJECT).as_posix().encode("utf-8")
        payload = path.read_bytes()
        digest.update(len(relative).to_bytes(8, "big"))
        digest.update(relative)
        digest.update(len(payload).to_bytes(8, "big"))
        digest.update(payload)
    return digest.hexdigest()


def _require_novelty_replay(
    value: Any,
    *,
    registry: Mapping[str, Any],
    registry_content_sha256: str,
    checker_source_fingerprint: str,
) -> dict[str, Any]:
    """Validate and bind a freshly computed registry answer fail-closed."""

    if not isinstance(value, Mapping):
        raise NoveltyReplayError("novelty checker did not return an object")
    novelty = dict(value)
    canonical_digest = novelty.get("canonical_digest")
    matched_entries = novelty.get("matched_entries")
    if (
        novelty.get("checked") is not True
        or type(novelty.get("novel")) is not bool
        or novelty.get("code_type") != "css"
        or not isinstance(canonical_digest, str)
        or len(canonical_digest) != 64
        or any(character not in "0123456789abcdef" for character in canonical_digest)
        or novelty.get("registry_version") != registry.get("registry_version")
        or novelty.get("registry_sha256") != registry.get("registry_sha256")
        or not isinstance(matched_entries, list)
        or any(not isinstance(entry, Mapping) for entry in matched_entries)
        or novelty["novel"] is bool(matched_entries)
    ):
        raise NoveltyReplayError(
            "novelty checker returned malformed or stale registry evidence",
        )
    novelty["registry_content_sha256"] = registry_content_sha256
    novelty["checker_source_fingerprint"] = checker_source_fingerprint
    novelty["replayed_from_construction"] = True
    return novelty


def canonicalize_for_audit(
    ranked: Mapping[str, Any],
    *,
    code_builder: Callable[..., Any] | None = None,
    novelty_checker: Callable[..., dict[str, Any]] | None = None,
    registry_path: str | Path = DEFAULT_REGISTRY,
) -> dict[str, Any]:
    """Rebuild a selected row and replay novelty against the current registry.

    All input novelty and canonical-digest fields are advisory, including
    apparently complete cache bindings.  They are never authentication, so
    Stage 2 reconstructs the BB code and invokes the current checker for every
    scanned candidate before deduplication or known-code filtering.
    """

    code_builder = build_bb_code if code_builder is None else code_builder
    novelty_checker = (
        check_code_novelty if novelty_checker is None else novelty_checker
    )
    updated = dict(ranked)
    identity = updated.get("triage_identity")
    if not isinstance(identity, Mapping):
        identity = candidate_identity(updated)
    identity = dict(identity)
    candidate = _construction_candidate(
        updated, str(identity["canonical_digest"]),
    )
    if candidate.get("C_terms") or candidate.get("D_terms"):
        raise ValueError("XOR audit canonicalization supports CSS BB only")
    ell = candidate["ell"]
    m = candidate["m"]
    if type(ell) is not int or type(m) is not int:
        raise TypeError("ell and m must be integers")
    if ell <= 0 or m <= 0:
        raise ValueError("ell and m must be positive")
    a_terms = _normalise_bb_terms(candidate["A_terms"], "A")
    b_terms = _normalise_bb_terms(candidate["B_terms"], "B")
    validate_terms(ell, m, a_terms, "A")
    validate_terms(ell, m, b_terms, "B")
    code = code_builder(ell, m, a_terms, b_terms)
    try:
        rebuilt_n, rebuilt_k = get_code_params_fast(code)
    except (AttributeError, TypeError, ValueError, OverflowError) as exc:
        raise ValueError(
            "rebuilt BB code returned invalid n/k parameters"
        ) from exc
    if type(rebuilt_n) is not int or type(rebuilt_k) is not int:
        raise ValueError("rebuilt BB code returned non-integer n/k parameters")
    if rebuilt_n <= 0 or rebuilt_k <= 0:
        raise ValueError("rebuilt BB code must have positive n and k")
    reported_n = updated.get("n")
    reported_k = updated.get("k")
    updated["n"] = rebuilt_n
    updated["k"] = rebuilt_k
    updated["required_distance"] = minimum_winning_distance(
        rebuilt_n, rebuilt_k
    )
    selection_geometry = {
        "reconstructed": True,
        "n": rebuilt_n,
        "k": rebuilt_k,
        "reported_n": reported_n,
        "reported_k": reported_k,
        "reported_n_matches": (
            type(reported_n) is int and reported_n == rebuilt_n
        ),
        "reported_k_matches": (
            type(reported_k) is int and reported_k == rebuilt_k
        ),
    }
    prior_geometry = updated.get(_AUTHORITATIVE_GEOMETRY)
    if (
        isinstance(prior_geometry, Mapping)
        and prior_geometry.get("reconstructed") is True
        and prior_geometry.get("n") == reported_n
        and prior_geometry.get("k") == reported_k
    ):
        # rank_candidate_files already performed an authoritative rebuild.
        # Preserve the original caller-reported n/k mismatch and append the
        # independent selection-time replay instead of erasing provenance.
        geometry = dict(prior_geometry)
        geometry["selection_rebuild"] = selection_geometry
        updated[_AUTHORITATIVE_GEOMETRY] = geometry
    else:
        updated[_AUTHORITATIVE_GEOMETRY] = selection_geometry

    registry_path = Path(registry_path).resolve()
    initial_registry_sha256 = _file_sha256(registry_path)
    if initial_registry_sha256 is None:
        raise NoveltyReplayError("known-code registry is unavailable")
    initial_source_fingerprint = _novelty_source_fingerprint()
    try:
        # load_registry is cached by path. Clear it before the replay so an
        # in-process registry update can never retain a stale novelty verdict.
        load_registry.cache_clear()
        registry = load_registry(registry_path)
        replayed = novelty_checker(
            code,
            code_type="css",
            registry_path=registry_path,
        )
    except (OSError, TypeError, ValueError) as exc:
        raise NoveltyReplayError(
            "authoritative novelty replay failed",
        ) from exc
    if (
        _file_sha256(registry_path) != initial_registry_sha256
        or _novelty_source_fingerprint() != initial_source_fingerprint
    ):
        raise NoveltyReplayError(
            "novelty dependencies changed during authoritative replay",
        )
    existing_novelty = _require_novelty_replay(
        replayed,
        registry=registry,
        registry_content_sha256=initial_registry_sha256,
        checker_source_fingerprint=initial_source_fingerprint,
    )
    actual_digest = str(existing_novelty["canonical_digest"])

    digest_kind = str(identity.get("digest_kind", ""))
    claimed_digest = str(identity.get("canonical_digest", ""))
    if (
        digest_kind in {"canonical", "registry-canonical"}
        and claimed_digest
        and claimed_digest != actual_digest
    ):
        raise ValueError(
            "stored canonical digest does not match reconstructed BB code",
        )
    identity["precanonical_digest"] = claimed_digest
    identity["canonical_digest"] = actual_digest
    identity["digest_kind"] = "registry-canonical"
    updated["triage_identity"] = identity
    updated["canonical_digest"] = actual_digest
    updated["novelty"] = dict(existing_novelty)
    return updated


def _select_audit_page(
    ranked: list[dict[str, Any]],
    top: int,
    *,
    start_index: int,
    seen_digests: Iterable[str],
    canonicalizer: Callable[[Mapping[str, Any]], dict[str, Any]] | None = None,
) -> tuple[list[dict[str, Any]], dict[str, int], int]:
    """Fill one durable audit page from a stable raw-rank cursor."""

    if top < 0:
        raise ValueError("top must be non-negative")
    if start_index < 0 or start_index > len(ranked):
        raise ValueError("selection start_index is outside the ranked pool")
    canonicalizer = (
        canonicalize_for_audit if canonicalizer is None else canonicalizer
    )
    selected: list[dict[str, Any]] = []
    seen_digests = {str(value) for value in seen_digests}
    stats = {
        "canonicalized_candidates": 0,
        "canonical_duplicates_skipped": 0,
        "known_codes_skipped": 0,
        "unsupported_candidates_skipped": 0,
        "canonicalization_errors": 0,
        "unscanned_eligible_candidates": 0,
        "selection_exhausted": True,
    }
    if top == 0:
        unscanned = sum(
            not _is_trusted_terminal_rejection(row)
            for row in ranked[start_index:]
        )
        stats["unscanned_eligible_candidates"] = unscanned
        stats["selection_exhausted"] = unscanned == 0
        return selected, stats, start_index

    next_index = len(ranked)
    for index in range(start_index, len(ranked)):
        row = ranked[index]
        if _is_trusted_terminal_rejection(row):
            continue
        if row.get("C_terms") or row.get("D_terms"):
            row["campaign_skip_reason"] = "UNSUPPORTED_NONCSS"
            stats["unsupported_candidates_skipped"] += 1
            continue
        try:
            updated = canonicalizer(row)
        except (KeyError, TypeError, ValueError) as exc:
            row["campaign_skip_reason"] = "CANONICALIZATION_ERROR"
            row["campaign_skip_error"] = str(exc)
            stats["canonicalization_errors"] += 1
            continue
        ranked[index] = updated
        stats["canonicalized_candidates"] += 1
        novelty = updated.get("novelty")
        if (
            isinstance(novelty, Mapping)
            and novelty.get("novel") is not True
        ):
            updated["campaign_skip_reason"] = "KNOWN_CODE"
            stats["known_codes_skipped"] += 1
            continue
        digest = str(updated["triage_identity"]["canonical_digest"])
        if digest in seen_digests:
            updated["campaign_skip_reason"] = "CANONICAL_DUPLICATE"
            stats["canonical_duplicates_skipped"] += 1
            continue
        seen_digests.add(digest)
        selected.append(updated)
        if len(selected) == top:
            unscanned = sum(
                not _is_trusted_terminal_rejection(remaining)
                for remaining in ranked[index + 1 :]
            )
            stats["unscanned_eligible_candidates"] = unscanned
            stats["selection_exhausted"] = unscanned == 0
            next_index = len(ranked) if unscanned == 0 else index + 1
            break
    return selected, stats, next_index


def _snapshot_descriptor_matches(
    descriptor: int,
    expected: Mapping[str, int],
) -> bool:
    return _stat_identity(os.fstat(descriptor)) == dict(expected)


def _read_ranked_snapshot_row(
    snapshot: RankedSnapshot,
    index: int,
) -> dict[str, Any]:
    """Cryptographically read one row without scanning the ranked pool."""

    if index < 0 or index >= snapshot.rows:
        raise ValueError("ranked snapshot row index is outside the pool")
    chunk = snapshot.chunks[index // RANKED_SNAPSHOT_CHUNK_ROWS]
    snapshot_start = int(chunk["snapshot_start"])
    snapshot_end = int(chunk["snapshot_end"])
    offsets_start = int(chunk["offsets_start"])
    offsets_end = int(chunk["offsets_end"])
    with (
        snapshot.snapshot_path.open("rb") as ranked_stream,
        snapshot.offsets_path.open("rb") as offsets_stream,
    ):
        fcntl.flock(ranked_stream.fileno(), fcntl.LOCK_SH)
        fcntl.flock(offsets_stream.fileno(), fcntl.LOCK_SH)
        try:
            if (
                not _snapshot_descriptor_matches(
                    ranked_stream.fileno(), snapshot.snapshot_stat
                )
                or not _snapshot_descriptor_matches(
                    offsets_stream.fileno(), snapshot.offsets_stat
                )
            ):
                raise ValueError(
                    "ranked snapshot was replaced before boundary read",
                )
            ranked_stream.seek(snapshot_start)
            snapshot_payload = ranked_stream.read(
                snapshot_end - snapshot_start,
            )
            offsets_stream.seek(offsets_start)
            offsets_payload = offsets_stream.read(
                offsets_end - offsets_start,
            )
            if (
                len(snapshot_payload) != snapshot_end - snapshot_start
                or hashlib.sha256(snapshot_payload).hexdigest()
                != chunk["snapshot_sha256"]
            ):
                raise ValueError("ranked snapshot data chunk hash mismatch")
            if (
                len(offsets_payload) != offsets_end - offsets_start
                or hashlib.sha256(offsets_payload).hexdigest()
                != chunk["offsets_sha256"]
            ):
                raise ValueError("ranked snapshot offset chunk hash mismatch")
            offset_count = int(chunk["end_row"]) - int(
                chunk["start_row"],
            ) + 1
            offsets = struct.unpack(f">{offset_count}Q", offsets_payload)
            if (
                offsets[0] != snapshot_start
                or offsets[-1] != snapshot_end
                or any(
                    left >= right
                    for left, right in zip(offsets, offsets[1:])
                )
            ):
                raise ValueError(
                    "ranked snapshot offset chunk is inconsistent",
                )
            row_in_chunk = index - int(chunk["start_row"])
            left = offsets[row_in_chunk] - snapshot_start
            right = offsets[row_in_chunk + 1] - snapshot_start
            payload = snapshot_payload[left:right]
            if not payload.endswith(b"\n"):
                raise ValueError("ranked snapshot row is partial")
            try:
                row = json.loads(payload)
            except (UnicodeDecodeError, json.JSONDecodeError) as exc:
                raise ValueError("ranked snapshot row is invalid") from exc
            if not isinstance(row, dict):
                raise ValueError("ranked snapshot row is not an object")
            if (
                not _snapshot_descriptor_matches(
                    ranked_stream.fileno(), snapshot.snapshot_stat
                )
                or not _snapshot_descriptor_matches(
                    offsets_stream.fileno(), snapshot.offsets_stat
                )
            ):
                raise ValueError("ranked snapshot changed during boundary read")
            return row
        finally:
            fcntl.flock(offsets_stream.fileno(), fcntl.LOCK_UN)
            fcntl.flock(ranked_stream.fileno(), fcntl.LOCK_UN)


def _validate_ranked_snapshot_eligible_boundary(
    snapshot: RankedSnapshot,
) -> None:
    """Prove the manifest's eligible prefix boundary by random access."""

    if snapshot.eligible_rows:
        last_eligible = _read_ranked_snapshot_row(
            snapshot,
            snapshot.eligible_rows - 1,
        )
        if _is_trusted_terminal_rejection(last_eligible):
            raise ValueError(
                "ranked snapshot eligible boundary ends in a rejection",
            )
    if snapshot.eligible_rows < snapshot.rows:
        first_rejected = _read_ranked_snapshot_row(
            snapshot,
            snapshot.eligible_rows,
        )
        if not _is_trusted_terminal_rejection(first_rejected):
            raise ValueError(
                "ranked snapshot eligible boundary skips an eligible row",
            )


def _select_snapshot_audit_page(
    snapshot: RankedSnapshot,
    top: int,
    *,
    start_index: int,
    seen_digests: Iterable[str],
    canonicalizer: Callable[[Mapping[str, Any]], dict[str, Any]] | None = None,
) -> tuple[list[dict[str, Any]], dict[str, int], int]:
    """Fill one page by random-accessing only its ranked snapshot rows."""

    if top < 0:
        raise ValueError("top must be non-negative")
    if start_index < 0 or start_index > snapshot.eligible_rows:
        raise ValueError("selection start_index is outside the ranked pool")
    canonicalizer = (
        canonicalize_for_audit if canonicalizer is None else canonicalizer
    )
    selected: list[dict[str, Any]] = []
    seen_digests = {str(value) for value in seen_digests}
    stats = {
        "canonicalized_candidates": 0,
        "canonical_duplicates_skipped": 0,
        "known_codes_skipped": 0,
        "unsupported_candidates_skipped": 0,
        "canonicalization_errors": 0,
        "unscanned_eligible_candidates": 0,
        "selection_exhausted": True,
    }
    if top == 0:
        remaining = snapshot.eligible_rows - start_index
        stats["unscanned_eligible_candidates"] = remaining
        stats["selection_exhausted"] = remaining == 0
        return selected, stats, start_index

    next_index = snapshot.eligible_rows
    with (
        snapshot.snapshot_path.open("rb") as ranked_stream,
        snapshot.offsets_path.open("rb") as offsets_stream,
    ):
        fcntl.flock(ranked_stream.fileno(), fcntl.LOCK_SH)
        fcntl.flock(offsets_stream.fileno(), fcntl.LOCK_SH)
        try:
            if (
                not _snapshot_descriptor_matches(
                    ranked_stream.fileno(), snapshot.snapshot_stat
                )
                or not _snapshot_descriptor_matches(
                    offsets_stream.fileno(), snapshot.offsets_stat
                )
            ):
                raise ValueError("ranked snapshot was replaced before page read")

            loaded_chunk_number: int | None = None
            loaded_snapshot_payload = b""
            loaded_offsets: tuple[int, ...] = ()
            for index in range(start_index, snapshot.eligible_rows):
                chunk_number = index // RANKED_SNAPSHOT_CHUNK_ROWS
                chunk = snapshot.chunks[chunk_number]
                if loaded_chunk_number != chunk_number:
                    snapshot_start = int(chunk["snapshot_start"])
                    snapshot_end = int(chunk["snapshot_end"])
                    offsets_start = int(chunk["offsets_start"])
                    offsets_end = int(chunk["offsets_end"])
                    ranked_stream.seek(snapshot_start)
                    loaded_snapshot_payload = ranked_stream.read(
                        snapshot_end - snapshot_start,
                    )
                    offsets_stream.seek(offsets_start)
                    encoded_offsets = offsets_stream.read(
                        offsets_end - offsets_start,
                    )
                    if (
                        len(loaded_snapshot_payload)
                        != snapshot_end - snapshot_start
                        or hashlib.sha256(
                            loaded_snapshot_payload,
                        ).hexdigest()
                        != chunk["snapshot_sha256"]
                    ):
                        raise ValueError(
                            "ranked snapshot data chunk hash mismatch",
                        )
                    if (
                        len(encoded_offsets) != offsets_end - offsets_start
                        or hashlib.sha256(encoded_offsets).hexdigest()
                        != chunk["offsets_sha256"]
                    ):
                        raise ValueError(
                            "ranked snapshot offset chunk hash mismatch",
                        )
                    offset_count = int(chunk["end_row"]) - int(
                        chunk["start_row"],
                    ) + 1
                    loaded_offsets = struct.unpack(
                        f">{offset_count}Q",
                        encoded_offsets,
                    )
                    if (
                        loaded_offsets[0] != snapshot_start
                        or loaded_offsets[-1] != snapshot_end
                        or any(
                            left >= right
                            for left, right in zip(
                                loaded_offsets,
                                loaded_offsets[1:],
                            )
                        )
                    ):
                        raise ValueError(
                            "ranked snapshot offset chunk is inconsistent",
                        )
                    loaded_chunk_number = chunk_number

                row_in_chunk = index - int(chunk["start_row"])
                left = loaded_offsets[row_in_chunk] - int(
                    chunk["snapshot_start"],
                )
                right = loaded_offsets[row_in_chunk + 1] - int(
                    chunk["snapshot_start"],
                )
                payload = loaded_snapshot_payload[left:right]
                if not payload.endswith(b"\n"):
                    raise ValueError("ranked snapshot row is partial")
                try:
                    row = json.loads(payload)
                except (UnicodeDecodeError, json.JSONDecodeError) as exc:
                    raise ValueError("ranked snapshot row is invalid") from exc
                if (
                    not isinstance(row, dict)
                    or _is_trusted_terminal_rejection(row)
                ):
                    raise ValueError(
                        "ranked snapshot eligible prefix is inconsistent"
                    )
                if row.get("C_terms") or row.get("D_terms"):
                    stats["unsupported_candidates_skipped"] += 1
                    continue
                try:
                    updated = canonicalizer(row)
                except (KeyError, TypeError, ValueError):
                    stats["canonicalization_errors"] += 1
                    continue
                stats["canonicalized_candidates"] += 1
                novelty = updated.get("novelty")
                if (
                    isinstance(novelty, Mapping)
                    and novelty.get("novel") is not True
                ):
                    stats["known_codes_skipped"] += 1
                    continue
                digest = str(updated["triage_identity"]["canonical_digest"])
                if digest in seen_digests:
                    stats["canonical_duplicates_skipped"] += 1
                    continue
                seen_digests.add(digest)
                selected.append(updated)
                if len(selected) == top:
                    next_index = index + 1
                    remaining = snapshot.eligible_rows - next_index
                    stats["unscanned_eligible_candidates"] = remaining
                    stats["selection_exhausted"] = remaining == 0
                    break
            if (
                not _snapshot_descriptor_matches(
                    ranked_stream.fileno(), snapshot.snapshot_stat
                )
                or not _snapshot_descriptor_matches(
                    offsets_stream.fileno(), snapshot.offsets_stat
                )
            ):
                raise ValueError("ranked snapshot changed during page read")
        finally:
            fcntl.flock(offsets_stream.fileno(), fcntl.LOCK_UN)
            fcntl.flock(ranked_stream.fileno(), fcntl.LOCK_UN)
    return selected, stats, next_index


def select_audit_candidates(
    ranked: list[dict[str, Any]],
    top: int,
    *,
    canonicalizer: Callable[[Mapping[str, Any]], dict[str, Any]] | None = None,
) -> tuple[list[dict[str, Any]], dict[str, int]]:
    """Fill the first audit page with unique, registry-novel CSS candidates."""

    selected, stats, _ = _select_audit_page(
        ranked,
        top,
        start_index=0,
        seen_digests=(),
        canonicalizer=canonicalizer,
    )
    return selected, stats


def _selection_binding(
    ranked: Iterable[Mapping[str, Any]],
    *,
    top: int,
    known_answer_artifact: Path,
    ranked_snapshot_identity: Mapping[str, Any] | None = None,
    ranked_size: int | None = None,
) -> str:
    """Bind a cursor to every input that can alter candidate selection."""

    if ranked_snapshot_identity is None:
        ranked_binding: Any = list(ranked)
    else:
        identity = dict(ranked_snapshot_identity)
        if ranked_size is None:
            try:
                ranked_size = len(ranked)  # type: ignore[arg-type]
            except TypeError as exc:
                raise ValueError(
                    "snapshot-bound ranked pool must have a stable length"
                ) from exc
        if (
            not _is_sha256(identity.get("binding_sha256"))
            or not _is_sha256(identity.get("snapshot_sha256"))
            or not _is_sha256(identity.get("offsets_sha256"))
            or not _is_sha256(identity.get("chunk_index_sha256"))
            or not _is_sha256(identity.get("counts_sha256"))
            or identity.get("chunk_rows") != RANKED_SNAPSHOT_CHUNK_ROWS
            or identity.get("rows") != ranked_size
            or isinstance(identity.get("eligible_rows"), bool)
            or not isinstance(identity.get("eligible_rows"), int)
            or not 0 <= identity["eligible_rows"] <= ranked_size
        ):
            raise ValueError("ranked snapshot identity is malformed")
        ranked_binding = {"snapshot": identity}
    return _json_sha256({
        "schema_version": SELECTION_LEDGER_SCHEMA_VERSION,
        "top": top,
        "ranked": ranked_binding,
        "known_answer_sha256": _file_sha256(known_answer_artifact),
        "solver_runtime": solver_runtime_fingerprint(),
        "source_fingerprint": certificate_source_fingerprint(),
    })


def _new_selection_ledger(
    binding_sha256: str,
    *,
    snapshot_identity_sha256_value: str,
    snapshot_rows: int,
    eligible_rows: int,
) -> dict[str, Any]:
    return new_selection_ledger(
        binding_sha256=binding_sha256,
        snapshot_identity_sha256_value=snapshot_identity_sha256_value,
        snapshot_rows=snapshot_rows,
        eligible_rows=eligible_rows,
    )


def _load_selection_ledger(
    path: Path,
    *,
    binding_sha256: str,
    snapshot_identity_sha256_value: str,
    snapshot_rows: int,
    eligible_rows: int,
) -> dict[str, Any]:
    """Load a cursor fail-closed; stale bindings safely restart at rank zero."""

    if path.is_symlink():
        raise ValueError("selection ledger may not be a symlink")
    value = _load_json_object(path)
    if value is None:
        return _new_selection_ledger(
            binding_sha256,
            snapshot_identity_sha256_value=snapshot_identity_sha256_value,
            snapshot_rows=snapshot_rows,
            eligible_rows=eligible_rows,
        )
    # Old schema and stale snapshot bindings are never trusted. Restarting at
    # rank zero is safe and lets pre-v2 runs resume without inheriting a cursor.
    if (
        value.get("schema_version") != SELECTION_LEDGER_SCHEMA_VERSION
        or value.get("gate") != SELECTION_LEDGER_GATE
        or value.get("binding_sha256") != binding_sha256
        or value.get("snapshot_identity_sha256")
        != snapshot_identity_sha256_value
        or value.get("snapshot_rows") != snapshot_rows
        or value.get("eligible_rows") != eligible_rows
    ):
        return _new_selection_ledger(
            binding_sha256,
            snapshot_identity_sha256_value=snapshot_identity_sha256_value,
            snapshot_rows=snapshot_rows,
            eligible_rows=eligible_rows,
        )
    return validate_selection_ledger(
        value,
        binding_sha256=binding_sha256,
        snapshot_identity_sha256_value=snapshot_identity_sha256_value,
        snapshot_rows=snapshot_rows,
        eligible_rows=eligible_rows,
    )


def _prepare_selection_page(
    ranked: list[dict[str, Any]],
    *,
    top: int,
    ledger_path: Path,
    known_answer_artifact: Path,
    canonicalizer: Callable[[Mapping[str, Any]], dict[str, Any]] | None = None,
    ranked_snapshot_identity: Mapping[str, Any] | None = None,
) -> tuple[
    list[dict[str, Any]],
    dict[str, int],
    dict[str, Any],
    dict[str, Any],
]:
    """Create or replay one pending page before any expensive solver work."""

    binding_sha256 = _selection_binding(
        ranked,
        top=top,
        known_answer_artifact=known_answer_artifact,
        ranked_snapshot_identity=ranked_snapshot_identity,
    )
    ranked_identity_sha256 = snapshot_identity_sha256(
        dict(ranked_snapshot_identity)
        if ranked_snapshot_identity is not None
        else {
            "selection_binding_sha256": binding_sha256,
            "rows": len(ranked),
        }
    )
    ledger = _load_selection_ledger(
        ledger_path,
        binding_sha256=binding_sha256,
        snapshot_identity_sha256_value=ranked_identity_sha256,
        snapshot_rows=len(ranked),
        eligible_rows=len(ranked),
    )
    pending = ledger.get("pending")
    start_index = int(
        pending["start_index"] if isinstance(pending, Mapping)
        else ledger["cursor"]
    )
    selected, stats, next_index = _select_audit_page(
        ranked,
        top,
        start_index=start_index,
        seen_digests=ledger["committed_digests"],
        canonicalizer=canonicalizer,
    )
    selected_digests = [
        str(row["triage_identity"]["canonical_digest"])
        for row in selected
    ]
    scan_evidence = make_scan_evidence(
        snapshot_identity_sha256_value=ranked_identity_sha256,
        start_index=start_index,
        next_index=next_index,
        snapshot_rows=len(ranked),
        eligible_rows=len(ranked),
        selection_exhausted=bool(stats["selection_exhausted"]),
    )
    page = make_selection_page(
        binding_sha256=binding_sha256,
        snapshot_identity_sha256_value=ranked_identity_sha256,
        page_sequence=ledger["completed_pages"],
        previous_ack_sha256=ledger["last_ack_sha256"],
        start_index=start_index,
        next_index=next_index,
        selected_digests=selected_digests,
        scan_evidence=scan_evidence,
    )
    if pending is not None and dict(pending) != page:
        raise ValueError("pending selection page no longer replays exactly")
    ledger = install_pending_page(ledger, page)
    atomic_write_json(ledger_path, ledger)
    return selected, stats, page, ledger


def _prepare_snapshot_selection_page(
    snapshot: RankedSnapshot,
    *,
    top: int,
    ledger_path: Path,
    known_answer_artifact: Path,
    canonicalizer: Callable[[Mapping[str, Any]], dict[str, Any]] | None = None,
) -> tuple[
    list[dict[str, Any]],
    dict[str, int],
    dict[str, Any],
    dict[str, Any],
]:
    """Create or replay one pending page directly from an immutable snapshot."""

    binding_sha256 = _selection_binding(
        (),
        top=top,
        known_answer_artifact=known_answer_artifact,
        ranked_snapshot_identity=snapshot.identity,
        ranked_size=snapshot.rows,
    )
    ranked_identity_sha256 = snapshot_identity_sha256(snapshot.identity)
    ledger = _load_selection_ledger(
        ledger_path,
        binding_sha256=binding_sha256,
        snapshot_identity_sha256_value=ranked_identity_sha256,
        snapshot_rows=snapshot.rows,
        eligible_rows=snapshot.eligible_rows,
    )
    pending = ledger.get("pending")
    start_index = int(
        pending["start_index"] if isinstance(pending, Mapping)
        else ledger["cursor"]
    )
    selected, stats, next_index = _select_snapshot_audit_page(
        snapshot,
        top,
        start_index=start_index,
        seen_digests=ledger["committed_digests"],
        canonicalizer=canonicalizer,
    )
    selected_digests = [
        str(row["triage_identity"]["canonical_digest"])
        for row in selected
    ]
    scan_evidence = make_scan_evidence(
        snapshot_identity_sha256_value=ranked_identity_sha256,
        start_index=start_index,
        next_index=next_index,
        snapshot_rows=snapshot.rows,
        eligible_rows=snapshot.eligible_rows,
        selection_exhausted=bool(stats["selection_exhausted"]),
    )
    page = make_selection_page(
        binding_sha256=binding_sha256,
        snapshot_identity_sha256_value=ranked_identity_sha256,
        page_sequence=ledger["completed_pages"],
        previous_ack_sha256=ledger["last_ack_sha256"],
        start_index=start_index,
        next_index=next_index,
        selected_digests=selected_digests,
        scan_evidence=scan_evidence,
    )
    if pending is not None and dict(pending) != page:
        raise ValueError("pending selection page no longer replays exactly")
    ledger = install_pending_page(ledger, page)
    atomic_write_json(ledger_path, ledger)
    return selected, stats, page, ledger


def _certificate_budget(config: AuditConfig) -> dict[str, float | int]:
    return {
        "timeout_per_logical_s": config.certificate_timeout_per_logical_s,
        "total_timeout_s": config.certificate_total_timeout_s,
        "solver_workers": config.certificate_solver_workers,
    }


def _verification_budget(config: AuditConfig) -> dict[str, float | int]:
    return {
        "timeout_per_logical_s": config.verification_timeout_per_logical_s,
        "total_timeout_s": config.verification_total_timeout_s,
        "solver_workers": config.certificate_solver_workers,
    }


def _certificate_is_exact(certificate: Mapping[str, Any]) -> bool:
    milp = certificate.get("milp")
    if not isinstance(milp, Mapping) or milp.get("exact") is not True:
        return False
    try:
        return int(milp["completed_directions"]) == int(
            milp["expected_directions"],
        )
    except (KeyError, TypeError, ValueError):
        return False


def _cache_binding_matches(
    metadata: Mapping[str, Any] | None,
    *,
    canonical_digest: str,
    candidate_payload_sha256: str,
    known_answer_sha256: str | None,
    solver_runtime: Mapping[str, Any],
    source_fingerprint: str,
) -> bool:
    return bool(
        isinstance(metadata, Mapping)
        and metadata.get("schema_version") == CACHE_SCHEMA_VERSION
        and metadata.get("canonical_digest") == canonical_digest
        and metadata.get("candidate_payload_sha256") == candidate_payload_sha256
        and metadata.get("known_answer_sha256") == known_answer_sha256
        and metadata.get("solver_runtime") == solver_runtime
        and metadata.get("source_fingerprint") == source_fingerprint
    )


def _certificate_cache_reusable(
    certificate: Mapping[str, Any] | None,
    metadata: Mapping[str, Any] | None,
    *,
    canonical_digest: str,
    known_answer_sha256: str | None,
    candidate_payload_sha256: str,
    solver_runtime: Mapping[str, Any],
    source_fingerprint: str,
) -> tuple[bool, bool]:
    """Return (reusable, checkpoint-compatible) for a certificate cache."""

    binding_matches = _cache_binding_matches(
        metadata,
        canonical_digest=canonical_digest,
        candidate_payload_sha256=candidate_payload_sha256,
        known_answer_sha256=known_answer_sha256,
        solver_runtime=solver_runtime,
        source_fingerprint=source_fingerprint,
    )
    if certificate is None or not binding_matches:
        return False, False
    if metadata.get("certificate_payload_sha256") != _json_sha256(certificate):
        return False, False
    # Incomplete work is never terminal; its checkpoint keeps valid directions.
    return _certificate_is_exact(certificate), True


def _call_with_checkpoint(
    operation: Callable[..., dict[str, Any]],
    positional: Mapping[str, Any],
    *,
    checkpoint_path: Path,
    resume: bool,
    kwargs: Mapping[str, Any],
) -> dict[str, Any]:
    return operation(
        dict(positional),
        checkpoint_path=checkpoint_path,
        resume=resume,
        **dict(kwargs),
    )


def certify_candidate(
    candidate: dict[str, Any],
    canonical_digest: str,
    config: AuditConfig,
    *,
    builder: Callable[..., dict[str, Any]] | None = None,
    verifier: Callable[..., dict[str, Any]] | None = None,
) -> dict[str, Any]:
    """Build and independently verify a durable exact certificate.

    Exact terminal results are reusable. Incomplete builds and failed
    verification runs resume checkpoints. Every cache is bound to the
    candidate, known-answer artifact, and solver runtime.
    """

    builder = build_certificate if builder is None else builder
    verifier = verify_certificate if verifier is None else verifier
    paths = state_paths(config.state_dir, canonical_digest)
    known_answer_sha256 = _file_sha256(config.known_answer_artifact)
    solver_runtime = solver_runtime_fingerprint()
    source_fingerprint = certificate_source_fingerprint()
    build_budget = _certificate_budget(config)
    candidate_payload_sha256 = _json_sha256(candidate)

    certificate = (
        _load_json_object(paths["certificate"]) if config.resume else None
    )
    certificate_metadata = (
        _load_json_object(paths["certificate_metadata"])
        if config.resume else None
    )
    reusable, checkpoint_compatible = _certificate_cache_reusable(
        certificate,
        certificate_metadata,
        canonical_digest=canonical_digest,
        known_answer_sha256=known_answer_sha256,
        candidate_payload_sha256=candidate_payload_sha256,
        solver_runtime=solver_runtime,
        source_fingerprint=source_fingerprint,
    )
    certificate_resumed = reusable
    if not reusable:
        checkpoint_resume = bool(
            config.resume
            and (
                checkpoint_compatible
                or certificate_metadata is None
            )
        )
        certificate = _call_with_checkpoint(
            builder,
            candidate,
            checkpoint_path=paths["certificate_checkpoint"],
            resume=checkpoint_resume,
            kwargs={
                "known_answer_artifact": config.known_answer_artifact,
                "timeout_per_logical": (
                    config.certificate_timeout_per_logical_s
                ),
                "total_timeout": config.certificate_total_timeout_s,
                "solver_workers": config.certificate_solver_workers,
            },
        )
        atomic_write_json(paths["certificate"], certificate)
        atomic_write_json(
            paths["certificate_metadata"],
            {
                "schema_version": CACHE_SCHEMA_VERSION,
                "kind": "qldpc-certificate-cache",
                "canonical_digest": canonical_digest,
                "known_answer_sha256": known_answer_sha256,
                "candidate_payload_sha256": candidate_payload_sha256,
                "solver_runtime": solver_runtime,
                "source_fingerprint": source_fingerprint,
                "budget": build_budget,
                "exact": _certificate_is_exact(certificate),
                "passed": certificate.get("passed") is True,
                "certificate_sha256": certificate.get("certificate_sha256"),
                "certificate_payload_sha256": _json_sha256(certificate),
            },
        )

    certificate_sha256 = certificate.get("certificate_sha256")
    certificate_payload_sha256 = _json_sha256(certificate)
    certificate_exact = _certificate_is_exact(certificate)
    certificate_passed = bool(
        certificate_exact and certificate.get("passed") is True,
    )
    verify_budget = _verification_budget(config)
    verification_envelope = (
        _load_json_object(paths["verification"]) if config.resume else None
    )
    verification = None
    verification_resumed = False
    verification_binding_matches = bool(
        _cache_binding_matches(
            verification_envelope,
            canonical_digest=canonical_digest,
            candidate_payload_sha256=candidate_payload_sha256,
            known_answer_sha256=known_answer_sha256,
            solver_runtime=solver_runtime,
            source_fingerprint=source_fingerprint,
        )
        and verification_envelope.get("certificate_payload_sha256")
        == certificate_payload_sha256
        and isinstance(verification_envelope.get("verification"), dict)
    )
    if verification_binding_matches:
        cached_verification = verification_envelope["verification"]
        successful = cached_verification.get("passed") is True
        terminal_skip = bool(
            cached_verification.get("skipped") is True
            and not certificate_passed
            and certificate_exact
        )
        if successful or terminal_skip:
            verification = cached_verification
            verification_resumed = True
    if verification is None:
        if certificate_passed:
            verification_checkpoint_resume = bool(
                config.resume
                and (
                    verification_binding_matches
                    or verification_envelope is None
                )
            )
            verification = _call_with_checkpoint(
                verifier,
                certificate,
                checkpoint_path=paths["verification_checkpoint"],
                resume=verification_checkpoint_resume,
                kwargs={
                    "known_answer_artifact": config.known_answer_artifact,
                    "rerun_milp": True,
                    "timeout_per_logical": (
                        config.verification_timeout_per_logical_s
                    ),
                    "total_timeout": config.verification_total_timeout_s,
                    "solver_workers": config.certificate_solver_workers,
                },
            )
        else:
            verification = {
                "passed": False,
                "skipped": True,
                "reason": (
                    "certificate build did not pass the exact challenge gate"
                ),
            }
        atomic_write_json(
            paths["verification"],
            {
                "schema_version": CACHE_SCHEMA_VERSION,
                "kind": "qldpc-certificate-verification-cache",
                "canonical_digest": canonical_digest,
                "known_answer_sha256": known_answer_sha256,
                "candidate_payload_sha256": candidate_payload_sha256,
                "solver_runtime": solver_runtime,
                "source_fingerprint": source_fingerprint,
                "budget": verify_budget,
                "certificate_sha256": certificate_sha256,
                "certificate_payload_sha256": certificate_payload_sha256,
                "verification": verification,
            },
        )

    return {
        "attempted": True,
        "certificate_path": str(paths["certificate"]),
        "certificate_checkpoint_path": str(paths["certificate_checkpoint"]),
        "verification_path": str(paths["verification"]),
        "verification_checkpoint_path": str(
            paths["verification_checkpoint"],
        ),
        "certificate_exact": certificate_exact,
        "certificate_passed": certificate_passed,
        "verification_passed": verification.get("passed") is True,
        "verification_attempted": verification.get("skipped") is not True,
        "certificate_resumed": certificate_resumed,
        "verification_resumed": verification_resumed,
    }


def audit_candidate(
    ranked: Mapping[str, Any],
    config: AuditConfig,
    *,
    symmetry_checker: Callable[[dict[str, Any]], dict[str, Any]] | None = None,
    replay_loader: Callable[..., list[dict[str, Any]]] | None = None,
    sector_solver: Callable[[tuple[Any, ...]], dict[str, Any]] | None = None,
    artifact_writer: Callable[..., dict[str, Any]] | None = None,
    # Retained for source compatibility only. Stage 2 deliberately never
    # invokes certificate work inside a candidate/CP-SAT worker.
    certificate_builder: Callable[..., dict[str, Any]] | None = None,
    certificate_verifier: Callable[..., dict[str, Any]] | None = None,
) -> dict[str, Any]:
    """Run a resumable two-sector threshold audit for one ranked candidate."""

    symmetry_checker = (
        verify_bb_translation_symmetry
        if symmetry_checker is None else symmetry_checker
    )
    replay_loader = (
        load_replayable_sectors if replay_loader is None else replay_loader
    )
    sector_solver = solve_sector if sector_solver is None else sector_solver
    artifact_writer = write_artifact if artifact_writer is None else artifact_writer

    identity = ranked.get("triage_identity")
    if not isinstance(identity, Mapping):
        identity = candidate_identity(ranked)
    canonical_digest = str(identity["canonical_digest"])
    paths = state_paths(config.state_dir, canonical_digest)

    try:
        candidate = _construction_candidate(ranked, canonical_digest)
    except (KeyError, TypeError, ValueError) as exc:
        return {
            "canonical_digest": canonical_digest,
            "status": "UNSUPPORTED",
            "error": str(exc),
        }
    if candidate.get("C_terms") or candidate.get("D_terms"):
        return {
            "canonical_digest": canonical_digest,
            "status": "UNSUPPORTED",
            "error": "XOR sector audit currently supports CSS candidates only",
        }

    symmetry = symmetry_checker(candidate)
    if symmetry.get("verified") is not True:
        artifact = artifact_writer(
            paths["audit"],
            candidate,
            [],
            threshold_only=True,
            translation_symmetry=symmetry,
        )
        return {
            "canonical_digest": canonical_digest,
            "status": artifact["status"],
            "audit_path": str(paths["audit"]),
            "error": "BB translation symmetry audit failed",
        }

    sectors = (
        replay_loader(
            paths["audit"],
            candidate,
            threshold_only=True,
            translation_symmetry=symmetry,
        )
        if config.resume else []
    )
    artifact = artifact_writer(
        paths["audit"],
        candidate,
        sectors,
        threshold_only=True,
        translation_symmetry=symmetry,
    )
    resumed_sectors = len(sectors)
    completed = {str(item.get("sector")) for item in sectors}
    anchors = tuple(int(value) for value in symmetry["orbit_representatives"])
    max_weight = int(candidate["required_distance"]) - 1

    for sector in ("X", "Z"):
        if artifact["status"] in TERMINAL_STATUSES:
            break
        if sector in completed:
            continue
        result = sector_solver((
            candidate,
            sector,
            config.solver_timeout_s,
            max_weight,
            config.solver_workers,
            config.seed,
            anchors,
        ))
        sectors = [
            item for item in sectors
            if str(item.get("sector")) != sector
        ]
        sectors.append(result)
        artifact = artifact_writer(
            paths["audit"],
            candidate,
            sectors,
            threshold_only=True,
            translation_symmetry=symmetry,
        )

    result: dict[str, Any] = {
        "canonical_digest": canonical_digest,
        "status": artifact["status"],
        "audit_path": str(paths["audit"]),
        "completed_sectors": artifact["completed_sectors"],
        "resumed_sectors": resumed_sectors,
    }
    if artifact["status"] == "THRESHOLD_PROVEN":
        result["certificate"] = {"attempted": False}
        if config.certify:
            result["certificate"]["deferred"] = True
    return result


def _audit_worker(
    payload: tuple[dict[str, Any], AuditConfig],
) -> dict[str, Any]:
    ranked, config = payload
    return audit_candidate(ranked, config)


def _candidate_hard_timeout(config: AuditConfig) -> float:
    """Bound both sequential X/Z sector calls for one Stage 2 candidate."""

    configured = config.candidate_hard_timeout_s
    if configured is not None:
        return positive_wall_timeout(configured, "candidate hard timeout")
    # Each candidate has exactly two sequential sector solves.  The fixed
    # allowance covers reconstruction and atomic checkpoint writes.
    return 2.0 * positive_wall_timeout(
        config.solver_timeout_s, "solver timeout"
    ) + 5.0


def _certificate_hard_timeout(config: AuditConfig) -> float:
    """Bound one complete build plus independent verification candidate."""

    configured = config.certificate_hard_timeout_s
    if configured is not None:
        return positive_wall_timeout(configured, "certificate hard timeout")
    return (
        positive_wall_timeout(
            config.certificate_total_timeout_s,
            "certificate total timeout",
        )
        + positive_wall_timeout(
            config.verification_total_timeout_s,
            "verification total timeout",
        )
        + 5.0
    )


def _stage2_hard_wall_result(
    candidate: Mapping[str, Any],
    config: AuditConfig,
    *,
    hard_timeout_s: float,
    peer_timeout: bool,
) -> dict[str, Any]:
    """Recover a just-committed artifact or mark killed work retryable."""

    identity = candidate.get("triage_identity")
    if not isinstance(identity, Mapping):
        identity = candidate_identity(candidate)
    digest = str(identity["canonical_digest"])
    path = state_paths(config.state_dir, digest)["audit"]
    artifact = _load_json_object(path)
    if artifact is not None and artifact.get("status") in TERMINAL_STATUSES:
        result: dict[str, Any] = {
            "canonical_digest": digest,
            "status": str(artifact["status"]),
            "audit_path": str(path),
            "completed_sectors": int(
                artifact.get("completed_sectors", 0) or 0
            ),
            "resumed_sectors": 0,
            "recovered_after_worker_termination": True,
        }
        if result["status"] == "THRESHOLD_PROVEN":
            result["certificate"] = {
                "attempted": False,
                "deferred": config.certify,
            }
        return result
    return {
        "canonical_digest": digest,
        "status": "UNRESOLVED",
        "audit_path": str(path),
        "completed_sectors": int(
            artifact.get("completed_sectors", 0)
            if artifact is not None else 0
        ),
        "resumed_sectors": 0,
        "hard_wall": {
            "timed_out": not peer_timeout,
            "peer_timeout_interruption": peer_timeout,
            "candidate_timeout_s": hard_timeout_s,
        },
    }


def audit_selected_candidates(
    selected: list[dict[str, Any]],
    config: AuditConfig,
    *,
    candidate_workers: int,
) -> list[dict[str, Any]]:
    """Audit candidates with a process-enforced wall deadline per candidate."""

    if candidate_workers < 1:
        raise ValueError("candidate_workers must be positive")
    hard_timeout = _candidate_hard_timeout(config)
    termination_grace = positive_wall_timeout(
        config.hard_wall_termination_grace_s,
        "hard-wall termination grace",
    )
    queued = deque(selected)
    completed: dict[str, dict[str, Any]] = {}
    while queued:
        executor = ProcessPoolExecutor(max_workers=candidate_workers)
        active: dict[Any, tuple[dict[str, Any], float]] = {}
        pool_terminated = False

        def submit_available() -> None:
            while queued and len(active) < candidate_workers:
                candidate = queued.popleft()
                future = executor.submit(_audit_worker, (candidate, config))
                active[future] = (
                    candidate,
                    time.monotonic() + hard_timeout,
                )

        submit_available()
        try:
            while active:
                now = time.monotonic()
                next_deadline = min(deadline for _, deadline in active.values())
                done, _ = wait(
                    active,
                    timeout=max(0.0, next_deadline - now),
                    return_when=FIRST_COMPLETED,
                )
                for future in done:
                    candidate, _ = active.pop(future)
                    identity = candidate.get("triage_identity")
                    if not isinstance(identity, Mapping):
                        identity = candidate_identity(candidate)
                    digest = str(identity["canonical_digest"])
                    try:
                        completed[digest] = future.result()
                    except Exception as exc:
                        completed[digest] = {
                            "canonical_digest": digest,
                            "status": "ERROR",
                            "error": f"{type(exc).__name__}: {exc}",
                        }
                submit_available()
                now = time.monotonic()
                overdue = {
                    future
                    for future, (_, deadline) in active.items()
                    if deadline <= now
                }
                if not overdue:
                    continue
                interrupted = list(active.values())
                terminate_process_pool(
                    executor,
                    grace_s=termination_grace,
                )
                pool_terminated = True
                for candidate, deadline in interrupted:
                    identity = candidate.get("triage_identity")
                    if not isinstance(identity, Mapping):
                        identity = candidate_identity(candidate)
                    digest = str(identity["canonical_digest"])
                    completed[digest] = _stage2_hard_wall_result(
                        candidate,
                        config,
                        hard_timeout_s=hard_timeout,
                        peer_timeout=deadline > now,
                    )
                active.clear()
        finally:
            if not pool_terminated:
                executor.shutdown(wait=True, cancel_futures=True)
    order = {
        str(candidate["triage_identity"]["canonical_digest"]): index
        for index, candidate in enumerate(selected)
    }
    return sorted(
        completed.values(),
        key=lambda item: order[item["canonical_digest"]],
    )


def _certificate_phase_item(
    item: Mapping[str, Any],
) -> tuple[dict[str, Any], str]:
    """Normalize a ranked row or Stage-3 artifact for exact certification."""

    nested = item.get("candidate")
    gate = item.get("gate")
    if gate == STAGE3_GATE:
        raw_candidate = claim_from_certifiable_stage3_artifact(item)
    elif gate is not None:
        raise ValueError(f"unsupported certification artifact gate: {gate}")
    elif isinstance(nested, Mapping):
        raw_candidate = dict(nested)
    else:
        raw_candidate = dict(item)

    digest_values: list[str] = []
    for digest_value in (
        item.get("canonical_digest"),
        raw_candidate.get("canonical_digest"),
    ):
        if digest_value:
            digest_values.append(str(digest_value))
    identity = item.get("triage_identity")
    if isinstance(identity, Mapping) and identity.get("canonical_digest"):
        digest_values.append(str(identity["canonical_digest"]))
    nested_identity = raw_candidate.get("triage_identity")
    if (
        isinstance(nested_identity, Mapping)
        and nested_identity.get("canonical_digest")
    ):
        digest_values.append(str(nested_identity["canonical_digest"]))
    if not digest_values:
        raise ValueError("certification item lacks a canonical digest")
    if len(set(digest_values)) != 1:
        raise ValueError("certification item has conflicting canonical digests")
    canonical_digest = digest_values[0]
    return (
        _construction_candidate(raw_candidate, canonical_digest),
        canonical_digest,
    )


def claim_from_certifiable_stage3_artifact(
    artifact: Mapping[str, Any],
) -> dict[str, Any]:
    """Validate and unwrap either terminal Stage-3 proof status.

    ``claim_from_threshold_artifact`` already performs the authoritative
    envelope, geometry, direction, and witness replay.  An exact Stage-3 run
    has the same artifact schema and proof obligations, but reports
    ``EXACT_PROVEN`` and must have used the uncapped formulation.  Normalize
    only that status for the shared validator; no evidence is weakened.
    """

    status = artifact.get("status")
    if status == "THRESHOLD_PROVEN":
        return claim_from_threshold_artifact(artifact)
    if status != "EXACT_PROVEN":
        raise ValueError(
            "Stage 3 artifact status must be THRESHOLD_PROVEN or EXACT_PROVEN"
        )
    if artifact.get("threshold_only") is not False:
        raise ValueError(
            "Stage 3 EXACT_PROVEN artifact must have threshold_only=false"
        )
    normalized = dict(artifact)
    normalized["status"] = "THRESHOLD_PROVEN"
    return claim_from_threshold_artifact(normalized)


def _certificate_phase_failure(exc: Exception) -> dict[str, Any]:
    return {
        "attempted": True,
        "certificate_passed": False,
        "verification_passed": False,
        "error": f"{type(exc).__name__}: {exc}",
    }


def _certificate_phase_hard_wall(
    *,
    hard_timeout_s: float,
    peer_timeout: bool,
) -> dict[str, Any]:
    reason = (
        "certificate worker terminated after a peer hard-wall timeout"
        if peer_timeout
        else "certificate/verification candidate hard-wall timeout"
    )
    return {
        "attempted": True,
        "certificate_passed": False,
        "verification_passed": False,
        "error": reason,
        "hard_wall": {
            "timed_out": not peer_timeout,
            "peer_timeout_interruption": peer_timeout,
            "candidate_timeout_s": hard_timeout_s,
        },
    }


def _certificate_worker(
    payload: tuple[
        dict[str, Any],
        str,
        AuditConfig,
        Callable[..., dict[str, Any]],
    ],
) -> tuple[str, dict[str, Any]]:
    candidate, canonical_digest, config, certifier = payload
    return (
        canonical_digest,
        certifier(candidate, canonical_digest, config),
    )


def certify_selected_candidates(
    items: Iterable[Mapping[str, Any]],
    config: AuditConfig,
    *,
    certificate_workers: int = 1,
    max_total_workers: int | None = None,
    certifier: Callable[..., dict[str, Any]] | None = None,
) -> dict[str, dict[str, Any]]:
    """Run exact certification in a separate, bounded campaign phase.

    Callers must finish all screening workers before entering this function.
    Ranked Stage-2 rows and successful Stage-3 artifacts share this entrypoint.
    """

    if certificate_workers < 1:
        raise ValueError("certificate_workers must be positive")
    if max_total_workers is not None:
        validate_worker_budget(
            certificate_workers,
            config.certificate_solver_workers,
            max_total_workers,
        )
    custom_certifier = certifier is not None
    certifier = certify_candidate if certifier is None else certifier
    prepared: list[tuple[dict[str, Any], str]] = []
    seen: set[str] = set()
    for item in items:
        candidate, canonical_digest = _certificate_phase_item(item)
        if canonical_digest in seen:
            continue
        seen.add(canonical_digest)
        prepared.append((candidate, canonical_digest))

    if not config.certify:
        return {
            digest: {"attempted": False}
            for _, digest in prepared
        }

    results: dict[str, dict[str, Any]] = {}
    # Unit/integration callers may inject a local closure that cannot cross a
    # process boundary.  Production always uses the default top-level
    # certifier and therefore always receives the hard wall, including with a
    # single configured worker.
    if certificate_workers == 1 and custom_certifier:
        for candidate, digest in prepared:
            try:
                results[digest] = certifier(candidate, digest, config)
            except Exception as exc:
                results[digest] = _certificate_phase_failure(exc)
        return results

    hard_timeout = _certificate_hard_timeout(config)
    termination_grace = positive_wall_timeout(
        config.hard_wall_termination_grace_s,
        "hard-wall termination grace",
    )
    queued = deque(prepared)
    completed: dict[str, dict[str, Any]] = {}
    while queued:
        executor = ProcessPoolExecutor(max_workers=certificate_workers)
        active: dict[Any, tuple[str, float]] = {}
        pool_terminated = False

        def submit_available() -> None:
            while queued and len(active) < certificate_workers:
                candidate, digest = queued.popleft()
                future = executor.submit(
                    _certificate_worker,
                    (candidate, digest, config, certifier),
                )
                active[future] = (
                    digest,
                    time.monotonic() + hard_timeout,
                )

        submit_available()
        try:
            while active:
                now = time.monotonic()
                next_deadline = min(deadline for _, deadline in active.values())
                done, _ = wait(
                    active,
                    timeout=max(0.0, next_deadline - now),
                    return_when=FIRST_COMPLETED,
                )
                for future in done:
                    digest, _ = active.pop(future)
                    try:
                        returned_digest, result = future.result()
                        if returned_digest != digest:
                            raise ValueError(
                                "certificate worker returned wrong digest"
                            )
                        completed[digest] = result
                    except Exception as exc:
                        completed[digest] = _certificate_phase_failure(exc)
                submit_available()
                now = time.monotonic()
                overdue = {
                    future
                    for future, (_, deadline) in active.items()
                    if deadline <= now
                }
                if not overdue:
                    continue
                interrupted = list(active.values())
                terminate_process_pool(
                    executor,
                    grace_s=termination_grace,
                )
                pool_terminated = True
                for digest, deadline in interrupted:
                    completed[digest] = _certificate_phase_hard_wall(
                        hard_timeout_s=hard_timeout,
                        peer_timeout=deadline > now,
                    )
                active.clear()
        finally:
            if not pool_terminated:
                executor.shutdown(wait=True, cancel_futures=True)
    return {
        digest: completed[digest]
        for _, digest in prepared
    }


def merge_certification_results(
    screening_results: Iterable[Mapping[str, Any]],
    certifications: Mapping[str, Mapping[str, Any]],
    *,
    certify: bool,
) -> list[dict[str, Any]]:
    """Merge the non-overlapping certification phase into screen results."""

    merged: list[dict[str, Any]] = []
    for result in screening_results:
        updated = dict(result)
        if updated.get("status") in CERTIFIABLE_PROOF_STATUSES:
            digest = str(updated["canonical_digest"])
            if not certify:
                updated["certificate"] = {"attempted": False}
            elif digest in certifications:
                updated["certificate"] = dict(certifications[digest])
            else:
                updated["certificate"] = {
                    "attempted": False,
                    "certificate_passed": False,
                    "verification_passed": False,
                    "error": "missing result from certification phase",
                }
        merged.append(updated)
    return merged


def _annotate_ranked(
    ranked: list[dict[str, Any]],
    selected_digests: set[str],
    results: Iterable[Mapping[str, Any]] = (),
) -> list[dict[str, Any]]:
    by_digest = {
        str(result["canonical_digest"]): dict(result)
        for result in results
    }
    annotated = []
    remaining_selected = set(selected_digests)
    for row in ranked:
        updated = dict(row)
        digest = str(row["triage_identity"]["canonical_digest"])
        selected = digest in remaining_selected
        updated["campaign_selected"] = selected
        if selected:
            remaining_selected.remove(digest)
        if selected and digest in by_digest:
            updated["campaign_audit"] = by_digest[digest]
        else:
            updated.pop("campaign_audit", None)
        annotated.append(updated)
    return annotated


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("inputs", nargs="+", type=Path)
    parser.add_argument("--top", type=int, default=20)
    parser.add_argument("--state-dir", type=Path, required=True)
    parser.add_argument("--ranked-output", type=Path, required=True)
    parser.add_argument("--summary-output", type=Path, required=True)
    parser.add_argument(
        "--selection-ledger",
        type=Path,
        help=(
            "durable Stage 2 pagination ledger; an unacknowledged page is "
            "replayed exactly after interruption"
        ),
    )
    parser.add_argument("--timeout", type=float, default=300)
    parser.add_argument("--candidate-workers", type=int, default=2)
    parser.add_argument("--solver-workers", type=int, default=4)
    parser.add_argument("--certificate-workers", type=int, default=1)
    parser.add_argument("--certificate-solver-workers", type=int, default=1)
    parser.add_argument("--max-total-workers", type=int, default=8)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument(
        "--resume",
        action=argparse.BooleanOptionalAction,
        default=True,
    )
    parser.add_argument(
        "--certify",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="build and independently rerun an exact certificate after proof",
    )
    parser.add_argument(
        "--known-answer-artifact",
        type=Path,
        default=DEFAULT_KNOWN_ANSWER,
    )
    parser.add_argument(
        "--certificate-timeout-per-logical",
        type=float,
        default=300,
    )
    parser.add_argument(
        "--certificate-total-timeout",
        type=float,
        default=7200,
    )
    parser.add_argument(
        "--verification-timeout-per-logical",
        type=float,
        default=300,
    )
    parser.add_argument(
        "--verification-total-timeout",
        type=float,
        default=7200,
    )
    parser.add_argument(
        "--candidate-hard-timeout",
        type=float,
        help=(
            "process wall timeout per Stage 2 candidate; defaults to two "
            "sector soft budgets plus checkpoint overhead"
        ),
    )
    parser.add_argument(
        "--certificate-hard-timeout",
        type=float,
        help=(
            "process wall timeout per certificate candidate; defaults to "
            "build plus verification total budgets"
        ),
    )
    parser.add_argument(
        "--hard-wall-termination-grace",
        type=float,
        default=DEFAULT_TERMINATION_GRACE_S,
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    if args.top < 0:
        parser.error("top must be non-negative")
    for name in (
        "timeout",
        "certificate_timeout_per_logical",
        "certificate_total_timeout",
        "verification_timeout_per_logical",
        "verification_total_timeout",
        "hard_wall_termination_grace",
    ):
        value = getattr(args, name)
        if not math.isfinite(value) or value <= 0:
            parser.error(f"{name.replace('_', '-')} must be positive")
    for name in ("candidate_hard_timeout", "certificate_hard_timeout"):
        value = getattr(args, name)
        if value is not None and (not math.isfinite(value) or value <= 0):
            parser.error(f"{name.replace('_', '-')} must be positive")
    ranked_snapshot: RankedSnapshot | None = None
    ranked_snapshot_identity: dict[str, Any] | None = None
    ranked_snapshot_cache_hit = False
    try:
        validate_worker_budget(
            args.candidate_workers,
            args.solver_workers,
            args.max_total_workers,
        )
        validate_worker_budget(
            args.certificate_workers,
            args.certificate_solver_workers,
            args.max_total_workers,
        )
        if args.selection_ledger is None:
            ranked, counts = rank_candidate_files(args.inputs)
        else:
            ranked_snapshot, ranked_snapshot_cache_hit = prepare_ranked_snapshot(
                args.inputs,
                ledger_path=args.selection_ledger,
            )
            ranked = []
            counts = dict(ranked_snapshot.counts)
            ranked_snapshot_identity = dict(ranked_snapshot.identity)
    except (OSError, TypeError, ValueError) as exc:
        parser.error(str(exc))

    selection_page: dict[str, Any] | None = None
    try:
        if args.selection_ledger is None:
            selected, selection_counts = select_audit_candidates(
                ranked, args.top,
            )
        else:
            assert ranked_snapshot is not None
            (
                selected,
                selection_counts,
                selection_page,
                _,
            ) = _prepare_snapshot_selection_page(
                ranked_snapshot,
                top=args.top,
                ledger_path=args.selection_ledger,
                known_answer_artifact=args.known_answer_artifact,
            )
            # The page artifact is intentionally bounded. Stage 3 consumes only
            # the current page's unresolved rows; the immutable snapshot and
            # ledger own the global pool and cursor.
            ranked = list(selected)
    except (OSError, TypeError, ValueError) as exc:
        parser.error(str(exc))
    selected_digests = {
        str(row["triage_identity"]["canonical_digest"])
        for row in selected
    }
    atomic_write_jsonl(
        args.ranked_output,
        _annotate_ranked(ranked, selected_digests),
    )

    config = AuditConfig(
        state_dir=args.state_dir,
        solver_timeout_s=args.timeout,
        solver_workers=args.solver_workers,
        seed=args.seed,
        resume=args.resume,
        certify=args.certify,
        known_answer_artifact=args.known_answer_artifact,
        certificate_timeout_per_logical_s=(
            args.certificate_timeout_per_logical
        ),
        certificate_total_timeout_s=args.certificate_total_timeout,
        certificate_solver_workers=args.certificate_solver_workers,
        verification_timeout_per_logical_s=(
            args.verification_timeout_per_logical
        ),
        verification_total_timeout_s=args.verification_total_timeout,
        candidate_hard_timeout_s=args.candidate_hard_timeout,
        certificate_hard_timeout_s=args.certificate_hard_timeout,
        hard_wall_termination_grace_s=(
            args.hard_wall_termination_grace
        ),
    )
    screening_results = audit_selected_candidates(
        selected,
        config,
        candidate_workers=args.candidate_workers,
    )
    # Stage 2 is fully complete and durable before Stage 4 can consume CPU.
    atomic_write_jsonl(
        args.ranked_output,
        _annotate_ranked(ranked, selected_digests, screening_results),
    )
    threshold_digests = {
        str(result["canonical_digest"])
        for result in screening_results
        if result.get("status") == "THRESHOLD_PROVEN"
    }
    certificate_items = [
        candidate for candidate in selected
        if str(candidate["triage_identity"]["canonical_digest"])
        in threshold_digests
    ]
    certifications = certify_selected_candidates(
        certificate_items,
        config,
        certificate_workers=args.certificate_workers,
        max_total_workers=args.max_total_workers,
    )
    results = merge_certification_results(
        screening_results,
        certifications,
        certify=args.certify,
    )
    annotated = _annotate_ranked(ranked, selected_digests, results)
    atomic_write_jsonl(args.ranked_output, annotated)

    status_counts: dict[str, int] = {}
    for result in results:
        status = str(result["status"])
        status_counts[status] = status_counts.get(status, 0) + 1
    certified = sum(
        result.get("certificate", {}).get("certificate_passed") is True
        and result.get("certificate", {}).get("verification_passed") is True
        for result in results
    )
    summary = {
        "schema_version": 1,
        "gate": "qldpc-proof-oriented-candidate-pool",
        "inputs": [str(path) for path in args.inputs],
        **counts,
        **selection_counts,
        "selected_candidates": len(selected),
        "top": args.top,
        "worker_budget": {
            "candidate_workers": args.candidate_workers,
            "solver_workers": args.solver_workers,
            "max_total_workers": args.max_total_workers,
            "configured_solver_workers": (
                args.candidate_workers * args.solver_workers
            ),
        },
        "hard_wall_budget": {
            "candidate_timeout_s": _candidate_hard_timeout(config),
            "certificate_timeout_s": _certificate_hard_timeout(config),
            "termination_grace_s": config.hard_wall_termination_grace_s,
        },
        "phase_worker_budgets": {
            "phases_overlap": False,
            "sector_audit": {
                "candidate_workers": args.candidate_workers,
                "solver_workers_per_candidate": args.solver_workers,
                "configured_solver_workers": (
                    args.candidate_workers * args.solver_workers
                ),
                "max_total_workers": args.max_total_workers,
            },
            "certification": {
                "enabled": args.certify,
                "certificate_workers": args.certificate_workers,
                "solver_workers_per_certificate": (
                    args.certificate_solver_workers
                ),
                "configured_solver_workers": (
                    args.certificate_workers
                    * args.certificate_solver_workers
                ),
                "max_total_workers": args.max_total_workers,
            },
        },
        "certify": args.certify,
        "status_counts": status_counts,
        "certified_wins": certified,
        "certificate_operational_errors": sum(
            bool(result.get("certificate", {}).get("error"))
            for result in results
        ),
        "ranked_output": str(args.ranked_output),
        "state_dir": str(args.state_dir),
        "results": results,
    }
    if selection_page is not None:
        summary["selection_page"] = selection_page
    if ranked_snapshot_identity is not None:
        summary["ranked_snapshot"] = {
            **ranked_snapshot_identity,
            "cache_hit": ranked_snapshot_cache_hit,
        }
    atomic_write_json(args.summary_output, summary)
    print(json.dumps(summary, indent=2))
    return 0 if not (
        any(result["status"] == "ERROR" for result in results)
        or summary["certificate_operational_errors"]
    ) else 2


if __name__ == "__main__":
    raise SystemExit(main())
