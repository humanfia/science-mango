#!/usr/bin/env python3
"""Rank, deduplicate, and deeply audit a pool of qLDPC candidates."""

from __future__ import annotations

import argparse
import hashlib
import importlib.metadata
import json
import math
import os
import platform
import sys
import uuid
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Iterable, Mapping

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation.bb_code import build_bb_code
from evaluation.certificate_dispatch import build_certificate, verify_certificate
from evaluation.final_gate import classify_win, minimum_winning_distance
from evaluation.proof_triage import (
    candidate_identity,
    deduplicate_ranked,
    normalize_record,
    rank_record,
    stable_sort_key,
)
from evaluation.registry import check_code_novelty
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
SOLVER_RUNTIME_PACKAGES = (
    "numpy",
    "ortools",
    "qldpc",
    "scipy",
    "highspy",
)
_TRUSTED_STAGE1_OUTCOME = "_trusted_stage1_outcome"


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
                    # A live search writer may be between writes when this
                    # reader reaches EOF. Ignore only that unterminated final
                    # fragment; malformed completed lines still fail closed.
                    if not line.endswith(("\n", "\r")):
                        continue
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
) -> str | None:
    """Replay a formal Stage 1 audit before using it as a priority lane."""

    attempt = record.get("audit_attempt")
    if not isinstance(attempt, Mapping) or attempt.get("schema_version") != 2:
        return None
    outcome = classify_evaluation(record)
    if outcome is AuditOutcome.THRESHOLD_REJECTED:
        return "REJECTED"
    if outcome is not AuditOutcome.EXACT:
        return None
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
    return "THRESHOLD_PROVEN" if gate["passed"] is True else "REJECTED"


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


def rank_candidate_files(
    paths: Iterable[Path],
) -> tuple[list[dict[str, Any]], dict[str, int]]:
    """Load, proof-rank, and canonical-deduplicate all candidate files."""

    records, sources = read_candidate_jsonl(paths)
    prepared: list[dict[str, Any]] = []
    prepared_sources: list[str] = []
    ineligible_records = 0
    malformed_records = 0
    for record, source in zip(records, sources, strict=True):
        try:
            normalized = normalize_record(record)
            n = normalized.get("n")
            k = normalized.get("k")
            if (
                isinstance(n, bool)
                or not isinstance(n, int)
                or isinstance(k, bool)
                or not isinstance(k, int)
            ):
                raise TypeError("candidate n and k must be integers")
            if n <= 0 or k <= 0:
                ineligible_records += 1
                continue
            required_distance = minimum_winning_distance(n, k)
        except (KeyError, TypeError, ValueError, OverflowError):
            malformed_records += 1
            continue

        # Stage 1 search rows intentionally contain distance estimates rather
        # than a proof threshold.  Derive the threshold from the authoritative
        # final-gate rules here, and overwrite any stale caller-supplied value.
        # A top-level value wins for flat, nested-claim, and wrapped-artifact
        # records when proof_triage normalizes the row.
        enriched = dict(record)
        enriched.pop(_TRUSTED_STAGE1_OUTCOME, None)
        enriched["required_distance"] = required_distance
        try:
            trusted_outcome = _trusted_stage1_outcome(
                enriched,
                required_distance,
            )
        except AuditStateError:
            malformed_records += 1
            continue
        if trusted_outcome is not None:
            enriched[_TRUSTED_STAGE1_OUTCOME] = trusted_outcome
        prepared.append(enriched)
        prepared_sources.append(source)

    ranked = deduplicate_ranked(prepared, prepared_sources)
    ranked, trusted_counts = _promote_trusted_stage1_rows(
        ranked,
        prepared,
        prepared_sources,
    )

    def selection_key(row: Mapping[str, Any]) -> tuple[Any, ...]:
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
        # stable_sort_key's final two fields are deterministic identities.
        # Insert this advisory upper-bound tie-break immediately before them;
        # it never outranks actual lower-bound proof progress.
        return (*proof_key[:-2], -estimated_fom, *proof_key[-2:])

    ranked.sort(key=selection_key)
    eligible = [
        row for row in ranked
        if row["proof_score"].get("rejected") is not True
        and row["proof_score"].get("status") != "REJECTED"
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


def _package_version(name: str) -> str:
    try:
        return importlib.metadata.version(name)
    except importlib.metadata.PackageNotFoundError:
        return "unavailable"


def solver_runtime_fingerprint() -> dict[str, Any]:
    """Return the runtime identity that makes solver caches reproducible."""

    return {
        "python": platform.python_version(),
        "packages": {
            name: _package_version(name)
            for name in SOLVER_RUNTIME_PACKAGES
        },
    }


def certificate_source_fingerprint() -> str:
    """Bind certificate caches to all code and registry inputs they execute."""

    paths = {
        Path(__file__).resolve(),
        PROJECT / "scripts" / "audit_direction_pool.py",
        PROJECT / "scripts" / "finalize_challenge.py",
        PROJECT / "tests" / "verify_known_answer_gate.py",
        PROJECT / "results" / "known_code_registry.json",
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


def canonicalize_for_audit(
    ranked: Mapping[str, Any],
    *,
    code_builder: Callable[..., Any] | None = None,
    novelty_checker: Callable[..., dict[str, Any]] | None = None,
) -> dict[str, Any]:
    """Bind one selected historical row to the real registry digest.

    Older expanded-search rows did not compute canonical novelty unless their
    short MILP screen finished. Proof triage uses an exact-claim hash as a safe
    fallback, but before expensive XOR work we reconstruct the BB code and
    replace that fallback with the registry's canonical graph digest.
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
    existing_novelty = updated.get("novelty")
    has_checked_novelty = (
        isinstance(existing_novelty, Mapping)
        and existing_novelty.get("checked") is True
        and existing_novelty.get("canonical_digest")
    )
    if has_checked_novelty:
        actual_digest = str(existing_novelty["canonical_digest"])
    else:
        candidate = _construction_candidate(
            updated, str(identity["canonical_digest"]),
        )
        if candidate.get("C_terms") or candidate.get("D_terms"):
            raise ValueError("XOR audit canonicalization supports CSS BB only")
        code = code_builder(
            int(candidate["ell"]),
            int(candidate["m"]),
            candidate["A_terms"],
            candidate["B_terms"],
        )
        existing_novelty = novelty_checker(code, code_type="css")
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


def select_audit_candidates(
    ranked: list[dict[str, Any]],
    top: int,
    *,
    canonicalizer: Callable[[Mapping[str, Any]], dict[str, Any]] | None = None,
) -> tuple[list[dict[str, Any]], dict[str, int]]:
    """Fill the audit queue with unique, registry-novel CSS candidates."""

    if top < 0:
        raise ValueError("top must be non-negative")
    canonicalizer = (
        canonicalize_for_audit if canonicalizer is None else canonicalizer
    )
    selected: list[dict[str, Any]] = []
    seen_digests: set[str] = set()
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
            row["proof_score"].get("rejected") is not True
            and row["proof_score"].get("status") != "REJECTED"
            for row in ranked
        )
        stats["unscanned_eligible_candidates"] = unscanned
        stats["selection_exhausted"] = unscanned == 0
        return selected, stats

    for index, row in enumerate(ranked):
        if (
            row["proof_score"].get("rejected") is True
            or row["proof_score"].get("status") == "REJECTED"
        ):
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
                remaining["proof_score"].get("rejected") is not True
                and remaining["proof_score"].get("status") != "REJECTED"
                for remaining in ranked[index + 1 :]
            )
            stats["unscanned_eligible_candidates"] = unscanned
            stats["selection_exhausted"] = unscanned == 0
            break
    return selected, stats


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


def audit_selected_candidates(
    selected: list[dict[str, Any]],
    config: AuditConfig,
    *,
    candidate_workers: int,
) -> list[dict[str, Any]]:
    """Audit selected candidates and isolate per-candidate failures."""

    if candidate_workers == 1:
        results = []
        for candidate in selected:
            try:
                results.append(audit_candidate(candidate, config))
            except Exception as exc:
                identity = candidate_identity(candidate)
                results.append({
                    "canonical_digest": identity["canonical_digest"],
                    "status": "ERROR",
                    "error": f"{type(exc).__name__}: {exc}",
                })
        return results

    results = []
    with ProcessPoolExecutor(max_workers=candidate_workers) as executor:
        futures = {
            executor.submit(_audit_worker, (candidate, config)):
            str(candidate["triage_identity"]["canonical_digest"])
            for candidate in selected
        }
        for future in as_completed(futures):
            digest = futures[future]
            try:
                results.append(future.result())
            except Exception as exc:
                results.append({
                    "canonical_digest": digest,
                    "status": "ERROR",
                    "error": f"{type(exc).__name__}: {exc}",
                })
    order = {
        str(candidate["triage_identity"]["canonical_digest"]): index
        for index, candidate in enumerate(selected)
    }
    return sorted(results, key=lambda item: order[item["canonical_digest"]])


def _certificate_phase_item(
    item: Mapping[str, Any],
) -> tuple[dict[str, Any], str]:
    """Normalize a ranked row or Stage-3 artifact for exact certification."""

    nested = item.get("candidate")
    gate = item.get("gate")
    if gate == STAGE3_GATE:
        raw_candidate = claim_from_threshold_artifact(item)
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


def _certificate_phase_failure(exc: Exception) -> dict[str, Any]:
    return {
        "attempted": True,
        "certificate_passed": False,
        "verification_passed": False,
        "error": f"{type(exc).__name__}: {exc}",
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
    if certificate_workers == 1:
        for candidate, digest in prepared:
            try:
                results[digest] = certifier(candidate, digest, config)
            except Exception as exc:
                results[digest] = _certificate_phase_failure(exc)
        return results

    with ProcessPoolExecutor(max_workers=certificate_workers) as executor:
        futures = {
            executor.submit(
                _certificate_worker,
                (candidate, digest, config, certifier),
            ): digest
            for candidate, digest in prepared
        }
        completed: dict[str, dict[str, Any]] = {}
        for future in as_completed(futures):
            digest = futures[future]
            try:
                returned_digest, result = future.result()
                if returned_digest != digest:
                    raise ValueError("certificate worker returned wrong digest")
                completed[digest] = result
            except Exception as exc:
                completed[digest] = _certificate_phase_failure(exc)
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
        if updated.get("status") == "THRESHOLD_PROVEN":
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
    ):
        value = getattr(args, name)
        if not math.isfinite(value) or value <= 0:
            parser.error(f"{name.replace('_', '-')} must be positive")
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
        ranked, counts = rank_candidate_files(args.inputs)
    except (OSError, TypeError, ValueError) as exc:
        parser.error(str(exc))

    selected, selection_counts = select_audit_candidates(
        ranked, args.top,
    )
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
    atomic_write_json(args.summary_output, summary)
    print(json.dumps(summary, indent=2))
    return 0 if not (
        any(result["status"] == "ERROR" for result in results)
        or summary["certificate_operational_errors"]
    ) else 2


if __name__ == "__main__":
    raise SystemExit(main())
