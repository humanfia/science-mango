#!/usr/bin/env python3
"""Run resumable Stage 3 logical-direction audits over a Stage 2 pool."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import sys
import time
import uuid
from collections import deque
from pathlib import Path
from typing import Any, Callable, Iterable, Mapping

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from scripts.screen_frontier_candidate import (
    screen_candidate,
)
from evaluation.process_hard_wall import (
    DEFAULT_TERMINATION_GRACE_S,
    IsolatedCallOutcome,
    IsolatedCallStartupTimeout,
    poll_isolated_call,
    positive_wall_timeout,
    start_isolated_call,
)


PROJECT = Path(__file__).resolve().parent.parent
CONSTRUCTION_FIELDS = (
    "source", "trial", "ansatz", "ell", "m", "A_terms", "B_terms",
    "C_terms", "D_terms", "n", "k", "required_distance",
    "max_row_weight", "max_qubit_degree", "tanner_components", "novelty",
    "canonical_digest",
)


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
            descriptor = os.open(path.parent, os.O_RDONLY)
        except OSError:
            return
        try:
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
    finally:
        temporary.unlink(missing_ok=True)


def atomic_write_json(path: Path, value: Mapping[str, Any]) -> None:
    _atomic_write_text(path, json.dumps(dict(value), indent=2) + "\n")


def atomic_write_jsonl(
    path: Path, rows: Iterable[Mapping[str, Any]],
) -> None:
    _atomic_write_text(
        path,
        "".join(json.dumps(dict(row), sort_keys=True) + "\n" for row in rows),
    )


def read_ranked_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
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
                raise ValueError(f"{path}:{line_number}: row must be an object")
            rows.append(value)
    return rows


def canonical_digest(row: Mapping[str, Any]) -> str:
    identity = row.get("triage_identity")
    digest = (
        identity.get("canonical_digest")
        if isinstance(identity, Mapping) else row.get("canonical_digest")
    )
    if not isinstance(digest, str) or not digest:
        raise ValueError("Stage 2 row lacks a canonical digest")
    return digest


def candidate_from_stage2(row: Mapping[str, Any]) -> dict[str, Any]:
    audit = row.get("campaign_audit")
    if not isinstance(audit, Mapping) or audit.get("status") != "UNRESOLVED":
        raise ValueError("Stage 3 accepts only campaign_audit.status=UNRESOLVED")
    digest = canonical_digest(row)
    candidate = {
        name: row[name]
        for name in CONSTRUCTION_FIELDS
        if name in row and row[name] is not None
    }
    candidate["canonical_digest"] = digest
    missing = [
        name for name in (
            "ell", "m", "A_terms", "B_terms", "n", "k",
            "required_distance",
        )
        if name not in candidate
    ]
    if missing:
        raise ValueError("Stage 2 row lacks: " + ", ".join(missing))
    if candidate.get("C_terms") or candidate.get("D_terms"):
        raise ValueError("Stage 3 pool currently supports CSS candidates only")
    return candidate


def select_unresolved(
    rows: list[dict[str, Any]], top: int = 0,
) -> tuple[list[tuple[str, dict[str, Any]]], dict[str, int]]:
    selected: list[tuple[str, dict[str, Any]]] = []
    seen: set[str] = set()
    malformed = duplicates = unselected = 0
    for row in rows:
        audit = row.get("campaign_audit")
        if not isinstance(audit, Mapping) or audit.get("status") != "UNRESOLVED":
            continue
        try:
            digest = canonical_digest(row)
            candidate = candidate_from_stage2(row)
        except (KeyError, TypeError, ValueError):
            malformed += 1
            continue
        if digest in seen:
            duplicates += 1
            continue
        seen.add(digest)
        if top > 0 and len(selected) >= top:
            unselected += 1
        else:
            selected.append((digest, candidate))
    return selected, {
        "input_rows": len(rows),
        "selected_candidates": len(selected),
        "malformed_unresolved_rows": malformed,
        "duplicate_digests_skipped": duplicates,
        "unselected_unresolved_candidates": unselected,
        "selection_exhausted": unselected == 0,
    }


def validate_worker_budget(
    candidate_workers: int,
    direction_workers: int,
    max_total_workers: int,
) -> None:
    if candidate_workers < 1:
        raise ValueError("candidate_workers must be positive")
    if not 1 <= direction_workers <= 8:
        raise ValueError("direction_workers must be between 1 and 8")
    if max_total_workers < 1:
        raise ValueError("max_total_workers must be positive")
    requested = candidate_workers * direction_workers
    if requested > max_total_workers:
        raise ValueError(
            "candidate_workers * direction_workers exceeds max_total_workers "
            f"({candidate_workers} * {direction_workers} = {requested} > "
            f"{max_total_workers})",
        )


def safe_digest(digest: str) -> str:
    return hashlib.sha256(digest.encode()).hexdigest()


def direction_state_path(state_dir: Path, digest: str) -> Path:
    return state_dir / "directions" / f"{safe_digest(digest)}.json"


def _screen_one(
    digest: str,
    candidate: dict[str, Any],
    state_dir: Path,
    *,
    timeout: float,
    direction_workers: int,
    threshold_only: bool,
    resume: bool,
    direction_hard_timeout: float | None = None,
    candidate_hard_timeout: float | None = None,
    termination_grace: float = DEFAULT_TERMINATION_GRACE_S,
    screener: Callable[..., dict[str, Any]] = screen_candidate,
) -> dict[str, Any]:
    path = direction_state_path(state_dir, digest)
    try:
        artifact = screener(
            candidate,
            output=path,
            timeout=timeout,
            workers=direction_workers,
            threshold_only=threshold_only,
            resume=resume,
            hard_timeout=direction_hard_timeout,
            candidate_timeout=candidate_hard_timeout,
            termination_grace=termination_grace,
        )
        return {
            "canonical_digest": digest,
            "status": artifact["status"],
            "artifact_path": str(path),
            "completed_directions": artifact["completed_directions"],
            "expected_directions": artifact["expected_directions"],
        }
    except Exception as exc:
        return {
            "canonical_digest": digest,
            "status": "ERROR",
            "artifact_path": str(path),
            "error": f"{type(exc).__name__}: {exc}",
        }


def _screen_worker(payload: tuple[Any, ...]) -> dict[str, Any]:
    (
        digest,
        candidate,
        state_dir,
        timeout,
        workers,
        threshold_only,
        resume,
        direction_hard_timeout,
        candidate_hard_timeout,
        termination_grace,
    ) = payload
    return _screen_one(
        digest,
        candidate,
        state_dir,
        timeout=timeout,
        direction_workers=workers,
        threshold_only=threshold_only,
        resume=resume,
        direction_hard_timeout=direction_hard_timeout,
        candidate_hard_timeout=candidate_hard_timeout,
        termination_grace=termination_grace,
    )


def _candidate_wall_timeout(
    candidate: Mapping[str, Any],
    *,
    timeout: float,
    direction_workers: int,
    direction_hard_timeout: float | None,
    candidate_hard_timeout: float | None,
) -> float:
    """Bound setup, replay, every direction, and worker cleanup from submit."""

    k = candidate.get("k")
    if isinstance(k, bool) or not isinstance(k, int) or k <= 0:
        raise ValueError("Stage 3 candidate k must be a positive integer")
    if candidate_hard_timeout is not None:
        return positive_wall_timeout(
            candidate_hard_timeout,
            "candidate hard timeout",
        )
    per_direction = positive_wall_timeout(
        timeout + 5.0
        if direction_hard_timeout is None
        else direction_hard_timeout,
        "direction hard timeout",
    )
    expected = 2 * k
    return positive_wall_timeout(
        math.ceil(expected / direction_workers) * per_direction + 5.0,
        "candidate hard timeout",
    )


def _load_partial_artifact(path: Path) -> dict[str, Any] | None:
    try:
        value = json.loads(path.read_text())
    except (FileNotFoundError, OSError, UnicodeError, json.JSONDecodeError):
        return None
    return dict(value) if isinstance(value, Mapping) else None


def _hard_wall_result(
    digest: str,
    candidate: Mapping[str, Any],
    path: Path,
    outcome: IsolatedCallOutcome,
    *,
    timeout_s: float,
) -> dict[str, Any]:
    """Recover durable progress after killing exactly one candidate session."""

    artifact = _load_partial_artifact(path)
    expected = 2 * int(candidate["k"])
    completed = 0
    if artifact is not None:
        raw_completed = artifact.get("completed_directions", 0)
        if (
            isinstance(raw_completed, int)
            and not isinstance(raw_completed, bool)
            and 0 <= raw_completed <= expected
        ):
            completed = raw_completed
    result = {
        "canonical_digest": digest,
        # A killed worker never promotes terminal mathematics in the same
        # attempt.  A subsequent resume can validate the durable directions
        # and return a terminal artifact without recomputing them.
        "status": "UNRESOLVED",
        "artifact_path": str(path),
        "completed_directions": completed,
        "expected_directions": expected,
        "hard_wall": {
            "timed_out": True,
            "candidate_timeout_s": timeout_s,
            "completed_directions_retained": completed,
            **dict(outcome.hard_wall or {}),
        },
    }
    if outcome.error:
        result["hard_wall"]["error"] = outcome.error
    return result


def screen_selected_candidates(
    selected: list[tuple[str, dict[str, Any]]],
    state_dir: Path,
    *,
    timeout: float,
    candidate_workers: int,
    direction_workers: int,
    threshold_only: bool,
    resume: bool,
    direction_hard_timeout: float | None = None,
    candidate_hard_timeout: float | None = None,
    termination_grace: float = DEFAULT_TERMINATION_GRACE_S,
    screener: Callable[..., dict[str, Any]] = screen_candidate,
) -> list[dict[str, Any]]:
    if candidate_workers < 1:
        raise ValueError("candidate_workers must be positive")
    grace = positive_wall_timeout(
        termination_grace,
        "hard-wall termination grace",
    )
    queued = deque(selected)
    results: dict[str, dict[str, Any]] = {}
    active: dict[
        str,
        tuple[Any, dict[str, Any], Path, float],
    ] = {}

    def submit_available() -> None:
        while queued and len(active) < candidate_workers:
            digest, candidate = queued.popleft()
            path = direction_state_path(state_dir, digest)
            try:
                wall_timeout = _candidate_wall_timeout(
                    candidate,
                    timeout=timeout,
                    direction_workers=direction_workers,
                    direction_hard_timeout=direction_hard_timeout,
                    candidate_hard_timeout=candidate_hard_timeout,
                )
                handle = start_isolated_call(
                    _screen_one,
                    args=(digest, candidate, state_dir),
                    kwargs={
                        "timeout": timeout,
                        "direction_workers": direction_workers,
                        "threshold_only": threshold_only,
                        "resume": resume,
                        "direction_hard_timeout": direction_hard_timeout,
                        "candidate_hard_timeout": candidate_hard_timeout,
                        "termination_grace": termination_grace,
                        "screener": screener,
                    },
                    timeout_s=wall_timeout,
                    termination_grace_s=grace,
                )
            except IsolatedCallStartupTimeout as exc:
                results[digest] = _hard_wall_result(
                    digest,
                    candidate,
                    path,
                    IsolatedCallOutcome(
                        status="timeout",
                        error=str(exc),
                        hard_wall=dict(exc.hard_wall),
                    ),
                    timeout_s=wall_timeout,
                )
                continue
            except Exception as exc:
                results[digest] = {
                    "canonical_digest": digest,
                    "status": "ERROR",
                    "artifact_path": str(path),
                    "error": f"{type(exc).__name__}: {exc}",
                }
                continue
            active[digest] = (handle, candidate, path, wall_timeout)

    submit_available()
    while active:
        made_progress = False
        for digest, (handle, candidate, path, wall_timeout) in list(
            active.items()
        ):
            try:
                outcome = poll_isolated_call(handle)
            except Exception as exc:
                made_progress = True
                del active[digest]
                if handle.remaining() <= 0:
                    results[digest] = _hard_wall_result(
                        digest,
                        candidate,
                        path,
                        IsolatedCallOutcome(
                            status="timeout",
                            error=(
                                "candidate hard-wall cleanup failed: "
                                f"{type(exc).__name__}: {exc}"
                            ),
                            hard_wall={"cleanup_failed": True},
                        ),
                        timeout_s=wall_timeout,
                    )
                else:
                    results[digest] = {
                        "canonical_digest": digest,
                        "status": "ERROR",
                        "artifact_path": str(path),
                        "error": (
                            "isolated Stage 3 worker poll failed: "
                            f"{type(exc).__name__}: {exc}"
                        ),
                    }
                continue
            if outcome is None:
                continue
            made_progress = True
            del active[digest]
            if outcome.status == "completed" and isinstance(
                outcome.value, Mapping
            ):
                result = dict(outcome.value)
                if outcome.hard_wall is not None:
                    result["hard_wall_cleanup"] = dict(outcome.hard_wall)
            elif outcome.status == "timeout":
                result = _hard_wall_result(
                    digest,
                    candidate,
                    path,
                    outcome,
                    timeout_s=wall_timeout,
                )
            else:
                result = {
                    "canonical_digest": digest,
                    "status": "ERROR",
                    "artifact_path": str(path),
                    "error": outcome.error or "isolated Stage 3 worker failed",
                }
            if result.get("canonical_digest") != digest:
                result = {
                    "canonical_digest": digest,
                    "status": "ERROR",
                    "artifact_path": str(path),
                    "error": "isolated Stage 3 worker returned the wrong digest",
                }
            results[digest] = result
        submit_available()
        if active and not made_progress:
            nearest = min(handle.deadline for handle, *_ in active.values())
            time.sleep(min(0.01, max(0.0, nearest - time.monotonic())))
    return [results[digest] for digest, _ in selected]


def annotate_rows(
    rows: list[dict[str, Any]],
    selected: list[tuple[str, dict[str, Any]]],
    results: Iterable[Mapping[str, Any]],
) -> list[dict[str, Any]]:
    selected_digests = {digest for digest, _ in selected}
    by_digest = {
        str(result["canonical_digest"]): dict(result) for result in results
    }
    annotated = []
    remaining_selected = set(selected_digests)
    for row in rows:
        updated = dict(row)
        try:
            digest = canonical_digest(row)
        except ValueError:
            annotated.append(updated)
            continue
        is_selected = digest in remaining_selected
        updated["campaign_direction_selected"] = is_selected
        if is_selected:
            remaining_selected.remove(digest)
        if is_selected and digest in by_digest:
            updated["campaign_direction_audit"] = by_digest[digest]
        else:
            updated.pop("campaign_direction_audit", None)
        annotated.append(updated)
    return annotated


def threshold_artifacts(
    results: Iterable[Mapping[str, Any]],
) -> tuple[list[dict[str, Any]], dict[str, str]]:
    """Load replay-validated threshold or exact artifacts for Stage 4."""

    from scripts.audit_candidate_pool import (
        CERTIFIABLE_PROOF_STATUSES,
        claim_from_certifiable_stage3_artifact,
    )

    artifacts = []
    failures: dict[str, str] = {}
    for result in results:
        status = result.get("status")
        if status not in CERTIFIABLE_PROOF_STATUSES:
            continue
        digest = str(result["canonical_digest"])
        try:
            value = json.loads(Path(str(result["artifact_path"])).read_text())
            if not isinstance(value, dict):
                raise ValueError("Stage 3 artifact must be an object")
            if value.get("status") != status:
                raise ValueError(
                    "Stage 3 result and artifact statuses do not match"
                )
            claim_from_certifiable_stage3_artifact(value)
            artifacts.append(value)
        except Exception as exc:
            failures[digest] = (
                f"artifact validation failed: {type(exc).__name__}: {exc}"
            )
    return artifacts, failures


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("ranked_input", type=Path)
    parser.add_argument("--state-dir", type=Path, required=True)
    parser.add_argument("--ranked-output", type=Path, required=True)
    parser.add_argument("--summary-output", type=Path, required=True)
    parser.add_argument("--stage4-manifest", type=Path)
    parser.add_argument("--top", type=int, default=0)
    parser.add_argument("--timeout", type=float, default=300)
    parser.add_argument("--candidate-workers", type=int, default=1)
    parser.add_argument("--direction-workers", type=int, default=4)
    parser.add_argument("--max-total-workers", type=int, default=8)
    parser.add_argument("--exact", action="store_true")
    parser.add_argument(
        "--resume", action=argparse.BooleanOptionalAction, default=True,
    )
    parser.add_argument(
        "--certify", action=argparse.BooleanOptionalAction, default=False,
        help="run the separate certificate pool after all Stage 3 work",
    )
    parser.add_argument("--certificate-workers", type=int, default=1)
    parser.add_argument("--certificate-solver-workers", type=int, default=1)
    parser.add_argument(
        "--known-answer-artifact", type=Path,
        default=PROJECT / "results" / "known_answer_gate.json",
    )
    parser.add_argument("--certificate-timeout-per-logical", type=float, default=300)
    parser.add_argument("--certificate-total-timeout", type=float, default=7200)
    parser.add_argument("--verification-timeout-per-logical", type=float, default=300)
    parser.add_argument("--verification-total-timeout", type=float, default=7200)
    parser.add_argument("--direction-hard-timeout", type=float)
    parser.add_argument("--candidate-hard-timeout", type=float)
    parser.add_argument("--certificate-hard-timeout", type=float)
    parser.add_argument(
        "--hard-wall-termination-grace",
        type=float,
        default=DEFAULT_TERMINATION_GRACE_S,
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    if (
        args.top < 0
        or not math.isfinite(args.timeout)
        or args.timeout <= 0
    ):
        parser.error("top must be nonnegative and timeout must be positive")
    for name in (
        "certificate_timeout_per_logical",
        "certificate_total_timeout",
        "verification_timeout_per_logical",
        "verification_total_timeout",
        "hard_wall_termination_grace",
    ):
        value = getattr(args, name)
        if not math.isfinite(value) or value <= 0:
            parser.error(f"{name.replace('_', '-')} must be positive")
    for name in (
        "direction_hard_timeout",
        "candidate_hard_timeout",
        "certificate_hard_timeout",
    ):
        value = getattr(args, name)
        if value is not None and (not math.isfinite(value) or value <= 0):
            parser.error(f"{name.replace('_', '-')} must be positive")
    try:
        validate_worker_budget(
            args.candidate_workers,
            args.direction_workers,
            args.max_total_workers,
        )
        if args.certify:
            validate_worker_budget(
                args.certificate_workers,
                args.certificate_solver_workers,
                args.max_total_workers,
            )
        rows = read_ranked_jsonl(args.ranked_input)
        selected, counts = select_unresolved(rows, args.top)
    except (OSError, TypeError, ValueError) as exc:
        parser.error(str(exc))
    results = screen_selected_candidates(
        selected,
        args.state_dir,
        timeout=args.timeout,
        candidate_workers=args.candidate_workers,
        direction_workers=args.direction_workers,
        threshold_only=not args.exact,
        resume=args.resume,
        direction_hard_timeout=args.direction_hard_timeout,
        candidate_hard_timeout=args.candidate_hard_timeout,
        termination_grace=args.hard_wall_termination_grace,
    )
    atomic_write_jsonl(
        args.ranked_output,
        annotate_rows(rows, selected, results),
    )
    artifacts, artifact_failures = threshold_artifacts(results)
    if artifact_failures:
        results = [
            {
                **result,
                "status": "ERROR",
                "error": artifact_failures[str(result["canonical_digest"])],
            }
            if str(result["canonical_digest"]) in artifact_failures
            else result
            for result in results
        ]
    if args.stage4_manifest is not None:
        atomic_write_jsonl(args.stage4_manifest, artifacts)
    if args.certify and artifacts:
        from scripts.audit_candidate_pool import (
            AuditConfig,
            certify_selected_candidates,
            merge_certification_results,
        )
        config = AuditConfig(
            state_dir=args.state_dir,
            resume=args.resume,
            certify=True,
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
            certificate_hard_timeout_s=args.certificate_hard_timeout,
            hard_wall_termination_grace_s=(
                args.hard_wall_termination_grace
            ),
        )
        certifications = certify_selected_candidates(
            artifacts,
            config,
            certificate_workers=args.certificate_workers,
            max_total_workers=args.max_total_workers,
        )
        results = merge_certification_results(
            results, certifications, certify=True,
        )
    annotated = annotate_rows(rows, selected, results)
    atomic_write_jsonl(args.ranked_output, annotated)
    status_counts: dict[str, int] = {}
    for result in results:
        status = str(result["status"])
        status_counts[status] = status_counts.get(status, 0) + 1
    summary = {
        "schema_version": 1,
        "gate": "qldpc-direction-candidate-pool",
        **counts,
        "threshold_only": not args.exact,
        "hard_wall_budget": {
            "direction_timeout_s": (
                args.direction_hard_timeout
                if args.direction_hard_timeout is not None
                else args.timeout + 5.0
            ),
            "candidate_timeout_s": args.candidate_hard_timeout,
            "certificate_timeout_s": args.certificate_hard_timeout,
            "termination_grace_s": args.hard_wall_termination_grace,
        },
        "worker_budget": {
            "phases_overlap": False,
            "stage3": {
                "candidate_workers": args.candidate_workers,
                "direction_workers": args.direction_workers,
                "solver_workers_per_direction": 1,
                "configured_solver_workers": (
                    args.candidate_workers * args.direction_workers
                ),
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
            },
            "max_total_workers": args.max_total_workers,
        },
        "status_counts": status_counts,
        "certify": args.certify,
        "stage4_candidates": len(artifacts),
        "certified_wins": sum(
            result.get("certificate", {}).get("certificate_passed") is True
            and result.get("certificate", {}).get("verification_passed") is True
            for result in results
        ),
        "operational_errors": (
            counts["malformed_unresolved_rows"]
            + status_counts.get("ERROR", 0)
            + sum(
                bool(result.get("certificate", {}).get("error"))
                for result in results
            )
        ),
        "stage4_manifest": (
            None if args.stage4_manifest is None else str(args.stage4_manifest)
        ),
        "ranked_output": str(args.ranked_output),
        "state_dir": str(args.state_dir),
        "results": results,
    }
    atomic_write_json(args.summary_output, summary)
    print(json.dumps(summary, indent=2))
    return 2 if summary["operational_errors"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
