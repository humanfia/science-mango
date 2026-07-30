#!/usr/bin/env python3
"""Run the mandatory, fail-closed terminal gate on proposed challenge claims.

Input may be a JSON object, a JSON list, or JSONL.  The IBM/known-answer replay
is a global prerequisite, while certificates are independently replayed.  A
well-formed batch completes successfully when it records a WIN, NO_WIN, or
INCOMPLETE outcome; malformed input and invalid controls still exit nonzero.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import sys
import time
import uuid
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Mapping

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation.certificate_dispatch import (
    SUPPORTED_CERTIFICATE_TYPES,
    verify_certificate,
)
from evaluation.failure_disposition import (
    INCOMPLETE,
    classify_build_failure,
    contradiction_disposition,
    incomplete_result_disposition,
    terminal_candidate_rejection,
    validate_failure_disposition,
)
from evaluation.known_answer_integrity import (
    _strict_wall_timeout,
    check_known_answer_integrity,
)
from evaluation.process_hard_wall import (
    DEFAULT_TERMINATION_GRACE_S,
    run_isolated_call,
)


SCHEDULER_SCHEMA_VERSION = 1
SCHEDULER_GATE = "qldpc-strict-replay-round-robin"
SCHEDULER_FILENAME = "strict-replay-scheduler.json"
KNOWN_ANSWER_OUTER_CUSHION_S = 5.0
TERMINAL_NEGATIVE_REPLAY_CHECKS = frozenset(
    {
        "schema",
        "certificate_sha256",
        "known_answer_sha256",
        "matrix_sha256",
        "direction_count",
        "stored_direction_evidence",
        "milp_rerun",
        "distance_recomputed",
        "final_gate",
        "certificate_passed_flag",
    }
)


def load_rows(path: Path) -> list[dict[str, Any]]:
    text = path.read_text()
    try:
        value = json.loads(text)
    except json.JSONDecodeError:
        value = [json.loads(line) for line in text.splitlines() if line.strip()]
    if isinstance(value, dict):
        value = [value]
    if not isinstance(value, list) or not all(isinstance(row, dict) for row in value):
        raise ValueError("input must be a JSON object, list of objects, or JSONL")
    return value


def parse_args() -> argparse.Namespace:
    project = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("claims", type=Path, help="Candidate claim JSON/JSONL")
    parser.add_argument(
        "--known-answer-artifact",
        type=Path,
        default=project / "results" / "known_answer_gate.json",
    )
    parser.add_argument(
        "--known-answer-trust",
        type=Path,
        default=project / "results" / "known_answer_trust.json",
    )
    parser.add_argument(
        "--known-answer-timeout-per-logical",
        type=int,
        default=300,
    )
    parser.add_argument(
        "--known-answer-total-timeout",
        type=int,
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
        help="Cumulative wall budget for strict replay of the input batch.",
    )
    parser.add_argument(
        "--verification-solver-workers",
        type=int,
        default=1,
    )
    parser.add_argument(
        "--verification-state-dir",
        type=Path,
        help="Optional directory for bound per-certificate replay checkpoints.",
    )
    parser.add_argument(
        "--resume",
        action=argparse.BooleanOptionalAction,
        default=True,
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=project / "results" / "final_gate.json",
    )
    return parser.parse_args()


def _validate_verification_budget(args: argparse.Namespace) -> None:
    for name in (
        "verification_timeout_per_logical",
        "verification_total_timeout",
    ):
        value = getattr(args, name)
        if (
            isinstance(value, bool)
            or not math.isfinite(float(value))
            or float(value) <= 0
        ):
            raise ValueError(f"{name} must be positive and finite")
    workers = args.verification_solver_workers
    if isinstance(workers, bool) or not isinstance(workers, int):
        raise ValueError("verification_solver_workers must be an integer")
    if not 1 <= workers <= 8:
        raise ValueError("verification_solver_workers must be between 1 and 8")


def _payload_sha256(value: dict[str, Any]) -> str:
    encoded = json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def _atomic_write_json(path: Path, value: Mapping[str, Any]) -> None:
    """Durably replace scheduler state without exposing a partial JSON file."""

    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(
        f".{path.name}.{os.getpid()}.{uuid.uuid4().hex}.tmp",
    )
    try:
        with temporary.open("w", encoding="utf-8") as stream:
            json.dump(
                dict(value),
                stream,
                sort_keys=True,
                separators=(",", ":"),
                ensure_ascii=False,
                allow_nan=False,
            )
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
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
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass


def _scheduler_binding(payloads: list[str]) -> str:
    return _payload_sha256(
        {
            "schema_version": SCHEDULER_SCHEMA_VERSION,
            "certificate_payload_sha256": sorted(payloads),
        }
    )


def _load_scheduler(
    path: Path,
    payloads: list[str],
) -> dict[str, Any]:
    """Load a reorder-safe cursor, resetting only for a different batch."""

    binding = _scheduler_binding(payloads)
    expected_payloads = sorted(payloads)
    try:
        value = json.loads(path.read_text())
    except FileNotFoundError:
        value = None
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise ValueError(f"strict replay scheduler is unavailable: {exc}") from exc
    if not isinstance(value, Mapping) or value.get("binding_sha256") != binding:
        scheduler = {
            "schema_version": SCHEDULER_SCHEMA_VERSION,
            "gate": SCHEDULER_GATE,
            "binding_sha256": binding,
            "certificate_payload_sha256": expected_payloads,
            "next_payload_sha256": payloads[0],
            "scheduled_attempts": 0,
        }
        _atomic_write_json(path, scheduler)
        return scheduler
    next_payload = value.get("next_payload_sha256")
    attempts = value.get("scheduled_attempts")
    if (
        value.get("schema_version") != SCHEDULER_SCHEMA_VERSION
        or value.get("gate") != SCHEDULER_GATE
        or value.get("certificate_payload_sha256") != expected_payloads
        or not isinstance(next_payload, str)
        or next_payload not in payloads
        or isinstance(attempts, bool)
        or not isinstance(attempts, int)
        or attempts < 0
    ):
        raise ValueError("strict replay scheduler is malformed")
    return dict(value)


def _advance_scheduler(
    path: Path,
    scheduler: dict[str, Any],
    *,
    payloads: list[str],
    current_payload: str,
) -> None:
    """Advance before solver entry so a crash cannot starve peer certificates."""

    current_index = payloads.index(current_payload)
    scheduler["next_payload_sha256"] = payloads[
        (current_index + 1) % len(payloads)
    ]
    scheduler["last_started_payload_sha256"] = current_payload
    scheduler["scheduled_attempts"] = int(
        scheduler["scheduled_attempts"]
    ) + 1
    scheduler["updated_at"] = datetime.now(timezone.utc).isoformat()
    _atomic_write_json(path, scheduler)


def _incomplete_result(
    failure: str,
    *,
    domain: str = "runtime",
    code: str = "STRICT_REPLAY_INCOMPLETE",
) -> dict[str, Any]:
    return {
        "passed": False,
        "accepted": False,
        "replay_complete": False,
        "failures": [failure],
        "failure_disposition": incomplete_result_disposition(
            domain=domain,
            code=code,
        ),
    }


def _verification_disposition(
    certificate: dict[str, Any],
    verification: dict[str, Any],
) -> str:
    """Normalize replay failure semantics before the batch outcome is counted."""

    if verification.get("passed") is True:
        return "ACCEPTED"
    if verification.get("replay_complete") is not True:
        try:
            failure = validate_failure_disposition(
                verification.get("failure_disposition"),
            )
        except ValueError:
            failure = incomplete_result_disposition(
                domain="solver",
                code="STRICT_REPLAY_INCOMPLETE",
            )
        if failure["status"] != INCOMPLETE:
            failure = incomplete_result_disposition(
                domain="solver",
                code="STRICT_REPLAY_INCOMPLETE",
            )
        verification["failure_disposition"] = failure
        verification["replay_complete"] = False
        return "INCOMPLETE"

    # Standalone replay remains useful for exact negative certificates, but a
    # certificate may not override a contradictory verifier result merely by
    # self-reporting CANDIDATE_REJECTED. Every non-candidate binding/evidence
    # check must independently pass, and the replayed final gate must reproduce
    # the exact typed rejection.
    checks = verification.get("checks")
    failures = verification.get("failures")
    replayed_gate = verification.get("final_gate")
    candidate_only_failures = {"final_gate", "certificate_passed_flag"}
    certificate_failure = certificate.get("failure_disposition")
    replayed_failure = classify_build_failure(
        exact=True,
        passed=False,
        final_gate=replayed_gate,
    )
    if (
        terminal_candidate_rejection(certificate)
        and isinstance(checks, Mapping)
        and set(checks) >= TERMINAL_NEGATIVE_REPLAY_CHECKS
        and {
            name for name, passed in checks.items() if passed is not True
        }
        == candidate_only_failures
        and isinstance(failures, list)
        and len(failures) == len(candidate_only_failures)
        and set(failures) == candidate_only_failures
        and replayed_failure
        == validate_failure_disposition(certificate_failure)
    ):
        verification["failure_disposition"] = replayed_failure
        return "REJECTED"

    # Stage 4 certificates already passed construction and an independent
    # replay. Any complete Stage 5 mismatch is contradictory evidence, never a
    # proof that no winner exists. The same rule protects malformed standalone
    # negative artifacts.
    verification["failure_disposition"] = contradiction_disposition(
        (
            "STRICT_REPLAY_CONTRADICTS_PASSED_CERTIFICATE"
            if certificate.get("passed") is True
            else "STRICT_REPLAY_CONTRADICTS_NEGATIVE_CERTIFICATE"
        ),
    )
    return "INCOMPLETE"


def _known_answer_outer_timeout(total_timeout_per_code: int) -> float:
    """Add a process kill boundary outside the baseline runner's own timeout."""

    return (
        float(_strict_wall_timeout(total_timeout_per_code))
        + KNOWN_ANSWER_OUTER_CUSHION_S
    )


def _strict_integrity_with_hard_wall(args: argparse.Namespace) -> dict[str, Any]:
    timeout = _known_answer_outer_timeout(
        args.known_answer_total_timeout,
    )
    try:
        outcome = run_isolated_call(
            check_known_answer_integrity,
            args=(args.known_answer_artifact, args.known_answer_trust),
            kwargs={
                "mode": "strict",
                "timeout_per_logical": args.known_answer_timeout_per_logical,
                "total_timeout_per_code": args.known_answer_total_timeout,
            },
            timeout_s=timeout,
            termination_grace_s=DEFAULT_TERMINATION_GRACE_S,
        )
    except (OSError, RuntimeError, TimeoutError, ValueError) as exc:
        return {
            "passed": False,
            "mode": "strict",
            "failures": [
                "strict known-answer integrity hard-wall setup failed: "
                f"{type(exc).__name__}: {exc}"
            ],
        }
    if outcome.status == "completed" and isinstance(outcome.value, dict):
        integrity = dict(outcome.value)
        if outcome.hard_wall is not None:
            integrity["hard_wall_cleanup"] = dict(outcome.hard_wall)
        return integrity
    failure = (
        "strict known-answer integrity exceeded its process hard wall"
        if outcome.status == "timeout"
        else "strict known-answer integrity worker failed"
    )
    if outcome.error:
        failure += f": {outcome.error}"
    return {
        "passed": False,
        "mode": "strict",
        "failures": [failure],
        "hard_wall": dict(outcome.hard_wall or {}),
    }


def _verify_certificate_with_hard_wall(
    certificate: dict[str, Any],
    *,
    known_answer_artifact: Path,
    timeout_per_logical: float,
    checkpoint_path: Path | None,
    resume: bool,
    total_timeout: float,
    solver_workers: int,
) -> dict[str, Any]:
    """Replay one certificate in a killable process, preserving checkpoints."""

    # The fair scheduler's per-certificate share includes forced cleanup.
    # Reserve a small slice for TERM->KILL so a wedged native solver cannot
    # consume the next peer's entire share after its mathematical deadline.
    termination_grace = min(
        DEFAULT_TERMINATION_GRACE_S,
        max(0.001, total_timeout * 0.05),
        total_timeout * 0.5,
    )
    solver_timeout = total_timeout - termination_grace
    try:
        outcome = run_isolated_call(
            verify_certificate,
            args=(certificate,),
            kwargs={
                "known_answer_artifact": known_answer_artifact,
                "rerun_milp": True,
                "timeout_per_logical": min(
                    timeout_per_logical,
                    solver_timeout,
                ),
                "checkpoint_path": checkpoint_path,
                "resume": resume,
                "total_timeout": solver_timeout,
                "solver_workers": solver_workers,
            },
            timeout_s=solver_timeout,
            termination_grace_s=termination_grace,
        )
    except (OSError, RuntimeError, TimeoutError, ValueError) as exc:
        return {
            **_incomplete_result(
                "strict certificate replay hard-wall setup failed: "
                f"{type(exc).__name__}: {exc}",
                domain="runtime",
                code="STRICT_REPLAY_HARD_WALL_SETUP_FAILED",
            ),
            "hard_wall": {"setup_failed": True},
        }
    if outcome.status == "completed" and isinstance(outcome.value, dict):
        verification = dict(outcome.value)
        if outcome.hard_wall is not None:
            verification["hard_wall_cleanup"] = dict(outcome.hard_wall)
        return verification
    failure = (
        "strict certificate replay exceeded its process hard wall"
        if outcome.status == "timeout"
        else "strict certificate replay worker failed"
    )
    if outcome.error:
        failure += f": {outcome.error}"
    return {
        **_incomplete_result(
            failure,
            domain="runtime",
            code=(
                "STRICT_REPLAY_HARD_WALL_TIMEOUT"
                if outcome.status == "timeout"
                else "STRICT_REPLAY_WORKER_FAILED"
            ),
        ),
        "hard_wall": dict(outcome.hard_wall or {}),
    }


def main() -> int:
    args = parse_args()
    try:
        _validate_verification_budget(args)
    except (TypeError, ValueError, OverflowError) as exc:
        print(
            f"FINAL GATE FAILED: invalid verification budget: {exc}",
            file=sys.stderr,
        )
        return 2
    try:
        rows = load_rows(args.claims)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"FINAL GATE FAILED: cannot load claims: {exc}", file=sys.stderr)
        return 2

    if not rows or any(
        row.get("certificate_type") not in SUPPORTED_CERTIFICATE_TYPES for row in rows
    ):
        print(
            "FINAL GATE FAILED: raw candidate metadata is forbidden; "
            "run scripts/build_certificate.py first",
            file=sys.stderr,
        )
        return 2

    payloads = [_payload_sha256(certificate) for certificate in rows]
    if len(set(payloads)) != len(payloads):
        print(
            "FINAL GATE FAILED: duplicate certificate payloads are forbidden",
            file=sys.stderr,
        )
        return 2

    integrity = _strict_integrity_with_hard_wall(args)

    evaluations_by_index: dict[int, dict[str, Any]] = {}
    if integrity.get("passed") is True:
        replay_started = time.monotonic()
        scheduler = None
        scheduler_path = None
        if args.verification_state_dir is not None:
            args.verification_state_dir.mkdir(parents=True, exist_ok=True)
            scheduler_path = (
                args.verification_state_dir / SCHEDULER_FILENAME
            )
            try:
                scheduler = _load_scheduler(scheduler_path, payloads)
            except (OSError, TypeError, ValueError) as exc:
                print(
                    f"FINAL GATE FAILED: cannot load replay scheduler: {exc}",
                    file=sys.stderr,
                )
                return 2
        start_payload = (
            payloads[0]
            if scheduler is None
            else str(scheduler["next_payload_sha256"])
        )
        start_index = payloads.index(start_payload)
        schedule = [
            *range(start_index, len(rows)),
            *range(0, start_index),
        ]
        for position, index in enumerate(schedule):
            certificate = rows[index]
            payload_sha256 = payloads[index]
            remaining = args.verification_total_timeout - (
                time.monotonic() - replay_started
            )
            checkpoint = None
            if args.verification_state_dir is not None:
                checkpoint = args.verification_state_dir / (
                    f"{payload_sha256}.json"
                )
            if remaining <= 0:
                break
            if scheduler is not None and scheduler_path is not None:
                try:
                    _advance_scheduler(
                        scheduler_path,
                        scheduler,
                        payloads=payloads,
                        current_payload=payload_sha256,
                    )
                except (OSError, TypeError, ValueError) as exc:
                    print(
                        "FINAL GATE FAILED: cannot advance replay scheduler: "
                        f"{exc}",
                        file=sys.stderr,
                    )
                    return 2
            remaining_certificates = len(schedule) - position
            # Reserve an equal worst-case share for every not-yet-scheduled
            # peer. A slow first replay therefore cannot consume the nominal
            # batch budget before each certificate has been entered once.
            certificate_total_timeout = (
                remaining / remaining_certificates
            )
            try:
                verification = _verify_certificate_with_hard_wall(
                    certificate,
                    known_answer_artifact=args.known_answer_artifact,
                    timeout_per_logical=min(
                        args.verification_timeout_per_logical,
                        certificate_total_timeout,
                    ),
                    checkpoint_path=checkpoint,
                    resume=args.resume,
                    total_timeout=certificate_total_timeout,
                    solver_workers=args.verification_solver_workers,
                )
            except Exception as exc:
                verification = _incomplete_result(
                    "strict certificate replay failed: "
                    f"{type(exc).__name__}: {exc}",
                    domain="runtime",
                    code="STRICT_REPLAY_RUNTIME_ERROR",
                )
            if not isinstance(verification, dict):
                verification = _incomplete_result(
                    "strict certificate replay returned a non-object result",
                    domain="schema",
                    code="STRICT_REPLAY_RESULT_NOT_OBJECT",
                )
            else:
                verification = {
                    **verification,
                    "replay_complete": (
                        True
                        if verification.get("passed") is True
                        else verification.get("replay_complete") is True
                    ),
                }
            evaluation = {
                "source_index": index,
                "claim": certificate.get("claim"),
                "certificate_sha256": certificate.get("certificate_sha256"),
                "certificate_payload_sha256": payload_sha256,
                "disposition": _verification_disposition(
                    certificate,
                    verification,
                ),
                "checkpoint_path": (
                    None if checkpoint is None else str(checkpoint)
                ),
                "result": verification,
            }
            evaluations_by_index[index] = evaluation
            if evaluation["disposition"] == "ACCEPTED":
                break
        for index, certificate in enumerate(rows):
            if index in evaluations_by_index:
                continue
            payload_sha256 = payloads[index]
            checkpoint = (
                None
                if args.verification_state_dir is None
                else args.verification_state_dir / f"{payload_sha256}.json"
            )
            evaluations_by_index[index] = {
                "source_index": index,
                "claim": certificate.get("claim"),
                "certificate_sha256": certificate.get("certificate_sha256"),
                "certificate_payload_sha256": payload_sha256,
                "disposition": "INCOMPLETE",
                "checkpoint_path": (
                    None if checkpoint is None else str(checkpoint)
                ),
                "result": _incomplete_result(
                    "strict replay deferred by fair batch scheduler",
                    domain="solver",
                    code="STRICT_REPLAY_DEFERRED",
                ),
            }
    else:
        for index, certificate in enumerate(rows):
            evaluations_by_index[index] = {
                "source_index": index,
                "claim": certificate.get("claim"),
                "certificate_sha256": certificate.get("certificate_sha256"),
                "certificate_payload_sha256": payloads[index],
                "disposition": "INCOMPLETE",
                "result": _incomplete_result(
                    "strict known-answer integrity failed",
                    domain="known_answer",
                    code="STRICT_KNOWN_ANSWER_INCOMPLETE",
                ),
            }
    evaluations = [
        evaluations_by_index[index] for index in range(len(rows))
    ]
    accepted = sum(
        item["disposition"] == "ACCEPTED" for item in evaluations
    )
    rejected = sum(
        item["disposition"] == "REJECTED" for item in evaluations
    )
    incomplete = sum(
        item["disposition"] == "INCOMPLETE" for item in evaluations
    )
    passed = bool(integrity.get("passed") is True and accepted > 0)
    if passed:
        outcome = "WIN"
    elif incomplete:
        outcome = "INCOMPLETE"
    else:
        outcome = "NO_WIN"
    artifact = {
        "schema_version": 1,
        "gate": "qldpc-challenge-final-batch",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "passed": passed,
        "outcome": outcome,
        "known_answer_integrity": integrity,
        "verification_budget": {
            "timeout_per_logical": args.verification_timeout_per_logical,
            "total_timeout": args.verification_total_timeout,
            "solver_workers": args.verification_solver_workers,
            "resume": args.resume,
            "state_dir": (
                None
                if args.verification_state_dir is None
                else str(args.verification_state_dir)
            ),
        },
        "summary": {
            "accepted": accepted,
            "rejected": rejected,
            "incomplete": incomplete,
            "total": len(evaluations),
        },
        "evaluations": evaluations,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = args.output.with_suffix(args.output.suffix + ".tmp")
    temporary.write_text(json.dumps(artifact, indent=2) + "\n")
    temporary.replace(args.output)

    status = outcome
    print(
        f"FINAL GATE {status}: {accepted}/{len(evaluations)} accepted; "
        f"artifact={args.output}"
    )
    if not passed:
        for failure in integrity.get("failures") or []:
            print(f"  known-answer: {failure}")
        for item in evaluations:
            result = item["result"]
            if item["disposition"] != "ACCEPTED":
                print(
                    f"  claim[{item['source_index']}] "
                    f"{item['disposition'].lower()}: "
                    + "; ".join(result.get("failures") or ["rejected"])
                )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
