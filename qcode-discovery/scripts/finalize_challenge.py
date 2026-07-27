#!/usr/bin/env python3
"""Run the mandatory, fail-closed terminal gate on proposed challenge claims.

Input may be a JSON object, a JSON list, or JSONL.  Every submitted row must
pass.  The command exits nonzero for an empty input, malformed evidence, an
unsupported certificate type, or any rejected candidate.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation.certificate_dispatch import (
    SUPPORTED_CERTIFICATE_TYPES,
    verify_certificate,
)
from evaluation.known_answer_integrity import check_known_answer_integrity


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

    try:
        integrity = check_known_answer_integrity(
            args.known_answer_artifact,
            args.known_answer_trust,
            mode="strict",
            timeout_per_logical=args.known_answer_timeout_per_logical,
            total_timeout_per_code=args.known_answer_total_timeout,
        )
    except (OSError, TypeError, ValueError, json.JSONDecodeError) as exc:
        integrity = {
            "passed": False,
            "mode": "strict",
            "failures": [f"strict known-answer integrity failed: {exc}"],
        }

    evaluations = []
    if integrity.get("passed") is True:
        replay_started = time.monotonic()
        if args.verification_state_dir is not None:
            args.verification_state_dir.mkdir(parents=True, exist_ok=True)
        for index, certificate in enumerate(rows):
            remaining = args.verification_total_timeout - (
                time.monotonic() - replay_started
            )
            checkpoint = None
            if args.verification_state_dir is not None:
                checkpoint = args.verification_state_dir / (
                    f"{index:04d}-{_payload_sha256(certificate)}.json"
                )
            if remaining <= 0:
                verification = {
                    "passed": False,
                    "accepted": False,
                    "failures": ["strict replay batch timeout exhausted"],
                }
            else:
                try:
                    verification = verify_certificate(
                        certificate,
                        known_answer_artifact=args.known_answer_artifact,
                        rerun_milp=True,
                        timeout_per_logical=min(
                            args.verification_timeout_per_logical,
                            remaining,
                        ),
                        checkpoint_path=checkpoint,
                        resume=args.resume,
                        total_timeout=remaining,
                        solver_workers=args.verification_solver_workers,
                    )
                except Exception as exc:
                    verification = {
                        "passed": False,
                        "accepted": False,
                        "failures": [
                            "strict certificate replay failed: "
                            f"{type(exc).__name__}: {exc}"
                        ],
                    }
            evaluations.append(
                {
                    "source_index": index,
                    "claim": certificate.get("claim"),
                    "certificate_sha256": certificate.get("certificate_sha256"),
                    "checkpoint_path": (
                        None if checkpoint is None else str(checkpoint)
                    ),
                    "result": verification,
                }
            )
    else:
        for index, certificate in enumerate(rows):
            evaluations.append(
                {
                    "source_index": index,
                    "claim": certificate.get("claim"),
                    "certificate_sha256": certificate.get("certificate_sha256"),
                    "result": {
                        "passed": False,
                        "accepted": False,
                        "failures": ["strict known-answer integrity failed"],
                    },
                }
            )
    accepted = sum(item["result"].get("passed") is True for item in evaluations)
    passed = bool(
        integrity.get("passed") is True and evaluations and accepted == len(evaluations)
    )
    artifact = {
        "schema_version": 1,
        "gate": "qldpc-challenge-final-batch",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "passed": passed,
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
            "rejected": len(evaluations) - accepted,
            "total": len(evaluations),
        },
        "evaluations": evaluations,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = args.output.with_suffix(args.output.suffix + ".tmp")
    temporary.write_text(json.dumps(artifact, indent=2) + "\n")
    temporary.replace(args.output)

    status = "PASSED" if passed else "FAILED"
    print(
        f"FINAL GATE {status}: {accepted}/{len(evaluations)} accepted; "
        f"artifact={args.output}"
    )
    if not passed:
        for failure in integrity.get("failures") or []:
            print(f"  known-answer: {failure}")
        for item in evaluations:
            result = item["result"]
            if not result.get("accepted"):
                print(
                    f"  claim[{item['source_index']}]: "
                    + "; ".join(result.get("failures") or ["rejected"])
                )
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
