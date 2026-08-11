#!/usr/bin/env python3
"""Independently rebuild and fully verify one qLDPC challenge certificate."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from evaluation.certificate_dispatch import (
    EXACT_ANCHOR_CSS_TYPE,
    verify_certificate,
)
from evaluation.exact_anchor_certificate import load_trusted_checker_policy
from evaluation.known_answer_integrity import check_known_answer_integrity


def main() -> int:
    project = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument(
        "--known-answer-artifact", type=Path,
        default=project / "results" / "known_answer_gate.json",
    )
    parser.add_argument(
        "--known-answer-trust", type=Path,
        default=project / "results" / "known_answer_trust.json",
    )
    parser.add_argument(
        "--known-answer-mode", choices=("fast", "strict"), default="strict",
    )
    parser.add_argument("--known-answer-timeout-per-logical", type=int, default=300)
    parser.add_argument("--known-answer-total-timeout", type=int, default=7200)
    parser.add_argument("--timeout-per-logical", type=float, default=None)
    parser.add_argument("--total-timeout", type=float, default=7200)
    parser.add_argument("--checkpoint", type=Path)
    parser.add_argument(
        "--resume",
        action=argparse.BooleanOptionalAction,
        default=True,
    )
    parser.add_argument("--solver-workers", type=int, default=1)
    parser.add_argument("--artifact-root", type=Path)
    parser.add_argument("--trusted-checker-policy", type=Path)
    parser.add_argument("--checker-timeout", type=float)
    args = parser.parse_args()
    checkpoint = args.checkpoint or args.certificate.with_suffix(
        args.certificate.suffix + ".verify.checkpoint.json",
    )
    try:
        certificate = json.loads(args.certificate.read_text())
        is_calibration = (
            certificate.get("certificate_type") == EXACT_ANCHOR_CSS_TYPE
        )
        if is_calibration:
            if args.artifact_root is None:
                raise ValueError("exact anchor requires explicit --artifact-root")
            if args.trusted_checker_policy is None:
                raise ValueError(
                    "exact anchor requires explicit --trusted-checker-policy"
                )
            if args.checker_timeout is None:
                raise ValueError("exact anchor requires explicit --checker-timeout")
            trusted_checkers = load_trusted_checker_policy(
                args.trusted_checker_policy,
            )
            result = verify_certificate(
                certificate,
                known_answer_artifact=args.known_answer_artifact,
                artifact_root=args.artifact_root,
                trusted_checkers=trusted_checkers,
                checker_timeout_s=args.checker_timeout,
            )
        else:
            integrity = check_known_answer_integrity(
                args.known_answer_artifact,
                args.known_answer_trust,
                mode=args.known_answer_mode,
                timeout_per_logical=args.known_answer_timeout_per_logical,
                total_timeout_per_code=args.known_answer_total_timeout,
            )
            if not integrity["passed"]:
                print("VERIFICATION FAILED: known-answer integrity", file=sys.stderr)
                for failure in integrity["failures"]:
                    print(f"  {failure}", file=sys.stderr)
                return 1
            result = verify_certificate(
                certificate,
                known_answer_artifact=args.known_answer_artifact,
                rerun_milp=True,
                timeout_per_logical=args.timeout_per_logical,
                checkpoint_path=checkpoint,
                resume=args.resume,
                total_timeout=args.total_timeout,
                solver_workers=args.solver_workers,
            )
    except (OSError, ValueError, KeyError, json.JSONDecodeError) as exc:
        print(f"VERIFICATION FAILED: {exc}", file=sys.stderr)
        return 2
    if is_calibration:
        valid = result.get("calibration_valid") is True
        print(
            "CALIBRATION VERIFIED / NOT A WIN"
            if valid else "CALIBRATION INVALID / NOT A WIN"
        )
        for failure in result.get("failures", []):
            print(f"  {failure}")
        return 0 if valid else 1
    status = "PASSED" if result["passed"] else "FAILED"
    print(
        f"VERIFICATION {status}: d={result.get('distance')} "
        f"directions={result.get('directions_verified', 0)}/"
        f"{result.get('directions_total', 0)}"
    )
    if result["failures"]:
        for failure in result["failures"]:
            print(f"  {failure}")
    return 0 if result["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
