#!/usr/bin/env python3
"""Independently rebuild and fully verify one qLDPC challenge certificate."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from evaluation.certificate import verify_css_certificate
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
        "--known-answer-mode", choices=("fast", "strict"), default="fast",
    )
    parser.add_argument("--known-answer-timeout-per-logical", type=int, default=300)
    parser.add_argument("--known-answer-total-timeout", type=int, default=7200)
    parser.add_argument("--timeout-per-logical", type=float, default=None)
    args = parser.parse_args()
    try:
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
        certificate = json.loads(args.certificate.read_text())
        result = verify_css_certificate(
            certificate,
            known_answer_artifact=args.known_answer_artifact,
            rerun_milp=True,
            timeout_per_logical=args.timeout_per_logical,
        )
    except (OSError, ValueError, KeyError, json.JSONDecodeError) as exc:
        print(f"VERIFICATION FAILED: {exc}", file=sys.stderr)
        return 2
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
