#!/usr/bin/env python3
"""Fully replay every certificate in a challenge release manifest."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from evaluation.certificate import verify_css_certificate
from evaluation.known_answer_integrity import check_known_answer_integrity
from evaluation.release_gate import validate_release_manifest


def main() -> int:
    project = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--run-id")
    parser.add_argument("--known-answer-mode", choices=("fast", "strict"), default="fast")
    parser.add_argument(
        "--known-answer-artifact", type=Path,
        default=project / "results" / "known_answer_gate.json",
    )
    parser.add_argument(
        "--known-answer-trust", type=Path,
        default=project / "results" / "known_answer_trust.json",
    )
    parser.add_argument("--timeout-per-logical", type=float, default=None)
    parser.add_argument("--known-answer-timeout-per-logical", type=int, default=300)
    parser.add_argument("--known-answer-total-timeout", type=int, default=7200)
    args = parser.parse_args()

    static = validate_release_manifest(
        args.manifest, expected_run_id=args.run_id,
    )
    integrity = check_known_answer_integrity(
        args.known_answer_artifact,
        args.known_answer_trust,
        mode=args.known_answer_mode,
        timeout_per_logical=args.known_answer_timeout_per_logical,
        total_timeout_per_code=args.known_answer_total_timeout,
    )
    failures = list(static["failures"]) + [
        f"known-answer: {failure}" for failure in integrity["failures"]
    ]
    verified = 0
    if static["passed"] and integrity["passed"]:
        manifest = json.loads(args.manifest.read_text())
        for index, entry in enumerate(manifest["certificates"]):
            certificate_path = args.manifest.parent / entry["file"]
            certificate = json.loads(certificate_path.read_text())
            result = verify_css_certificate(
                certificate,
                known_answer_artifact=args.known_answer_artifact,
                rerun_milp=True,
                timeout_per_logical=args.timeout_per_logical,
            )
            if result["passed"]:
                verified += 1
            else:
                failures.extend(
                    f"certificate[{index}]: {failure}"
                    for failure in result["failures"]
                )
    passed = not failures and verified == static.get("certificates", 0) > 0
    print(
        f"RELEASE REPLAY {'PASSED' if passed else 'FAILED'}: "
        f"{verified}/{static.get('certificates', 0)} certificates"
    )
    for failure in failures:
        print(f"  {failure}")
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
